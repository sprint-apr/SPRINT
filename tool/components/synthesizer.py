import os
import pymysql
import argparse
import datetime
import requests
import socket
import paramiko
from tqdm import tqdm
from pathlib import Path
from synthesizer.drivers import (
    AlphaRepair,
    Project,
    Configuration,
    BertOnly,
)

HOST_NAME = socket.gethostname()

conn = pymysql.connect(
    host="163.152.26.125", user="validator", password="tlfja12", db="synthesis_icse25"
)


def put_patch_at_remote(sftps, remote_patches_dir, target):
    for sftp in sftps:
        try:
            sftp.stat(target_dir := str(remote_patches_dir / target.id))
        except FileNotFoundError:
            sftp.mkdir(target_dir)
        remote_path = remote_patches_dir.joinpath(
            target.id, target.patches_json_file_path.parts[-1]
        )
        if target.patches_json_file_path.exists():
            sftp.put(
                str(target.patches_json_file_path),
                str(remote_path),
            )


def establish_sftp(hostname):
    ssh_config = paramiko.SSHConfig().from_path(Path.home() / ".ssh" / "config")
    ssh = paramiko.SSHClient()
    ssh.set_missing_host_key_policy(paramiko.AutoAddPolicy())
    host_config = ssh_config.lookup(hostname)
    private_key = paramiko.RSAKey.from_private_key_file(Path.home() / ".ssh" / "id_rsa")

    ssh.connect(
        hostname=host_config["hostname"],
        username=host_config.get("user"),
        pkey=private_key,
    )

    sftp = ssh.open_sftp()
    return sftp


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("bugs_dir", type=Path)
    parser.add_argument("driver", choices=["ar", "bo"])
    parser.add_argument("--device", choices=["cuda:0", "cuda:1", "cpu"], required=True)
    parser.add_argument("--abspatch_dir", type=Path, default=None)
    parser.add_argument("--beam-width", type=int, required=True)
    parser.add_argument(
        "--suffix", type=str, default=datetime.datetime.now().strftime("%m%d")
    )
    parser.add_argument("--skip-inference", action="store_true")
    parser.add_argument("--timeout", type=float, default=3600)
    parser.add_argument("--num-max-patches", type=int, default=30000)
    parser.add_argument(
        "--trial-id",
        default="bert_only_test",
        help="Specify identifier for csv and json",
    )
    parser.add_argument(
        "--bid",
        help="Specify single bug id to work (use underscore '_' instead of dash '-')",
    )
    parser.add_argument("--target", help="Specifies target bug id file")
    parser.add_argument("--exclude", help="Specifies bug id files to exclude running")
    parser.add_argument("--db", help="Specifies db file to use")
    args = parser.parse_args()

    device = args.device
    driver = AlphaRepair if args.driver == "ar" else BertOnly

    middle = (
        datetime.datetime.now().strftime("%Y%m%d")
        if args.driver == "ar"
        else args.abspatch_dir.parts[-1]
    )
    trial_id = f"{args.driver}.{middle}.{args.beam_width}.{args.suffix}"

    abspatch_limit = int((args.num_max_patches / 10) / args.beam_width)

    configuration = Configuration(
        trial_id=trial_id,
        abspatch_dir=args.abspatch_dir,
        beam_width=args.beam_width,
        abspatch_limit=abspatch_limit,
        num_max_patches=args.num_max_patches,
        timeout=args.timeout,
        generate_beam=not args.skip_inference,
        device=device,
        verbose=False,
    )

    # run with single bug
    if args.bid != None:
        driver = (AlphaRepair if args.driver == "ar" else BertOnly)(configuration, conn)
        target = Project(args.bugs_dir / args.bid, configuration)
        driver.run(target)
        exit(0)

    targets = [Project(args.bugs_dir / id.name, configuration) for id in 
               Path(args.abspatch_dir).glob('*')]

    # Prepare remote dirs
    patches_dir_path = (Path.home() / trial_id).with_suffix(".patches")
    sftps = list(
        establish_sftp(hostname)
        for hostname in ["thanos"]
        if HOST_NAME.lower() not in hostname
    )

    for sftp in sftps:
        try:
            sftp.stat(str(patches_dir_path))
        except FileNotFoundError:
            sftp.mkdir(str(patches_dir_path))

    log = Path(trial_id).with_suffix(".log")
    log.write_text(f"# Start Time: {datetime.datetime.now().strftime('%m%d-%H%M')}\n")
    driver = (AlphaRepair if args.driver == "ar" else BertOnly)(configuration, conn)
    for i, target in enumerate(tqdm(targets)):
        msg, probe = driver.run(target)
        text = f"[{i+1}] / {len(targets)} {msg}"
        log.write_text(msg + "\n")
        put_patch_at_remote(sftps, patches_dir_path, target)
