
import json
from pathlib import Path
import click

@click.group("cli")
def cli():
  pass

@cli.command
@click.argument("textfile", type=click.Path(path_type=Path))
@click.argument("key", type=str)
def json_escape(textfile: Path, key: str):
  content = textfile.read_text()
  with open((output_path := textfile.with_suffix(".json")), "w") as fp:
    json.dump({key: content}, fp, indent=4)
    print(output_path)


if __name__ == '__main__':
  cli()