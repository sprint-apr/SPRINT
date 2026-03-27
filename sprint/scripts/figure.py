import click
import os
import matplotlib.pyplot as plt
import pandas as pd
from matplotlib_venn import venn2, venn3


@click.group()
def figure():
    pass

@figure.command()
@click.option('--folder', '-d', required=True, type=click.Path(exists=True, file_okay=False),
              help='Folder containing bug ID text files')
def venn_group(folder):
    txt_files = [os.path.join(folder, f) for f in os.listdir(folder) if f.endswith('.txt')]
    if len(txt_files) < 2 or len(txt_files) > 3:
        raise click.UsageError("Folder must contain 2 or 3 text files for Venn diagram.")

    sets = {}
    for fname in txt_files:
        with open(fname, "r") as f:
            items = {line.strip() for line in f if line.strip()}
        sets[os.path.splitext(os.path.basename(fname))[0]] = items

    # Venn diagram
    plt.figure(figsize=(8, 6))
    if len(sets) == 2:
        (name1, s1), (name2, s2) = sets.items()
        venn2([s1, s2], set_labels=(name1, name2))
    elif len(sets) == 3:
        (name1, s1), (name2, s2), (name3, s3) = sets.items()
        venn3([s1, s2, s3], set_labels=(name1, name2, name3))
    else:
        raise click.UsageError("Only 2 or 3 files supported for Venn diagram.")

    plt.title("Bug ID Venn Diagram")
    plt.tight_layout()
    plt.savefig("group_figure.pdf")
    click.echo("Saved Venn diagram as group_figure.pdf")

@figure.command()
@click.option('--folder', '-d', required=True, type=click.Path(exists=True, file_okay=False),
              help='Folder containing bug ID text files')
def compare(folder):
    txt_files = [f for f in os.listdir(folder) if f.endswith(".txt")]
    if not txt_files:
        raise ValueError("No txt files found in the folder!")

    tool_sets = {}
    for f in txt_files:
        tool_name = os.path.splitext(f)[0]  # filename = tool name
        with open(os.path.join(folder, f), "r") as fh:
            bug_ids = {line.strip() for line in fh if line.strip()}
        tool_sets[tool_name] = bug_ids

    all_bug_ids = set().union(*tool_sets.values())

    # create DataFrame
    df = pd.DataFrame(index=sorted(all_bug_ids))
    for tool, bugs in tool_sets.items():
        df[tool] = [bug in bugs for bug in df.index]

    df.index.name = "bug_id"
    df.to_csv("bug_id_tool_matrix.csv")
    print("Saved bug_id_tool_matrix.csv")

