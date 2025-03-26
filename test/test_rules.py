#!/usr/bin/env python3
import argparse
import glob
import subprocess
import re
from collections import Counter
import sys

def main():
    parser = argparse.ArgumentParser(
        description="Process SMT2 proofs using cvc5. Supply either a directory (-d) to search recursively for .smt2 files or a single file (-f) to process."
    )
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("-d", "--directory", help="Directory to recursively search for .smt2 files")
    group.add_argument("-f", "--file", help="Single SMT2 file to process")

    args = parser.parse_args()

    # Determine the list of files to process
    if args.directory:
        # Use glob to recursively find all .smt2 files in the provided directory.
        smt2_files = glob.glob(f"{args.directory}/**/*.smt2", recursive=True)
        if not smt2_files:
            print(f"No .smt2 files found in directory '{args.directory}' recursively.")
            sys.exit(1)
    else:
        # A single file was provided.
        smt2_files = [args.file]

    rule_counter = Counter()

    for filename in smt2_files:
        print(f"Processing {filename}...")
        try:
            # Run cvc5 on the file and capture its output.
            result = subprocess.run(
                ["cvc5",
                    "--dump-proofs",
                    "--proof-format-mode=cpc",
                    "--proof-granularity=dsl-rewrite",
                    "--proof-print-conclusion",
                    # "--expr-depth=-1",
                    "--proof-dag-global",
                    filename
                ],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                check=True
            )
            output = result.stdout
        except subprocess.CalledProcessError as e:
            print(f"Error running cvc5 on {filename}: {e.stderr}")
            continue

        # Remove the first line (e.g., the "unsat"/"sat" message) from the proof output.
        lines = output.splitlines()
        proof_output = "\n".join(lines[1:]) if len(lines) > 1 else ""

        # Write the proof output to a file with the extension .prf (e.g., file.smt2.prf).
        prf_filename = f"{filename}.prf"
        try:
            with open(prf_filename, "w") as prf_file:
                prf_file.write(proof_output)
            print(f"Proof written to {prf_filename}")
        except IOError as io_err:
            print(f"Error writing proof to {prf_filename}: {io_err}")

        # Extract rule names that appear after ':rule'
        rules = re.findall(r":rule\s+(\S+)", output)
        rule_counter.update(rules)

    # Sort rules by frequency (highest first).
    sorted_rules = sorted(rule_counter.items(), key=lambda item: item[1], reverse=True)

    # Write the sorted rule frequencies to a file.
    output_filename = "rule_frequencies.txt"
    try:
        with open(output_filename, "w") as f:
            for rule, count in sorted_rules:
                f.write(f"{rule}: {count}\n")
        print(f"Rule frequencies written to {output_filename}")
    except IOError as io_err:
        print(f"Error writing rule frequencies to {output_filename}: {io_err}")

if __name__ == "__main__":
    main()
