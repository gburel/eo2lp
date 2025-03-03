#!/usr/bin/env python3
import glob
import subprocess
import re
from collections import Counter
import os

def main():
    # Recursively find all .smt2 files in the current directory.
    smt2_files = glob.glob("**/*.smt2", recursive=True)
    if not smt2_files:
        print("No .smt2 files found in the directory recursively.")
        return

    rule_counter = Counter()

    for filename in smt2_files:
        print(f"Processing {filename}...")
        try:
            # Run cvc5 on the file and capture its output.
            result = subprocess.run(
                ["cvc5",
                    "--dump-proofs",
                    "--proof-granularity=dsl-rewrite",
                    "--proof-print-conclusion",
                    "--dag-thresh=0",
                    "--expr-depth=-1",
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

        # Write the proof output to a file with the extension .prf (e.g., file.smt2.prf).
        prf_filename = f"{filename}.prf"
        try:
            with open(prf_filename, "w") as prf_file:
                prf_file.write(output)
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
