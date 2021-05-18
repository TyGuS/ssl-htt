import subprocess
from time import perf_counter
from os import listdir, getcwd
from os.path import isfile, join
import csv


# Directory where benchmark programs are located
BENCHMARK_DIR    = getcwd()
# Directory names of the benchmark groups to evaluate
BENCHMARK_GROUPS = ["bst", "dll", "srtl"]
# Name of output statistics CSV file
STAT_FILE        = "advanced-HTT.csv"
# Name of output diff file
DIFF_FILE        = "advanced-HTT.diff"
# Directory where original SuSLik-generated certificates are stored
ORIGINAL_DIR     = "/home/artifact/projects/suslik/certify/HTT/certification-benchmarks-advanced"

# Check the proof size and spec size of a Coq (.v) file
def coqwc(fpath, cwd):
	res = subprocess.run(["coqwc", fpath], cwd=cwd, text=True, capture_output=True)
	if res.returncode != 0:
		return None
	try:
		line = res.stdout.split("\n")[1].split()
		return (line[0], line[1])
	except e:
		print(e)
		return None


# Compile a Coq (.v) file
def coqc(fpath, cwd):
	t1 = perf_counter()
	code = subprocess.call(["make", fpath], cwd=cwd)
	t2 = perf_counter()

	if code == 0:
		d = t2 - t1
		return f"{d:.1f}"
	else:
		return None

# Generate a diff file comparing Coq (.v) files in two directories
def gen_diff(dir1, dir2, out_file):
	cmd = ["diff", "-r", "-x", "*.glob", "-x", "*.vo*", "-x", ".*.aux", "-x", ".lia*", "-x", "Makefile", dir1, dir2]
	return subprocess.call(cmd, stdout=out_file)


def main():
	with open(DIFF_FILE, "w") as f:
		print("Comparing manually edited certificates to SuSLik-generated ones...")
		if gen_diff(BENCHMARK_DIR, ORIGINAL_DIR, f) == 0:
			print(f"Diff file generated at {DIFF_FILE}!")
		else:
			print(f"No diff file generated! Expected SuSLik-generated certificates in {ORIGINAL_DIR}.")

	with open(STAT_FILE, "w", newline="") as csvfile:
		print("\nRunning benchmarks...\n")
		writer = csv.writer(csvfile)
		header = ["Benchmark Group", "File Name", "Spec Size", "Proof Size", "Proof Checking Time (sec)"]
		writer.writerow(header)

		for group in BENCHMARK_GROUPS:
			cwd = join(BENCHMARK_DIR, group)
			files = [f for f in listdir(cwd) if isfile(join(cwd, f))]

			print("=========================================")
			print(f"  Benchmark Group: {group}")
			print("=========================================\n")

			# compile common defs
			print(f"Compiling common definitions for benchmark group '{group}'...", end="")
			if "common.v" not in files:
				print(f"- ERR\n  Common definitions not found for benchmark group '{group}'.")
				continue
			if coqc("common", cwd) is None:
				print(f"- ERR\n  Failed to compile common definitions for benchmark group '{group}'.")
				continue
			print("done!")

			for f in files:
				if f == "common.v" or not f.endswith(".v"):
					continue

				print(f"Checking sizes for {f}...", end="")
				sizes = coqwc(f, cwd)
				if sizes is None:
					print(f"- ERR\n  Failed to check sizes for {f}.")
					duration = None
				else:
					print("done!")
					print(f"Compiling {f}...", end="")
					duration = coqc(f+"o", cwd)
					if duration is None:
						print(f"- ERR\n  Failed to compile {f}.")
					else:
						print("done!")

				row = [group, f, sizes[0], sizes[1], duration]
				rowstr = list(map(lambda x: "-" if x is None else str(x), row))

				writer.writerow(rowstr)
				csvfile.flush()

			print("\n")

		print(f"\nFinished running benchmarks! Results written to {STAT_FILE}.")

if __name__ == '__main__':
	main()
