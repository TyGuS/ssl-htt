import subprocess
from time import perf_counter
import os
from os.path import isfile, join, dirname, realpath
import csv
import argparse


# Directory where benchmark programs are located
BENCHMARK_DIR    = dirname(realpath(__file__))
# Directory names of the benchmark groups to evaluate
BENCHMARK_GROUPS = ["bst", "dll", "srtl"]
# Name of output statistics CSV file
STAT_FILE        = "advanced-HTT.csv"
# Name of output diff file
DIFF_FILE        = "advanced-HTT.diff"


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
	cmd = [
		"diff", "-r",
		"-x", "*.csv",
		"-x", "*.diff",
		"-x", "*.glob",
		"-x", "*.vo*",
		"-x", ".*.aux",
		"-x", ".lia*",
		"-x", "Makefile",
		"-x", "*.csv",
		dir1, dir2
	]
	return subprocess.call(cmd, stdout=out_file)


def cmdline():
	parser = argparse.ArgumentParser(description="Evaluation tool for advanced HTT benchmarks.")
	parser.add_argument("--nodiff", action="store_true",
		                help="Skip diff file generation")
	parser.add_argument("--nostat", action="store_true",
		                help="Skip proof compilation/generation of stats CSV file")
	parser.add_argument("--diffSource", action="store", default=None,
		                help="The directory containing the generated advanced benchmark HTT certificates")
	parser.add_argument("--outputDir", action="store", default=BENCHMARK_DIR,
		                help="The directory where output files should be stored")
	return parser.parse_args()


def mkdirs(filename):
	if not os.path.exists(dirname(filename)):
		try:
			os.makedirs(dirname(filename))
		except OSError as exc:
			if exc.errno != errno.EEXIST:
				raise


def main():
	opts = cmdline()

	if not opts.nodiff:
		diff_file_path = join(opts.outputDir, DIFF_FILE)
		suslik_home = os.environ.get("SUSLIK_HOME")
		if opts.diffSource is None and suslik_home is None:
			print("No diff file generated! Environment variable $SUSLIK_HOME not set.")
			print("Please set it or specify a source directory with the --diffSource option.")
		else:
			if opts.diffSource is None:
				diff_source = join(suslik_home, "certify/HTT/certification-benchmarks-advanced")
			else:
				diff_source = opts.diffSource
			mkdirs(diff_file_path)
			with open(diff_file_path, "w") as f:
				print("Comparing manually edited certificates to SuSLik-generated ones...")
				if gen_diff(BENCHMARK_DIR, diff_source, f) == 2:
					print(f"No diff file generated! Make sure SuSLik-generated certificates are present in:")
					print(f"  {diff_source}")
				else:
					print(f"Diff file generated at:")
					print(f"  {diff_file_path}")

	if not opts.nostat:
		stat_file_path = join(opts.outputDir, STAT_FILE)
		mkdirs(stat_file_path)
		with open(stat_file_path, "w", newline="") as csvfile:
			print("\nRunning benchmarks...\n")
			writer = csv.writer(csvfile)
			header = ["Benchmark Group", "File Name", "Spec Size", "Proof Size", "Proof Checking Time (sec)"]
			writer.writerow(header)

			for group in BENCHMARK_GROUPS:
				cwd = join(BENCHMARK_DIR, group)
				files = [f for f in os.listdir(cwd) if isfile(join(cwd, f))]

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

			print(f"\nFinished running benchmarks! Results written to {stat_file_path}.")

if __name__ == '__main__':
	main()
