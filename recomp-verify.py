import glob
import os
import shutil
import subprocess
import sys
from functools import partial

root_dir = os.path.dirname(os.path.abspath(__file__))
tool = root_dir + "/bin/recomp-verify.jar"
tlc = root_dir + "/bin/tla2tools.jar"

def write(name, contents):
    # Writes contents to a file
    with open(name, "w") as f:
        f.write(contents)

def decomp(spec, cfg):
    # Decomposes the spec and cfg using the recomp tool
    cmd_args = ["java", "-jar", tool, spec, cfg, "--decomp"]
    ret = subprocess.run(cmd_args, capture_output=True, text=True)
    # Print the return code and stdout for debugging
    return ret.stdout.rstrip().split(",")

def create_err_trace(txt):
    # Extracts error trace from the model checking output
    lines = txt.split("\n")
    keep = []
    capture = False
    for l in lines:
        if ("Error:" in l):
            capture = True
        if ("distinct states found" in l):
            capture = False
        if (capture and "errCounter" not in l):
            keep.append(l)
    return "\n".join(keep)

def verify(spec, cfg, cust, naive, verbose):
    # Runs the model checking algorithm
    cmd_args = ["java", "-Xmx25g", "-jar", tool, spec, cfg]
    if cust:
        cmd_args.append("--cust")
        cmd_args.append("custom_recomp.csv")
    if naive:
        cmd_args.append("--naive")
    if verbose:
        cmd_args.append("--verbose")
    
    print("Command to run:", ' '.join(cmd_args))  # Confirm the command with --cust
    retcode = subprocess.call(cmd_args)
    
    
    if retcode == 99:
        replay_args = ["java", "-jar", tlc, "-deadlock", "ErrTrace.tla"]
        replay = subprocess.run(replay_args, capture_output=True, text=True)
        replay_out = replay.stdout
        print(f"Replay command exited with return code: {replay.returncode}")  # Debug
        if "Error:" in replay_out:
            err_trace = create_err_trace(replay_out)
            print("Here is the error trace:\n")
            print(err_trace)
        else:
            print("Could not confirm the violating trace in the TLA+ spec; this is a bug in the tool.")

def verify_single_process(spec, cfg, cust, naive, verbose):
    # Sets up directories and copies necessary files for single-process verification
    orig_dir = os.getcwd()
    os.makedirs("out", exist_ok=True)
    dest_dir = orig_dir + "/out"

    for filename in glob.glob(os.path.join(orig_dir, '*.*')):
        shutil.copy(filename, dest_dir)

    os.chdir("out")
    verify(spec, cfg, cust, naive, verbose)
    os.chdir(orig_dir)

def verify_capture_output(spec, cfg, pdir, *args):
    # Captures output of the verification process
    shutil.copy(spec, pdir + "/")
    shutil.copy(cfg, pdir + "/")

    cmd_args = ["java", "-Xmx7g", "-jar", tool, spec, cfg]
    for arg in args:
        cmd_args.append(arg)

    # Uses TLC to run the one-component case
    if pdir == "mono":
        cmd_args = ["java", "-Xmx7g", "-jar", tlc, "-deadlock", "-workers", "1", "-config", cfg, spec]

    cd_args = ["cd", pdir]
    cmd = " ".join(cd_args) + "; " + " ".join(cmd_args)
    ret = subprocess.run(cmd, capture_output=True, text=True, shell=True)

    # Print the return code and stdout/stderr for debugging
    print(f"Command exited with return code: {ret.returncode}")
    print(f"Command stdout: {ret.stdout}")
    print(f"Command stderr: {ret.stderr}")

    return ret.stdout.rstrip()

def get_all_output(dest_dir, subdirs):
    """
    Print contents from log files
    """
    print("\n--- Log Outputs ---")
    for subdir in subdirs:
        log_file = os.path.join(dest_dir, subdir, f"{subdir}.log")
        if os.path.exists(log_file):
            with open(log_file, 'r') as f:
                content = f.read().strip()
                if content:  # Only print non-empty logs
                    print(f"\n- Contents of {subdir}/{subdir}.log -:\n")
                    print(content)
                else:
                    print(f"\n{subdir}.log is empty.")
        else:
            print(f"\nLog file {subdir}.log does not exist in {subdir}.")

def get_winner_output(dest_dir, subdir):
        log_file = os.path.join(dest_dir, subdir, f"{subdir}.log")
        if os.path.exists(log_file):
            with open(log_file, 'r') as f:
                content = f.read().strip()
                if content:  # Only print non-empty logs
                    print(content)
                else:
                    print(f"\n{subdir}.log is empty.")
        else:
            print(f"\nLog file {subdir}.log does not exist in {subdir}.")

def create_script(script_name, spec, cfg, subdir, flag):
    """
    Creates a shell script for running a specific strategy.
    """
    return f"""#!/usr/bin/env bash
echo "Running {script_name}"
echo "Spec file is: {spec}"
echo "CFG file is: {cfg}"
echo "Running in subdirectory: {subdir}"

# Navigate to the target directory
cd "./{subdir}" || {{
    echo "Failed to cd into the target directory." >&2
    exit 1
}}

# Run the verification script with the {flag} option
python3 "{os.path.join(root_dir, 'recomp-verify.py')}" \\
    "{os.path.basename(spec)}" \\
    "{os.path.basename(cfg)}" \\
    {flag} > "{subdir}.log" 2>&1
"""

def run_multi_verif_with_parallel(dest_dir, spec, cfg, verbose=False):
    # Get the absolute path to recomp-verify.py using root_dir
    script_path = os.path.join(root_dir, "recomp-verify.py")

    # Prepare the individual subdirectories for each verification case
    subdirs = ["mono", "cust_1", "cust_2", "naive"]
    
    # Determine the original directory (the one containing the TLA and CFG files)
    orig_dir = os.path.dirname(os.path.abspath(spec))
    if not orig_dir:
        orig_dir = os.getcwd()

    # Define the path to no_invs.cfg
    no_invs_cfg_path = os.path.join(root_dir, "no_invs.cfg")

    # Loop through subdirs to create each directory and copy spec, cfg, and no_invs.cfg files
    for subdir in subdirs:
        subdir_path = os.path.join(dest_dir, subdir)
        os.makedirs(subdir_path, exist_ok=True)
        
        # Copy the required files only if they don't already exist
        shutil.copy(spec, os.path.join(subdir_path, os.path.basename(spec)))
        shutil.copy(cfg, os.path.join(subdir_path, os.path.basename(cfg)))
        if os.path.exists(no_invs_cfg_path):
            shutil.copy(no_invs_cfg_path, os.path.join(subdir_path, "no_invs.cfg"))

    # Define strategies and corresponding flags
    strategy_flags = {
        "mono": "--cust",
        "cust_1": "--cust",
        "cust_2": "--cust",
        "naive": "--naive"
    }

    # Define file names for each corresponding .sh file
    script_names = ["mono.sh", "cust_1.sh", "cust_2.sh", "naive.sh"]

    # Generate each shell script in the desired format
    for subdir, script_name in zip(subdirs, script_names):
        # The strategy flag
        flag = strategy_flags[subdir]

        # Shell script content:
        script_content = create_script(script_name, spec, cfg, subdir, flag)
        script_path = os.path.join(dest_dir, script_name)
        with open(script_path, 'w') as f:
            f.write(script_content)

        # Make the script executable
        os.chmod(script_path, 0o755)
    
    if verbose:
        print("Shell scripts created successfully. List as follows:")
        for script in script_names:
            print(f"- {os.path.join(dest_dir, script)}")

     # Run them in parallel
    parallel_cmd = (
        f'parallel --halt now,done=1 --line-buffer --keep-order ::: '
        f'"./mono.sh" "./cust_1.sh" "./cust_2.sh" "./naive.sh"'
    )

    # Run the parallel command
    process = subprocess.Popen(parallel_cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, shell=True, text=True)
    stdout, stderr = process.communicate()

        
    # If there's an error, print the stderr output
    if process.returncode != 0:
        print("Parallel command found an error")  # Display error output

    winner_strategy = ""
    for line in stderr.splitlines():
        if ".sh" in line:
            winner_strategy += line.split(".sh")[0][2:] + "\n"

    if verbose:
        get_all_output(dest_dir, subdirs)
    else:
        get_winner_output(dest_dir, winner_strategy.strip())

def verify_multi_process(spec, cfg, verbose):
    # Sets up directories and runs multi-process verification using the 'parallel' command
    orig_dir = os.getcwd()
    os.makedirs("out", exist_ok=True)
    dest_dir = orig_dir + "/out"
    shutil.copy(spec, dest_dir)
    shutil.copy(cfg, dest_dir)

    # Copy no_invs.cfg to dest_dir if it exists, otherwise touch an empty one
    no_invs_cfg_path = os.path.join(orig_dir, "no_invs.cfg")
    dest_file = os.path.join(dest_dir, "no_invs.cfg")

    if os.path.exists(no_invs_cfg_path):
        # Copy the existing no_invs.cfg file
        if os.path.abspath(no_invs_cfg_path) != os.path.abspath(dest_file):
            shutil.copy(no_invs_cfg_path, dest_file)
    else:
        # Create an empty no_invs.cfg file
        with open(dest_file, "w") as f:
            print("Creating an empty no_invs.cfg file in the destination directory.")

    os.chdir("out")

    # Decompose the spec and cfg
    os.makedirs("decomp", exist_ok=True)
    shutil.copy(spec, "decomp/")
    shutil.copy(cfg, "decomp/")
    os.chdir("decomp")
    components = decomp(spec, cfg)
    os.chdir(dest_dir)

    # If there's only one component, there is no need to run multiple processes
    if len(components) <= 1:
        os.makedirs("mono", exist_ok=True)
        output = verify_capture_output(spec, cfg, "mono")
        print(output)
        return

    # Otherwise, build three recomp maps
    os.makedirs("mono", exist_ok=True)
    os.makedirs("cust_1", exist_ok=True)
    os.makedirs("cust_2", exist_ok=True)
    mono = ",".join(components) + "\n"
    recomp_1 = components[0] + "\n" + ",".join(components[1:]) + "\n"
    recomp_2 = ",".join(components[0:-1]) + "\n" + components[-1] + "\n"
    write("mono/custom_recomp.csv", mono)
    write("cust_1/custom_recomp.csv", recomp_1)
    write("cust_2/custom_recomp.csv", recomp_2)

    # Also run the naive mapping
    os.makedirs("naive", exist_ok=True)

    # # Run the verification processes in parallel
    output = run_multi_verif_with_parallel(dest_dir, spec, cfg, verbose)

def run():
    # Parse arguments and run the appropriate verification process
    if len(sys.argv) < 3 or len(sys.argv) > 5:
        print("usage: recomp-verify.py <file.tla> <file.cfg> [--cust|--naive|--parallel] [--verbose]")
        return

    spec = sys.argv[1]
    cfg = sys.argv[2]
    multi_process = "--parallel" in sys.argv
    cust = "--cust" in sys.argv
    naive = "--naive" in sys.argv
    verbose = "--verbose" in sys.argv

    if multi_process:
        verify_multi_process(spec, cfg, verbose)
    else:
        verify_single_process(spec, cfg, cust, naive, verbose)

run()
