#!/usr/bin/env python3
import os
import subprocess
import sys

root_dir = os.path.dirname(os.path.abspath(__file__))
tool = root_dir + "/bin/recomp-verify.jar"

def decomp(spec, cfg):
    """Decompose TLA+ specification into components without verification"""
    cmd_args = ["java", "-jar", tool, spec, cfg, "--decomp"]
    ret = subprocess.run(cmd_args, capture_output=True, text=True)
    if ret.returncode != 0:
        print(f"Error during decomposition: {ret.stderr}", file=sys.stderr)
        sys.exit(1)
    return ret.stdout.rstrip().split(",")

def main():
    if len(sys.argv) != 3:
        print("usage: decomp-wrapper.py <file.tla> <file.cfg>")
        print("Decomposes TLA+ specification into components without verification")
        sys.exit(1)
    
    spec = sys.argv[1]
    cfg = sys.argv[2]
    
    # Check if files exist
    if not os.path.exists(spec):
        print(f"Error: TLA+ specification file '{spec}' not found", file=sys.stderr)
        sys.exit(1)
    
    if not os.path.exists(cfg):
        print(f"Error: Configuration file '{cfg}' not found", file=sys.stderr)
        sys.exit(1)
    
    try:
        components = decomp(spec, cfg)
        print(f"\nTotal components: {len(components)}")
        print(f"Components: {','.join(components)}")
    except Exception as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

if __name__ == "__main__":
    main()