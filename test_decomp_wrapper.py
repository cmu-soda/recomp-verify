#!/usr/bin/env python3
import subprocess
import sys
from pathlib import Path

def run_decomp(spec_dir, spec_name, use_python=True):
    root = Path(__file__).parent
    if use_python:
        cmd = ["python3", str(root / "decomp-wrapper.py"), f"{spec_name}.tla", f"{spec_name}.cfg"]
    else:
        cmd = ["java", "-jar", str(root / "bin/recomp-verify.jar"), f"{spec_name}.tla", f"{spec_name}.cfg", "--decomp"]
    
    result = subprocess.run(cmd, cwd=spec_dir, capture_output=True, text=True, timeout=30)
    if result.returncode != 0:
        return None
    
    if use_python:
        for line in result.stdout.split('\n'):
            if line.startswith('Components: '):
                return [c.strip() for c in line.replace('Components: ', '').split(',')]
    else:
        return [c.strip() for c in result.stdout.strip().split(',')]

def main():
    verbose = "--verbose" in sys.argv or "-v" in sys.argv
    
    root = Path(__file__).parent
    benchmarks = root / "benchmarks/tla"
    
    specs = []
    for cfg_file in benchmarks.rglob("*.cfg"):
        if cfg_file.name != "no_invs.cfg" and (cfg_file.parent / f"{cfg_file.stem}.tla").exists():
            specs.append((str(cfg_file.parent), cfg_file.stem))
    
    failures = []
    for spec_dir, spec_name in sorted(specs):
        java_components = run_decomp(spec_dir, spec_name, use_python=False)
        python_components = run_decomp(spec_dir, spec_name, use_python=True)
        
        rel_path = Path(spec_dir).relative_to(root)
        
        if verbose:
            status = "✓" if java_components == python_components else "✗"
            print(f"{status} {rel_path}/{spec_name}")
            print(f"  Java:   {java_components}")
            print(f"  Python: {python_components}")
        
        if java_components != python_components:
            failures.append(f"{rel_path}/{spec_name}: Java={java_components}, Python={python_components}")
    
    if failures:
        print("FAILURE :(")
        print(f"{len(failures)} failures:")
        for failure in failures:
            print(f"  {failure}")
        sys.exit(1)
    else:
        print(f"SUCCESS :) {len(specs)} specs passed")

if __name__ == "__main__":
    main()