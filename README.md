# Recomp-Verify - FMCAD 2024

Recomp-Verify is a model checker for safety properties in TLA+.
The tool is the research prototype from our FMCAD 2024 paper [Recomposition: A New Technique for Efficient Compositional Verification](https://iandardik.github.io/assets/papers/recomp_fmcad24.pdf).

## Getting Started

To use the tool, simply clone the repo.
Building this project requires building and importing a branch of the [FORTIS](https://github.com/iandardik/LTS-Robustness/tree/decomp) repository, so, for convenience, we have pre-built all Jar files.
To run the model checker you only need to run the python script ``recomp-verify.py`` in the root level directory.
To check if the tool works on your local machine, try running the pyv-lockserv-20 benchmark.
For example:
```
$ cd recomp-verify/benchmarks/tla/lockserv/20/
$ python3 ../../../../recomp-verify.py lockserv.tla lockserv.cfg --cust
D0 = C1 || C2 || C3 || C4
E0 = T4
n: 5
m: 1
WARNING: sun.reflect.Reflection.getCallerClass is not supported. This will impact performance.
k: 0
Total # states checked: 61
Property satisfied!
```

## Usage Menu

Here is the usage menu for the tool:
```
recomp-verify.py <file.tla> <file.cfg> [--cust|--naive|--parallel] [--verbose]
```
There are four modes for running the tool:
1. Default mode (no flags). In this mode, the model checker uses heuristics to guess a good recomposition map.
1. Naive mode (--naive flag). In this mode, the model checker uses the identity recomposition map, i.e. no components are recomposed.
1. Custom mode (--cust flag). In this mode, you can specify a custom recomposition map in a file named ``custom_recomp.csv``. Please see the benchmarks for examples.
1. Parallel mode (--parallel flag). This mode runs four different recomosition strategies in parallel. Beware: you may need to kill zombie processes in this mode (see Known Issues).

## System Requirements

The model checker has been tested with the following version of Java:
```
java 18.0.2.1 2022-08-18
Java(TM) SE Runtime Environment (build 18.0.2.1+1-1)
Java HotSpot(TM) 64-Bit Server VM (build 18.0.2.1+1-1, mixed mode, sharing)
```
and the following version of Python:
```
Python 3.9.6
```
The model checker has been tested exclusively on a MacBook Pro with an M1 processor and 32GB of RAM.

## Known Issues
- The Python script must be run in the same directory that contains the TLA+ file that is being model checked.
- The tool does not give good error messages when a TLA+ spec is malformed; a work-around is to run TLC on a spec for a better error message to see why it is malformed.
- The model checker works on a subset of the TLA+ language; please see our paper for the precise definition of this subset.
- When running in parallel mode, the script will not clean up all processes that it spawns. You may need to manually kill processes that the script spawns using ``kill -9``.
