# Frama-C ARMv8

[![Build Status](https://github.com/kth-step/frama-c-arm8/actions/workflows/build.yml/badge.svg?branch=master)](https://github.com/kth-step/frama-c-arm8/actions/workflows/build.yml)

Frama-C plugin for automatically generating HOL4 ARMv8 contracts from ACSL contract annotations.

### Requirements

1. Linux/WSL
2. OCaml and dune installed 
3. Frama-C installed from https://git.frama-c.com/pub/frama-c
4. HOLBA installed from https://github.com/kth-step/HolBA/tree/master

### Building
1. `git clone https://github.com/VincentLagerros/frama-c-arm8`
2. `cd frama-c-arm8`
3. Run with `dune build --profile release && dune exec --profile release -- frama-c -arm8 "[C file]" -arm8-type="holba"` or alternatively `./run.sh` 

### Testing

Generated hol files can test build by editing the `spec_arm8Script.sml` template.

1. `source ~/HolBA/env.sh`
2. `cd ~/frama-c/src/plugins/frama-c-arm8/hol-template`
3. `Holmake` 

### Flags

`-arm8` Enables the plugin

`-arm8-output <file>` Specify the output destination

`-arm8-type <holba|hol|py|dbg>` Specify the output format, default is HolBA (`holba`)
* `holba`: Prints Hol4 code, without helper functions
* `hol`: Prints Hol4 code, with helper functions 
* `py`: Prints Python code with Z3
* `dbg`: Debug output 

`-arm8-acsl` Enables pretty printing of the ensures/requires clause as a HOL comment

`-arm8-globals` Enables globals variables to be used in a contract, but does not autogenerate the code for the globals
