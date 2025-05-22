# C2Validator

## Introduction

This is the source code for my master's thesis at **KTH Royal Institute of Technology** in collaboration with **Oracle's Java Platform Group**. This project aims to experiment translation validation for HotSpot C2 compiler. For more details, please refer to my master's thesis on [DIVA]() or [PDF]().

## Usage

### Build and dependency

This tool is written in [LEAN](https://lean-lang.org) and should be built with its package manager `lake`. To start using, you need to use [my modified JVM](https://github.com/TerenceNg03/jdk-c2-validation) built with fast-debugging enabled. The tool also requires the most recent version of [Z3 Prover](https://github.com/Z3Prover/z3).

### Command Line Interface

Run the following command at the root directory to get help.
```sh
lake exe Main --help
```

### Verify a Java File
Make sure you have a debug build `java` and `z3` command available.
```sh
lake exe Main <FILE_TO_VERIFY>
```