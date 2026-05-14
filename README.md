# TLA+ Model Checking Guide

This repository contains a TLA+ specification for **MCAS**. To verify the specification, we use the **TLC Model Checker** with a dedicated model configuration (`MCAS.tla` and `MCAS.cfg`).

## Prerequisites

You need the TLA+ tools (specifically `tla2tools.jar`) installed on your system. You can download it from the [official TLA+ releases](https://github.com/tlaplus/tlaplus/releases).

## File Structure

*   `MCAS.tla`: The main specification module containing the system logic.
*   `MCAS.cfg`: The configuration file defining constants, invariants, and properties for TLC.

The same structure is defined for TreeCAS module, for checking this one you need to run command with operand `TreeCAS.tla` file.

## How to Run the Model Checker

To check the specification using the command line, navigate to the project directory and run:

```bash
java -cp tla2tools.jar tlc2.TLC MCAS.tla
java -cp tla2tools.jar tlc2.TLC TreeCAS.tla
```

## Common Options

Use all available CPU cores to speed up the check:

```bash
java -cp tla2tools.jar tlc2.TLC -workers auto MCAS.tla
java -cp tla2tools.jar tlc2.TLC -workers auto TreeCAS.tla
```

## Expected Output

TLC will analyze the state space defined in `MCAS.cfg`. If the specification is correct, you should see:

```text
Model checking completed. No error has been found.
```

If an invariant is violated, TLC will provide a Error-Trace showing the sequence of steps that led to the failure.
