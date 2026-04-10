# TLA+ Model Checking Guide

This repository contains a TLA+ specification for **MCAS**. To verify the specification, we use the **TLC Model Checker** with a dedicated model configuration (`MC.tla` and `MC.cfg`).

## Prerequisites

You need the TLA+ tools (specifically `tla2tools.jar`) installed on your system. You can download it from the [official TLA+ releases](https://github.com/tlaplus/tlaplus/releases).

## File Structure

*   `MCAS.tla`: The main specification module containing the system logic.
*   `MC.tla`: The model-specific module that extends `MCAS` for checking.
*   `MC.cfg`: The configuration file defining constants, invariants, and properties for TLC.

## How to Run the Model Checker

To check the specification using the command line, navigate to the project directory and run:

```bash
java -cp tla2tools.jar tlc2.TLC MC.tla
```

## Common Options

Use all available CPU cores to speed up the check:

```bash
java -cp tla2tools.jar tlc2.TLC -workers auto MC.tla
```

## Expected Output

TLC will analyze the state space defined in `MC.cfg`. If the specification is correct, you should see:

```text
Model checking completed. No error has been found.
```

If an invariant is violated, TLC will provide a Error-Trace showing the sequence of steps that led to the failure.
