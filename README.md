# CallGraph & Object Liveness Analysis

A static program analysis tool built on the [Soot](https://github.com/soot-oss/soot) framework that performs whole-program call graph construction, points-to analysis, object liveness tracking, and automatic null-insertion to assist the Java garbage collector (GC) in reclaiming memory earlier.

---

## Table of Contents

- [Overview](#overview)
- [Project Structure](#project-structure)
- [How It Works](#how-it-works)
- [Prerequisites](#prerequisites)
- [Setup & Configuration](#setup--configuration)
- [Running the Analysis](#running-the-analysis)
- [Output](#output)
- [Debug Mode](#debug-mode)
- [How to Create a GitHub Repository](#how-to-create-a-github-repository)

---

## Overview

This tool analyses compiled Java bytecode (`.class` files) to determine the lifetime of heap objects across method boundaries. When an object is determined to be dead (no longer reachable after a given program point), the tool **automatically inserts null assignments** into the bytecode so the GC can reclaim that memory as early as possible—without waiting for the variable to fall out of scope.

The tool has been tested against the **DaCapo benchmark suite** (specifically `avrora`, `luindex`, `lusearch-fix`, `h2`, `xalan` workload) using TamiFlex reflection logs to handle reflective calls accurately.

---

## Project Structure

```
.
├── src/
│   └── testing/
│       ├── Driver.java              # Entry point; configures and launches Soot
│       └── CalIGraphAnalysis.java   # Core analysis pass (SceneTransformer)
├── tests/
│   ├── reflogs/
│   │   └── sunflow.log              # TamiFlex reflection log for sunflow
│   ├── results/                     # Analysis output files (auto-created)
│   └── output/                      # Instrumented class output (auto-created)
├── out/                             # TamiFlex-dumped class files for the benchmark
├── dacapo-9.12-MR1-bach.jar         # DaCapo benchmark JAR
└── README.md
```

---

## Prerequisites

| Requirement | Version |
|---|---|
| Java JDK | 8 (required by Soot and DaCapo) |
| Soot | 4.x (on classpath) |
| DaCapo Benchmark JAR | `dacapo-9.12-MR1-bach.jar` |
| TamiFlex | For generating reflection logs (`reflogs/`) |

> **Note:** The JDK must be Java 8. Soot's SPARK analysis and the DaCapo benchmarks are not compatible with newer JDK versions without additional configuration.

---

## Setup & Configuration

### 1. Add dependencies to your classpath
Ensure the following JARs are on your build/run classpath:
- `soot-<version>-jar-with-dependencies.jar`
- `dacapo-9.12-MR1-bach.jar`

### 2. Prepare the benchmark classes
Run the target benchmark under **TamiFlex** to dump loaded classes and generate a reflection log:
```bash
java -javaagent:poa.jar -jar dacapo-9.12-MR1-bach.jar avrora
```
This produces the `out/` directory (dumped classes) and `avrora.log` (reflection log). Place them as shown in the project structure above.

### 3. Configure benchmarks in `Driver.java`
Each entry in the `BENCHMARKS` array has four fields:

```java
static final String[][] BENCHMARKS = {
    {
        "out",                        // [0] Path to TamiFlex-dumped classes
        "Harness",                    // [1] Main class (always "Harness" for DaCapo)
        "tests/reflogs/avrora.log",  // [2] TamiFlex reflection log
        "avrora"                     // [3] Label used in output file names
    },
};
```

Add more entries to analyse additional benchmarks.

---

## Running the Analysis

Compile both source files with Soot on the classpath, then run:

```bash
javac -cp .;soot.jar;dacapo-9.12-MR1-bach.jar src/testing/*.java -d bin/
java  -cp bin;soot.jar;dacapo-9.12-MR1-bach.jar testing.Driver
```

> On Linux/macOS, replace `;` with `:` in classpath separators.

The driver will:
1. Configure Soot (whole-program mode, SPARK call graph, phantom refs enabled)
2. Run the `wjtp.mhpA` transformation pass
3. Write results to `tests/results/<label>_result.txt`
4. Write instrumented class files to `tests/output/<label>/`

---

## Output

| File/Directory | Description |
|---|---|
| `tests/results/<label>_result.txt` | Full analysis log including method bodies after null-insertion |
| `tests/output/<label>/` | Instrumented `.class` files with null assignments injected |

The result file contains the final Jimple representation of every analysed method body, showing the inserted `null` assignments.

---

---h |
