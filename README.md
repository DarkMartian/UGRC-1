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

The tool has been tested against the **DaCapo benchmark suite** (specifically the `sunflow` workload) using TamiFlex reflection logs to handle reflective calls accurately.

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
│   └── checking1/                   # Instrumented class output (auto-created)
├── out/                             # TamiFlex-dumped class files for the benchmark
├── dacapo-9.12-MR1-bach.jar         # DaCapo benchmark JAR
└── README.md
```

---

## How It Works

The analysis runs as a **Soot `wjtp` (whole-Jimple transformation pack) pass** and proceeds through the following stages:

### 1. Class Hierarchy Construction
Builds `parent` and `child` maps for all application classes, and resolves overriding methods across the inheritance hierarchy using `overloadedMethods`.

### 2. Call Graph Traversal & Points-To Analysis
Starting from `main`, traverses the call graph constructed by **SPARK** (Soot's flow-insensitive, context-insensitive points-to analysis). For each method, it:
- Maps each `JimpleLocal` to the set of abstract heap objects it may point to (`local2object`)
- Maps each abstract heap object back to the locals that alias it (`object2local`)
- Tracks field edges between heap objects (`object2object`, `object2object2`)
- Records which objects each method **creates** (`methodCreates`) and **uses** (`methodUses`)

### 3. Control-Flow Graph (CFG) Construction
Builds per-method intra-procedural CFGs using `ExceptionalUnitGraph`. The CFG is then simplified by `simplifyMethodGraphs()`.

### 4. Context-Insensitive Object Liveness Analysis
`performContextInsensitiveAnalysis()` computes a **dataflow fixed-point** over the method call graph. For each method `M`, it determines:
- `LiveObjIn[n]` — objects live before statement `n`
- `LiveObjOut[n]` — objects live after statement `n`
- `methodKilled[M]` — objects that are created or flow into `M` but do **not** escape

### 5. Safe-Local Null Insertion
For each method with a non-empty kill set:
- **Safe locals** are identified: non-parameter locals whose entire points-to set is within the kill set
- Using `SimpleLiveLocals`, the last use of each safe local is found
- A `local = null` assignment is inserted **immediately after** the last use, enabling the GC to collect the object sooner

### 6. Field-Link Freeing (`freeLink`)
For objects that die within a method:
- **At last use (`freeLinkAtLastUse`):** If a field link `O'.f → O` is uniquely determined (only one object points to `O` via `f`), the field is nulled at the last-use point
- **At method exit (`freeLinkAtExit`):** Ambiguous field links (multiple sources) are freed at return statements to prevent reference cycles

Field paths (e.g., `l.f1.f2`) are resolved by `findFieldPaths()`, and null assignments are emitted by `nullPath()`.

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
java -javaagent:poa.jar -jar dacapo-9.12-MR1-bach.jar sunflow
```
This produces the `out/` directory (dumped classes) and `sunflow.log` (reflection log). Place them as shown in the project structure above.

### 3. Configure benchmarks in `Driver.java`
Each entry in the `BENCHMARKS` array has four fields:

```java
static final String[][] BENCHMARKS = {
    {
        "out",                        // [0] Path to TamiFlex-dumped classes
        "Harness",                    // [1] Main class (always "Harness" for DaCapo)
        "tests/reflogs/sunflow.log",  // [2] TamiFlex reflection log
        "sunflow"                     // [3] Label used in output file names
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
1. Filter `$$Lambda$` entries from the TamiFlex log (runtime-generated classes with no stable `.class` file on the classpath)
2. Configure Soot (whole-program mode, SPARK call graph, phantom refs enabled)
3. Run the `wjtp.mhpA` transformation pass
4. Write results to `tests/results/<label>_result.txt`
5. Write instrumented class files to `tests/checking1/<label>/`

---

## Output

| File/Directory | Description |
|---|---|
| `tests/results/<label>_result.txt` | Full analysis log including method bodies after null-insertion |
| `tests/checking1/<label>/` | Instrumented `.class` files with null assignments injected |

The result file contains the final Jimple representation of every analysed method body, showing the inserted `null` assignments.

---

## Debug Mode

Set the static flag in `CalIGraphAnalysis.java` to enable verbose output:

```java
static boolean debug = false;  // ← change to true
```

With debug enabled, the analysis prints:
- Class hierarchy maps (`parent`, `child`)
- Overriding method chains
- `local2object` and `object2local` maps
- Per-method CFGs before and after simplification
- Object liveness sets (`in`/`out`) at every statement
- Kill sets and safe locals per method
- Every inserted null/navigation statement

---

## How to Create a GitHub Repository

Follow these steps to publish this project on GitHub entirely through the browser — no command line needed.

### Step 1 — Create a GitHub account
Go to [https://github.com](https://github.com) and sign up if you don't already have an account.

### Step 2 — Create a new repository
1. Click the **"+"** icon in the top-right corner of GitHub
2. Select **"New repository"**
3. Fill in the details:
   - **Repository name:** e.g., `callgraph-liveness-analysis`
   - **Description:** e.g., `Static analysis tool using Soot for object liveness and GC-friendly null insertion`
   - **Visibility:** Choose **Public** or **Private**
   - Check **"Add a README file"** (you can replace it with this file later)
   - Optionally add a `.gitignore` → select **Java** from the dropdown
   - Optionally choose a **License** (e.g., MIT)
4. Click **"Create repository"**

### Step 3 — Upload your files
1. Inside your new repository, click **"Add file" → "Upload files"**
2. Drag and drop the following files:
   - `Driver.java`
   - `CalIGraphAnalysis.java`
   - `README.md` (this file)
3. Add a commit message like `Initial commit: add analysis source files`
4. Click **"Commit changes"**

### Step 4 — Organise into folders (optional)
GitHub's web UI cannot create folders directly, but you can create a file inside a folder path. When uploading, type a path like `src/testing/Driver.java` in the filename field to automatically create the folder structure.

### Step 5 — Clone the repository locally (optional)
Once the repo is created, copy the repository URL (green **"Code"** button → HTTPS) and run:
```bash
git clone https://github.com/<your-username>/callgraph-liveness-analysis.git
```
You can then add files, commit, and push using standard Git commands.

---

## Key Classes & Methods Summary

| Class / Method | Purpose |
|---|---|
| `Driver` | Configures Soot options, filters TamiFlex log, launches analysis |
| `CalIGraphAnalysis` | Main `SceneTransformer`; orchestrates all analysis phases |
| `iterateCallGraph` | Traverses the call graph, populates PTA maps |
| `iterateCFG` | Builds per-method CFGs and object create/use sets |
| `performContextInsensitiveAnalysis` | Fixed-point object liveness dataflow |
| `computeObjectLiveness` | Per-method `LiveObjIn` / `LiveObjOut` computation |
| `freeLink` | Inserts null statements for dead field links |
| `freeLinkAtLastUse` | Nulls unique field links at last-use point |
| `freeLinkAtExit` | Nulls ambiguous field links at method return |
| `findFieldPaths` | Resolves access paths (`l.f1.f2`) to a heap object |
| `nullPath` | Emits Jimple null-assignment statements for a field path |
