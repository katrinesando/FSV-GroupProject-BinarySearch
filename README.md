# Binary Search Tree Project

This repository contains a small Coq development for binary search trees. This project is done by Katrine Sandø and Christian Cordes.

## How to build

From the project root run:

```bash
make
```

This will compile the `.v` files and produce the corresponding `.vo`/`.vok` files.

If `make` fails due to Coq load-path errors you can compile the files individually with `coqc` (fallback):

```bash
coqc -Q . project_lib project_lib.v
coqc -Q . BstProject BST.v
coqc -Q . BstProject BSTInsert.v
coqc -Q . BstProject BSTExtra.v
```

Notes:
- The `-Q . <logical>` arguments map the current directory to a logical Coq path used inside the files. The project uses two logical paths: `project_lib` and `BstProject`.
- The `_CoqProject` file in the repo lists the files and the `-Q` mappings that `coq_makefile`/`make` uses. If you edit file names, update `_CoqProject` accordingly.

## Compatibility shim (why `NPeano` may appear)

Older Software Foundations-style code used a module named `NPeano` and functions like `beq_nat`. Newer Coq versions use the `Nat` module and `Nat.eqb` and the file was therefore updated.

## Troubleshooting

- "Cannot find a physical path bound to logical path ..." — this means a `-Q` mapping or filename listed in `_CoqProject` is incorrect. Inspect `_CoqProject` and ensure it contains lines like `-Q . project_lib` and `-Q . BstProject`, and that the file list matches actual filenames (e.g. `BSTExtra.v` vs `BSTExtras.v`).
- If `beq_nat` or similar names are reported as missing, the `NPeano.v` shim is present to provide those names; make sure `NPeano.v` is present and listed in `_CoqProject`.
- If `make` still fails, try compiling the individual files with the `coqc -Q` commands shown above. The error output will often indicate which file or mapping is missing.

## Example quick commands

Run the build and show Coq errors (if any):

```bash
make    # builds everything
# or individual file if make fails
coqc -Q . BstProject BST.v
```