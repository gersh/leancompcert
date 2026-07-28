# Prominent-project compatibility run

Date: 2026-07-28
Host: AArch64 Linux
CompCert: 3.17

This run tested unchanged upstream Lean sources at pinned revisions. A
successful translation-unit result means Lean emitted C, the normalizer made
only its named mechanical ABI-preserving rewrites, and CompCert compiled the
result to an AArch64 object. It does not mean every module or dependency in the
upstream repository was compiled by CompCert.

| Project | Pinned revision | Upstream baseline | Tested source | Generated C | Result |
|---|---|---:|---|---:|---|
| Lean/Lake 4.32.1 | `f054605aea4b840552cca2e725580bffd1e1b704` | installed release | `LakeMain.lean` | application entry | CompCert object linked and `--version` differentially matched |
| Batteries 4.32.0 | `023ce7d62a0531e22a5331e20b587817a80d49ff` | selected Lake module built | `Batteries/Data/HashMap/Basic.lean` | 106,656 bytes / 2,190 lines | CompCert object produced |
| Aesop 4.32.0 | `a7dbf0c63b694e47f425f3dcddbc0e178bb432d3` | all 174 Lake jobs built | `Aesop/Search/Main.lean` | 684,891 bytes / 16,347 lines | CompCert object produced |
| mathlib4 4.32.1 | `520045ab14e26149ee970e2e617ca04b09bde5d6` | 8,639 cached artifacts materialized | `Mathlib/Tactic/NormNum/Core.lean` | 932,283 bytes / 15,779 lines | CompCert object produced |
| doc-gen4 4.32.1 | `4df39adbbe5f699a7653f526e0e6faa2d34d404e` | all 194 Lake jobs built | `Main.lean` | 183,043 bytes / 4,474 lines | CompCert object linked and `--help` differentially matched |

Upstream repositories:

- <https://github.com/leanprover/lean4>
- <https://github.com/leanprover-community/batteries>
- <https://github.com/leanprover-community/aesop>
- <https://github.com/leanprover-community/mathlib4>
- <https://github.com/leanprover/doc-gen4>

## Compatibility findings

The first attempts exposed two additional instances of the same GNU-style
flexible-array initialization used by Lean's C emitter:

- static `lean_closure_object` values, including zero-capture closures;
- static `lean_array_object` and `lean_sarray_object` values, including empty
  arrays.

The normalizer now materializes a fixed-size anonymous struct when elements
exist and omits the flexible member and empty initializer when there are none.
The generated header, function pointer, arity, size, capacity, and element
field order are preserved. Unit tests cover captured and zero-capture closures
and populated and empty arrays.

## Executable checks

### Lake

The installed Lean 4.32.1 `LakeMain.lean` was built through
`lean-compcert build` and run with `--version`. The conventional and CompCert
executables had identical stdout, stderr, and exit status:

```text
Lake version 5.0.0-src+f054605 (Lean version 4.32.1)
```

### doc-gen4

Lake's recorded response file was copied, its conventional `Main.c.o.export`
entry was replaced with the CompCert-built `Main.o`, and the conventional
atomics adapter was added. All imported DocGen4, SQLite, Markdown, Unicode,
BibTeX, CLI, Lean, and system objects remained exactly those from the normal
Lake build.

The resulting mixed executable and upstream executable were both run with
`--help`. Both exited 0 and their 777-byte stdout and empty stderr were
byte-identical.

## Boundary and remaining work

These results show that sizable real Lean-generated application modules are
accepted by CompCert and that CompCert objects interoperate with ordinary Lake
objects at the tested ABI boundary.

They do not establish whole-repository CompCert builds. In particular:

- imported project modules in the executable checks remained conventionally
  compiled;
- doc-gen4's C/C++/SQLite/Markdown dependencies remained external;
- Aesop and mathlib execute much of the tested code as compiler
  metaprogramming, so translation-unit compilation is the relevant result;
- whole-package replacement needs a Lake facet that maps every module object
  into the existing link graph.
