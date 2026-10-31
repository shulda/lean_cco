> Historical preparation report from `shulda/cycle_constrainedness` at
> `30abcca888c0348f6b1ce5a32581b9250e5f7ae5`. Private/held/Work status and
> reproduction commands below refer to that source snapshot. Current public
> allocation and compiled provider status follow main and the live STATE.
> See [public release context](coordination/releases/B049-B064/README.md).

# Human-article coverage of formalization preparation

Frozen source `490c3f36d85db5a0b3ced0598e6c431825254ec5`; after B062–B064, 29 October 2026.

**342/342 catalogue results (100%)** mapped to human proof packages: 56 modules, 2,509 claims, 173 auxiliary equations and 64 private packages.
Coverage includes repaired/qualified source readings and explicit conditional interfaces. It is not Lean completion or independent correctness/global certification.

| Human article | Own prepared results | Result count | Original proof bytes |
|---|---:|---:|---:|
| Foundations I | 63/63 | 100.0% | 100.0% |
| Foundations II | 52/52 | 100.0% | 100.0% |
| Foundations III | 49/49 | 100.0% | 100.0% |
| EPPA | 52/52 | 100.0% | 100.0% |
| Ramsey I | 45/45 | 100.0% | 100.0% |
| Ramsey II | 44/44 | 100.0% | 100.0% |
| Ramsey III | 29/29 | 100.0% | 100.0% |
| SIR | 8/8 | 100.0% | 100.0% |

Original attached proof TeX: **592,577/592,577 bytes (100%)**. Statement/proof spans are deduplicated; sidecar expansions are excluded. Every frozen result environment, including unlabelled results, is resolved by its exact catalogue identity.

B062 adds eight exact trace/quotient results, B063 four automatic-core results and B064 eight final unfiltered-EP results. Ramsey III is now 29/29 locally prepared. There are no remaining unmapped result environments.

The [completion review](PREPARATION_COMPLETION_REVIEW.md) lists source corrections, held broad readings, six unchanged external bindings and receiving priorities. The catalogue coverage does not silently remove those obligations. In particular the TV1 RAW/STRONG proof-equation correction and B036 function/restriction gate remain, B062 corrects a RAW-calculus reference, and B064 explicitly completes the finite-source/zero-coordinate recipe. Overall EPPA stays source-relative.

Reproduce `python tools/measure_preparation_coverage.py --root .`. All 93 active source fingerprints and one previously retained legacy provider are checked (94 total). Previous 61 allocations, public Work/CI/policy and separate human edition are unchanged. Private B020–B064 remain held.
