# Independent corroborating control of current-source cache closure

Actual reviewer: `/root/full_control_resume`, review only. I authored no
production code, tests, workflow changes or implementation decisions for this
infrastructure. The separate review-only `/root/full_control_resume/triangle_control`
checked the helper and workflow semantics. This report is corroboration, not a
live STATE approval under another actor's identity.

## Final exact-source disposition

**No remaining source/control blocker found** at frozen author leaf
`acff2244bbf193140d40a2069f2cda7542a3063d`, as integrated in PR #9 exact head
`ce93b92c70a36195979263e9fd578943edc53214`. This supersedes only the pending
disposition, preserving the rejected `285da06` finding and all limits below.

I independently fetched the PR commit metadata: its parent is accepted main
`4206ff772cc3ee334fe530b55dbb0afe8174dfd4` and its tree is
`7db06ece7ddec278e8a6a84bdeb4ee88938cbf81`. That tree equals local
`e1dded510eb9440329a4369b41525d47e661331c`. All six executable infrastructure,
workflow and test files are byte-identical to the frozen author leaf, including
the previously reviewed metadata/hash helpers. Compared with accepted main,
there is no change to CCO source, mathematical TeX, manifest or toolchain;
the two additional submission-document changes record accepted status.

Final checks independently completed:

- All **67 Python tests** pass both on the final combined tree and in my
  review worktree with the exact frozen infrastructure files.
- Repeated the real nested-directory alias/self-loop fixture against the
  frozen guard: valid output checks **158/158**; the appended-byte child is
  rejected for its exact descriptor mismatch. The earlier false pass is closed.
- Independently exercised the final clean helper's `lib`, `lib/lean` and `ir`
  parent-alias preflight: each refuses before deletion, preserving owned and
  external sentinels. The final selective-repair code preflights every affected
  library and IR parent before any unlink, switching nested directory aliases
  to safe whole-namespace clearing. The real-filesystem tests cover both paths.
- In the independently fresh-built B003 review environment, the exact final
  infrastructure passes rehash build **1037**, complete guard **158/158**,
  further pinned build/official executable audit **2069** standard-three
  declarations, and final complete guard **158/158**. Project outputs were
  originally built fresh, with only external packages symlinked.
- In the actual final combined worktree, my additional read-only complete
  guard passes **317/317**, the official pinned audit independently sees
  **3657** declarations with only `propext`, `Classical.choice`, `Quot.sound`,
  and the subsequent complete guard again passes **317/317**. Its compiler
  build was owned and reported by the coordinator; I do not relabel that build
  as my independent fresh compilation.
- The frozen guard still rejects the untouched original AgeAP witness for the
  root import-header mismatch. The same 297-file digest, byte sizes and mtimes
  recorded below remain unchanged after this final check.

The review-only helper independently inspected all five changed files at exact
`acff2244` and found no blocker, including the final safe-parent preflight.
I wrote only reports; the implementation author supplied all production fixes.
Exact-head remote CI, the registered reviewer's personal formal approval and
green resulting-main verification still gate deployment/acceptance.

## Initial exact-head finding

Reviewed `285da06dcf14a69c532449174172de09c92c9302`, based on accepted B003
main `68322c7`. Its normal build layout passed, and it correctly rejected the
preserved AgeAP failure witness. I nevertheless withheld a positive disposition:
the recursive output-trace discovery missed nested symlinked build directories.

The controlled fixture `cco-cache-alias-fixture` used exact source `285da06`
and an intentional copy of my independently fresh, correct project outputs.
Baseline complete verification checked 158 olean parts and 158 source modules.
Appending a zero byte to `CCO/StrongExact/Examples.olean` made the ordinary
layout fail for exactly its output-descriptor mismatch. Moving its containing
`StrongExact` directory to an absolute alias target and symlinking the original
directory to that target made the same corrupted output incorrectly pass:
33 byte-checked parts, although 158 current source modules were still checked.
The source/header helper could read the module correctly through that alias.
The fixture was restored; the original failure witness was never modified.

The implementation author subsequently supplied a finite-source-trace repair.
The guard obtains the compiler-derived current source closure first, opens each
exact corresponding trace path, and unions those paths with the existing
orphan-trace scan. It does not recursively follow directory symlinks. My real
fixture then accepted a valid nested directory alias plus an actual self-loop
with all 158 parts checked, and rejected the corrupted Examples output for its
exact descriptor mismatch. Individual artifact aliases also passed with 158
parts. The author wrote this repair; I only reviewed and exercised it.

## Semantic review

- The toolchain-only helper reads current source headers with pinned
  `Lean.parseImports'`, including implicit imports, complete ordered import
  records/flags and module mode. It reads actual compiled headers with
  `Lean.readModuleData`, without importing CCO artifacts.
- Current source-reachable CCO modules are enumerated independently of the
  compiled root's old import closure. Every such module gets source-input,
  compiled-header and effective audit-resolution checks. Source hashes use
  pinned `Lake.Hash.ofText`; output hashes use actual bytes through pinned
  `Lake.computeFileHash`, rather than trusting hash sidecars.
- The trace source-input comparison permits relocation between worktrees but
  requires the same source-relative filename and one unambiguous input entry.
  Changed proof bodies with unchanged imports and old source input hashes are
  rejected. Malformed metadata or unreadable outputs fail closed.
- The effective `Lean.findOLean` result must identify the same checked file,
  with both sides resolved. Valid aliases of one artifact are accepted;
  a genuinely different artifact is rejected. The finite trace repair covers
  source-reachable children behind nested directory aliases without following
  symlink loops.
- Cold missing modules require no pre-build repair. `--require-complete`
  requires every current source-reachable module and its trace after the build.
  In an ordinary owned directory, targeted invalidation removes the identified
  module's generated library/IR outputs and preserves consistent siblings.
  Aliased directory cases use the safe whole-namespace clearing described above;
  source files and external alias targets remain preserved.
- Workflow ordering is repair, actual-input-hash compiler build,
  complete-closure guard, pinned official audit, final complete-closure guard.
  The revised workflow has one bounded clean-project-output fallback when the
  first post-build complete check fails; it must rebuild and pass that check
  before auditing. The clean helper removes CCO root/namespace library and IR
  outputs, preserves packages/non-CCO/source, and unlinks aliases without
  following them. Persistent failure remains fatal. The audit's own additional
  `lake build` is why the last check is necessary. The allowlist is unchanged.
  Pinned Lake supports the explicit artifact-cache disablement and `--rehash`;
  the latter recomputes actual input hashes instead of trusting sidecars.
- This is a material bytes/source-input/import-closure check, not a proof-body
  regeneration oracle. Arbitrarily fabricated current-input traces plus matching
  headers are not independently certified to represent current proof bodies.
  The ordinary compiler build and transitive audit remain mandatory.

## Preserved failure witness and repair limits

I ran the new guard externally from the unchanged `cco-review-ageap` checkout
at `5ff0881ee48d74823350a2820ac37c5bdd488d29`, with no repair option. It exited
1 specifically for `CCO.trace` compiled imports differing from the current
source header. A before/after snapshot of all 297 source/build files recorded
SHA-256, size and nanosecond mtime; every entry was unchanged. The aggregate
snapshot digest was `f619dd5217cd4ce4667720b6aa50523156c5abc09fd327ece92d67197699e784`.

A separate intentional copy of that witness independently reproduced the
failure: the old byte-only guard accepted 33 parts, while `import CCO;
#check CCO.AgeAP` failed with unknown identifier. Targeted repair removed
exactly eight generated root outputs and preserved every child byte and mtime.
The subsequent nominal successful 776-job build nevertheless produced/restored
the same stale root SHA-256 `73e6933ae60ab4b9ad258006611831a4c804d1f854e15ffd4df18e26e0a7bccd`.
The complete guard correctly continued to reject it. A further copied-fixture
attempt with explicit rehashing and artifact-cache disablement also remained
rejected. This is fail-closed evidence, not a successful recovery claim or
an explanation of how the stale snapshot was first produced.

The new bounded clean fallback subsequently recovered this same copied fixture:
the helper discarded ten generated CCO trees/root files, the artifact-cache-
disabled `lake --rehash build` completed 776 jobs including an actual root
compile, the complete check passed 33/33 and `import CCO` exposed `CCO.AgeAP`.
This establishes recovery of that controlled copy, not universal recovery or
the initiating cause. The original witness remained untouched.

A separate known-good controlled child-byte corruption did recover: repair
removed exactly the eight Examples generated outputs, changed or added no
other artifacts, and preserved all other modules. The subsequent 1037-job
build succeeded, complete verification returned 158/158, and explicit root
imports exposed `CCO.AgeAP` and `toy_two_edge_supported` again. No source or
production test file was modified in these artifact fixtures.

## Validation record

At exact initial head `285da06`, a new worktree with only the pinned external
packages symlinked and no copied CCO project outputs passed fresh build
**1037 jobs**, all **63 Python tests**, and complete verification **158/158**.
The same worktree passed a further pinned build plus the official pinned
axiom-audit executable: **2069 CCO declarations**, only `propext`,
`Classical.choice`, `Quot.sound`. Complete guards immediately before and after
that build/audit passed 158/158. These normal-layout successes did not override
the concrete nested-alias finding above.

The initiating cause of the original stale-generation state remains unproved.
No claim is made that CAS, copying, mtime, hashing or the compiler caused it.
Remote exact-head CI, formal adoption by the registered reviewer and resulting
main verification remain coordinator responsibilities.
