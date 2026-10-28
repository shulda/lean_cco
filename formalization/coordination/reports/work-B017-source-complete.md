# B017 completed source packet — C01–22

Owner/actual implementer: `/root/b017_kernel`. All C01–22 mathematical
obligations are proved, including their actual-source provider instances.
There is no open provider, new axiom, changed premise or mathematical-contract
change. The full claim-to-Lean map and hypothesis firewalls are in
`../submissions/B017.md`.

## Frozen implementation

- Accepted starting main: `7169a805d337110e6dad4e6d0636e950b31f157d`.
- Source freeze: `5917c29433db6c3f1385ca8b3bced9173ad807ea`.
- Source-freeze git tree: `ab6110f55c61d08a03be469ed321f000b1615ad6`.
- 32 new public modules under `CCO/FiniteKernel/`; every module is imported
  additively by `CCO.lean`, whose complete accepted base prefix is preserved.
- The standalone root closure has 461 project modules. It imports no
  unaccepted B009/B015 implementation.
- Source pin remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
  Literal source-blob checks returned
  `e47d0d2de416e03dd0207dc56a581088da78b74c` for
  `sections/finite_packet_kernel_constraints.tex`, and
  `078017a03e1d6f62088fb17fb6e31bce4f6e8ef6` for
  `sections/simultaneous_typed_exact_quotients.tex`.
- The pinned toolchain, locked manifest, lakefile, package contract,
  finite_kernel module/notes, public policy and accepted shared APIs are
  unchanged relative to the accepted base.

The source freeze follows the substantive mathematical closure
`eaea2a1037e072bb027ca2f35684cdcfb03b6d5d`. The only subsequent production
change was the targeted `Mathlib.Data.Finite.Prod` import in the actual local
pair-group consumer, needed for its explicit finite instance. No shared
foundation was broadened and no proof, signature or premise changed.
Later commits containing this report/map are documentation only.

## Actual conclusions and boundaries

The general branch acts on the FULL automorphism group of the original
directed unary/binary relational structure. Actual invariant finite classes
partition ALL points. The assembled product tuple is an actual permutation
of those points, not an uninstantiated provider. Global patching preserves
unary instances, internal binary loops and both ordered cross directions;
it requires neither homogeneity nor countability.

The compact-projection premise requests a solution over EVERY finite
superset extending the SAME prescribed tuple. The finite-continuation
algorithm is explicitly proved using a maximum finite failure bound and Nat
recursion, then instantiated on actual finite solution levels. Actual
owner-named homogeneity remains a distinct optional hypothesis, never inferred
from the reduct's homogeneity.

The linear branch derives intrinsic-coordinate finiteness and linearity from
the actual finite groups and given group representations. The actual local
pair annihilators generate the global row space. C11 is the explicit countable
one-vector functional extension and directed union, without Zorn or a
separation black box. C12 is an explicit finite-basis bidual sum followed by
direct-sum evaluation, yielding a FULL product tuple. The finite dual embedding
is literal zero extension, and the width-two criterion retains every ACTUAL
singleton/pair marginal, including singleton binding restrictions. Empty
tests/projections, zero-dimensional factors and sets of cardinality at most
two have explicit consumers. The final consumer returns an actual global
owner-kernel automorphism under the exact row-space equality.

The independent named-axis branch proves actual full-group finite projection
on whole finite named sorts, allowing an arbitrary infinite complement. Its
canonical Goursat/rank instance counts the ACTUAL finite image, after proving
that image finite. The graph-flatness conclusion reads three actual pair
images from one genuine full-group lift and needs no abelian premise.

The two countercontrols are actual relational structures with their FULL
automorphism groups proved: the four-shift hidden-parity source is explicitly
nonhomogeneous, and the left-regular S3 source is genuinely homogeneous with
moving owners, trivial owner kernel, intrinsic C2 fibres and a nonhomogeneous
owner-named expansion. Neither example claims CCO or SAP.

## Final author validation

Run in `/workspace/scratch/6b2f11185e14/cco-b017` with the pinned local runtime,
unchanged locked manifest, an independent writable project build directory,
`LAKE_RESTORE_ARTIFACTS=true`, `LAKE_ARTIFACT_CACHE=false`, and the established
`proc_self_compat.so` preload. `lean --version` reports Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`; `lake --version` reports
5.0.0-src+5045d00 using Lean 4.34.1.

| Check | Observed result |
| --- | --- |
| `lake --rehash build` | Build completed successfully, 2608 jobs |
| `python3 tools/verify_project_cache.py --require-complete`, before audit | Consistent: 461 olean parts, 461 current source modules |
| `lake env /workspace/scratch/6b2f11185e14/runtime/axiom-audit/.lake/build/bin/axiom-audit --root CCO --allow propext,Classical.choice,Quot.sound` | 6348 declarations audited; every transitive axiom within the allowlist |
| Same complete cache/source/byte guard, after audit | Consistent: 461 olean parts, 461 current source modules |
| `python3 tools/mathlib_cache_roots.py --project /workspace/scratch/6b2f11185e14/cco-b017 --reject-broad --json` | 107 actual external roots; 461 project modules; no broad import |
| Literal source hashes and protected-file diff against accepted base | Both pinned blobs match; no protected change |
| New public root-import coverage | All 32 present; accepted base root prefix intact |

Reproducible local logs are `b017-full-build.log`, `b017-guard-pre.log`,
`b017-audit.log`, `b017-guard-post.log` and `b017-mathlib-roots.json` under
`/workspace/scratch/6b2f11185e14/`. The initial final build exposed the missing
finite-product instance import described above. That failed check was repaired,
then the final whole build was rerun once. Successful author whole builds and
specialists' successful target builds were not repeated without a new change.

## Actual authorship and remaining publication gates

- `/root/b017_kernel`: actual general source, kernel/patching, compact
  projection, actual linear row/annihilator/width consumers and boundaries;
  final additive root imports, whole build and audit, source packet.
- `/root`: explicit countable separation, finite bidual/full-product dual,
  finite zero-extended dual tests, pure named Goursat and rank-count proofs.
- `/root/b015_groupoid/quotient_calculus`: actual C21–22 countercontrols,
  reused after its B015 helper work was finished; see
  `work-B017-actual-countercontrols.md`.
- `/root/b009_inheritance`: actual C16–20 named axes and instantiated linear
  image/count consumers, reused after its B009 helper work was finished;
  see `work-B017-named-axes.md`.

The registered `/root/independent_review` authored none of this code or its
implementation design. The coordinator alone publishes the union with current
accepted main, obtains exact-head CI/audit and ONE substantive non-author
whole-package review, and integrates under the single live lock with actual
resulting-main CI/audit. This author packet makes no independent-review,
external-CI, submission or acceptance assertion. No GitHub or live queue write
was performed by the B017 owner/helper agents.
