# B037 Ramsey provider: exact source recovery and cache validation

The vendored E01 provider has exact Git subtree
374241ce3751715c90b12c0b071f36026819ad4a. After the transient workspace was
lost, all original sources were downloaded once from the exact upstream
Git blobs and the compatibility/configuration files replayed from history.
The reconstructed subtree equals the previous subtree BYTE FOR BYTE.
The old local commit objects were not recovered; new recovery commits are
25c0cff144739f697ec5c85151774a03fb227979 (foundations/config),
c3859c1de76296ff54b313367968827deae59da4 (complete source/provenance),
b3f048e6a2a5d242fab68cb45ac01f4e26a8da38 (guards) and
65a1888fa389d105ed2d71fc0f191c7316742989 (tests/cache CI wiring).

## Mathematical source and compatibility

The actual original declaration is
StructuralRamsey.Structure.allThoseRamseyClasses_theorem_2_19_partialFunctions
from janhubicka/partite-construction@918732dcff88fd1ab9be69f70e4f1d66385106e3,
source blob f50d08fbe712389680fa3bbe162ab4f69396c4cb. Its intact closure is
87 PartiteConstruction modules plus 18 SuccessorTree modules from
janhubicka/lean-successors@ce5ce187ef88e28d84a4a465517b3f9c87a0640a.
UPSTREAM.json records every original commit/tree/blob and source SHA256;
COMPATIBILITY.patch records all 27 edited source files separately.
The original tree has 105 Lean modules; CCORamsey.lean adds one actual facade.
The available SuccessorTree LICENSE is retained verbatim.

The source port keeps original namespaces and every theorem statement.
It removes 15 broad Mathlib.Tactic imports, supplies targeted consumer imports,
uses receiving Mathlib.Data.Prod.Lex and adapts one length proof with
Nat.lt_succ_of_lt. It introduces no axiom, admission or hypothetical Ramsey
provider. All ten existing receiving dependency entries remain unchanged;
only the CCORamsey path package is appended. The package uses receiving
Lean4.34.1 and the original nine exact Mathlib dependency entries.
No unrestricted lake update or shared dependency source edit was performed.
The mathematical source pin remains 490c3f36d85db5a0b3ced0598e6c431825254ec5.

## Separate provider identity and CI cache

The Ramsey registration and guard bind the exact Git subtree, actual source
Git blobs including hidden tracked edits, configurations and dependency
entries, actual current source closure, source hashes, compiled import
headers/flags, trace output descriptors/bytes and compiler search-path
resolution. Cold prechecks may lack outputs; complete checks require 106/106.
Source identity failures are rejected. Repair deletes only private generated
Ramsey namespace outputs and rejects shared/aliased build parents.

The fixed cco-ramsey-dependency-v1 cache key binds subtree, facade, platform,
toolchain/manifests/configurations, registration and guard implementation.
It excludes unrelated CCO theorem source/commits and uses no broad fallback.
Existing EPPA registration, pin, metadata helper and guard semantics remain
unchanged. CI adds a separate vendor/ramsey/.lake/build cache and provider
checks before/after the standard complete CCO axiom audit.
The import walker discovers 26 actual targeted Mathlib roots, rejects broad
Mathlib/Mathlib.Tactic and never passes unknown CCO/provider roots to cache.

## Fresh post-recovery evidence

- Full standalone CCORamsey facade rebuilt successfully: 1182 Lake jobs,
  exactly 106 provider oleans. Log: round16-recovery-ramsey-build.log.
- Actual 26-root lake exe cache get succeeded; no files needed downloading,
  1061 files already decompressed. Log: round16-recovery-ramsey-cache.log.
- Root package overlay was prepared using the existing isolated EPPA helper.
  Actual-root source/artifact/search-path guard passed 106/106 at the exact
  subtree. Log: round16-recovery-ramsey-guard.log.
- Warm actual-root facade build passed in 1.760 seconds with all 106 olean
  SHA256 values and nanosecond mtimes unchanged.
- Nine identity/isolation tests and four existing cache-root tests pass.
  Log: round16-recovery-ramsey-tests.log.
- The restored source/guard/configuration reproduces the original cache key
  cco-ramsey-dependency-v1-b49429bd1d6575984bba956dff298d5ae19e187d9b021ffdbfe7832e7336df9c.

Historical pre-loss validation, retained as conversation receipts rather
than restored log files: independent cold 47.383s; warm 1.377s with zero fresh
provider builds and all 106 hashes/mtimes unchanged; deliberate corruption of
one Basic.olean rejected exactly one module, safe private repair/recovery
ended 106/106. No claim is made that the old scratch logs survived.
The owning batch keeps its single final source review, complete audit and
exact-head/main CI. This provider report alone does not complete B037's
E02/E03 bridges or local transfer obligations.
