# B033 — independent frozen mathematical review

Disposition: **APPROVE exact public head `9a45a84e15e4994a242729cf24061f7a6391f62d` (PR #43)**.

The earlier local/union checkpoints below retain their original pending gates;
the final public-CI section closes those gates for this exact head only.

## Identity and reviewed object

- Registered reviewer: `independent_review`.
- Actual stable reviewer identity: `/root/independent_review`.
- I authored none of the complete B033 production Lean, implementation design,
  infrastructure, tests, source preparation, or repairs, including any helper or
  historical checkpoint. This is a separate non-author review, not an author
  reassigned a reviewer name.
- Actual implementation authors reported by the owner: `/root/b025_transversal`,
  `/root/b025_transversal/path_geometry`, `/root/external12`, `/root`, and
  `/root/b023_mi`. Root retains responsibility for binding this provenance in the
  live ledger before a formal submission.
- Mathematical head: `55136b696bd61413c894d0afcf109dc758b00d3c`.
- Mathematical tree: `697a20639d1f278cb3c4de5a776ceb255ba70647`.
- Accepted base: `614a0ee0d5ec557a64a1df6734a84e584c8964c6`.
- Immutable mathematical source: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.

I personally read all 27 new `CCO/ProfileHelly` modules, 2700 Lean lines,
against the published B033 package, the 37 claims and ten definitions in
`formalization/profile_helly/module.json`, its proof notes, and the pinned
`profile_completion_from_helly` proof and selected supporting context. Those
contract/source files were already read during publication and remain unchanged.
The frozen production diff contains only these new modules and additive direct
root imports. The entire accepted root import prefix is retained. No accepted
proof, source pin, mathematical contract, toolchain, manifest, or configuration
is changed by this mathematical checkpoint.

## Substantive source and provider findings

| Contract scope | Actual implementation and review finding |
| --- | --- |
| C01–C03: standalone table and return squares | `Table` and `TableLaws` contain finite nonempty typed atom palettes, actual converse/Peirce/reversal laws, nonempty atomic products, and menu associativity. Return-square absorption is proved from these laws. No source structure, SAP, CCO, identity atom, or desired completion is an input. |
| C04–C09: colliding semantic walks and cyclic cuts | `Word.Realizes` permits nonadjacent collisions. `guarded_readout` uses strong positive-length induction with the actual distinct endpoint guard; its closed-tail case absorbs a real return square. `two_arc_readout` cuts at the first actual diversity edge before algebraically transporting to arbitrary arc terminals. It does not assume those terminals have distinct semantic images. |
| C10–C15: simple paths and shared intersections | `Algebraic` tests distinct, internally disjoint actual simple arcs. Arbitrary path-profile intersection is then proved for every distinct endpoint pair, recorded or missing. Both prefix and suffix comparisons strictly decrease the number of shared internal vertices after removing a chosen common vertex; opposite orders of shared vertices require no extra hypothesis. |
| C16–C21: one edge and fixed-carrier completion | The finite image of all positive simple-path profiles is pairwise intersecting by the preceding theorem. The explicit input `Word.Helly` supplies one atom for every old path; an empty path family uses the actual nonempty endpoint palette. Filling writes both typed converse orientations. New-cycle compatibility is proved algebraically, not by assuming a realization. The exact finite `Sym2` missing-pair measure drops by one; recursion ends in the full triangle-defined complete class on the same vertices and sorts. |
| C22–C24: genuine semantic CCO | `CycleFeasible` uses actual finite complete allowed networks and positive realized cycle words. `SemanticHomCCO` allows different finite targets and nonadjacent collisions. Semantic cycles imply algebraic compatibility; the fixed-carrier constructor supplies a homomorphic completion. Conversely an actual completion hom restricts to every specified cycle. The stronger same-carrier `SemanticCCO` is separately proved and is not substituted as the definition of the homomorphic statement. |
| C25–C26: actual free partial amalgam | `freeAmalgam` constructs a finite carrier with only the literal base identified. Both factor maps are injective full induced typed embeddings, preserve all diagonal and off-diagonal colours, and have intersection exactly the original base. Every specified edge lies in a complete factor. Factor image legality and fan readout are proved directly from actual colours, with no SAP/completion premise. |
| C27–C32: mixed cycles and all base visits | `MixedCycles` proves actual two distinct overlap visits and rules out genuinely mixed simple cycles for empty/singleton overlap. `FreeAmalgamFan` propagates along every actual intermediate vertex of a positive walk. Every overlap vertex is a genuine universal fan anchor: each triangle lies in the complete factor containing its opposite edge. `fan_intersection_at` handles arbitrary cuts, including internal anchors, by literal colours, set Peirce and positive prefix/suffix products. If there is no overlap visit, both arcs stay in one complete factor. This direct algebraic argument covers two-visit digons and arbitrary further base visits without inventing a simple two-cycle, skipping intermediate visits, or requiring semantic completion of the amalgam. |
| C33–C36: strong amalgamation and the source theorem | The generic fixed-carrier algebraic constructor is applied directly to the free partial amalgam. `Embedding.extend` retains every complete factor's whole induced colouring and point map, so exact intersection and commutation survive. `distinct_fork` explicitly builds three distinct formal vertices, even with repeated sorts, using only nonempty totality and the full class. `helly_to_cco` retains the optional fork implication; `source_providers` also discharges the fork and SAP conclusions under the intended table interpretation. |
| C37 and indexed boundaries | Empty/singleton/two-vertex carriers and disconnected pairs have explicit completion results. Indexed Helly passes the finite image family and handles repeated profiles/words; distinct-index pairwise input is completed on the diagonal by actual positive-profile nonemptiness. All words remain positive, and all filling measures count distinct unordered pairs. |

The universal-fan argument is a genuine algebraic alternative to repeatedly
contracting and expanding the list of base segments. In particular, its
`run` induction reads every traversed edge, its hypotheses are verified from
actual complete factors, and the final free-amalgam theorem has no conditional
cycle, homomorphic-completion, or SAP provider left to discharge.

## Actual consumer and scope

`three_factor_amalgam` constructs a common complete finite network for three
arbitrary complete factors over the original complete base. It invokes the
derived SAP theorem twice and proves all three pairwise image intersections are
exactly that original base. The second application does not silently enlarge
the prescribed base. The proof also covers an empty base.

The source assumptions remain standalone table laws and the explicit finite
positive-profile Helly input, with fully supported palettes and the full
triangle-defined class. No countability, source homogeneity, ambient CCO/SAP,
exactness, distributivity, EPPA, HKN, or B024 theorem is introduced. A homomorphic
cycle witness may collide, while the independently derived strong amalgam has
literal injective induced factor maps and the required exact intersection.
No opaque remaining provider or stronger source premise was found.

## Validation evidence and limits

Per the agreed review workflow I did not compile, build, audit, run tests, spawn
another reviewer, or participate in implementation. I rely on the owner's sole
strict final pipeline for local compilation evidence and will personally bind
the final public exact-head CI before formal approval.

Owner-reported evidence at the unchanged mathematical freeze:

- Whole build: 3506 jobs, success.
- Official pinned axiom audit: 14957 CCO declarations, only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Complete CCO artifact and current-source guards: 967/967 before and after audit.
- Complete external-provider artifact and current-source guards: 269/269 before
  and after audit, provider commit `cd358cde844d5419fd43f30c441511927e09142f`.
- 121 tests; 23 module checks; 31 package envelopes; bounded B033 control covering
  1042 tables, 120 admissible tables, and 10314 fixed-vertex completions.
- 167 actual external Mathlib roots with broad imports rejected; fixed pins and
  whitespace checks retained. Prebuild repair was scoped to the expected
  changed root import header, one module and eight outputs.

These are owner-reported local results, not reviewer executions or a claim
about future remote CI. Final documentation, the public head/tree/ancestry,
completed exact-head PR CI and audit, formal ledger provenance/lease, and the
resulting-main audit remain integration gates. This local mathematical PASS
does not certify any future head or acceptance event.

## Final owner documentation delta — LOCAL PASS

I read the complete two-document delta at owner head
`620f78098fbbac4de2ef6a9b1b01347588e59221`, tree
`464f48355101e53b595a60c265f1ead95038dc56`, once after the whole mathematical
review. Relative to the reviewed mathematical freeze it adds exactly
`formalization/coordination/submissions/B033.md` (191 lines) and
`formalization/coordination/reports/work-B033-source-complete.md` (120 lines).
An exact scoped Git diff confirms no Lean/root, toolchain, manifest, source
module, pin, or B033 package-contract change.

The maps faithfully distinguish the ordinary possibly colliding finite-target
semantic CCO from the stronger same-carrier constructor; keep positive-profile
Helly as the explicit input; explain the actual universal-fan alternative,
two distinct overlap visits, digon and empty/singleton-base boundaries; and
identify the genuine twice-derived SAP consumer. The stated exact missing-pair
measure, full-class membership, whole-factor inducedness and three original-base
intersection conclusions agree with the reviewed proofs. Actual five-contributor
provenance and preservation of the coordinator's newer WIP are reported without
relabeling an author as reviewer.

The local validation numbers agree with the owner's supplied strict-pipeline
evidence. Bounded finite controls are correctly described as diagnostics, not
unbounded proofs. Both documents explicitly leave public author recording,
exact-head CI/audit, substantive formal approval, the sole CAS integration lock
and resulting-main CI/audit to the coordinator. No future public transition is
claimed. There is no documentation blocker. The disposition remains local
mathematical and documentation PASS, pending personally bound public exact-head
CI and the normal formal integration gates.

## Integration-only union and public content binding — PASS, CI pending

I inspected only the actual post-review union and 22 added Markdown lines at
local `c953c6ef55545b4509db17b96ef95d278f8cf2f9`, tree
`762c19475a8b4e5645672a957c263c93b8f69f74`. All 27 B033 proof blobs are
byte-identical to the reviewed mathematical freeze. Every nonroot blob from
actual merged B024 main `e10afddd47439af3d1eeb714397871eabc282f58` is retained
exactly; its entire `CCO.lean` is the literal prefix of the union root, followed
by the 27 new B033 imports. There are 991 unique direct imports, hence 992 CCO
modules including the root. Relative to that merged main, the exact additive
boundary is 27 B033 modules, `CCO.lean` and the two B033 Markdown reports.
No B024 theorem is imported by a B033 module or used as its mathematical input.
I reused my completed B024 review, rather than rereading its unchanged proofs.

The 11 added lines in each report accurately explain the union, unchanged B033
mathematics, expected combined 992-module/current-source and unchanged 269-module
provider checks, and absence of a duplicate local whole build or audit. They
leave final exact public CI and normal formal integration gates pending.

I personally fetched public PR #43 and the exact Git object for head
`9a45a84e15e4994a242729cf24061f7a6391f62d`: its tree is the same
`762c19475a8b4e5645672a957c263c93b8f69f74`, with local-source provenance
`c953c6e...`. The public compare against actual merged B024 main `e10afdd...`
reports ahead 32, behind 0 and merge base exactly `e10afdd...`; its file boundary
is exactly the same 30 files. PR head/base match those objects. At this content
check B024 resulting-main CI/acceptance and B033 exact PR CI are still pending,
so this is content PASS, not premature formal public approval. No repeated
mathematical review, build, audit, or test was run.

## Final personally verified public CI and formal disposition

On 2026-10-29 I personally fetched the public PR, exact head Git object,
synthetic merge Git object, actual main and coordination refs, complete parsed
STATE, completed PR run/job/step metadata, actual-base push-run metadata, and the
FULL decoded 2,066,939-character PR job log. These are independent reads of the
external evidence, not adoption of the coordinator's success summary.

- PR: <https://github.com/shulda/lean_cco/pull/43>.
- Exact approved public head: `9a45a84e15e4994a242729cf24061f7a6391f62d`.
- Exact approved tree: `762c19475a8b4e5645672a957c263c93b8f69f74`, equal to the
  personally checked final integration-only union `c953c6e...` above.
- PR base and actual current main remain
  `e10afddd47439af3d1eeb714397871eabc282f58`; PR is open and mergeable.
- Synthetic merge `608c5fdc12da3ffa8f7f65e5c652d64b8339ee11` has the SAME approved
  tree and exactly the ordered parents actual accepted main `e10afdd...`,
  approved public head `9a45a84...`.
- Completed pull-request run `40928862223` reports `success` for that exact head
  and base. Job `123641626486` and every substantive test/build/guard/audit step
  completed successfully.
- Actual complete logs: 121 Python tests passed; facade build 1330 jobs; CCO
  build 3531 jobs and official-audit 3531-job replay; pinned official audit
  15725 CCO declarations, all within exactly `propext`, `Classical.choice`,
  `Quot.sound`.
- Complete CCO guards before AND after the audit each report 992 ACTUAL olean
  parts AND 992 CURRENT source modules. Provider checks at the facade, pre-audit
  and post-audit stages each report 269 ACTUAL parts AND 269 CURRENT source
  modules, exact pin `cd358cde844d5419fd43f30c441511927e09142f`.
- Independent count of actual `Built` log entries: all 27 distinct new
  `CCO.ProfileHelly` modules plus the root compiled. The accepted-base cache
  retained the unchanged B024 modules; none was rebuilt. The fixed provider
  cache was also a hit, with zero provider modules rebuilt. This is actual
  compilation of every new B033 module, not a whole-project cold-cache claim.

Actual base push run `40928590992` independently reports completed `success`
for exact main `e10afdd...`. Observed public coordination ref was
`a096f5b19838f43a4caf55b6e0fa0480a7c7c5aa`; its complete parsed STATE is revision
248, policy 8, immutable source pin unchanged, integration lock null. It records
B024 ACCEPTED at revision 247 with that exact integration commit and successful
main audit/run. B033 is SUBMITTED at this exact approved head/PR/green run.
All FIVE actual authors are preserved in its author list: `/root/b023_mi`,
`/root/b025_transversal`, `/root/b025_transversal/path_geometry`, `/root/external12`,
and coordinator actor `root` representing actual `/root`. No production author
is the registered reviewer or has been renamed to this actual review-only role.

**Final disposition: APPROVE only the exact public head/tree above.** The whole
27-module/2700-line mathematical review, final two-document read, genuine import
union/22-line clarification, actual authorship and completed exact public CI are
all bound. No mathematical or documentation blocker remains. I wrote reports
only and performed no implementation/design/test work, helper delegation,
duplicate build, or audit. Formal review lease/approval events, sole-lock
expected-head merge, and successful actual resulting-main CI/audit remain the
coordinator's subsequent gates before ACCEPTED. This report does not predict
those future results or approve any moved head.
