# B036 unary reset and midpoint implementation

The source pin is `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
This implementation preserves the B036 mathematical contract and accepted APIs.
It generalizes the accepted `UnarySupport` primitive graph semantics into
local `Unary/Primitive` modules by removing only symbol/sort-finiteness fields;
all accepted files/APIs remain unchanged. Arbitrary fixed unary signatures
are allowed, including arbitrary extra full-R function and relation alphabets;
no deeper CCO, Ramsey, SAP, EPPA or geometry provider is imported.

## Actual proof path

- C01–C06: `Unary/Category`, `Unary/FiniteAge`, `SortRestriction` retain actual
  partial-unary domains, arbitrary relation arities and nullary truth. The
  selected sorts form a closed induced object. `selectedEmbeddingEquiv` factors
  every embedding of an all-selected source using the same literal point map,
  with inverse the actual inclusion. `restricted_age_is_actual_image` identifies
  the hereditary all-selected class with the actual isomorphism-closed image
  of restriction. The coloring pullback proves Ramsey; restricting joint and
  strong amalgam hosts proves optional JEP and SAP with the exact base images.
- C25–C28: `Unary/Task` gives actual fibre orders and old induced embeddings.
  Structural fibre/reset laws are required only on the hereditary legal old
  age (`Fibres.Allowed`), with each allowed fibre order carrying that actual
  legality witness; arbitrary raw interpretations need not be equivalences.
  U1/U0 retain exactly the same unary functions, including all partial domains.
  The full ambient `FullObject` may add EXTRA unary partial functions and
  arbitrary relations; every `FullHom` preserves/reflects all of them.
  `Unary/Definable` proves transport of genuine partial-unary terms and Boolean
  qf formulas, including nullary atoms, then constructs actual qf task-code
  naturality. General functorially determined codes retain their stated
  relation-by-relation naturality input; the theorem does not assume a full
  source embedding or an EP conclusion as a callback.
- C29–C31: `Unary/StoredPatterns` enumerates only the original comparisons by
  a finite array. Induction builds actual induced extensions, keeps every old
  comparison and relation, and records all midpoint choices. Each new midpoint
  is outside the entire accumulated host; `StoredArray.distinct` proves that
  the stored choices are distinct, and `fresh` excludes the original source.
  Joint embedding combines the positive and legally reversed patterns without
  requiring disjointness or SAP.
- C32–C38: `Unary/PointedTemplate` uses the WHOLE actual closure under both old
  and extra full-ambient functions. Its `PointedRealization` is an isomorphism
  of the complete expanded induced closure fixing BOTH roots. Root generation
  proves uniqueness of the entire embedding. `template_global_sign` colors ALL
  full template embeddings, takes a full ambient Ramsey witness, and produces
  one global comparison sign on all oriented reset edges. Both edges of each
  stored path receive it. Two-edge transitivity gives the positive source copy
  or undoes the reversed source order. `TaskHomOfPreserves` proves order
  reflection using totality/injectivity; task-code preservation follows from
  the actual generated code interpretations. `ResetSetting` retains the full
  stated hereditary, reasonable, precompact, reduct-surjective, full-lift and
  legal-reversal hypotheses. `abstract_reset_order_EP` chooses the old host
  BEFORE every exact-carrier competitor. No intermediate Ramsey or SAP input
  is used in this reset criterion.
- C39–C44: `FreshMidpoints` starts from the actual WHOLE ordered pair closure.
  A permitted witness has the same complete unexpanded POINTED generated type,
  and its midpoint lies outside that entire witness closure. The source free
  order-extension input chooses an allowed ordering extending the WHOLE base
  and placing the midpoint between the two roots. The actual ordered strong
  amalgam is then constructed. Its exact intersection law forces the witness
  midpoint outside the entire earlier host. This supplies `MidpointSchema`,
  and the original-comparison array induction gives finite fresh iteration.
  Free order-extension is required only for PERMITTED unexpanded witnesses
  (`HasAllowedOrder`), not arbitrary graphs. Unexpanded SAP alone is not used
  as a substitute for ordered SAP.
- C53: `ClosureBoundaries` has concrete finite partial-unary diagrams with
  identical binary root reducts but F(0)=F(1) versus F(0)≠F(1). It proves there
  is no rooted induced embedding even between their actual generated subtype
  structures. Its existing midpoint already belongs to the entire pair
  closure, separating mere reset reachability from fresh extension.
- C55: the actual `TaskEP` and `FullArrow` definitions retain all fixed-host
  and all-template-embedding quantifiers. The proof is an arbitrary-finite
  theorem, not a bounded diagnostic asserted to cover infinite families.

## Recovery and validation status

The previous ephemeral workspace was lost before its source commits were
published. The actual proof text was recovered from preserved author tool-call
history into new commits, without claiming the missing local commit objects
still exist. These files are preserved by the current Git history. The
previous unary core had passed narrow compilation; the qf constructor's last
implicit-binder correction was pending. The recovered tree, including that
correction and legality-gated fibre laws, passed a fresh pinned narrow build
of all owner roots (753 jobs). The subsequent unrestricted-symbol local primitive generalization passed
a fresh narrow build of all owner roots (746 jobs), with a direct compiler
check confirming `store_all_original_comparisons` uses the NEW local primitive
signature. A stale generated module was moved aside reversibly and artifact
restoration disabled for that check; `--rehash` alone had left its old interface
visible. Logs are retained in the receiving runtime. No batch completion, independent approval,
final audit, PR or main CI success is asserted by this report.
