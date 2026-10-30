# B048 canonical full language and actual pair source

Author: `/root/b047_pair_safe_split/infinite_type_fibres`.
Accepted source base: `787dd3b59e0405223a9b5870d562d2861c9f33d4`.
Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Public batch claim: B048 / STATE 388; coordinator is the sole remote publisher.

## Scope and source mapping

This work supplies D01 and C01–C02, and the all-tuple representation support
for C03. The substantive support-normal completion hypothesis A03 remains
explicit in the owner's full-language construction. Neither irreducibility,
canonical naming nor pair SAP is claimed to imply A03.

- `Canonical/Signature.lean`: one normalized finite-total signature, complete
  `BoolTable`, pullbacks, full custom embeddings/isomorphisms and exact reads.
  `AtomicTest L k` contains every old relation symbol and EVERY map from its
  full arity to the k slots. Repeated arguments and nullary symbols are literal.
- `Canonical/FirstOrder.lean`: relational Mathlib language with no function
  symbols; exact BoolTable/FO-structure and custom/FO embedding/isomorphism
  conversions with inverse laws. Arbitrary structures can be decoded, so the
  marked Fraisse construction can use the existing CountableAge implementation.
- `Canonical/Profiles.lean`: complete finite atomic profiles, explicit finite
  positive/negative qf conjunction `profileFormula`, exact realization and QF.
  Unary profiles retain all diagonal higher-arity information; pair profiles
  retain all two-support repeated tuples. `nullaryType` is the ambient 0-type,
  preserved by every pullback, including the actual empty induced structure.
- `Canonical/Source.lean`: actual finite realized unary names, their real
  carrier fibres, actual realized distinct-pair atoms, literal old-carrier
  equivalence `pack`, converse, identity, realization, and AtomicSource.
  Same-sort symmetry is exactly the A02 premise `SameSortSymmetric`; it is not
  inferred from old full homogeneity. Full embeddings give identical pair
  owners and tagged colours for any two full realizations. Tagged colours
  recover all old pair-profile truth even on the diagonal via the unary name.
- `Canonical/Expansion.lean`: finite normalized definitional expansion retaining
  ALL old symbols and adding unary and irreflexive pair-profile names. Possible
  but unrealized names simply define empty predicates; the actual typed pair
  source uses only realized names. Full embeddings and isomorphisms correspond
  bijectively, with the same point maps/permutations. No equality of full and
  pair-reduct automorphism groups is asserted. Every distinct pair has an
  actual irreflexive named predicate, giving complete-factor irreducibility.
  Finite qf/equality profiles and same-sort symmetry survive the expansion.
- `Canonical/NameFormulas.lean`: explicit old-language unary/pair qf formulas,
  with the pair formula including logical inequality; their semantics are
  exactly the added full relation predicates.
- `Canonical/Normalization.lean`: a proved encoding of ANY custom relational
  language with `Finite (Sigma L.Rel)` into the normalized signature. Every
  old symbol and tuple read is retained; full embeddings/isomorphisms convert
  in both directions with inverse laws. Finite total symbol count is essential;
  mere finiteness separately at each arity is not used as a substitute.

The owner's final working full table may be `U := expand T`, with pair source
`source U (sameSortSymmetric_expand hsym)`. Its irreflexive separation is proved
by `expand_separates`, even when the original signature is empty. A03 acts on
the working canonical full language, preserving all positive and negative data
on distinguished full factors. Canonical naming does not delete higher tuples.

## Compiled checkpoints

- `5ba9e2a3ce6d5f14bafac61a5d00597fc304bc9e`: minimal Signature/FirstOrder seam.
- `7456456edb8b21f6983548c4f6a29f081d785427`: exact arbitrary FO decoding.
- `b626acda17731c3d601e05198982705eb6a083a2`: genuine qf profiles and actual source.
- `27b5ca6cbec66f1511d2afda9abed4196f908f23`: full definitional expansion/separation.
- `6e99357a09e7245f526ec13a21980ae685c18171`: qf names, irreducibility, symmetry.
- `791ecd5e259a0208dc47127a46bd25f8661cdc78`: arbitrary finite-total normalization
  and exact expanded-predicate definability/full embedding-isomorphism equivalence.

Pinned Lean 4.34.1 and bundled Lake were used with the unchanged manifest and
private worktree outputs. Final narrow check:

```
lake build CCO.FullPhaseLift.Canonical.NameFormulas \
  CCO.FullPhaseLift.Canonical.Normalization
```

Succeeded with 1054 jobs (incremental replay included). No broad project build,
transitive axiom audit or remote writes were duplicated; the owner/coordinator
performs final assembled validation. No new axiom, sorry or provider callback.
