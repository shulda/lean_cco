import CCO.TransitionClosure.OriginalNamedAtomicBranch

/-!
# B049 source07 C39-C40: FULL finite named hidden RAW transition term language

The pinned source07 names ALL actual original-G invariant nonempty RAW
relations R with NO literal old identity, not merely the fine old atom
transitions. This source-tight module therefore includes the COMPLETE
finite RAW primitive transition menu: each symbol retains its genuine
represented proper full meet-irreducible source J, the actual invariant
relation R, and the literal kernel condition R;Rᵒᵖ <= J.
Original SAP and terminal FULL NR2 construct its true named hidden
target, rather than postulating represented target membership.

The term grammar freely composes genuine named quotient identities,
upward maps between represented full original coordinates, and ANY
of these complete primitive invariant RAW transition symbols.
All terms have exact source and target quotient carriers and no length
bound. A semantic-preserving embedding in the independently compiled
arbitrary ORIGINAL FULL quotient-term language proves FINITENESS of
the induced unary FUNCTIONS, not of terms or quotient points.

The real→hidden projection is separately named and has the literal
original representative interpretation. A fine atom gives one genuine
primitive RAW symbol (by its exact old invariant singleton relation);
combined with the accepted whole-branch-to-atom proof this shows every
positive quotient-functional old STRONG branch map is named.

A complete proof that the primitive list is closed under all converse
symbol/inverse identities, the final binary hidden-language consumer
and source tuple-type enrichment are separate remaining duties.
No quotient SAP/CCO or synthetic STRONG identity.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.QuotientTransport

/-- The source07 COMPLETE actual finite MENU of old RAW
identity-free quotient-transition symbols:
- source is a genuinely represented original proper FULL MI;
- R is an ACTUAL NONEMPTY original-G invariant typed RAW relation;
- R;Rᵒᵖ is contained in the source full original J;
- no ACTUAL diagonal identity pair is included in R.
This includes ALL eligible many-atom invariant R, not
only original diversity fine-atom symbols. -/
abbrev OriginalNamedRawTransitionSymbol
    (H : HomogeneousSource S G) (i j : ι) :=
  {p : OriginalNamedHiddenCoordinate S H i ×
      OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j //
    (∀ x z : X i,
      QuotientTransport.compose p.2.val.val
        (QuotientTransport.converse p.2.val.val) x z →
          p.1.val x z) ∧
    (∀ x : X i, ∀ y : X j,
      p.2.val.val x y →
        (⟨i,x⟩ : Sigma X) ≠ ⟨j,y⟩)}

/-- Actual source finite orbital palette and the real FULL finite
colour equivalence lattice ensure only finitely many distinct
eligible primitive RAW transition symbols. Finite carrier or finite
syntax is NOT assumed. -/
theorem originalNamedRawTransitionSymbol_finite
    (H : HomogeneousSource S G) {i j : ι} :
    Finite (OriginalNamedRawTransitionSymbol S H i j) := by
  haveI : Finite (OriginalNamedHiddenCoordinate S H i) :=
    original_named_hidden_coordinates_finite S H
  haveI : Finite
      (OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j) :=
    originalNonemptyInvariantTypedRel_finite S H
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- The original actual B040 canonical quotient transport
associated to one genuine primitive named invariant RAW symbol,
on the SAME original homogeneous group. -/
noncomputable def originalNamedRawTransitionSymbol_transport
    (H : HomogeneousSource S G)
    {i j : ι} (a : OriginalNamedRawTransitionSymbol S H i j) :
    Transport (originalColourEqAsInvEq S H a.val.1.val)
      a.val.2.val.val :=
  typed_quotient_transport (originalColourEqAsInvEq S H a.val.1.val)
    a.val.2.val.val a.val.2.val.property a.val.2.property
    (S.original_sort_transitive_of_homogeneous H i)
    (S.original_sort_transitive_of_homogeneous H j)
    a.property.1

/-- Exactly the real transported target represented proper FULL MI:
the B040 interval transport proves MI and noncollapse is from the
ORIGINAL age SAP, with independent terminal full-NR2 RAW naming. -/
noncomputable def originalNamedRawTransitionSymbol_target
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (a : OriginalNamedRawTransitionSymbol S H i j) :
    OriginalNamedHiddenCoordinate S H j :=
  original_named_hidden_transport_target S H sap nr2 a.val.1
    (originalNamedRawTransitionSymbol_transport S H a)

/-- The original genuine B040 unary quotient bijection denoted
by a full named RAW transition symbol. Its target is the actual
terminal represented hidden coordinate, not a free quotient chart. -/
noncomputable def originalNamedRawTransitionSymbol_function
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (a : OriginalNamedRawTransitionSymbol S H i j) :
    Quotient a.val.1.val.val →
      Quotient (originalNamedRawTransitionSymbol_target
        S H sap nr2 a).val.val :=
  fun q => (originalNamedRawTransitionSymbol_transport S H a).quotientEquiv q

/-- Every true OLD atomic transition is also one of the
source07 named full-RAW primitive symbols. Its relation is
the complete real original fine a-orbital, not the pointwise
restriction of a larger R. Source OLD atoms are irreflexive,
so the no-identity condition is DERIVED, not assumed. -/
noncomputable def originalNamedAtomicSymbol_asRaw
    (H : HomogeneousSource S G)
    {i j : ι} (a : OriginalNamedAtomicTransitionSymbol S H i j) :
    OriginalNamedRawTransitionSymbol S H i j := by
  let A : OriginalInvariantTypedRel (X := X) (G := G) i j :=
    ⟨S.atomRel a.val.2, by
      intro g x y hxy
      exact (S.colourInvariant_of_homogeneous H g x y).trans hxy⟩
  let R : OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j :=
    ⟨A,S.realized a.val.2⟩
  refine ⟨⟨a.val.1,R⟩, ?_⟩
  constructor
  · intro x z hxz
    obtain ⟨y,hxy,hzy⟩ := hxz
    exact a.property x z y hxy hzy
  · intro x y hxy heq
    exact S.atomRel_ne hxy heq

/-- Genuine real→hidden source projection x↦[x]_J for a named
FULL original J; not a map on an invented hidden real singleton,
and not a STRONG positive identity edge. -/
def originalRealToNamedHiddenProjection
    (H : HomogeneousSource S G)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i) :
    X i → Quotient D.val.val :=
  fun x => Quotient.mk D.val.val x

/-- The real→hidden projection is the actual original
quotient-upward map from the ORIGINAL equality coordinate. -/
theorem originalRealToNamedHiddenProjection_eq_oldUp
    (H : HomogeneousSource S G)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (x : X i) :
    originalRealToNamedHiddenProjection S H D x =
      Quot.mapRight
        (show (⊥ : ColourEq S i) ≤ D.val from bot_le)
        (Quotient.mk (⊥ : ColourEq S i).val x) := by
  rfl

/-- A source07 genuinely well-typed FULL named hidden unary term:
identities, upward projections between actual named coordinate
kernels, or arbitrary finite sequences of EVERY identity-free
many-atom invariant RAW primitive transition. Distinct terms may
represent the SAME unary function. -/
inductive OriginalNamedRawUnaryTerm
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    {i : ι} → OriginalNamedHiddenCoordinate S H i →
    {j : ι} → OriginalNamedHiddenCoordinate S H j →
    Type (max u v w t) where
  | ident {i : ι} (D : OriginalNamedHiddenCoordinate S H i) :
      OriginalNamedRawUnaryTerm H sap nr2 D D
  | up {i j : ι}
      {D : OriginalNamedHiddenCoordinate S H i}
      {E F : OriginalNamedHiddenCoordinate S H j}
      (w : OriginalNamedRawUnaryTerm H sap nr2 D E)
      (hEF : E.val ≤ F.val) :
      OriginalNamedRawUnaryTerm H sap nr2 D F
  | transition {i j k : ι}
      {D : OriginalNamedHiddenCoordinate S H i}
      (a : OriginalNamedRawTransitionSymbol S H j k)
      (w : OriginalNamedRawUnaryTerm H sap nr2 D a.val.1) :
      OriginalNamedRawUnaryTerm H sap nr2 D
        (originalNamedRawTransitionSymbol_target S H sap nr2 a)

namespace OriginalNamedRawUnaryTerm

/-- Source-tight actual semantic embedding in the independently
proved ORIGINAL FULL mixed unary term language, not a bound on
syntax length. The primitive R data are the same old G-invariant
relations and accepted B040 transports; upward maps are literal. -/
noncomputable def toOld
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι}
    {D : OriginalNamedHiddenCoordinate S H i}
    {E : OriginalNamedHiddenCoordinate S H j} :
    OriginalNamedRawUnaryTerm S H sap nr2 D E →
      OriginalOldUnaryWord S H i D.val j E.val
  | .ident D => .ident _ D.val
  | .up w hEF => .up (toOld H sap nr2 w) hEF
  | .transition a w => .transition (toOld H sap nr2 w)
      a.val.2 (originalNamedRawTransitionSymbol_transport S H a)

/-- Actual generated named term interpretation on genuine old
quotient class carriers. No independent automorphism action
on hidden quotient sorts is asserted. -/
noncomputable def eval
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι}
    {D : OriginalNamedHiddenCoordinate S H i}
    {E : OriginalNamedHiddenCoordinate S H j}
    (w : OriginalNamedRawUnaryTerm S H sap nr2 D E) :
    Quotient D.val.val → Quotient E.val.val :=
  OriginalOldUnaryWord.eval S H (toOld S H sap nr2 w)

end OriginalNamedRawUnaryTerm

/-- All finite named hidden unary syntax trees between two
actual old sort tags. The source/target represented FULL MI
quotient kernels are part of the semantic type, not omitted. -/
abbrev OriginalNamedRawUnaryTermDatum
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (i j : ι) :=
  Σ D : OriginalNamedHiddenCoordinate S H i,
    Σ E : OriginalNamedHiddenCoordinate S H j,
      OriginalNamedRawUnaryTerm S H sap nr2 D E

/-- Count actual TYPED unary functions, not syntax, with the
true source and target FULL original quotient equivalences
included in the sigma data. -/
noncomputable def originalNamedRawUnaryTermDatum_function
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (d : OriginalNamedRawUnaryTermDatum S H sap nr2 i j) :
    OriginalCanonicalRawTransitionFunction S i j :=
  ⟨d.1.val,d.2.1.val,OriginalNamedRawUnaryTerm.eval S H sap nr2 d.2.2⟩

/-- SOURCE07 C39/C40: the WHOLE NAMED hidden language generated
by real old proper represented FULL MI quotient coordinates, actual
source-level upward maps and ALL genuine original-G invariant
identity-free RAW primitive transition names has only FINITELY
many distinct interpreted unary functions per pair of original
sorts. Syntax itself can be arbitrarily long.

Every term embeds unchanged into the already proved original
FULL mixed RAW transition/projection grammar; the latter's
full normal-form theorem bounds its ACTUAL quotient functions.
No additional terminal assumption beyond original FULL NR2,
no quotient SAP/CCO and no artificial STRONG identity. -/
theorem original_named_raw_unary_term_functions_finite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} :
    (Set.range
      (originalNamedRawUnaryTermDatum_function
        S H sap nr2 (i := i) (j := j))).Finite := by
  have hAll := original_old_unary_term_functions_finite
    S H (i := i) (j := j)
  apply hAll.subset
  intro f hf
  obtain ⟨d,rfl⟩ := hf
  exact ⟨⟨d.1.val,d.2.1.val,
      OriginalNamedRawUnaryTerm.toOld S H sap nr2 d.2.2⟩,rfl⟩

end CCO.TransitionClosure
