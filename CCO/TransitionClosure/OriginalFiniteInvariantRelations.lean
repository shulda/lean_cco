import CCO.PairHomogeneity
import CCO.RawOrbitals
import Mathlib.Data.Fintype.Basic

/-!
# B049 source07 C35-C40: FINITE actual old invariant typed RAW relation menus

Between any two ORIGINAL named sorts the homogeneous old group has
finitely many invariant equality-inclusive binary relations, despite
the original carriers being infinite. A relation is uniquely
determined by the subset of its ACTUALLY occurring optional fine
pair colours, including the genuine same-sort none/identity value.

The family of NONEMPTY invariant RAW relations is finite and closed
under actual typed composition; the original same-sort identity is a
real member. Closure uses genuine old homogeneity to derive
middle-sort seriality, not a new relation-algebra axiom, arbitrary
quotient action, CCO/SAP on a quotient or a formal identity atom.

These finite relation FUNCTIONS (truth tables on original orbitals)
are the C35 receiving input to finite canonical hidden unary
function naming. This lemma alone does not assert finite syntactic
terms, exactness of transported equivalences or completion of the
later quotient normal-form theorem.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

/-- Every actual OLD invariant RAW typed relation. The subtype
retains true original pairs, including logical equality; no
quotient-reduct automorphism group is substituted for G. -/
abbrev OriginalInvariantTypedRel (i j : ι) :=
  {R : TRel X i j // TRel.Invariant (G := G) R}

/-- The finite ORIGINAL optional fine pair-colour truth table of
an old invariant typed RAW relation, including the old identity
colour none when source and target sorts agree. -/
def originalInvariantTypedRelCode {i j : ι}
    (R : OriginalInvariantTypedRel (X := X) (G := G) i j) :
    Set (Option (S.Atom i j)) :=
  S.rawSupport R.val

/-- A real full OLD homogeneous source can move any pair with one
optional named fine colour to any other pair with that SAME colour.
Consequently the original truth-table map is injective; no
definability oracle or quotient homogeneity is assumed. -/
theorem originalInvariantTypedRelCode_injective
    (H : HomogeneousSource S G) {i j : ι} :
    Function.Injective
      (originalInvariantTypedRelCode S (G := G)
        (i := i) (j := j)) := by
  intro R T hCodes
  apply Subtype.ext
  funext x y
  apply propext
  constructor
  · intro hRxy
    have hColour : S.colour x y ∈ S.rawSupport T.val := by
      rw [← hCodes]
      exact ⟨x,y,hRxy,rfl⟩
    obtain ⟨a,b,hTab,hCol⟩ := hColour
    obtain ⟨g,hga,hgb⟩ :=
      S.pair_homogeneous_of_homogeneous H a x b y hCol
    have hMoved := T.property g a b hTab
    simpa only [hga,hgb] using hMoved
  · intro hTxy
    have hColour : S.colour x y ∈ S.rawSupport R.val := by
      rw [hCodes]
      exact ⟨x,y,hTxy,rfl⟩
    obtain ⟨a,b,hRab,hCol⟩ := hColour
    obtain ⟨g,hga,hgb⟩ :=
      S.pair_homogeneous_of_homogeneous H a x b y hCol
    have hMoved := R.property g a b hRab
    simpa only [hga,hgb] using hMoved

/-- Source07 D08/C35, finite family of ALL original
G-invariant typed RAW relations, even though their carriers
may be infinite. Each is determined by a finite optional
original fine-colour table; no Axiom/Prop is added. -/
theorem originalInvariantTypedRel_finite
    (H : HomogeneousSource S G) {i j : ι} :
    Finite (OriginalInvariantTypedRel (X := X) (G := G) i j) := by
  classical
  letI := S.finiteAtom i j
  exact Finite.of_injective (originalInvariantTypedRelCode S (G := G))
    (originalInvariantTypedRelCode_injective S H)

/-- Only the genuine NONEMPTY old invariant typed RAW relations.
Actual original relational composition of two such states is
again nonempty; no syntactic word outside the finite old
relation family is included by definition. -/
abbrev OriginalNonemptyInvariantTypedRel (i j : ι) :=
  {R : OriginalInvariantTypedRel (X := X) (G := G) i j //
    TRel.Nonempty R.val}

/-- Source D08/C35: the nonempty original old typed relation
family is finite as a subtype of the genuinely proved full
old invariant relation family. -/
theorem originalNonemptyInvariantTypedRel_finite
    (H : HomogeneousSource S G) {i j : ι} :
    Finite (OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j) := by
  haveI : Finite (OriginalInvariantTypedRel (X := X) (G := G) i j) :=
    originalInvariantTypedRel_finite S H
  exact Finite.of_injective Subtype.val Subtype.val_injective

/-- Exact equality-inclusive original RAW typed composition,
closed under invariance of the SAME original group G. -/
def originalInvariantTypedRel_comp
    {i j k : ι}
    (R : OriginalInvariantTypedRel (X := X) (G := G) i j)
    (T : OriginalInvariantTypedRel (X := X) (G := G) j k) :
    OriginalInvariantTypedRel (X := X) (G := G) i k :=
  ⟨TRel.comp R.val T.val,
    TRel.invariant_comp R.val T.val R.property T.property⟩

/-- All three genuine original named sorts and the complete middle
sort transitivity are retained: the RAW product of TWO nonempty
invariant typed old relations has an actual old three-vertex
representative (not necessarily all distinct, since RAW includes
equality). Hence the NONEMPTY finite relation family is closed
under composable RAW products. -/
def originalNonemptyInvariantTypedRel_comp
    (H : HomogeneousSource S G)
    {i j k : ι}
    (R : OriginalNonemptyInvariantTypedRel (X := X) (G := G) i j)
    (T : OriginalNonemptyInvariantTypedRel (X := X) (G := G) j k) :
    OriginalNonemptyInvariantTypedRel (X := X) (G := G) i k :=
  ⟨originalInvariantTypedRel_comp R.val T.val,
    TRel.comp_nonempty_invariant
      R.val.val T.val.val R.property T.property
      T.val.property (S.original_sort_transitive_of_homogeneous H j)⟩

/-- Real logical original identity belongs to the finite nonempty
same-sort relation family. It is NOT a diversity STRONG atom and
must be omitted (not multiplied by empty) for positive OLD words. -/
def originalNonemptyInvariantTypedRel_ident
    (i : ι) :
    OriginalNonemptyInvariantTypedRel (X := X) (G := G) i i := by
  let R : OriginalInvariantTypedRel (X := X) (G := G) i i :=
    ⟨TRel.ident X i, by
      intro g x y h
      exact congrArg (fun a : X i => g • a) h⟩
  classical
  let x : X i := Classical.choice (S.nonemptySort i)
  exact ⟨R, ⟨x,x,rfl⟩⟩

end CCO.TransitionClosure
