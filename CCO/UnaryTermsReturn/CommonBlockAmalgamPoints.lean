import CCO.UnaryTermsReturn.CommonBlockAmalgamBlocks
import CCO.CloneSAP.FiniteUnion
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

/-!
# B052 C16: injective old real points for the common-block SAP amalgam

The finite abstract union A ⊔_C B identifies *only* actual
displayed base points (not all points of the same hidden block).
The A points remain literally unchanged; the extra B points
receive their proven compatible block labels and fresh clone
indices strictly above every A clone. These are actual old
real points, not artificial hidden quotient vertices.

Every B point, including those in the base, retains its original
named real sort and the exact canonical A/B block equality from
CommonBlockAmalgamBlocks. The resulting map of the abstract
union is injective and separates the A and B copies away from
C, as required for strong rather than ordinary amalgamation.

The final induced-age SAP theorem must additionally verify
all original typed fine colours and produce the finite target
substructure/embeddings. No SAP instance is claimed here yet.
-/

namespace CCO.UnaryTermsReturn

open CCO
open CCO.CloneSAP

/-- Maximum ACTUAL clone index in the finite A old
diagram; fresh B clones will be larger than this number. -/
noncomputable def commonBlockFiniteMaxClone
    (A : FiniteInduced (X := CommonBlockReal)) : ℕ :=
  A.finite_vertices.toFinset.sup
    (fun p : Sigma CommonBlockReal => p.2.2)

theorem commonBlockFiniteClone_le_max
    (A : FiniteInduced (X := CommonBlockReal))
    (a : ↥A.vertices) :
    a.val.2.2 ≤ commonBlockFiniteMaxClone A := by
  classical
  have hm : a.val ∈ A.finite_vertices.toFinset := by
    simpa using a.property
  exact Finset.le_sup (s := A.finite_vertices.toFinset)
    (f := fun p : Sigma CommonBlockReal => p.2.2) hm

/-- For every B old point use the genuine compatible block
label from the previous module and a clone-index encoding
its unique B vertex. Even when two B points have the SAME
block, the clone index distinguishes their real identities. -/
noncomputable def commonBlockFreshBPoint
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B)
    (b : ↥B.vertices) : Sigma CommonBlockReal := by
  classical
  letI : Finite ↥B.vertices := B.finite_vertices.to_subtype
  letI : Fintype ↥B.vertices := Fintype.ofFinite _
  exact ⟨b.val.1,
    (commonBlockAmalgamLabel C A B s t b,
     commonBlockFiniteMaxClone A + 1 + ((Fintype.equivFin ↥B.vertices) b).val)⟩

/-- Distinct B vertices have genuinely distinct chosen
fresh clones, even if their old block labels agree. -/
theorem commonBlockFreshBPoint_injective
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B) :
    Function.Injective (commonBlockFreshBPoint C A B s t) := by
  classical
  letI : Finite ↥B.vertices := B.finite_vertices.to_subtype
  letI : Fintype ↥B.vertices := Fintype.ofFinite _
  intro b b' h
  have hClone := congrArg
    (fun p : Sigma CommonBlockReal => p.2.2) h
  change commonBlockFiniteMaxClone A + 1 +
      ((Fintype.equivFin ↥B.vertices) b).val =
    commonBlockFiniteMaxClone A + 1 +
      ((Fintype.equivFin ↥B.vertices) b').val at hClone
  have hIndex : ((Fintype.equivFin ↥B.vertices) b).val =
      ((Fintype.equivFin ↥B.vertices) b').val := by omega
  exact (Fintype.equivFin ↥B.vertices).injective (Fin.ext hIndex)

/-- No old A point can equal a newly coded B point,
since every new clone index is strictly above the
maximum old A clone index. This proves the STRONG
intersection condition, not merely preservation of colour. -/
theorem commonBlockFreshBPoint_disjoint_A
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B)
    (a : ↥A.vertices) (b : ↥B.vertices) :
    a.val ≠ commonBlockFreshBPoint C A B s t b := by
  classical
  letI : Finite ↥B.vertices := B.finite_vertices.to_subtype
  letI : Fintype ↥B.vertices := Fintype.ofFinite _
  intro heq
  have hClone := congrArg
    (fun p : Sigma CommonBlockReal => p.2.2) heq
  have hBound := commonBlockFiniteClone_le_max A a
  change a.val.2.2 = commonBlockFiniteMaxClone A + 1 +
      ((Fintype.equivFin ↥B.vertices) b).val at hClone
  omega

/-- The canonical abstract strong pushout uses A points
literally and fresh actual old B points only for B
vertices outside the displayed base. -/
noncomputable def commonBlockAmalgamPoint
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B) :
    FiniteUnion.Union (A := ↥A.vertices) t.toEmbedding →
      Sigma CommonBlockReal
  | .inl a => a.val
  | .inr b => commonBlockFreshBPoint C A B s t b.val

/-- The full old real point assignment is injective on
the abstract union, including all real named sorts.
Only displayed C base points are identified. -/
theorem commonBlockAmalgamPoint_injective
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B) :
    Function.Injective (commonBlockAmalgamPoint C A B s t) := by
  intro u v h
  cases u with
  | inl a =>
    cases v with
    | inl b =>
        congr 1
        exact Subtype.ext h
    | inr b =>
        exact False.elim
          (commonBlockFreshBPoint_disjoint_A C A B s t a b.val h)
  | inr a =>
    cases v with
    | inl b =>
        exact False.elim
          (commonBlockFreshBPoint_disjoint_A C A B s t b a.val h.symm)
    | inr b =>
        congr 1
        apply Subtype.ext
        exact commonBlockFreshBPoint_injective C A B s t h

/-- The left old copy is pointwise ACTUAL identity. -/
theorem commonBlockAmalgamPoint_left
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B)
    (a : ↥A.vertices) :
    commonBlockAmalgamPoint C A B s t
      (FiniteUnion.left t.toEmbedding a) = a.val := rfl

/-- Every B old point, both anchored and unanchored,
retains its actual original named sort under the
canonical strong amalgam map. -/
theorem commonBlockAmalgamPoint_right_sort
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B)
    (b : ↥B.vertices) :
    (commonBlockAmalgamPoint C A B s t
      (FiniteUnion.right s.toEmbedding t.toEmbedding b)).1 =
        b.val.1 := by
  classical
  by_cases hb : b ∈ Set.range t.toEmbedding
  · obtain ⟨c,rfl⟩ := hb
    rw [FiniteUnion.right_base]
    change (s.toEmbedding c).val.1 = (t.toEmbedding c).val.1
    exact (s.preserves_sort c).trans (t.preserves_sort c).symm
  · rw [FiniteUnion.right_off s.toEmbedding t.toEmbedding b hb]
    rfl

/-- The B copy has its exact compatible block label,
even on points belonging to the displayed common base. -/
theorem commonBlockAmalgamPoint_right_block
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B)
    (b : ↥B.vertices) :
    (commonBlockAmalgamPoint C A B s t
      (FiniteUnion.right s.toEmbedding t.toEmbedding b)).2.1 =
        commonBlockAmalgamLabel C A B s t b := by
  classical
  by_cases hb : b ∈ Set.range t.toEmbedding
  · obtain ⟨c,rfl⟩ := hb
    rw [FiniteUnion.right_base]
    exact (commonBlockAmalgamLabel_base C A B s t
      (t.toEmbedding c) c rfl).symm
  · rw [FiniteUnion.right_off s.toEmbedding t.toEmbedding b hb]
    rfl

/-- The resulting old B pair relation for block equality
is exactly the original B relation, including mixed real
sorts and same-sort off-diagonal pairs. -/
theorem commonBlockAmalgamPoint_right_block_iff
    (C A B : FiniteInduced (X := CommonBlockReal))
    (s : InducedEmbedding commonBlockOriginalAtomicSource C A)
    (t : InducedEmbedding commonBlockOriginalAtomicSource C B)
    (b b' : ↥B.vertices) :
    (commonBlockAmalgamPoint C A B s t
      (FiniteUnion.right s.toEmbedding t.toEmbedding b)).2.1 =
      (commonBlockAmalgamPoint C A B s t
        (FiniteUnion.right s.toEmbedding t.toEmbedding b')).2.1 ↔
      b.val.2.1 = b'.val.2.1 := by
  rw [commonBlockAmalgamPoint_right_block C A B s t b,
    commonBlockAmalgamPoint_right_block C A B s t b']
  exact commonBlockAmalgamLabel_eq_iff C A B s t b b'

end CCO.UnaryTermsReturn
