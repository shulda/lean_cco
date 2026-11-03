import CCO.UnaryTermsReturn.CommonBlockAmalgamPoints

/-!
# B052 C16: genuine ORIGINAL age SAP for the two-sort common-block model

This theorem proves the actual source10 SAP condition, rather than
assuming it for the example. The age consists of complete finite
induced diagrams on the true two-sorted old Nat-block/Nat-clone
carriers, with literal equality for repeated real points and an
atomic same/different-block colour at every distinct typed pair.

The strong pushout uses the ACTUAL finite union A ⊔_C B.
Its real-point assignment was constructed in
CommonBlockAmalgamPoints:
  - the A side remains literal old points;
  - B blocks touching C are mapped to precisely the corresponding
    A blocks, even across different original sorts;
  - other B blocks are placed strictly above all A blocks;
  - fresh B clone indices are above all A clone indices.

No two points are identified except the displayed C base and
the target is a finite induced substructure of the same ACTUAL
old source. No hidden quotient SAP/CCO, new axiom, positive
STRONG diagonal, or HN theorem is used.

The companion original semantic CCO is independently proved in
CommonBlockSemanticCCO. Together these constitute the genuine
old SAP+CCO example needed for malformed-unary-cycle diagnostic.
-/

namespace CCO.UnaryTermsReturn

open CCO
open CCO.CloneSAP

/-- The old atomic tagged colour is completely determined by
the original old sort tags, literal real equality and old block
equality. An injective sort-preserving map which preserves
and REFLECTS block equality therefore preserves every true
fine old colour, including the real diagonal.

The statement compares four ACTUAL original points, not an
uninterpreted hidden quotient graph. -/
theorem commonBlockTaggedColour_of_sort_eq_block_eq
    (p q r s : Sigma CommonBlockReal)
    (hpr : p.1 = r.1) (hqs : q.1 = s.1)
    (heq : p = q ↔ r = s)
    (hblock : p.2.1 = q.2.1 ↔ r.2.1 = s.2.1) :
    taggedColour commonBlockOriginalAtomicSource p q =
      taggedColour commonBlockOriginalAtomicSource r s := by
  rcases p with ⟨i,x⟩
  rcases q with ⟨j,y⟩
  rcases r with ⟨i',x'⟩
  rcases s with ⟨j',y'⟩
  dsimp at hpr hqs
  cases hpr
  cases hqs
  suffices hColour : commonBlockOldColour i j x y =
      commonBlockOldColour i j x' y' by
    exact congrArg (fun c : Option Bool =>
      (⟨i, j, c⟩ : Σ i : Bool, Σ j : Bool, Option Bool)) hColour
  by_cases hxy : (⟨i,x⟩ : Sigma CommonBlockReal) = ⟨j,y⟩
  · have hxy' : (⟨i,x'⟩ : Sigma CommonBlockReal) =
        ⟨j,y'⟩ := heq.mp hxy
    simp only [commonBlockOldColour,if_pos hxy,if_pos hxy']
  · have hxy' : (⟨i,x'⟩ : Sigma CommonBlockReal) ≠
        ⟨j,y'⟩ := fun h => hxy (heq.mpr h)
    simp only [commonBlockOldColour,if_neg hxy,if_neg hxy',
      Option.some.injEq]
    by_cases hb : x.1 = y.1
    · have hb' : x'.1 = y'.1 := hblock.mp hb
      simp only [decide_eq_true_eq.mpr hb,
        decide_eq_true_eq.mpr hb']
    · have hb' : x'.1 ≠ y'.1 := fun h => hb (hblock.mpr h)
      simp [hb,hb']

/-- ACTUAL source10 C16 AgeSAP witness. No missing original
provider: every pair of finite induced embeddings C→A and
C→B has a common finite induced D, genuine induced embeddings
A→D and B→D, the exact base commutation, and the strong
intersection condition. Old CCO is not used to prove SAP. -/
theorem commonBlockOriginalAgeSAP :
    AgeSAP commonBlockOriginalAtomicSource := by
  classical
  refine ⟨?_⟩
  intro C A B eCA eCB
  let s := eCA.toEmbedding
  let t := eCB.toEmbedding
  let U := FiniteUnion.Union (A := ↥A.vertices) t
  let h : U ↪ Sigma CommonBlockReal := {
    toFun := commonBlockAmalgamPoint C A B eCA eCB
    inj' := commonBlockAmalgamPoint_injective C A B eCA eCB
  }
  let D : FiniteInduced (X := CommonBlockReal) := {
    vertices := Set.range h
    finite_vertices := Set.finite_range h
  }
  let lift : U ↪ ↥D.vertices := {
    toFun := fun u => ⟨h u,⟨u,rfl⟩⟩
    inj' := by
      intro u v huv
      exact h.injective (congrArg Subtype.val huv)
  }
  let aMap : ↥A.vertices ↪ ↥D.vertices :=
    (FiniteUnion.left t).trans lift
  let bMap : ↥B.vertices ↪ ↥D.vertices :=
    (FiniteUnion.right s t).trans lift
  let aEmb : InducedEmbedding commonBlockOriginalAtomicSource A D := {
    toEmbedding := aMap
    preserves_sort := by
      intro a
      rfl
    preserves_colours := by
      intro a b
      rfl
  }
  let bEmb : InducedEmbedding commonBlockOriginalAtomicSource B D := {
    toEmbedding := bMap
    preserves_sort := by
      intro b
      exact commonBlockAmalgamPoint_right_sort
        C A B eCA eCB b
    preserves_colours := by
      intro b b'
      have hsort : b.val.1 = (bMap b).val.1 :=
        (commonBlockAmalgamPoint_right_sort
          C A B eCA eCB b).symm
      have hsort' : b'.val.1 = (bMap b').val.1 :=
        (commonBlockAmalgamPoint_right_sort
          C A B eCA eCB b').symm
      have hEq : b.val = b'.val ↔
          (bMap b).val = (bMap b').val := by
        constructor
        · intro heq
          exact congrArg Subtype.val
            (congrArg bMap (Subtype.ext heq))
        · intro heq
          exact congrArg Subtype.val
            (bMap.injective (Subtype.ext heq))
      have hBlock : b.val.2.1 = b'.val.2.1 ↔
          (bMap b).val.2.1 = (bMap b').val.2.1 :=
        (commonBlockAmalgamPoint_right_block_iff
          C A B eCA eCB b b').symm
      exact commonBlockTaggedColour_of_sort_eq_block_eq
        b.val b'.val (bMap b).val (bMap b').val
        hsort hsort' hEq hBlock
  }
  refine ⟨D,aEmb,bEmb,?_,?_⟩
  · intro c
    exact congrArg lift (FiniteUnion.commute s t c)
  · intro a b heq
    have hUnion : FiniteUnion.left t a =
        FiniteUnion.right s t b := lift.injective heq
    exact FiniteUnion.intersection s t a b hUnion

end CCO.UnaryTermsReturn
