import CCO.UnaryTermsReturn.CommonBlockFreshness
import CCO.Finite

/-!
# B052 C16 — original two-sorted block equality encoded in fine colours

The actual old binary atomic type distinguishes the genuine logical
diagonal, same-block DIVERSITY and different-block DIVERSITY.
Equality of underlying common block labels is therefore precisely
the disjunction of (1) literal tagged real identity or (2) the
true old fine atom some true.

Consequently EVERY original finite fully induced embedding preserves
AND REFLECTS the common block equivalence, including the mixed-sort
case. This is a prerequisite for constructing actual strong-age
amalgams by aligning anchored blocks and choosing fresh unanchored
blocks. No original SAP/CCO/homogeneity hypothesis is assumed.
-/

namespace CCO.UnaryTermsReturn

/-- Real old block equality includes the true original diagonal,
while the positive fine atom some true covers the off-diagonal
same-block pairs. No fictitious fine equality atom appears. -/
theorem commonBlockOldBlockEq_iff
    (p q : Sigma CommonBlockReal) :
    p.2.1 = q.2.1 ↔
      p = q ∨ commonBlockOldColour p.1 q.1 p.2 q.2 = some true := by
  classical
  by_cases hpq : p = q
  · subst q
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      rfl
  · have hColour :
        commonBlockOldColour p.1 q.1 p.2 q.2 =
          some (decide (p.2.1 = q.2.1)) := by
      simp only [commonBlockOldColour, if_neg hpq]
    constructor
    · intro hb
      right
      rw [hColour]
      exact congrArg Option.some (decide_eq_true_eq.mpr hb)
    · intro hh
      rcases hh with hEq | hSome
      · exact False.elim (hpq hEq)
      · rw [hColour] at hSome
        exact decide_eq_true_eq.mp (Option.some.inj hSome)

/-- The COMPLETE old induced embedding preserves and reflects the
real block equivalence on every typed pair. The proof uses BOTH
the preserved old fine colour and genuine point injectivity,
so same-sort diagonal pairs are not mistaken for diversity. -/
theorem commonBlockInducedEmbedding_preserves_block
    (A B : FiniteInduced (X := CommonBlockReal))
    (e : InducedEmbedding commonBlockOriginalAtomicSource A B)
    (p q : ↥A.vertices) :
    p.val.2.1 = q.val.2.1 ↔
      (e.toEmbedding p).val.2.1 =
        (e.toEmbedding q).val.2.1 := by
  let f := e.toEmbedding
  have hEq : p.val = q.val ↔ (f p).val = (f q).val := by
    constructor
    · intro h
      exact congrArg Subtype.val (congrArg f (Subtype.ext h))
    · intro h
      have hSub : f p = f q := Subtype.ext h
      exact congrArg Subtype.val (f.injective hSub)
  have hColour :
      commonBlockOldColour p.val.1 q.val.1 p.val.2 q.val.2 =
        commonBlockOldColour (f p).val.1 (f q).val.1
          (f p).val.2 (f q).val.2 := by
    exact congrArg
      (fun z : Σ _ : Bool, Σ _ : Bool, Option Bool => z.2.2)
      (e.preserves_colours p q)
  constructor
  · intro hb
    rcases (commonBlockOldBlockEq_iff p.val q.val).mp hb with h | h
    · exact (commonBlockOldBlockEq_iff (f p).val (f q).val).mpr
        (Or.inl (hEq.mp h))
    · exact (commonBlockOldBlockEq_iff (f p).val (f q).val).mpr
        (Or.inr (hColour.symm.trans h))
  · intro hb
    rcases (commonBlockOldBlockEq_iff (f p).val (f q).val).mp hb with h | h
    · exact (commonBlockOldBlockEq_iff p.val q.val).mpr
        (Or.inl (hEq.mpr h))
    · exact (commonBlockOldBlockEq_iff p.val q.val).mpr
        (Or.inr (hColour.trans h))

end CCO.UnaryTermsReturn
