import CCO.ResetOrder.Counterexample.Rectangular

/-! Every convex order on the uniform rectangular host contains the given
ordered source. The host is chosen before its arbitrary competitor order. -/
namespace CCO.ResetOrder.Counterexample
namespace Rectangle
variable {n : ℕ} (o : (rectangleBase n).ConvexOrder) (d : Fin n)

def pOrder : LinearOrder (Fin n) := by
  letI := o.order
  exact LinearOrder.lift' (fun p => (p, d, d)) (fun _ _ h => congrArg Prod.fst h)

def qOrder (p : Fin n) : LinearOrder (Fin n) := by
  letI := o.order
  exact LinearOrder.lift' (fun q => (p, q, d)) (fun _ _ h => congrArg (fun x : Rectangle n => x.2.1) h)

def vOrder (p q : Fin n) : LinearOrder (Fin n) := by
  letI := o.order
  exact LinearOrder.lift' (fun v => (p, q, v)) (fun _ _ h => congrArg (fun x : Rectangle n => x.2.2) h)

noncomputable def pPerm : Fin n ≃ Fin n := by
  letI := pOrder o d
  exact (Fintype.orderIsoFinOfCardEq (Fin n) (Fintype.card_fin n)).toEquiv

noncomputable def qPerm (p : Fin n) : Fin n ≃ Fin n := by
  letI := qOrder o d p
  exact (Fintype.orderIsoFinOfCardEq (Fin n) (Fintype.card_fin n)).toEquiv

noncomputable def vPerm (p q : Fin n) : Fin n ≃ Fin n := by
  letI := vOrder o p q
  exact (Fintype.orderIsoFinOfCardEq (Fin n) (Fintype.card_fin n)).toEquiv

theorem pPerm_lt (p p' : Fin n) :
    (pOrder o d).lt (pPerm o d p) (pPerm o d p') ↔ p < p' := by
  exact @OrderIso.lt_iff_lt (Fin n) (Fin n) Fin.instLinearOrder.toPreorder
    (pOrder o d).toPreorder
    (@Fintype.orderIsoFinOfCardEq (Fin n) (pOrder o d) _ n (Fintype.card_fin n)) _ _

theorem qPerm_lt (p q q' : Fin n) :
    (qOrder o d p).lt (qPerm o d p q) (qPerm o d p q') ↔ q < q' := by
  exact @OrderIso.lt_iff_lt (Fin n) (Fin n) Fin.instLinearOrder.toPreorder
    (qOrder o d p).toPreorder
    (@Fintype.orderIsoFinOfCardEq (Fin n) (qOrder o d p) _ n (Fintype.card_fin n)) _ _

theorem vPerm_lt (p q v v' : Fin n) :
    (vOrder o p q).lt (vPerm o p q v) (vPerm o p q v') ↔ v < v' := by
  exact @OrderIso.lt_iff_lt (Fin n) (Fin n) Fin.instLinearOrder.toPreorder
    (vOrder o p q).toPreorder
    (@Fintype.orderIsoFinOfCardEq (Fin n) (vOrder o p q) _ n (Fintype.card_fin n)) _ _

/-- Coarse class, fine class, then point comparison, for the ACTUAL arbitrary
convex order. No coordinate-order hypothesis is imposed on the competitor. -/
theorem arbitrary_lt_iff (p q v p' q' v' : Fin n) :
    o.order.lt (p, q, v) (p', q', v') ↔
      (pOrder o d).lt p p' ∨ p = p' ∧
        ((qOrder o d p).lt q q' ∨ q = q' ∧ (vOrder o p q).lt v v') := by
  by_cases hp : p = p'
  · subst p'
    have hpp : ¬ (pOrder o d).lt p p := by
      exact @lt_irrefl (Fin n) (pOrder o d).toPreorder p
    simp only [hpp, false_or, true_and]
    by_cases hq : q = q'
    · subst q'
      have hqq : ¬ (qOrder o d p).lt q q := by
        exact @lt_irrefl (Fin n) (qOrder o d p).toPreorder q
      simp only [hqq, false_or, true_and]
      rfl
    · simp only [hq, false_and, or_false]
      exact compare_convex_classes o.order (rectangleBase n).Q o.convexQ
        (x := (p, q, v)) (y := (p, q', v'))
        (x' := (p, q, d)) (y' := (p, q', d)) rfl rfl
        (fun h => hq (congrArg (fun z : Fin n × Fin n => z.2) h))
  · simp only [hp, false_and, or_false]
    exact compare_convex_classes o.order (rectangleBase n).P o.convexP
      (x := (p, q, v)) (y := (p', q', v'))
      (x' := (p, d, d)) (y' := (p', d, d)) rfl rfl hp

noncomputable def permute (x : Rectangle n) : Rectangle n :=
  let p := pPerm o d x.1
  let q := qPerm o d p x.2.1
  (p, q, vPerm o p q x.2.2)

/-- A real embedding of the canonically ordered rectangle into ANY convex
ordering of that same base. In fact the constructed map is a permutation. -/
noncomputable def orderEmbedding : Nested.ConvexOrder.Embedding (rectangleOrder n) o where
  point := permute o d
  injective := by
    rintro ⟨p, q, v⟩ ⟨p', q', v'⟩ h
    have hp : p = p' := (pPerm o d).injective (congrArg Prod.fst h)
    subst p'
    have hq : q = q' := (qPerm o d (pPerm o d p)).injective
      (congrArg (fun x : Rectangle n => x.2.1) h)
    subst q'
    have hv : v = v' := (vPerm o (pPerm o d p) (qPerm o d (pPerm o d p) q)).injective
      (congrArg (fun x : Rectangle n => x.2.2) h)
    subst v'
    rfl
  p_iff x y := (pPerm o d).injective.eq_iff
  q_iff := by
    rintro ⟨p, q, v⟩ ⟨p', q', v'⟩
    change (pPerm o d p, qPerm o d (pPerm o d p) q) =
      (pPerm o d p', qPerm o d (pPerm o d p') q') ↔ (p, q) = (p', q')
    constructor
    · intro h
      have hp := (pPerm o d).injective (congrArg Prod.fst h)
      subst p'
      exact Prod.ext rfl ((qPerm o d (pPerm o d p)).injective (congrArg Prod.snd h))
    · intro h
      cases h
      rfl
  lt_iff := by
    rintro ⟨p, q, v⟩ ⟨p', q', v'⟩
    change o.order.lt
      (pPerm o d p, qPerm o d (pPerm o d p) q,
        vPerm o (pPerm o d p) (qPerm o d (pPerm o d p) q) v)
      (pPerm o d p', qPerm o d (pPerm o d p') q',
        vPerm o (pPerm o d p') (qPerm o d (pPerm o d p') q') v') ↔ _
    rw [arbitrary_lt_iff o d, rectangle_lt_iff]
    rw [pPerm_lt]
    by_cases hp : p = p'
    · subst p'
      simp only [true_and]
      rw [qPerm_lt, (qPerm o d (pPerm o d p)).injective.eq_iff]
      by_cases hq : q = q'
      · subst q'
        simp only [true_and]
        rw [vPerm_lt]
      · simp only [hq, false_and, or_false]
    · have hp' : pPerm o d p ≠ pPerm o d p' := (pPerm o d).injective.ne hp
      simp only [hp, hp', false_and, or_false]

end Rectangle

/-- Exact fixed-host lower expansion property, including the empty source. -/
theorem lower_EP_quantifier {X : Type*} [Finite X] {A : Nested X} (a : A.ConvexOrder) :
    ∀ o : (rectangleBase (Nat.card X)).ConvexOrder,
      Nonempty (Nested.ConvexOrder.Embedding a o) := by
  intro o
  by_cases h : Nat.card X = 0
  · haveI : IsEmpty X := by
      letI := Fintype.ofFinite X
      exact Fintype.card_eq_zero_iff.mp (by simpa only [Nat.card_eq_fintype_card] using h)
    exact ⟨{
      point := isEmptyElim
      injective := fun x => isEmptyElim x
      p_iff := fun x => isEmptyElim x
      q_iff := fun x => isEmptyElim x
      lt_iff := fun x => isEmptyElim x }⟩
  · let d : Fin (Nat.card X) := ⟨0, Nat.pos_of_ne_zero h⟩
    exact ⟨(Rectangle.orderEmbedding o d).comp a.rankEmbedding⟩

end CCO.ResetOrder.Counterexample
