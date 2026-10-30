import CCO.ResetOrder.Counterexample.Successor

/-! Isomorphism closure of the three concrete ages: transport every symbol
on the actual carrier. Orders and successor functions are transported too. -/
universe u v
namespace CCO.ResetOrder.Counterexample.Nested
variable {X : Type u} {Y : Type v} (A : Nested X) (e : X ≃ Y)

def relabel : Nested Y where
  P := A.P.comap e.symm
  Q := A.Q.comap e.symm
  refine := A.refine

def relabelEmbedding : Embedding A (A.relabel e) where
  point := e
  injective := e.injective
  p_iff x y := by
    change A.P.r (e.symm (e x)) (e.symm (e y)) ↔ A.P.r x y
    simp only [e.symm_apply_apply]
  q_iff x y := by
    change A.Q.r (e.symm (e x)) (e.symm (e y)) ↔ A.Q.r x y
    simp only [e.symm_apply_apply]

namespace ConvexOrder
variable {A} (a : ConvexOrder A)

def relabel : ConvexOrder (A.relabel e) := by
  letI := a.order
  exact {
    order := LinearOrder.lift' e.symm e.symm.injective
    convexP := fun h₁ h₂ hR => a.convexP h₁ h₂ hR
    convexQ := fun h₁ h₂ hR => a.convexQ h₁ h₂ hR }

def relabelEmbedding : Embedding a (a.relabel e) where
  toEmbedding := A.relabelEmbedding e
  lt_iff x y := by
    change a.order.lt (e.symm (e x)) (e.symm (e y)) ↔ a.order.lt x y
    simp only [e.symm_apply_apply]

namespace Successor
variable {a} (s : Successor a)

def relabel : Successor (a.relabel e) where
  next y := e (s.next (e.symm y))
  sameP y := by
    change A.P.r (e.symm y) (e.symm (e (s.next (e.symm y))))
    simpa only [e.symm_apply_apply] using s.sameP (e.symm y)
  le_next y := by
    change a.order.le (e.symm y) (e.symm (e (s.next (e.symm y))))
    simpa only [e.symm_apply_apply] using s.le_next (e.symm y)
  least x y hP hxy := by
    change a.order.le (e.symm (e (s.next (e.symm x)))) (e.symm y)
    simpa only [e.symm_apply_apply] using s.least (e.symm x) (e.symm y) hP hxy
  strict x h := by
    obtain ⟨y, hP, hxy⟩ := h
    change a.order.lt (e.symm x) (e.symm (e (s.next (e.symm x))))
    simpa only [e.symm_apply_apply] using s.strict (e.symm x) ⟨e.symm y, hP, hxy⟩

def relabelEmbedding : Embedding s (s.relabel e) where
  toOrderedEmbedding := a.relabelEmbedding e
  map_next x := by
    change e (s.next x) = e (s.next (e.symm (e x)))
    rw [e.symm_apply_apply]

end Successor
end ConvexOrder
end CCO.ResetOrder.Counterexample.Nested
