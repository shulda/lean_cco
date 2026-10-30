import CCO.FiniteFibres.Automorphisms
import CCO.FiniteFibres.AtomicAdapter
import CCO.FiniteFibres.Real.Basic

/-! Enumeration identifies the two FULL original automorphism groups.
No dense earlier subgroup is substituted for either full group. -/
universe u v
namespace CCO.FiniteFibres
variable {A : Type u} (S : AtomicSource.{0,u,v} Unit (fun _ => A)) [Fintype A]

noncomputable def fullAutEquiv : Real.Aut S ≃ Aut (targetOfAtomic S) := by
  let e : A ≃ Fin (targetOfAtomic S).size := Fintype.equivFin A
  exact {
    toFun := fun g => ⟨e.symm.trans (g.val.trans e),by
      intro x y
      change S.colour (i := ()) (j := ()) (e.symm (e (g.val (e.symm x))))
        (e.symm (e (g.val (e.symm y)))) = S.colour (e.symm x) (e.symm y)
      simpa only [Equiv.symm_apply_apply] using g.property (e.symm x) (e.symm y)⟩
    invFun := fun h => ⟨e.trans (h.val.trans e.symm),by
      intro x y
      exact (h.property (e x) (e y)).trans (targetOfAtomic_edge S x y)⟩
    left_inv := by
      intro g
      apply Subtype.ext
      apply Equiv.ext
      intro x
      change e.symm (e (g.val (e.symm (e x)))) = g.val x
      simp only [Equiv.symm_apply_apply]
    right_inv := by
      intro h
      apply Subtype.ext
      apply Equiv.ext
      intro x
      change e (e.symm (h.val (e (e.symm x)))) = h.val x
      simp only [Equiv.apply_symm_apply] }

theorem source_fullAut_two_group (cco : CCO.SemanticCCO.{0,u,0,v} S) :
    ∃ k : Nat, Nat.card (Real.Aut S) = 2^k := by
  obtain ⟨k,hk⟩ := automorphism_two_group (targetOfAtomic S) (targetOfAtomic_CCO S cco)
  exact ⟨k,(Nat.card_congr (fullAutEquiv S)).trans hk⟩

end CCO.FiniteFibres
