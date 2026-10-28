import CCO.SIR.Positive.Direct.CycleConsistency
import Mathlib.Data.Fintype.EquivFin

/-! Realize a finite signed-component diagram by actual natural-number
parents, Boolean sheets, and distinct natural-number fibre points. -/

universe z

namespace CCO.SIR.Positive.Direct

variable {V : Type z} (D : PartialDiagram source V)

/-- Explicit realization once the two elementary consequences of simple-cycle
consistency have been established. The public CCO theorem discharges both.
-/
theorem injective_realization_of_parent_separation
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    (hsep : ∀ x y (h : x ≠ y), D.edge x y h = some .n →
      ¬ (edGraph D).Reachable x y) :
    ∃ f : DiagramHom D, f.IsInjective := by
  classical
  letI : Finite V := D.finite_type
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype (edGraph D).ConnectedComponent := Fintype.ofFinite _
  let pid : (edGraph D).ConnectedComponent → ℕ :=
    fun C => (Fintype.equivFin _ C).val
  have hpid : Function.Injective pid :=
    Fin.val_injective.comp (Fintype.equivFin _).injective
  let vid : V → ℕ := fun v => (Fintype.equivFin V v).val
  have hvid : Function.Injective vid :=
    Fin.val_injective.comp (Fintype.equivFin V).injective
  obtain ⟨s,hs⟩ := SignedWalk.exists_potential (sign D) (closed_sign_zero D hcycles)
  let point : V → Point := fun v =>
    (pid ((edGraph D).connectedComponentMk v), s v, vid v)
  have hpoint (x y : V) (hxy : x ≠ y) : point x ≠ point y := by
    intro heq
    exact hxy (hvid (congrArg index heq))
  have hparent {x y : V} (hadj : (edGraph D).Adj x y) :
      F (point x) (point y) :=
    congrArg pid (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj)
  have he {x y : V} (hxy : x ≠ y) (he : D.edge x y hxy = some .e) :
      colour (point x) (point y) = some .e := by
    apply (colour_e _ _).mpr
    refine ⟨hpoint x y hxy,hparent ⟨hxy,Or.inl he⟩,?_⟩
    have hh := (hs x y ⟨hxy,Or.inl he⟩).symm.trans (sign_e D hxy he)
    change s x = s y
    cases hx : s x <;> cases hy : s y <;> simp_all
  have hd {x y : V} (hxy : x ≠ y) (hd : D.edge x y hxy = some .d) :
      colour (point x) (point y) = some .d := by
    apply (colour_d _ _).mpr
    refine ⟨hparent ⟨hxy,Or.inr hd⟩,?_⟩
    have hh := (hs x y ⟨hxy,Or.inr hd⟩).symm.trans (sign_d D hxy hd)
    change s x ≠ s y
    cases hx : s x <;> cases hy : s y <;> simp_all
  have hn {x y : V} (hxy : x ≠ y) (hn : D.edge x y hxy = some .n) :
      colour (point x) (point y) = some .n := by
    apply (colour_n _ _).mpr
    intro hp
    have hc : (edGraph D).connectedComponentMk x =
        (edGraph D).connectedComponentMk y := hpid hp
    exact hsep x y hxy hn (SimpleGraph.ConnectedComponent.exact hc)
  let f : DiagramHom D := {
    point := point
    preserves_edge := by
      intro x y hxy a ha
      cases a with
      | e => exact he hxy ha
      | d => exact hd hxy ha
      | n => exact hn hxy ha
  }
  refine ⟨f,?_⟩
  intro x y hxy
  apply hvid
  exact congrArg (fun q : Sigma (fun _ : Unit => Point) => index q.2) hxy

theorem realization_of_parent_separation
    (hcycles : ∀ C : SimpleCycle D, CycleHom C)
    (hsep : ∀ x y (h : x ≠ y), D.edge x y h = some .n →
      ¬ (edGraph D).Reachable x y) :
    Nonempty (DiagramHom D) := by
  obtain ⟨f,_⟩ := injective_realization_of_parent_separation D hcycles hsep
  exact ⟨f⟩

end CCO.SIR.Positive.Direct
