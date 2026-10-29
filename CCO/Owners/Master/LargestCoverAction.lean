import CCO.GroupActions

/-! Transfer the largest-cover action invariant to every nested pair.
The intermediate group map need not be onto. Empty carriers, infinite
groups and nonfaithful actions are all allowed. -/

namespace CCO.Owners.Master

variable {GL GY GZ L Y Z : Type*} [Group GL] [Group GY] [Group GZ]
variable [MulAction GL L] [MulAction GY Y] [MulAction GZ Z]

/-- Descent of onto group maps and fibre-transitive kernels, using actual
commuting maps. No point-action equivalence with a nonempty premise is used. -/
theorem largest_cover_action
    (a : GL →* GY) (b : GY →* GZ) (c : GL →* GZ)
    (triangle : ∀ g, b (a g) = c g)
    (q : L → Y) (r : Y → Z) (ontoq : Function.Surjective q)
    (equivq : ∀ g l, q (g • l) = a g • q l)
    (ontoc : Function.Surjective c)
    (fibre : GroupActions.FibreTransitive c (r ∘ q)) :
    Function.Surjective b ∧ GroupActions.FibreTransitive b r := by
  constructor
  · intro g
    obtain ⟨k, hk⟩ := ontoc g
    exact ⟨a k, (triangle k).trans hk⟩
  · intro x y hxy
    obtain ⟨l, hl⟩ := ontoq x
    obtain ⟨l', hl'⟩ := ontoq y
    obtain ⟨k, hk, hmove⟩ := fibre l l' (by
      simpa only [Function.comp_apply, hl, hl'] using hxy)
    refine ⟨a k, (triangle k).trans hk, ?_⟩
    calc
      a k • x = a k • q l := by rw [hl]
      _ = q (k • l) := (equivq k l).symm
      _ = q l' := congrArg q hmove
      _ = y := hl'

/-- The whole prescribed target element is also retained under descent.
This direct implication needs neither inhabited carriers nor a surjective
intermediate group map. -/
theorem largest_cover_prescribed
    (a : GL →* GY) (b : GY →* GZ) (c : GL →* GZ)
    (triangle : ∀ g, b (a g) = c g)
    (q : L → Y) (r : Y → Z) (ontoq : Function.Surjective q)
    (equivq : ∀ g l, q (g • l) = a g • q l)
    (lift : GroupActions.PrescribedLift c (r ∘ q)) :
    GroupActions.PrescribedLift b r := by
  intro x y g hxy
  obtain ⟨l, hl⟩ := ontoq x
  obtain ⟨l', hl'⟩ := ontoq y
  obtain ⟨k, hk, hmove⟩ := lift l l' g (by
    simpa only [Function.comp_apply, hl, hl'] using hxy)
  refine ⟨a k, (triangle k).trans hk, ?_⟩
  calc
    a k • x = a k • q l := by rw [hl]
    _ = q (k • l) := (equivq k l).symm
    _ = q l' := congrArg q hmove
    _ = y := hl'

end CCO.Owners.Master
