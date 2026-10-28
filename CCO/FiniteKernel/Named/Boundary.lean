import CCO.FiniteKernel.Named.CheckSource

/-! Empty, singleton and empty-axis boundaries for the ACTUAL named-axis
source. No finite cardinal convention conceals an infinite ambient group.
-/

universe u v w z
namespace CCO.FiniteKernel.NamedAxes
noncomputable section

variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : NamedAxes S I)

theorem actualImage_empty : P.actualImage (∅ : Finset I) = ⊤ := by
  apply Subgroup.ext
  intro p
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨1,?_⟩
    funext i
    exact False.elim (Finset.notMem_empty i.val i.property)

theorem checkPairs_empty : IsEmpty (P.CheckPairs (∅ : Finset I)) := by
  refine ⟨fun p => ?_⟩
  exact Finset.notMem_empty p.val.1.val p.val.1.property

theorem checkPairs_singleton (i : I) : IsEmpty (P.CheckPairs ({i} : Finset I)) := by
  refine ⟨fun p => ?_⟩
  have h1 : p.val.1.val = i := Finset.mem_singleton.mp p.val.1.property
  have h2 : p.val.2.val = i := Finset.mem_singleton.mp p.val.2.property
  have he : p.val.1 = p.val.2 := Subtype.ext (h1.trans h2.symm)
  exact (Nat.ne_of_lt p.property) (congrArg (P.coordinateCode {i}) he)

theorem empty_axis_intrinsic_subsingleton (i : I)
    (hempty : ∀ x : X, ¬ S.unary (P.name i) x) : Subsingleton (P.Intrinsic i) := by
  refine ⟨?_⟩
  intro g h
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact False.elim (hempty x.val x.property)

end
end CCO.FiniteKernel.NamedAxes
