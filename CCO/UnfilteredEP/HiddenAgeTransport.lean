import CCO.UnfilteredEP.GeneratedHostReadout
import CCO.FullCode.ExpansionSetting

/-! Literal transport of hidden-age membership along induced bijections.
All function domains and values are carried by the displayed old map. -/

universe u v
namespace CCO.UnfilteredEP
open CCO.FullCode
noncomputable section
variable {L : Language.{u}} (K : FiniteHidden.{u,v} L → Prop)

/-- Iso-closed age membership transports to the target of an actual
bijective full induced map. It is not a mere unmarked isomorphism claim. -/
theorem hidden_member_of_bijective_embedding
    (isoClosed : HiddenIsoClosed K)
    {A B : FiniteHidden.{u,v} L} (member : K A)
    (f : Structure.Embedding A.model B.model) (onto : Function.Surjective f.point) :
    K B := by
  let e : B.Carrier ≃ A.Carrier := (Equiv.ofBijective f.point ⟨f.injective,onto⟩).symm
  have equal : A.model.comapEquiv e = B.model :=
    (A.model.comapEquivEmbedding e).source_eq_of_same_point
      (inverseInduced f onto) (fun _ => rfl)
  have actual := isoClosed A member B.Carrier e
  change K ⟨B.Carrier,B.model,B.finite⟩
  rw [← equal]
  exact actual

/-- Heredity and actual isomorphism closure imply membership for every
full induced subobject map, including arbitrary finite carrier copies. -/
theorem hidden_member_of_embedding
    (hereditary : HereditaryHidden K) (isoClosed : HiddenIsoClosed K)
    {A B : FiniteHidden.{u,v} L} (member : K B)
    (f : Structure.Embedding A.model B.model) : K A := by
  let C := B.induced (Set.range f.point) f.range_closed
  have hC : K C := hereditary B member _ _
  let e : A.Carrier ≃ C.Carrier := Equiv.ofBijective
    (fun x => ⟨f.point x,⟨x,rfl⟩⟩)
    ⟨fun _ _ h => f.injective (congrArg Subtype.val h),by
      rintro ⟨y,⟨x,rfl⟩⟩
      exact ⟨x,rfl⟩⟩
  let g := (B.model.inclusion (Set.range f.point) f.range_closed).comp
    (C.model.comapEquivEmbedding e)
  have equal : C.model.comapEquiv e = A.model :=
    g.source_eq_of_same_point f (fun _ => rfl)
  have actual := isoClosed C hC A.Carrier e
  change K ⟨A.Carrier,A.model,A.finite⟩
  rw [← equal]
  exact actual

end
end CCO.UnfilteredEP
