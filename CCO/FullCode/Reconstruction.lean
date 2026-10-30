import CCO.FullCode.SupportEquivalence
import CCO.FullCode.ExpandedRestriction
import CCO.FullCode.PresentationQuotient

/-! Complete codes recover the ENTIRE actual marked support structure,
not only its underlying set or its unmarked isomorphism type. -/
universe u v w a b
namespace CCO.FullCode.Object
variable {L : Language.{u}} {V : Type v} {W : Type w}
  {C : Structure L V} {D : Structure L W} {S : RootScheme L}
  {A : Type a} {B : Type b} {N : NormalForms L}
  {O : Object C S A} {P : Object D S B}

theorem Embedding.support_reconstructed (f : Embedding N O P) (hC : N.Valid C)
    (hD : N.Valid D) (surj : Function.Surjective f.point) :
    O.supportStructure = P.supportStructure.comapEquiv (f.supportEquiv hC hD surj) :=
  (f.onSupport hC hD).source_eq_of_same_point
    (P.supportStructure.comapEquivEmbedding (f.supportEquiv hC hD surj)) (fun _ => rfl)

theorem Embedding.unique_marked_extension (f : Embedding N O P) (hC : N.Valid C)
    (hD : N.Valid D) :
    ∃! g : Structure.Embedding O.supportStructure P.supportStructure,
      ∀ a j, g.point ⟨(O.root a).coordinate j, O.coordinate_mem_support a j⟩ =
        (f.onSupport hC hD).point ⟨(O.root a).coordinate j, O.coordinate_mem_support a j⟩ := by
  refine ⟨f.onSupport hC hD, fun _ _ => rfl, ?_⟩
  intro g hg
  exact O.embedding_unique_on_coordinates hg

end CCO.FullCode.Object
