import AllThoseEPPA.TreeLikeTreeIrreducibleExtension
import AllThoseEPPA.TreeLikeInfiniteCopiesSurjectiveInverse
import AllThoseEPPA.TreeLikeInfiniteCopiesGlueCarrier

/-! Every actual tree vertex lies in a FULL source copy, including
one-generated closures whose singleton is not a closed substructure. -/
universe u v w
namespace CCO.HKNReservoir
open AllThoseEPPA
variable {L : Language.{u}} {Γ : Type w} [Group Γ]
variable (act : L.Action Γ) {U : Type v} (A : Structure L U)

theorem tree_vertex_in_full_copy {V : Type v} {D : Structure L V}
    (tree : TreeLike.TreeAmalgamation act A D) (x : V) :
    ∃ f : Structure.Embedding act A D, x ∈ Set.range f.toFun := by
  obtain ⟨f,hf⟩ := tree.everyIrreducibleExtendsToA act A
    (D.closureAtSet x) (D.isClosed_closureSet {x}) (D.closureAt_isIrreducible x)
  exact ⟨f,hf (D.mem_closureAtSet x)⟩

theorem finite_tree_carrier [Finite U] {V : Type v} {D : Structure L V}
    (tree : TreeLike.TreeAmalgamation act A D) : Finite V := by
  induction tree with
  | copy C f hsurj => exact Finite.of_surjective f.toFun hsurj
  | glue C B₁ B₂ h₁ h₂ δ₁ δ₂ α₁ α₂ ih₁ ih₂ =>
    letI := ih₁
    letI := ih₂
    infer_instance

/-- Exact cross-intersection makes the concrete amalgam map globally injective.
This distinguishes an actual realization from a homomorphism-embedding
which could collapse unrelated packets. -/
theorem gluedCarrierMap_injective {I : Type*} {X : Type*} {Y : Type*} {N : Type*}
    (f : I → X) (g : I → Y) (l : X → N) (r : Y → N)
    (hl : Function.Injective l) (hr : Function.Injective r)
    (hcross : ∀ x y, l x = r y → ∃ i, f i = x ∧ g i = y) :
    Function.Injective (TreeLike.gluedCarrierMap f g l r) := by
  intro p q he
  cases p with
  | inl x =>
    cases q with
    | inl y => exact congrArg Sum.inl (hl he)
    | inr y =>
      obtain ⟨i,_,hi⟩ := hcross x y.val he
      exact False.elim (y.property ⟨i,hi⟩)
  | inr x =>
    cases q with
    | inl y =>
      obtain ⟨i,_,hi⟩ := hcross y x.val he.symm
      exact False.elim (x.property ⟨i,hi⟩)
    | inr y => exact congrArg Sum.inr (Subtype.ext (hr he))

end CCO.HKNReservoir
