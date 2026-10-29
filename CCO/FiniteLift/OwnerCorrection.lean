import CCO.FiniteLift.OwnerCover

/-! C24: ONE chosen action lift followed by ONE kernel correction.
This is the only extra group hypothesis needed for relative roots,
separate from all externally prescribed source-extension requests. -/

universe v w t
namespace CCO.FiniteLift
open Owners.Product OwnerCover
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (HS : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K H : ExactKernel S G)

theorem owner_kernel_point (Bbar : Set (J S HS cco K H).Q)
    (onto : Function.Surjective (ownerAction S HS cco K H Bbar))
    (fibres : GroupActions.FibreTransitive (ownerAction S HS cco K H Bbar)
      (fun b : ((rH S HS cco K H) ⁻¹' Bbar) => fullProjection (rH S HS cco K H) Bbar b))
    (b b' : ((rH S HS cco K H) ⁻¹' Bbar))
    (δ : OrbitalAut G (J S HS cco K H).Q (Subtype.val : Bbar → (J S HS cco K H).Q))
    (hδ : δ.val (fullProjection (rH S HS cco K H) Bbar b) =
      fullProjection (rH S HS cco K H) Bbar b') :
    ∃ γ, ownerAction S HS cco K H Bbar γ = δ ∧ γ.val b = b' := by
  obtain ⟨γ₀,hγ₀⟩ := onto δ
  have he : fullProjection (rH S HS cco K H) Bbar (γ₀.val b) =
      fullProjection (rH S HS cco K H) Bbar b' := by
    have hh := (fullOwnerQuotient S HS cco K H Bbar).action_projection γ₀ b
    change (ownerAction S HS cco K H Bbar γ₀).val
      (fullProjection (rH S HS cco K H) Bbar b) =
        fullProjection (rH S HS cco K H) Bbar (γ₀.val b) at hh
    rw [hγ₀] at hh
    exact hh.symm.trans hδ
  obtain ⟨η,hη,hηb⟩ := fibres (γ₀.val b) b' he
  refine ⟨η * γ₀,?_,?_⟩
  · rw [map_mul,hη,hγ₀,one_mul]
  · exact hηb

end CCO.FiniteLift
