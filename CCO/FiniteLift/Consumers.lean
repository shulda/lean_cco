import CCO.FiniteLift.Source

/-! Common-witness consumers actually invoke the complete source theorem.
The partial-map extension and independently requested rooted transport
live on the ONE literal full K-preimage, never on separately trimmed sets. -/

universe v w t
namespace CCO.FiniteLift
open Owners.Product OwnerCover
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (HS : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K : ExactKernel S G)

include HS cco

theorem ordinary_common_witness (finiteK : K.FiniteClasses)
    (safe : Set (S.Atom () ())) (A0 : Set A) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty)
    (Dbar : Set K.Q)
    (w : OrdinaryWitness (G := G) (aclSet (FullAut G K.Q))
      (quotientSafePalette S K safe) (K.proj '' A0) Dbar)
    (p : OrbitalPartial (G := G) (Subtype.val : (K.proj ⁻¹' Dbar) → A))
    (hDom : p.domain ⊆ {x | x.val ∈ A0}) (hRan : ∀ x, p.map x ∈ {x | x.val ∈ A0})
    (Z : Set (K.proj ⁻¹' Dbar))
    (hZ : Unsafe (fun x y : (K.proj ⁻¹' Dbar) => S.menuRel safe x.val y.val) Z)
    (z : (K.proj ⁻¹' Dbar)) (hz : z ∈ Z) :
    (K.proj ⁻¹' Dbar).Finite ∧ aclSet G A0 ⊆ K.proj ⁻¹' Dbar ∧
      ∃ α β : OrbitalAut G A (Subtype.val : (K.proj ⁻¹' Dbar) → A),
        p.Extends α ∧ (∀ x ∈ Z, (β.val x).val ∈ aclSet G A0) ∧ (β.val z).val ∈ A0 := by
  have W := (finite_lift S HS cco K finiteK safe).ordinary A0 finiteA nonemptyA Dbar w
  obtain ⟨α,hα⟩ := W.extensions p hDom hRan
  obtain ⟨β,hβZ,hβz⟩ := W.roots Z hZ z hz
  exact ⟨W.finite,W.closure,α,β,hα,hβZ,hβz⟩

theorem relative_common_witness (finiteK : K.FiniteClasses)
    (safe : Set (S.Atom () ())) (A0 : Set A) (finiteA : A0.Finite) (nonemptyA : A0.Nonempty)
    (H : ExactKernel S G) (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (finiteBbar : Bbar.Finite) (imageD : rK S HS cco K H '' Dbar = Bbar)
    (onto : Function.Surjective (ownerAction S HS cco K H Bbar))
    (fibres : GroupActions.FibreTransitive (ownerAction S HS cco K H Bbar)
      (fun b : ((rH S HS cco K H) ⁻¹' Bbar) => fullProjection (rH S HS cco K H) Bbar b))
    (w : RelativeWitness (quotientOwner S HS cco K H Dbar Bbar imageD)
      (aclSet (FullAut G K.Q)) (quotientSafePalette S K safe) (K.proj '' A0))
    (p : OrbitalPartial (G := G) (Subtype.val : (K.proj ⁻¹' Dbar) → A))
    (hDom : p.domain ⊆ {x | x.val ∈ A0}) (hRan : ∀ x, p.map x ∈ {x | x.val ∈ A0})
    (γ : OrbitalAut G H.Q (Subtype.val : ((rH S HS cco K H) ⁻¹' Bbar) → H.Q))
    (compatible : ∀ x : p.domain,
      (realOwner S HS cco K H Dbar Bbar imageD).projection (p.map x) =
        γ.val ((realOwner S HS cco K H Dbar Bbar imageD).projection x.val))
    (Z : Set (K.proj ⁻¹' Dbar))
    (hZ : Unsafe (fun x y : (K.proj ⁻¹' Dbar) => S.menuRel safe x.val y.val) Z)
    (z : (K.proj ⁻¹' Dbar)) (hz : z ∈ Z) :
    ((rH S HS cco K H) ⁻¹' Bbar).Finite ∧
      H.proj '' (K.proj ⁻¹' Dbar) = (rH S HS cco K H) ⁻¹' Bbar ∧
      (K.proj ⁻¹' Dbar).Finite ∧ aclSet G A0 ⊆ K.proj ⁻¹' Dbar ∧
      ∃ α β : OrbitalAut G A (Subtype.val : (K.proj ⁻¹' Dbar) → A),
        p.Extends α ∧ (realOwner S HS cco K H Dbar Bbar imageD).action α = γ ∧
        (∀ x ∈ Z, (β.val x).val ∈ aclSet G A0) ∧ (β.val z).val ∈ A0 := by
  have W := (finite_lift S HS cco K finiteK safe).relative A0 finiteA nonemptyA H
    Dbar Bbar finiteBbar imageD onto fibres w
  obtain ⟨α,hα,hαγ⟩ := W.extensions p hDom hRan γ compatible
  obtain ⟨β,hβZ,hβz⟩ := W.roots Z hZ z hz
  exact ⟨complete_packet_finite S HS cco K H finiteK Bbar finiteBbar,
    owner_image S HS cco K H Dbar Bbar imageD,W.finite,W.closure,α,β,hα,hαγ,hβZ,hβz⟩

end CCO.FiniteLift
