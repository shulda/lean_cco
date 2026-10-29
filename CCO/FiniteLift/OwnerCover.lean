import CCO.FiniteLift.Join
import CCO.FiniteLift.Recognition
import Mathlib.Data.Set.Finite.Lattice

/-! C19–C20: finite COMPLETE inverse owner packets, literal owner images
and the honest induced full finite group maps. No onto/kernel group
assumption is used to construct these maps or to prove packet finiteness. -/

universe v w t
namespace CCO.FiniteLift
open Owners.Product Owners.Provider
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (HS : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K H : ExactKernel S G)

namespace OwnerCover

abbrev J := ExactKernel.join S HS cco K H
abbrev rK := ExactKernel.toJoinK S HS cco K H
abbrev rH := ExactKernel.toJoinH S HS cco K H

/-- Every fibre of the H-to-common-owner map is covered by ANY one
finite real K-class above it, including equality/degenerate quotients. -/
theorem fibre_finite (finiteK : K.FiniteClasses) (c : (J S HS cco K H).Q) :
    ((rH S HS cco K H) ⁻¹' {c}).Finite := by
  obtain ⟨x,rfl⟩ := (J S HS cco K H).onto c
  apply ((finiteK x).image H.proj).subset
  intro b hb
  have he : rK S HS cco K H (K.proj x) = rH S HS cco K H b := hb.symm
  obtain ⟨a,ha,hb'⟩ := class_incidence S HS cco K H (K.proj x) b he
  exact ⟨a,(K.proj_eq x a).mp ha.symm,hb'⟩

theorem complete_packet_finite (finiteK : K.FiniteClasses)
    (Bbar : Set (J S HS cco K H).Q) (finiteBbar : Bbar.Finite) :
    ((rH S HS cco K H) ⁻¹' Bbar).Finite :=
  finiteBbar.preimage' (fun c _ => fibre_finite S HS cco K H finiteK c)

/-- Complete incidence, not a hand-selected finite owner subset. -/
theorem owner_image (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (imageD : rK S HS cco K H '' Dbar = Bbar) :
    H.proj '' fullPreimage K.proj Dbar = (rH S HS cco K H) ⁻¹' Bbar := by
  ext b
  constructor
  · rintro ⟨a,ha,rfl⟩
    change rH S HS cco K H (H.proj a) ∈ Bbar
    rw [← imageD]
    exact ⟨K.proj a,ha,rfl⟩
  · intro hb
    have hb' : rH S HS cco K H b ∈ rK S HS cco K H '' Dbar := imageD ▸ hb
    obtain ⟨q,hq,he⟩ := hb'
    obtain ⟨a,ha,hb⟩ := class_incidence S HS cco K H q b he
    exact ⟨a,by change K.proj a ∈ Dbar; rw [ha]; exact hq,hb⟩

def fullOwnerQuotient (Bbar : Set (J S HS cco K H).Q) :
    OrbitalQuotient (G := G)
      (Subtype.val : ((rH S HS cco K H) ⁻¹' Bbar) → H.Q)
      (Subtype.val : Bbar → (J S HS cco K H).Q) :=
  fullQuotient (rH S HS cco K H) (toJoinH_onto S HS cco K H)
    (toJoinH_smul S HS cco K H) Bbar

noncomputable def ownerAction (Bbar : Set (J S HS cco K H).Q) :=
  (fullOwnerQuotient S HS cco K H Bbar).action

def quotientOwnerProjection (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (imageD : rK S HS cco K H '' Dbar = Bbar) : Dbar → Bbar :=
  fun q => ⟨rK S HS cco K H q.val,by rw [← imageD]; exact ⟨q.val,q.property,rfl⟩⟩

theorem quotientOwnerProjection_onto (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (imageD : rK S HS cco K H '' Dbar = Bbar) :
    Function.Surjective (quotientOwnerProjection S HS cco K H Dbar Bbar imageD) := by
  intro b
  have hb : b.val ∈ rK S HS cco K H '' Dbar := imageD ▸ b.property
  obtain ⟨q,hq,he⟩ := hb
  exact ⟨⟨q,hq⟩,Subtype.ext he⟩

def quotientOwner (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (imageD : rK S HS cco K H '' Dbar = Bbar) :
    OrbitalQuotient (G := G) (Subtype.val : Dbar → K.Q)
      (Subtype.val : Bbar → (J S HS cco K H).Q) where
  ambient := rK S HS cco K H
  equivariant := toJoinK_smul S HS cco K H
  projection := quotientOwnerProjection S HS cco K H Dbar Bbar imageD
  surjective := quotientOwnerProjection_onto S HS cco K H Dbar Bbar imageD
  target_injective := Subtype.val_injective
  commutes _ := rfl

def realOwnerProjection (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (imageD : rK S HS cco K H '' Dbar = Bbar) :
    fullPreimage K.proj Dbar → ((rH S HS cco K H) ⁻¹' Bbar) :=
  fun x => ⟨H.proj x.val,by
    rw [← owner_image S HS cco K H Dbar Bbar imageD]
    exact ⟨x.val,x.property,rfl⟩⟩

theorem realOwnerProjection_onto (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (imageD : rK S HS cco K H '' Dbar = Bbar) :
    Function.Surjective (realOwnerProjection S HS cco K H Dbar Bbar imageD) := by
  intro b
  have hb : b.val ∈ H.proj '' fullPreimage K.proj Dbar :=
    (owner_image S HS cco K H Dbar Bbar imageD).symm ▸ b.property
  obtain ⟨x,hx,he⟩ := hb
  exact ⟨⟨x,hx⟩,Subtype.ext he⟩

def realOwner (Dbar : Set K.Q) (Bbar : Set (J S HS cco K H).Q)
    (imageD : rK S HS cco K H '' Dbar = Bbar) :
    OrbitalQuotient (G := G) (Subtype.val : fullPreimage K.proj Dbar → A)
      (Subtype.val : ((rH S HS cco K H) ⁻¹' Bbar) → H.Q) where
  ambient := H.proj
  equivariant := H.proj_smul
  projection := realOwnerProjection S HS cco K H Dbar Bbar imageD
  surjective := realOwnerProjection_onto S HS cco K H Dbar Bbar imageD
  target_injective := Subtype.val_injective
  commutes _ := rfl

end OwnerCover
end CCO.FiniteLift
