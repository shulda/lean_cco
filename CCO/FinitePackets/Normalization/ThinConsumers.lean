import CCO.FinitePackets.Normalization.ElementaryAbelian
import CCO.FinitePackets.Normalization.ColourTransport
import CCO.FinitePackets.Normalization.MinimalCutSubgroups
import CCO.FinitePackets.Normalization.TerminalThin
import CCO.FinitePackets.Geometry.CutCrossing
import CCO.FinitePackets.Normalization.Examples.TwinConsumer

/-! Downstream source instances: the ACTUAL terminal greatest packet has
the regular elementary-abelian group and the whole minimal-cut subgroup
interval.  The true twin-cell source separately refutes the converse. -/
universe v w t
namespace CCO.FinitePackets.Normalization
open CCO.RealHull.Geometry CCO.ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (hterm : NoFiniteExactKernel S)
include H hterm

theorem terminal_actual_packet_group :
    ThinBottom S (Geometry.sigma S H ⊥) ∧
    ∃ d : Nat, Nonempty (Translation S (Geometry.sigma S H ⊥) G ≃*
      Multiplicative (Fin d → ZMod 2)) ∧
      Nat.card (Translation S (Geometry.sigma S H ⊥) G) = 2^d := by
  have hthin := terminal_greatest_finite_packet_thin S H hterm
  exact ⟨hthin,translation_elementary_abelian S (Geometry.sigma S H ⊥) H hthin⟩

theorem terminal_actual_minimal_cut [Infinite M] :
    ∃ E : ColourEq S (), Geometry.MinimalInfiniteCut S E ∧
      Nonempty (Set.Iic E ≃o WithTop (Subgroup (equivalenceTranslations S
        (Geometry.sigma S H ⊥) (G := G) (E ⊓ Geometry.sigma S H ⊥)))) := by
  obtain ⟨E,hE⟩ := Geometry.exists_minimal_infinite_cut S
  exact ⟨E,hE,⟨minimalCutSubgroupIso S (Geometry.sigma S H ⊥) H
    (terminal_greatest_finite_packet_thin S H hterm) E hE (Geometry.sigma_bottom_spec S H)⟩⟩

section Identity
omit H hterm

theorem identity_packet_thin : ThinBottom S (⊥ : ColourEq S ()) := by
  intro c hc
  obtain ⟨x,y,hxy⟩ := colour_realized S c
  have he : x = y := hc x y hxy
  have hn : c = none := hxy.symm.trans ((col_none S x y).mpr he)
  rw [hn]
  exact thin_none S

theorem identity_translation_eq_one (e : Translation S (⊥ : ColourEq S ()) G) : e = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact (e.property.2 x).symm

theorem identity_translation_card : Nat.card (Translation S (⊥ : ColourEq S ()) G) = 1 := by
  letI : Subsingleton (Translation S (⊥ : ColourEq S ()) G) :=
    ⟨fun e f => (identity_translation_eq_one S e).trans (identity_translation_eq_one S f).symm⟩
  exact Nat.card_unique

end Identity

omit H hterm

namespace Examples.Twin

theorem actual_thin_bottom : ThinBottom source packetEq := by
  intro c hc
  cases c with
  | none => exact thin_none source
  | some a =>
    obtain ⟨x,y,hxy⟩ := source.realized a
    exact all_packet_atoms_thin a ⟨x,y,hc x y hxy,hxy⟩

theorem regularizer_stops_but_exact_normalization_does_not :
    squareKernel source homogeneous packetEq = ⊥ ∧ ¬ NoFiniteExactKernel source := by
  refine ⟨squareKernel_eq_bot_of_thin source homogeneous packetEq actual_thin_bottom,?_⟩
  intro hterm
  have hfin : Geometry.FiniteIndex source ⊥ packetEq :=
    (Geometry.finiteIndex_bottom_iff_finite_classes source packetEq).mpr packet_finite
  obtain ⟨B,hB⟩ := packet_exact
  exact packet_nonidentity (hterm packetEq hfin B hB)

theorem actual_twin_packet_elementary :
    ∃ d : Nat, Nonempty (Translation source packetEq Aut ≃*
      Multiplicative (Fin d → ZMod 2)) ∧ Nat.card (Translation source packetEq Aut) = 2^d :=
  translation_elementary_abelian source packetEq homogeneous actual_thin_bottom

noncomputable def actual_twin_row_subgroup_interval :
    Set.Iic rowEq ≃o WithTop (Subgroup (equivalenceTranslations source packetEq
      (G := Aut) (rowEq ⊓ packetEq))) :=
  minimalCutSubgroupIso source packetEq homogeneous actual_thin_bottom rowEq
    row_minimal_infinite (by
      rw [← finitePacket_eq]
      exact Geometry.sigma_bottom_spec source homogeneous)

end Examples.Twin
end CCO.FinitePackets.Normalization
