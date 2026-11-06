import CCO.AclOwners.UnaryTransfer
import CCO.DirectOwnerClosure.DirectHull
import CCO.RawExact.DiagramReindex
import Mathlib.Order.Irreducible

/-! Optional N10: the ORIGINAL greatest finite-class equivalence being
proper FULL meet-irreducible supplies exactly one original minimal infinite
direction by the generic C19 commuting-lattice argument. ONLY the direct
original C07 closure theorem is then used. No thin normalization, exact
owner correspondence, quotient source or later clone kernel enters. This
optional branch is forbidden ancestry of the four main B060 exports. -/

universe v w t
namespace CCO.CloneTupleGeometry.OptionalFMI
open ParityHasse.Original FinitePackets.Geometry
noncomputable section

/-- Finite FULL-lattice MI provides a least strict coarsening; this is not
an assumption that the greatest finite packet is already exact. -/
theorem least_strict_of_infIrred {L : Type*} [Lattice L] [OrderTop L] [Finite L]
    {F : L} (hF : InfIrred F) : ∃ D : L, F < D ∧ ∀ E : L, F < E → D ≤ E := by
  obtain ⟨D,hFD,hmin⟩ := wellFounded_lt.has_min {E : L | F < E}
    ⟨⊤,lt_top_iff_ne_top.mpr hF.ne_top⟩
  refine ⟨D,hFD,?_⟩
  intro E hFE
  by_contra hDE
  have hm : D ⊓ E = F := by
    apply le_antisymm ?_ (le_inf hFD.le hFE.le)
    by_contra hle
    have hFm : F < D ⊓ E := lt_of_le_of_ne (le_inf hFD.le hFE.le)
      (fun he => hle he.symm.le)
    have hmD : D ⊓ E < D := lt_of_le_of_ne inf_le_left (fun he =>
      hDE (he ▸ (show D ⊓ E ≤ E from inf_le_right)))
    exact hmin _ hFm hmD
  rcases hF.2 hm with he | he
  · exact hFD.ne' he
  · exact hFE.ne' he

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

/-- The literal FULL source lattice, with no exactness or normalization
restriction. Only its generic finite commuting-lattice properties are used. -/
def sourceFullSublattice : Sublattice (Setoid M) where
  carrier := {E | ColourInvariant S () E}
  infClosed' := by
    intro E hE F hF x y x' y' hc
    exact and_congr (hE x y x' y' hc) (hF x y x' y' hc)
  supClosed' := by
    intro E hE F hF
    exact (ColourEq.join S H ⟨E,hE⟩ ⟨F,hF⟩).property

/-- Actual original-source C64–C67. The only extra premise is precisely
that the ORIGINAL greatest finite-class equivalence Sigma(Id) is proper
FULL MI. It is not a premise about the eventual clone kernel. -/
theorem original_unique_direction
    (hF : InfIrred (sigma S H (⊥ : ColourEq S ()))) :
    ∃ E : ColourEq S (), DirectOwnerClosure.UniqueDirection S E := by
  let L := sourceFullSublattice S H
  letI : Finite L := inferInstanceAs (Finite (ColourEq S ()))
  letI := ColourEq.lattice S H (i := ())
  let F : ColourEq S () := sigma S H ⊥
  obtain ⟨D,hFD,hleast⟩ := least_strict_of_infIrred hF
  have hcomm : ExactCRT.Abstract.Commutes L := by
    intro E F
    exact invariant_relations_commute S H E.property F.property
  have hfinite : AclOwners.Unary.FiniteClasses F.val :=
    (AclOwners.Unary.finiteClasses_iff F.val).mpr (finiteIndex_sigma S H ⊥)
  have hgreatest : ∀ E : L, AclOwners.Unary.FiniteClasses E.val → E ≤ F := by
    intro E hE
    exact sigma_greatest S H bot_le ((AclOwners.Unary.finiteClasses_iff E.val).mp hE)
  have hi (E : ColourEq S ()) : AclOwners.Unary.MinimalInfinite L E ↔
      MinimalInfiniteCut S E := by
    constructor
    · rintro ⟨hE,hmin⟩
      refine ⟨fun h => hE ((AclOwners.Unary.finiteClasses_iff E.val).mpr h),?_⟩
      intro J hJE
      exact (AclOwners.Unary.finiteClasses_iff J.val).mp (hmin J hJE)
    · rintro ⟨hE,hmin⟩
      refine ⟨fun h => hE ((AclOwners.Unary.finiteClasses_iff E.val).mp h),?_⟩
      intro J hJE
      exact (AclOwners.Unary.finiteClasses_iff J.val).mpr (hmin J hJE)
  obtain ⟨E,hE,huniq⟩ := AclOwners.Unary.unique_minimal_infinite L hcomm
    F D hfinite hgreatest hFD hleast
  exact ⟨E,(hi E).mp hE,fun J hJ => huniq J ((hi J).mpr hJ)⟩

/-- Actual original C68: the original proper-F-MI premise discharges the
unique-direction input of the direct real-closure C07 theorem. Every finite
base, including the empty base, has exactly the ORIGINAL finite-packet hull. -/
theorem original_all_finite_base_packet_closure [Infinite M]
    (cco : SemanticCCO.{0,v,v,w} S)
    (hF : InfIrred (sigma S H (⊥ : ColourEq S ()))) :
    ∀ A : Finset M, DirectOwnerClosure.algebraicClosure
      (DirectOwnerClosure.FullAut S) A = DirectOwnerClosure.packetHull S H A := by
  classical
  obtain ⟨E,hE⟩ := original_unique_direction S H hF
  exact DirectOwnerClosure.direct_real_acl S H (semanticCCO_change_universe S cco) hE

end
end CCO.CloneTupleGeometry.OptionalFMI
