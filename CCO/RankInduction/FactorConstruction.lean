import CCO.RankInduction.SourceStage
import CCO.RankInduction.AmalgamationBridge
import CCO.RankInduction.OrbitalTransfer

/-! All principal inputs of B028 in each actual maximal normalized
factor, from ONE already fixed strict lower-rank master. Only the
ordinary EPPA theorem in the literal strict fine quotient is recursive. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT CanonicalQuotients Owners.Product Owners.Provider Owners.Master
open MIGeometry ParityHasse.Original FinitePackets.Normalization RealClosure.Bounds AclOwners RelativeMI

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M] [DecidableEq M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (normalized : NoFiniteExactKernel S) (A0 : Finset M)
variable (B : LowerMaster S H cco normalized (↑A0 : Set M)) (D : Direction S)

local instance factorConstructionCoreAction : MulAction G (Quotient (factorCore S H cco D).val) :=
  originalQuotientAction S H (hat S H (semanticCCO_change_universe S cco) D)
local instance factorConstructionOwnerInvariant : Invariant G (factorOwner S H cco normalized D).val :=
  exactInvariant S H cco (factorOwner S H cco normalized D)
local instance factorConstructionJointInvariant : Invariant G (jointKernel S H cco normalized).val :=
  exactInvariant S H cco (jointKernel S H cco normalized)
local instance factorConstructionCoarseInvariant :
    Invariant G (coarseCut S H (semanticCCO_change_universe S cco) normalized D).val :=
  ⟨colourInvariant_groupInvariant (factorSource S H (semanticCCO_change_universe S cco) D)
    (factorH S H (semanticCCO_change_universe S cco) D)
    (coarseCut S H (semanticCCO_change_universe S cco) normalized D).property⟩
local instance factorConstructionCoarseAction : MulAction G
    (Quotient (coarseCut S H (semanticCCO_change_universe S cco) normalized D).val) :=
  originalQuotientAction (factorSource S H (semanticCCO_change_universe S cco) D)
    (factorH S H (semanticCCO_change_universe S cco) D)
    (coarseCut S H (semanticCCO_change_universe S cco) normalized D)

def factorSeed : Finset (Quotient (factorCore S H cco D).val) := by
  classical
  exact A0.image Quotient.mk''

theorem factorSeed_coe : (↑(factorSeed S H cco A0 D) : Set _) = factorInput S H cco (↑A0) D := by
  simp only [factorSeed, factorInput, Finset.coe_image]

theorem factorOwners_finite : (factorOwners S H cco normalized B D).Finite :=
  B.finite.image _

def coarseOwnerSet := (coarseEquiv S H (semanticCCO_change_universe S cco) normalized D).symm ''
  factorOwners S H cco normalized B D

theorem coarseOwnerSet_finite : (coarseOwnerSet S H cco normalized A0 B D).Finite :=
  (factorOwners_finite S H cco normalized A0 B D).image _

def coarseOwners := (coarseOwnerSet_finite S H cco normalized A0 B D).toFinset

theorem coarseOwners_coe : (↑(coarseOwners S H cco normalized A0 B D) : Set _) =
    coarseOwnerSet S H cco normalized A0 B D :=
  (coarseOwnerSet_finite S H cco normalized A0 B D).coe_toFinset

/-- The actual finite coarse set is the inverse image of the ENTIRE
original owner image, and its identification keeps every point. -/
def coarseOwnerEquiv : (coarseOwners S H cco normalized A0 B D) ≃ factorOwners S H cco normalized B D where
  toFun b := ⟨coarseEquiv S H (semanticCCO_change_universe S cco) normalized D b.val, by
    have hb : b.val ∈ coarseOwnerSet S H cco normalized A0 B D := by
      rw [← coarseOwners_coe S H cco normalized A0 B D]
      exact b.property
    obtain ⟨c, hc, hcb⟩ := hb
    rw [← hcb, Equiv.apply_symm_apply]
    exact hc⟩
  invFun b := ⟨(coarseEquiv S H (semanticCCO_change_universe S cco) normalized D).symm b.val, by
    apply (coarseOwnerSet_finite S H cco normalized A0 B D).mem_toFinset.mpr
    exact ⟨b.val, b.property, rfl⟩⟩
  left_inv b := Subtype.ext ((coarseEquiv S H (semanticCCO_change_universe S cco) normalized D).symm_apply_apply b.val)
  right_inv b := Subtype.ext ((coarseEquiv S H (semanticCCO_change_universe S cco) normalized D).apply_symm_apply b.val)

@[simp] theorem coarseOwnerEquiv_val (b : coarseOwners S H cco normalized A0 B D) :
    (coarseOwnerEquiv S H cco normalized A0 B D b).val =
      coarseEquiv S H (semanticCCO_change_universe S cco) normalized D b.val := rfl

theorem seed_owner_native (x : factorSeed S H cco A0 D) :
    coarseProjection S H (semanticCCO_change_universe S cco) normalized D x.val ∈
      factorOwners S H cco normalized B D := by
  classical
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp x.property
  refine ⟨Quotient.mk'' a, B.contains ⟨a, ha, rfl⟩, ?_⟩
  exact congrArg (coarseProjection S H (semanticCCO_change_universe S cco) normalized D) heq

theorem seed_over_coarse (x : factorSeed S H cco A0 D) :
    coarseOwner (factorSource S H (semanticCCO_change_universe S cco) D)
      (factorH S H (semanticCCO_change_universe S cco) D)
      (coarseCut S H (semanticCCO_change_universe S cco) normalized D) x.val ∈
        coarseOwners S H cco normalized A0 B D := by
  apply (coarseOwnerSet_finite S H cco normalized A0 B D).mem_toFinset.mpr
  refine ⟨coarseProjection S H (semanticCCO_change_universe S cco) normalized D x.val,
    seed_owner_native S H cco normalized A0 B D x, ?_⟩
  apply (coarseEquiv S H (semanticCCO_change_universe S cco) normalized D).injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem old_owner_membership (b : Quotient (coarseCut S H (semanticCCO_change_universe S cco) normalized D).val) :
    b ∈ (Quotient.mk'' : Quotient (factorCore S H cco D).val → _) ''
        (↑(factorSeed S H cco A0 D) : Set _) ↔
      coarseEquiv S H (semanticCCO_change_universe S cco) normalized D b ∈
        nestedImage S H cco (jointKernel S H cco normalized) (factorOwner S H cco normalized D)
          (jointKernel_le_owner S H cco normalized D)
          ((Quotient.mk'' : M → Quotient (jointKernel S H cco normalized).val) '' (↑A0 : Set M)) := by
  classical
  constructor
  · rintro ⟨q, hq, heq⟩
    obtain ⟨a, ha, haq⟩ := Finset.mem_image.mp hq
    refine ⟨Quotient.mk'' a, ⟨a, ha, rfl⟩, ?_⟩
    exact (congrArg (coarseProjection S H (semanticCCO_change_universe S cco) normalized D) haq).trans
      (congrArg (coarseEquiv S H (semanticCCO_change_universe S cco) normalized D) heq)
  · rintro ⟨q, ⟨a, ha, haq⟩, hqb⟩
    refine ⟨Quotient.mk'' a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, ?_⟩
    apply (coarseEquiv S H (semanticCCO_change_universe S cco) normalized D).injective
    exact (congrArg (Abstract.quotientMap (jointKernel_le_owner S H cco normalized D)) haq).trans hqb

/-- M1 is exactly the source's coarse EPPA-witness input, after the
canonical double-quotient identification. -/
theorem coarse_eppa : CoarseEPPAFor
    (factorSource S H (semanticCCO_change_universe S cco) D)
    (factorH S H (semanticCCO_change_universe S cco) D)
    (coarseCut S H (semanticCCO_change_universe S cco) normalized D)
    (factorSeed S H cco A0 D) (coarseOwners S H cco normalized A0 B D) := by
  classical
  letI : MulAction G (Quotient (coarseCut S H (semanticCCO_change_universe S cco) normalized D).val) :=
    originalQuotientAction (factorSource S H (semanticCCO_change_universe S cco) D)
      (factorH S H (semanticCCO_change_universe S cco) D)
      (coarseCut S H (semanticCCO_change_universe S cco) normalized D)
  let e := coarseEquiv S H (semanticCCO_change_universe S cco) normalized D
  let E := coarseOwnerEquiv S H cco normalized A0 B D
  apply eppaFor_equiv (G := G) e.symm
    (equivariant_symm (G := G) e (coarseEquiv_equivariant S H (semanticCCO_change_universe S cco) normalized D))
    E.symm (by
      intro b
      apply e.injective
      exact (congrArg Subtype.val (E.apply_symm_apply b)).trans (e.apply_symm_apply b.val).symm)
  have preimage : E.symm ⁻¹' {b | b.val ∈
      (Quotient.mk'' : Quotient (factorCore S H cco D).val → _) ''
        (↑(factorSeed S H cco A0 D) : Set _)} =
      {b | b.val ∈ nestedImage S H cco (jointKernel S H cco normalized)
        (factorOwner S H cco normalized D) (jointKernel_le_owner S H cco normalized D)
        ((Quotient.mk'' : M → Quotient (jointKernel S H cco normalized).val) '' (↑A0 : Set M))} := by
    ext b
    change (E.symm b).val ∈ (Quotient.mk'' : Quotient (factorCore S H cco D).val → _) ''
      (↑(factorSeed S H cco A0 D) : Set _) ↔ _
    rw [old_owner_membership S H cco normalized A0 D]
    have h := congrArg Subtype.val (E.apply_symm_apply b)
    exact Iff.of_eq (congrArg (fun c => c ∈ _) h)
  change EPPAFor (G := G)
    (ι := (Subtype.val : factorOwners S H cco normalized B D → Quotient (factorOwner S H cco normalized D).val))
    (E.symm ⁻¹' {b | b.val ∈ (Quotient.mk'' : Quotient (factorCore S H cco D).val → _) ''
      (↑(factorSeed S H cco A0 D) : Set _)})
  rw [preimage]
  exact master_image_eppa S H cco (jointKernel S H cco normalized)
    (factorOwner S H cco normalized D) (jointKernel_le_owner S H cco normalized D) B

end
end CCO.RankInduction.Factors
