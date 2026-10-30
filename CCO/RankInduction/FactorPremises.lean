import CCO.RankInduction.FactorConstruction

/-! Orbit coverage, full owner packets and the strictly lower fine EPPA
input are all derived before invoking the actual normalized B028 theorem. -/

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

local instance factorPremisesCoreAction : MulAction G (Quotient (factorCore S H cco D).val) :=
  originalQuotientAction S H (hat S H (semanticCCO_change_universe S cco) D)
local instance factorPremisesOwnerInvariant : Invariant G (factorOwner S H cco normalized D).val :=
  exactInvariant S H cco (factorOwner S H cco normalized D)
local instance factorPremisesJointInvariant : Invariant G (jointKernel S H cco normalized).val :=
  exactInvariant S H cco (jointKernel S H cco normalized)
local instance factorPremisesFineInvariant : Invariant G (Fine S H (semanticCCO_change_universe S cco) D).val :=
  exactInvariant S H cco (Fine S H (semanticCCO_change_universe S cco) D)
local instance factorPremisesCoarseAction : MulAction G
    (Quotient (coarseCut S H (semanticCCO_change_universe S cco) normalized D).val) :=
  originalQuotientAction (factorSource S H (semanticCCO_change_universe S cco) D)
    (factorH S H (semanticCCO_change_universe S cco) D)
    (coarseCut S H (semanticCCO_change_universe S cco) normalized D)
local instance factorPremisesFineAction : MulAction G
    (Quotient (fineCut S H (semanticCCO_change_universe S cco) D).val) :=
  originalQuotientAction (factorSource S H (semanticCCO_change_universe S cco) D)
    (factorH S H (semanticCCO_change_universe S cco) D)
    (fineCut S H (semanticCCO_change_universe S cco) D)

/-- Full finite owner transitivity comes from M3 to Top. An ORIGINAL
projected seed point supplies the old orbit representative. -/
theorem coarse_orbit (nonemptyA : A0.Nonempty) : CoarseOrbitCover
    (factorSource S H (semanticCCO_change_universe S cco) D)
    (factorH S H (semanticCCO_change_universe S cco) D)
    (coarseCut S H (semanticCCO_change_universe S cco) normalized D)
    (factorSeed S H cco A0 D) (coarseOwners S H cco normalized A0 B D)
    (seed_over_coarse S H cco normalized A0 B D) := by
  classical
  letI : MulAction G (Quotient (coarseCut S H (semanticCCO_change_universe S cco) normalized D).val) :=
    originalQuotientAction (factorSource S H (semanticCCO_change_universe S cco) D)
      (factorH S H (semanticCCO_change_universe S cco) D)
      (coarseCut S H (semanticCCO_change_universe S cco) normalized D)
  intro b
  obtain ⟨a, ha⟩ := nonemptyA
  let x : factorSeed S H cco A0 D := ⟨Quotient.mk'' a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  let old : coarseOwners S H cco normalized A0 B D :=
    ⟨Quotient.mk'' x.val, seed_over_coarse S H cco normalized A0 B D x⟩
  let E := coarseOwnerEquiv S H cco normalized A0 B D
  let e := coarseEquiv S H (semanticCCO_change_universe S cco) normalized D
  let action := fullActionEquivalenceOf
    (ι := (Subtype.val : (coarseOwners S H cco normalized A0 B D) → _))
    (κ := (Subtype.val : factorOwners S H cco normalized B D → _)) e
    (coarseEquiv_equivariant S H (semanticCCO_change_universe S cco) normalized D) E (fun _ => rfl)
  obtain ⟨g, move⟩ := master_image_transitive S H cco (jointKernel S H cco normalized)
    (factorOwner S H cco normalized D) (jointKernel_le_owner S H cco normalized D) B (E old) (E b)
  let γ := action.group.symm g
  refine ⟨γ, x, ?_⟩
  change γ • old = b
  apply action.point.injective
  rw [action.equivariant]
  change action.group (action.group.symm g) • E old = E b
  exact (congrArg (fun k => k • E old) (action.group.apply_symm_apply g)).trans move

/-- M2 closes the displayed coarse set under the ACTUAL owner packet
of the actual factor source; palette names are transported, not assumed
identical. -/
theorem coarse_closed :
    letI := originalQuotientAction (factorSource S H (semanticCCO_change_universe S cco) D)
      (factorH S H (semanticCCO_change_universe S cco) D)
      (coarseCut S H (semanticCCO_change_universe S cco) normalized D)
    ∀ b ∈ coarseOwners S H cco normalized A0 B D, ∀ c,
      ownerPacket (factorSource S H (semanticCCO_change_universe S cco) D)
        (factorH S H (semanticCCO_change_universe S cco) D)
        (coarseOwner (factorSource S H (semanticCCO_change_universe S cco) D)
          (factorH S H (semanticCCO_change_universe S cco) D)
          (coarseCut S H (semanticCCO_change_universe S cco) normalized D))
        Quotient.mk''_surjective (fun _ _ => rfl) b c →
      c ∈ coarseOwners S H cco normalized A0 B D := by
  letI : MulAction G (Quotient (coarseCut S H (semanticCCO_change_universe S cco) normalized D).val) :=
    originalQuotientAction (factorSource S H (semanticCCO_change_universe S cco) D)
      (factorH S H (semanticCCO_change_universe S cco) D)
      (coarseCut S H (semanticCCO_change_universe S cco) normalized D)
  intro b hb c hbc
  let T := factorSource S H (semanticCCO_change_universe S cco) D
  let HT := factorH S H (semanticCCO_change_universe S cco) D
  let CQ : SemanticCCO.{0,v,v,v} T := semanticCCO_change_universe T
    (factorCCO S H (semanticCCO_change_universe S cco) D)
  let E : ExactEq T HT CQ () :=
    ⟨(coarseCut S H (semanticCCO_change_universe S cco) normalized D).val,
      coarseCut_exact S H (semanticCCO_change_universe S cco) normalized D⟩
  let U := quotientSource T HT CQ E
  let HU := quotientSource_homogeneous T HT CQ E
  let V := quotientSource S H cco (factorOwner S H cco normalized D)
  let HV := quotientSource_homogeneous S H cco (factorOwner S H cco normalized D)
  let e := coarseEquiv S H (semanticCCO_change_universe S cco) normalized D
  have hp : finitePacket U HU b c :=
    (owner_packet_iff T HT U HU (Quotient.mk'' : Quotient (factorCore S H cco D).val → _)
      Quotient.mk''_surjective (fun _ _ => rfl) b c).mp hbc
  have hp' : finitePacket V HV (e b) (e c) :=
    (packet_equiv U HU V HV e
      (coarseEquiv_equivariant S H (semanticCCO_change_universe S cco) normalized D) b c).mp hp
  have hb' : e b ∈ factorOwners S H cco normalized B D :=
    (coarseOwnerEquiv S H cco normalized A0 B D ⟨b, hb⟩).property
  have hc := master_image_closed S H cco (jointKernel S H cco normalized)
    (factorOwner S H cco normalized D) (jointKernel_le_owner S H cco normalized D) B
    (e b) hb' (e c) hp'
  exact (coarseOwnerSet_finite S H cco normalized A0 B D).mem_toFinset.mpr
    ⟨e c, hc, e.symm_apply_apply c⟩

/-- The sole ordinary-EPPA recursion is in the literal original
nonidentity kernel D join hat_D. -/
theorem factor_fine_eppa (lower : Lower S G H cco) :
    letI := originalQuotientAction (factorSource S H (semanticCCO_change_universe S cco) D)
      (factorH S H (semanticCCO_change_universe S cco) D)
      (factorDirection S H (semanticCCO_change_universe S cco) normalized D).val
    OrdinaryEPPA G (Quotient (factorDirection S H (semanticCCO_change_universe S cco) normalized D).val.val) := by
  letI : MulAction G (Quotient (Fine S H (semanticCCO_change_universe S cco) D).val) :=
    @CanonicalQuotients.quotientMulAction _ G _ _ _ (factorPremisesFineInvariant S H cco D)
  letI : MulAction G (Quotient (fineCut S H (semanticCCO_change_universe S cco) D).val) :=
    originalQuotientAction (factorSource S H (semanticCCO_change_universe S cco) D)
      (factorH S H (semanticCCO_change_universe S cco) D)
      (fineCut S H (semanticCCO_change_universe S cco) D)
  let F : ExactEq S H cco () := Fine S H (semanticCCO_change_universe S cco) D
  have ep := (lower F (fine_ne_bot S H (semanticCCO_change_universe S cco) D)).2.1
  change OrdinaryEPPA G (Quotient (fineCut S H (semanticCCO_change_universe S cco) D).val)
  exact ordinaryEPPA_equiv (G := G) (fineEquiv S H (semanticCCO_change_universe S cco) D).symm
    (equivariant_symm (G := G) _ (fineEquiv_equivariant S H (semanticCCO_change_universe S cco) D)) ep

/-- Actual C18: every local selector, owner language, safe padding,
reservoir, decoder and image-group field is CONSTRUCTED by B028. -/
theorem factor_witness (lower : Lower S G H cco)
    (safe : Set (S.Atom () ()))
    (hs : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe))
    (nonemptyA : A0.Nonempty) :
    Nonempty (OriginalWitness
      (factorSource S H (semanticCCO_change_universe S cco) D)
      (factorH S H (semanticCCO_change_universe S cco) D)
      (coarseCut S H (semanticCCO_change_universe S cco) normalized D)
      (factorSeed S H cco A0 D) (coarseOwners S H cco normalized A0 B D)
      (seed_over_coarse S H cco normalized A0 B D) (factorPalette S H cco safe D)) := by
  classical
  letI := factor_infinite S H (semanticCCO_change_universe S cco) normalized D
  have seedNonempty : (factorSeed S H cco A0 D).Nonempty := by
    obtain ⟨a, ha⟩ := nonemptyA
    exact ⟨Quotient.mk'' a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  apply normalized_relative_mi
    (factorSource S H (semanticCCO_change_universe S cco) D)
    (factorH S H (semanticCCO_change_universe S cco) D)
    (coarseCut S H (semanticCCO_change_universe S cco) normalized D)
    (factorCCO S H (semanticCCO_change_universe S cco) D)
    (factor_normalized S H (semanticCCO_change_universe S cco) normalized D)
    (factorDirection S H (semanticCCO_change_universe S cco) normalized D)
    (factorDirection_unique S H (semanticCCO_change_universe S cco) normalized D)
    (coarseCut_exact S H (semanticCCO_change_universe S cco) normalized D)
    (factorDirection_le_coarse S H (semanticCCO_change_universe S cco) normalized D)
    (factor_fine_eppa S H cco normalized D lower)
    (factorPalette S H cco safe D)
    (canonical_factor_safety S H (semanticCCO_change_universe S cco) normalized D safe
      (finset_strong_closed S H safe hs))
    (factorSeed S H cco A0 D) seedNonempty (coarseOwners S H cco normalized A0 B D)
    (seed_over_coarse S H cco normalized A0 B D)
    (coarse_eppa S H cco normalized A0 B D)
    (coarse_orbit S H cco normalized A0 B D nonemptyA)
    (coarse_closed S H cco normalized A0 B D)

end
end CCO.RankInduction.Factors
