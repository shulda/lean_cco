import CCO.RankInduction.FactorGeometry
import CCO.MIGeometry.SourceAssembly
import CCO.MIGeometry.SurvivingDirections
import CCO.Owners.Master.NestedQuotients

/-! Concrete normalized factor sources and their actual fine/coarse cuts.
Both iterated quotient carriers are identified equivariantly with the
literal original quotients. No full-automorphism surjectivity is asserted. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT ParityHasse.Original AclOwners MIGeometry
open FinitePackets.Normalization RealClosure.Bounds

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

def factorSource (D : Direction S) : AtomicSource.{0,v,v} Unit
    (fun _ => Quotient (Core S H cco D).val) :=
  actualQuotientSource S H (hat S H cco D)

local instance factorSourcesAction (D : Direction S) :
    MulAction G (Quotient (Core S H cco D).val) :=
  originalQuotientAction S H (hat S H cco D)

theorem factorH (D : Direction S) : HomogeneousSource (factorSource S H cco D) G :=
  (hatQuotient_source S H cco D).1

theorem factorCCO (D : Direction S) : SemanticCCO.{0,v,0,v} (factorSource S H cco D) :=
  (hatQuotient_source S H cco D).2

theorem factor_normalized (normalized : NoFiniteExactKernel S) (D : Direction S) :
    NoFiniteExactKernel (factorSource S H cco D) :=
  hatQuotient_normalized S H cco normalized D

theorem factor_infinite (normalized : NoFiniteExactKernel S) (D : Direction S) :
    Infinite (Quotient (Core S H cco D).val) :=
  hatQuotient_infinite S H cco normalized D

theorem factor_directionCount (normalized : NoFiniteExactKernel S) (D : Direction S) :
    directionCount (factorSource S H cco D) = 1 :=
  hat_quotient_directionCount S H cco normalized D

/-- The coarse cut is the actual original owner equivalence modulo the
factor kernel, with its full inherited original orbital language. -/
def coarseCut (normalized : NoFiniteExactKernel S) (D : Direction S) :
    ColourEq (factorSource S H cco D) () :=
  quotientColourEq S H (hat S H cco D) (exactColour S H cco (Owner S H cco normalized D))
    (core_le_owner S H cco normalized D)

theorem coarseCut_exact (normalized : NoFiniteExactKernel S) (D : Direction S) :
    IsExactEq (factorSource S H cco D) (i := ()) (coarseCut S H cco normalized D).val :=
  quotientColourEq_exact S H cco (hat S H cco D) (hatPresentation S H cco D)
    (hatPresentation_represents S H cco D) _ (core_le_owner S H cco normalized D)
    (Owner S H cco normalized D).property

/-- The unique surviving direction is explicitly (D join hat)/hat. -/
def fineCut (D : Direction S) : ColourEq (factorSource S H cco D) () :=
  quotientColourEq S H (hat S H cco D) (ColourEq.join S H D.val (hat S H cco D))
    (by let := ColourEq.lattice S H (i := ()); exact le_sup_right)

theorem fineCut_isDirection (normalized : NoFiniteExactKernel S) (D : Direction S) :
    IsDirection (factorSource S H cco D) (fineCut S H cco D) := by
  have h := survivingEq_isDirection S H cco normalized {D} D (Set.mem_singleton D)
  let P : ColourEq S () → Prop := fun K =>
    IsDirection (actualQuotientSource S H K)
      (quotientColourEq S H K (ColourEq.join S H D.val K)
        (by let := ColourEq.lattice S H (i := ()); exact le_sup_right))
  have hP : P (selectedHat S H cco {D}) := h
  exact Eq.mp (congrArg P (selectedHat_singleton S H cco D)) hP

def factorDirection (normalized : NoFiniteExactKernel S) (D : Direction S) :
    Direction (factorSource S H cco D) :=
  ⟨fineCut S H cco D, fineCut_isDirection S H cco normalized D⟩

theorem factorDirection_unique (normalized : NoFiniteExactKernel S) (D : Direction S)
    (E : Direction (factorSource S H cco D)) : E = factorDirection S H cco normalized D := by
  classical
  let : Fintype (Direction (factorSource S H cco D)) := Fintype.ofFinite _
  have hc : Fintype.card (Direction (factorSource S H cco D)) = 1 := by
    simpa only [directionCount, Nat.card_eq_fintype_card] using factor_directionCount S H cco normalized D
  have hs : Subsingleton (Direction (factorSource S H cco D)) :=
    Fintype.card_le_one_iff_subsingleton.mp hc.le
  exact hs.elim _ _

theorem fineCut_exact (D : Direction S) :
    IsExactEq (factorSource S H cco D) (i := ()) (fineCut S H cco D).val := by
  apply quotientColourEq_exact S H cco (hat S H cco D) (hatPresentation S H cco D)
    (hatPresentation_represents S H cco D)
  exact isExactEq_sup S H (semanticCCO_change_universe S cco)
    (direction_exact S H cco D) (hat_exact S H cco D)

theorem factorDirection_le_coarse (normalized : NoFiniteExactKernel S) (D : Direction S) :
    (factorDirection S H cco normalized D).val ≤ coarseCut S H cco normalized D := by
  let := ColourEq.lattice S H (i := ())
  have hjoin : ColourEq.join S H D.val (hat S H cco D) ≤
      exactColour S H cco (Owner S H cco normalized D) :=
    sup_le (direction_le_owner S H cco normalized D) (core_le_owner S H cco normalized D)
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      exact (quotientColourEq_projection S H (hat S H cco D) _ _ x y).mpr
        (hjoin ((quotientColourEq_projection S H (hat S H cco D) _ _ x y).mp hqr))

/-- The fine recursion kernel is literally original D join hat, rather
than a nonidentity cut chosen independently of the source direction. -/
theorem fine_pullback (D : Direction S) :
    (quotientPullback S H (hat S H cco D) (fineCut S H cco D)).val =
      (Fine S H cco D).val := by
  exact congrArg Subtype.val (quotientPullback_quotientColourEq S H (hat S H cco D)
    (ColourEq.join S H D.val (hat S H cco D)) _)

def coarseProjection (normalized : NoFiniteExactKernel S) (D : Direction S) :
    Quotient (Core S H cco D).val → Quotient (Owner S H cco normalized D).val :=
  Abstract.quotientMap (core_le_owner S H cco normalized D)

theorem coarseCut_kernel (normalized : NoFiniteExactKernel S) (D : Direction S) :
    (coarseCut S H cco normalized D).val = Setoid.ker (coarseProjection S H cco normalized D) := by
  apply Setoid.ext
  intro q r
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      exact (quotientColourEq_projection S H (hat S H cco D) _ _ x y).trans Quotient.eq.symm

def coarseEquiv (normalized : NoFiniteExactKernel S) (D : Direction S) :
    Quotient (coarseCut S H cco normalized D).val ≃ Quotient (Owner S H cco normalized D).val :=
  (Quotient.congrRight (Setoid.ext_iff.mp (coarseCut_kernel S H cco normalized D))).trans
    (Setoid.quotientKerEquivOfSurjective (coarseProjection S H cco normalized D)
      (Abstract.quotientMap_surjective (core_le_owner S H cco normalized D)))

@[simp] theorem coarseEquiv_projection (normalized : NoFiniteExactKernel S) (D : Direction S)
    (q : Quotient (Core S H cco D).val) :
    coarseEquiv S H cco normalized D (Quotient.mk'' q) = coarseProjection S H cco normalized D q := rfl

local instance factorSourcesCoarseInvariant (normalized : NoFiniteExactKernel S) (D : Direction S) :
    CanonicalQuotients.Invariant G (coarseCut S H cco normalized D).val :=
  ⟨colourInvariant_groupInvariant (factorSource S H cco D) (factorH S H cco D)
    (coarseCut S H cco normalized D).property⟩

local instance factorSourcesOriginalCoarseInvariant (normalized : NoFiniteExactKernel S) (D : Direction S) :
    CanonicalQuotients.Invariant G (Owner S H cco normalized D).val :=
  Owners.Product.exactInvariant S H (semanticCCO_change_universe S cco) (Owner S H cco normalized D)

theorem coarseEquiv_equivariant (normalized : NoFiniteExactKernel S) (D : Direction S)
    (g : G) (q : Quotient (coarseCut S H cco normalized D).val) :
    coarseEquiv S H cco normalized D (g • q) = g • coarseEquiv S H cco normalized D q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    induction x using Quotient.inductionOn with
    | _ a => rfl

theorem core_le_fine (D : Direction S) : Core S H cco D ≤ Fine S H cco D := le_sup_right

def fineProjection (D : Direction S) :
    Quotient (Core S H cco D).val → Quotient (Fine S H cco D).val :=
  Abstract.quotientMap (core_le_fine S H cco D)

theorem fineCut_kernel (D : Direction S) :
    (fineCut S H cco D).val = Setoid.ker (fineProjection S H cco D) := by
  apply Setoid.ext
  intro q r
  induction q using Quotient.inductionOn with
  | _ x =>
    induction r using Quotient.inductionOn with
    | _ y =>
      exact (quotientColourEq_projection S H (hat S H cco D) _ _ x y).trans Quotient.eq.symm

def fineEquiv (D : Direction S) :
    Quotient (fineCut S H cco D).val ≃ Quotient (Fine S H cco D).val :=
  (Quotient.congrRight (Setoid.ext_iff.mp (fineCut_kernel S H cco D))).trans
    (Setoid.quotientKerEquivOfSurjective (fineProjection S H cco D)
      (Abstract.quotientMap_surjective (core_le_fine S H cco D)))

@[simp] theorem fineEquiv_projection (D : Direction S) (q : Quotient (Core S H cco D).val) :
    fineEquiv S H cco D (Quotient.mk'' q) = fineProjection S H cco D q := rfl

local instance factorSourcesFineInvariant (D : Direction S) :
    CanonicalQuotients.Invariant G (fineCut S H cco D).val :=
  ⟨colourInvariant_groupInvariant (factorSource S H cco D) (factorH S H cco D)
    (fineCut S H cco D).property⟩

local instance factorSourcesOriginalFineInvariant (D : Direction S) :
    CanonicalQuotients.Invariant G (Fine S H cco D).val :=
  Owners.Product.exactInvariant S H (semanticCCO_change_universe S cco) (Fine S H cco D)

theorem fineEquiv_equivariant (D : Direction S) (g : G) (q : Quotient (fineCut S H cco D).val) :
    fineEquiv S H cco D (g • q) = g • fineEquiv S H cco D q := by
  induction q using Quotient.inductionOn with
  | _ x =>
    induction x using Quotient.inductionOn with
    | _ a => rfl

end
end CCO.RankInduction.Factors
