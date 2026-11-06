import CCO.ExactEPGeometry.OriginalRetainedActualSelectedCharacter
import CCO.ExactEPGeometry.OriginalRetainedSelectedArrowDominance

/-!
# B062 C103: genuine retained selected-source SourcePhase

The corrected character is on the ENTIRE actual Reached groupoid. The
genuine old SourcePhase odd loop at an actual reached occupancy anchor
projects to a whole selected loop. Its dominance against ALL selected
full RAW equivalences is proved by actual pullback, and its character is
ONE. Transport to the actual selected root gives the true SourcePhase.

No quotient source/phase/dominance provider is a new hypothesis. The next
safe-source consumer still has to identify this phase's actual marked
successor with the next original-E selected quotient using both C96 ages.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.Towers RigidGroupoid.Geometry
open RigidGroupoid.Phase CategoryTheory
noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
variable (E : ExactEq A.source (P.parent r))
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- The ACTUAL retained selected quotient carries the original corrected
full character and a genuine nonidentity dominant distinguished odd arrow.
Every SourcePhase field is constructed from the actual original source. -/
def originalRetainedActualSelectedPhase :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
    SourcePhase Q.source Q.homogeneous CQ KQ := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let CB := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  letI := Reached.groupoid B.homogeneous CB (A := Kroot)
  letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
  letI := Reached.groupoid Q.homogeneous CQ (A := KQ)
  let F := originalRetainedSelectedReachedFunctor A B P transport tp hOne Kroot E hE
  let χ : Abstract.Character (Reached Q.source KQ) :=
    originalRetainedActualSelectedCharacter A B P transport tp hOne Kroot phase E hE
  let χOcc := originalRetainedSelectedOccupancyCharacter A B P transport tp hOne Kroot phase E hE
  let c : Occ := Quotient.mk'' (Reached.root Kroot)
  let a := originalReachedOccupancyAnchor A B P base hBase E Kroot c
  let eaa := originalRetainedSelectedArrowEquiv A B P transport tp hOne Kroot E hE a a
  let tOcc : c ⟶ c := eaa (phase.atSort a)
  let b := F.obj c
  let t : b ⟶ b := F.map tOcc
  have hOcc : χOcc.value tOcc = (1 : Abstract.Bit) := by
    change phase.character.value (eaa.symm (eaa (phase.atSort a))) = 1
    rw [eaa.symm_apply_apply]
    exact phase.atSort_detects a
  have ht : χ.value t = (1 : Abstract.Bit) :=
    (originalRetainedActualSelectedCharacter_value
      A B P transport tp hOne Kroot phase E hE tOcc).trans hOcc
  have htne : t ≠ Arrow.id (Reached.kernel Q.homogeneous CQ b) := by
    intro h
    have hh : χ.value t = 0 := h ▸ χ.map_id b
    exact zero_ne_one (hh.symm.trans ht)
  have hd : Dominant (Reached.kernel Q.homogeneous CQ b) t := by
    let hk := originalRetainedSelectedReached_kernel A B P transport tp hOne Kroot E hE c
    exact kernelArrowEquiv_dominant hk.symm tOcc
      (originalRetainedSelectedArrow_dominant A B P transport tp hOne Kroot E hE
        a (phase.atSort a) (phase.atSort_dominant a))
  let root := Reached.root KQ
  let R : b ⟶ root := Reached.connectingArrow Q.homogeneous CQ b root
  let odd := RigidGroupoid.Geometry.transport CQ t R
  have hDetect : χ.value odd = 1 := by
    have h := Abstract.transported_character (o := b) (a := root) χ t ht R
    dsimp only [Abstract.transported] at h
    rw [← Groupoid.inv_eq_inv R] at h
    change χ.value (R.inv.comp CQ (t.comp CQ R)) = 1 at h
    exact h
  exact {
    odd := odd
    odd_nonidentity := transport_nonidentity CQ htne R
    odd_dominant := transport_dominant CQ t hd R
    character := χ
    detects := hDetect
  }

/-- The actual SourcePhase uses EXACTLY the corrected all-Hom character
already related to old normalized source arrows, without a new choice. -/
theorem originalRetainedActualSelectedPhase_character :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
    (originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE).character =
      originalRetainedActualSelectedCharacter A B P transport tp hOne Kroot phase E hE := rfl

end
end CCO.ExactEPGeometry
