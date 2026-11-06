import CCO.ExactEPGeometry.OriginalRetainedActualSelectedPhase
import CCO.ExactEPGeometry.OriginalSelectedCompleteAtomicMask
import CCO.APCharacter.MaskReadout

/-!
# B062 C96/C103: true SourcePhase masks equal the corrected complete masks

The actual retained selected SourcePhase is now compared with the exact
whole-Hom orbital masks used by the C96 finite-age theorem. All its actual
Reached objects and full arrows occur, and its character has exactly the
proved corrected values. Active bits are unrestricted; every inactive actual
selected sort has precisely the original prescribed zero bit.
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

/-- The actual SourcePhase inactive/active labels are determined by
the real original Reached set on EVERY old named parent. -/
theorem originalRetainedActualSelectedPhase_validBit_iff (j : B.Sorts) (ε : Bit) :
    (originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE).validBit
      (Quotient.mk'' j : OriginalOccupancy A B P (P.parent r)
        (fun i => hOne (P.parent r) i) E) ε ↔
    (¬Nonempty (Bridge B.source Kroot j) → ε = 0) := by
  have h := originalRetainedSelectedReached_iff A B P transport tp hOne Kroot E hE j
  dsimp only [SourcePhase.validBit]
  constructor
  · intro hb hn
    exact hb (fun hh => hn (h.mp hh))
  · intro hb hn
    exact hb (fun hh => hn (h.mpr hh))

/-- On ALL actual complete quotient atom colours, including logical
identity, the true selected SourcePhase mask is exactly the full corrected
occupancy character mask already used in BOTH C96 finite-age directions. -/
theorem originalRetainedActualSelectedPhase_masks_iff :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
    let K := fun c => originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (anchor c)
    letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
    let χOcc := originalRetainedSelectedOccupancyCharacter A B P transport tp hOne Kroot phase E hE
    let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
    ∀ (c d : OriginalReachedOccupancy A B P base hBase E Kroot)
      (a : Option (Q.source.Atom (Quotient.mk'' (anchor c).val)
        (Quotient.mk'' (anchor d).val))) (ε η : Bit),
      φ.allows a ε η ↔ originalSelectedCompleteAtomicMask Q (K c) (K d)
        (fun (R : c ⟶ d) => χOcc.value R) a ε η := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
  let K := fun c => originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (anchor c)
  letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
  letI := Reached.groupoid Q.homogeneous CQ (A := KQ)
  let F := originalRetainedSelectedReachedFunctor A B P transport tp hOne Kroot E hE
  let FF := originalRetainedSelectedReachedFullyFaithful A B P transport tp hOne Kroot E hE
  let χOcc := originalRetainedSelectedOccupancyCharacter A B P transport tp hOne Kroot phase E hE
  let χ := originalRetainedActualSelectedCharacter A B P transport tp hOne Kroot phase E hE
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let hk := originalRetainedSelectedReached_kernel A B P transport tp hOne Kroot E hE
  dsimp only
  intro c d a ε η
  have hRel (R : c ⟶ d) : (F.map R).rel = R.rel :=
    kernelArrowEquiv_rel (hk c).symm (hk d).symm R
  have hVal (R : c ⟶ d) : χ.value (F.map R) = χOcc.value R :=
    originalRetainedActualSelectedCharacter_value A B P transport tp hOne Kroot phase E hE R
  constructor
  · intro h x y hc R hR
    have ht : (F.map R).rel x y :=
      (Iff.of_eq (congrFun (congrFun (hRel R) x) y)).mpr hR
    have hh := h.2.2 x y hc (F.obj c).property (F.obj d).property (F.map R) ht
    change η = ε + χ.value (F.map R) at hh
    exact hh.trans (congrArg (fun z => ε + z) (hVal R))
  · intro h
    refine ⟨(fun hn => False.elim (hn (F.obj c).property)),
      (fun hn => False.elim (hn (F.obj d).property)),?_⟩
    intro x y hc hi hj T hT
    let R : c ⟶ d := FF.preimage T
    have hMap : F.map R = T := FF.map_preimage T
    have hR : R.rel x y := by rw [← hRel,hMap]; exact hT
    have hh : η = ε + χOcc.value R := h x y hc R hR
    have hv : χ.value T = χOcc.value R := by
      have v := hVal R
      rw [hMap] at v
      exact v
    change η = ε + χ.value T
    rw [hv]
    exact hh

end
end CCO.ExactEPGeometry
