import CCO.ExactEPGeometry.OriginalRetainedSelectedReached
import CCO.ExactEPGeometry.OriginalReachedOccupancyAnchors

/-!
# B062 C103: actual selected Reached objects equal reached E-occupancies

The complete selected-source bridge reflection gives a genuine bijection
between its ACTUAL Reached object type and the already constructed full
old reached-occupancy groupoid objects. At each object the actual Reached
kernel is precisely the existing projected selected anchor kernel, by
uniqueness of the target of full source bridges. Thus the two full Hom
types use the same actual selected-source gates, not assumed new kernels.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Any whole arrow from the root identifies the ACTUAL reached target
kernel, regardless of the choice used by Reached.bridge. -/
theorem reachedKernel_eq_of_arrow
    {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
    {G : Type t} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) (C : ExactCalculus S)
    {i : ι} (K : Kernel S i) (b : Reached S K)
    (T : Kernel S b.val) (R : Arrow S K T) : Reached.kernel H C b = T := by
  have h := bridge_targetKernel_unique S H C (Reached.bridge b) R.toBridge
  apply h.trans
  apply kernel_ext S
  apply Setoid.ext
  intro x y
  exact Iff.of_eq (congrFun (congrFun R.target x) y)

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (E : ExactEq A.source (P.parent r))
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- Each true old reached occupancy yields a genuinely reached selected
object via its WHOLE projected root-to-anchor arrow. -/
def originalRetainedOccupancyToSelectedReached :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
    OriginalReachedOccupancy A B P base hBase E Kroot → Reached Q.source KQ := by
  dsimp only
  intro c
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let a := originalReachedOccupancyAnchor A B P base hBase E Kroot c
  let R := Reached.connectingArrow B.homogeneous C (Reached.root Kroot) a
  exact ⟨Quotient.mk'' a.val,⟨((originalRetainedSelectedArrowEquiv
    A B P transport tp hOne Kroot E hE (Reached.root Kroot) a) R).toBridge⟩⟩

/-- All and only the actually reached selected-source objects occur,
and their distinct occupancy names remain distinct. -/
def originalRetainedOccupancySelectedReachedEquiv :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
    OriginalReachedOccupancy A B P base hBase E Kroot ≃ Reached Q.source KQ := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  let f := originalRetainedOccupancyToSelectedReached A B P transport tp hOne Kroot E hE
  let Occ := OriginalOccupancy A B P base hBase E
  let ROcc := OriginalReachedOccupancy A B P base hBase E Kroot
  let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
  let forget : ROcc → Occ := Quotient.map (fun b : Reached B.source Kroot => b.val)
    (fun {_ _} h => h)
  have hName (c : ROcc) : (f c).val = forget c := by
    have h := congrArg forget (originalReachedOccupancyAnchor_class A B P base hBase E Kroot c)
    exact h
  apply Equiv.ofBijective f
  constructor
  · intro c d h
    have hNames : forget c = forget d := (hName c).symm.trans ((congrArg Subtype.val h).trans (hName d))
    induction c using Quotient.inductionOn with
    | _ b =>
      induction d using Quotient.inductionOn with
      | _ a =>
        change (Quotient.mk'' b.val : Occ) = Quotient.mk'' a.val at hNames
        have hRel : (originalExactOccupancySetoid A B P base hBase E).r
            b.val a.val := Quotient.exact hNames
        exact Quotient.sound hRel
  · intro b
    let i := originalOccupancyRepresentative A B P base hBase E b.val
    have hi : (Quotient.mk'' i : Occ) = b.val :=
      originalOccupancyRepresentative_class A B P base hBase E b.val
    have hNew : Nonempty (Bridge Q.source KQ (Quotient.mk'' i : Occ)) :=
      Eq.mpr (congrArg (fun c => Nonempty (Bridge Q.source KQ c)) hi) b.property
    have hOld := (originalRetainedSelectedReached_iff A B P transport tp hOne Kroot E hE i).mp hNew
    let a : Reached B.source Kroot := ⟨i,hOld⟩
    refine ⟨Quotient.mk'' a,?_⟩
    apply Subtype.ext
    exact (hName (Quotient.mk'' a)).trans hi

include tp hE in
/-- The actual selected Reached kernel at the corresponding object is
exactly the earlier genuine selected anchor gate. This supplies the full
Hom identification for the corrected SourcePhase character. -/
theorem originalRetainedSelectedReached_kernel
    (c : OriginalReachedOccupancy A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E Kroot) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
    let a := originalReachedOccupancyAnchor A B P base hBase E Kroot c
    Reached.kernel Q.homogeneous CQ
      (originalRetainedOccupancyToSelectedReached A B P transport tp hOne Kroot E hE c) =
      originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE a := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
  let a := originalReachedOccupancyAnchor A B P base hBase E Kroot c
  let R := Reached.connectingArrow B.homogeneous C (Reached.root Kroot) a
  exact reachedKernel_eq_of_arrow Q.source Q.homogeneous CQ _ _ _
    ((originalRetainedSelectedArrowEquiv A B P transport tp hOne Kroot E hE (Reached.root Kroot) a) R)

end
end CCO.ExactEPGeometry
