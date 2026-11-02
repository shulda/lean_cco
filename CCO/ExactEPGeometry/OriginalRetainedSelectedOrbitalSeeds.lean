import CCO.ExactEPGeometry.OriginalSelectedCompleteAtomicMask

/-!
# B062 C88–C93: real selected E-quotient orbitals force all seed equations

The true selected Q is ALREADY constructed by the AP+HOM CCO typed
simultaneous-quotient provider, and the complete selected Hom groupoid,
full K/E gates, exact Arrow action and C84 source-corrected character
are proved from the original retained safe step. This module applies
the preceding real-orbital mask lemma to precisely those providers.

Every finite diagram considered here consists of ACTUAL points of
that selected quotient source, at actual reached E-occupancy anchors.
Its assumed pair legality is the explicit complete full-Arrow mask
on the quotient atomic colour. It is not a fictitious fine lift and
does not posit separate pairwise Arrow equations. The result derives
ALL of them and extends one compatible marking, including duplicate
K/E gate points. Identifying these masks with the full original
marked-age quotient and realizing arbitrary legal prefix diagrams
remain separate C88–C96 source obligations.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- C91 on ACTUAL selected quotient orbitals: the explicit complete
local mask at a real quotient pair is EQUIVALENT to all the genuine
full selected-groupoid Arrow-action equations on its K/E classes.
The character is the previously constructed C84 corrected character
and the projected kernels are PROVED actual full-exact gates. -/
theorem originalRetainedSelectedActualMask_iff_action
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    let Occ := OriginalReachedOccupancy A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E Kroot
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport (P.parent r) (fun i => hOne (P.parent r) i) E
    let anchor := originalReachedOccupancyAnchor
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
    let K := fun a : Occ => originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE (anchor a)
    let F := originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ (a b : Occ)
      (x : Q.Point (Quotient.mk'' (anchor a).val))
      (y : Q.Point (Quotient.mk'' (anchor b).val))
      (eps eta : ZMod 2),
      originalSelectedCompleteAtomicMask Q (K a) (K b)
        (fun (R : a ⟶ b) => chi.value R)
        (Q.source.colour x y) eps eta ↔
      ∀ (R : a ⟶ b),
        F.map R ((K a).project x) = (K b).project y →
          eta = eps + chi.value R := by
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun i => hOne (P.parent r) i) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport (P.parent r) (fun i => hOne (P.parent r) i) E
  let anchor := originalReachedOccupancyAnchor
    A B P (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
  let K := fun a : Occ => originalRetainedSelectedKernel
    A B P transport tp hOne Kroot E hE (anchor a)
  let F := originalRetainedSelectedPointFunctor
    A B P transport tp hOne Kroot E hE
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  change ∀ (a b : Occ)
      (x : Q.Point (Quotient.mk'' (anchor a).val))
      (y : Q.Point (Quotient.mk'' (anchor b).val))
      (eps eta : ZMod 2),
      originalSelectedCompleteAtomicMask Q (K a) (K b)
        (fun (R : a ⟶ b) => chi.value R)
        (Q.source.colour x y) eps eta ↔
      ∀ (R : a ⟶ b),
        F.map R ((K a).project x) = (K b).project y →
          eta = eps + chi.value R
  intro a b x y eps eta
  rw [originalSelectedCompleteAtomicMask_iff_at_pair
    Q (K a) (K b) (fun (R : a ⟶ b) => chi.value R)
    x y eps eta]
  constructor
  · intro h R hAction
    have hReal : R.rel x y :=
      (R.quotientMap_eq_iff Q.homogeneous x y).mp hAction
    exact h R hReal
  · intro h R hReal
    apply h R
    exact (R.quotientMap_eq_iff Q.homogeneous x y).mpr hReal

/-- From REAL pair-local atomic masks of ANY FINITE family of already
realized quotient-prefix points, derive the full C91 arrow equations,
descent of all repeated gate-point bits C92, and the C93 global
selected-character marking. No arbitrary quotient-prefix diagram is
assumed realized, and no unverified original marked-age lift occurs. -/
theorem originalRetainedSelectedFiniteOrbitalSeedExtension
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    let Occ := OriginalReachedOccupancy A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E Kroot
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport (P.parent r) (fun i => hOne (P.parent r) i) E
    let anchor := originalReachedOccupancyAnchor
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
    let K := fun a : Occ => originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE (anchor a)
    let F := originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ {V : Type z} [Finite V]
      (owners : V → Occ)
      (point : ∀ v : V,
        Q.Point (Quotient.mk'' (anchor (owners v)).val))
      (bits : V → ZMod 2),
      (∀ i j : V,
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour (point i) (point j))
          (bits i) (bits j)) →
      ∃ mark, Abstract.IsMarking F chi mark ∧
        ∀ v : V,
          mark (⟨owners v, (K (owners v)).project (point v)⟩ :
            Abstract.Point F) = bits v := by
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun i => hOne (P.parent r) i) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport (P.parent r) (fun i => hOne (P.parent r) i) E
  let anchor := originalReachedOccupancyAnchor
    A B P (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
  let K := fun a : Occ => originalRetainedSelectedKernel
    A B P transport tp hOne Kroot E hE (anchor a)
  let F := originalRetainedSelectedPointFunctor
    A B P transport tp hOne Kroot E hE
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  change ∀ {V : Type z} [Finite V]
      (owners : V → Occ)
      (point : ∀ v : V,
        Q.Point (Quotient.mk'' (anchor (owners v)).val))
      (bits : V → ZMod 2),
      (∀ i j : V,
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour (point i) (point j))
          (bits i) (bits j)) →
      ∃ mark, Abstract.IsMarking F chi mark ∧
        ∀ v : V,
          mark (⟨owners v, (K (owners v)).project (point v)⟩ :
            Abstract.Point F) = bits v
  intro V _ owners point bits hAllowed
  let points : V → Abstract.Point F :=
    fun v => ⟨owners v, (K (owners v)).project (point v)⟩
  have hLocal :
      ∀ (i j : V) (R : (points i).1 ⟶ (points j).1),
        F.map R (points i).2 = (points j).2 →
          bits j = bits i + chi.value R := by
    intro i j R hAction
    have hReal : R.rel (point i) (point j) :=
      (R.quotientMap_eq_iff Q.homogeneous (point i) (point j)).mp hAction
    exact (hAllowed i j) (point i) (point j) rfl R hReal
  obtain ⟨mark,hm,hvalues⟩ :=
    originalRetainedSelectedPresentedSeedExtension
      A B P transport tp hOne Kroot phase E hE points bits hLocal
  exact ⟨mark,hm,hvalues⟩

end
end CCO.ExactEPGeometry
