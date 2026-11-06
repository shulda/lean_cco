import CCO.ExactEPGeometry.QuotientSaturatedWalkPowers
import CCO.ExactEPGeometry.OriginalOneSortExactDescent

/-!
# B062 C98: ACTUAL quotient atom walk powers are E-saturated old powers

The real one-original-sort exact E induces a true equivariant same-sort
kernel e on EVERY current parent of the genuine existing all-parent
AP+HOM-CCO quotient. Both e and each actual current atomic orbital R are
invariant under the SAME current homogeneous group. The accepted symmetric
pair-flip calculus proves R;e=e;R, rather than taking it as an additional
mathematical premise.

For ANY genuinely realized current pair orbital (including old logical
equality), every n-step walk of its actual quotient pair orbital pulls
back to exactly e;(R^n);e, with n=0 yielding the entire e-kernel.
All intermediate quotient classes and actual old source points are used.
No quotient SAP, section of automorphism groups or mixed reverse exact
descent. The subsequent C99 parity/index-two and C101 maximality still
require their own source-proved pivot and gate instances.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- The full SOURCE C98 same-parent relation equality, before finite
parity stabilization: old E-saturated powers are precisely the full
pullbacks of all actual quotient orbital powers, including zero.

The commutation of E and the old atom is PROVED from the current source
invariant same-sort pair-flip calculus, not added as a hypothesis. -/
theorem originalExactAllCurrentOrbitalRelPow_bisaturated_pullback
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i : B.Sorts} (x y : B.Point i) (n : Nat) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    let e := originalExactCurrentKernelFamily
      A B P transport base hOne E i
    let pi : B.Point i → Q.Point i := fun z => Quotient.mk'' z
    ∀ a b : B.Point i,
      relPow
        (Q.source.rawAtomRel (Q.source.colour (pi x) (pi y)))
        n (pi a) (pi b) ↔
        setoidBiSaturation e
          (relPow (B.source.rawAtomRel (B.source.colour x y)) n) a b := by
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hOne E
  let J := originalExactCurrentKernelFamily
    A B P transport base hOne E
  let W := originalExactCurrentKernelWords
    A B P transport base hOne E
  let e : Setoid (B.Point i) := J i
  let pi : B.Point i → Q.Point i := fun z => Quotient.mk'' z
  let R : B.Point i → B.Point i → Prop :=
    B.source.rawAtomRel (B.source.colour x y)
  let D : Q.Point i → Q.Point i → Prop :=
    Q.source.rawAtomRel (Q.source.colour (pi x) (pi y))
  have hRep : RawExact.evaluate B.source (W i).words = e.r :=
    originalExactCurrentKernelWords_relation
      A B P transport base hOne E i
  have hInvE : TRel.Invariant (G := B.G) e.r := by
    rw [←hRep]
    exact RawExact.presentation_invariant_of_homogeneous
      B.source B.homogeneous (W i).words
  have hInvR : TRel.Invariant (G := B.G) R :=
    B.source.rawAtomRel_invariant (B.source.colour x y)
      (B.source.colourInvariant_of_homogeneous B.homogeneous)
  have hComm : RawSymmetric.compose R e.r = RawSymmetric.compose e.r R :=
    RawSymmetric.invariant_commute R e.r hInvR hInvE
      (B.source.pair_flip_of_homogeneous B.homogeneous)
  have hKernel : ∀ a b, pi a = pi b ↔ e.r a b := by
    intro a b
    exact Quotient.eq
  have hBlock : GroupActions.pullback pi pi D =
      Quotient.block B.source W (B.source.colour x y) := by
    funext a b
    apply propext
    exact (originalExactAllCurrentPairBlock
      A B P transport base hOne E x a y b).symm
  have hSat : Quotient.block B.source W (B.source.colour x y) =
      setoidBiSaturation e R := by
    funext a b
    apply propext
    change (∃ mid, (∃ aa,
        RawExact.evaluate B.source (W i).words a aa ∧ R aa mid) ∧
        RawExact.evaluate B.source (W i).words mid b) ↔
      (∃ aa mid, e.r a aa ∧ R aa mid ∧ e.r mid b)
    rw [hRep]
    constructor
    · rintro ⟨mid,⟨aa,haa,hamid⟩,hmidb⟩
      exact ⟨aa,mid,haa,hamid,hmidb⟩
    · rintro ⟨aa,mid,haa,hamid,hmidb⟩
      exact ⟨mid,⟨aa,haa,hamid⟩,hmidb⟩
  have hPull : GroupActions.pullback pi pi D =
      setoidBiSaturation e R := hBlock.trans hSat
  have hSurj : Function.Surjective pi := Quotient.mk''_surjective
  have hPow := quotientRelPow_bisaturated_pullback pi hSurj
    e hKernel R hComm D hPull n
  change ∀ (a b : B.Point i),
    relPow D n (pi a) (pi b) ↔
      setoidBiSaturation e (relPow R n) a b
  intro a b
  exact Iff.of_eq (congrFun (congrFun hPow a) b)

end
end CCO.ExactEPGeometry
