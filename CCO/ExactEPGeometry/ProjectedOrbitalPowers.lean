import CCO.ExactEPGeometry.OriginalOccupancyOrbitals
import CCO.ParityHasse.Original.ParitySeed
import CCO.ExactCRT.TypedPullback

/-!
# B062 C98: all positive powers of genuine quotient pair orbitals

For every actual same-sort old pair orbital (including original equality),
its complete E-saturated block is exactly the pullback of the corresponding
named quotient orbital in the ALREADY BUILT all-parent E-quotient. Every
positive length quotient walk then pulls back to the same-length walk in
that actual full block. This uses the surjective middle E-class projection,
not a section or quotient SAP.

Length ZERO is intentionally NOT replaced by old logical equality:
quotient equality pulls back to the entire old E-kernel, as C72 proved.
The further C98 cancellation of intermediate E-factors to
E;(c^n);E uses original same-sort invariant commutation and is separately
required. The special C97 odd orbital is obtained from the actual
SourcePhase pivot, not by assuming every nominal atom is realized.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- A surjective quotient projection preserves and reflects ALL positive
walk powers of ANY relation on its quotient. At zero, this statement
would be false when fibres have more than one point. -/
theorem quotientPullback_positiveRelPow
    {X Q : Type*} (pi : X → Q) (hsurj : Function.Surjective pi)
    (D : Q → Q → Prop) (n : Nat) :
    GroupActions.pullback pi pi (relPow D (n+1)) =
      relPow (GroupActions.pullback pi pi D) (n+1) := by
  induction n with
  | zero =>
      funext x y
      apply propext
      exact (relPow_one D (pi x) (pi y)).trans
        (relPow_one (GroupActions.pullback pi pi D) x y).symm
  | succ n ih =>
      calc
        GroupActions.pullback pi pi (relPow D ((n+1)+1)) =
            GroupActions.pullback pi pi
              (fun a c => ∃ b, D a b ∧ relPow D (n+1) b c) := rfl
        _ = (fun a c => ∃ b,
              GroupActions.pullback pi pi D a b ∧
                GroupActions.pullback pi pi (relPow D (n+1)) b c) :=
            ExactCRT.pullback_comp pi pi pi hsurj D (relPow D (n+1))
        _ = (fun a c => ∃ b,
              GroupActions.pullback pi pi D a b ∧
                relPow (GroupActions.pullback pi pi D) (n+1) b c) := by
            rw [ih]
        _ = relPow (GroupActions.pullback pi pi D) ((n+1)+1) := rfl

/-- C98 actual-source instantiation before parity stabilization:
for EVERY realized current pair orbital on one displayed parent, the
pullback of each genuine quotient orbital positive walk power equals the
power of the COMPLETE E-saturated old current orbital, with real middle
sort and all old equality. This is not merely an abstract quotient table. -/
theorem originalExactAllCurrentOrbitalPositivePowers_pullback
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i : B.Sorts} (x y : B.Point i) (n : Nat) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    let pi : B.Point i → Q.Point i := fun z => Quotient.mk'' z
    ∀ a b : B.Point i,
      relPow
        (Q.source.rawAtomRel
          (Q.source.colour (pi x) (pi y))) (n+1)
          (pi a) (pi b) ↔
        relPow
          (Quotient.block B.source
            (originalExactCurrentKernelWords A B P transport base hOne E)
            (B.source.colour x y)) (n+1) a b := by
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hOne E
  let pi : B.Point i → Q.Point i := fun z => Quotient.mk'' z
  let D : Q.Point i → Q.Point i → Prop :=
    Q.source.rawAtomRel (Q.source.colour (pi x) (pi y))
  let R : B.Point i → B.Point i → Prop :=
    Quotient.block B.source
      (originalExactCurrentKernelWords A B P transport base hOne E)
      (B.source.colour x y)
  have hPull : GroupActions.pullback pi pi D = R := by
    funext a b
    apply propext
    exact (originalExactAllCurrentPairBlock
      A B P transport base hOne E x a y b).symm
  have hSurj : Function.Surjective pi := Quotient.mk''_surjective
  have hPow := quotientPullback_positiveRelPow pi hSurj D n
  rw [hPull] at hPow
  intro a b
  exact Iff.of_eq (congrFun (congrFun hPow a) b)

end
end CCO.ExactEPGeometry
