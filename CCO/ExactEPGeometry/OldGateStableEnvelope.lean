import CCO.ExactEPGeometry.PrefixExactLargestLift
import CCO.ExactEPGeometry.PrefixExactEquivalenceLift
import CCO.ExactEPGeometry.OriginalBridgeSaturation

/-!
# B062 C51–C54: ORIGINAL exact-domain enclosure by the largest old gate

Suppose an original REAL equality-inclusive RAW exact relation D
contains the old identity and its trace on one current named sort is
EXACTLY a genuine current full-exact equivalence F. Then D lies below
the canonical greatest ORIGINAL exact lift L_p(F).

This is a genuine source application, not an order-theoretic postulate.
The proof stabilizes ACTUAL old RAW positive powers of D, uses the
accepted ORIGINAL homogeneous CCO convolution/finiteness to form an
old full-RAW-exact equivalence, proves by fixed-middle-sort (TP) that
every old power has the SAME actual current F trace, and invokes the
previously proved E1/E2/E3 largest-fiber adjunction. Thus the old
envelope containing D really belongs to the exact fiber of F.

C51's old D^2 is treated by applying this theorem to the REAL old
exact square; its current trace must come from the selected current
full bridge and (TP), not an assumed abstract quotient relation.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- A REAL old nonempty RAW exact D, with genuine original diagonal,
lies below the canonical largest ORIGINAL exact preimage of its
current equivalence trace. Each positive power's unchanged trace is
proved from actual typed TP, while the original stabilizing power
is an actual exact old EQUIVALENCE. -/
theorem original_reflexive_exact_below_largest
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts) (F : ExactEq B.source p)
    (D : RawExact.NonemptyExact A.source (P.parent p) (P.parent p))
    (hRef : ∀ a : A.Point (P.parent p),
      RawExact.evaluate A.source D.words a a)
    (hTrace : ∀ x y : B.Point p,
      F x y ↔ RawExact.evaluate A.source D.words
        (P.point p x) (P.point p y)) :
    ∀ x y : A.Point (P.parent p),
      RawExact.evaluate A.source D.words x y →
        PrefixExactLargestLift.largest A B P transport tp p F x y := by
  let R := RawExact.evaluate A.source D.words
  let C := exactCalculus_of_homogeneous_CCO
    A.source A.homogeneous A.cco
  have hExact : FullExact A.source R := ⟨D,rfl⟩
  obtain ⟨n,hStable⟩ :=
    originalPower_stabilizes A.source A.homogeneous C
      R hExact hRef
  have hPowerFull : FullExact A.source (originalPower R n) :=
    originalPower_exact A.source C R hExact n
  have hPowerEquiv : RawSymmetric.EquivRel (originalPower R n) :=
    originalPower_equiv_of_stable A.source A.homogeneous C
      R hExact hRef n hStable
  let oldSetoid : Setoid (A.Point (P.parent p)) :=
    { r := originalPower R n
      iseqv := {
        refl := hPowerEquiv.refl
        symm := by intro x y h; exact hPowerEquiv.symm x y h
        trans := by intro x y z h k; exact hPowerEquiv.trans x y z h k
      } }
  have hPowerInv : TRel.Invariant (G := A.G)
      (originalPower R n) :=
    hPowerFull.invariant A.source A.homogeneous
  let E : ExactEq A.source (P.parent p) :=
    ⟨⟨oldSetoid, groupInvariant_colourInvariant
      A.source A.homogeneous hPowerInv⟩,hPowerFull⟩
  have hCurrent : RawSymmetric.EquivRel
      (fun x y : B.Point p => F x y) :=
    ⟨F.val.val.refl,
      fun x y h => F.val.val.symm h,
      fun x y z h k => F.val.val.trans h k⟩
  have hETrace :
      PrefixExactRestriction.rho A B P transport p E = F := by
    apply ExactEq.ext
    intro x y
    calc
      (PrefixExactRestriction.rho A B P transport p E) x y ↔
          E (P.point p x) (P.point p y) :=
        PrefixExactRestriction.rho_iff A B P transport p E x y
      _ ↔ originalPower R n (P.point p x) (P.point p y) := Iff.rfl
      _ ↔ F x y := PrefixExactEquivalenceLift.original_power_trace
        A B P tp D (fun x y => F x y) hCurrent hTrace n x y
  have hBelow : E ≤ PrefixExactLargestLift.largest
      A B P transport tp p F :=
    PrefixExactLargestLift.largest_dominates
      A B P transport tp p F E hETrace
  change E.val ≤ (PrefixExactLargestLift.largest A B P transport tp p F).val
    at hBelow
  intro x y hxy
  apply hBelow
  change originalPower R n x y
  exact originalPower_mono R hRef (Nat.zero_le n) x y hxy

end
end CCO.ExactEPGeometry
