import CCO.ExactEPGeometry.OriginalGateTargetTrace

/-!
# B062 C56: ONE canonical ORIGINAL exact gate across a real bridge

For a real current full RAW-exact Arrow R:p->q of a genuine AP-only
safe-prefix source, the original gate G_p has actual q² trace K_q.
The proved E1/E2/E3 largest-fiber adjunction implies that the typed
reindexing of G_p lies below the largest original lift G_q.

Applying the SAME statement to the genuine converse Arrow R.inv yields
the opposite inclusion. The original endpoints are identified ONLY by
the actual equality of their original parent sorts, not by identifying
the two distinct current unary types. The type-cast is a simple
equality transport in the EXACT original equivalence lattice, never
an arbitrary quotient exact-descent map.

No SAP, automorphism group section, generic old mixed commutation or
partial/selected generating arrow replacement.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

variable {ι : Type u} {X : ι → Type v}

/-- Genuine transport of ORIGINAL full-RAW-exact equivalences along
an ACTUAL original-sort equality. This does not transport any quotient
points or assert mixed exact reverse descent. -/
def oldExactEqCast (S : AtomicSource.{u,v,w} ι X)
    {i j : ι} (h : i = j) (F : ExactEq S j) : ExactEq S i := by
  cases h
  exact F

theorem oldExactEqCast_iff
    (S : AtomicSource.{u,v,w} ι X)
    {i j : ι} (h : i = j) (F : ExactEq S j)
    (x y : X i) :
    oldExactEqCast S h F x y ↔ F (h ▸ x) (h ▸ y) := by
  cases h
  exact Iff.rfl

theorem oldExactEqCast_mono
    (S : AtomicSource.{u,v,w} ι X)
    {i j : ι} (h : i = j) (E F : ExactEq S j)
    (hEF : E ≤ F) :
    oldExactEqCast S h E ≤ oldExactEqCast S h F := by
  cases h
  exact hEF

@[simp] theorem oldExactEqCast_cancel
    (S : AtomicSource.{u,v,w} ι X)
    {i j : ι} (h : i = j) (E : ExactEq S i) :
    oldExactEqCast S h (oldExactEqCast S h.symm E) = E := by
  cases h
  rfl

/-- The original canonical gate for the source of an ACTUAL full
current bridge maps into the greatest exact original gate for the
target. There is no assumed equality of original lifts: the
preimage condition is proved from real current C² trace and E1. -/
theorem original_gate_le_target
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    {p q : B.Sorts}
    (hSame : P.parent p = P.parent q)
    (Kp : Kernel B.source p) (Kq : Kernel B.source q)
    (R : Arrow B.source Kp Kq) :
    let Gp := PrefixExactLargestLift.largest A B P transport tp p
      (current_kernel_exact_eq B Kp)
    let Gq := PrefixExactLargestLift.largest A B P transport tp q
      (current_kernel_exact_eq B Kq)
    oldExactEqCast A.source hSame.symm Gp ≤ Gq := by
  dsimp only
  let Fp := current_kernel_exact_eq B Kp
  let Fq := current_kernel_exact_eq B Kq
  let Gp := PrefixExactLargestLift.largest A B P transport tp p Fp
  let Gq := PrefixExactLargestLift.largest A B P transport tp q Fq
  have hTarget := current_arrow_original_gate_target_trace
    A B P transport tp hSame Kp Kq R
  have hRho :
      PrefixExactRestriction.rho A B P transport q
        (oldExactEqCast A.source hSame.symm Gp) = Fq := by
    apply ExactEq.ext
    intro y z
    calc
      (PrefixExactRestriction.rho A B P transport q
        (oldExactEqCast A.source hSame.symm Gp)) y z ↔
          (oldExactEqCast A.source hSame.symm Gp)
            (P.point q y) (P.point q z) :=
        PrefixExactRestriction.rho_iff A B P transport q _ y z
      _ ↔ Gp (hSame.symm ▸ P.point q y)
            (hSame.symm ▸ P.point q z) :=
        oldExactEqCast_iff A.source hSame.symm Gp
          (P.point q y) (P.point q z)
      _ ↔ Fq y z := (hTarget y z).symm
  exact PrefixExactLargestLift.largest_dominates
    A B P transport tp q Fq
      (oldExactEqCast A.source hSame.symm Gp) hRho

/-- Source C56, with the ACTUAL groupoid Arrow, its REAL converse
and the genuine greatest original RAW-exact fiber adjunction.
Every full bridge between current types with the same original
parent identifies their canonical ORIGINAL maximal exact gates.
The transported equality is equality of FULL exact original
equivalences, not merely equality of binary supports. -/
theorem original_gates_equal_across_arrow
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    {p q : B.Sorts}
    (hSame : P.parent p = P.parent q)
    (Kp : Kernel B.source p) (Kq : Kernel B.source q)
    (R : Arrow B.source Kp Kq) :
    let Gp := PrefixExactLargestLift.largest A B P transport tp p
      (current_kernel_exact_eq B Kp)
    let Gq := PrefixExactLargestLift.largest A B P transport tp q
      (current_kernel_exact_eq B Kq)
    Gp = oldExactEqCast A.source hSame Gq := by
  dsimp only
  let Gp := PrefixExactLargestLift.largest A B P transport tp p
    (current_kernel_exact_eq B Kp)
  let Gq := PrefixExactLargestLift.largest A B P transport tp q
    (current_kernel_exact_eq B Kq)
  have hForward :
      oldExactEqCast A.source hSame.symm Gp ≤ Gq :=
    original_gate_le_target A B P transport tp hSame Kp Kq R
  have hReverse :
      oldExactEqCast A.source hSame Gq ≤ Gp :=
    original_gate_le_target A B P transport tp hSame.symm Kq Kp R.inv
  apply le_antisymm
  · calc
      Gp = oldExactEqCast A.source hSame
          (oldExactEqCast A.source hSame.symm Gp) :=
        (oldExactEqCast_cancel A.source hSame Gp).symm
      _ ≤ oldExactEqCast A.source hSame Gq :=
        oldExactEqCast_mono A.source hSame _ _ hForward
  · exact hReverse

end
end CCO.ExactEPGeometry
