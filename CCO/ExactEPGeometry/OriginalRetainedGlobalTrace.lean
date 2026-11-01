import CCO.ExactEPGeometry.OriginalRetainedIdentityArrow

/-!
# B062 C79: original one-sort gate trace on every retained identity arrow

For a true current FULL reached phase, all selected original gate
identities have the SAME real old gate G. Its untyped global relation
on tagged points is a genuine setoid, by ORIGINAL transitivity,
symmetry and the actual one-sort condition.

This source lemma identifies the complete relation of the real
C78 Arrow with exactly that one global G setoid on actual old
endpoints; there is no guessed quotient arrow, group-action
section or additional SAP hypothesis.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C79's typed-to-global equation, for EVERY actual current full
gate-identity arrow between E-supported reached types. The G is
the same TRUE root largest original full RAW-exact equivalence in
all cases, not a separate noncanonical original lift. -/
theorem original_retained_identity_arrow_global_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b c : Reached B.source Kroot)
    (hSupported : (originalExactOccupancySetoid
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E).r b.val c.val)
    (x : B.Point b.val) (y : B.Point c.val) :
    (original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE b c hSupported).rel x y ↔
    (currentOriginalExactSetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k)
      (PrefixExactLargestLift.largest A B P transport tp r
        (current_kernel_exact_eq B Kroot))).r
      (⟨b.val,x⟩ : Sigma B.Point) (⟨c.val,y⟩ : Sigma B.Point) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let Kb := Reached.kernel B.homogeneous C b
  let Gr := PrefixExactLargestLift.largest A B P transport tp r
    (current_kernel_exact_eq B Kroot)
  let Gb := PrefixExactLargestLift.largest A B P transport tp b.val
    (current_kernel_exact_eq B Kb)
  let hbi := hOne (P.parent r) (P.parent b.val)
  let hbc := hOne (P.parent r) (P.parent c.val)
  let hij := hOne (P.parent b.val) (P.parent c.val)
  have hRootGate : Gr = oldExactEqCast A.source hbi Gb := by
    have h := original_gates_constant_on_full_reached
      A B P transport tp hOne Kroot (Reached.root Kroot) b
    dsimp only at h
    rw [Reached.root_kernel B.homogeneous C (A := Kroot)] at h
    exact h
  have hOld : Gb (P.point b.val x)
      (hij.symm ▸ P.point c.val y) ↔
      Gr (hbi.symm ▸ P.point b.val x)
        (hbc.symm ▸ P.point c.val y) := by
    rw [hRootGate]
    have hc := oldExactEqCast_iff A.source hbi Gb
      (hbi.symm ▸ P.point b.val x)
      (hbc.symm ▸ P.point c.val y)
    have hTarget : (hbi ▸ (hbc.symm ▸ P.point c.val y)) =
        (hij.symm ▸ P.point c.val y) := by
      cases hbi
      cases hbc
      cases hij
      rfl
    have hSource : (hbi ▸ (hbi.symm ▸ P.point b.val x)) =
        P.point b.val x := by
      cases hbi
      rfl
    rw [hSource,hTarget] at hc
    exact hc.symm
  exact (original_retained_identity_arrow_iff
    A B P transport tp hOne Kroot E hE b c hSupported x y).trans hOld

end
end CCO.ExactEPGeometry
