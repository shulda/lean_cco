import CCO.ExactEPGeometry.OriginalOneSortExactDescent
import CCO.ExactEPGeometry.OriginalRetainedIdentityArrow

/-!
# B062 C82: genuine old quotient gate and local retained-kernel nesting

Before building the next AP-only quotient safe step, two ACTUAL
preconditions must be proved:
* The genuine ORIGINAL exact gate G with E <= G is FULL E-bisaturated
  and has a real full RAW-exact image on the one-original-sort E quotient.
* At EVERY reached current parent b, the genuine current restriction
  e_b of E lies below the actual current gate K_b.

Only the ORIGINAL one-sort descent I12 is used for the first statement;
only the already proved C56 full connected gate and E1/E2/E3
largest-fiber adjunction are used for the second. These lemmas do NOT
claim an arbitrary mixed quotient descent or assume the projected
current K_b/e_b is exact. That additional actual-source C82 step
remains separately necessary before C83.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C82 old-source algebra: for ACTUAL full RAW-exact equivalences
E <= G on the same original sort, two-sided E-saturation of G is
literally G. Logical identity in the real old carrier is preserved. -/
theorem original_retained_gate_E_saturated
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E G : ExactEq A.source base) (hEG : E ≤ G) :
    RawExact.saturate
      (RawExact.evaluate A.source
        (originalExactSourceKernelWords A base hOne E base).words)
      (fun x y : A.Point base => G x y)
      (RawExact.evaluate A.source
        (originalExactSourceKernelWords A base hOne E base).words) =
      (fun x y : A.Point base => G x y) := by
  let KE : Kernel A.source base := ⟨E.val.val,E.property⟩
  let KG : Kernel A.source base := ⟨G.val.val,G.property⟩
  have hW := originalExactSourceKernelWords_relation A base hOne E base
  rw [hW]
  change TRel.comp (TRel.comp KE.rel KG.rel) KE.rel = KG.rel
  have hNested : KE.setoid ≤ KG.setoid := hEG
  rw [KE.left_absorb hNested]
  exact KE.right_absorb hNested

/-- Original C82 REAL quotient gate exactness: the full E-saturated
old exact gate G descends under I12 to the ACTUAL original
one-sort canonical exact quotient source. Neither original nor
quotient SAP is used; the quotient identity is the whole E-kernel. -/
theorem original_retained_original_quotient_gate_exact
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E G : ExactEq A.source base) (hEG : E ≤ G) :
    FullExact
      (CCO.ExactCRT.CanonicalTyped.source A.source A.homogeneous
        (originalExactSourceKernelFamily A base hOne E)
        (originalExactSourceKernelWords A base hOne E)
        (originalExactSourceKernelWords_relation A base hOne E))
      (CCO.ExactCRT.quotientRelation
        (CCO.ExactCRT.CanonicalTyped.projection
          (originalExactSourceKernelFamily A base hOne E) base)
        (CCO.ExactCRT.CanonicalTyped.projection
          (originalExactSourceKernelFamily A base hOne E) base)
        (fun x y : A.Point base => G x y)) :=
  originalOneSortFullExactDescent A base hOne E
    (fun x y : A.Point base => G x y) G.property
    (original_retained_gate_E_saturated A base hOne E G hEG)

/-- C82 current-side nested kernel obligation, on EVERY genuinely
reached current parent (including the root). This uses the same
selected original gate G for the full reached component and
transports only actual equalities of ORIGINAL sort names. -/
theorem original_retained_current_E_below_full_gate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot) :
    originalExactOnCurrentSort A B P transport (P.parent r)
      (fun i => hOne (P.parent r) i) E b.val ≤
      current_kernel_exact_eq B
        (Reached.kernel B.homogeneous
          (exactCalculus_of_homogeneous_CCO
            B.source B.homogeneous B.cco) b) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let Kb := Reached.kernel B.homogeneous C b
  let Gr := PrefixExactLargestLift.largest A B P transport tp r
    (current_kernel_exact_eq B Kroot)
  let Gb := PrefixExactLargestLift.largest A B P transport tp b.val
    (current_kernel_exact_eq B Kb)
  let hSame := hOne (P.parent r) (P.parent b.val)
  have hRootGate : Gr = oldExactEqCast A.source hSame Gb := by
    have h := original_gates_constant_on_full_reached
      A B P transport tp hOne Kroot (Reached.root Kroot) b
    dsimp only at h
    rw [Reached.root_kernel B.homogeneous C (A := Kroot)] at h
    exact h
  have hCast : oldExactEqCast A.source hSame.symm E ≤ Gb := by
    have h : E ≤ oldExactEqCast A.source hSame Gb := by
      simpa only [hRootGate] using hE
    have hCast := oldExactEqCast_mono
      A.source hSame.symm E (oldExactEqCast A.source hSame Gb) h
    simpa only [oldExactEqCast_cancel] using hCast
  change PrefixExactRestriction.rho A B P transport b.val
      (oldExactEqCast A.source hSame.symm E) ≤
      current_kernel_exact_eq B Kb
  calc
    PrefixExactRestriction.rho A B P transport b.val
        (oldExactEqCast A.source hSame.symm E) ≤
      PrefixExactRestriction.rho A B P transport b.val Gb :=
        (PrefixExactRestriction.rho_mono A B P transport b.val) hCast
    _ = current_kernel_exact_eq B Kb :=
      (PrefixExactLargestLift.largest_spec
        A B P transport tp b.val (current_kernel_exact_eq B Kb)).1

end
end CCO.ExactEPGeometry
