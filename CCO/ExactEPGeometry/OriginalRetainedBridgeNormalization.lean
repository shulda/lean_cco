import CCO.ExactEPGeometry.OriginalRetainedIdentityComposition
import CCO.ExactEPGeometry.OriginalRetainedGamma

/-!
# B062 C84: genuine original identity bridges collapse at one anchor

C79 has already proved the exact composition I_ab ; I_bc = I_ac
for the WHOLE full-RAW exact gate-identity bridges across the
actual full Reached source groupoid. Given any three real reached
objects a,b,c in ONE original E-occupancy component, normalizing
the complete bridge I_bc through the actual anchor a yields the
FULL source gate identity I_aa, not logical diagonal equality.

No quotient source/marked step is assumed. This is the precise
old-side identity coherence needed to identify duplicate E-occupancy
objects before defining selected quotient character masks.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The actual old whole I_ab ; I_bc ; I_ca equals the full
gate identity at anchor a. All composition witnesses belong to
the true intermediate reached types b and c. -/
theorem originalRetainedIdentity_normalized_at_anchor
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (a b c : Reached B.source Kroot)
    (hba : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r b.val a.val)
    (hca : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r c.val a.val) :
    let CB := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let J := originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E
    let Iab := original_retained_identity_arrow A B P transport tp
      hOne Kroot E hE a b (J.symm hba)
    let Ibc := original_retained_identity_arrow A B P transport tp
      hOne Kroot E hE b c (J.trans hba (J.symm hca))
    let Ica := original_retained_identity_arrow A B P transport tp
      hOne Kroot E hE c a hca
    (Iab.comp CB Ibc).comp CB Ica =
      Arrow.id (Reached.kernel B.homogeneous CB a) := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let J := originalExactOccupancySetoid A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E
  let Iab := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE a b (J.symm hba)
  let Ibc := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE b c (J.trans hba (J.symm hca))
  let Iac := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE a c (J.symm hca)
  let Ica := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE c a hca
  have habc : Iab.comp CB Ibc = Iac :=
    original_retained_identity_arrow_comp A B P transport tp
      hOne Kroot E hE a b c (J.symm hba)
      (J.trans hba (J.symm hca))
  have haca : Iac.comp CB Ica =
      Arrow.id (Reached.kernel B.homogeneous CB a) := by
    calc
      Iac.comp CB Ica =
          original_retained_identity_arrow A B P transport tp
            hOne Kroot E hE a a (J.refl a.val) :=
        original_retained_identity_arrow_comp A B P transport tp
          hOne Kroot E hE a c a (J.symm hca) hca
      _ = Arrow.id (Reached.kernel B.homogeneous CB a) :=
        original_retained_identity_arrow_self
          A B P transport tp hOne Kroot E hE a
  exact (congrArg (fun T => T.comp CB Ica) habc).trans haca

end
end CCO.ExactEPGeometry
