import CCO.ExactEPGeometry.OriginalRetainedNormalizedArrows
import CCO.ExactEPGeometry.OriginalRetainedIdentityComposition
import CCO.ExactEPGeometry.OriginalRetainedGamma
import CCO.RigidGroupoid.Geometry.QuotientBijection

/-!
# B062 C84/C93: normalizing whole original Arrows preserves their point action

For a true retained original exact E, each reached old type b has the
actual E-occupancy anchor a_b and the genuine whole old-G identity
transport I_(b,a_b). A full Arrow R:b->c normalized to
  N = I_(a_b,b) ; R ; I_(c,a_c)
acts on the transported old K-classes exactly as
  I_(c,a_c) ∘ R
does on the original class.

The cancellation of I_(b,a_b);I_(a_b,b) is the TRUE C79 whole
full-RAW-exact identity bridge composition, not equality of points
or a section of the automorphism group. The proof includes ALL real
K-quotient points and every full Arrow.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The C79 actual whole original identity transports cancel on
K-quotient points at the old source, even when the involved
different unary types are distinct. -/
theorem originalRetainedAnchorIdentity_cancel
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
    let CB := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let J := originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E
    let a := originalReachedOccupancyAnchorOf A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot b
    let hba := originalReachedOccupancyAnchorOf_supported
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E Kroot b
    let Iba := original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE b a hba
    let Iab := original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE a b (J.symm hba)
    ∀ q : (Reached.kernel B.homogeneous CB b).Class,
      Iab.quotientMap B.homogeneous
        (Iba.quotientMap B.homogeneous q) = q := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let J := originalExactOccupancySetoid A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E
  let a := originalReachedOccupancyAnchorOf A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E Kroot b
  let hba : J.r b.val a.val :=
    originalReachedOccupancyAnchorOf_supported
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E Kroot b
  let Iba := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b a hba
  let Iab := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE a b (J.symm hba)
  let Kb := Reached.kernel B.homogeneous CB b
  have hCancel : Iba.comp CB Iab = Arrow.id Kb := by
    calc
      Iba.comp CB Iab =
          original_retained_identity_arrow
            A B P transport tp hOne Kroot E hE b b
              (J.trans hba (J.symm hba)) :=
        original_retained_identity_arrow_comp
          A B P transport tp hOne Kroot E hE b a b
          hba (J.symm hba)
      _ = Arrow.id Kb :=
        original_retained_identity_arrow_self
          A B P transport tp hOne Kroot E hE b
  intro q
  have hComp :=
    Arrow.quotientMap_comp B.homogeneous CB Iba Iab q
  calc
    Iab.quotientMap B.homogeneous
      (Iba.quotientMap B.homogeneous q) =
      (Iba.comp CB Iab).quotientMap B.homogeneous q :=
      hComp.symm
    _ = (Arrow.id Kb).quotientMap B.homogeneous q := by rw [hCancel]
    _ = q := Arrow.quotientMap_id B.homogeneous q

/-- The normalized whole old source Arrow has precisely the
anchor-point action required for the E-occupancy selected quotient
groupoid, before applying the actual C83 selected point map. -/
theorem originalRetainedNormalizedArrow_anchor_action
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
    (R : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) c)) :
    let CB := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let J := originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E
    let a := originalReachedOccupancyAnchorOf A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot b
    let d := originalReachedOccupancyAnchorOf A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot c
    let hba := originalReachedOccupancyAnchorOf_supported
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E Kroot b
    let hcd := originalReachedOccupancyAnchorOf_supported
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E Kroot c
    let Iba := original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE b a hba
    let Icd := original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE c d hcd
    ∀ q : (Reached.kernel B.homogeneous CB b).Class,
      (originalRetainedNormalizedArrow
        A B P transport tp hOne Kroot E hE b c R).quotientMap
          B.homogeneous (Iba.quotientMap B.homogeneous q) =
      Icd.quotientMap B.homogeneous
        (R.quotientMap B.homogeneous q) := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let J := originalExactOccupancySetoid A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E
  let a := originalReachedOccupancyAnchorOf A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E Kroot b
  let d := originalReachedOccupancyAnchorOf A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E Kroot c
  let hba : J.r b.val a.val :=
    originalReachedOccupancyAnchorOf_supported
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E Kroot b
  let hcd : J.r c.val d.val :=
    originalReachedOccupancyAnchorOf_supported
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E Kroot c
  let Iba := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b a hba
  let Iab := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE a b (J.symm hba)
  let Icd := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE c d hcd
  intro q
  change ((Iab.comp CB R).comp CB Icd).quotientMap B.homogeneous
      (Iba.quotientMap B.homogeneous q) =
    Icd.quotientMap B.homogeneous (R.quotientMap B.homogeneous q)
  rw [Arrow.quotientMap_comp B.homogeneous CB
    (Iab.comp CB R) Icd (Iba.quotientMap B.homogeneous q)]
  rw [Arrow.quotientMap_comp B.homogeneous CB
    Iab R (Iba.quotientMap B.homogeneous q)]
  rw [originalRetainedAnchorIdentity_cancel
    A B P transport tp hOne Kroot E hE b q]

end
end CCO.ExactEPGeometry
