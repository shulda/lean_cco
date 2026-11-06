import CCO.ExactEPGeometry.OriginalCurrentAtomicSaturation
import CCO.ExactEPGeometry.CanonicalStepProduct
import CCO.ExactEPGeometry.OriginalDiscardedSaturatedOldPair

/-!
# B062 C103: every actual next atomic block, including discarded steps

Apply E7 to both TRUE prefixes, using the constructed exact/(TP)
certificates for the actual SingleStep successor. For any genuinely
occurring next pair colour its saturated block is the old projected block
at fixed endpoint children, for arbitrary original E. At a discarded
step every class meets every legal child; consequently the equality holds
on ALL endpoints, including arbitrary child presentations of the classes.

This concerns every genuine new atomic block, not only saturated OLD
predicates on the next carrier. The selected-source isomorphism and the
retained safe-step/tower construction remain separate obligations.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry

noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
variable (E : ExactEq A.source (P.parent r))

include transport tp

/-- On fixed actual children, EVERY genuinely realized next atom has
exactly its old projected saturated block. The optional atom is read
from a real next pair, so no unoccupied cross-child diagonal is inserted. -/
theorem originalActualNextAtomicSaturation_iff
    {c d : (SingleStep.successor B phase).Sorts}
    (a x : (SingleStep.successor B phase).Point c)
    (b y : (SingleStep.successor B phase).Point d) :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
    originalCurrentExactSaturatedColour A N (P.compose R) (P.parent r) hBase E
      ⟨c,d,N.source.colour a b⟩ ⟨c,x⟩ ⟨d,y⟩ ↔
    originalCurrentExactSaturatedColour A B P (P.parent r) hBase E
      (taggedColour B.source (R.project ⟨c,a⟩) (R.project ⟨d,b⟩))
      (R.project ⟨c,x⟩) (R.project ⟨d,y⟩) := by
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
  let tpN := ExactTraceProduct.compose P R transport tp
    (canonical_step_exact_transport B phase) (canonical_step_exact_product B phase)
  have hN := originalCurrentAtomicSaturation_iff_original
    A N (P.compose R) tpN (P.parent r) hBase E a x b y
  have hB := originalCurrentAtomicSaturation_iff_original
    A B P tp (P.parent r) hBase E
      (R.point c a) (R.point c x) (R.point d b) (R.point d y)
  exact hN.trans hB.symm

/-- Discarded source C103: any global new E-class meets a specified
actual child iff its old image meets that child's parent. This is a
class-occupancy assertion, not false pointwise child-surjectivity. -/
theorem originalDiscardedActualChild_occupancy_iff
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    (p : Sigma (SingleStep.successor B phase).Point)
    (c : (SingleStep.successor B phase).Sorts) :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
    let S := currentOriginalExactSetoid A N (P.compose R) (P.parent r) hBase E
    let T := currentOriginalExactSetoid A B P (P.parent r) hBase E
    (∃ x : N.Point c, S.r p ⟨c,x⟩) ↔
      ∃ y : B.Point c.1, T.r (R.project p) ⟨c.1,y⟩ := by
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
  let S := currentOriginalExactSetoid A N (P.compose R) (P.parent r) hBase E
  let T := currentOriginalExactSetoid A B P (P.parent r) hBase E
  change (∃ x : N.Point c, S.r p ⟨c,x⟩) ↔
    ∃ y : B.Point c.1, T.r (R.project p) ⟨c.1,y⟩
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x.val,hx⟩
  · rintro ⟨y,hy⟩
    obtain ⟨x,hx⟩ := originalDiscardedEachParentClassHitsChosenChild
      A B P transport tp hOne Kroot phase E hNot c y
    refine ⟨x,?_⟩
    change T.r (R.project p) (R.project ⟨c,x⟩)
    have hx' : T.r ⟨c.1,y⟩ (R.project ⟨c,x⟩) := hx
    exact T.trans hy hx'

/-- Every actual NEW atomic block of a discarded step is precisely its
OLD projected atomic block on ALL global E-class presentations. The
quantified colour is that of a genuine new pair; both actual children
and logical equality are preserved. No OLD-only palette claim is used. -/
theorem originalDiscardedActualNextAtomicSaturation_iff
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    {c d : (SingleStep.successor B phase).Sorts}
    (a : (SingleStep.successor B phase).Point c)
    (b : (SingleStep.successor B phase).Point d)
    (p q : Sigma (SingleStep.successor B phase).Point) :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
    originalCurrentExactSaturatedColour A N (P.compose R) (P.parent r) hBase E
      ⟨c,d,N.source.colour a b⟩ p q ↔
    originalCurrentExactSaturatedColour A B P (P.parent r) hBase E
      (taggedColour B.source (R.project ⟨c,a⟩) (R.project ⟨d,b⟩))
      (R.project p) (R.project q) := by
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
  let S := currentOriginalExactSetoid A N (P.compose R) (P.parent r) hBase E
  let T := currentOriginalExactSetoid A B P (P.parent r) hBase E
  let Dnew := fun u v : Sigma N.Point =>
    taggedColour N.source u v = ⟨c,d,N.source.colour a b⟩
  let Dold := fun u v : Sigma B.Point =>
    taggedColour B.source u v = taggedColour B.source (R.project ⟨c,a⟩) (R.project ⟨d,b⟩)
  have hPull (u v : Sigma N.Point) : S.r u v ↔ T.r (R.project u) (R.project v) :=
    Iff.rfl
  change setoidSaturation S Dnew p q ↔
    setoidSaturation T Dold (R.project p) (R.project q)
  constructor
  · rintro ⟨⟨i,x⟩,⟨j,y⟩,hpx,hColour,hyq⟩
    have hi : i = c := congrArg Sigma.fst hColour
    have hj : j = d := congrArg (fun f : Age.Colour N.source => f.2.1) hColour
    subst i
    subst j
    have hFixed : setoidSaturation S Dnew ⟨c,x⟩ ⟨d,y⟩ :=
      ⟨⟨c,x⟩,⟨d,y⟩,S.refl _,hColour,S.refl _⟩
    have hOld := (originalActualNextAtomicSaturation_iff
      A B P transport tp hOne Kroot phase E a x b y).mp hFixed
    exact (setoidSaturation_congr T Dold
      ((hPull _ _).mp hpx) ((hPull _ _).mp (S.symm hyq))).mpr hOld
  · intro hOld
    obtain ⟨u,v,hpu,hColour,hvq⟩ := hOld
    have hParents : (∃ x : B.Point c.1, T.r (R.project p) ⟨c.1,x⟩) ∧
        (∃ y : B.Point d.1, T.r (R.project q) ⟨d.1,y⟩) := by
      have hu : u.1 = c.1 := congrArg Sigma.fst hColour
      have hv : v.1 = d.1 :=
        congrArg (fun f : Age.Colour B.source => f.2.1) hColour
      rcases u with ⟨i,u⟩
      rcases v with ⟨j,v⟩
      dsimp only at hu hv
      subst i
      subst j
      exact ⟨⟨u,hpu⟩,⟨v,T.symm hvq⟩⟩
    obtain ⟨x,hpx⟩ := (originalDiscardedActualChild_occupancy_iff
      A B P transport tp hOne Kroot phase E hNot p c).mpr hParents.1
    obtain ⟨y,hqy⟩ := (originalDiscardedActualChild_occupancy_iff
      A B P transport tp hOne Kroot phase E hNot q d).mpr hParents.2
    have hOldFixed := (setoidSaturation_congr T Dold
      ((hPull _ _).mp hpx) ((hPull _ _).mp hqy)).mp
        (⟨u,v,hpu,hColour,hvq⟩ : setoidSaturation T Dold (R.project p) (R.project q))
    have hFixed := (originalActualNextAtomicSaturation_iff
      A B P transport tp hOne Kroot phase E a x b y).mpr hOldFixed
    exact (setoidSaturation_congr S Dnew hpx hqy).mpr hFixed

/-- On literal global E-classes, the actual reduct-induced equivalence
preserves and reflects EVERY genuine NEW atomic block of a discarded
step. It compares actual NEW atom predicates, not old predicates merely
pulled back to the new source. -/
theorem originalDiscardedActualNextQuotientAtomicBlock_iff
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    {c d : (SingleStep.successor B phase).Sorts}
    (a : (SingleStep.successor B phase).Point c)
    (b : (SingleStep.successor B phase).Point d) :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
    let S := currentOriginalExactSetoid A N (P.compose R) (P.parent r) hBase E
    let T := currentOriginalExactSetoid A B P (P.parent r) hBase E
    ∀ q s : Quotient S,
      fullSaturationOnClasses S
        (fun u v => taggedColour N.source u v = ⟨c,d,N.source.colour a b⟩) q s ↔
      fullSaturationOnClasses T
        (fun u v => taggedColour B.source u v =
          taggedColour B.source (R.project ⟨c,a⟩) (R.project ⟨d,b⟩))
        (originalGlobalEclassEquivAlongReduct A B N P R (P.parent r) hBase E q)
        (originalGlobalEclassEquivAlongReduct A B N P R (P.parent r) hBase E s) := by
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
  let S := currentOriginalExactSetoid A N (P.compose R) (P.parent r) hBase E
  let T := currentOriginalExactSetoid A B P (P.parent r) hBase E
  let Dnew := fun u v : Sigma N.Point =>
    taggedColour N.source u v = ⟨c,d,N.source.colour a b⟩
  let Dold := fun u v : Sigma B.Point =>
    taggedColour B.source u v = taggedColour B.source (R.project ⟨c,a⟩) (R.project ⟨d,b⟩)
  dsimp only
  intro q s
  induction q using Quotient.inductionOn with
  | _ p =>
    induction s using Quotient.inductionOn with
    | _ z =>
      rw [originalGlobalEclassEquivAlongReduct_mk,
        originalGlobalEclassEquivAlongReduct_mk]
      exact (fullSaturationOnClasses_mk S Dnew p z).trans
        ((originalDiscardedActualNextAtomicSaturation_iff
          A B P transport tp hOne Kroot phase E hNot a b p z).trans
          (fullSaturationOnClasses_mk T Dold (R.project p) (R.project z)).symm)

/-- Every OLD atomic block is also hit by a genuine NEW atomic block
of a discarded step. The witnesses come from the actual whole reduct
bijection. Together with the preceding all-new-block theorem this is
exhaustive in BOTH palette directions, including logical identity. -/
theorem originalDiscardedOldAtomicBlock_has_actualNextBlock
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    (a b : Sigma B.Point) :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
    ∃ aa bb : Sigma N.Point,
      R.project aa = a ∧ R.project bb = b ∧
      ∀ p q : Sigma N.Point,
        originalCurrentExactSaturatedColour A N (P.compose R) (P.parent r) hBase E
          (taggedColour N.source aa bb) p q ↔
        originalCurrentExactSaturatedColour A B P (P.parent r) hBase E
          (taggedColour B.source a b) (R.project p) (R.project q) := by
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
  obtain ⟨aa,ha⟩ := R.bijective.2 a
  obtain ⟨bb,hb⟩ := R.bijective.2 b
  change R.project aa = a at ha
  change R.project bb = b at hb
  refine ⟨aa,bb,ha,hb,?_⟩
  intro p q
  have h := originalDiscardedActualNextAtomicSaturation_iff
    A B P transport tp hOne Kroot phase E hNot aa.2 bb.2 p q
  change originalCurrentExactSaturatedColour A N (P.compose R) (P.parent r) hBase E
      (taggedColour N.source aa bb) p q ↔
    originalCurrentExactSaturatedColour A B P (P.parent r) hBase E
      (taggedColour B.source (R.project aa) (R.project bb)) (R.project p) (R.project q) at h
  rw [ha,hb] at h
  exact h

end
end CCO.ExactEPGeometry
