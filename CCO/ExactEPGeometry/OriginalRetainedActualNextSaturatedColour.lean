import CCO.ExactEPGeometry.OriginalRetainedActualNextTag
import CCO.ExactEPGeometry.OriginalCurrentExactSaturatedColour

/-!
# B062 C96: actual retained NEW atomic blocks at fixed child labels

For two fixed actual successor children, the full original-E saturation
of any complete NEW pair colour is precisely the full old saturation of
its literal unary-reduct image. The converse lifts both OLD witnesses to
the prescribed children: their old parent names are read from the complete
tagged colour, and original E preserves the actual next tag on that parent.

Both directions retain logical equality. The restriction to fixed actual
endpoint children is essential. No claim is made here that unrelated child
labels or occupancy classes may be erased, or that OLD blocks alone are
the entire NEW quotient language.
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
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- EVERY old E-witness in the same parent as an actual child point lifts
to that SAME actual child, with its literal old point unchanged. This is
the restriction of the true reduct bijection to the prescribed E-class. -/
theorem originalRetainedActualChild_lift_E_witness
    (c : (SingleStep.successor B phase).Sorts)
    (x : (SingleStep.successor B phase).Point c)
    (y : B.Point c.1)
    (hxy : (currentOriginalExactSetoid A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E).r
      ((SingleStep.projection B phase).project ⟨c,x⟩) ⟨c.1,y⟩) :
    ∃ yy : (SingleStep.successor B phase).Point c,
      (SingleStep.projection B phase).point c yy = y := by
  have hLocal := (originalExactOnCurrentSort_iff A B P transport
    (P.parent r) (fun i => hOne (P.parent r) i) E c.1 x.val y).mpr hxy
  have hTag := originalRetainedActualNextTag_eq_of_E
    A B P transport tp hOne Kroot phase E hE c.1 x.val y hLocal
  exact ⟨⟨y,hTag.symm.trans x.property⟩,rfl⟩

/-- C96 for one COMPLETE actual NEW atomic colour, including none on
the logical diagonal. Both endpoint labels are fixed actual children,
and both E-saturations are on the WHOLE tagged current carrier. -/
theorem originalRetainedActualNextSaturatedColour_iff
    (c d : (SingleStep.successor B phase).Sorts)
    (a : Option ((SingleStep.successor B phase).source.Atom c d))
    (x : (SingleStep.successor B phase).Point c)
    (y : (SingleStep.successor B phase).Point d) :
    originalCurrentExactSaturatedColour A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E ⟨c,d,a⟩ ⟨c,x⟩ ⟨d,y⟩ ↔
    originalCurrentExactSaturatedColour A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E
      ⟨c.1,d.1,a.map ((SingleStep.projection B phase).atom c d)⟩
      ((SingleStep.projection B phase).project ⟨c,x⟩)
      ((SingleStep.projection B phase).project ⟨d,y⟩) := by
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
  let T := currentOriginalExactSetoid A B P (P.parent r) hBase E
  let S := currentOriginalExactSetoid A N (P.compose R) (P.parent r) hBase E
  change setoidSaturation S
      (fun u v => taggedColour N.source u v = ⟨c,d,a⟩) ⟨c,x⟩ ⟨d,y⟩ ↔
    setoidSaturation T
      (fun u v => taggedColour B.source u v =
        ⟨c.1,d.1,a.map (R.atom c d)⟩)
      (R.project ⟨c,x⟩) (R.project ⟨d,y⟩)
  constructor
  · rintro ⟨⟨i,u⟩,⟨j,v⟩,hxu,hColour,hvy⟩
    have hi : i = c := congrArg Sigma.fst hColour
    have hj : j = d := congrArg (fun b : Age.Colour N.source => b.2.1) hColour
    subst i
    subst j
    have hAtom : N.source.colour u v = a := by
      simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hColour
    refine ⟨R.project ⟨c,u⟩,R.project ⟨d,v⟩,hxu,?_,hvy⟩
    change (⟨c.1,d.1,B.source.colour (R.point c u) (R.point d v)⟩ :
      Age.Colour B.source) = _
    rw [R.colour c d u v,hAtom]
  · rintro ⟨⟨i,u⟩,⟨j,v⟩,hxu,hColour,hvy⟩
    have hi : i = c.1 := congrArg Sigma.fst hColour
    have hj : j = d.1 :=
      congrArg (fun b : Age.Colour B.source => b.2.1) hColour
    subst i
    subst j
    obtain ⟨uu,huu⟩ := originalRetainedActualChild_lift_E_witness
      A B P transport tp hOne Kroot phase E hE c x u hxu
    obtain ⟨vv,hvv⟩ := originalRetainedActualChild_lift_E_witness
      A B P transport tp hOne Kroot phase E hE d y v (T.symm hvy)
    have hAtom : B.source.colour u v = a.map (R.atom c d) := by
      simpa only [taggedColour,Sigma.mk.injEq,heq_eq_eq,true_and] using hColour
    have hNew : N.source.colour uu vv = a := by
      apply Option.map_injective (R.atom_injective c d)
      rw [← R.colour c d uu vv,huu,hvv]
      exact hAtom
    refine ⟨⟨c,uu⟩,⟨d,vv⟩,?_,?_,?_⟩
    · change T.r (R.project ⟨c,x⟩) (R.project ⟨c,uu⟩)
      change T.r (R.project ⟨c,x⟩) ⟨c.1,R.point c uu⟩
      rw [huu]
      exact hxu
    · exact congrArg (fun b => (⟨c,d,b⟩ : Age.Colour N.source)) hNew
    · change T.r (R.project ⟨d,vv⟩) (R.project ⟨d,y⟩)
      change T.r ⟨d.1,R.point d vv⟩ (R.project ⟨d,y⟩)
      rw [hvv]
      exact hvy

/-- The COMPLETE NEW block on arbitrary actual endpoints is determined
by their two actual child-occupancy conditions and the projected OLD
block. This quantifies over every NEW optional atom and every endpoint;
the unary conditions may not be omitted. -/
theorem originalRetainedActualNextSaturatedColour_factorization
    (c d : (SingleStep.successor B phase).Sorts)
    (a : Option ((SingleStep.successor B phase).source.Atom c d))
    (p q : Sigma (SingleStep.successor B phase).Point) :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
    let S := currentOriginalExactSetoid A N (P.compose R) (P.parent r) hBase E
    originalCurrentExactSaturatedColour A N (P.compose R)
      (P.parent r) hBase E ⟨c,d,a⟩ p q ↔
      (∃ x : N.Point c, S.r p ⟨c,x⟩) ∧
      (∃ y : N.Point d, S.r q ⟨d,y⟩) ∧
      originalCurrentExactSaturatedColour A B P (P.parent r) hBase E
        ⟨c.1,d.1,a.map (R.atom c d)⟩ (R.project p) (R.project q) := by
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
  let S := currentOriginalExactSetoid A N (P.compose R) (P.parent r) hBase E
  let T := currentOriginalExactSetoid A B P (P.parent r) hBase E
  let Dnew := fun u v : Sigma N.Point => taggedColour N.source u v = ⟨c,d,a⟩
  let Dold := fun u v : Sigma B.Point =>
    taggedColour B.source u v = ⟨c.1,d.1,a.map (R.atom c d)⟩
  change setoidSaturation S Dnew p q ↔
    (∃ x : N.Point c, S.r p ⟨c,x⟩) ∧
    (∃ y : N.Point d, S.r q ⟨d,y⟩) ∧
    setoidSaturation T Dold (R.project p) (R.project q)
  constructor
  · rintro ⟨⟨i,x⟩,⟨j,y⟩,hpx,hColour,hyq⟩
    have hi : i = c := congrArg Sigma.fst hColour
    have hj : j = d := congrArg (fun b : Age.Colour N.source => b.2.1) hColour
    subst i
    subst j
    have hFixed : setoidSaturation S Dnew ⟨c,x⟩ ⟨d,y⟩ :=
      ⟨⟨c,x⟩,⟨d,y⟩,S.refl _,hColour,S.refl _⟩
    have hOld := (originalRetainedActualNextSaturatedColour_iff
      A B P transport tp hOne Kroot phase E hE c d a x y).mp hFixed
    exact ⟨⟨x,hpx⟩,⟨y,S.symm hyq⟩,
      (setoidSaturation_congr T Dold hpx (S.symm hyq)).mpr hOld⟩
  · rintro ⟨⟨x,hpx⟩,⟨y,hqy⟩,hOld⟩
    have hOldFixed := (setoidSaturation_congr T Dold hpx hqy).mp hOld
    have hFixed := (originalRetainedActualNextSaturatedColour_iff
      A B P transport tp hOne Kroot phase E hE c d a x y).mpr hOldFixed
    exact (setoidSaturation_congr S Dnew hpx hqy).mpr hFixed

/-- On the TRUE global original-E quotient carrier, EVERY saturated NEW
atomic block is precisely its two class-occupancy labels together with
the corresponding OLD atomic block. The old classes are transported by
the actual reduct-induced equivalence, never by an automorphism section. -/
theorem originalRetainedActualNextQuotientAtomicBlock_iff
    (c d : (SingleStep.successor B phase).Sorts)
    (a : Option ((SingleStep.successor B phase).source.Atom c d)) :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
    let S := currentOriginalExactSetoid A N (P.compose R) (P.parent r) hBase E
    let T := currentOriginalExactSetoid A B P (P.parent r) hBase E
    ∀ q s : Quotient S,
      fullSaturationOnClasses S
        (fun u v => taggedColour N.source u v = ⟨c,d,a⟩) q s ↔
        (∃ x : N.Point c, (Quotient.mk'' ⟨c,x⟩ : Quotient S) = q) ∧
        (∃ y : N.Point d, (Quotient.mk'' ⟨d,y⟩ : Quotient S) = s) ∧
        fullSaturationOnClasses T
          (fun u v => taggedColour B.source u v =
            ⟨c.1,d.1,a.map (R.atom c d)⟩)
          (originalGlobalEclassEquivAlongReduct
            A B N P R (P.parent r) hBase E q)
          (originalGlobalEclassEquivAlongReduct
            A B N P R (P.parent r) hBase E s) := by
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
  let S := currentOriginalExactSetoid A N (P.compose R) (P.parent r) hBase E
  let T := currentOriginalExactSetoid A B P (P.parent r) hBase E
  let Dnew := fun u v : Sigma N.Point => taggedColour N.source u v = ⟨c,d,a⟩
  let Dold := fun u v : Sigma B.Point =>
    taggedColour B.source u v = ⟨c.1,d.1,a.map (R.atom c d)⟩
  intro q s
  induction q using Quotient.inductionOn with
  | _ p =>
    induction s using Quotient.inductionOn with
    | _ z =>
      rw [originalGlobalEclassEquivAlongReduct_mk,
        originalGlobalEclassEquivAlongReduct_mk,
        fullSaturationOnClasses_mk S Dnew,
        fullSaturationOnClasses_mk T Dold]
      have hc : (∃ x : N.Point c,
          (Quotient.mk'' ⟨c,x⟩ : Quotient S) = Quotient.mk'' p) ↔
          ∃ x : N.Point c, S.r p ⟨c,x⟩ := by
        constructor
        · rintro ⟨x,hx⟩
          exact ⟨x,S.symm (Quotient.exact hx)⟩
        · rintro ⟨x,hx⟩
          exact ⟨x,Quotient.sound (S.symm hx)⟩
      have hd : (∃ y : N.Point d,
          (Quotient.mk'' ⟨d,y⟩ : Quotient S) = Quotient.mk'' z) ↔
          ∃ y : N.Point d, S.r z ⟨d,y⟩ := by
        constructor
        · rintro ⟨y,hy⟩
          exact ⟨y,S.symm (Quotient.exact hy)⟩
        · rintro ⟨y,hy⟩
          exact ⟨y,Quotient.sound (S.symm hy)⟩
      rw [hc,hd]
      exact originalRetainedActualNextSaturatedColour_factorization
        A B P transport tp hOne Kroot phase E hE c d a p z

end
end CCO.ExactEPGeometry
