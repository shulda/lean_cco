import CCO.TerminalHiddenHN.ActualAge
import CCO.TerminalHiddenHN.Interpretation
import CCO.TypedOrbitFrames.ActualProjectionSystem
import CCO.TypedOrbitFrames.CompletedOriginalReduct

/-! The canonical actual MI-only interpretation instantiates every field
of RealInterpretation on the SAME shared signature and target. Its real
roots are literal original points, every sort has one onto original real
projection, and the old fine atoms retain their exact named semantics.
No real representative, source Hom or interpretation provider is supplied
by the caller. The terminal gates here only construct the actual model.
-/

universe u v w r
namespace CCO.TerminalHiddenHN
open CCO.TerminalPowers CCO.TypedOrbitFrames CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames CCO.HiddenSAPReadings
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

/-- The original real sort names are literal summand tags of the shared
completed language, with no additional quotient or real sort. -/
def actualRealSort : ι ↪ (Lang S H sap hCover).Sorts where
  toFun i := ⟨⟨i,.inl ()⟩⟩
  inj' := by
    intro i j h
    exact congrArg (fun s => s.down.1) h

def actualRealRoot (i : ι) (x : X i) :
    (Hidden S H sap hCover).Carrier (actualRealSort S H sap hCover i) :=
  ⟨.inl ⟨i,x⟩,rfl⟩

theorem actualRealRoot_bijective (i : ι) :
    Function.Bijective (actualRealRoot S H sap hCover i) := by
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    change (Sum.inl (⟨i,x⟩ : Sigma X) : Values S H) = .inl ⟨i,y⟩ at hv
    simpa only [Sum.inl.injEq,Sigma.mk.injEq,heq_eq_eq,true_and] using hv
  · intro y
    obtain ⟨x,hx⟩ := original_completed_real_carrier_exists S (HF S H) sap (NR2 S hCover) y
    refine ⟨x,?_⟩
    apply Subtype.ext
    exact hx.symm

/-- Every actual primitive has proper quotient output. In particular
there is no primitive quotient-to-real selector or other new real value. -/
theorem actualPrimitive_output_not_real (F : (Lang S H sap hCover).Func) (i : ι) :
    (Lang S H sap hCover).output F ≠ actualRealSort S H sap hCover i := by
  intro h
  have h' := congrArg ULift.down h
  change originalCompletedPrimitiveOutput S (HF S H) sap (NR2 S hCover) F.down =
    ⟨i,.inl ()⟩ at h'
  rcases F with ⟨F⟩
  cases F with
  | inl p =>
      rcases p with ⟨j,D⟩
      cases h'
  | inr p =>
      cases p with
      | inl p =>
          rcases p with ⟨j,p⟩
          cases h'
      | inr p =>
          rcases p with ⟨j,k,a⟩
          cases h'

/-- EVERY actual sort, including each orphan proper quotient sort, has
one uniform onto projection term from its original real sort. -/
theorem actual_sort_projection (s : (Lang S H sap hCover).Sorts) :
    ∃ i, ∃ q : Term (Lang S H sap hCover) (actualRealSort S H sap hCover i) s,
      Function.Surjective (fun x =>
        (Hidden S H sap hCover).typedEval q (actualRealRoot S H sap hCover i x)) := by
  rcases s with ⟨⟨i,c⟩⟩
  cases c with
  | inl unit =>
      cases unit
      refine ⟨i,.id _,?_⟩
      intro y
      obtain ⟨x,hx⟩ := (actualRealRoot_bijective S H sap hCover i).2 y
      refine ⟨x,?_⟩
      apply Subtype.ext
      exact congrArg Subtype.val hx
  | inr D =>
      refine ⟨i,originalProjectionAsTerm S (HF S H) sap (NR2 S hCover) D,?_⟩
      intro y
      obtain ⟨p,hp⟩ := original_projection_typedEval_surjective
        S (HF S H) sap (NR2 S hCover) D y
      obtain ⟨x,hx⟩ := (actualRealRoot_bijective S H sap hCover i).2 p
      refine ⟨x,?_⟩
      have hEval := congrArg
        (fun z : (originalCompletedStructure S (HF S H) sap (NR2 S hCover)).Carrier
            ⟨⟨i,.inl ()⟩⟩ =>
          (originalCompletedStructure S (HF S H) sap (NR2 S hCover)).typedEval
            (originalProjectionAsTerm S (HF S H) sap (NR2 S hCover) D) z) hx
      exact hEval.trans hp

/-- The chosen names are precisely the existing real/real semantic
cylinders of the original fine atoms, including their true diversity. -/
theorem actual_old_atom_iff {i j : ι} (a : S.Atom i j) (x : X i) (y : X j) :
    (Hidden S H sap hCover).rel (originalCompletedOldAtomName S (HF S H) a)
      (fun n => if n.val = 0 then (actualRealRoot S H sap hCover i x).val
        else (actualRealRoot S H sap hCover j y).val) ↔ S.atomRel a x y := by
  change originalCompletedCylinderBinaryPredicate S (HF S H)
    (originalCompletedOldAtomName S (HF S H) a)
      (if (0 : Fin 2).val = 0 then .inl ⟨i,x⟩ else .inl ⟨j,y⟩)
      (if (1 : Fin 2).val = 0 then .inl ⟨i,x⟩ else .inl ⟨j,y⟩) ↔
    S.colour x y = some a
  simpa using original_completed_old_atom_name_semantics S (HF S H) a x y

/-- Canonical actual source instance. All interpretation data are
constructed from the original source; no conditional provider remains. -/
def actualInterpretation :
    RealInterpretation.{u,v,w,max u v,max v w,max u v}
      (G := FullAut S) S (Lang S H sap hCover) (Hidden S H sap hCover) where
  finiteSorts := inferInstance
  finiteFuncs := inferInstance
  finiteRels := inferInstance
  binary _ := rfl
  realSort := actualRealSort S H sap hCover
  root := actualRealRoot S H sap hCover
  root_bijective := actualRealRoot_bijective S H sap hCover
  motion := originalCompletedMotionHom S (HF S H) sap (NR2 S hCover)
  root_equivariant := by intro g i x; rfl
  primitive_real_identity F i h := by
    exact False.elim (actualPrimitive_output_not_real S H sap hCover F i h)
  projection := actual_sort_projection S H sap hCover
  atom := originalCompletedOldAtomName S (HF S H)
  atom_iff := actual_old_atom_iff S H sap hCover

end
end CCO.TerminalHiddenHN
