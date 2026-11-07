import CCO.TerminalHiddenHN.ActualAge
import CCO.HiddenSAPReadings.OrbitalNamedTerms
import CCO.TypedOrbitFrames.ActualSemanticFunctions

/-! Finite actual term FUNCTIONS at every hidden input sort. The original
motion group is transitive on both real and proper quotient carriers.
Evaluation at one point therefore injects the equivariant term functions
into its finite actual singleton closure. No hidden homogeneity, CCO,
Ramsey property or syntactic term-length bound is assumed. -/

universe u v w r
namespace CCO.TerminalHiddenHN
open CCO.TypedOrbitFrames CCO.HiddenSAPReadings CCO.UnaryFreshFrames
open CCO.UnaryTermsReturn
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

theorem hidden_carrier_nonempty (s : (Lang S H sap hCover).Sorts) :
    Nonempty ((Hidden S H sap hCover).Carrier s) := by
  rcases s with ⟨⟨i,c⟩⟩
  obtain ⟨x⟩ := S.nonemptySort i
  cases c with
  | inl unit =>
    cases unit
    exact ⟨⟨.inl ⟨i,x⟩,rfl⟩⟩
  | inr D =>
    exact ⟨⟨originalCompletedNamedHiddenNode S (HF S H) D
      (Quotient.mk D.val.val x),rfl⟩⟩

theorem hidden_carrier_motion_transitive (s : (Lang S H sap hCover).Sorts) :
    letI := CCO.UnaryFreshFrames.Structure.carrierAction (Hidden S H sap hCover) s
    CCO.UnaryFreshFrames.Quotient.Transitive
      (G := originalCompletedMotionSubgroup S (HF S H) sap (NR2 S hCover))
      (M := (Hidden S H sap hCover).Carrier s) := by
  letI := CCO.UnaryFreshFrames.Structure.carrierAction (Hidden S H sap hCover) s
  intro x y
  letI := completedSortAction S (HF S H) sap (NR2 S hCover) s
  obtain ⟨g,hg⟩ := completed_sort_transitive S (HF S H) sap (NR2 S hCover) s x y
  refine ⟨⟨originalCompletedMotionHom S (HF S H) sap (NR2 S hCover) g,⟨g,rfl⟩⟩,?_⟩
  apply Subtype.ext
  change originalCompletedNamedAct S (HF S H) g x.val = y.val
  exact congrArg Subtype.val hg

theorem hidden_named_functions_finite (s : (Lang S H sap hCover).Sorts) :
    ((Hidden S H sap hCover).NamedFunctions s).Finite := by
  letI := CCO.UnaryFreshFrames.Structure.carrierAction (Hidden S H sap hCover) s
  obtain ⟨x⟩ := hidden_carrier_nonempty S H sap hCover s
  exact (Hidden S H sap hCover).namedFunctions_finite
    (originalCompletedMotionSubgroup S (HF S H) sap (NR2 S hCover))
    (hidden_carrier_motion_transitive S H sap hCover s) x
    (original_completed_all_singleton_closures_finite S (HF S H) sap (NR2 S hCover) x.val)

/-- The exact output sort is retained; distinct syntactic transition
loops can denote the same member of this actual finite function family. -/
def TermFunctionSet (s t : (Lang S H sap hCover).Sorts) :
    Set ((Hidden S H sap hCover).Carrier s → Values S H) :=
  Set.range (fun q : CCO.UnaryFreshFrames.Term (Lang S H sap hCover) s t =>
    (Hidden S H sap hCover).termFunction q)

theorem termFunctionSet_finite (s t : (Lang S H sap hCover).Sorts) :
    (TermFunctionSet S H sap hCover s t).Finite := by
  apply (hidden_named_functions_finite S H sap hCover s).subset
  rintro f ⟨q,rfl⟩
  exact ⟨t,q,rfl⟩

instance termFunctionSet_finiteType (s t : (Lang S H sap hCover).Sorts) :
    Finite (TermFunctionSet S H sap hCover s t) :=
  (termFunctionSet_finite S H sap hCover s t).to_subtype

noncomputable instance termFunctionSet_fintype (s t : (Lang S H sap hCover).Sorts) :
    Fintype (TermFunctionSet S H sap hCover s t) := Fintype.ofFinite _

/-- Choose an actual existing named term, separately at its exact input
and output sorts. No bound on the syntax of arbitrary terms is asserted. -/
def termFunctionRepresentative {s t : (Lang S H sap hCover).Sorts}
    (f : TermFunctionSet S H sap hCover s t) :
    CCO.UnaryFreshFrames.Term (Lang S H sap hCover) s t :=
  Classical.choose f.property

theorem termFunctionRepresentative_spec {s t : (Lang S H sap hCover).Sorts}
    (f : TermFunctionSet S H sap hCover s t) :
    (Hidden S H sap hCover).termFunction (termFunctionRepresentative S H sap hCover f) = f.val :=
  Classical.choose_spec f.property

end
end CCO.TerminalHiddenHN
