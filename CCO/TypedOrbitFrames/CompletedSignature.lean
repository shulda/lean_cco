import CCO.TypedOrbitFrames.CompletedOriginalAction
import CCO.UnaryTermsReturn.CompletedNamedBinaryCylinders
import CCO.UnaryFreshFrames.Language
import Mathlib.Tactic.FinCases

/-!
# The actual completed terminal signature

Sorts are the genuine original real or represented proper MI coordinates;
unary symbols are exactly the existing projection/upward/full RAW names;
binary symbols are the existing full semantic cylinder names. Each
primitive graph is a total function on its actual input sort, extended
canonically by identity off that sort as required by the generic API.
-/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TerminalLattice CCO.TransitionClosure
open CCO.UnaryTermsReturn CCO.UnaryFreshFrames

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

/-- The canonical actual represented sort of a completed vertex. The
proof of named membership contributes no extra sort or coordinate. -/
def originalCompletedVertexSort (H : HomogeneousSource S G) :
    OriginalCompletedNamedCarrier S H → OriginalCompletedCoordinateCode S H
  | .inl ⟨i,_⟩ => ⟨i,.inl ()⟩
  | .inr ⟨⟨i,⟨J,_⟩⟩,hNamed⟩ =>
      ⟨i,.inr ⟨J,by
        obtain ⟨D,hD⟩ := hNamed
        change D.val = J at hD
        rw [← hD]
        exact D.property⟩⟩

theorem original_completed_reading_sort
    (H : HomogeneousSource S G) {x : OriginalCompletedNamedCarrier S H}
    {C : OriginalCompletedCoordinateCode S H}
    {q : Quotient (originalCompletedCoordinateKernel S H C).val}
    (h : OriginalCompletedCoordinateReading S H x C q) :
    originalCompletedVertexSort S H x = C := by
  cases h <;> rfl

def originalCompletedPrimitiveInput (H : HomogeneousSource S G) :
    OriginalCompletedPrimitiveSymbol S H → OriginalCompletedCoordinateCode S H
  | .inl ⟨i,_⟩ => ⟨i,.inl ()⟩
  | .inr (.inl ⟨i,p⟩) => ⟨i,.inr p.val.1⟩
  | .inr (.inr ⟨i,⟨_,a⟩⟩) => ⟨i,.inr a.val.1⟩

noncomputable def originalCompletedPrimitiveOutput (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    OriginalCompletedPrimitiveSymbol S H → OriginalCompletedCoordinateCode S H
  | .inl ⟨i,D⟩ => ⟨i,.inr D⟩
  | .inr (.inl ⟨i,p⟩) => ⟨i,.inr p.val.2⟩
  | .inr (.inr ⟨_,⟨j,a⟩⟩) =>
      ⟨j,.inr (originalNamedRawTransitionSymbol_target S H sap nr2 a)⟩

theorem original_completed_labelled_input_sort
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {s : OriginalCompletedPrimitiveSymbol S H}
    {x y : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedLabelledStep S H sap nr2 s x y) :
    originalCompletedVertexSort S H x = originalCompletedPrimitiveInput S H s := by
  cases h <;> rfl

theorem original_completed_labelled_output_sort
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {s : OriginalCompletedPrimitiveSymbol S H}
    {x y : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedLabelledStep S H sap nr2 s x y) :
    originalCompletedVertexSort S H y =
      originalCompletedPrimitiveOutput S H sap nr2 s := by
  cases h <;> rfl

/-- Each literal actual named primitive is functional; the same label
cannot choose unrelated values in different quotient charts. -/
theorem original_completed_labelled_functional
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {s : OriginalCompletedPrimitiveSymbol S H}
    {x y z : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedLabelledStep S H sap nr2 s x y)
    (h' : OriginalCompletedNamedLabelledStep S H sap nr2 s x z) : y = z := by
  cases h <;> cases h' <;> rfl

/-- All actual vertices of a symbol's input sort have its genuine
primitive value. Hidden orphan inputs require no real root in the base. -/
theorem original_completed_labelled_total
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (s : OriginalCompletedPrimitiveSymbol S H)
    (x : OriginalCompletedNamedCarrier S H)
    (hx : originalCompletedVertexSort S H x = originalCompletedPrimitiveInput S H s) :
    ∃ y, OriginalCompletedNamedLabelledStep S H sap nr2 s x y := by
  obtain ⟨C,q,hRead⟩ := original_completed_coordinate_reading_exists S H x
  have hC : C = originalCompletedPrimitiveInput S H s :=
    (original_completed_reading_sort S H hRead).symm.trans hx
  cases s with
  | inl s =>
      rcases s with ⟨i,D⟩
      cases hC
      cases hRead with
      | real x => exact ⟨_,.projection D x⟩
  | inr s =>
      cases s with
      | inl s =>
          rcases s with ⟨i,⟨⟨D,E⟩,hDE⟩⟩
          cases hC
          cases hRead with
          | hidden D q => exact ⟨_,.upward D E hDE q⟩
      | inr s =>
          rcases s with ⟨i,⟨j,a⟩⟩
          cases hC
          cases hRead with
          | hidden D q => exact ⟨_,.raw a q⟩

noncomputable def originalCompletedPrimitiveFunction
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (s : OriginalCompletedPrimitiveSymbol S H) (x : OriginalCompletedNamedCarrier S H) :
    OriginalCompletedNamedCarrier S H := by
  classical
  exact if hx : originalCompletedVertexSort S H x = originalCompletedPrimitiveInput S H s
    then Classical.choose (original_completed_labelled_total S H sap nr2 s x hx)
    else x

theorem original_completed_primitive_function_graph
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (s : OriginalCompletedPrimitiveSymbol S H) (x : OriginalCompletedNamedCarrier S H)
    (hx : originalCompletedVertexSort S H x = originalCompletedPrimitiveInput S H s) :
    OriginalCompletedNamedLabelledStep S H sap nr2 s x
      (originalCompletedPrimitiveFunction S H sap nr2 s x) := by
  classical
  unfold originalCompletedPrimitiveFunction
  rw [dif_pos hx]
  exact Classical.choose_spec (original_completed_labelled_total S H sap nr2 s x hx)

theorem original_completed_primitive_function_of_graph
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {s : OriginalCompletedPrimitiveSymbol S H}
    {x y : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedLabelledStep S H sap nr2 s x y) :
    originalCompletedPrimitiveFunction S H sap nr2 s x = y :=
  original_completed_labelled_functional S H sap nr2
    (original_completed_primitive_function_graph S H sap nr2 s x
      (original_completed_labelled_input_sort S H sap nr2 h)) h

/-- The actual finite terminal language, with harmless universe lifts
only on sort/function names to match the generic one-universe API. -/
noncomputable def originalCompletedLanguage (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) : Language.{max u v w} where
  Sorts := ULift.{w} (OriginalCompletedCoordinateCode S H)
  Func := ULift.{w} (OriginalCompletedPrimitiveSymbol S H)
  Rel := OriginalCompletedCylinderBinaryName S H
  input s := ⟨originalCompletedPrimitiveInput S H s.down⟩
  output s := ⟨originalCompletedPrimitiveOutput S H sap nr2 s.down⟩
  arity _ := 2
  argument name k := ⟨if k = 0 then name.1 else name.2.1⟩

/-- The genuine completed hidden STRUCTURE on the actual B052 carrier.
Its binary predicates are full semantic cylinders, never a finer old-G
orbital partition, and its unary functions are exactly genuine names. -/
noncomputable def originalCompletedStructure (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    Structure (originalCompletedLanguage S H sap nr2)
      (OriginalCompletedNamedCarrier S H) where
  sort x := ⟨originalCompletedVertexSort S H x⟩
  func s x := originalCompletedPrimitiveFunction S H sap nr2 s.down x
  func_sort s x hx := by
    have hInput : originalCompletedVertexSort S H x =
        originalCompletedPrimitiveInput S H s.down := congrArg ULift.down hx
    exact congrArg ULift.up (original_completed_labelled_output_sort S H sap nr2
      (original_completed_primitive_function_graph S H sap nr2 s.down x hInput))
  func_offsort s x hx := by
    classical
    have hInput : originalCompletedVertexSort S H x ≠
        originalCompletedPrimitiveInput S H s.down := fun h => hx (congrArg ULift.up h)
    exact dif_neg hInput
  rel name xs := by
    change (Fin 2 → OriginalCompletedNamedCarrier S H) at xs
    exact originalCompletedCylinderBinaryPredicate S H name (xs 0) (xs 1)
  rel_sort name xs hx := by
    change (Fin 2 → OriginalCompletedNamedCarrier S H) at xs
    change originalCompletedCylinderBinaryPredicate S H name (xs 0) (xs 1) at hx
    obtain ⟨hne,q,r,hq,hr,hRelation⟩ := hx
    intro k
    change Fin 2 at k
    fin_cases k
    · exact congrArg ULift.up (original_completed_reading_sort S H hq)
    · exact congrArg ULift.up (original_completed_reading_sort S H hr)

end CCO.TypedOrbitFrames
