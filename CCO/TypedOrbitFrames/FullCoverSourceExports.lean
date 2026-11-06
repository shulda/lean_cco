import CCO.TypedOrbitFrames.FullCoverNR2
import CCO.TypedOrbitFrames.ExactColouredOrbit
import CCO.TypedOrbitFrames.PointGeneratedSAP
import CCO.TypedOrbitFrames.InfiniteCommonClass
import CCO.TypedOrbitFrames.CompatibleSingleFrame
import CCO.TypedOrbitFrames.ActualSequentialFrames

/-! All seven source11 results under precisely the standing FULL infinite-
cover premise. NR2 is derived by FullCoverNR2, not supplied as another
source assumption. Actual named structures and closures use that proved
provider, and all original exported APIs remain available unchanged. -/

namespace CCO.TypedOrbitFrames.Source

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames CCO.RealClosure.Bounds

universe u v w r z t
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]
variable (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))

local notation "terminalNR2" => original_nr2_of_all_full_covers_infinite S hCover

variable {B : Type z} {Y : Type t}

/-- Source result 1: actual complete-base chordless classification.
This combinatorial conclusion needs no infinite-cover or NR2 premise. -/
theorem complete_base_chords
    (D : PartialDiagram S (B ⊕ Y))
    (hBase : OriginalCompleteBaseSpokes S D)
    (C : SimpleCycle D)
    (hNo : OriginalNoSpecifiedProperChord S C) :
    (∀ p : Fin C.length, ∃ y : Y, C.vertices p = Sum.inr y) ∨
      (C.length = 3 ∧
        ∃ p : Fin C.length, ∃ d : B, C.vertices p = Sum.inl d) := by
  exact original_typed_complete_base_chordless_cases S D hBase C hNo

/-- Source result 2: infinitely many actual quotient classes of the
SAME complete old coloured type; the standing provider is discharged. -/
theorem exact_coloured_orbit_infinitude
    {B : Type z} [Finite B] (base : B ↪ Sigma X)
    {i : ι} (q : X i)
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (J : OriginalNamedHiddenCoordinate S H i)
    (hunforced :
      originalCompletedNamedHiddenNode S H J (Quotient.mk J.val.val q)
        ∉ originalCompletedRealBaseClosure S H sap terminalNR2 (Set.range base)) :
    (originalExactTypeClasses S base q J.val).Infinite := by
  exact original_typed_exact_coloured_orbit_infinitude S base q H sap cco
    terminalNR2 J hunforced

/-- Source result 3, including the literal PG-ACL equation. -/
theorem real_base_algebraic_closure_eq
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (D : Set (Sigma X)) (hD : D.Finite) :
    {x | (originalCompletedRealBaseOrbit S H D x).Finite} =
      originalCompletedRealBaseClosure S H sap terminalNR2 D := by
  exact original_completed_real_base_algebraic_closure_eq S H sap cco
    terminalNR2 D hD

/-- The accompanying TOS statement on the ENTIRE actual carrier. -/
theorem outside_real_base_orbit_infinite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (D : Set (Sigma X)) (hD : D.Finite)
    (x : OriginalCompletedNamedCarrier S H)
    (hx : x ∉ originalCompletedRealBaseClosure S H sap terminalNR2 D) :
    (originalCompletedRealBaseOrbit S H D x).Infinite := by
  exact original_completed_outside_real_base_orbit_infinite S H sap cco
    terminalNR2 D hD x hx

/-- Source result 4: actual full-old-group point-generated SAP. No
hidden homogeneity/SAP or additional NR2 premise is supplied. -/
theorem point_generated_coordinate_sap
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    PointGeneratedSAP.AgeSAP
      (originalCompletedOriginal S (TerminalPowers.full_homogeneous S H)
        sap terminalNR2) := by
  exact original_source_typed_point_generated_coordinate_sap S H sap cco terminalNR2

/-- Source result 5: the FULL proper MI dichotomy, with the numerical
NR2 input derived from the same literal full-cover premise. -/
theorem mi_fibre_infinite_dichotomy
    (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))
    (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} {m : Nat} (E : Fin m → ColourEq S i) (c : Fin m → X i)
    (hPair : ∀ j k, ∃ x : X i, E j (c j) x ∧ E k (c k) x)
    (J : ColourEq S i) (hJ : J ≠ ⊤)
    (hMI : ExactCRT.FiniteOrder.BinaryMeetIrreducible J) :
    (originalActualMeetEquivalence S E ≤ J →
      ∃ j, E j ≤ J ∧ ∀ x y : X i,
        x ∈ originalActualClassFibre S E c → y ∈ originalActualClassFibre S E c → J x y) ∧
    (¬ originalActualMeetEquivalence S E ≤ J →
      Infinite {q : Quotient J.val // ∃ y : X i,
        y ∈ originalActualClassFibre S E c ∧ Quotient.mk J.val y = q}) := by
  exact original_terminal_actual_mi_fibre_dichotomy S H cco
    (original_sort_nr2_of_all_full_covers_infinite S H hCover i)
    (hCover i) E c hPair J hJ hMI

/-- Source result 6: ONE compatible real frame, including the literal
CMF equality and real-identity freshness in the SAME avoidance. -/
theorem compatible_single_real_frame
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι}
    {m : Nat}
    (E : Fin m → OriginalNamedHiddenCoordinate S H i) (c : Fin m → X i)
    (hPair : ∀ j k, ∃ x : X i, (E j).val (c j) x ∧ (E k).val (c k) x)
    (B : Set (OriginalCompletedNamedCarrier S H)) (hB : B.Finite)
    (hAB : (originalCompletedStructure S H sap terminalNR2).closure
      (originalCompatibleFamilyVertices S H E c) ⊆ B) :
    ∃ x : X i, x ∈ originalActualClassFibre S (fun j => (E j).val) c ∧
      (originalCompletedStructure S H sap terminalNR2).closure
        (originalCompatibleFamilyVertices S H E c) ⊆
          (originalCompletedStructure S H sap terminalNR2).closureAt (.inl ⟨i,x⟩) ∧
      (originalCompletedStructure S H sap terminalNR2).closureAt (.inl ⟨i,x⟩) ∩ B =
        (originalCompletedStructure S H sap terminalNR2).closure
          (originalCompatibleFamilyVertices S H E c) ∧
      (.inl ⟨i,x⟩ : OriginalCompletedNamedCarrier S H) ∉ B := by
  exact original_typed_compatible_single_real_frame S H sap cco terminalNR2
    (hCover i) E c hPair B hB hAB

/-- Source result 7: every actual finite closed hidden base, with
literal forced named factors, ALL unforced outputs and exact intersection. -/
theorem fresh_representatives
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (A B F : Set (OriginalCompletedNamedCarrier S H))
    (hA : A.Finite) (hAcl : (originalCompletedStructure S H sap terminalNR2).Closed A)
    (hB : B.Finite) (hF : F.Finite) (hAB : A ⊆ B) :
    ∃ n : Nat, ∃ r : Fin n → OriginalTypedQuotientRequest S H,
      ∃ f : Fin n → OriginalCompletedNamedCarrier S H,
      Function.Injective f ∧
      (∀ j, originalTypedRequestVertex S H (r j) ∈ A ∧
        (originalCompletedQuotientSystem S H sap terminalNR2).IsChoice
          (originalTypedRequestAsSystemRequest S H sap terminalNR2 (r j)) (f j) ∧
        (originalCompletedStructure S H sap terminalNR2).sort (f j) ∈
          originalCompletedRealSorts S H sap terminalNR2 ∧ f j ∉ B ∪ F) ∧
      (∀ b ∈ A, (originalCompletedStructure S H sap terminalNR2).sort b ∉
        originalCompletedRealSorts S H sap terminalNR2 →
        ∃ j, originalTypedRequestVertex S H (r j) = b) ∧
      (∀ j C (t : Term (originalCompletedLanguage S H sap terminalNR2) ⟨⟨(r j).1,.inl ()⟩⟩ C),
        (Quotient.KernelLe
          ((originalCompletedStructure S H sap terminalNR2).typedEval
            (originalProjectionAsTerm S H sap terminalNR2 (r j).2.1))
          ((originalCompletedStructure S H sap terminalNR2).termFunction t) →
          ∃ s : Term (originalCompletedLanguage S H sap terminalNR2) ⟨⟨(r j).1,.inr (r j).2.1⟩⟩ C,
            (originalCompletedStructure S H sap terminalNR2).eval t (f j) =
              (originalCompletedStructure S H sap terminalNR2).eval s (originalTypedRequestVertex S H (r j)) ∧
            (originalCompletedStructure S H sap terminalNR2).eval s (originalTypedRequestVertex S H (r j)) ∈ A) ∧
        (¬ Quotient.KernelLe
          ((originalCompletedStructure S H sap terminalNR2).typedEval
            (originalProjectionAsTerm S H sap terminalNR2 (r j).2.1))
          ((originalCompletedStructure S H sap terminalNR2).termFunction t) →
          (originalCompletedStructure S H sap terminalNR2).eval t (f j) ∉ B ∪ F ∧
          ∀ i, i < j → (originalCompletedStructure S H sap terminalNR2).eval t (f j) ∉
            (originalCompletedStructure S H sap terminalNR2).closureAt (f i))) ∧
      B ∩ (originalCompletedStructure S H sap terminalNR2).closure
        ((A ∩ {x | (originalCompletedStructure S H sap terminalNR2).sort x ∈
          originalCompletedRealSorts S H sap terminalNR2}) ∪ Set.range f) = A := by
  exact original_typed_fresh_representatives S H sap terminalNR2 hCover
    A B F hA hAcl hB hF hAB

/-- The source fresh-frame provider in the generic unary-structure form,
with the SAME derived NR2 proof and literal additional forbidden set. -/
theorem fresh_real_frame
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (A B F : Set (OriginalCompletedNamedCarrier S H))
    (hA : A.Finite) (hAcl : (originalCompletedStructure S H sap terminalNR2).Closed A)
    (hB : B.Finite) (hF : F.Finite) (hAB : A ⊆ B) :
    ∃ D : Set (OriginalCompletedNamedCarrier S H), D.Finite ∧
      D ⊆ {x | (originalCompletedStructure S H sap terminalNR2).sort x ∈
        originalCompletedRealSorts S H sap terminalNR2} ∧
      A ⊆ (originalCompletedStructure S H sap terminalNR2).closure D ∧
      (originalCompletedStructure S H sap terminalNR2).closure D ∩ (B ∪ F) = A := by
  exact original_typed_fresh_real_frame S H sap terminalNR2 hCover
    A B F hA hAcl hB hF hAB

end CCO.TypedOrbitFrames.Source
