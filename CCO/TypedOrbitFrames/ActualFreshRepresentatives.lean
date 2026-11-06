import CCO.TypedOrbitFrames.ActualKernelClauses
import CCO.UnaryFreshFrames.Quotient.AFF
import CCO.UnaryFreshFrames.Quotient.Sequential

/-! Source11 actual fresh representatives. EVERY source provider is now
discharged for the actual B052 carrier and original motion subgroup.
No hidden homogeneity/SAP, real base, or compatible-family premise occurs. -/

namespace CCO.TypedOrbitFrames

open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames

universe u v w r
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ j : ι, MulAction G (X j)]

/-- One actual quotient vertex admits a fresh actual original real
representative, retaining all forced values and avoiding Z on EVERY
unforced term. The real identity is included in that same avoidance. -/
theorem original_typed_fresh_quotient_representative
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) {i : ι}
    (hCover : OriginalAllFullCoversInfinite S (i := i))
    (J : OriginalNamedHiddenCoordinate S H i) (q : Quotient J.val.val)
    (Z : Set (OriginalCompletedNamedCarrier S H)) (hZ : Z.Finite) :
    ∃ a : X i, Quotient.mk J.val.val a = q ∧
      (originalCompletedStructure S H sap nr2).closureAt (.inl ⟨i,a⟩) ∩ Z =
        (originalCompletedStructure S H sap nr2).closureAt
          (originalCompletedNamedHiddenNode S H J q) ∩ Z ∧
      (.inl ⟨i,a⟩ : OriginalCompletedNamedCarrier S H) ∉ Z ∧
      ∀ C (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C),
        ¬ Quotient.KernelLe
          ((originalCompletedStructure S H sap nr2).typedEval
            (originalProjectionAsTerm S H sap nr2 J))
          ((originalCompletedStructure S H sap nr2).termFunction t) →
        (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,a⟩) ∉ Z := by
  obtain ⟨x,hx,hcl,hFresh,hAvoid⟩ :=
    (originalCompletedStructure S H sap nr2).named_fibre_avoidance
      (originalCompletedMotionSubgroup S H sap nr2)
      (original_completed_real_carrier_transitive S H sap nr2 i)
      (originalProjectionAsTerm S H sap nr2 J)
      (original_projection_typedEval_surjective S H sap nr2 J)
      (original_projection_typedEval_not_injective S H sap nr2 J)
      (original_completed_all_singleton_closures_finite S H sap nr2)
      (original_projection_forced_named_factors S H sap nr2 J)
      (original_projection_infinite_unforced_index S H sap nr2 hCover J)
      ⟨originalCompletedNamedHiddenNode S H J q,rfl⟩ Z hZ
  obtain ⟨a,ha⟩ := original_completed_real_carrier_exists S H sap nr2 x
  have hq := congrArg Subtype.val hx
  change (originalCompletedStructure S H sap nr2).eval
    (originalProjectionAsTerm S H sap nr2 J) x.val = _ at hq
  rw [ha,original_projection_as_term_eval] at hq
  refine ⟨a,original_completed_hidden_node_injective S H J hq,?_,?_,?_⟩
  · simpa only [ha] using hcl
  · simpa only [ha] using hFresh
  · intro C t hn
    have ht := hAvoid C t hn
    change (originalCompletedStructure S H sap nr2).eval t x.val ∉ Z at ht
    simpa only [ha] using ht

/-- Arbitrary actual finite unary-closed A, including mutually incompatible
or different-sort orphan coordinates, has the literal fresh-frame equation.
The additional finite F is included in the actual forbidden set. -/
theorem original_typed_fresh_real_frame
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))
    (A B F : Set (OriginalCompletedNamedCarrier S H))
    (hA : A.Finite) (hAcl : (originalCompletedStructure S H sap nr2).Closed A)
    (hB : B.Finite) (hF : F.Finite) (hAB : A ⊆ B) :
    ∃ D : Set (OriginalCompletedNamedCarrier S H), D.Finite ∧
      D ⊆ {x | (originalCompletedStructure S H sap nr2).sort x ∈
        originalCompletedRealSorts S H sap nr2} ∧
      A ⊆ (originalCompletedStructure S H sap nr2).closure D ∧
      (originalCompletedStructure S H sap nr2).closure D ∩ (B ∪ F) = A := by
  exact (originalCompletedStructure S H sap nr2).quotient_system_fresh_frame
    (originalCompletedQuotientSystem S H sap nr2)
    (originalCompletedMotionSubgroup S H sap nr2)
    (original_completed_quotient_system_source_transitive S H sap nr2)
    (original_completed_all_singleton_closures_finite S H sap nr2)
    (original_completed_quotient_system_kernel_clauses S H sap nr2 hCover)
    A (B ∪ F) hA hAcl (hB.union hF) (fun _ h => Or.inl (hAB h))

/-- Genuine finite requests for EXISTING quotient vertices. Each index
retains its original sort and actual represented FULL MI kernel. -/
abbrev OriginalTypedQuotientRequest (H : HomogeneousSource S G) :=
  Σ i : ι, Σ J : OriginalNamedHiddenCoordinate S H i, Quotient J.val.val

def originalTypedRequestAsSystemRequest
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (r : OriginalTypedQuotientRequest S H) :
    (originalCompletedQuotientSystem S H sap nr2).Request :=
  ⟨⟨⟨r.1,r.2.1⟩⟩,⟨originalCompletedNamedHiddenNode S H r.2.1 r.2.2,rfl⟩⟩

/-- ALL finite actual quotient requests admit distinct fresh real choices,
with each unforced term avoiding both Z and EVERY earlier singleton
closure. Forced repeated values are retained by their literal named factors. -/
theorem original_typed_finite_sequential_avoidance
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))
    (n : Nat) (r : Fin n → OriginalTypedQuotientRequest S H)
    (Z : Set (OriginalCompletedNamedCarrier S H)) (hZ : Z.Finite) :
    ∃ f : Fin n → OriginalCompletedNamedCarrier S H, Function.Injective f ∧
      (∀ j, (originalCompletedQuotientSystem S H sap nr2).IsChoice
        (originalTypedRequestAsSystemRequest S H sap nr2 (r j)) (f j)) ∧
      (∀ j, (originalCompletedStructure S H sap nr2).sort (f j) ∈
        originalCompletedRealSorts S H sap nr2 ∧ f j ∉ Z) ∧
      ∀ j C (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨(r j).1,.inl ()⟩⟩ C),
        ¬ Quotient.KernelLe
          ((originalCompletedStructure S H sap nr2).typedEval
            (originalProjectionAsTerm S H sap nr2 (r j).2.1))
          ((originalCompletedStructure S H sap nr2).termFunction t) →
        (originalCompletedStructure S H sap nr2).eval t (f j) ∉ Z ∧
          ∀ i, i < j → (originalCompletedStructure S H sap nr2).eval t (f j) ∉
            (originalCompletedStructure S H sap nr2).closureAt (f i) := by
  exact (originalCompletedQuotientSystem S H sap nr2).finite_sequential_avoidance
    (originalCompletedMotionSubgroup S H sap nr2)
    (original_completed_quotient_system_source_transitive S H sap nr2)
    (original_completed_all_singleton_closures_finite S H sap nr2)
    (original_completed_quotient_system_kernel_clauses S H sap nr2 hCover)
    n (fun j => originalTypedRequestAsSystemRequest S H sap nr2 (r j)) Z hZ

end CCO.TypedOrbitFrames
