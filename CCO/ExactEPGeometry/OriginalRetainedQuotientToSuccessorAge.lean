import CCO.ExactEPGeometry.OriginalRetainedComparisonTables
import CCO.ExactEPGeometry.OriginalRetainedSelectedCorrectedMarkLegal
import CCO.ExactEPGeometry.OriginalPhaseFineMarkedNextEmbedding
import CCO.FullPhaseLift.BinarySource.MarkedComparisonSupport

/-!
# B062 C96/C103: every actual next quotient tuple has its actual successor age

The corrected canonical old marking descends to an ACTUAL globally legal
marking of the retained selected SourcePhase. For each finite tuple of true
next quotient points, the genuine global-E point bijection supplies an
injective old selected tuple carrying exactly its true corrected child bits.
The AP-only marked-age realization embeds that entire tuple into the actual
selected successor, retaining its complete old colour table and child names.
No source-age, marking, homogeneity or quotient-SAP provider is assumed.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry FullPhaseLift.BinarySource.MarkedComparison
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

/-- Whole finite-age inclusion from the ACTUAL original-E quotient of
the old successor to the ACTUAL retained selected SourcePhase successor.
Both actual child owners and every complete old selected colour are kept. -/
theorem originalRetainedQuotientToSuccessorAge :
    AgeMaps (originalRetainedQuotientComparisonTable A B P transport tp hOne Kroot phase E hE)
      (originalRetainedSuccessorComparisonTable A B P transport tp hOne Kroot phase E hE) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let QN := originalExactSelectedQuotientCurrentSource A N (P.compose R) hN base hBase E
  let QB := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let φ := originalRetainedActualSelectedPhase A B P transport tp hOne Kroot phase E hE
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  let M := SingleStep.successor QB φ
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  let e := originalRetainedOccupancyChildEquiv A B P transport tp hOne Kroot phase E hE
  let ζ := originalRetainedSelectedCorrectedMark A B P transport tp hOne Kroot phase E hE
  let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hBase E
  let parent := originalRetainedOccupancyParentMap A B P hOne Kroot phase E
  have hGlobal : φ.masks.GlobalMarking ζ :=
    originalRetainedSelectedCorrectedMark_globalMarking A B P transport tp hOne Kroot phase E hE
  have hParent (q : Sigma QN.Point) : (e q.1).1 = (f q).1 := by
    have hEParent := originalRetainedOccupancyChildEquiv_parent A B P transport tp hOne Kroot phase E hE q.1
    have hRep := originalOccupancyRepresentative_class A N (P.compose R) base hBase E q.1
    have hProjected := congrArg parent hRep
    have hFParent := originalPhaseSelectedPointEquiv_owner_formula A B P transport hOne Kroot phase E q
    exact hEParent.trans (hProjected.symm.trans hFParent.symm)
  intro n p
  let old : Fin n → Sigma QB.Point := fun i => f (p i)
  let bits : Fin n → Bit := fun i => ζ (old i)
  have hInjective : Function.Injective old := f.injective.comp p.injective
  have hLegal : Age.Legal QB.source φ.masks old bits :=
    ⟨fun i => hGlobal.1 (old i),fun i j => hGlobal.2 (old i) (old j)⟩
  obtain ⟨marked,hOwner,hColour⟩ := Age.embed_realized QB.source QB.homogeneous
    (φ.completion_property QB.cco) old bits hInjective hLegal
  obtain ⟨next,hNames,hFine⟩ := originalPhaseFineMarkedChart_nextEmbedding
    QB KQ φ old bits marked hOwner hColour
  refine ⟨next,?_,?_⟩
  · intro i
    apply UnarySource.childLabel_injective (SingleStep.identification QB φ)
    exact (hNames i).trans (Prod.ext (hParent (p i)).symm
      (originalRetainedSelectedCorrectedMark_child A B P transport tp hOne Kroot phase E hE (p i)))
  · intro i j
    exact hFine i j

end
end CCO.ExactEPGeometry
