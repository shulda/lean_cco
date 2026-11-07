import CCO.OldIdempotentForest.VisibleDiagram
import CCO.GuardedOldSeams.LiftSource
import CCO.StrongExact.CycleCompletion

/-! Original homomorphic CCO and original SAP supply a genuinely bad
specified simple cycle in the ACTUAL guarded visible lift. The canonical
root signatures add no equality edge to that diversity diagram. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.GuardedTwoRoot CCO.GuardedOldSeams
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
variable (tests : BoundedJoinedPairTests S H sap nr2 F)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

theorem hidden_noncompletion_has_specified_bad_cycle
    (cco : SemanticCCO.{u,v,z,w} S)
    (hNo : ¬ FiniteHiddenCompletion S H sap nr2 F) :
    ∃ C : SimpleCycle (G_typ S H sap nr2 F hUnary tests hCover), ¬ CycleHom C := by
  classical
  by_contra hn
  have hCycles : ∀ C : SimpleCycle (G_typ S H sap nr2 F hUnary tests hCover), CycleHom C := by
    intro C
    by_contra hC
    exact hn ⟨C,hC⟩
  have hStrong := ((G_typ S H sap nr2 F hUnary tests hCover).strongCompletion_iff_cycles_of_SAP_CCO
    H sap cco).mpr hCycles
  exact hNo ((typed_guarded_lift_equivalence S H sap nr2 F hUnary tests hCover).mp hStrong)

/-- The resulting private-system cycle is constructed on the literal
same OLD roots and original word interiors, with unchanged cyclic order. -/
noncomputable def guardedPrivateCycle
    (C : SimpleCycle (G_typ S H sap nr2 F hUnary tests hCover)) :
    (RootWordGeometry.privateBranchSystem
      (typedRootWordSystem S H sap nr2 F hUnary tests hCover)).Cycle :=
  RootWordGeometry.cycleOfSpecified
    (typedRootWordSystem S H sap nr2 F hUnary tests hCover)
    (typedRootWordSeeds S H sap nr2 F hUnary tests hCover) C

@[simp] theorem guardedPrivateCycle_vertex
    (C : SimpleCycle (G_typ S H sap nr2 F hUnary tests hCover)) (p : Fin C.length) :
    (guardedPrivateCycle S H sap nr2 F hUnary tests hCover C).vertex p = C.vertices p := rfl

end CCO.OldIdempotentForest
