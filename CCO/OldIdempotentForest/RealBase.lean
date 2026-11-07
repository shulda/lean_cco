import CCO.GuardedOldSeams.FullPullback
import CCO.HiddenSAPReadings.PartialSplitting

/-! One actual split homomorphism and one complete finite original real
base for EVERY position of a finite hidden source. The construction uses
visible SAP splitting directly, without a hidden completion or menu gate. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.ParityHasse.Original
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryFreshFrames
open CCO.UnarySupport CCO.UnarySupport.Structure
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Hidden" => originalCompletedStructure S H sap nr2
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

/-- The homomorphism and every real reading come from ONE simultaneous
split. The visible base is the complete induced structure on exactly
the range of those distinct tagged original real representatives. -/
structure OldBaseRealization where
  hom : Hom F (originalPartialTarget S H sap nr2)
  point : ∀ p : P, X (F.sort p).down.1
  reading : ∀ p, rootMap S H sap nr2 (F.sort p) (point p) = hom.point p
  injective : Function.Injective (fun p => (⟨(F.sort p).down.1,point p⟩ : Sigma X))
  base : FiniteInduced (X := X)
  base_eq_range : base.vertices = Set.range (fun p => (⟨(F.sort p).down.1,point p⟩ : Sigma X))

namespace OldBaseRealization
variable {S H sap nr2 F}
variable (R : OldBaseRealization S H sap nr2 F)

def tagged (p : P) : Sigma X := ⟨(F.sort p).down.1,R.point p⟩

theorem in_base (p : P) : R.tagged p ∈ R.base.vertices := by
  rw [R.base_eq_range]
  exact ⟨p,rfl⟩

theorem tagged_ne {p q : P} (hne : p ≠ q) : R.tagged p ≠ R.tagged q :=
  fun h => hne (R.injective h)

end OldBaseRealization

/-- Apply the accepted finite splitting ONCE to this entire actual Hom.
Both old real positions and orphan proper positions receive simultaneous
distinct real representatives; all source functions and relations remain
preserved by the resulting actual homomorphism. -/
theorem oldBaseRealization_of_hom
    (f : Hom F (originalPartialTarget S H sap nr2)) :
    Nonempty (OldBaseRealization S H sap nr2 F) := by
  classical
  obtain ⟨r⟩ := split_finite_assignment S H f.point sap ∅ Set.finite_empty
  let sf := splitAssignmentHom S H sap nr2 F f r
  have hsort (p : P) : (Hidden).sort (r.point p) = F.sort p :=
    (congrArg ULift.up (r.sort_eq p)).trans (f.sort_eq p)
  have hRoots (p : P) : ∃ x : X (F.sort p).down.1,
      (⟨(F.sort p).down.1,x⟩ : Sigma X) =
        (CCO.GuardedTwoRoot.SplitAssignment.allRepresentatives r) sap nr2 p ∧
      rootMap S H sap nr2 (F.sort p) x = r.point p :=
    rootBaseTerm_of_represents S H sap nr2
      ((CCO.GuardedTwoRoot.SplitAssignment.allRepresentatives_reads r) sap nr2 p) (hsort p)
  let point (p : P) : X (F.sort p).down.1 := (hRoots p).choose
  have hRep (p : P) : (⟨(F.sort p).down.1,point p⟩ : Sigma X) =
      (CCO.GuardedTwoRoot.SplitAssignment.allRepresentatives r) sap nr2 p :=
    (hRoots p).choose_spec.1
  refine ⟨{ hom := sf
            point := point
            reading := fun p => (hRoots p).choose_spec.2
            injective := ?_
            base := ⟨Set.range (fun p => (⟨(F.sort p).down.1,point p⟩ : Sigma X)),
              Set.finite_range _⟩
            base_eq_range := rfl }⟩
  intro p q h
  exact (CCO.GuardedTwoRoot.SplitAssignment.allRepresentatives_injective r) sap nr2
    ((hRep p).symm.trans (h.trans (hRep q)))

/-- A finite closed retained source uses the same construction directly.
No separate pair colours, pair embeddings, or hidden SAP are selected. -/
theorem oldBaseRealization_of_retained_hom {A : Set P} (hA : F.IsClosed A)
    (f : Hom (F.induce A hA) (originalPartialTarget S H sap nr2)) :
    Nonempty (OldBaseRealization S H sap nr2 (F.induce A hA)) :=
  oldBaseRealization_of_hom S H sap nr2 (F.induce A hA) f

end
end CCO.OldIdempotentForest
