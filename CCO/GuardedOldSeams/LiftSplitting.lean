import CCO.GuardedOldSeams.LiftMenus

/-! One simultaneous real-root splitting for the entire finite source.
Every guarded menu remains that of its previously fixed local factor;
actual binary source orbitals move both old roots together. -/

universe u v w r z
namespace CCO.GuardedOldSeams
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.GuardedTwoRoot
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2

/-- Complete actual binary coverage and reflection in ONE old local
factor give a single original motion to the images under any homomorphism.
No homogeneity of the ambient hidden completion is a premise. -/
theorem local_embedding_to_hom_pair_motion
    {P : Type z}
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (e : CCO.UnarySupport.Structure.Embedding F (originalPartialTarget S H sap nr2)) (f : Hom F (originalPartialTarget S H sap nr2))
    (b c : P) (hbc : b ≠ c) :
    ∃ g : G, originalCompletedNamedAct S H g (e.point b) = f.point b ∧
      originalCompletedNamedAct S H g (e.point c) = f.point c := by
  obtain ⟨R,hR⟩ := original_completed_distinct_pair_binary_exists S H sap
    (e.point b) (e.point c) (fun he => hbc (e.injective he))
  let xs : Fin ((originalPartialSignature S H sap nr2).arity R) → P := by
    change Fin 2 → P
    exact ![b,c]
  have hOld : F.rel R xs := e.reflect_rel R xs hR
  exact same_binary_motion S H R hR (f.map_rel R xs hOld)

variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
variable (tests : BoundedJoinedPairTests S H sap nr2 F)
include hUnary tests

/-- The actual simultaneous splitting handles every source position,
including orphan proper roots and coincident hidden images. -/
theorem guardedRootRealization_of_hom (f : Hom F (originalPartialTarget S H sap nr2)) :
    Nonempty (GuardedRootRealization S H sap nr2 F hUnary tests) := by
  classical
  obtain ⟨r⟩ := split_finite_assignment S H f.point sap ∅ Set.finite_empty
  let sf := splitAssignmentHom S H sap nr2 F f r
  have hsort (p : P) : (Hidden).sort (r.point p) = F.sort p :=
    (congrArg ULift.up (r.sort_eq p)).trans (f.sort_eq p)
  have hRoots (p : P) : ∃ x : X (F.sort p).down.1,
      (⟨(F.sort p).down.1,x⟩ : Sigma X) = (CCO.GuardedTwoRoot.SplitAssignment.allRepresentatives r) sap nr2 p ∧
      rootMap S H sap nr2 (F.sort p) x = r.point p :=
    rootBaseTerm_of_represents S H sap nr2
      ((CCO.GuardedTwoRoot.SplitAssignment.allRepresentatives_reads r) sap nr2 p) (hsort p)
  let root (p : P) : X (F.sort p).down.1 := (hRoots p).choose
  have hRep (p : P) : (⟨(F.sort p).down.1,root p⟩ : Sigma X) =
      (CCO.GuardedTwoRoot.SplitAssignment.allRepresentatives r) sap nr2 p := (hRoots p).choose_spec.1
  have hRead (p : P) : rootMap S H sap nr2 (F.sort p) (root p) = r.point p :=
    (hRoots p).choose_spec.2
  refine ⟨{ point := root, injective := ?_, guarded := ?_ }⟩
  · intro p q he
    exact (CCO.GuardedTwoRoot.SplitAssignment.allRepresentatives_injective r) sap nr2
      ((hRep p).symm.trans (he.trans (hRep q)))
  · intro k
    let e := guardedPairEmbedding S H sap nr2 F hUnary tests k
    let b := guardedPairLeft S H sap nr2 F k
    let c := guardedPairRight S H sap nr2 F k
    let localHom : Hom (F.closureStructure {k.val.1,k.val.2}) (originalPartialTarget S H sap nr2) := {
      point p := sf.point p.val
      sort_eq p := sf.sort_eq p.val
      map_func U p q h := sf.map_func U p.val q.val h
      map_rel R xs h := sf.map_rel R (Subtype.val ∘ xs) h }
    obtain ⟨g,hgb,hgc⟩ := local_embedding_to_hom_pair_motion S H sap nr2
      (F.closureStructure {k.val.1,k.val.2}) e localHom b c
      (fun he => k.property.1 (congrArg Subtype.val he))
    have hne : (⟨(F.sort k.val.1).down.1,root k.val.1⟩ : Sigma X) ≠
        ⟨(F.sort k.val.2).down.1,root k.val.2⟩ := by
      intro he
      exact k.property.1 ((CCO.GuardedTwoRoot.SplitAssignment.allRepresentatives_injective r) sap nr2
        ((hRep _).symm.trans (he.trans (hRep _))))
    obtain ⟨a,ha⟩ := S.some_colour_of_ne (root k.val.1) (root k.val.2) hne
    refine ⟨a,?_,ha⟩
    rintro record ⟨d,hd,rfl⟩
    apply d.pullback.atom_mem_of_holds ha
    apply (d.pullback_holds_iff ⟨r.point k.val.1,hsort _⟩
      ⟨r.point k.val.2,hsort _⟩ (root k.val.1) (root k.val.2)
      (hRead _) (hRead _)).mpr
    exact d.motion_preserves g hgb hgc hd

/-- Root-menu completion and genuine hidden HE completion are equivalent
under precisely the bounded local source gate. -/
theorem guarded_roots_iff_hidden_HE :
    Nonempty (GuardedRootRealization S H sap nr2 F hUnary tests) ↔
      ∃ f : Hom F (originalPartialTarget S H sap nr2), f.HomEmbedding := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.hiddenHom,R.hiddenHom_HE⟩
  · rintro ⟨f,_⟩
    exact guardedRootRealization_of_hom S H sap nr2 F hUnary tests f

end
end CCO.GuardedOldSeams
