import CCO.GuardedOldSeams.LiftLocal
import CCO.GuardedOldSeams.FullPullback
import CCO.GuardedTwoRoot.BoundedSourcePair
import CCO.HiddenSAPReadings.Coordinates

/-! Actual bounded source data and canonical hidden reconstruction.
Every menu is fixed from one embedding of the same actual old joined
support. No arbitrary irreducible-support completion is assumed. -/

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
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

/-- Only actual distinct joined root supports are guarded. -/
abbrev GuardedPair := {bc : P × P // bc.1 ≠ bc.2 ∧
  (F.closureStructure {bc.1,bc.2}).Irreducible}

/-- The complete-pattern gate is requested only at the accepted 2m
bound and only for the selected actual old pair closure. -/
def BoundedJoinedPairTests : Prop :=
  ∀ b c, b ≠ c → BoundedPairTest S H sap nr2 F b c

variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
variable (tests : BoundedJoinedPairTests S H sap nr2 F)
include hUnary tests

/-- Fix one complete local source instance before defining its menu. -/
def guardedPairEmbedding (k : GuardedPair S H sap nr2 F) :
    CCO.UnarySupport.Structure.Embedding
      (F.closureStructure {k.val.1,k.val.2}) (originalPartialTarget S H sap nr2) :=
  Classical.choice (tests k.val.1 k.val.2 k.property.1 k.property.2
    (actual_pair_support_bound S H sap nr2 F hUnary k.val.1 k.val.2))

def guardedPairLeft (k : GuardedPair S H sap nr2 F) :
    F.closure {k.val.1,k.val.2} := ⟨k.val.1,F.subset_closure _ (by simp)⟩

def guardedPairRight (k : GuardedPair S H sap nr2 F) :
    F.closure {k.val.1,k.val.2} := ⟨k.val.2,F.subset_closure _ (by simp)⟩

def guardedPairMenu (k : GuardedPair S H sap nr2 F) :
    S.Menu (F.sort k.val.1).down.1 (F.sort k.val.2).down.1 :=
  let e := guardedPairEmbedding S H sap nr2 F hUnary tests k
  pairMenu S H sap nr2 (factorRecords S H sap nr2
    ⟨e.point (guardedPairLeft S H sap nr2 F k),e.sort_eq _⟩
    ⟨e.point (guardedPairRight S H sap nr2 F k),e.sort_eq _⟩)

theorem guardedPairMenu_nonempty (k : GuardedPair S H sap nr2 F) :
    (guardedPairMenu S H sap nr2 F hUnary tests k).Nonempty := by
  let e := guardedPairEmbedding S H sap nr2 F hUnary tests k
  obtain ⟨x,y,a,_,ha⟩ := one_factor_all_comparisons S H sap nr2
    (F.closureStructure {k.val.1,k.val.2}) e
    (guardedPairLeft S H sap nr2 F k) (guardedPairRight S H sap nr2 F k)
    (fun he => k.property.1 (congrArg Subtype.val he))
  exact ⟨a,ha⟩

/-- Semantic root part of the visible graph. Every formal hidden source
vertex has its own real root, including real and orphan proper vertices. -/
structure GuardedRootRealization where
  point : ∀ p : P, X (F.sort p).down.1
  injective : Function.Injective (fun p => (⟨(F.sort p).down.1,point p⟩ : Sigma X))
  guarded : ∀ k : GuardedPair S H sap nr2 F,
    S.menuRel (guardedPairMenu S H sap nr2 F hUnary tests k)
      (point k.val.1) (point k.val.2)

omit tests in
/-- A singleton witness can be moved to ANY canonical root of its
actual named sort, using original source transitivity. -/
theorem canonical_singleton_embedding (p : P) (x : X (F.sort p).down.1) :
    ∃ e : CCO.UnarySupport.Structure.Embedding (F.singletonStructure p) (originalPartialTarget S H sap nr2),
      e.point ⟨p,F.mem_closureAt p⟩ = rootMap S H sap nr2 (F.sort p) x := by
  obtain ⟨e⟩ := hUnary p
  have hsort : (Hidden).sort (rootMap S H sap nr2 (F.sort p) x) = F.sort p :=
    (Hidden).eval_sort (rootBaseTerm S H sap nr2 (F.sort p)) rfl
  have hsame : originalCompletedVertexSort S H (e.point ⟨p,F.mem_closureAt p⟩) =
      originalCompletedVertexSort S H (rootMap S H sap nr2 (F.sort p) x) :=
    congrArg ULift.down ((e.sort_eq _).trans hsort.symm)
  obtain ⟨g,hg⟩ := same_sort_transitive S H _ _ hsame
  exact ⟨postcomposeAutEmbedding (Hidden) (F.singletonStructure p) e
    (originalCompletedMotionHom S H sap nr2 g),hg⟩

def GuardedRootRealization.localEmbeddings
    (R : GuardedRootRealization S H sap nr2 F hUnary tests) :
    RootLocalEmbeddings (C := F) (A := (originalPartialTarget S H sap nr2))
      (fun p => rootMap S H sap nr2 (F.sort p) (R.point p)) where
  sort_eq p := (Hidden).eval_sort (rootBaseTerm S H sap nr2 (F.sort p)) rfl
  singleton p := canonical_singleton_embedding S H sap nr2 F hUnary p (R.point p)
  pair b c hbc hirr := by
    let k : GuardedPair S H sap nr2 F := ⟨(b,c),hbc,hirr⟩
    obtain ⟨a,ha,hxy⟩ := R.guarded k
    obtain ⟨e,hb,hc,_,_⟩ := one_factor_complete_closed_image S H sap nr2
      (F.closureStructure {b,c})
      (guardedPairEmbedding S H sap nr2 F hUnary tests k)
      (guardedPairLeft S H sap nr2 F k) (guardedPairRight S H sap nr2 F k) ha hxy
    exact ⟨e,hb,hc⟩

/-- Canonical hidden completion read from the visible roots. -/
def GuardedRootRealization.hiddenHom
    (R : GuardedRootRealization S H sap nr2 F hUnary tests) : Hom F (originalPartialTarget S H sap nr2) :=
  R.localEmbeddings.hom (fun _ => rfl)

/-- Full HE follows from the accepted positive binary local cover;
the hypotheses only test bounded actual old joined pair supports. -/
theorem GuardedRootRealization.hiddenHom_HE
    (R : GuardedRootRealization S H sap nr2 F hUnary tests) :
    R.hiddenHom.HomEmbedding := by
  apply R.localEmbeddings.homEmbedding
    (total_of_unary_admissible hUnary (originalPartialTarget_total S H sap nr2))

/-- Every surviving atom reconstructs the SAME full old source factor,
including complete relations, equality and genuine unary domains. -/
theorem guardedPair_every_atom
    (k : GuardedPair S H sap nr2 F)
    {a : S.Atom (F.sort k.val.1).down.1 (F.sort k.val.2).down.1}
    (ha : a ∈ guardedPairMenu S H sap nr2 F hUnary tests k)
    {x : X (F.sort k.val.1).down.1} {y : X (F.sort k.val.2).down.1}
    (hxy : S.atomRel a x y) :
    ∃ e : CCO.UnarySupport.Structure.Embedding
        (F.closureStructure {k.val.1,k.val.2}) (originalPartialTarget S H sap nr2),
      e.point (guardedPairLeft S H sap nr2 F k) = rootMap S H sap nr2 (F.sort k.val.1) x ∧
      e.point (guardedPairRight S H sap nr2 F k) = rootMap S H sap nr2 (F.sort k.val.2) y ∧
      (originalPartialTarget S H sap nr2).IsClosed (Set.range e.point) ∧
      Nonempty (CCO.UnarySupport.Structure.DiagramIso
        (F.closureStructure {k.val.1,k.val.2})
        ((originalPartialTarget S H sap nr2).induce (Set.range e.point) (SourceSupport.embedding_range_closed e))) :=
  one_factor_complete_closed_image S H sap nr2 _
    (guardedPairEmbedding S H sap nr2 F hUnary tests k) _ _ ha hxy

end
end CCO.GuardedOldSeams
