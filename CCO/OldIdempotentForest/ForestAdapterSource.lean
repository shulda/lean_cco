import CCO.OldIdempotentForest.ForestAdapterSubtrees
import CCO.OldIdempotentForest.MacroIntervalsSourceChain
import CCO.OldIdempotentForest.StoppedPruningAlgebra
import CCO.OldIdempotentForest.PruningBounds
import CCO.OldIdempotentForest.GapConsumers
import CCO.OldIdempotentForest.LocalObstruction

/-! Actual source application of the received forest and stopped
pruning. Every deleted piece is its canonical original supported OLD
subpath. Its literal old certificate is proved, never supplied. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot
open CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.UnarySupport CCO.UnarySupport.Structure
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

/-- A positive typed word whose STATE is idempotent has a literal
same-sort cast of that very word with strong idempotent profile. -/
theorem original_word_idempotent {i j : ι} (word : PositiveWord S i j)
    (h : profileMul S H sap (.positive (wordProfile S H sap word))
      (.positive (wordProfile S H sap word)) = .positive (wordProfile S H sap word)) :
    ∃ hij : i = j, S.product (PositiveWord.profile S (gapCloseWord S hij word))
      (PositiveWord.profile S (gapCloseWord S hij word)) =
        PositiveWord.profile S (gapCloseWord S hij word) := by
  have hij : i = j := positive_idempotent_same_sort S H sap _ h
  refine ⟨hij,?_⟩
  cases hij
  rw [profileMul_compatible S H sap (wordProfile S H sap word) (wordProfile S H sap word) rfl] at h
  have he := congrArg Subtype.val (TypedProfileState.positive.inj h)
  change (⟨i,i,⟨S.product (PositiveWord.profile S word) (PositiveWord.profile S word),_⟩⟩ :
    TypedPrefix.State S) = ⟨i,i,⟨PositiveWord.profile S word,_⟩⟩ at he
  simpa only [Sigma.mk.injEq,heq_eq_eq,true_and,Subtype.mk.injEq,gapCloseWord] using he

variable (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable {n : ℕ} (C : SupportedMacroChain S H sap nr2 F n)

/-- The forest exists for THIS actual original source path and is
pruned by the actual STOP algorithm, with exact original occurrence yield. -/
structure SourcePrunedForest where
  forest : C.macroPath.Forest H sap
  pruning : PruningTree (Fin n)
  prunes : Prunes forest.tree pruning

theorem sourcePrunedForest_exists (hn : 0 < n) :
    Nonempty (SourcePrunedForest S H sap nr2 F C) := by
  letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
  obtain ⟨forest⟩ := C.macroPath.forest_exists H sap hn
  obtain ⟨p,hp⟩ := exists_stopped_pruning (C.macroPath.eval H sap) forest.tree forest.ramsey
  exact ⟨⟨forest,p,hp⟩⟩

namespace SourcePrunedForest
variable {S H sap nr2 F C} (R : SourcePrunedForest S H sap nr2 F C)

theorem locatedBounds {q : LocatedPiece (Fin n)} (hq : q ∈ locate 0 R.pruning.pieces) :
    q.start < q.stop ∧ q.stop ≤ n := by
  have h := R.prunes.located_bounds hq
  rw [R.forest.original_yield,List.length_finRange] at h
  exact h

/-- The actual source subpath of every retained singleton or maximal
deleted interval. Its word is assembled from the original sides only. -/
def piecePath (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces) :=
  C.intervalPath q.start q.stop (R.locatedBounds hq).1 (R.locatedBounds hq).2

theorem piecePath_eval (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces) :
    C.macroPath.eval H sap q.piece.word =
      .positive (wordProfile S H sap (R.piecePath q hq).flatten) := by
  have hs := R.prunes.located_slice hq
  rw [R.forest.original_yield] at hs
  have hv := C.eval_interval_eq_flatten q.start q.stop (R.locatedBounds hq).1 (R.locatedBounds hq).2
  rw [hs] at hv
  exact hv

/-- Actual C24/C06 source discharge: each maximal gap's entire ORIGINAL
atomic word has a nonempty same-sort idempotent strong profile. -/
theorem gap_original_idempotent (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces)
    (g : List (Fin n)) (hg : g ≠ []) (hgap : q.piece = .gap g hg) :
    ∃ hij : gapSort S H sap nr2 F (C.root ⟨q.start,by have hb := R.locatedBounds hq; omega⟩) =
        gapSort S H sap nr2 F (C.root ⟨q.stop,by have hb := R.locatedBounds hq; omega⟩),
      S.product (PositiveWord.profile S (gapCloseWord S hij (R.piecePath q hq).flatten))
        (PositiveWord.profile S (gapCloseWord S hij (R.piecePath q hq).flatten)) =
          PositiveWord.profile S (gapCloseWord S hij (R.piecePath q hq).flatten) := by
  letI : Semigroup (TypedProfileState S) := profileSemigroup S H sap
  have hmul : ∀ x y : List (Fin n), x ≠ [] → y ≠ [] →
      C.macroPath.eval H sap (x ++ y) = C.macroPath.eval H sap x * C.macroPath.eval H sap y :=
    C.macroPath.eval_append H sap
  have hi := R.prunes.located_gap_idempotent (C.macroPath.eval H sap) hmul
    R.forest.ramsey hq hg hgap
  have he := R.piecePath_eval q hq
  rw [hgap] at he
  change C.macroPath.eval H sap g = .positive (wordProfile S H sap (R.piecePath q hq).flatten) at he
  change profileMul S H sap (C.macroPath.eval H sap g) (C.macroPath.eval H sap g) =
    C.macroPath.eval H sap g at hi
  rw [he] at hi
  exact original_word_idempotent S H sap _ hi

/-- Every recorded gap has all the literal OLD boundary-coordinate
certificates, proved on its actual original supported subpath before
deleting any old vertex. No arbitrary holonomy or certificate is an input. -/
theorem gap_old_coordinate_certificates
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces)
    (g : List (Fin n)) (hg : g ≠ []) (hgap : q.piece = .gap g hg) :
    ∃ hij : gapSort S H sap nr2 F (C.root ⟨q.start,by have hb := R.locatedBounds hq; omega⟩) =
        gapSort S H sap nr2 F (C.root ⟨q.stop,by have hb := R.locatedBounds hq; omega⟩),
      ∃ idem : S.product (PositiveWord.profile S (gapCloseWord S hij (R.piecePath q hq).flatten))
          (PositiveWord.profile S (gapCloseWord S hij (R.piecePath q hq).flatten)) =
            PositiveWord.profile S (gapCloseWord S hij (R.piecePath q hq).flatten),
        ∀ (D : CCO.TransitionClosure.OriginalNamedHiddenCoordinate S H
            (gapSort S H sap nr2 F (C.root ⟨q.stop,by have hb := R.locatedBounds hq; omega⟩)))
          (above : envelope S (PositiveWord.profile S (gapCloseWord S hij (R.piecePath q hq).flatten)) idem ≤ D.val),
          Nonempty (GapCoordinateCertificate S H sap nr2 F hij D) := by
  obtain ⟨hij,idem⟩ := R.gap_original_idempotent q hq g hg hgap
  exact ⟨hij,idem,fun D above => old_gap_coordinate_equation S H sap nr2 F hUnary
    (R.piecePath q hq) hij idem D above⟩

theorem retained_bounds : R.pruning.leaves ≤ 2 ^ (3 * Nat.card (TypedProfileState S)) ∧
    (R.pruning.retainedRoots 0).card ≤ 2 ^ (3 * Nat.card (TypedProfileState S) + 1) := by
  have h := R.prunes.uniform_bounds
  exact ⟨h.1.trans (Nat.pow_le_pow_right Nat.zero_lt_two R.forest.height_bound),
    h.2.2.trans (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.add_le_add_right R.forest.height_bound 1))⟩

theorem retained_root_bound {i : ℕ} (hi : i ∈ R.pruning.retainedRoots 0) : i ≤ n := by
  have hb := PruningTree.retainedRoots_bounds hi
  rw [R.prunes.word,R.forest.original_yield,List.length_finRange,Nat.zero_add] at hb
  exact hb.2

/-- Only actual OLD source roots generate the retained support. There
are no auxiliary real representatives or future completion vertices. -/
def oldGenerators : Finset P := by
  classical
  exact (R.pruning.retainedRoots 0).attach.image
    (fun i => C.root ⟨i.val,Nat.lt_succ_of_le (R.retained_root_bound i.property)⟩)

theorem oldGenerators_card : R.oldGenerators.card ≤ 2 ^ (3 * Nat.card (TypedProfileState S)+1) := by
  classical
  exact Finset.card_image_le.trans (by
    simpa only [Finset.card_attach] using R.retained_bounds.2)

theorem root_mem_oldGenerators (i : Fin (n+1)) (hi : i.val ∈ R.pruning.retainedRoots 0) :
    C.root i ∈ R.oldGenerators := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨⟨i.val,hi⟩,Finset.mem_attach _ _,by congr 1⟩

theorem piece_old_boundaries (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces) :
    C.root ⟨q.start,by have hb := R.locatedBounds hq; omega⟩ ∈ R.oldGenerators ∧
      C.root ⟨q.stop,by have hb := R.locatedBounds hq; omega⟩ ∈ R.oldGenerators := by
  have hb := R.pruning.piece_boundaries_mem 0 hq
  exact ⟨R.root_mem_oldGenerators _ hb.1,R.root_mem_oldGenerators _ hb.2⟩

def pieceLeft (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces) :
    F.closure (R.oldGenerators : Set P) :=
  ⟨C.root ⟨q.start,by have hb := R.locatedBounds hq; omega⟩,
    F.subset_closure _ (R.piece_old_boundaries q hq).1⟩

def pieceRight (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces) :
    F.closure (R.oldGenerators : Set P) :=
  ⟨C.root ⟨q.stop,by have hb := R.locatedBounds hq; omega⟩,
    F.subset_closure _ (R.piece_old_boundaries q hq).2⟩

/-- Every deleted ORIGINAL whole word is admissible after ANY actual
homomorphism of this retained old closure and distinct representative
splitting. The literal OGC and FULL RAW envelope are discharged internally. -/
theorem gap_boundary_original_profile
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces)
    (g : List (Fin n)) (hg : g ≠ []) (hgap : q.piece = .gap g hg)
    (f : Hom (F.closureStructure (R.oldGenerators : Set P)) (originalPartialTarget S H sap nr2))
    (x : X (gapSort S H sap nr2 F (R.pieceLeft q hq).val))
    (y : X (gapSort S H sap nr2 F (R.pieceRight q hq).val))
    (hx : rootMap S H sap nr2 (F.sort (R.pieceLeft q hq).val) x = f.point (R.pieceLeft q hq))
    (hy : rootMap S H sap nr2 (F.sort (R.pieceRight q hq).val) y = f.point (R.pieceRight q hq))
    (hne : (⟨gapSort S H sap nr2 F (R.pieceLeft q hq).val,x⟩ : Sigma X) ≠
      ⟨gapSort S H sap nr2 F (R.pieceRight q hq).val,y⟩) :
    S.menuRel (PositiveWord.profile S (R.piecePath q hq).flatten) x y := by
  obtain ⟨hij,idem⟩ := R.gap_original_idempotent q hq g hg hgap
  exact old_gap_boundary_diversity_of_tagged S H sap nr2 F hUnary cco
    (R.piecePath q hq) hij idem (F.isClosed_closure _) (R.pieceLeft q hq).property
    (R.pieceRight q hq).property f x y hx hy hne

theorem original_endpoints_mem_oldGenerators :
    C.root ⟨0,by omega⟩ ∈ R.oldGenerators ∧ C.root ⟨n,by omega⟩ ∈ R.oldGenerators := by
  have hfirst := R.pruning.first_root_mem 0
  have hlast := R.pruning.last_root_mem 0
  rw [R.prunes.word,R.forest.original_yield,List.length_finRange,Nat.zero_add] at hlast
  exact ⟨R.root_mem_oldGenerators _ hfirst,R.root_mem_oldGenerators _ hlast⟩

/-- The complete old endpoint support of every retained original side
lies in this actual induced closure. No completion of it is asserted. -/
theorem piece_pair_support_subset (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces) :
    F.closure {C.root ⟨q.start,by have hb := R.locatedBounds hq; omega⟩,
      C.root ⟨q.stop,by have hb := R.locatedBounds hq; omega⟩} ⊆
        F.closure (R.oldGenerators : Set P) := by
  have hb := R.piece_old_boundaries q hq
  apply F.closure_mono
  rintro x (rfl | rfl)
  · exact hb.1
  · exact hb.2

theorem old_closure_bound
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2)) :
    Nat.card (F.closure (R.oldGenerators : Set P)) ≤
      originalSourceUniformNormalCodeBudget S H * 2 ^ (3 * Nat.card (TypedProfileState S)+1) :=
  old_source_generated_card S H sap nr2 F hUnary R.oldGenerators _ R.oldGenerators_card

/-- The source16 conservative OAB constant follows without changing
the actual semigroup cardinal or adding any OLD generator. -/
theorem old_anchor_bound
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2)) :
    Nat.card (F.closure (R.oldGenerators : Set P)) ≤
      originalSourceUniformNormalCodeBudget S H *
        (2 ^ (3 * Nat.card (TypedProfileState S)+3) + 4) := by
  apply R.old_closure_bound hUnary |>.trans
  apply Nat.mul_le_mul_left
  have hp : 2 ^ (3 * Nat.card (TypedProfileState S)+1) ≤
      2 ^ (3 * Nat.card (TypedProfileState S)+3) :=
    Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  omega

end SourcePrunedForest
end
end CCO.OldIdempotentForest
