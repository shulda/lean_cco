import CCO.OldIdempotentForest.ReconstructionRequests
import CCO.OldIdempotentForest.CycleReconstructionArrays
import CCO.OldIdempotentForest.CycleReconstructionAssignments

/-! Source16 C40(iii): requests over ANY given complete finite old base.
The endpoint gates are precisely the original kept-word profiles, RAW
idempotent gap envelopes and the fixed anchor's OWN profile. No hidden
Hom, real-base construction or completion provider is required. -/

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
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable {n : ℕ} (C : SupportedMacroChain S H sap nr2 F n)
variable (R : SourcePrunedForest S H sap nr2 F C) (A : FiniteInduced (X := X))

/-- Only retained root positions are constrained. Values at discarded
positions are arbitrary defaults, never prescribed gap interior values. -/
structure PlainBaseRoots where
  point : ChainPoints C
  injective : ∀ i : Fin (n+1), i.val ∈ R.pruning.retainedRoots 0 →
    ∀ j : Fin (n+1), j.val ∈ R.pruning.retainedRoots 0 →
      (⟨gapSort S H sap nr2 F (C.root i),point i⟩ : Sigma X) =
        ⟨gapSort S H sap nr2 F (C.root j),point j⟩ → i = j
  in_base : ∀ i : Fin (n+1), i.val ∈ R.pruning.retainedRoots 0 →
    (⟨gapSort S H sap nr2 F (C.root i),point i⟩ : Sigma X) ∈ A.vertices

namespace PlainBaseRoots
variable {S H sap nr2 F C R A}

/-- A genuinely retained-only assignment extends without adding any
condition at deleted positions or any point to the supplied old base. -/
def of_retained
    (point : ∀ i : {i : Fin (n+1) // i.val ∈ R.pruning.retainedRoots 0},
      X (gapSort S H sap nr2 F (C.root i.val)))
    (hinj : Function.Injective (fun i =>
      (⟨gapSort S H sap nr2 F (C.root i.val),point i⟩ : Sigma X)))
    (hin : ∀ i, (⟨gapSort S H sap nr2 F (C.root i.val),point i⟩ : Sigma X) ∈ A.vertices) :
    PlainBaseRoots S H sap nr2 F C R A := by
  let root : {i : Fin (n+1) // i.val ∈ R.pruning.retainedRoots 0} ↪ Fin (n+1) :=
    ⟨Subtype.val,Subtype.val_injective⟩
  let extended : ChainPoints C := extendTypedRootPoints S
    (fun i => gapSort S H sap nr2 F (C.root i)) root point
  have hpoint (i : Fin (n+1)) (hi : i.val ∈ R.pruning.retainedRoots 0) :
      extended i = point ⟨i,hi⟩ :=
    extendTypedRootPoints_at S (fun i => gapSort S H sap nr2 F (C.root i)) root point ⟨i,hi⟩
  refine ⟨extended,?_,?_⟩
  · intro i hi j hj he
    rw [hpoint i hi,hpoint j hj] at he
    exact congrArg Subtype.val (@hinj ⟨i,hi⟩ ⟨j,hj⟩ he)
  · intro i hi
    rw [hpoint i hi]
    exact hin ⟨i,hi⟩

variable (roots : PlainBaseRoots S H sap nr2 F C R A)

theorem piece_ne (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces) :
    (⟨gapSort S H sap nr2 F (R.pieceLeft q hq).val,
      roots.point ⟨q.start,by have hb := R.locatedBounds hq; omega⟩⟩ : Sigma X) ≠
    ⟨gapSort S H sap nr2 F (R.pieceRight q hq).val,
      roots.point ⟨q.stop,by have hb := R.locatedBounds hq; omega⟩⟩ := by
  intro he
  have hp := R.pruning.piece_boundaries_mem 0 hq
  have hi := congrArg Fin.val (roots.injective _ hp.1 _ hp.2 he)
  have hb := R.locatedBounds hq
  change q.start = q.stop at hi
  omega

end PlainBaseRoots

namespace SourcePrunedForest
variable {S H sap nr2 F C} (R : SourcePrunedForest S H sap nr2 F C)

def plainGapSortEq (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces)
    (g : List (Fin n)) (hg : g ≠ []) (hgap : q.piece = .gap g hg) :=
  (R.gap_original_idempotent q hq g hg hgap).choose

theorem plainGapIdem (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces)
    (g : List (Fin n)) (hg : g ≠ []) (hgap : q.piece = .gap g hg) :
    S.product (PositiveWord.profile S (gapCloseWord S (R.plainGapSortEq q hq g hg hgap)
      (R.piecePath q hq).flatten))
      (PositiveWord.profile S (gapCloseWord S (R.plainGapSortEq q hq g hg hgap)
        (R.piecePath q hq).flatten)) =
      PositiveWord.profile S (gapCloseWord S (R.plainGapSortEq q hq g hg hgap)
        (R.piecePath q hq).flatten) :=
  (R.gap_original_idempotent q hq g hg hgap).choose_spec

theorem plain_first_retained : (0 : Fin (n+1)).val ∈ R.pruning.retainedRoots 0 :=
  R.pruning.first_root_mem 0

theorem plain_last_retained : (Fin.last n).val ∈ R.pruning.retainedRoots 0 := by
  change n ∈ R.pruning.retainedRoots 0
  have h := R.pruning.last_root_mem 0
  simpa only [R.prunes.word,R.forest.original_yield,List.length_finRange,Nat.zero_add] using h

end SourcePrunedForest

variable (roots : PlainBaseRoots S H sap nr2 F C R A)

/-- On a retained singleton this is its exact ORIGINAL side word, via
the source interval's literal singleton equality. No new presentation or
reflected-menu provider occurs in this endpoint condition. -/
def PlainKeptProfiles : Prop :=
  ∀ q (hq : q ∈ locate 0 R.pruning.pieces), q.piece.IsKept →
    S.menuRel (PositiveWord.profile S (R.piecePath q hq).flatten)
      (roots.point ⟨q.start,by have hb := R.locatedBounds hq; omega⟩)
      (roots.point ⟨q.stop,by have hb := R.locatedBounds hq; omega⟩)

/-- Deleted gaps require only their actual RAW Id-union-e envelope.
Same-sort idempotence is proved from the actual forest, not an input. -/
def PlainGapEnvelopes : Prop :=
  ∀ q (hq : q ∈ locate 0 R.pruning.pieces) g hg (hgap : q.piece = .gap g hg),
    envelope S
      (PositiveWord.profile S (gapCloseWord S (R.plainGapSortEq q hq g hg hgap)
        (R.piecePath q hq).flatten)) (R.plainGapIdem q hq g hg hgap)
      (Eq.mp (congrArg X (R.plainGapSortEq q hq g hg hgap))
        (roots.point ⟨q.start,by have hb := R.locatedBounds hq; omega⟩))
      (roots.point ⟨q.stop,by have hb := R.locatedBounds hq; omega⟩)

theorem plain_piece_original_profile
    (kept : PlainKeptProfiles S H sap nr2 F C R A roots)
    (gaps : PlainGapEnvelopes S H sap nr2 F C R A roots)
    (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces) :
    S.menuRel (PositiveWord.profile S (R.piecePath q hq).flatten)
      (roots.point ⟨q.start,by have hb := R.locatedBounds hq; omega⟩)
      (roots.point ⟨q.stop,by have hb := R.locatedBounds hq; omega⟩) := by
  cases hp : q.piece with
  | kept i => exact kept q hq (by simp [hp,Piece.IsKept])
  | gap g hg =>
    let hij := R.plainGapSortEq q hq g hg hp
    let idem := R.plainGapIdem q hq g hg hp
    have hne := gap_cast_ne_of_tagged hij _ _ (roots.piece_ne q hq)
    exact gap_original_profile_of_closed S hij _ _ _
      ((envelope_distinct_iff S _ idem hne).mp (gaps q hq g hg hp))

def plainPieceRequest
    (kept : PlainKeptProfiles S H sap nr2 F C R A roots)
    (gaps : PlainGapEnvelopes S H sap nr2 F C R A roots)
    (k : R.PieceIndex) : WordRequest S := by
  let q := R.indexedPiece k
  let hq := R.indexedPiece_mem k
  have hb : q.start < q.stop ∧ q.stop ≤ n := R.locatedBounds hq
  have hm := plain_piece_original_profile S H sap nr2 F C R A roots kept gaps q hq
  exact {
    sourceSort := gapSort S H sap nr2 F (R.pieceLeft q hq).val
    targetSort := gapSort S H sap nr2 F (R.pieceRight q hq).val
    word := (R.piecePath q hq).flatten
    source := roots.point ⟨q.start,by omega⟩
    target := roots.point ⟨q.stop,by omega⟩
    atom := hm.choose
    profile := hm.choose_spec.1
    colour := hm.choose_spec.2 }

variable (anchor : SupportedMacroSide S H sap nr2 F (C.root (Fin.last n)) (C.root 0))
variable (hAnchor : S.menuRel (PositiveWord.profile S anchor.word)
  (roots.point (Fin.last n)) (roots.point 0))

def plainAnchorRequest : WordRequest S where
  sourceSort := gapSort S H sap nr2 F (C.root (Fin.last n))
  targetSort := gapSort S H sap nr2 F (C.root 0)
  word := anchor.word
  source := roots.point (Fin.last n)
  target := roots.point 0
  atom := hAnchor.choose
  profile := hAnchor.choose_spec.1
  colour := hAnchor.choose_spec.2

def plainWordRequests
    (kept : PlainKeptProfiles S H sap nr2 F C R A roots)
    (gaps : PlainGapEnvelopes S H sap nr2 F C R A roots) :
    Fin ((locate 0 R.pruning.pieces).length+1) → WordRequest S :=
  Fin.lastCases (plainAnchorRequest S H sap nr2 F C R A roots anchor hAnchor)
    (plainPieceRequest S H sap nr2 F C R A roots kept gaps)

variable (kept : PlainKeptProfiles S H sap nr2 F C R A roots)
variable (gaps : PlainGapEnvelopes S H sap nr2 F C R A roots)

@[simp] theorem plainWordRequests_piece (k : R.PieceIndex) :
    plainWordRequests S H sap nr2 F C R A roots anchor hAnchor kept gaps k.castSucc =
      plainPieceRequest S H sap nr2 F C R A roots kept gaps k :=
  Fin.lastCases_castSucc _

@[simp] theorem plainWordRequests_anchor :
    plainWordRequests S H sap nr2 F C R A roots anchor hAnchor kept gaps (Fin.last _) =
      plainAnchorRequest S H sap nr2 F C R A roots anchor hAnchor :=
  Fin.lastCases_last

theorem plainWordRequests_inBase (k : Fin ((locate 0 R.pruning.pieces).length+1)) :
    (plainWordRequests S H sap nr2 F C R A roots anchor hAnchor kept gaps k).InBase S A := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [plainWordRequests_anchor]
    exact ⟨roots.in_base _ R.plain_last_retained,roots.in_base _ R.plain_first_retained⟩
  · rw [plainWordRequests_piece]
    have hb := R.pruning.piece_boundaries_mem 0 (R.indexedPiece_mem j)
    exact ⟨roots.in_base _ hb.1,roots.in_base _ hb.2⟩

/-- ONE simultaneous insertion over precisely the caller's actual base. -/
structure PlainBaseRequests where
  insertion : SimultaneousWords S A
    (plainWordRequests S H sap nr2 F C R A roots anchor hAnchor kept gaps)

theorem plain_base_requests :
    Nonempty (PlainBaseRequests S H sap nr2 F C R A roots anchor hAnchor kept gaps) := by
  obtain ⟨out⟩ := simultaneous_word_insertion S H sap A
    (plainWordRequests S H sap nr2 F C R A roots anchor hAnchor kept gaps)
    (plainWordRequests_inBase S H sap nr2 F C R A roots anchor hAnchor kept gaps)
  exact ⟨⟨out⟩⟩

namespace PlainBaseRequests
variable {S H sap nr2 F C R A roots anchor hAnchor kept gaps}
variable (out : PlainBaseRequests S H sap nr2 F C R A roots anchor hAnchor kept gaps)

def point (_out : PlainBaseRequests S H sap nr2 F C R A roots anchor hAnchor kept gaps) :
    ChainPoints C := roots.point

theorem point_in_base (i : Fin (n+1)) (hi : i.val ∈ R.pruning.retainedRoots 0) :
    (⟨gapSort S H sap nr2 F (C.root i),out.point i⟩ : Sigma X) ∈ A.vertices :=
  roots.in_base i hi

theorem first : out.point 0 = roots.point 0 := rfl
theorem last : out.point (Fin.last n) = roots.point (Fin.last n) := rfl

def piece_line (k : R.PieceIndex) :
    FreshWordLine S (R.piecePath (R.indexedPiece k) (R.indexedPiece_mem k)).flatten
      (out.point ⟨(R.indexedPiece k).start,by have hb := R.locatedBounds (R.indexedPiece_mem k); omega⟩)
      (out.point ⟨(R.indexedPiece k).stop,by have hb := R.locatedBounds (R.indexedPiece_mem k); omega⟩)
      A.vertices := by
  exact Eq.mp (congrArg (fun request : WordRequest S =>
    FreshWordLine S request.word request.source request.target A.vertices)
    (plainWordRequests_piece S H sap nr2 F C R A roots anchor hAnchor kept gaps k))
    (out.insertion.line k.castSucc)

def anchor_line : FreshWordLine S anchor.word
    (out.point (Fin.last n)) (out.point 0) A.vertices := by
  exact Eq.mp (congrArg (fun request : WordRequest S =>
    FreshWordLine S request.word request.source request.target A.vertices)
    (plainWordRequests_anchor S H sap nr2 F C R A roots anchor hAnchor kept gaps))
    (out.insertion.line (Fin.last _))

theorem old_base_subset : A.vertices ⊆ out.insertion.base.vertices := out.insertion.old_subset

end PlainBaseRequests

end
end CCO.OldIdempotentForest
