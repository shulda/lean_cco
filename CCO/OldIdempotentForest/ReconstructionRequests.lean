import CCO.OldIdempotentForest.ForestAdapterSource
import CCO.OldIdempotentForest.RealBase
import CCO.OldIdempotentForest.RetainedSides
import CCO.GuardedOldSeams.Simultaneous

/-! The actual pruned source issues its EXACT original whole-word
requests and fixed original anchor over ONE complete old real base.
Every profile premise is proved from the retained source, and one
simultaneous insertion realizes the entire finite request family. -/

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

namespace SourcePrunedForest
variable {S H sap nr2 F C} (R : SourcePrunedForest S H sap nr2 F C)

abbrev PieceIndex := Fin (locate 0 R.pruning.pieces).length

def indexedPiece (k : R.PieceIndex) : LocatedPiece (Fin n) :=
  (locate 0 R.pruning.pieces).get k

theorem indexedPiece_mem (k : R.PieceIndex) : R.indexedPiece k ∈ locate 0 R.pruning.pieces :=
  List.get_mem _ _

def anchorLeft : F.closure (R.oldGenerators : Set P) :=
  ⟨C.root ⟨n,by omega⟩,F.subset_closure _ R.original_endpoints_mem_oldGenerators.2⟩

def anchorRight : F.closure (R.oldGenerators : Set P) :=
  ⟨C.root ⟨0,by omega⟩,F.subset_closure _ R.original_endpoints_mem_oldGenerators.1⟩

theorem piece_boundaries_ne (hC : Function.Injective C.root)
    (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces) :
    R.pieceLeft q hq ≠ R.pieceRight q hq := by
  intro h
  have he := congrArg Fin.val (hC (congrArg Subtype.val h))
  have hb := R.locatedBounds hq
  change q.start = q.stop at he
  omega

/-- Kept singleton membership comes from its actual original side.
Maximal gaps use the actual OLD coordinate certificates and exact MI
reconstruction already discharged by the source forest adapter. -/
theorem piece_original_profile
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root)
    (D : OldBaseRealization S H sap nr2 (F.closureStructure (R.oldGenerators : Set P)))
    (q : LocatedPiece (Fin n)) (hq : q ∈ locate 0 R.pruning.pieces) :
    S.menuRel (PositiveWord.profile S (R.piecePath q hq).flatten)
      (D.point (R.pieceLeft q hq)) (D.point (R.pieceRight q hq)) := by
  have hne := D.tagged_ne (R.piece_boundaries_ne hC q hq)
  cases q with
  | mk start piece =>
    cases piece with
    | kept i =>
      have hstart : start < n := by
        have hb := R.locatedBounds hq
        simp only [LocatedPiece.stop,Piece.word,List.length_singleton] at hb
        omega
      change S.menuRel (PositiveWord.profile S
        (C.intervalPath start (start+1) (by omega) (by omega)).flatten) _ _
      rw [C.intervalPath_flatten_single start hstart]
      exact retained_side_profile_of_hom S H sap nr2 F (C.side ⟨start,hstart⟩)
        (F.isClosed_closure _) (R.pieceLeft ⟨start,.kept i⟩ hq).property
        (R.pieceRight ⟨start,.kept i⟩ hq).property D.hom _ _
        (D.reading (R.pieceLeft ⟨start,.kept i⟩ hq))
        (D.reading (R.pieceRight ⟨start,.kept i⟩ hq)) hne
    | gap g hg =>
      exact R.gap_boundary_original_profile hUnary cco _ hq g hg rfl D.hom _ _
        (D.reading _) (D.reading _) hne

def pieceRequest
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root)
    (D : OldBaseRealization S H sap nr2 (F.closureStructure (R.oldGenerators : Set P)))
    (k : R.PieceIndex) : WordRequest S := by
  let q := R.indexedPiece k
  let hq := R.indexedPiece_mem k
  have hm := R.piece_original_profile hUnary cco hC D q hq
  exact {
    sourceSort := gapSort S H sap nr2 F (R.pieceLeft q hq).val
    targetSort := gapSort S H sap nr2 F (R.pieceRight q hq).val
    word := (R.piecePath q hq).flatten
    source := D.point (R.pieceLeft q hq)
    target := D.point (R.pieceRight q hq)
    atom := hm.choose
    profile := hm.choose_spec.1
    colour := hm.choose_spec.2 }

def anchorRequest
    (D : OldBaseRealization S H sap nr2 (F.closureStructure (R.oldGenerators : Set P)))
    (anchor : SupportedMacroSide S H sap nr2 F (C.root ⟨n,by omega⟩) (C.root ⟨0,by omega⟩)) :
    WordRequest S := by
  have hne : R.anchorLeft ≠ R.anchorRight := fun h => anchor.distinct (congrArg Subtype.val h)
  have hm := retained_side_profile_of_hom S H sap nr2 F anchor
    (F.isClosed_closure _) R.anchorLeft.property R.anchorRight.property
    D.hom (D.point R.anchorLeft) (D.point R.anchorRight)
    (D.reading R.anchorLeft) (D.reading R.anchorRight) (D.tagged_ne hne)
  exact {
    sourceSort := gapSort S H sap nr2 F R.anchorLeft.val
    targetSort := gapSort S H sap nr2 F R.anchorRight.val
    word := anchor.word
    source := D.point R.anchorLeft
    target := D.point R.anchorRight
    atom := hm.choose
    profile := hm.choose_spec.1
    colour := hm.choose_spec.2 }

section LiteralRequests
variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
variable (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root)
variable (D : OldBaseRealization S H sap nr2 (F.closureStructure (R.oldGenerators : Set P)))
variable (anchor : SupportedMacroSide S H sap nr2 F (C.root ⟨n,by omega⟩) (C.root ⟨0,by omega⟩))

@[simp] theorem pieceRequest_word (k : R.PieceIndex) :
    (R.pieceRequest hUnary cco hC D k).word =
      (R.piecePath (R.indexedPiece k) (R.indexedPiece_mem k)).flatten := rfl

@[simp] theorem pieceRequest_source (k : R.PieceIndex) :
    (R.pieceRequest hUnary cco hC D k).source =
      D.point (R.pieceLeft (R.indexedPiece k) (R.indexedPiece_mem k)) := rfl

@[simp] theorem pieceRequest_target (k : R.PieceIndex) :
    (R.pieceRequest hUnary cco hC D k).target =
      D.point (R.pieceRight (R.indexedPiece k) (R.indexedPiece_mem k)) := rfl

@[simp] theorem anchorRequest_word : (R.anchorRequest D anchor).word = anchor.word := rfl
@[simp] theorem anchorRequest_source : (R.anchorRequest D anchor).source = D.point R.anchorLeft := rfl
@[simp] theorem anchorRequest_target : (R.anchorRequest D anchor).target = D.point R.anchorRight := rfl

end LiteralRequests

/-- The located pieces retain their actual list order. The last request
is the separate fixed ORIGINAL anchor, closing last old root to first. -/
def wordRequests
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root)
    (D : OldBaseRealization S H sap nr2 (F.closureStructure (R.oldGenerators : Set P)))
    (anchor : SupportedMacroSide S H sap nr2 F (C.root ⟨n,by omega⟩) (C.root ⟨0,by omega⟩)) :
    Fin ((locate 0 R.pruning.pieces).length+1) → WordRequest S :=
  Fin.lastCases (R.anchorRequest D anchor) (R.pieceRequest hUnary cco hC D)

@[simp] theorem wordRequests_piece
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root)
    (D : OldBaseRealization S H sap nr2 (F.closureStructure (R.oldGenerators : Set P)))
    (anchor : SupportedMacroSide S H sap nr2 F (C.root ⟨n,by omega⟩) (C.root ⟨0,by omega⟩))
    (k : R.PieceIndex) :
    R.wordRequests hUnary cco hC D anchor k.castSucc = R.pieceRequest hUnary cco hC D k :=
  Fin.lastCases_castSucc _

@[simp] theorem wordRequests_anchor
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root)
    (D : OldBaseRealization S H sap nr2 (F.closureStructure (R.oldGenerators : Set P)))
    (anchor : SupportedMacroSide S H sap nr2 F (C.root ⟨n,by omega⟩) (C.root ⟨0,by omega⟩)) :
    R.wordRequests hUnary cco hC D anchor (Fin.last _) = R.anchorRequest D anchor :=
  Fin.lastCases_last

theorem wordRequests_inBase
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root)
    (D : OldBaseRealization S H sap nr2 (F.closureStructure (R.oldGenerators : Set P)))
    (anchor : SupportedMacroSide S H sap nr2 F (C.root ⟨n,by omega⟩) (C.root ⟨0,by omega⟩))
    (k : Fin ((locate 0 R.pruning.pieces).length+1)) :
    (R.wordRequests hUnary cco hC D anchor k).InBase S D.base := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [R.wordRequests_anchor]
    exact ⟨D.in_base R.anchorLeft,D.in_base R.anchorRight⟩
  · rw [R.wordRequests_piece]
    exact ⟨D.in_base _,D.in_base _⟩

end SourcePrunedForest

/-- Actual source requests, ONE actual split Hom/base and ONE simultaneous
whole-original-word insertion. No completion, profile, certificate or
splitting provider is a field supplied by the source application. -/
structure SourceReconstructionRequests
    (R : SourcePrunedForest S H sap nr2 F C)
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root)
    (anchor : SupportedMacroSide S H sap nr2 F (C.root ⟨n,by omega⟩) (C.root ⟨0,by omega⟩)) where
  data : OldBaseRealization S H sap nr2 (F.closureStructure (R.oldGenerators : Set P))
  insertion : SimultaneousWords S data.base (R.wordRequests hUnary cco hC data anchor)

theorem source_reconstruction_requests_of_hom
    (R : SourcePrunedForest S H sap nr2 F C)
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (cco : SemanticCCO.{u,v,max u v,w} S) (hC : Function.Injective C.root)
    (anchor : SupportedMacroSide S H sap nr2 F (C.root ⟨n,by omega⟩) (C.root ⟨0,by omega⟩))
    (f : Hom (F.closureStructure (R.oldGenerators : Set P)) (originalPartialTarget S H sap nr2)) :
    Nonempty (SourceReconstructionRequests S H sap nr2 F C R hUnary cco hC anchor) := by
  obtain ⟨D⟩ := oldBaseRealization_of_hom S H sap nr2 _ f
  obtain ⟨out⟩ := simultaneous_word_insertion S H sap D.base
    (R.wordRequests hUnary cco hC D anchor) (R.wordRequests_inBase hUnary cco hC D anchor)
  exact ⟨⟨D,out⟩⟩

namespace SourceReconstructionRequests
variable {S H sap nr2 F C}
variable {R : SourcePrunedForest S H sap nr2 F C}
variable {hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2)}
variable {cco : SemanticCCO.{u,v,max u v,w} S} {hC : Function.Injective C.root}
variable {anchor : SupportedMacroSide S H sap nr2 F (C.root ⟨n,by omega⟩) (C.root ⟨0,by omega⟩)}
variable (out : SourceReconstructionRequests S H sap nr2 F C R hUnary cco hC anchor)

def piece_line (k : R.PieceIndex) :
    FreshWordLine S (R.piecePath (R.indexedPiece k) (R.indexedPiece_mem k)).flatten
      (out.data.point (R.pieceLeft (R.indexedPiece k) (R.indexedPiece_mem k)))
      (out.data.point (R.pieceRight (R.indexedPiece k) (R.indexedPiece_mem k))) out.data.base.vertices := by
  exact Eq.mp (congrArg (fun request : WordRequest S =>
    FreshWordLine S request.word request.source request.target out.data.base.vertices)
    (R.wordRequests_piece hUnary cco hC out.data anchor k)) (out.insertion.line k.castSucc)

def anchor_line : FreshWordLine S anchor.word
    (out.data.point R.anchorLeft) (out.data.point R.anchorRight) out.data.base.vertices := by
  exact Eq.mp (congrArg (fun request : WordRequest S =>
    FreshWordLine S request.word request.source request.target out.data.base.vertices)
    (R.wordRequests_anchor hUnary cco hC out.data anchor)) (out.insertion.line (Fin.last _))

theorem piece_represented (k : R.PieceIndex) :
    PositiveWord.represented S (R.piecePath (R.indexedPiece k) (R.indexedPiece_mem k)).flatten
      (out.data.point (R.pieceLeft (R.indexedPiece k) (R.indexedPiece_mem k)))
      (out.data.point (R.pieceRight (R.indexedPiece k) (R.indexedPiece_mem k))) := by
  let request := R.pieceRequest hUnary cco hC out.data k
  exact CCO.StrongExact.profile_realizes_prescribed_pair_of_SAP S H sap request.word
    request.atom request.profile request.source request.target request.colour

theorem anchor_represented : PositiveWord.represented S anchor.word
    (out.data.point R.anchorLeft) (out.data.point R.anchorRight) := by
  let request := R.anchorRequest out.data anchor
  exact CCO.StrongExact.profile_realizes_prescribed_pair_of_SAP S H sap request.word
    request.atom request.profile request.source request.target request.colour

theorem old_base_subset : out.data.base.vertices ⊆ out.insertion.base.vertices :=
  out.insertion.old_subset

end SourceReconstructionRequests
end
end CCO.OldIdempotentForest
