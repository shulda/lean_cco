import CCO.GuardedOldSeams.BranchSource
import CCO.GuardedOldSeams.Envelope
import CCO.GuardedOldSeams.LiftOrdered
import CCO.GuardedOldSeams.LiftSplitting
import CCO.StrongExact.ExactConverse
import CCO.UnaryTermsReturn.NamedReturnLoop

/-! Exact ORIGINAL macro words and their SAME locally vetted old models.
The path contains genuine diversity RAW factors, never their reflexive
envelopes or a substitute presentation of a semigroup value. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot
open CCO.UnaryTermsReturn CCO.TransitionClosure CCO.ParityHasse.Original
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.HiddenSAPReadings CCO.TypedOrbitFrames CCO.UnaryFreshFrames
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

abbrev gapSort (b : P) : ι := (F.sort b).down.1

/-- Every side retains its own original word and the selected complete
OLD pair model. No embedding of the ambient partial source is required. -/
structure SupportedMacroSide (b c : P) where
  word : PositiveWord S (gapSort S H sap nr2 F b) (gapSort S H sap nr2 F c)
  distinct : b ≠ c
  joined : (F.closureStructure {b,c}).Irreducible
  model : CCO.UnarySupport.Structure.Embedding
    (F.closureStructure {b,c}) (originalPartialTarget S H sap nr2)
  contains : pairMenu S H sap nr2 (factorRecords S H sap nr2
    ⟨model.point ⟨b,F.subset_closure _ (by simp)⟩,model.sort_eq _⟩
    ⟨model.point ⟨c,F.subset_closure _ (by simp)⟩,model.sort_eq _⟩) ⊆
      PositiveWord.profile S word

namespace SupportedMacroSide
variable {S H sap nr2 F} {b c : P}
variable (side : SupportedMacroSide S H sap nr2 F b c)

def left : (originalCompletedStructure S H sap nr2).Carrier (F.sort b) :=
  ⟨side.model.point ⟨b,F.subset_closure _ (by simp)⟩,side.model.sort_eq _⟩

def right : (originalCompletedStructure S H sap nr2).Carrier (F.sort c) :=
  ⟨side.model.point ⟨c,F.subset_closure _ (by simp)⟩,side.model.sort_eq _⟩

def menu : S.Menu (gapSort S H sap nr2 F b) (gapSort S H sap nr2 F c) :=
  pairMenu S H sap nr2 (factorRecords S H sap nr2 side.left side.right)

theorem menu_nonempty : side.menu.Nonempty := by
  obtain ⟨x,y,a,_,ha⟩ := one_factor_all_comparisons S H sap nr2 _ side.model
    ⟨b,F.subset_closure _ (by simp)⟩ ⟨c,F.subset_closure _ (by simp)⟩
    (fun he => side.distinct (congrArg Subtype.val he))
  exact ⟨a,ha⟩

def letter : QuotientTransport.Letter G X
    (gapSort S H sap nr2 F b) (gapSort S H sap nr2 F c) where
  relation := S.menuRel (PositiveWord.profile S side.word)
  invariant := (originalPositiveStrongBranchRelation S H sap side.word).val.property
  nonempty := (originalPositiveStrongBranchRelation S H sap side.word).property

theorem letter_inside_word {x : X (gapSort S H sap nr2 F b)}
    {y : X (gapSort S H sap nr2 F c)} (h : side.letter.relation x y) :
    PositiveWord.represented S side.word x y := by
  obtain ⟨a,ha,hxy⟩ := h
  exact CCO.StrongExact.profile_realizes_prescribed_pair_of_SAP S H sap side.word a ha x y hxy

/-- Source-derived instance for an ACTUAL original branch of the fixed
same-support theta package, not an arbitrary equation provider. -/
def ofGuardedPackage
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    (tests : BoundedJoinedPairTests S H sap nr2 F)
    (hCover : ∀ i, CCO.TypedOrbitFrames.OriginalAllFullCoversInfinite S (i := i))
    (k : GuardedPair S H sap nr2 F)
    (word : PositiveWord S (gapSort S H sap nr2 F k.val.1) (gapSort S H sap nr2 F k.val.2))
    (hword : word ∈ (guardedPairPackage S H sap nr2 F hUnary tests hCover k).words) :
    SupportedMacroSide S H sap nr2 F k.val.1 k.val.2 where
  word := word
  distinct := k.property.1
  joined := k.property.2
  model := guardedPairEmbedding S H sap nr2 F hUnary tests k
  contains := by
    intro a ha
    have hm := (guardedPairPackage S H sap nr2 F hUnary tests hCover k).menu
    have hPresent : a ∈ CCO.StrongExact.present S
        (guardedPairPackage S H sap nr2 F hUnary tests hCover k).words := hm.symm ▸ ha
    exact hPresent word hword

end SupportedMacroSide

/-- A nonempty literal chain of original source-supported branch words. -/
inductive SourceMacroPath : P → P → Type (max u v w r z)
  | single {b c : P} (side : SupportedMacroSide S H sap nr2 F b c) : SourceMacroPath b c
  | cons {b c d : P} (side : SupportedMacroSide S H sap nr2 F b c)
      (tail : SourceMacroPath c d) : SourceMacroPath b d

namespace SourceMacroPath
variable {S H sap nr2 F} {b c : P}

def flatten : {b c : P} → SourceMacroPath S H sap nr2 F b c →
    PositiveWord S (gapSort S H sap nr2 F b) (gapSort S H sap nr2 F c)
  | _,_,.single side => side.word
  | _,_,.cons side tail => PositiveWord.append S side.word tail.flatten

def rawWord : {b c : P} → SourceMacroPath S H sap nr2 F b c →
    QuotientTransport.Word G X (gapSort S H sap nr2 F b) (gapSort S H sap nr2 F c)
  | _,_,.single side => .cons side.letter (.nil _)
  | _,_,.cons side tail => .cons side.letter tail.rawWord

theorem raw_inside_flatten (path : SourceMacroPath S H sap nr2 F b c)
    (x : X (gapSort S H sap nr2 F b)) (y : X (gapSort S H sap nr2 F c)) :
    path.rawWord.eval x y → PositiveWord.represented S path.flatten x y := by
  induction path with
  | single side =>
    rintro ⟨z,hxz,hzy⟩
    subst z
    exact side.letter_inside_word hxz
  | cons side tail ih =>
    rintro ⟨z,hxz,hzy⟩
    rw [flatten,PositiveWord.represented_append]
    exact ⟨z,side.letter_inside_word hxz,ih z y hzy⟩

theorem flatten_profile_cons {d : P}
    (side : SupportedMacroSide S H sap nr2 F b c)
    (tail : SourceMacroPath S H sap nr2 F c d) :
    PositiveWord.profile S (SourceMacroPath.cons side tail).flatten =
      S.product (PositiveWord.profile S side.word) (PositiveWord.profile S tail.flatten) :=
  PositiveWord.profile_append_of_SAP S H sap side.word tail.flatten

end SourceMacroPath
end
end CCO.OldIdempotentForest
