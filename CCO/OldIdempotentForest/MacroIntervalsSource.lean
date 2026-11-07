import CCO.OldIdempotentForest.MacroIntervals
import CCO.OldIdempotentForest.GapPath

/-! The actual source-supported macro path evaluates its ORIGINAL
atomic concatenation. This adapter keeps side occurrences and all their
local models; no word is selected merely from an equal profile. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.UnarySupport CCO.UnarySupport.Structure
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

namespace SourceMacroPath
variable {S H sap nr2 F} {b c : P}

def profileLetters : {b c : P} → SourceMacroPath S H sap nr2 F b c →
    List (ReachableProfile S)
  | _,_,.single side => [wordProfile S H sap side.word]
  | _,_,.cons side tail => wordProfile S H sap side.word :: tail.profileLetters

theorem profileLetters_ne_nil (path : SourceMacroPath S H sap nr2 F b c) :
    path.profileLetters ≠ [] := by cases path <;> exact List.cons_ne_nil _ _

theorem profileLetters_composable (path : SourceMacroPath S H sap nr2 F b c) :
    path.profileLetters.IsChain ReachableProfile.Compatible := by
  induction path with
  | single side => exact List.IsChain.singleton _
  | cons side tail ih =>
    cases tail with
    | single next => exact List.isChain_cons_cons.mpr ⟨rfl,ih⟩
    | cons next rest => exact List.isChain_cons_cons.mpr ⟨rfl,ih⟩

/-- The same literal recursive flattening used by the OLD gap theorem,
now identified with evaluation in the actual finite typed semigroup. -/
theorem eval_profileLetters (path : SourceMacroPath S H sap nr2 F b c) :
    profileEval S H sap TypedProfileState.positive path.profileLetters =
      .positive (wordProfile S H sap path.flatten) := by
  induction path with
  | single side => rfl
  | cons side tail ih =>
    change profileEval S H sap TypedProfileState.positive
      (wordProfile S H sap side.word :: tail.profileLetters) = _
    rw [profileEval_cons_of_ne S H sap _ _ _ tail.profileLetters_ne_nil,ih]
    rw [profileMul_compatible S H sap (wordProfile S H sap side.word)
      (wordProfile S H sap tail.flatten) rfl,compose_wordProfile]
    rfl

theorem eval_profileLetters_nonzero (path : SourceMacroPath S H sap nr2 F b c) :
    profileEval S H sap TypedProfileState.positive path.profileLetters ≠ .zero := by
  rw [path.eval_profileLetters]
  exact TypedProfileState.positive_ne_zero _

theorem profile_interval_nonzero (path : SourceMacroPath S H sap nr2 F b c)
    (lo hi : ℕ) (hlo : lo < hi) (hhi : hi ≤ path.profileLetters.length) :
    profileEval S H sap TypedProfileState.positive
      ((path.profileLetters.drop lo).take (hi-lo)) ≠ .zero :=
  positive_interval_nonzero S H sap _ path.profileLetters_composable lo hi hlo hhi

end SourceMacroPath
end
end CCO.OldIdempotentForest
