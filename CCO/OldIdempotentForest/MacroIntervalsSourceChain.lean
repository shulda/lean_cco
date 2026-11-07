import CCO.OldIdempotentForest.MacroIntervalsSource
import CCO.OldIdempotentForest.ForestAdapterComposable

/-! Canonical contiguous subpaths of one actually supported OLD macro
chain. The exact side, its original word and its one complete local model
are retained at each indexed occurrence. -/

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

theorem append_original_assoc {i j k l : ι}
    (first : PositiveWord S i j) (second : PositiveWord S j k) (third : PositiveWord S k l) :
    PositiveWord.append S (PositiveWord.append S first second) third =
      PositiveWord.append S first (PositiveWord.append S second third) := by
  induction first with
  | single a => rfl
  | cons a rest ih => simpa only [PositiveWord.append] using congrArg (PositiveWord.cons a) (ih second)

abbrev TaggedMacroSide := Σ b : P, Σ c : P, SupportedMacroSide S H sap nr2 F b c

namespace SourceMacroPath
variable {S H sap nr2 F} {b c d : P}

def taggedSides : {b c : P} → SourceMacroPath S H sap nr2 F b c →
    List (TaggedMacroSide S H sap nr2 F)
  | _,_,.single side => [⟨_,_,side⟩]
  | _,_,.cons side tail => ⟨_,_,side⟩ :: tail.taggedSides

def castTarget (h : c = d) (path : SourceMacroPath S H sap nr2 F b c) :
    SourceMacroPath S H sap nr2 F b d := by cases h; exact path

@[simp] theorem castTarget_taggedSides (h : c = d)
    (path : SourceMacroPath S H sap nr2 F b c) :
    (path.castTarget h).taggedSides = path.taggedSides := by cases h; rfl

theorem profileLetters_taggedSides (path : SourceMacroPath S H sap nr2 F b c) :
    path.profileLetters = path.taggedSides.map
      (fun side => wordProfile S H sap side.2.2.word) := by
  induction path with
  | single side => rfl
  | cons side tail ih => exact congrArg (List.cons (wordProfile S H sap side.word)) ih

end SourceMacroPath

/-- Actual source sides between successive literal OLD roots. This
contains no completion, holonomy or source-equation callback. -/
structure SupportedMacroChain (n : ℕ) where
  root : Fin (n+1) → P
  side : ∀ k : Fin n, SupportedMacroSide S H sap nr2 F (root k.castSucc) (root k.succ)

namespace SupportedMacroChain
variable {S H sap nr2 F} {n : ℕ} (C : SupportedMacroChain S H sap nr2 F n)

def macroPath : MacroPath S n where
  sort k := gapSort S H sap nr2 F (C.root k)
  word k := (C.side k).word

def taggedSide (k : Fin n) : TaggedMacroSide S H sap nr2 F :=
  ⟨C.root k.castSucc,C.root k.succ,C.side k⟩

def intervalPath (lo hi : ℕ) (hlo : lo < hi) (hhi : hi ≤ n) :
    SourceMacroPath S H sap nr2 F
      (C.root ⟨lo,by omega⟩) (C.root ⟨hi,by omega⟩) := by
  by_cases hOne : lo+1 = hi
  · let path : SourceMacroPath S H sap nr2 F
        (C.root ⟨lo,by omega⟩) (C.root ⟨lo+1,by omega⟩) :=
      .single (C.side ⟨lo,by omega⟩)
    exact path.castTarget (congrArg C.root (Fin.ext hOne))
  · exact .cons (C.side ⟨lo,by omega⟩)
      (intervalPath (lo+1) hi (by omega) hhi)
termination_by hi-lo
decreasing_by omega

theorem intervalPath_flatten_single (lo : ℕ) (hlo : lo < n) :
    (C.intervalPath lo (lo+1) (by omega) (by omega)).flatten = (C.side ⟨lo,hlo⟩).word := by
  rw [intervalPath,dif_pos rfl]
  rfl

theorem intervalPath_flatten_cons (lo hi : ℕ) (hlo : lo+1 < hi) (hhi : hi ≤ n) :
    (C.intervalPath lo hi (by omega) hhi).flatten =
      PositiveWord.append S (C.side ⟨lo,by omega⟩).word
        (C.intervalPath (lo+1) hi hlo hhi).flatten := by
  rw [intervalPath,dif_neg (show ¬lo+1=hi by omega)]
  rfl

/-- Literal recombination of adjacent ORIGINAL intervals. This is
equality of their exact words, not merely equality of strong profiles. -/
theorem intervalPath_flatten_append (lo mid hi : ℕ)
    (hlm : lo < mid) (hmh : mid < hi) (hhi : hi ≤ n) :
    PositiveWord.append S (C.intervalPath lo mid hlm (by omega)).flatten
      (C.intervalPath mid hi hmh hhi).flatten =
        (C.intervalPath lo hi (by omega) hhi).flatten := by
  by_cases hOne : lo+1 = mid
  · subst mid
    rw [C.intervalPath_flatten_single lo (by omega),C.intervalPath_flatten_cons lo hi (by omega) hhi]
  · rw [C.intervalPath_flatten_cons lo mid (by omega) (by omega),
      C.intervalPath_flatten_cons lo hi (by omega) hhi,append_original_assoc]
    exact congrArg (PositiveWord.append S (C.side ⟨lo,by omega⟩).word)
      (intervalPath_flatten_append (lo+1) mid hi (by omega) hmh hhi)
termination_by mid-lo
decreasing_by omega

/-- The chosen source interval is literally the slice of ORIGINAL
side occurrences, including their same actual full local models. -/
theorem intervalPath_taggedSides (lo hi : ℕ) (hlo : lo < hi) (hhi : hi ≤ n) :
    (C.intervalPath lo hi hlo hhi).taggedSides =
      ((((List.finRange n).drop lo).take (hi-lo)).map C.taggedSide) := by
  have hloN : lo < (List.finRange n).length := by simpa using (show lo < n by omega)
  have hget : (List.finRange n)[lo] = (⟨lo,by omega⟩ : Fin n) := by
    apply Fin.ext
    simp only [List.getElem_finRange,Fin.coe_cast,Fin.val_mk]
  rw [List.drop_eq_getElem_cons hloN]
  by_cases hOne : lo+1 = hi
  · have hLen : hi-lo = 1 := by omega
    rw [hLen]
    simp only [List.take_succ_cons,List.take_zero,List.map_cons,List.map_nil]
    rw [intervalPath, dif_pos hOne,SourceMacroPath.castTarget_taggedSides]
    rw [hget]
    rfl
  · have hLen : hi-lo = (hi-(lo+1))+1 := by omega
    rw [hLen,List.take_succ_cons,List.map_cons]
    rw [hget]
    rw [intervalPath,dif_neg hOne]
    change C.taggedSide ⟨lo,by omega⟩ ::
        (C.intervalPath (lo+1) hi (by omega) hhi).taggedSides = _
    rw [intervalPath_taggedSides (lo+1) hi (by omega) hhi]
termination_by hi-lo
decreasing_by omega

theorem intervalPath_profileLetters (lo hi : ℕ) (hlo : lo < hi) (hhi : hi ≤ n) :
    (C.intervalPath lo hi hlo hhi).profileLetters =
      ((((List.finRange n).drop lo).take (hi-lo)).map (C.macroPath.letter H sap)) := by
  rw [SourceMacroPath.profileLetters_taggedSides,C.intervalPath_taggedSides,List.map_map]
  rfl

/-- Evaluation of the located original indices is exactly the strong
profile of the same literal whole old gap word. -/
theorem eval_interval_eq_flatten (lo hi : ℕ) (hlo : lo < hi) (hhi : hi ≤ n) :
    C.macroPath.eval H sap (((List.finRange n).drop lo).take (hi-lo)) =
      .positive (wordProfile S H sap (C.intervalPath lo hi hlo hhi).flatten) := by
  have h := (C.intervalPath lo hi hlo hhi).eval_profileLetters
  rw [C.intervalPath_profileLetters,profileEval_map] at h
  exact h

end SupportedMacroChain
end
end CCO.OldIdempotentForest
