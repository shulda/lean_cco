import CCO.OldIdempotentForest.MacroIntervalsSourceChain
import CCO.OldIdempotentForest.StoppedPruning
import Mathlib.Logic.Function.Basic

/-! Literal recomposition of ORIGINAL source-supported intervals.
Adjacent positive intervals concatenate by equality of their exact words.
No empty word or artificial STRONG identity is used. Actual walks inside
deleted gaps supply their own intermediate points. -/

universe u v w r z a
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.GuardedTwoRoot
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.UnarySupport CCO.UnarySupport.Structure

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)

namespace SupportedMacroChain
variable {S H sap nr2 F} {n : Nat} (C : SupportedMacroChain S H sap nr2 F n)

/-- The two specified boundary points are retained. The exact whole
original interval walk is free to choose every intervening point. -/
def IntervalWalk
    (point : ∀ i : Fin (n + 1), X (gapSort S H sap nr2 F (C.root i)))
    (lo hi : Nat) : Prop :=
  ∃ hlo : lo < hi, ∃ hhi : hi ≤ n,
    PositiveWord.represented S (C.intervalPath lo hi hlo hhi).flatten
      (point ⟨lo,by omega⟩) (point ⟨hi,by omega⟩)

/-- Literal ORIGINAL word concatenation at the same boundary real point. -/
theorem IntervalWalk.append
    {point : ∀ i : Fin (n + 1), X (gapSort S H sap nr2 F (C.root i))}
    {lo mid hi : Nat} (left : C.IntervalWalk point lo mid)
    (right : C.IntervalWalk point mid hi) : C.IntervalWalk point lo hi := by
  obtain ⟨hlm,hmid,hleft⟩ := left
  obtain ⟨hmh,hhi,hright⟩ := right
  refine ⟨Nat.lt_trans hlm hmh,hhi,?_⟩
  rw [← C.intervalPath_flatten_append lo mid hi hlm hmh hhi,
    PositiveWord.represented_append]
  exact ⟨point ⟨mid,by omega⟩,hleft,hright⟩

/-- A nonempty ordered interval partition recomposes the exact original
outer path. A singleton is already the whole path, so no empty semantics
or unit is required in the induction. -/
theorem recompose_original_intervals {A : Type a}
    (point : ∀ i : Fin (n + 1), X (gapSort S H sap nr2 F (C.root i))) :
    ∀ ps : List (Piece A), ps ≠ [] → ∀ start : Nat,
      (∀ q ∈ locate start ps, C.IntervalWalk point q.start q.stop) →
      C.IntervalWalk point start (start + (piecesWord ps).length)
  | [],hne,_,_ => False.elim (hne rfl)
  | first :: rest,_,start,walks => by
      have hfirst : C.IntervalWalk point start (start + first.word.length) :=
        walks ⟨start,first⟩ (by simp [locate])
      cases rest with
      | nil =>
          simpa only [piecesWord_cons,piecesWord_nil,List.append_nil] using hfirst
      | cons second tail =>
          have hrest : C.IntervalWalk point (start + first.word.length)
              (start + first.word.length + (piecesWord (second :: tail)).length) :=
            recompose_original_intervals point (second :: tail) (by simp)
              (start + first.word.length) (fun q hq => walks q (by
                exact List.mem_cons_of_mem _ hq))
          have hwhole := IntervalWalk.append C hfirst hrest
          simpa only [piecesWord_cons,List.length_append,Nat.add_assoc] using hwhole

end SupportedMacroChain

/-- A stopped pruning of the actual macro occurrence word recomposes
the entire ORIGINAL supported path, with its original outer roots. -/
theorem Prunes.recompose_original_path {n : Nat}
    (C : SupportedMacroChain S H sap nr2 F n)
    (point : ∀ i : Fin (n + 1), X (gapSort S H sap nr2 F (C.root i)))
    {tree : FactorizationTree (Fin n)} {pruned : PruningTree (Fin n)}
    (hp : Prunes tree pruned) (hyield : tree.value = List.finRange n)
    (walks : ∀ q ∈ locate 0 pruned.pieces, C.IntervalWalk point q.start q.stop) :
    C.IntervalWalk point 0 n := by
  have hne : pruned.pieces ≠ [] := by
    intro hz
    have hw := pruned.word_ne_nil
    apply hw
    rw [← pruned.pieces_word,hz]
    rfl
  have hwhole := C.recompose_original_intervals point pruned.pieces hne 0 walks
  simpa only [pruned.pieces_word,hp.word,hyield,List.length_finRange,Nat.zero_add] using hwhole

namespace SupportedMacroChain
variable {S H sap nr2 F} {n : Nat} (C : SupportedMacroChain S H sap nr2 F n)

/-- Decompose EACH exact represented interval before gluing different
pieces. Its actual original-side walks retain BOTH prescribed boundary
points; all internal old-root positions receive points from this same
walk, rather than arbitrary preassigned deleted-root representatives. -/
theorem represented_interval_original_sides (C : SupportedMacroChain S H sap nr2 F n)
    (lo hi : Nat) (hlo : lo < hi) (hhi : hi ≤ n)
    (x : X (gapSort S H sap nr2 F (C.root ⟨lo,by omega⟩)))
    (y : X (gapSort S H sap nr2 F (C.root ⟨hi,by omega⟩)))
    (hw : PositiveWord.represented S (C.intervalPath lo hi hlo hhi).flatten x y) :
    ∃ point : ∀ k : Fin (n + 1), X (gapSort S H sap nr2 F (C.root k)),
      point ⟨lo,by omega⟩ = x ∧ point ⟨hi,by omega⟩ = y ∧
        ∀ k : Fin n, lo ≤ k.val → k.val < hi →
          PositiveWord.represented S (C.side k).word (point k.castSucc) (point k.succ) := by
  classical
  let initial : Fin (n + 1) := ⟨lo,by omega⟩
  let final : Fin (n + 1) := ⟨hi,by omega⟩
  let firstSide : Fin n := ⟨lo,by omega⟩
  have hif : initial ≠ final := by
    intro heq
    have hval := congrArg Fin.val heq
    dsimp [initial,final] at hval
    omega
  by_cases hone : lo + 1 = hi
  · subst hi
    rw [C.intervalPath_flatten_single lo (by omega)] at hw
    let base : ∀ k : Fin (n + 1), X (gapSort S H sap nr2 F (C.root k)) :=
      fun k => Classical.choice (S.nonemptySort _)
    let point := Function.update (Function.update base initial x) final y
    have hleft : point initial = x := by
      simp only [point,Function.update_of_ne hif,Function.update_self]
    have hright : point final = y := Function.update_self _ _ _
    refine ⟨point,hleft,hright,?_⟩
    intro k hk0 hk1
    have hkeq : k = firstSide := by
      apply Fin.ext
      change k.val = lo
      omega
    subst k
    change PositiveWord.represented S (C.side ⟨lo,by omega⟩).word
      (point initial) (point final)
    rw [hleft,hright]
    exact hw
  · have hnext : lo + 1 < hi := by omega
    rw [C.intervalPath_flatten_cons lo hi hnext hhi,PositiveWord.represented_append] at hw
    obtain ⟨middle,hfirst,htail⟩ := hw
    obtain ⟨tailPoint,htailFirst,htailLast,htailSides⟩ :=
      represented_interval_original_sides C (lo + 1) hi hnext hhi middle y htail
    let point := Function.update tailPoint initial x
    have hleft : point initial = x := Function.update_self _ _ _
    have hright : point final = y := by
      simpa only [point,Function.update_of_ne (Ne.symm hif)] using htailLast
    refine ⟨point,hleft,hright,?_⟩
    intro k hk0 hk1
    by_cases hke : k.val = lo
    · have hkeq : k = firstSide := Fin.ext hke
      subst k
      have hne : (⟨lo + 1,by omega⟩ : Fin (n + 1)) ≠ initial := by
        intro heq
        have hval := congrArg Fin.val heq
        dsimp [initial] at hval
        omega
      have hpnext : point ⟨lo + 1,by omega⟩ = middle := by
        simpa only [point,Function.update_of_ne hne] using htailFirst
      change PositiveWord.represented S (C.side ⟨lo,by omega⟩).word
        (point initial) (point ⟨lo + 1,by omega⟩)
      rw [hleft,hpnext]
      exact hfirst
    · have hkNext : lo + 1 ≤ k.val := by omega
      have hcast : k.castSucc ≠ initial := by
        intro heq
        have hval := congrArg Fin.val heq
        change k.val = lo at hval
        omega
      have hsucc : k.succ ≠ initial := by
        intro heq
        have hval := congrArg Fin.val heq
        change k.val + 1 = lo at hval
        omega
      simpa only [point,Function.update_of_ne hcast,Function.update_of_ne hsucc]
        using htailSides k hkNext hk1
termination_by hi - lo
decreasing_by omega

end SupportedMacroChain

end CCO.OldIdempotentForest
