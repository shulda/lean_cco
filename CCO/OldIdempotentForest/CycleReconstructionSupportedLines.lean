import CCO.OldIdempotentForest.SupportedCycle
import CCO.OldIdempotentForest.CycleReconstructionWordLines

/-! Actual supported original-word walks give typed point families on
their derived original cycle arcs. Backwards traversal uses the literal
reversed word of the SAME branch, then its proved converse semantics;
no same-profile presentation or new old support is selected. -/

universe u v w r z
namespace CCO.OldIdempotentForest

open CCO.GuardedOldSeams CCO.GuardedTwoRoot CCO.StrongExact
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.HiddenSAPReadings
open CCO.UnarySupport CCO.UnarySupport.Structure
open CycleGeometry
noncomputable section

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

/-- Literal reversal of an ORIGINAL positive atomic word reverses its
represented relation. This uses only actual original atomic converses. -/
theorem represented_reverse_original_iff {i j : ι} (word : PositiveWord S i j)
    (x : X j) (y : X i) :
    PositiveWord.represented S (reverseWord S word) x y ↔
      PositiveWord.represented S word y x := by
  induction word with
  | single a => exact (S.colour_swap y x a).symm
  | cons a tail ih =>
    change PositiveWord.represented S
      (PositiveWord.append S (reverseWord S tail) (.single (S.conv a))) x y ↔
      PositiveWord.represented S (.cons a tail) y x
    rw [PositiveWord.represented_append]
    change (∃ middle, PositiveWord.represented S (reverseWord S tail) x middle ∧
      S.colour middle y = some (S.conv a)) ↔
      ∃ middle, S.colour y middle = some a ∧ PositiveWord.represented S tail middle x
    constructor
    · rintro ⟨middle,htail,hfirst⟩
      exact ⟨middle,(S.colour_swap y middle a).mpr hfirst,(ih x middle).mp htail⟩
    · rintro ⟨middle,hfirst,htail⟩
      exact ⟨middle,(ih x middle).mpr htail,(S.colour_swap y middle a).mp hfirst⟩

private theorem represented_heq_word {i j i' j' : ι}
    (hi : i = i') (hj : j = j')
    (word : PositiveWord S i j) (word' : PositiveWord S i' j')
    (hword : HEq word word') (x : X i) (y : X j)
    (h : PositiveWord.represented S word x y) :
    PositiveWord.represented S word' (hi ▸ x) (hj ▸ y) := by
  cases hi
  cases hj
  have heq : word = word' := eq_of_heq hword
  cases heq
  exact h

private theorem sigma_transport {i j : ι} (h : i = j) (x : X i) :
    (⟨j,h ▸ x⟩ : Sigma X) = ⟨i,x⟩ := by
  cases h
  rfl

variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
variable {P : Type z} [Finite P]
variable (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
variable (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
variable (tests : BoundedJoinedPairTests S H sap nr2 F)
variable (hCover : ∀ i, OriginalAllFullCoversInfinite S (i := i))

local notation "actualR" => typedRootWordSystem S H sap nr2 F hUnary tests hCover
local notation "actualP" => RootWordGeometry.privateBranchSystem actualR

structure SupportedArcPoints (Q : RootFreePath actualP) (T : Q.OriginalBranchTraversal)
    (x : X (gapSort S H sap nr2 F Q.left)) (y : X (gapSort S H sap nr2 F Q.right)) where
  point : ∀ d : Fin (Q.length+1), X ((actualR).vertexSort (Q.vertex d))
  first_image :
    (⟨(actualR).vertexSort (Q.vertex 0),point 0⟩ : Sigma X) =
      ⟨gapSort S H sap nr2 F Q.left,x⟩
  last_image :
    (⟨(actualR).vertexSort (Q.vertex (Fin.last Q.length)),point (Fin.last Q.length)⟩ : Sigma X) =
      ⟨gapSort S H sap nr2 F Q.right,y⟩
  preserves_step : ∀ (d : Fin Q.length) (hne : Q.vertex d.castSucc ≠ Q.vertex d.succ)
    (a : S.Atom ((actualR).vertexSort (Q.vertex d.castSucc))
      ((actualR).vertexSort (Q.vertex d.succ))),
    (G_typ S H sap nr2 F hUnary tests hCover).edge (Q.vertex d.castSucc) (Q.vertex d.succ) hne = some a →
      S.colour (point d.castSucc) (point d.succ) = some a

/-- The exact supported ORIGINAL word, with its recorded traversal
orientation, realizes every stored old atom on this actual cycle arc. -/
theorem supported_arc_points (Q : RootFreePath actualP) (T : Q.OriginalBranchTraversal)
    (x : X (gapSort S H sap nr2 F Q.left)) (y : X (gapSort S H sap nr2 F Q.right))
    (h : PositiveWord.represented S
      (supportedSideOfTraversal S H sap nr2 F hUnary tests hCover Q T).word x y) :
    Nonempty (SupportedArcPoints S H sap nr2 F hUnary tests hCover Q T x y) := by
  classical
  let word := RootWordGeometry.branchWord actualR T.branch
  have hlength : Q.length = TypedPrefix.length S word := T.length_eq
  by_cases hf : T.forward = true
  · have hl : Q.left = (actualR).left T.branch.1 := by
      have he : Q.left = if T.forward then (actualR).left T.branch.1 else (actualR).right T.branch.1 := T.left_eq
      simpa [hf] using he
    have hr : Q.right = (actualR).right T.branch.1 := by
      have he : Q.right = if T.forward then (actualR).right T.branch.1 else (actualR).left T.branch.1 := T.right_eq
      simpa [hf] using he
    have hi : gapSort S H sap nr2 F Q.left = (actualR).sort ((actualR).left T.branch.1) :=
      congrArg (gapSort S H sap nr2 F) hl
    have hj : gapSort S H sap nr2 F Q.right = (actualR).sort ((actualR).right T.branch.1) :=
      congrArg (gapSort S H sap nr2 F) hr
    let x' : X ((actualR).sort ((actualR).left T.branch.1)) := hi ▸ x
    let y' : X ((actualR).sort ((actualR).right T.branch.1)) := hj ▸ y
    have hw : PositiveWord.represented S word x' y' :=
      represented_heq_word S hi hj _ word
        (supportedSideOfTraversal_word_forward S H sap nr2 F hUnary tests hCover Q T hf) x y h
    let line := LiteralLine.of_represented S word x' y' hw
    have hfirst : T.position 0 = 0 := by
      apply Fin.ext
      have hp := T.rank (0 : Fin (Q.length+1))
      simpa [hf] using hp
    have hlast : T.position (Fin.last Q.length) = Fin.last (TypedPrefix.length S word) := by
      apply Fin.ext
      have hp := T.rank (Fin.last Q.length)
      have hrank : (T.position (Fin.last Q.length)).val = Q.length := by simpa [hf] using hp
      change (T.position (Fin.last Q.length)).val = TypedPrefix.length S word
      omega
    refine ⟨{
      point := RootWordGeometry.traversalLinePoint T line
      first_image := ?_
      last_image := ?_
      preserves_step := ?_ }⟩
    · have hp := RootWordGeometry.traversalLinePoint_image T line 0
      rw [hfirst] at hp
      exact hp.trans ((RootWordGeometry.branchLinePoint_first_image actualR T.branch line).trans
        (sigma_transport hi x))
    · have hp := RootWordGeometry.traversalLinePoint_image T line (Fin.last Q.length)
      rw [hlast] at hp
      exact hp.trans ((RootWordGeometry.branchLinePoint_last_image actualR T.branch line).trans
        (sigma_transport hj y))
    · exact RootWordGeometry.traversalLine_preserves_step
        (typedRootWordSeeds S H sap nr2 F hUnary tests hCover) T line
  · have hfalse : T.forward = false := by cases hb : T.forward <;> simp_all
    have hl : Q.left = (actualR).right T.branch.1 := by
      have he : Q.left = if T.forward then (actualR).left T.branch.1 else (actualR).right T.branch.1 := T.left_eq
      simpa [hfalse] using he
    have hr : Q.right = (actualR).left T.branch.1 := by
      have he : Q.right = if T.forward then (actualR).right T.branch.1 else (actualR).left T.branch.1 := T.right_eq
      simpa [hfalse] using he
    have hi : gapSort S H sap nr2 F Q.left = (actualR).sort ((actualR).right T.branch.1) :=
      congrArg (gapSort S H sap nr2 F) hl
    have hj : gapSort S H sap nr2 F Q.right = (actualR).sort ((actualR).left T.branch.1) :=
      congrArg (gapSort S H sap nr2 F) hr
    let x' : X ((actualR).sort ((actualR).right T.branch.1)) := hi ▸ x
    let y' : X ((actualR).sort ((actualR).left T.branch.1)) := hj ▸ y
    have hwreverse : PositiveWord.represented S (reverseWord S word) x' y' :=
      represented_heq_word S hi hj _ (reverseWord S word)
        (supportedSideOfTraversal_word_reverse S H sap nr2 F hUnary tests hCover Q T hfalse) x y h
    have hw : PositiveWord.represented S word y' x' :=
      (represented_reverse_original_iff S word x' y').mp hwreverse
    let line := LiteralLine.of_represented S word y' x' hw
    have hfirst : T.position 0 = Fin.last (TypedPrefix.length S word) := by
      apply Fin.ext
      have hp : (T.position (0 : Fin (Q.length+1))).val =
          if T.forward then 0 else TypedPrefix.length S word := T.rank 0
      simpa [hfalse] using hp
    have hlast : T.position (Fin.last Q.length) = 0 := by
      apply Fin.ext
      have hp : (T.position (Fin.last Q.length)).val =
          if T.forward then Q.length else TypedPrefix.length S word-Q.length := T.rank (Fin.last Q.length)
      have hrank : (T.position (Fin.last Q.length)).val = TypedPrefix.length S word - Q.length :=
        by simpa [hfalse] using hp
      change (T.position (Fin.last Q.length)).val = 0
      omega
    refine ⟨{
      point := RootWordGeometry.traversalLinePoint T line
      first_image := ?_
      last_image := ?_
      preserves_step := ?_ }⟩
    · have hp := RootWordGeometry.traversalLinePoint_image T line 0
      rw [hfirst] at hp
      exact hp.trans ((RootWordGeometry.branchLinePoint_last_image actualR T.branch line).trans
        (sigma_transport hi x))
    · have hp := RootWordGeometry.traversalLinePoint_image T line (Fin.last Q.length)
      rw [hlast] at hp
      exact hp.trans ((RootWordGeometry.branchLinePoint_first_image actualR T.branch line).trans
        (sigma_transport hj y))
    · exact RootWordGeometry.traversalLine_preserves_step
        (typedRootWordSeeds S H sap nr2 F hUnary tests hCover) T line

end
end CCO.OldIdempotentForest
