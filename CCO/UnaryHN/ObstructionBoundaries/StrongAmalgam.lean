import CCO.UnaryHN.ObstructionBoundaries.AmalgamPoints

/-! Actual finite strong amalgamation of equivalence-colored networks.
The carrier is the shared-root point pushout and the equivalence relation
is the kernel of conservative root/left/right quotient-class labels. -/
universe u
namespace CCO.UnaryHN.Native.ObstructionBoundaries.NetworkAmalgam
open StructuralRamsey
open StructuralRamsey.Structure

variable {H V W : Type u} {P : Setoid H} {E : Setoid V} {F : Setoid W}

abbrev Labels (P : Setoid H) (E : Setoid V) (F : Setoid W) :=
  AmalgamLabel (Quotient P) (Quotient E) (Quotient F)

noncomputable def leftClassLabel (eL : Embedding (network P) (network E))
    (_eR : Embedding (network P) (network F)) (a : V) : Labels P E F :=
  leftLabelMap (classLabel P E eL a)

noncomputable def rightClassLabel (_eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (b : W) : Labels P E F :=
  rightLabelMap (classLabel P F eR b)

theorem leftClassLabel_eq_iff (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (a b : V) :
    leftClassLabel eL eR a = leftClassLabel eL eR b ↔ E.r a b := by
  constructor
  · intro h
    exact (classLabel_eq_iff P E eL (embedding_equivalence_iff eL) a b).mp
      (leftLabelMap_injective h)
  · intro h
    exact congrArg leftLabelMap
      ((classLabel_eq_iff P E eL (embedding_equivalence_iff eL) a b).mpr h)

theorem rightClassLabel_eq_iff (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (a b : W) :
    rightClassLabel eL eR a = rightClassLabel eL eR b ↔ F.r a b := by
  constructor
  · intro h
    exact (classLabel_eq_iff P F eR (embedding_equivalence_iff eR) a b).mp
      (rightLabelMap_injective h)
  · intro h
    exact congrArg rightLabelMap
      ((classLabel_eq_iff P F eR (embedding_equivalence_iff eR) a b).mpr h)

theorem leftClassLabel_root (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (r : H) :
    leftClassLabel eL eR (eL r) = .root (Quotient.mk P r) := by
  unfold leftClassLabel
  rw [classLabel_root P E eL (embedding_equivalence_iff eL) r]
  rfl

theorem rightClassLabel_root (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (r : H) :
    rightClassLabel eL eR (eR r) = .root (Quotient.mk P r) := by
  unfold rightClassLabel
  rw [classLabel_root P F eR (embedding_equivalence_iff eR) r]
  rfl

noncomputable def vertexLabel (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) : Carrier eL eR → Labels P E F
  | .inl r => .root (Quotient.mk P r)
  | .inr (.inl a) => leftClassLabel eL eR a.val
  | .inr (.inr b) => rightClassLabel eL eR b.val

theorem vertexLabel_left (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (a : V) :
    vertexLabel eL eR (leftPoint eL eR a) = leftClassLabel eL eR a := by
  unfold leftPoint
  cases hs : Rooted.split eL a with
  | inl r =>
    change AmalgamLabel.root (Quotient.mk P r) = leftClassLabel eL eR a
    have ha : eL r = a := by simpa only [hs, Rooted.unsplit] using Rooted.unsplit_split eL a
    rw [← ha, leftClassLabel_root]
  | inr a' =>
    change leftClassLabel eL eR a'.val = leftClassLabel eL eR a
    apply congrArg (leftClassLabel eL eR)
    simpa only [hs, Rooted.unsplit] using Rooted.unsplit_split eL a

theorem vertexLabel_right (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (b : W) :
    vertexLabel eL eR (rightPoint eL eR b) = rightClassLabel eL eR b := by
  unfold rightPoint
  cases hs : Rooted.split eR b with
  | inl r =>
    change AmalgamLabel.root (Quotient.mk P r) = rightClassLabel eL eR b
    have hb : eR r = b := by simpa only [hs, Rooted.unsplit] using Rooted.unsplit_split eR b
    rw [← hb, rightClassLabel_root]
  | inr b' =>
    change rightClassLabel eL eR b'.val = rightClassLabel eL eR b
    apply congrArg (rightClassLabel eL eR)
    simpa only [hs, Rooted.unsplit] using Rooted.unsplit_split eR b

def embeddingOfLabels {A B Q : Type u} (E : Setoid A) (label : B → Q)
    (f : A → B) (hf : Function.Injective f)
    (hLabel : ∀ a b, label (f a) = label (f b) ↔ E.r a b) :
    Embedding (network E) (network (Setoid.ker label)) where
  toFun := f
  injective := hf
  map_rel_iff := by
    intro color xs
    cases color
    · change (label (f (xs 0)) = label (f (xs 1)) ∧ f (xs 0) ≠ f (xs 1)) ↔
        E.r (xs 0) (xs 1) ∧ xs 0 ≠ xs 1
      exact and_congr (hLabel _ _) hf.ne_iff
    · change (¬ label (f (xs 0)) = label (f (xs 1))) ↔ ¬ E.r (xs 0) (xs 1)
      exact not_congr (hLabel _ _)
  map_func F := Empty.elim F

noncomputable def leftEmbedding (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) :
    Embedding (network E) (network (Setoid.ker (vertexLabel eL eR))) :=
  embeddingOfLabels E (vertexLabel eL eR) (leftPoint eL eR) (leftPoint_injective eL eR)
    (fun a b => by rw [vertexLabel_left, vertexLabel_left]; exact leftClassLabel_eq_iff eL eR a b)

noncomputable def rightEmbedding (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) :
    Embedding (network F) (network (Setoid.ker (vertexLabel eL eR))) :=
  embeddingOfLabels F (vertexLabel eL eR) (rightPoint eL eR) (rightPoint_injective eL eR)
    (fun a b => by rw [vertexLabel_right, vertexLabel_right]; exact rightClassLabel_eq_iff eL eR a b)

end CCO.UnaryHN.Native.ObstructionBoundaries.NetworkAmalgam

namespace CCO.UnaryHN.Native.ObstructionBoundaries
open StructuralRamsey
open StructuralRamsey.Structure
open NetworkAmalgam

/-- Actual finite SAP, including empty common bases and all original points.
Mixed equivalence classes are defined by the conservative quotient labels. -/
theorem completed_finiteHereditarySAP : FiniteHereditarySAP (completed.{u}) where
  finite C hC := hC.1
  singleton C _ := singleton C
  hereditary := completed_hereditary
  strong := by
    intro H V W Root Left Right hLeft hRight eL eR
    have hRoot := completed_hereditary hLeft eL
    obtain ⟨hH, P, rfl⟩ := hRoot
    obtain ⟨hV, E, rfl⟩ := hLeft
    obtain ⟨hW, F, rfl⟩ := hRight
    letI : Finite H := hH
    letI : Finite V := hV
    letI : Finite W := hW
    refine ⟨Carrier eL eR, inferInstance, network (Setoid.ker (vertexLabel eL eR)),
      completed_network _, leftEmbedding eL eR, rightEmbedding eL eR, ?_, ?_⟩
    · intro r
      exact (leftPoint_root eL eR r).trans (rightPoint_root eL eR r).symm
    · exact point_overlap eL eR

end CCO.UnaryHN.Native.ObstructionBoundaries
