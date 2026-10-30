import CCO.UnaryHN.ObstructionBoundaries.ClassLabels
import PartiteConstruction.Structure.RootedSplit
import Mathlib.Basic.Finite.Sum

/-! Literal shared-root point pushout. Distinct nonroot points from the
two factors remain disjoint; class labels will determine mixed colors. -/
universe u
namespace CCO.UnaryHN.Native.ObstructionBoundaries.NetworkAmalgam
open StructuralRamsey
open StructuralRamsey.Structure

variable {H V W : Type u} {P : Setoid H} {E : Setoid V} {F : Setoid W}

abbrev Carrier (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) :=
  H ⊕ (Rooted.Outside eL ⊕ Rooted.Outside eR)

def leftPointTag {A B C : Type u} : A ⊕ B → A ⊕ (B ⊕ C)
  | .inl r => .inl r
  | .inr a => .inr (.inl a)

def rightPointTag {A B C : Type u} : A ⊕ C → A ⊕ (B ⊕ C)
  | .inl r => .inl r
  | .inr b => .inr (.inr b)

theorem leftPointTag_injective {A B C : Type u} :
    Function.Injective (@leftPointTag A B C) := by
  intro x y h
  cases x <;> cases y <;> simp_all [leftPointTag]

theorem rightPointTag_injective {A B C : Type u} :
    Function.Injective (@rightPointTag A B C) := by
  intro x y h
  cases x <;> cases y <;> simp_all [rightPointTag]

noncomputable def leftPoint (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (a : V) : Carrier eL eR :=
  leftPointTag (Rooted.split eL a)

noncomputable def rightPoint (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (b : W) : Carrier eL eR :=
  rightPointTag (Rooted.split eR b)

theorem leftPoint_injective (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) : Function.Injective (leftPoint eL eR) :=
  leftPointTag_injective.comp (Rooted.splitEquiv eL).injective

theorem rightPoint_injective (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) : Function.Injective (rightPoint eL eR) :=
  rightPointTag_injective.comp (Rooted.splitEquiv eR).injective

theorem leftPoint_root (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (r : H) :
    leftPoint eL eR (eL r) = .inl r := by
  have h := Rooted.split_unsplit eL (Sum.inl r)
  change Rooted.split eL (eL r) = .inl r at h
  unfold leftPoint
  rw [h]
  rfl

theorem rightPoint_root (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (r : H) :
    rightPoint eL eR (eR r) = .inl r := by
  have h := Rooted.split_unsplit eR (Sum.inl r)
  change Rooted.split eR (eR r) = .inl r at h
  unfold rightPoint
  rw [h]
  rfl

theorem point_overlap (eL : Embedding (network P) (network E))
    (eR : Embedding (network P) (network F)) (a : V) (b : W)
    (h : leftPoint eL eR a = rightPoint eL eR b) :
    ∃ r : H, a = eL r ∧ b = eR r := by
  unfold leftPoint rightPoint at h
  cases hl : Rooted.split eL a with
  | inl r =>
    cases hr : Rooted.split eR b with
    | inl s =>
      simp only [hl, hr, leftPointTag, rightPointTag, Sum.inl.injEq] at h
      subst s
      refine ⟨r, ?_, ?_⟩
      · have ha : eL r = a := by simpa only [hl, Rooted.unsplit] using Rooted.unsplit_split eL a
        exact ha.symm
      · have hb : eR r = b := by simpa only [hr, Rooted.unsplit] using Rooted.unsplit_split eR b
        exact hb.symm
    | inr b' => simp [hl, hr, leftPointTag, rightPointTag] at h
  | inr a' =>
    cases hr : Rooted.split eR b with
    | inl s => simp [hl, hr, leftPointTag, rightPointTag] at h
    | inr b' => simp [hl, hr, leftPointTag, rightPointTag] at h

end CCO.UnaryHN.Native.ObstructionBoundaries.NetworkAmalgam
