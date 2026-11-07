import CCO.GuardedTwoRoot.G1OldSAP
import CCO.ParityHasse.Original.RelativeIndices
import Mathlib.Data.Fintype.Card

/-! The actual finite-index cut in the G1 diagnostic. K is same block
AND bit; J is same block. They are FULL old colour-invariant equivalences.
Inside EVERY J class, the actual K quotient is literally equivalent to
Bool, with finiteness proved separately from its cardinal. -/

namespace CCO.GuardedTwoRoot.G1
open CCO.ParityHasse.Original
noncomputable section

def fineSetoid : Setoid Real := Setoid.ker (fun x : Real => (block x,bit x))
def coarseSetoid : Setoid Real := Setoid.ker block

def fineColourEq : ColourEq source () := ⟨fineSetoid,by
  intro x y x' y' h
  change (block x,bit x) = (block y,bit y) ↔ (block x',bit x') = (block y',bit y')
  simpa only [Prod.mk.injEq] using fine_of_colour h⟩

def coarseColourEq : ColourEq source () := ⟨coarseSetoid,by
  intro x y x' y' h
  exact block_of_colour h⟩

/-- The true relative quotient is classified by the two actual bit
values, not by an assumed finite-index or an abstract cardinal provider. -/
def relativeBitEquiv (a : Real) : RelativeClass fineSetoid coarseSetoid a ≃ Bool where
  toFun := Quotient.lift (fun x : {x : Real // coarseSetoid a x} => bit x.val)
    (by
      intro x y h
      change (block x.val,bit x.val) = (block y.val,bit y.val) at h
      exact congrArg Prod.snd h)
  invFun b := Quotient.mk _ ⟨((block a,b),0),rfl⟩
  left_inv t := by
    induction t using Quotient.inductionOn with
    | _ x =>
      apply Quotient.sound
      change (block a,bit x.val) = (block x.val,bit x.val)
      exact Prod.ext x.property rfl
  right_inv _ := rfl

instance relativeClass_finite (a : Real) : Finite (RelativeClass fineSetoid coarseSetoid a) :=
  Finite.of_injective (relativeBitEquiv a) (relativeBitEquiv a).injective

/-- The literal relative index [J:K] is two in EVERY original block. -/
theorem coarse_fine_relative_index (a : Real) : relativeIndex fineSetoid coarseSetoid a = 2 := by
  change Nat.card (RelativeClass fineSetoid coarseSetoid a) = 2
  exact (Nat.card_congr (relativeBitEquiv a)).trans (by
    rw [Nat.card_eq_fintype_card,Fintype.card_bool])

theorem fine_le_coarse : fineColourEq ≤ coarseColourEq := by
  intro x y h
  exact congrArg Prod.fst h

theorem bot_lt_fine : (⊥ : ColourEq source ()) < fineColourEq := by
  refine lt_iff_le_not_ge.mpr ⟨bot_le,?_⟩
  intro h
  have he : (⊥ : ColourEq source ()) ((0,false),0) ((0,false),1) :=
    h (show fineColourEq ((0,false),0) ((0,false),1) from rfl)
  change (((0,false),0) : Real) = ((0,false),1) at he
  cases he

theorem fine_lt_coarse : fineColourEq < coarseColourEq := by
  refine lt_iff_le_not_ge.mpr ⟨fine_le_coarse,?_⟩
  intro h
  have he : fineColourEq ((0,false),0) ((0,true),0) :=
    h (show coarseColourEq ((0,false),0) ((0,true),0) from rfl)
  change ((0,false) : ℕ × Bool) = (0,true) at he
  cases he

theorem coarse_lt_top : coarseColourEq < (⊤ : ColourEq source ()) := by
  refine lt_iff_le_not_ge.mpr ⟨le_top,?_⟩
  intro h
  have he : coarseColourEq ((0,false),0) ((1,false),0) :=
    h (show (⊤ : ColourEq source ()) ((0,false),0) ((1,false),0) from trivial)
  change (0 : ℕ) = 1 at he
  cases he

/-- This is a cover in the FULL original invariant-equivalence poset. -/
theorem fine_covby_coarse : fineColourEq ⋖ coarseColourEq :=
  covBy_of_relativeIndex_two source homogeneous fineColourEq coarseColourEq
    fine_le_coarse ((0,false),0) (coarse_fine_relative_index _)

end
end CCO.GuardedTwoRoot.G1
