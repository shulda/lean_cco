import CCO.FullPhaseLift.Full.Frozen
import Mathlib.Tactic.FinCases

/-! The derived complete chosen-pair lift. Its input is the RAW signed A03
interface; neither this lift nor full SAP/homogeneity is a provider premise.
Every distinct chosen pair is named, forcing global output injectivity. -/

universe v w
namespace CCO.FullPhaseLift.Full
open Canonical

def twoPoint {V : Type v} (x y : V) : Fin 2 → V := Fin.cases x (fun _ => y)

theorem twoPoint_comp {V : Type v} {W : Type w} (f : V → W) (x y : V) :
    f ∘ twoPoint x y = twoPoint (f x) (f y) := by
  funext i
  fin_cases i <;> rfl

/-- Structural, automatically proved by the actual canonical FULL pair
names. This merely records an irreflexive named test for each distinct
real pair; it is not a completion/SAP/homogeneity hypothesis. -/
def SeparatesPoints {L : Signature} {M : Type w} (U : BoolTable L M) : Prop :=
  ∀ x y, x ≠ y → ∃ r : Fin L.size, ∃ slots : Fin (L.arity r) → Fin 2,
    U r (twoPoint x y ∘ slots) = true ∧ ∀ z, U r (fun _ => z) = false

def LowEquivalent {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (q p : V → M) : Prop :=
  ∀ r xs, SmallSupport xs → U r (q ∘ xs) = U r (p ∘ xs)

theorem injective_of_lowEquivalent {L : Signature} {M : Type w} {V : Type v}
    (U : BoolTable L M) (sep : SeparatesPoints U) (p : V ↪ M) (q : V → M)
    (h : LowEquivalent U q p) : Function.Injective q := by
  intro a b hab
  by_contra hne
  obtain ⟨r,slots,hr,hd⟩ := sep (p a) (p b) (fun he => hne (p.injective he))
  have hs : SmallSupport (twoPoint a b ∘ slots) :=
    (smallSupport_fin (show 2 ≤ 2 from le_rfl) slots).comp (twoPoint a b)
  have he := h r (twoPoint a b ∘ slots) hs
  have hp : (p : V → M) ∘ (twoPoint a b ∘ slots) = twoPoint (p a) (p b) ∘ slots := by
    funext j
    exact congrFun (twoPoint_comp p a b) (slots j)
  have hq : q ∘ (twoPoint a b ∘ slots) = fun _ => q a := by
    funext j
    have hh := congrFun (twoPoint_comp q a b) (slots j)
    rw [← hab] at hh
    exact hh.trans (by cases slots j using Fin.cases <;> rfl)
  rw [hp,hq,hr,hd] at he
  exact Bool.false_ne_true he

/-- Add every chosen low predicate before applying A03. ALL higher signed
data and every complete frozen factor are unchanged. The full target is
then restricted to the injective image of the ORIGINAL formal vertices. -/
theorem lift_chosen_pairs {L : Signature} {M : Type w}
    (U : BoolTable L M) (sep : SeparatesPoints U) (normal : SupportNormal U)
    (n : ℕ) (D : Partial L (Fin n)) (m : ℕ) (F : Fin m → FrozenFactor U D)
    (covered : HigherCovered F) (p : Fin n ↪ M) (hp : LowRealizes U D p) :
    ∃ q : Fin n ↪ M, Realizes U D q ∧ (∀ j, (F j).FixedBy q) ∧
      LowEquivalent U q p := by
  let D' := augmentLow U D p
  let F' : Fin m → FrozenFactor U D' := fun j => (F j).augment p hp
  have hc : Consistent U D' := augmentLow_consistent U D p
  have hcov : HigherCovered F' := higherCovered_augment F covered p hp
  have hpair : PairCompletion U D' F' := by
    refine ⟨p,?_,?_⟩
    · intro r xs b hs hd
      change augmentLow U D p r xs = some b at hd
      rw [augmentLow_small U D p r xs hs] at hd
      exact Option.some.inj hd
    · intro j
      exact p.injective.comp (F j).inclusion.injective
  obtain ⟨q,hq,hfix⟩ := normal n D' m F' hc hcov hpair
  have hl : LowEquivalent U q p := by
    intro r xs hs
    exact hq r xs _ (augmentLow_small U D p r xs hs)
  let q' : Fin n ↪ M := ⟨q,injective_of_lowEquivalent U sep p q hl⟩
  refine ⟨q',?_,?_,hl⟩
  · intro r xs b hd
    exact hq r xs b (augmentLow_extends U D p hp r xs b hd)
  · intro j
    exact hfix j

end CCO.FullPhaseLift.Full
