import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin

/-! Actual strict-total order and within-fibre order constructors. -/
universe u v
namespace CCO.ResetOrder.Hierarchy

structure TotalOrder (X : Type u) where
  lt : X → X → Prop
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ {x y z}, lt x y → lt y z → lt x z
  total : ∀ {x y}, x ≠ y → lt x y ∨ lt y x

namespace TotalOrder
@[ext] theorem ext {X : Type u} {a b : TotalOrder X}
    (h : ∀ x y, a.lt x y ↔ b.lt x y) : a = b := by
  cases a; cases b
  congr
  funext x y
  exact propext (h x y)

theorem asymm {X : Type u} (o : TotalOrder X) {x y : X}
    (h : o.lt x y) : ¬ o.lt y x := fun h' => o.irrefl x (o.trans h h')

def reverse {X : Type u} (o : TotalOrder X) : TotalOrder X where
  lt x y := o.lt y x
  irrefl := o.irrefl
  trans h h' := o.trans h' h
  total h := (o.total h).symm

theorem reverse_reverse {X : Type u} (o : TotalOrder X) : o.reverse.reverse = o := by
  apply ext
  intro x y
  rfl

def pullback {X : Type u} {Y : Type v} (o : TotalOrder Y)
    (f : X → Y) (hf : Function.Injective f) : TotalOrder X where
  lt x y := o.lt (f x) (f y)
  irrefl x := o.irrefl (f x)
  trans := o.trans
  total h := o.total (fun e => h (hf e))
end TotalOrder

structure FibreOrder {X : Type u} (E : X → X → Prop) where
  lt : X → X → Prop
  same : ∀ {x y}, lt x y → E x y
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ {x y z}, lt x y → lt y z → lt x z
  total : ∀ {x y}, E x y → x ≠ y → lt x y ∨ lt y x

namespace FibreOrder
@[ext] theorem ext {X : Type u} {E : X → X → Prop} {a b : FibreOrder E}
    (h : ∀ x y, a.lt x y ↔ b.lt x y) : a = b := by
  cases a; cases b
  congr
  funext x y
  exact propext (h x y)

def restrict {X : Type u} (o : TotalOrder X) (E : X → X → Prop)
    (hE : ∀ {x y z}, E x y → E y z → E x z)
    (hEs : ∀ {x y}, E x y → E y x) : FibreOrder E where
  lt x y := E x y ∧ o.lt x y
  same h := h.1
  irrefl x h := o.irrefl x h.2
  trans h h' := ⟨hE h.1 h'.1, o.trans h.2 h'.2⟩
  total he h := (o.total h).imp (fun hxy => ⟨he, hxy⟩) (fun hyx => ⟨hEs he, hyx⟩)

def reverse {X : Type u} {E : X → X → Prop} (o : FibreOrder E)
    (hEs : ∀ {x y}, E x y → E y x) : FibreOrder E where
  lt x y := o.lt y x
  same h := hEs (o.same h)
  irrefl := o.irrefl
  trans h h' := o.trans h' h
  total he h := o.total (hEs he) (Ne.symm h)

def changeFibre {X : Type u} {E F : X → X → Prop} (o : FibreOrder E)
    (h : ∀ x y, E x y ↔ F x y) : FibreOrder F where
  lt := o.lt
  same hxy := (h _ _).1 (o.same hxy)
  irrefl := o.irrefl
  trans := o.trans
  total he hxy := o.total ((h _ _).2 he) hxy
end FibreOrder

def fibreLex {X : Type u} {Y : Type v} (key : X → Y) (o : TotalOrder Y)
    (t : FibreOrder (fun x y => key x = key y)) : TotalOrder X where
  lt x y := o.lt (key x) (key y) ∨ (key x = key y ∧ t.lt x y)
  irrefl x := by
    rintro (h | ⟨_, h⟩)
    · exact o.irrefl _ h
    · exact t.irrefl _ h
  trans := by
    intro x y z h h'
    rcases h with h | ⟨he, ht⟩ <;> rcases h' with h' | ⟨he', ht'⟩
    · exact Or.inl (o.trans h h')
    · exact Or.inl (he' ▸ h)
    · exact Or.inl (he.symm ▸ h')
    · exact Or.inr ⟨he.trans he', t.trans ht ht'⟩
  total := by
    intro x y hxy
    by_cases hk : key x = key y
    · exact (t.total hk hxy).imp (fun h => Or.inr ⟨hk, h⟩)
        (fun h => Or.inr ⟨hk.symm, h⟩)
    · exact (o.total hk).imp Or.inl Or.inl

theorem fibreLex_same {X : Type u} {Y : Type v} (key : X → Y) (o : TotalOrder Y)
    (t : FibreOrder (fun x y => key x = key y)) {x y : X} (h : key x = key y) :
    (fibreLex key o t).lt x y ↔ t.lt x y := by
  constructor
  · rintro (hlt | ⟨_, hlt⟩)
    · exact False.elim (o.irrefl (key y) (h ▸ hlt))
    · exact hlt
  · exact fun hlt => Or.inr ⟨h, hlt⟩

def KeyLex {n : ℕ} {Y : Fin n → Type u} (o : ∀ i, TotalOrder (Y i))
    (x y : ∀ i, Y i) : Prop :=
  ∃ i, (∀ j, j < i → x j = y j) ∧ (o i).lt (x i) (y i)

theorem keyLex_irrefl {n : ℕ} {Y : Fin n → Type u} (o : ∀ i, TotalOrder (Y i))
    (x : ∀ i, Y i) : ¬ KeyLex o x x := by
  rintro ⟨i, _, h⟩
  exact (o i).irrefl _ h

theorem keyLex_trans {n : ℕ} {Y : Fin n → Type u} (o : ∀ i, TotalOrder (Y i))
    {x y z : ∀ i, Y i} (h : KeyLex o x y) (h' : KeyLex o y z) : KeyLex o x z := by
  obtain ⟨i, hi, hlt⟩ := h
  obtain ⟨j, hj, hlt'⟩ := h'
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact ⟨i, fun k hk => (hi k hk).trans (hj k (hk.trans hij)), (hj i hij) ▸ hlt⟩
  · exact ⟨i, fun k hk => (hi k hk).trans (hj k hk), (o i).trans hlt hlt'⟩
  · exact ⟨j, fun k hk => (hi k (hk.trans hji)).trans (hj k hk), (hi j hji).symm ▸ hlt'⟩

theorem keyLex_total {n : ℕ} {Y : Fin n → Type u} (o : ∀ i, TotalOrder (Y i))
    {x y : ∀ i, Y i} (hne : x ≠ y) : KeyLex o x y ∨ KeyLex o y x := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ y i)
  have hs : s.Nonempty := by
    by_contra hempty
    apply hne
    funext i
    by_contra hi
    exact hempty ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let i := s.min' hs
  have hi : x i ≠ y i := (Finset.mem_filter.1 (Finset.min'_mem s hs)).2
  have before : ∀ j, j < i → x j = y j := by
    intro j hj
    by_contra hj'
    have hmem : j ∈ s := Finset.mem_filter.2 ⟨Finset.mem_univ _, hj'⟩
    exact (not_le_of_gt hj) (Finset.min'_le s j hmem)
  exact ((o i).total hi).imp (fun h => ⟨i, before, h⟩)
    (fun h => ⟨i, fun j hj => (before j hj).symm, h⟩)

def keyOrder {n : ℕ} {Y : Fin n → Type u} (o : ∀ i, TotalOrder (Y i)) : TotalOrder (∀ i, Y i) where
  lt := KeyLex o
  irrefl := keyLex_irrefl o
  trans := keyLex_trans o
  total := keyLex_total o
end CCO.ResetOrder.Hierarchy
