/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/

/- CCO compatibility port, 6 November 2026.
Adapted from ReemMelamed/algebraic-automata at
0acb244aaa913c32eeeff48e939cb5df469a3f70 for the receiving
Lean 4.34.1 / Mathlib v4.34.1 environment. Original notices retained.
Compatibility modifications are recorded in PROVENANCE.json and PORT_REPORT.md. -/

module

public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Max
public import AlgebraicAutomata.FactorizationForest.Split
public import AlgebraicAutomata.ForMathlib.Data.List.SemigroupProd
public import AlgebraicAutomata.ForMathlib.Data.List.Slice

/-!
# Simon's Factorization Forest Theorem (Tree Version)

Formalization of the tree version of Simon's Factorization Forest Theorem,
constructing a Ramsey factorization tree of height at most `3 * nS S - 1` from
a Ramsey split (`simon_word`).

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

@[expose] public section


open RamseySplit

/-- Evaluates a list of elements in `S` via a semigroup homomorphism `ϕ : S →ₙ* T`,
defaulting to an arbitrary element on the empty list. -/
noncomputable def mulHomEval {S T : Type*} [Semigroup S] [Semigroup T] [Nonempty T]
    (ϕ : S →ₙ* T) (w : List S) : T :=
  if hw : w = [] then Classical.arbitrary T else ϕ (listProdNE w hw)

/-- `mulHomEval ϕ` is multiplicative on non-empty lists. -/
lemma mulHomEval_append {S T : Type*} [Semigroup S] [Semigroup T] [Nonempty T]
    (ϕ : S →ₙ* T) (u v : List S) (hu : u ≠ []) (hv : v ≠ []) :
    mulHomEval ϕ (u ++ v) = mulHomEval ϕ u * mulHomEval ϕ v := by
  have huv : u ++ v ≠ [] := by simp [hu]
  simp only [mulHomEval, dite_eq_right huv, dite_eq_right hu, dite_eq_right hv,
    listProdNE_concat u v hu hv, ϕ.map_mul]

/-- Factorization tree over alphabet `A`: leaf, binary concatenation, or idempotent node. -/
inductive FactorizationTree (A : Type*) where
  | leaf (a : A) : FactorizationTree A
  | binary (l r : FactorizationTree A) : FactorizationTree A
  | idempotent (children : List (FactorizationTree A)) : FactorizationTree A

namespace FactorizationTree

section TreeDefinitions

variable {A : Type*}

mutual
/-- Yields the list of leaves under `t` in left-to-right order. -/
def value : FactorizationTree A → List A
  | leaf a => [a]
  | binary l r => value l ++ value r
  | idempotent children => listValue children

/-- Yield of a list of factorization trees, concatenated left to right. -/
def listValue : List (FactorizationTree A) → List A
  | [] => []
  | t :: ts => value t ++ listValue ts
end

/-- The yield of a leaf `leaf a` is `[a]`. -/
@[simp]
lemma value_leaf (a : A) : (leaf a).value = [a] := rfl

/-- The yield of a binary node is the concatenation of the yields of its children. -/
@[simp]
lemma value_binary (l r : FactorizationTree A) : (binary l r).value = l.value ++ r.value := rfl

/-- Concatenation property for `listValue (t :: ts)`. -/
@[simp]
lemma listValue_cons (t : FactorizationTree A) (ts : List (FactorizationTree A)) :
    listValue (t :: ts) = value t ++ listValue ts := rfl

/-- Empty list yields empty word. -/
@[simp]
lemma listValue_nil : listValue ([] : List (FactorizationTree A)) = [] := rfl

/-- The yield of an idempotent node equals the yield of its children. -/
@[simp]
lemma value_idempotent (children : List (FactorizationTree A)) :
    (idempotent children).value = listValue children := rfl

/-- `listValue` characterization via flatten and map. -/
lemma listValue_eq_flatten (ts : List (FactorizationTree A)) :
    listValue ts = (ts.map value).flatten := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [listValue_cons, ih]

mutual
/-- Height of a factorization tree. -/
def height : FactorizationTree A → ℕ
  | leaf _ => 0
  | binary l r => 1 + max (height l) (height r)
  | idempotent children => 1 + listHeight children

/-- Maximum height across a list of factorization trees. -/
def listHeight : List (FactorizationTree A) → ℕ
  | [] => 0
  | t :: ts => max (height t) (listHeight ts)
end

/-- A leaf has height 0. -/
@[simp]
lemma height_leaf (a : A) : (leaf a).height = 0 := rfl

/-- Height of a binary node is $1 + \max(l.height, r.height)$. -/
@[simp]
lemma height_binary (l r : FactorizationTree A) :
    (binary l r).height = 1 + max l.height r.height := rfl

/-- Empty list of trees has height 0. -/
@[simp]
lemma listHeight_nil : listHeight ([] : List (FactorizationTree A)) = 0 := rfl

/-- Height of a non-empty list of trees. -/
@[simp]
lemma listHeight_cons (t : FactorizationTree A) (ts : List (FactorizationTree A)) :
    listHeight (t :: ts) = max (height t) (listHeight ts) := rfl

/-- Height of an idempotent node is $1 + \text{listHeight}(children)$. -/
@[simp]
lemma height_idempotent (children : List (FactorizationTree A)) :
    (idempotent children).height = 1 + listHeight children := rfl

/-- If every tree in `ts` has height $\le H$, then `listHeight ts \le H`. -/
lemma listHeight_le {H : ℕ} : ∀ (ts : List (FactorizationTree A)),
    (∀ t ∈ ts, height t ≤ H) → listHeight ts ≤ H
  | [], _ => Nat.zero_le H
  | t :: ts, h => max_le (h t (.head _)) (listHeight_le ts fun x hx ↦ h x (.tail _ hx))

/-- The height of any element of `ts` is bounded by `listHeight ts`. -/
lemma height_le_listHeight {c : FactorizationTree A} {ts : List (FactorizationTree A)}
  (h : c ∈ ts) : c.height ≤ listHeight ts := by
  induction ts with
  | nil => contradiction
  | cons t ts ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · dsimp [listHeight]
      omega
    · dsimp [listHeight]
      exact (ih hmem).trans (by omega)


/-- A tree that is not a leaf has height at least 1. -/
lemma height_pos_of_not_leaf (t : FactorizationTree A)
    (h : ∀ a, t ≠ leaf a) : 1 ≤ t.height := by
  cases t with
  | leaf a => exact (h a rfl).elim
  | binary l r => simp
  | idempotent children => simp

/-- The height of an idempotent tree is strictly greater than the height of each of its children. -/
lemma height_ge_child_of_idempotent {cs : List (FactorizationTree A)}
    {c : FactorizationTree A} (hc : c ∈ cs) :
    c.height + 1 ≤ (idempotent cs).height := by
  have h := height_le_listHeight hc
  simp only [height_idempotent]
  omega

/-- The height of a binary tree is strictly greater than the height of its left subtree. -/
lemma height_ge_child_of_binary_left (l r : FactorizationTree A) :
    l.height + 1 ≤ (binary l r).height := by
  simp only [height_binary]
  omega

/-- The height of a binary tree is strictly greater than the height of its right subtree. -/
lemma height_ge_child_of_binary_right (l r : FactorizationTree A) :
    r.height + 1 ≤ (binary l r).height := by
  simp only [height_binary]
  omega
/-- Induction principle for factorization trees. -/
@[elab_as_elim]
lemma induction_on {P : FactorizationTree A → Prop} (t : FactorizationTree A)
    (h_leaf : ∀ a, P (.leaf a))
    (h_binary : ∀ l r, P l → P r → P (.binary l r))
    (h_idempotent : ∀ children, (∀ t ∈ children, P t) → P (.idempotent children)) : P t := by
  induction h : t.height using Nat.strong_induction_on generalizing t with
  | h _ ih =>
    cases t with
    | leaf a => exact h_leaf a
    | binary l r =>
      rw [height_binary] at h
      exact h_binary l r
        (ih l.height (by omega) l rfl)
        (ih r.height (by omega) r rfl)
    | idempotent children =>
      rw [height_idempotent] at h
      apply h_idempotent
      intro c hc
      have h_le := height_le_listHeight hc
      exact ih c.height (by omega) c rfl

variable {S : Type*} [Semigroup S]

/-- Predicate stating that `t` is a Ramsey factorization tree with respect to `eval`. -/
def IsRamsey (eval : List A → S) (t : FactorizationTree A) : Prop :=
  match t with
  | leaf _ => True
  | binary l r => IsRamsey eval l ∧ IsRamsey eval r
  | idempotent children =>
      2 ≤ children.length ∧
      (∀ c ∈ children, IsRamsey eval c) ∧
      ∃ e : S, IsIdempotentElem e ∧ ∀ t ∈ children, eval (value t) = e
termination_by t

/-- A binary node is Ramsey iff both children are Ramsey. -/
@[simp]
lemma isRamsey_binary (eval : List A → S) (l r : FactorizationTree A) :
    (binary l r).IsRamsey eval ↔ l.IsRamsey eval ∧ r.IsRamsey eval := by rw [IsRamsey]

/-- Predicate stating that all trees in a list are Ramsey. -/
def listIsRamsey (eval : List A → S) : List (FactorizationTree A) → Prop
  | [] => True
  | t :: ts => IsRamsey eval t ∧ listIsRamsey eval ts

/-- Every leaf is trivially Ramsey. -/
lemma leaf_isRamsey (eval : List A → S) (a : A) : (leaf a).IsRamsey eval := by
  simp [IsRamsey]

/-- Constructs a Ramsey binary node from Ramsey children. -/
lemma binary_isRamsey (eval : List A → S) {l r : FactorizationTree A}
    (hl : l.IsRamsey eval) (hr : r.IsRamsey eval) :
    (binary l r).IsRamsey eval := (isRamsey_binary eval l r).mpr ⟨hl, hr⟩

/-- `listIsRamsey eval cs` holds iff every `c ∈ cs` is Ramsey. -/
lemma listIsRamsey_iff (eval : List A → S) :
    ∀ (ts : List (FactorizationTree A)), listIsRamsey eval ts ↔ ∀ t ∈ ts, t.IsRamsey eval
  | [] => by simp [listIsRamsey]
  | t :: ts => by simp [listIsRamsey, listIsRamsey_iff eval ts]

/-- An idempotent node is Ramsey iff all children are Ramsey and yield identical values. -/
@[simp]
lemma isRamsey_idempotent (eval : List A → S) (children : List (FactorizationTree A)) :
    (idempotent children).IsRamsey eval ↔
      2 ≤ children.length ∧
      listIsRamsey eval children ∧
      ∃ e : S, IsIdempotentElem e ∧ ∀ t ∈ children, eval (value t) = e := by
  unfold IsRamsey
  rw [← listIsRamsey_iff]

/-- Membership characterization for elements of `listValue cs`. -/
lemma mem_listValue {cs : List (FactorizationTree A)} {x : A}
    (h : x ∈ listValue cs) : ∃ c ∈ cs, x ∈ c.value := by
  induction cs with
  | nil => contradiction
  | cons c cs ih =>
    rcases List.mem_append.mp h with h1 | h2
    · exact ⟨c, .head _, h1⟩
    · obtain ⟨c', hc', hx'⟩ := ih h2
      exact ⟨c', .tail _ hc', hx'⟩

/-- A Ramsey factorization tree yields a non-empty word. -/
lemma tree_value_ne_nil {eval : List A → S} (t : FactorizationTree A)
    (ht : t.IsRamsey eval) : t.value ≠ [] := by
  induction t using FactorizationTree.induction_on with
  | h_leaf a => simp
  | h_binary l r ih_l ih_r =>
    rw [isRamsey_binary] at ht
    simp [value_binary, ih_l ht.1]
  | h_idempotent children ih =>
    rw [isRamsey_idempotent] at ht
    rcases ht with ⟨hlen, hlist, -⟩
    rcases children with _ | ⟨c, cs⟩
    · change 2 ≤ 0 at hlen
      omega
    · have hc_ramsey : c.IsRamsey eval := (listIsRamsey_iff eval (c :: cs)).mp hlist c (.head _)
      simp [value_idempotent, ih c (.head _) hc_ramsey]

end TreeDefinitions

end FactorizationTree


section SplitToTree

variable {A S : Type*} [Semigroup S]
variable (eval : List A → S)
variable (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
variable (u : List A)

/-- Constructs a factorization tree from an inner split step. -/
lemma split_to_tree_inner {n : ℕ} (m : ℕ) (_ : m < n)
    (s : Split (Fin (u.length + 1)) n)
    (h_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (ih : ∀ (i j : Fin (u.length + 1)) (_ : (i : ℕ) < (j : ℕ)),
      (∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m) →
      ∃ t : FactorizationTree A,
        t.value = (u.drop i).take (j - i) ∧
        t.IsRamsey eval ∧
        t.height ≤ 3 * m) :
    ∀ (i j : Fin (u.length + 1)) (_ : (i : ℕ) < (j : ℕ)),
    (s i : ℕ) = m → (s j : ℕ) = m →
    (∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) ≤ m) →
    ∃ (trees : List (FactorizationTree A)),
      trees ≠ [] ∧
      FactorizationTree.listValue trees = (u.drop i).take (j - i) ∧
      FactorizationTree.listIsRamsey eval trees ∧
      (∀ t ∈ trees, eval (t.value) = (wordLabeling eval hmul u).σ i j) ∧
      (∀ t ∈ trees, t.height ≤ 3 * m) ∧
      ((∃ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m) →
        2 ≤ trees.length) := by
  intro i j
  have H : ∀ (len : ℕ) (i j : Fin (u.length + 1))
      (hij : (i : ℕ) < (j : ℕ)) (hlen : (j : ℕ) - (i : ℕ) = len),
      (s i : ℕ) = m → (s j : ℕ) = m →
      (∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) ≤ m) →
      ∃ (trees : List (FactorizationTree A)),
        trees ≠ [] ∧
        FactorizationTree.listValue trees = (u.drop i).take (j - i) ∧
        FactorizationTree.listIsRamsey eval trees ∧
        (∀ t ∈ trees, eval (t.value) = (wordLabeling eval hmul u).σ i j) ∧
        (∀ t ∈ trees, t.height ≤ 3 * m) ∧
        ((∃ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m) →
          2 ≤ trees.length) := by
    intro len
    induction len using Nat.strong_induction_on with
    | h len ih_strong =>
      intro i j hij hlen hsi hsj h_between
      by_cases h_cut : ∃ x : Fin (u.length + 1),
        (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m
      · let S_cuts :=
          (Finset.univ : Finset (Fin (u.length + 1))).filter
          (fun (x : Fin (u.length + 1)) =>
          (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m)
        have h_nonempty : S_cuts.Nonempty := by
          rcases h_cut with ⟨x, hix, hxj, hsx⟩
          exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨hix, hxj, hsx⟩⟩⟩
        let k := S_cuts.min' h_nonempty
        have hk_mem := Finset.min'_mem S_cuts h_nonempty
        have hk_prop := (Finset.mem_filter.mp hk_mem).2
        have hik : (i : ℕ) < (k : ℕ) := hk_prop.1
        have hkj : (k : ℕ) < (j : ℕ) := hk_prop.2.1
        have hsk : (s k : ℕ) = m := hk_prop.2.2
        have h_less : ∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) →
          (x : ℕ) < (k : ℕ) → (s x : ℕ) < m := by
          intro x hix hxk
          have h_bet := h_between x hix (hxk.trans hkj)
          by_contra
          have hx_mem : x ∈ S_cuts :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ x, ⟨hix, hxk.trans hkj, by omega⟩⟩
          have h_min := Finset.min'_le S_cuts x hx_mem
          omega
        obtain ⟨t_outer, ht_outer_val, ht_outer_ramsey, ht_outer_height⟩ := ih i k hik h_less
        have h_len : (j : ℕ) - (k : ℕ) < len := by omega
        obtain ⟨trees_inner, h_inner_ne, h_inner_val, h_inner_ramsey,
                h_inner_eval, h_inner_height, _⟩ :=
          ih_strong ((j : ℕ) - (k : ℕ)) h_len k j hkj rfl hsk hsj
            (fun x hkx hxj => h_between x (hik.trans hkx) hxj)
        have h_rel_ik : SplitRelation s i k := by
          apply splitRelation_of_le_between s hik (by lia)
          intro z hz1 hz2
          have h := h_between z hz1 (hz2.trans hkj)
          omega
        have h_rel_kj : SplitRelation s k j := by
          apply splitRelation_of_le_between s hkj (by lia)
          intro z hz1 hz2
          have h := h_between z (hik.trans hz1) hz2
          omega
        obtain ⟨h_color_idem, h_color_eq, h_eval_ij_ik, -, h_eval_kj_eq_ij⟩ :=
          isRamsey_idem_step h_ramsey hik hkj h_rel_ik h_rel_kj
        have h_eval_ik_eq_ij := h_eval_ij_ik.symm
        have h_val_concat :
          FactorizationTree.listValue (t_outer :: trees_inner) = (u.drop i).take (j - i) := by
          rw [FactorizationTree.listValue_cons, ht_outer_val, h_inner_val]
          exact list_drop_take_append u i k j hik.le hkj.le
        have h_trees_ramsey :
          FactorizationTree.listIsRamsey eval (t_outer :: trees_inner) :=
          ⟨ht_outer_ramsey, h_inner_ramsey⟩
        have h_trees_eval_all :
            ∀ t ∈ (t_outer :: trees_inner), eval (t.value) = (wordLabeling eval hmul u).σ i j :=
          List.forall_mem_cons.2 ⟨ht_outer_val.symm ▸ h_eval_ik_eq_ij,
            fun t ht ↦ (h_inner_eval t ht).trans h_eval_kj_eq_ij⟩
        have h_height : ∀ t ∈ t_outer :: trees_inner, t.height ≤ 3 * m :=
          List.forall_mem_cons.2 ⟨ht_outer_height, h_inner_height⟩
        grind only [List.eq_nil_of_length_eq_zero, List.length_pos_of_mem, = List.mem_cons,
          = List.length_cons]
      · obtain ⟨t_outer, ht_outer_val, ht_outer_ramsey, ht_outer_height⟩ :=
          ih i j hij (by grind only)
        exact ⟨[t_outer], by simp, by simp [FactorizationTree.listValue, ht_outer_val],
          ⟨ht_outer_ramsey, trivial⟩, List.forall_mem_singleton.2 (ht_outer_val.symm ▸ rfl),
          List.forall_mem_singleton.2 ht_outer_height, fun hc ↦ (h_cut hc).elim⟩
  intro hij hsi hsj h_between
  exact H ((j : ℕ) - (i : ℕ)) i j hij rfl hsi hsj h_between

/-- Helper constructing a middle factorization tree from an idempotent sequence. -/
lemma split_to_tree_mid {n : ℕ}
    (s : Split (Fin (u.length + 1)) n)
    (h_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (m : ℕ) (hm : m < n)
    (ih_outer : ∀ (a b : Fin (u.length + 1)), (a : ℕ) < (b : ℕ) →
      (∀ x : Fin (u.length + 1), (a : ℕ) < (x : ℕ) → (x : ℕ) < (b : ℕ) → (s x : ℕ) < m) →
      ∃ t : FactorizationTree A,
        t.value = (u.drop a).take (b - a) ∧
        t.IsRamsey eval ∧
        t.height ≤ 3 * m)
    (a b : Fin (u.length + 1)) (hab : (a : ℕ) < (b : ℕ))
    (hsa : (s a : ℕ) = m) (hsb : (s b : ℕ) = m)
    (h_bound : ∀ x : Fin (u.length + 1), (a : ℕ) < (x : ℕ) → (x : ℕ) < (b : ℕ) → (s x : ℕ) ≤ m) :
    ∃ t_mid : FactorizationTree A,
      t_mid.value = (u.drop a).take (b - a) ∧
      t_mid.IsRamsey eval ∧
      t_mid.height ≤ 1 + 3 * m := by
  by_cases h_no_mid : ∀ x :
    Fin (u.length + 1), (a : ℕ) < (x : ℕ) → (x : ℕ) < (b : ℕ) → (s x : ℕ) < m
  · obtain ⟨t_mid, ht_mid_val, ht_mid_ramsey, ht_mid_height⟩ :=
      ih_outer a b hab h_no_mid
    exact ⟨t_mid, ht_mid_val, ht_mid_ramsey, by omega⟩
  · push Not at h_no_mid
    rcases h_no_mid with ⟨k_2, hak2, hk2b, _⟩
    have hk2_prop : (s k_2 : ℕ) = m := by
      have h_bound_k2 := h_bound k_2 hak2 hk2b
      omega
    have h_rel_a2 : SplitRelation s a k_2 := by
      apply splitRelation_of_le_between s hak2 (by lia)
      intro x hx1 hx2
      have hx_b := h_bound x hx1 (hx2.trans hk2b)
      lia
    have h_rel_2b : SplitRelation s k_2 b := by
      apply splitRelation_of_le_between s hk2b (by lia)
      intro x hx1 hx2
      have hx_b := h_bound x (hak2.trans hx1) hx2
      lia
    obtain ⟨-, -, -, h_idem_ab, -⟩ :=
      isRamsey_idem_step h_ramsey hak2 hk2b h_rel_a2 h_rel_2b
    have h_inner := split_to_tree_inner eval hmul u m hm s h_ramsey
      ih_outer a b hab hsa hsb h_bound
    obtain ⟨trees, _, h_trees_val, h_trees_ramsey, h_trees_eval,
            h_trees_height, h_trees_len⟩ := h_inner
    have h_len2 : 2 ≤ trees.length := h_trees_len ⟨k_2, hak2, hk2b, hk2_prop⟩
    exact ⟨.idempotent trees,
      by
        rw [FactorizationTree.value_idempotent]
        exact h_trees_val,
      by rw [FactorizationTree.isRamsey_idempotent]
         exact ⟨h_len2, h_trees_ramsey, _, h_idem_ab, h_trees_eval⟩,
      by rw [FactorizationTree.height_idempotent]
         have h_le := FactorizationTree.listHeight_le trees (fun t ht => h_trees_height t ht)
         omega⟩

/-- Constructs a factorization tree from an outer split step. -/
lemma split_to_tree_outer {n : ℕ}
    (s : Split (Fin (u.length + 1)) n)
    (h_ramsey : IsRamsey (wordLabeling eval hmul u) s) :
    ∀ (m : ℕ), m ≤ n → ∀ (i j : Fin (u.length + 1)), (i : ℕ) < (j : ℕ) →
    (∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m) →
    ∃ t : FactorizationTree A,
      t.value = (u.drop i).take (j - i) ∧
      t.IsRamsey eval ∧
      t.height ≤ 3 * m := by
  intro m
  induction m with
  | zero =>
    intro hm i j hij h_less
    have hj_eq : (j : ℕ) = (i : ℕ) + 1 := by
      by_contra
      let x : Fin (u.length + 1) := ⟨i.val + 1, by omega⟩
      have hx_less := h_less x (by lia) (by lia)
      omega
    have hi_lt : (i : ℕ) < u.length := by
      have hj_lt := j.isLt
      omega
    let t := FactorizationTree.leaf u[i.val]
    have ht_val : t.value = (u.drop i).take (j - i) := by
      simp only [FactorizationTree.value_leaf, t]
      rw [hj_eq]
      have h_diff : (i : ℕ) + 1 - (i : ℕ) = 1 := by omega
      exact h_diff.symm ▸ (list_drop_take_one u i.val hi_lt).symm
    exact ⟨t, ht_val, FactorizationTree.leaf_isRamsey eval _, by simp [t]⟩
  | succ m' ih_m' =>
    intro hm i j hij h_less
    let S_cuts :=
      (Finset.univ : Finset (Fin (u.length + 1))).filter
      (fun (x : Fin (u.length + 1)) =>
      (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m')
    by_cases h_empty : S_cuts = ∅
    · have h_less' :
          ∀ x : Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m' := by
        intro x hix hxj
        have h_sx_lt := h_less x hix hxj
        by_contra
        have h_mem : x ∈ S_cuts := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hix, hxj, by omega⟩
        have h_empty_x := Finset.ext_iff.mp h_empty x
        simp [h_mem] at h_empty_x
      obtain ⟨t, ht_val, ht_ramsey, ht_height⟩ := ih_m' (by omega) i j hij h_less'
      exact ⟨t, ht_val, ht_ramsey, by omega⟩
    · have h_nonempty : S_cuts.Nonempty := Finset.nonempty_of_ne_empty h_empty
      let k_1 := S_cuts.min' h_nonempty
      have hk1_mem := Finset.min'_mem S_cuts h_nonempty
      have hk1_prop := (Finset.mem_filter.mp hk1_mem).2
      let k_r := S_cuts.max' h_nonempty
      have hkr_mem := Finset.max'_mem S_cuts h_nonempty
      have hkr_prop := (Finset.mem_filter.mp hkr_mem).2
      have hik1 : (i : ℕ) < (k_1 : ℕ) := hk1_prop.1
      have h_less_ik1 : ∀ x :
        Fin (u.length + 1), (i : ℕ) < (x : ℕ) → (x : ℕ) < (k_1 : ℕ) → (s x : ℕ) < m' := by
        intro x hix hxk
        have h_sx_lt := h_less x hix (hxk.trans hk1_prop.2.1)
        by_contra
        have h_min_le := Finset.min'_le S_cuts x
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hix, hxk.trans hk1_prop.2.1, by omega⟩)
        omega
      obtain ⟨t_ik1, ht_ik1_val, ht_ik1_ramsey, ht_ik1_height⟩ :=
        ih_m' (by omega) i k_1 hik1 h_less_ik1
      have hkrj : (k_r : ℕ) < (j : ℕ) := hkr_prop.2.1
      have h_less_krj : ∀ x :
        Fin (u.length + 1), (k_r : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m' := by
        intro x hkx hxj
        have h_sx_lt := h_less x (by omega) hxj
        by_contra
        have h_le_max := Finset.le_max' S_cuts x
          (Finset.mem_filter.mpr ⟨Finset.mem_univ x, by omega, hxj, by omega⟩)
        omega
      obtain ⟨t_krj, ht_krj_val, ht_krj_ramsey, ht_krj_height⟩ :=
        ih_m' (by omega) k_r j hkrj h_less_krj
      by_cases h_eq : k_1 = k_r
      · obtain ⟨t_k1j, ht_k1j_val, ht_k1j_ramsey, ht_k1j_height⟩ :=
          ih_m' (by omega) k_1 j (h_eq ▸ hkrj) (h_eq ▸ h_less_krj)
        have ht_val : (FactorizationTree.binary t_ik1 t_k1j).value = (u.drop i).take (j - i) := by
          simp [ht_ik1_val, ht_k1j_val,
            list_drop_take_append u i.val k_1.val j.val hik1.le (h_eq ▸ hkrj).le]
        exact ⟨.binary t_ik1 t_k1j, ht_val,
          FactorizationTree.binary_isRamsey eval ht_ik1_ramsey ht_k1j_ramsey, by
            simp
            omega⟩
      · have hk1kr : (k_1 : ℕ) < (k_r : ℕ) := by
          have hle : k_1 ≤ k_r := Finset.min'_le S_cuts k_r hkr_mem
          omega
        have hk1j : (k_1 : ℕ) < (j : ℕ) := hk1kr.trans hkrj
        have h_mid := split_to_tree_mid eval hmul u s h_ramsey m' (by omega)
          (fun x y hxy hless => ih_m' (by omega) x y hxy hless)
          k_1 k_r hk1kr hk1_prop.2.2 hkr_prop.2.2 (fun x hk1x hxkr => by
            have hx_less := h_less x (hik1.trans hk1x) (hxkr.trans hkrj)
            omega)
        obtain ⟨t_mid, ht_mid_val, ht_mid_ramsey, _⟩ := h_mid
        have ht_val : (FactorizationTree.binary t_ik1 (.binary t_mid t_krj)).value =
            (u.drop i).take (j - i) := by
          simp [ht_ik1_val, ht_mid_val, ht_krj_val,
            list_drop_take_append u k_1.val k_r.val j.val hk1kr.le hkrj.le,
            list_drop_take_append u i.val k_1.val j.val hik1.le hk1j.le]
        exact ⟨.binary t_ik1 (.binary t_mid t_krj), ht_val,
          FactorizationTree.binary_isRamsey eval ht_ik1_ramsey
          (FactorizationTree.binary_isRamsey eval ht_mid_ramsey ht_krj_ramsey), by
            simp
            omega⟩

end SplitToTree

section ForestTheorem

/-- Simon's Factorization Forest Theorem for finite semigroups with evaluation map. -/
theorem factorization_forest_theorem {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧
      t.IsRamsey eval ∧
      t.height ≤ 3 * nS S - 1 := by
  have instNonemptyFin : Nonempty (Fin (nS S)) := instNonemptyFin_nS
  obtain ⟨s, h_norm, h_ramsey⟩ := simon_word eval hmul u
  let n := nS S
  have hn_pos : 0 < n := nS_pos
  let m := n - 1
  have hm_lt : m < n := Nat.sub_lt hn_pos (by omega)
  let i : Fin (u.length + 1) := ⟨0, by omega⟩
  let j : Fin (u.length + 1) := ⟨u.length, by omega⟩
  have hij : (i : ℕ) < (j : ℕ) := by cases u with | nil => contradiction | cons => simp [i, j]
  have h_bound_all : ∀ x : Fin (u.length + 1), (s x : ℕ) ≤ m :=
    fun x ↦ Nat.le_pred_of_lt (s x).isLt
  have hsi : (s i : ℕ) = m := by
    have h_min :
        (Finset.min' (Finset.univ : Finset (Fin (u.length + 1))) Finset.univ_nonempty) = i :=
      (Finset.min'_eq_iff _ _ i).mpr ⟨Finset.mem_univ i, fun w _ ↦ Fin.zero_le w⟩
    have h_max :
        ((Finset.max' (Finset.univ : Finset (Fin (nS S))) Finset.univ_nonempty :
          Fin (nS S)) : ℕ) = m := by
      rw [Fin.val_max'_univ]
    have h_norm' : s (Finset.min' Finset.univ Finset.univ_nonempty) =
      Finset.max' Finset.univ Finset.univ_nonempty := h_norm
    rw [h_min] at h_norm'
    exact congrArg Fin.val h_norm' ▸ h_max
  let S_cuts :=
    (Finset.univ : Finset (Fin (u.length + 1))).filter
    (fun (x : Fin (u.length + 1)) =>
    (i : ℕ) < (x : ℕ) ∧ (x : ℕ) < (j : ℕ) ∧ (s x : ℕ) = m)
  have h_u_val : (u.drop i).take (j - i) = u := by
    dsimp [i, j]
    simp [List.take_length]
  by_cases h_empty : S_cuts = ∅
  · have h_less : ∀ x : Fin (u.length + 1),
      (i : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m := by
      intro x hix hxj
      have h_bound_x := h_bound_all x
      by_contra
      have h_mem : x ∈ S_cuts := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hix, hxj, by omega⟩
      have h_empty_x := Finset.ext_iff.mp h_empty x
      simp [h_mem] at h_empty_x
    obtain ⟨t, ht_val, ht_ramsey, ht_height⟩ :=
      split_to_tree_outer eval hmul u s h_ramsey m hm_lt.le i j hij h_less
    exact ⟨t, ht_val.trans h_u_val, ht_ramsey, by omega⟩
  · have h_nonempty : S_cuts.Nonempty := Finset.nonempty_of_ne_empty h_empty
    let k_r := S_cuts.max' h_nonempty
    have hkr_mem := Finset.max'_mem S_cuts h_nonempty
    have hkr_prop := (Finset.mem_filter.mp hkr_mem).2
    have hikr : (i : ℕ) < (k_r : ℕ) := hkr_prop.1
    have hkrj : (k_r : ℕ) < (j : ℕ) := hkr_prop.2.1
    have hskr : (s k_r : ℕ) = m := hkr_prop.2.2
    have h_less_krj : ∀ x :
      Fin (u.length + 1), (k_r : ℕ) < (x : ℕ) → (x : ℕ) < (j : ℕ) → (s x : ℕ) < m := by
      intro x hkx hxj
      have h_bound_x := h_bound_all x
      by_contra
      have h_le_max := Finset.le_max' S_cuts x
        (Finset.mem_filter.mpr ⟨Finset.mem_univ x, by omega, hxj, by omega⟩)
      omega
    obtain ⟨t_krj, ht_krj_val, ht_krj_ramsey, ht_krj_height⟩ :=
      split_to_tree_outer eval hmul u s h_ramsey m hm_lt.le k_r j hkrj h_less_krj
    have h_mid := split_to_tree_mid eval hmul u s h_ramsey m hm_lt
      (fun a b hab hless => split_to_tree_outer eval hmul u s h_ramsey m hm_lt.le a b hab hless)
      i k_r hikr hsi hskr (fun x _ _ => h_bound_all x)
    obtain ⟨t_mid, ht_mid_val, ht_mid_ramsey, _⟩ := h_mid
    have ht_val : (FactorizationTree.binary t_mid t_krj).value = u := by
      simp [ht_mid_val, ht_krj_val, list_drop_take_append u i.val k_r.val j.val hikr.le hkrj.le,
        h_u_val]
    exact ⟨.binary t_mid t_krj, ht_val,
      FactorizationTree.binary_isRamsey eval ht_mid_ramsey ht_krj_ramsey, by
        simp
        grind⟩

/-- Simon's Factorization Forest Theorem for semigroup homomorphisms. -/
theorem factorization_forest_theorem_mulHom {S T : Type*} [Semigroup S] [Semigroup T]
    [Fintype T] [Nonempty T] (ϕ : S →ₙ* T) (u : List S) (hu : u ≠ []) :
    ∃ t : FactorizationTree S,
      t.value = u ∧ t.IsRamsey (mulHomEval ϕ) ∧ t.height ≤ 3 * nS T - 1 :=
  factorization_forest_theorem (mulHomEval ϕ) (mulHomEval_append ϕ) u hu

/-- Classical height bound $3|S| - 1$ for factorization trees. -/
theorem factorization_forest_classical_bound {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧
      t.IsRamsey eval ∧
      t.height ≤ 3 * Fintype.card S - 1 := by
  grind only [nS_le_card, factorization_forest_theorem eval hmul u hu]

/-- Classical height bound $3|S| - 1$ for semigroup homomorphisms. -/
theorem factorization_forest_classical_bound_mulHom {S T : Type*} [Semigroup S] [Semigroup T]
    [Fintype T] [Nonempty T] (ϕ : S →ₙ* T) (u : List S) (hu : u ≠ []) :
    ∃ t : FactorizationTree S,
      t.value = u ∧ t.IsRamsey (mulHomEval ϕ) ∧ t.height ≤ 3 * Fintype.card T - 1 :=
  factorization_forest_classical_bound (mulHomEval ϕ) (mulHomEval_append ϕ) u hu

end ForestTheorem
