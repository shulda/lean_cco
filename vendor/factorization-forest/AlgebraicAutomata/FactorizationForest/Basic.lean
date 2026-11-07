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

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin
public import AlgebraicAutomata.GreensRelations.Order
public import AlgebraicAutomata.ForMathlib.Data.List.Slice

/-!
# Ramsey Splits — Basic Definitions

Core structures and definitions for Ramsey splits, including multiplicative
labelings, splits, Ramsey condition, Simon complexity, and Green's relation invariants.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

@[expose] public section

lemma Fin.val_max'_univ {m : ℕ} [Nonempty (Fin m)] :
    (Finset.max' Finset.univ Finset.univ_nonempty : Fin m).val = m - 1 :=
  congrArg Fin.val
    ((Finset.max'_eq_iff _ _ ⟨m - 1, Nat.sub_lt (Fin.pos_iff_nonempty.mpr ‹_›) (by omega)⟩).mpr
      ⟨Finset.mem_univ _, fun w _ ↦ Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt w.isLt)⟩)

namespace RamseySplit

open GreensRelations

section SplitDefinitions

variable {S α : Type*} [Semigroup S] [LinearOrder α]

variable {h : ℕ}

/-- A multiplicative labeling over a linearly ordered type `α` into a semigroup
`S`, satisfying the property that `σ x y * σ y z = σ x z` for all `x < y < z`.
This models the evaluation of subwords in a factorization. -/
structure MultiplicativeLabeling (S α : Type*) [Semigroup S] [LinearOrder α] where
  /-- The labeling function, mapping a pair of indices to a semigroup element. -/
  σ : α → α → S
  /-- Multiplicativity: adjacent subwords multiply together correctly. -/
  prop : ∀ x y z : α, x < y → y < z → σ x y * σ y z = σ x z

/-- Coercion from `MultiplicativeLabeling` to its underlying labeling function. -/
instance : CoeFun (MultiplicativeLabeling S α) (fun _ => α → α → S) :=
  ⟨MultiplicativeLabeling.σ⟩

/-- A split is a function assigning each element of `α` a bounded integer rank
in `Fin h`. The rank encodes the "level" at which an element participates in the
factorization forest construction. -/
abbrev Split (α : Type*) (h : ℕ) : Type _ := α → Fin h

/-- `SplitRelation s x y` holds when `x` and `y` have the same rank under `s`,
and every element `z` between them (in the linear order) has a rank at most
equal to that of the minimum of `x` and `y`. -/
abbrev SplitRelation (s : Split α h) (x y : α) : Prop :=
  s x = s y ∧ ∀ z, min x y ≤ z → z ≤ max x y → s z ≤ s (min x y)

/-- A strictly monotone transformation of ranks preserves `SplitRelation`. -/
lemma SplitRelation.comp_strictMono {h₁ h₂ : ℕ} (s : Split α h₁) (f : Fin h₁ → Fin h₂)
    (hf : StrictMono f) (x y : α) :
    SplitRelation (f ∘ s) x y ↔ SplitRelation s x y := by
  simp only [SplitRelation, Function.comp_apply, hf.injective.eq_iff, hf.le_iff_le]

/-- Points of equal rank with bounded intermediate ranks satisfy `SplitRelation`. -/
lemma splitRelation_of_le_between {α : Type*} [LinearOrder α] {h : ℕ} (s : Split α h)
    {a b : α} (hab : a < b) (heq : s a = s b)
    (hbetween : ∀ z, a < z → z < b → s z ≤ s a) : SplitRelation s a b := by
  constructor
  · exact heq
  · intro z hz1 hz2
    rw [min_eq_left hab.le] at hz1 ⊢
    rw [max_eq_right hab.le] at hz2
    rcases hz1.eq_or_lt with rfl | ha
    · rfl
    rcases hz2.eq_or_lt with rfl | hb
    · rw [heq]
    exact hbetween z ha hb

/-- A split function is normalized if the minimal element of `α` receives the
maximal possible rank `Finset.max' Finset.univ`. This normalization ensures
the split is compatible with the inductive structure of the proof. -/
abbrev IsNormalized [Fintype α] [Nonempty α] [Nonempty (Fin h)]
    (s : Split α h) : Prop :=
  let min_α := Finset.min' Finset.univ Finset.univ_nonempty
  s min_α = Finset.max' Finset.univ Finset.univ_nonempty

/-- `IsRamsey L s` holds if adjacent split-related points evaluate to idempotents and
cross-related points evaluate uniformly. -/
abbrev IsRamsey (L : MultiplicativeLabeling S α) (s : Split α h) : Prop :=
  (∀ x y z : α, x < y → y < z → SplitRelation s x y → SplitRelation s y z →
    IsIdempotentElem (L.σ x y)) ∧
  (∀ x y u v : α, x < y → u < v →
    SplitRelation s x y → SplitRelation s u v → SplitRelation s x u →
    L.σ x y = L.σ u v)

/-- Properties of labels on three adjacent split-related points in a Ramsey labeling. -/
lemma isRamsey_idem_step {L : MultiplicativeLabeling S α} {s : Split α h} (h_ramsey : IsRamsey L s)
    {x y z : α} (hxy : x < y) (hyz : y < z)
    (h_rel_xy : SplitRelation s x y) (h_rel_yz : SplitRelation s y z) :
    IsIdempotentElem (L.σ x y) ∧
    L.σ x y = L.σ y z ∧
    L.σ x z = L.σ x y ∧
    IsIdempotentElem (L.σ x z) ∧
    L.σ y z = L.σ x z := by
  have h_eq := h_ramsey.2 x y y z hxy hyz h_rel_xy h_rel_yz h_rel_xy
  have h_idem := h_ramsey.1 x y z hxy hyz h_rel_xy h_rel_yz
  have h_tot := L.prop x y z hxy hyz
  have h_xz : L.σ x z = L.σ x y := by rw [← h_tot, ← h_eq, h_idem.eq]
  exact ⟨h_idem, h_eq, h_xz, h_xz ▸ h_idem, by rw [h_xz, h_eq]⟩

/-- A strictly monotone transformation of ranks preserves `IsRamsey`. -/
lemma IsRamsey.comp_strictMono {h₁ h₂ : ℕ} {L : MultiplicativeLabeling S α}
    {s : Split α h₁} (f : Fin h₁ → Fin h₂) (hf : StrictMono f) (h : IsRamsey L s) :
    IsRamsey L (f ∘ s) :=
  let hsr u v := (SplitRelation.comp_strictMono s f hf u v).mp
  ⟨fun x y z hxy hyz h1 h2 ↦ h.1 x y z hxy hyz (hsr x y h1) (hsr y z h2),
   fun x y u v hxy huv h1 h2 h3 ↦
     h.2 x y u v hxy huv (hsr x y h1) (hsr u v h2) (hsr x u h3)⟩

end SplitDefinitions

section WordDefinitions

/-- Multiplicative labeling mapping `(i, j)` to `eval(u[i..j])`. -/
abbrev wordLabeling {A S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) : MultiplicativeLabeling S (Fin (u.length + 1)) where
  σ := fun i j => eval ((u.drop i.val).take (j.val - i.val))
  prop := by
    intros x y z hxy hyz
    have h_ne : ∀ (a b : Fin (u.length + 1)), a < b →
        (u.drop a.val).take (b.val - a.val) ≠ [] := by
      intro a b hab
      rw [ne_eq, List.take_eq_nil_iff]
      intro h_or
      rcases h_or with h1 | h2
      · omega
      · rw [List.drop_eq_nil_iff] at h2
        omega
    rw [← hmul _ _ (h_ne x y hxy) (h_ne y z hyz),
        list_drop_take_append u x.val y.val z.val hxy.le hyz.le]

end WordDefinitions

section nD

variable {S : Type*} [Semigroup S] [Fintype S]

open Classical in
/-- Number of elements in `D` in the `H`-class of some idempotent, or 1 if non-regular. -/
noncomputable def nD (D : Set S) : ℕ :=
  if IsRegularDClass D then
    (Finset.univ.filter (fun x ↦
      x ∈ D ∧ ∃ e ∈ D, IsIdempotentElem e ∧ IsGreenH x e
    )).card
  else
    1

open Classical in
/-- The value `nD D` is strictly positive for any Green's `D`-class `D`. -/
theorem nD_pos (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) : 0 < nD D := by
  dsimp [nD]
  split_ifs with hReg
  · obtain ⟨e, heD, he_idem⟩ := (isRegularDClass_iff_exists_idempotent D hD).mp hReg
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, heD, e, heD, he_idem, IsGreenH.refl _⟩⟩
  · decide

end nD

section SimonComplexity

variable {S : Type*} [Semigroup S] [Fintype S]

open Classical in
/-- The number of elements strictly above in the $\mathcal{J}$-order decreases strictly
when moving up. -/
lemma strictlyAbove_card_lt {x y : S} (hlt : GreenJClass.mk x < GreenJClass.mk y) :
    (Finset.univ.filter (fun z ↦ GreenJClass.mk y < GreenJClass.mk z)).card <
    (Finset.univ.filter (fun z ↦ GreenJClass.mk x < GreenJClass.mk z)).card := by
  have h_le : Finset.univ.filter (fun (z : S) => GreenJClass.mk y < GreenJClass.mk z) ⊆
              Finset.univ.filter (fun (z : S) => GreenJClass.mk x < GreenJClass.mk z) := by
    grind
  have h_ne : Finset.univ.filter (fun (z : S) => GreenJClass.mk y < GreenJClass.mk z) ≠
              Finset.univ.filter (fun (z : S) => GreenJClass.mk x < GreenJClass.mk z) := by
    intro heq
    have h_mem := congrArg (y ∈ ·) heq
    simp [hlt] at h_mem
  exact Finset.card_lt_card (lt_of_le_of_ne h_le h_ne)

open Classical in
/-- The Simon complexity of `x ∈ S`, recursively summing `nD` along ascending `J`-chains. -/
noncomputable def nSElement (x : S) : ℕ :=
  let currentCost := nD (IsGreenD.eqvClass x)
  let strictlyAbove := Finset.univ.filter
    (fun (y : S) => GreenJClass.mk x < GreenJClass.mk y)
  let maxAbove := strictlyAbove.attach.sup (fun ⟨y, _hy⟩ => nSElement y)
  currentCost + maxAbove
termination_by (Finset.univ.filter
  (fun (y : S) => GreenJClass.mk x < GreenJClass.mk y)).card
decreasing_by
  exact strictlyAbove_card_lt (Finset.mem_filter.mp _hy).right

open Classical in
/-- The maximum Simon complexity over all elements of the semigroup `S`.
This is the global bound used in the statement of Simon's theorem. -/
noncomputable def nS (S : Type*) [Semigroup S] [Fintype S] : ℕ :=
  let all_vals := Finset.univ.image (fun (x : S) => nSElement x)
  if h : all_vals.Nonempty then
    Finset.max' all_vals h
  else
    0

open Classical in
/-- The Simon complexity of any element `x ∈ S` is strictly positive.
This follows from the fact that `nD` is always positive. -/
lemma nSElement_pos (x : S) : 0 < nSElement x := by
  rw [nSElement]
  have h_pos := nD_pos (IsGreenD.eqvClass x) ⟨x, rfl⟩
  omega

/-- `Fin (nSElement x)` is nonempty since `nSElement` is always positive. -/
lemma nonempty_fin_nSElement (x : S) : Nonempty (Fin (nSElement x)) :=
  Fin.pos_iff_nonempty.mp (nSElement_pos x)

/-- Instance providing nonemptiness for `Fin (nSElement x)`, used to satisfy the
`Nonempty (Fin h)` hypothesis in the Simon split construction. -/
instance instNonemptyFin_nSElement (x : S) : Nonempty (Fin (nSElement x)) :=
  nonempty_fin_nSElement x

open Classical in
/-- The Simon complexity `nS S` of any non-empty finite semigroup `S` is strictly positive. -/
lemma nS_pos {S : Type*} [Semigroup S] [Fintype S] [Nonempty S] : 0 < nS S :=
  let ⟨x⟩ : Nonempty S := inferInstance
  have h_mem := Finset.mem_image_of_mem (nSElement : S → ℕ) (Finset.mem_univ x)
  have h_eq : nS S = Finset.max' _ ⟨nSElement x, h_mem⟩ := dite_eq_left ⟨nSElement x, h_mem⟩
  h_eq.symm ▸ (nSElement_pos x).trans_le (Finset.le_max' _ _ h_mem)

/-- `Fin (nS S)` is non-empty for any non-empty finite semigroup `S`. -/
instance instNonemptyFin_nS {S : Type*} [Semigroup S] [Fintype S] [Nonempty S] :
    Nonempty (Fin (nS S)) :=
  Fin.pos_iff_nonempty.mp nS_pos

open Classical in
/-- In a finite semigroup, `nD D` is bounded by the cardinality of `D`. -/
lemma nD_le_card_eqvClass (x : S) :
    nD (IsGreenD.eqvClass x) ≤ (Finset.univ.filter (· ∈ IsGreenD.eqvClass x)).card := by
  dsimp [nD]
  split_ifs with hReg
  · apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact hy.1
  · have hx_mem : x ∈ Finset.univ.filter (· ∈ IsGreenD.eqvClass x) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact IsGreenD.refl x
    exact Finset.card_pos.mpr ⟨x, hx_mem⟩

omit [Fintype S] in
/-- Membership in the $\mathcal{D}$-class coincides with equality of $\mathcal{J}$-classes
in finite semigroups. -/
lemma mem_isGreenD_eqvClass_iff_greenJClass_eq [Finite S] (x z : S) :
    z ∈ IsGreenD.eqvClass x ↔ GreenJClass.mk z = GreenJClass.mk x := by
  grind [GreenJClass.mk_eq_mk_iff, isGreenJ_of_isGreenD, isGreenD_of_isGreenJ]

open Classical in
/-- The fiber of elements $\mathcal{D}$-equivalent to `x` equals the fiber of elements
with the same $\mathcal{J}$-class. -/
lemma filter_isGreenD_eqvClass_eq (x : S) :
    Finset.univ.filter (· ∈ IsGreenD.eqvClass x) =
    Finset.univ.filter (fun z ↦ GreenJClass.mk z = GreenJClass.mk x) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_isGreenD_eqvClass_iff_greenJClass_eq x z

open Classical in
/-- The cost `nD` of the $\mathcal{D}$-class is bounded by the size of the
corresponding $\mathcal{J}$-class. -/
lemma nD_le_card_j_eq (x : S) :
    nD (IsGreenD.eqvClass x) ≤
      (Finset.univ.filter (fun z ↦ GreenJClass.mk z = GreenJClass.mk x)).card := by
  rw [← filter_isGreenD_eqvClass_eq]
  exact nD_le_card_eqvClass x

open Classical in
/-- Auxiliary bound on `nSElement x` by elements with $\mathcal{J}$-class $\ge \mathcal{J}(x)$,
by induction on the strictly above count. -/
theorem nSElement_le_card_ge_aux (n : ℕ) (x : S)
    (hn : (Finset.univ.filter (fun y ↦ GreenJClass.mk x < GreenJClass.mk y)).card ≤ n) :
    nSElement x ≤ (Finset.univ.filter (fun z ↦ GreenJClass.mk x ≤ GreenJClass.mk z)).card := by
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
    rw [nSElement]
    dsimp only
    set currentCost := nD (IsGreenD.eqvClass x)
    set strictlyAbove := Finset.univ.filter (fun (y : S) => GreenJClass.mk x < GreenJClass.mk y)
    set maxAbove := strictlyAbove.attach.sup (fun ⟨y, _hy⟩ => nSElement y)
    set A := Finset.univ.filter (fun z ↦ GreenJClass.mk z = GreenJClass.mk x)
    have h_nD : currentCost ≤ A.card := nD_le_card_j_eq x
    set Target := Finset.univ.filter (fun z ↦ GreenJClass.mk x ≤ GreenJClass.mk z)
    have h_A_sub : A ⊆ Target := by
      intro z hz
      have h_eq : GreenJClass.mk z = GreenJClass.mk x := (Finset.mem_filter.mp hz).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h_eq]⟩
    have h_A_le : A.card ≤ Target.card := Finset.card_le_card h_A_sub
    have h_sup_le : maxAbove ≤ Target.card - A.card := by
      apply Finset.sup_le
      rintro ⟨y, hy_mem⟩ -
      have hy_lt : GreenJClass.mk x < GreenJClass.mk y :=
        (Finset.mem_filter.mp hy_mem).2
      have h_card_y := strictlyAbove_card_lt hy_lt
      have h_y_lt_n : (Finset.univ.filter (fun z ↦ GreenJClass.mk y < GreenJClass.mk z)).card < n :=
        h_card_y.trans_le hn
      have ih_y := ih (Finset.univ.filter (fun z ↦ GreenJClass.mk y < GreenJClass.mk z)).card
        h_y_lt_n y le_rfl
      set B := Finset.univ.filter (fun z ↦ GreenJClass.mk y ≤ GreenJClass.mk z)
      have h_disj : Disjoint A B := by
        rw [Finset.disjoint_filter]
        intro z _ hzA hzB
        rw [hzA] at hzB
        exact lt_irrefl _ (hy_lt.trans_le hzB)
      have h_sub : A ∪ B ⊆ Target := by
        intro z hz
        rcases Finset.mem_union.mp hz with hA | hB
        · have h_eq := (Finset.mem_filter.mp hA).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h_eq]⟩
        · have h_le := (Finset.mem_filter.mp hB).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy_lt.le.trans h_le⟩
      have h_union_card : (A ∪ B).card = A.card + B.card :=
        Finset.card_union_of_disjoint h_disj
      have h_card_le := Finset.card_le_card h_sub
      rw [h_union_card] at h_card_le
      have : nSElement y ≤ Target.card - A.card := by omega
      exact this
    change currentCost + maxAbove ≤ Target.card
    omega

open Classical in
/-- The Simon complexity of `x ∈ S` is bounded by the number of elements with J-class ≥ x. -/
theorem nSElement_le_card_ge (x : S) :
    nSElement x ≤ (Finset.univ.filter (fun z ↦ GreenJClass.mk x ≤ GreenJClass.mk z)).card :=
  nSElement_le_card_ge_aux _ x le_rfl

open Classical in
/-- Simon complexity of an element is bounded by the cardinality of `S`. -/
theorem nSElement_le_card (x : S) : nSElement x ≤ Fintype.card S := by
  apply (nSElement_le_card_ge x).trans
  have h_sub : Finset.univ.filter (fun z ↦ GreenJClass.mk x ≤ GreenJClass.mk z) ⊆ Finset.univ :=
    Finset.filter_subset _ _
  have h_le := Finset.card_le_card h_sub
  rw [Finset.card_univ] at h_le
  exact h_le

open Classical in
/-- The Simon complexity `nS S` is bounded by the cardinality of `S` (Colcombet line 361). -/
theorem nS_le_card : nS S ≤ Fintype.card S := by
  dsimp [nS]
  split_ifs with h
  · have h_mem := Finset.max'_mem _ h
    rw [Finset.mem_image] at h_mem
    obtain ⟨x, _, hx_eq⟩ := h_mem
    rw [← hx_eq]
    exact nSElement_le_card x
  · exact Nat.zero_le _

end SimonComplexity

section LabelingProperties

variable {S : Type*} [Semigroup S]

/-- The set of elements of `S` whose Green's `J`-class is at least as large as
that of `a`, i.e., `b` such that `a ≤_J b`. Used to bound the image of a
multiplicative labeling during the induction in Simon's theorem. -/
abbrev jUp (a : S) : Set S := { b | GreenJClass.mk a ≤ GreenJClass.mk b }

/-- States that all strictly ordered pairs `(x, y)` under the labeling `σ`
map into the set `U`. This is the hypothesis that the labeling takes values
in the relevant J-upward closure. -/
abbrev labelingIn {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (U : Set S) : Prop :=
  ∀ x y : α, x < y → σ.σ x y ∈ U

/-- Factors are J-greater than or equal to the product containing them. -/
lemma labeling_factor_le_J {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (u v w x : α)
    (huv : u ≤ v) (hvw : v < w) (hwx : w ≤ x) :
    GreenJClass.mk (σ.σ u x) ≤ GreenJClass.mk (σ.σ v w) :=
  have h1 : GreenJClass.mk (σ.σ u x) ≤ GreenJClass.mk (σ.σ v x) :=
    huv.eq_or_lt.elim (fun | rfl => le_rfl) fun h ↦
      (σ.prop u v x h (hvw.trans_le hwx)).symm ▸ IsGreenJRel.mul_left _ rfl
  have h2 : GreenJClass.mk (σ.σ v x) ≤ GreenJClass.mk (σ.σ v w) :=
    hwx.eq_or_lt.elim (fun | rfl => le_rfl) fun h ↦
      (σ.prop v w x hvw h).symm ▸ IsGreenJRel.mul_right _ rfl
  h1.trans h2

variable [Finite S]

/-- If a prefix product is `D`-related to `a`, the extended product is also `D`-related to `a`. -/
lemma isGreenD_of_prefix (a : S) {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (h_img : labelingIn σ (jUp a))
    (u v w : α) (huv : u < v) (hvw : v ≤ w) (hD : IsGreenD (σ.σ u v) a) :
    IsGreenD (σ.σ u w) a :=
  hvw.eq_or_lt.elim (fun | rfl => hD) fun hvw_lt ↦
    isGreenD_of_isGreenJ (GreenJClass.mk_eq_mk_iff.mp (le_antisymm
      (GreenJClass.mk_eq_mk_iff.mpr (isGreenJ_of_isGreenD hD) ▸
        labeling_factor_le_J σ u u v w le_rfl huv hvw)
      (h_img u w (huv.trans hvw_lt))))

end LabelingProperties

section GeneralUtility

/-- A subtype of `α` representing elements strictly between `xs[i]` and
`xs[i+1]` (or between `xs[i]` and +∞ if `i` is the last index).
Used to restrict the inductive hypothesis to proper sub-intervals. -/
abbrev OpenIntervalType {α : Type*} [LinearOrder α] (xs : List α) (i : ℕ) : Type _ :=
  { y : α // ∃ (hi_lt : i < xs.length),
    xs[i] < y ∧
    ∀ (h_next_lt : i + 1 < xs.length), y < xs[i + 1] }

/-- A strictly increasing sequence covering a domain bounds any element `x`
either at one of the sequence points or within a consecutive interval.
This is the key covering lemma used in the split combination construction. -/
lemma list_interval_covers {α : Type*} [LinearOrder α] (x : α) :
    ∀ (xs : List α), x ∉ xs →
    (∃ y ∈ xs, y < x) →
    ∃ (i : ℕ) (hi_lt : i < xs.length),
      xs[i] < x ∧
      ∀ (hi_succ_lt : i + 1 < xs.length), x < xs[i + 1]
  | [], _, ⟨_, hy, _⟩ => nomatch hy
  | a :: tail, h_not_in, h_lb => by
    by_cases h_tail : ∃ y ∈ tail, y < x
    · obtain ⟨i, hi, hlt, hgt⟩ :=
        list_interval_covers x tail (fun h => h_not_in (List.Mem.tail _ h)) h_tail
      exact ⟨i + 1, Nat.succ_lt_succ hi, hlt, fun h ↦ hgt (Nat.lt_of_succ_lt_succ h)⟩
    · grind only [List.length_pos_of_mem, = List.mem_cons, = List.getElem_cons, List.getElem_mem]

/-- An element in an open interval `OpenIntervalType xs i` is never a member
of the sequence `xs` itself (since it is strictly between two consecutive
sequence points, while the sequence is strictly monotone). -/
lemma not_mem_of_openInterval {α : Type*} [LinearOrder α] {xs : List α}
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length) (hj_lt : j < xs.length),
      i < j → xs[i] < xs[j])
    (i : ℕ) (z : α)
    (h_in : ∃ (hi_lt : i < xs.length),
      xs[i] < z ∧ ∀ (hi_succ_lt : i + 1 < xs.length),
      z < xs[i + 1]) : z ∉ xs := by
  grind [List.mem_iff_getElem]

/-- Two open intervals defined by the same strictly increasing sequence are
disjoint: if an element `x` lies in both interval `i` and interval `k`,
then `i = k`. -/
lemma openInterval_unique {α : Type*} [LinearOrder α] (xs : List α)
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length)
      (hj_lt : j < xs.length), i < j →
      xs[i] < xs[j])
    (x : α) (i k : ℕ) (hi : i < xs.length) (hk : k < xs.length)
    (hlt_i : xs[i] < x)
    (hgt_i : ∀ h_next_lt : i + 1 < xs.length,
      x < xs[i + 1])
    (hlt_k : xs[k] < x)
    (hgt_k : ∀ h_next_lt : k + 1 < xs.length,
      x < xs[k + 1]) :
    i = k := by
  rcases lt_trichotomy i k with h | rfl | h <;> first | rfl | cases (show False by grind only)

end GeneralUtility

end RamseySplit
