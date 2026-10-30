import CCO.RigidGroupoid.Geometry.Quotient.Blocks
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Setoid.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite diversity rank uses ordered typed palettes consistently.
Actual quotient atoms are unions of old atoms; the injection below is built
from real witnesses and pair homogeneity, rather than assumed as cardinal data. -/

universe u v w q r t
namespace CCO.SimultaneousQuotients.Towers

/-- Genuine nonidentity of a kernel is exactly a swallowed distinct pair. -/
theorem kernel_ne_bot_iff {A : Type*} (J : Setoid A) :
    J ≠ ⊥ ↔ ∃ x y : A, x ≠ y ∧ J x y := by
  classical
  constructor
  · intro hJ
    by_contra h
    apply hJ
    apply Setoid.ext
    intro x y
    constructor
    · intro hxy
      change x = y
      by_contra hne
      exact h ⟨x,y,hne,hxy⟩
    · intro hxy
      change x = y at hxy
      subst y
      exact J.refl x
  · rintro ⟨x,y,hne,hxy⟩ hJ
    rw [hJ] at hxy
    exact hne hxy

variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,q,r} ι Q)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)] [∀ i, MulAction G (Q i)]
variable (H : HomogeneousSource S G)
variable (π : ∀ i, X i → Q i) (surjπ : ∀ i, Function.Surjective (π i))
variable (equivπ : ∀ i (g : G) x, π i (g • x) = g • π i x)
variable (hT : ∀ {i j} (x : Q i) (y : Q j) (x' : Q i) (y' : Q j),
  T.colour x y = T.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y')

include surjπ in
theorem atom_lift_exists {i j : ι} (a : T.Atom i j) :
    ∃ c : S.Atom i j, ∃ (x : X i) (y : X j),
      S.colour x y = some c ∧ T.colour (π i x) (π j y) = some a := by
  obtain ⟨q,r,hqr⟩ := T.realized a
  obtain ⟨x,rfl⟩ := surjπ i q
  obtain ⟨y,rfl⟩ := surjπ j r
  cases hc : S.colour x y with
  | some c => exact ⟨c,x,y,hc,hqr⟩
  | none =>
    have he := (S.colour_none_iff x y).mp hc
    cases he
    have hn := (T.colour_none_iff (π i x) (π i x)).mpr rfl
    rw [hn] at hqr
    cases hqr

noncomputable def liftAtom {i j : ι} (a : T.Atom i j) : S.Atom i j :=
  Classical.choose (atom_lift_exists S T π surjπ a)

theorem liftAtom_spec {i j : ι} (a : T.Atom i j) :
    ∃ (x : X i) (y : X j), S.colour x y = some (liftAtom S T π surjπ a) ∧
      T.colour (π i x) (π j y) = some a :=
  Classical.choose_spec (atom_lift_exists S T π surjπ a)

include H surjπ equivπ hT in
/-- Distinct actual quotient atoms cannot share an old atom. -/
theorem liftAtom_injective (i j : ι) : Function.Injective
    (liftAtom S T π surjπ (i := i) (j := j)) := by
  intro a b hab
  obtain ⟨x,y,hxy,hpa⟩ := liftAtom_spec S T π surjπ a
  obtain ⟨x',y',hx'y',hpb⟩ := liftAtom_spec S T π surjπ b
  obtain ⟨g,hgx,hgy⟩ := (S.pair_homogeneous_of_homogeneous H) x x' y y'
    (by rw [hxy,hx'y',hab])
  have hh := (hT (π i x) (π j y) (π i x') (π j y')).mpr
    ⟨g,by rw [←equivπ i g x,hgx],by rw [←equivπ j g y,hgy]⟩
  rw [hpa,hpb] at hh
  exact Option.some.inj hh

include H surjπ equivπ hT in
theorem atom_card_le (i j : ι) :
    letI := S.finiteAtom i j
    letI := T.finiteAtom i j
    Fintype.card (T.Atom i j) ≤ Fintype.card (S.Atom i j) := by
  letI := S.finiteAtom i j
  letI := T.finiteAtom i j
  exact Fintype.card_le_of_injective _ (liftAtom_injective S T H π surjπ equivπ hT i j)

include H surjπ equivπ hT in
/-- A real old diversity edge swallowed by the quotient kernel cannot be
any chosen lift of a quotient diversity atom. -/
theorem swallowed_not_lift {i : ι} {x y : X i} {c : S.Atom i i}
    (hxy : S.colour x y = some c) (hπ : π i x = π i y) :
    ∀ a : T.Atom i i, liftAtom S T π surjπ a ≠ c := by
  intro a ha
  obtain ⟨x',y',hx'y',hpa⟩ := liftAtom_spec S T π surjπ a
  obtain ⟨g,hgx,hgy⟩ := (S.pair_homogeneous_of_homogeneous H) x x' y y'
    (by rw [hxy,hx'y',ha])
  have hh := (hT (π i x) (π i y) (π i x') (π i y')).mpr
    ⟨g,by rw [←equivπ i g x,hgx],by rw [←equivπ i g y,hgy]⟩
  rw [hπ,(T.colour_none_iff _ _).mpr rfl,hpa] at hh
  cases hh

include H surjπ equivπ hT in
theorem atom_card_lt_of_swallowed {i : ι} {x y : X i}
    (hxy : x ≠ y) (hπ : π i x = π i y) :
    letI := S.finiteAtom i i
    letI := T.finiteAtom i i
    Fintype.card (T.Atom i i) < Fintype.card (S.Atom i i) := by
  letI := S.finiteAtom i i
  letI := T.finiteAtom i i
  obtain ⟨c,hc⟩ : ∃ c : S.Atom i i, S.colour x y = some c := by
    cases hh : S.colour x y with
    | some c => exact ⟨c,rfl⟩
    | none =>
      have he := (S.colour_none_iff x y).mp hh
      have he' : x = y := by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using he
      exact False.elim (hxy he')
  apply Fintype.card_lt_of_injective_not_surjective (liftAtom S T π surjπ)
    (liftAtom_injective S T H π surjπ equivπ hT i i)
  intro hs
  obtain ⟨a,ha⟩ := hs c
  exact swallowed_not_lift S T H π surjπ equivπ hT hc hπ a ha

/-- Sum over ordered typed diversity palettes; equality is never counted. -/
noncomputable def diversityRank {ι : Type u} {Y : ι → Type v}
    (A : AtomicSource.{u,v,w} ι Y) : Nat := by
  letI := A.finiteSort
  letI : ∀ i j, Fintype (A.Atom i j) := A.finiteAtom
  exact ∑ i, ∑ j, Fintype.card (A.Atom i j)

include H surjπ equivπ hT in
theorem diversityRank_le : diversityRank T ≤ diversityRank S := by
  classical
  letI := S.finiteSort
  letI : ∀ i j, Fintype (S.Atom i j) := S.finiteAtom
  letI : ∀ i j, Fintype (T.Atom i j) := T.finiteAtom
  unfold diversityRank
  rw [show T.finiteSort = S.finiteSort from Subsingleton.elim _ _]
  change (∑ i, ∑ j, Fintype.card (T.Atom i j)) ≤
    (∑ i, ∑ j, Fintype.card (S.Atom i j))
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact atom_card_le S T H π surjπ equivπ hT i j

include H surjπ equivπ hT in
/-- C48: any nonidentity current kernel strictly lowers TOTAL diversity
rank. All other palettes weakly decrease, so none compensate for its loss. -/
theorem diversityRank_lt_of_nonidentity
    (h : ∃ i, ∃ x y : X i, x ≠ y ∧ π i x = π i y) :
    diversityRank T < diversityRank S := by
  classical
  letI := S.finiteSort
  letI : ∀ i j, Fintype (S.Atom i j) := S.finiteAtom
  letI : ∀ i j, Fintype (T.Atom i j) := T.finiteAtom
  obtain ⟨i,x,y,hxy,hπ⟩ := h
  unfold diversityRank
  rw [show T.finiteSort = S.finiteSort from Subsingleton.elim _ _]
  change (∑ i, ∑ j, Fintype.card (T.Atom i j)) <
    (∑ i, ∑ j, Fintype.card (S.Atom i j))
  apply Finset.sum_lt_sum
  · intro k _
    exact Finset.sum_le_sum (fun l _ => atom_card_le S T H π surjπ equivπ hT k l)
  · refine ⟨i,Finset.mem_univ i,?_⟩
    apply Finset.sum_lt_sum
    · intro j _
      exact atom_card_le S T H π surjπ equivπ hT i j
    · exact ⟨i,Finset.mem_univ i,
        atom_card_lt_of_swallowed S T H π surjπ equivπ hT hxy hπ⟩

end CCO.SimultaneousQuotients.Towers
