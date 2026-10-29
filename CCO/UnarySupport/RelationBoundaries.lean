import CCO.UnarySupport.BoundaryLanguages
import Mathlib.Data.Fin.VecNotation

namespace CCO.UnarySupport.Boundaries
open Structure

def ternaryOnly : Structure (relationalSignature (fun _ : Unit => 3)) (Fin 3) :=
  relational _ (fun _ xs => xs 0 = 0 ∧ xs 1 = 1 ∧ xs 2 = 2)

theorem ternary_irreducible : ternaryOnly.Irreducible := by
  constructor
  intro d
  have h := d.rel_local () id (by exact ⟨rfl, rfl, rfl⟩)
  rcases h with hl | hr
  · exact d.left_proper (Set.eq_univ_of_forall hl)
  · exact d.right_proper (Set.eq_univ_of_forall hr)

theorem ternary_not_pair_covered :
    ¬ ∃ S, ternaryOnly.LocalSupport S ∧ (0 : Fin 3) ∈ S ∧ (1 : Fin 3) ∈ S := by
  rintro ⟨S, hS, h0, h1⟩
  cases hS with
  | singleton x =>
    have he : ternaryOnly.closureAt x = {x} := relational_closure _ _ {x}
    rw [he] at h0 h1
    have h01 : (0 : Fin 3) = 1 := h0.trans h1.symm
    exact (by decide : (0 : Fin 3) ≠ 1) h01
  | binary R hR xs hr hd => exact False.elim (by cases hR)

abbrev mixedArity : Bool → ℕ | false => 2 | true => 3

def pairSource : Structure (relationalSignature mixedArity) (Fin 3) :=
  relational _ (fun R => match R with
    | false => fun xs => xs 0 ≠ xs 1
    | true => fun _ => False)

def pairTarget : Structure (relationalSignature mixedArity) (Fin 3) :=
  relational _ (fun R => match R with
    | false => fun xs => xs 0 ≠ xs 1
    | true => fun xs => xs 0 = 0 ∧ xs 1 = 1 ∧ xs 2 = 2)

def pairMap : Hom pairSource pairTarget where
  point := id
  sort_eq _ := rfl
  map_func F := Empty.elim F
  map_rel R xs h := by
    cases R with
    | false => exact h
    | true => exact False.elim h

theorem support_omits_triple {S : Set (Fin 3)} (hS : pairSource.LocalSupport S) :
    ¬ ((0 : Fin 3) ∈ S ∧ (1 : Fin 3) ∈ S ∧ (2 : Fin 3) ∈ S) := by
  intro h
  cases hS with
  | singleton x =>
    have he : pairSource.closureAt x = {x} := relational_closure _ _ {x}
    rw [he] at h
    exact (by decide : (0 : Fin 3) ≠ 1) (h.1.trans h.2.1.symm)
  | binary R hR xs hr hd =>
    cases R with
    | true => exact False.elim (by cases hR)
    | false =>
      have he : pairSource.closure (Set.range xs) = Set.range xs := relational_closure _ _ _
      rw [he] at h
      obtain ⟨i, hi⟩ := h.1
      obtain ⟨j, hj⟩ := h.2.1
      obtain ⟨k, hk⟩ := h.2.2
      have hij : i.val ≠ j.val := by
        intro he
        have he' : i = j := Fin.ext he
        have : (0 : Fin 3) = 1 := hi.symm.trans ((congrArg xs he').trans hj)
        exact (by decide : (0 : Fin 3) ≠ 1) this
      have hik : i.val ≠ k.val := by
        intro he
        have he' : i = k := Fin.ext he
        have : (0 : Fin 3) = 2 := hi.symm.trans ((congrArg xs he').trans hk)
        exact (by decide : (0 : Fin 3) ≠ 2) this
      have hjk : j.val ≠ k.val := by
        intro he
        have he' : j = k := Fin.ext he
        have : (1 : Fin 3) = 2 := hj.symm.trans ((congrArg xs he').trans hk)
        exact (by decide : (1 : Fin 3) ≠ 2) this
      have hi' : i.val < 2 := i.isLt
      have hj' : j.val < 2 := j.isLt
      have hk' : k.val < 2 := k.isLt
      omega

theorem pair_locally_induced : pairMap.LocallyInduced := by
  intro S hS
  refine ⟨fun _ _ _ _ h => h, ?_, ?_⟩
  · intro R xs hxs
    cases R with
    | false => exact Iff.rfl
    | true =>
      constructor
      · rintro ⟨h0, h1, h2⟩
        exact support_omits_triple hS ⟨h0 ▸ hxs 0, h1 ▸ hxs 1, h2 ▸ hxs 2⟩
      · exact False.elim
  · intro F
    exact Empty.elim F

theorem pair_source_irreducible : pairSource.Irreducible := by
  constructor
  intro d
  have split : ∀ x y : Fin 3, x ≠ y →
      (x ∈ d.left ∧ y ∈ d.left) ∨ (x ∈ d.right ∧ y ∈ d.right) := by
    intro x y hxy
    let xs : Fin 2 → Fin 3 := ![x, y]
    have hr : pairSource.rel false xs := hxy
    rcases d.rel_local false xs hr with hl | hr
    · exact Or.inl ⟨hl 0, hl 1⟩
    · exact Or.inr ⟨hr 0, hr 1⟩
  have hin : ∀ x, x ∈ d.left ∨ x ∈ d.right := by
    intro x
    rw [← Set.mem_union, d.cover]
    trivial
  classical
  obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem d.left).1 d.left_proper
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem d.right).1 d.right_proper
  have hxy : x ≠ y := by
    intro h
    rcases hin x with hl | hr
    · exact hx hl
    · exact hy (h ▸ hr)
  rcases split x y hxy with hl | hr
  · exact hx hl.1
  · exact hy hr.2

theorem pair_not_global_embedding :
    ¬ ∃ e : Embedding pairSource pairTarget, ∀ x, e.point x = x := by
  rintro ⟨e, he⟩
  apply e.reflect_rel true id
  exact ⟨he 0, he 1, he 2⟩

/-- Local singleton/pair reflection cannot control a missing all-distinct
ternary tuple, even when every binary pair is already displayed. -/
theorem higher_relation_counterexamples :
    ternaryOnly.Irreducible ∧
    (¬ ∃ S, ternaryOnly.LocalSupport S ∧ (0 : Fin 3) ∈ S ∧ (1 : Fin 3) ∈ S) ∧
    pairSource.Irreducible ∧ pairMap.LocallyInduced ∧
    (¬ ∃ e : Embedding pairSource pairTarget, ∀ x, e.point x = x) :=
  ⟨ternary_irreducible, ternary_not_pair_covered, pair_source_irreducible,
    pair_locally_induced, pair_not_global_embedding⟩

end CCO.UnarySupport.Boundaries
