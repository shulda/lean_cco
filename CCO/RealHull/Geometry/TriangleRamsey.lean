import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

/-!
# Explicit finite multicolour triangle Ramsey

The proof retains a largest outgoing colour class at each pivot. It constructs
`t+1` DISTINCT vertices from `f_k(t)` vertices, with one colour for each of the
first `t` outgoing rows. At `t=k+1` two row colours agree, and the last vertex
closes an actual monochromatic triangle. No infinite Ramsey or compactness
theorem is used. Finiteness is proved BEFORE the cardinal bound for consumers.
-/

universe u v
namespace CCO.RealHull.Geometry.TriangleRamsey

def bound (k : ℕ) : ℕ → ℕ
  | 0 => 1
  | t+1 => k * bound k t + 1

@[simp] theorem bound_zero (k : ℕ) : bound k 0 = 1 := rfl
@[simp] theorem bound_succ (k t : ℕ) : bound k (t+1) = k * bound k t + 1 := rfl
theorem bound_pos (k t : ℕ) : 0 < bound k t := by cases t <;> simp [bound]
@[simp] theorem bound_one (t : ℕ) : bound 1 t = t+1 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [bound,ih]

variable {V : Type u} {C : Type v} [Fintype C] [Nonempty C]

/-- The complete finite greedy construction, with every original vertex and
every directed row equality retained. Symmetry is not needed at this stage.
-/
theorem greedy_fan (colour : V → V → C) (t : ℕ) (s : Finset V)
    (hs : bound (Fintype.card C) t ≤ s.card) :
    ∃ (points : Fin (t+1) → V) (rows : Fin t → C),
      Function.Injective points ∧ (∀ i, points i ∈ s) ∧
      ∀ (i : Fin t) (j : Fin (t+1)), i.val < j.val →
        colour (points i.castSucc) (points j) = rows i := by
  classical
  induction t generalizing s with
  | zero =>
      obtain ⟨x,hx⟩ := Finset.card_pos.mp (lt_of_lt_of_le (bound_pos _ _) hs)
      refine ⟨fun _ => x, Fin.elim0, ?_, fun _ => hx, ?_⟩
      · intro i j _
        apply Fin.ext
        have hi := i.isLt
        have hj := j.isLt
        omega
      · intro i
        exact Fin.elim0 i
  | succ t ih =>
      obtain ⟨x,hx⟩ := Finset.card_pos.mp (lt_of_lt_of_le (bound_pos _ _) hs)
      have hcard : Fintype.card C * bound (Fintype.card C) t ≤ (s.erase x).card := by
        rw [Finset.card_erase_of_mem hx]
        simp only [bound_succ] at hs
        omega
      obtain ⟨c,_,hc⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
        (s := s.erase x) (t := Finset.univ) (f := colour x)
        (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty (by simpa using hcard)
      obtain ⟨p,r,hp,hm,hr⟩ := ih _ hc
      have hpx : x ∉ Set.range p := by
        rintro ⟨i,hi⟩
        have hh := (Finset.mem_filter.mp (hm i)).1
        exact (Finset.mem_erase.mp hh).1 hi
      refine ⟨Fin.cons x p, Fin.cons c r, Fin.cons_injective_of_injective hpx hp, ?_, ?_⟩
      · intro i
        refine Fin.cases hx (fun j => ?_) i
        exact Finset.mem_of_mem_erase (Finset.mem_filter.mp (hm j)).1
      · intro i
        refine Fin.cases ?_ (fun i => ?_) i
        · intro j
          refine Fin.cases ?_ (fun j => ?_) j
          · intro hij
            simp at hij
          · intro _
            simpa only [Fin.cons_zero,Fin.cons_succ,Fin.castSucc_zero] using
              (Finset.mem_filter.mp (hm j)).2
        · intro j
          refine Fin.cases ?_ (fun j => ?_) j
          · intro hij
            simp at hij
          · intro hij
            have hij' : i.val < j.val := by simpa using hij
            simpa only [Fin.cons_succ,Fin.castSucc_succ] using hr i j hij'

def MonochromaticTriangle (colour : V → V → C) : Prop :=
  ∃ x y z, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    colour x y = colour x z ∧ colour x y = colour y z

theorem triangle_of_card (colour : V → V → C) (s : Finset V)
    (hs : bound (Fintype.card C) (Fintype.card C+1) ≤ s.card) :
    ∃ x ∈ s, ∃ y ∈ s, ∃ z ∈ s, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      colour x y = colour x z ∧ colour x y = colour y z := by
  obtain ⟨p,r,hp,hm,hr⟩ := greedy_fan colour _ s hs
  have hni : ¬ Function.Injective r := by
    intro hi
    have hc := Fintype.card_le_of_injective r hi
    simp only [Fintype.card_fin] at hc
    omega
  have hpair : ∃ i j, r i = r j ∧ i ≠ j := by
    by_contra h
    apply hni
    intro i j he
    by_contra hne
    exact h ⟨i,j,he,hne⟩
  obtain ⟨i,j,heq,hne⟩ := hpair
  have ordered (i j : Fin (Fintype.card C+1)) (heq : r i = r j) (hij : i.val < j.val) :
      ∃ x ∈ s, ∃ y ∈ s, ∃ z ∈ s, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
        colour x y = colour x z ∧ colour x y = colour y z := by
    let last : Fin (Fintype.card C+1+1) := Fin.last (Fintype.card C+1)
    have hil : i.val < last.val := i.isLt
    have hjl : j.val < last.val := j.isLt
    refine ⟨p i.castSucc,hm _,p j.castSucc,hm _,p last,hm _,?_,?_,?_,?_,?_⟩
    · apply hp.ne
      intro h
      have hv : i.val = j.val :=
        congrArg (fun q : Fin (Fintype.card C+1+1) => q.val) h
      omega
    · apply hp.ne
      intro h
      have hv : j.val = Fintype.card C+1 := congrArg Fin.val h
      omega
    · apply hp.ne
      intro h
      have hv : i.val = Fintype.card C+1 := congrArg Fin.val h
      omega
    · exact (hr i j.castSucc hij).trans (hr i last hil).symm
    · exact (hr i j.castSucc hij).trans (heq.trans (hr j last hjl).symm)
  by_cases hij : i.val < j.val
  · exact ordered i j heq hij
  · have hv : i.val ≠ j.val := fun he => hne (Fin.ext he)
    exact ordered j i heq.symm (by omega)

/-- The usual finite undirected triangle property; logical diagonal colours
are irrelevant because the three witnesses are distinct.
-/
def TriangleProperty (k n : ℕ) : Prop :=
  ∀ colour : Fin n → Fin n → Fin k,
    (∀ x y, colour x y = colour y x) → MonochromaticTriangle colour

theorem triangleProperty_bound (k : ℕ) (hk : 0 < k) :
    TriangleProperty k (bound k (k+1)) := by
  letI : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  intro colour _
  obtain ⟨x,_,y,_,z,_,h⟩ := triangle_of_card colour Finset.univ
    (by simp only [Finset.card_univ,Fintype.card_fin]; exact le_rfl)
  exact ⟨x,y,z,h⟩

noncomputable def ramseyNumber (k : ℕ) (hk : 0 < k) : ℕ := by
  classical
  exact Nat.find (show ∃ n, TriangleProperty k n from ⟨_,triangleProperty_bound k hk⟩)

theorem ramseyNumber_spec (k : ℕ) (hk : 0 < k) :
    TriangleProperty k (ramseyNumber k hk) := by
  classical
  exact Nat.find_spec _

theorem ramseyNumber_min (k n : ℕ) (hk : 0 < k) (hn : TriangleProperty k n) :
    ramseyNumber k hk ≤ n := by
  classical
  exact Nat.find_min' _ hn

theorem ramseyNumber_le_bound (k : ℕ) (hk : 0 < k) :
    ramseyNumber k hk ≤ bound k (k+1) := ramseyNumber_min k _ hk (triangleProperty_bound k hk)

/-- A no-injection bound first forces the type finite, so the displayed
natural-number cardinal bound cannot hold vacuously on an infinite type.
-/
theorem finite_card_lt_of_no_embedding (N : ℕ) (hno : ¬ Nonempty (Fin N ↪ V)) :
    Finite V ∧ Nat.card V < N := by
  classical
  have hfin : Finite V := by
    by_contra h
    letI : Infinite V := not_finite_iff_infinite.mp h
    exact hno ⟨⟨fun i => Infinite.natEmbedding V i.val,
      fun _ _ he => Fin.ext ((Infinite.natEmbedding V).injective he)⟩⟩
  letI : Finite V := hfin
  letI : Fintype V := Fintype.ofFinite V
  refine ⟨hfin, ?_⟩
  rw [Nat.card_eq_fintype_card]
  by_contra h
  apply hno
  exact Function.Embedding.nonempty_of_card_le (by simpa using (Nat.le_of_not_gt h))

end CCO.RealHull.Geometry.TriangleRamsey
