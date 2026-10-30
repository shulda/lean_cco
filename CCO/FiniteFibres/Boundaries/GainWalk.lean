import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-! Directed additive gains: actual simple cycles generate all closed-walk
relations. This proof permits arbitrary abelian gain groups and arbitrary
vertex types; it does not infer consistency from a bounded set of cycles. -/
namespace CCO.FiniteFibres.Boundaries.GainWalk

variable {V A : Type*} {K : SimpleGraph V} [AddCommGroup A]

def gain (weight : V → V → A) : {u v : V} → K.Walk u v → A
  | _,_,.nil => 0
  | u,_,.cons (v := v) _ p => weight u v + gain weight p

@[simp] theorem gain_nil (weight : V → V → A) (u : V) :
    gain weight (.nil : K.Walk u u) = 0 := rfl

@[simp] theorem gain_cons (weight : V → V → A) {u v w : V}
    (h : K.Adj u v) (p : K.Walk v w) :
    gain weight (.cons h p) = weight u v + gain weight p := rfl

theorem gain_append (weight : V → V → A) {u v w : V}
    (p : K.Walk u v) (q : K.Walk v w) :
    gain weight (p.append q) = gain weight p + gain weight q := by
  induction p with
  | nil => simp [gain]
  | cons h p ih => simp [gain,ih,add_assoc]

theorem gain_reverse (weight : V → V → A)
    (hrev : ∀ x y, weight y x = -weight x y) {u v : V} (p : K.Walk u v) :
    gain weight p.reverse = -gain weight p := by
  induction p with
  | nil => simp [gain]
  | @cons u v w h p ih =>
      rw [SimpleGraph.Walk.reverse_cons,gain_append,ih]
      change -gain weight p + (weight v u + 0) = -(weight u v + gain weight p)
      rw [hrev u v]
      abel

theorem gain_of_getVert (weight : V → V → A) {u v : V} (p : K.Walk u v)
    (f : ℕ → A)
    (hstep : ∀ n < p.length,
      weight (p.getVert n) (p.getVert (n+1)) = f (n+1) - f n) :
    gain weight p = f p.length - f 0 := by
  induction p generalizing f with
  | nil => simp [gain]
  | @cons u v w h p ih =>
      have hzero := hstep 0 (by simp)
      have htail : ∀ n < p.length,
          weight (p.getVert n) (p.getVert (n+1)) = f (n+1+1) - f (n+1) := by
        intro n hn
        simpa using hstep (n+1) (by simp; omega)
      have hh := ih (fun n => f (n+1)) htail
      simp only [SimpleGraph.Walk.getVert_zero,SimpleGraph.Walk.getVert_cons_succ] at hzero
      rw [gain_cons,hzero,hh]
      simp only [SimpleGraph.Walk.length_cons]
      abel

/-- Split at an actual repeated vertex of the tail. Genuine simple cycles
and immediate reversed edge pairs are the only irreducible cases. -/
theorem closed_gain_zero (weight : V → V → A)
    (hrev : ∀ x y, weight y x = -weight x y)
    (hcycle : ∀ u (p : K.Walk u u), p.IsCycle → gain weight p = 0)
    (u : V) (p : K.Walk u u) : gain weight p = 0 := by
  classical
  generalize hn : p.length = n
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
    cases p with
    | nil => rfl
    | @cons u v _ h q =>
      by_cases hlen : 3 ≤ (SimpleGraph.Walk.cons h q).length
      · by_cases hp : q.IsPath
        · exact hcycle _ _
            ((SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length).mpr
              ⟨by simpa using hp,hlen⟩)
        · have hex : ∃ (w : V) (r : K.Walk w w), r.IsSubwalk q ∧ ¬r.Nil := by
            have hh := mt SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil.mpr hp
            simpa only [not_forall,not_imp,exists_prop] using hh
          obtain ⟨w,r,⟨a,b,hab⟩,hr⟩ := hex
          have hrpos : 0 < r.length := Nat.pos_of_ne_zero
            (fun hz => hr (SimpleGraph.Walk.length_eq_zero_iff.mp hz))
          have hlenq : q.length + 1 = n := by simpa using hn
          have hparts : q.length = a.length + r.length + b.length := by simp [hab]
          have hz := ih r.length (by omega) w r rfl
          let short : K.Walk u u := .cons h (a.append b)
          have hshort : short.length < n := by
            simp only [short,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_append]
            omega
          have hzero := ih short.length hshort u short rfl
          simpa only [short,hab,gain_cons,gain_append,hz,add_zero] using hzero
      · cases q with
        | nil => exact (h.ne rfl).elim
        | @cons v w u h' q =>
          cases q with
          | nil => simp only [gain,add_zero,hrev u v,add_neg_cancel]
          | cons h'' r =>
            simp only [SimpleGraph.Walk.length_cons] at hlen
            omega

/-- Select one reference point in each actual connected component. The
closed-walk theorem proves that its path integrals are a global potential. -/
theorem exists_potential (weight : V → V → A)
    (hrev : ∀ x y, weight y x = -weight x y)
    (hclosed : ∀ u (p : K.Walk u u), gain weight p = 0) :
    ∃ f : V → A, ∀ x y, K.Adj x y → weight x y = f y - f x := by
  classical
  let path (C : K.ConnectedComponent) (v : C) : K.Walk C.out v.val :=
    (C.reachable_of_mem_supp C.out_eq v.property).some
  let potential (C : K.ConnectedComponent) (v : C) := gain weight (path C v)
  have hpot (C : K.ConnectedComponent) (x y : C) (hxy : K.Adj x.val y.val) :
      weight x.val y.val = potential C y - potential C x := by
    let closed : K.Walk C.out C.out :=
      ((path C x).append hxy.toWalk).append (path C y).reverse
    have hh := hclosed C.out closed
    simp only [closed,gain_append,gain_reverse weight hrev,SimpleGraph.Adj.toWalk,
      gain_cons,gain_nil,add_zero] at hh
    have heq : potential C x + weight x.val y.val = potential C y :=
      sub_eq_zero.mp (by simpa only [sub_eq_add_neg,potential] using hh)
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using heq
  let f : V → A := fun v =>
    potential (K.connectedComponentMk v) ⟨v,SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  refine ⟨f,?_⟩
  intro x y hxy
  have hy : K.connectedComponentMk y = K.connectedComponentMk x :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  have hh := hpot (K.connectedComponentMk x) ⟨x,rfl⟩ ⟨y,hy⟩ hxy
  have hcast {C C' : K.ConnectedComponent} (heq : C = C')
      (v : V) (hv : v ∈ C) (hv' : v ∈ C') :
      potential C ⟨v,hv⟩ = potential C' ⟨v,hv'⟩ := by cases heq; rfl
  have hfy : f y = potential (K.connectedComponentMk x) ⟨y,hy⟩ := hcast hy y _ _
  change weight x y = f y - f x
  rw [hfy]
  exact hh

end CCO.FiniteFibres.Boundaries.GainWalk
