import CCO.StrongExact.FinitePC
import Mathlib.Tactic.FinCases
import Mathlib.SetTheory.Cardinal.Finite

/-! Literal zero-, one- and two-vertex STRONG PC boundaries. There is
no third distinct formal vertex, so even an arbitrary initial network
is unchanged by every synchronous update. -/
universe u v w z
namespace CCO.SafeReadings
open StrongPC
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} (D : PartialDiagram S V)

include D in
/-- Three pairwise distinct formal vertices require at least three vertices. -/
theorem card_ge_three_of_distinct (x y z : V) (hxy : x ≠ y)
    (hxz : x ≠ z) (hzy : z ≠ y) : 3 ≤ Nat.card V := by
  classical
  let : Finite V := D.finite_type
  let f : Fin 3 → V := fun i => if i = 0 then x else if i = 1 then y else z
  have hf : Function.Injective f := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all [f]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

include D in
/-- The PC support quantifier has no legal third formal vertex. -/
theorem no_third_of_card_le_two (hsmall : Nat.card V ≤ 2)
    (p : DistinctPair V) (z : V) (hxz : p.src ≠ z) (hzy : z ≠ p.dst) : False := by
  have hthree := card_ge_three_of_distinct D p.src p.dst z p.ne hxz hzy
  omega

/-- Every network is already fixed on at most two vertices. No domain
nonemptiness or completion assumption is needed for this exact boundary. -/
theorem small_step_eq_self (hsmall : Nat.card V ≤ 2) (N : Network D) :
    step D N = N := by
  funext p
  apply Set.Subset.antisymm
  · exact step_refines D N p
  · intro a ha
    refine ⟨ha,?_⟩
    intro z hxz hzy
    exact False.elim (no_third_of_card_le_two D hsmall p z hxz hzy)

theorem small_stable (hsmall : Nat.card V ≤ 2) (N : Network D) : Stable D N := by
  intro p
  exact congrArg (fun M : Network D => M p) (small_step_eq_self D hsmall N)

theorem small_iterate_eq_self (hsmall : Nat.card V ≤ 2) (N : Network D) (n : Nat) :
    iterate D N n = N := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate, ih, small_step_eq_self D hsmall]

theorem small_initial_stable (hsmall : Nat.card V ≤ 2) : Stable D (initial D) :=
  small_stable D hsmall _

theorem small_initial_iterate (hsmall : Nat.card V ≤ 2) (n : Nat) :
    iterate D (initial D) n = initial D := small_iterate_eq_self D hsmall _ n

theorem small_fixedNetwork_eq_initial (hsmall : Nat.card V ≤ 2) :
    fixedNetwork D = initial D := small_initial_iterate D hsmall _

include D in
/-- No off-diagonal formal pair exists on an empty or singleton diagram. -/
theorem distinctPair_isEmpty_of_card_le_one (hsmall : Nat.card V ≤ 1) :
    IsEmpty (DistinctPair V) := by
  let : Finite V := D.finite_type
  let : Fintype V := Fintype.ofFinite V
  have hc : Fintype.card V ≤ 1 := by simpa only [Nat.card_eq_fintype_card] using hsmall
  let : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp hc
  exact ⟨fun p => p.ne (Subsingleton.elim _ _)⟩

include D in
theorem distinctPair_isEmpty_of_card_zero (hzero : Nat.card V = 0) :
    IsEmpty (DistinctPair V) := distinctPair_isEmpty_of_card_le_one D (by omega)

include D in
theorem distinctPair_isEmpty_of_card_one (hone : Nat.card V = 1) :
    IsEmpty (DistinctPair V) := distinctPair_isEmpty_of_card_le_one D (by omega)

/-- The whole dependent Boolean network has a unique value when there
are no distinct formal pairs; no fake diagonal menu is added. -/
theorem network_subsingleton_of_card_le_one (hsmall : Nat.card V ≤ 1) :
    Subsingleton (Network D) := by
  let : IsEmpty (DistinctPair V) := distinctPair_isEmpty_of_card_le_one D hsmall
  infer_instance

/-- On two vertices a recorded edge remains its literal original singleton. -/
theorem small_fixedNetwork_specified (hsmall : Nat.card V ≤ 2)
    (p : DistinctPair V) (a : S.Atom (D.vertexSort p.src) (D.vertexSort p.dst))
    (he : D.edge p.src p.dst p.ne = some a) : fixedNetwork D p = {a} := by
  rw [small_fixedNetwork_eq_initial D hsmall]
  simp only [initial, he]

/-- On two vertices an unspecified edge remains literal typed Top. -/
theorem small_fixedNetwork_missing (hsmall : Nat.card V ≤ 2)
    (p : DistinctPair V) (he : D.edge p.src p.dst p.ne = none) :
    fixedNetwork D p = Set.univ := by
  rw [small_fixedNetwork_eq_initial D hsmall]
  simp only [initial, he]

end CCO.SafeReadings
