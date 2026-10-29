import CCO.UnarySupport.TypedTerms
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Conditional bounds on actual completed ONE-generated class members.
No bound on arbitrary partial diagrams, or pointwise source bound, is assumed. -/

universe u v
namespace CCO.UnarySupport.Structure
variable {L : Signature.{u}} {V : Type v}

/-- The optional class bound quantifies over actual finite completed
one-generated members; it is not a bound supplied directly on C's points. -/
def UniformOneGeneratedBound (K : Class.{u,v} L) (m : ℕ) : Prop :=
  ∀ {X : Type v} [Finite X] (D : Structure L X), K D → D.Total →
    D.OneGenerated → Nat.card X ≤ m

theorem singleton_card_le [Finite V] (C : Structure L V) {K : Class.{u,v} L}
    (hCompleted : CompletedClass K) (hK : C.IrreduciblesIn K)
    {m : ℕ} (hm : UniformOneGeneratedBound K m) (x : V) :
    Nat.card (C.closureAt x) ≤ m :=
  hm (C.singletonStructure x) (C.singleton_mem_class hK x)
    (hCompleted _ (C.singleton_mem_class hK x)) (C.singleton_oneGenerated x)

/-- Unary closure is a union of the singleton closures. An actual
injection into their finite disjoint union proves the cardinal estimate. -/
theorem closure_card_le_of_singleton [Finite V] (C : Structure L V) {m : ℕ}
    (hm : ∀ x : V, Nat.card (C.closureAt x) ≤ m) (B : Finset V) :
    Nat.card (C.closure (B : Set V)) ≤ m * B.card := by
  classical
  let : Fintype (C.closure (B : Set V)) := Fintype.ofFinite _
  let : ∀ b : ↥B, Fintype (C.closureAt b.val) := fun _ => Fintype.ofFinite _
  have hcover (y : C.closure (B : Set V)) : ∃ b : ↥B, y.val ∈ C.closureAt b.val := by
    obtain ⟨x,hx,hxy⟩ := y.property
    exact ⟨⟨x,hx⟩,x,rfl,hxy⟩
  let f : C.closure (B : Set V) → Σ b : ↥B, C.closureAt b.val := fun y =>
    ⟨(hcover y).choose,⟨y.val,(hcover y).choose_spec⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun p : Σ b : ↥B, C.closureAt b.val => p.2.val) hab)
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at hcard
  calc
    Nat.card (C.closure (B : Set V)) = Fintype.card (C.closure (B : Set V)) := Nat.card_eq_fintype_card
    _ ≤ ∑ b : ↥B, Fintype.card (C.closureAt b.val) := hcard
    _ ≤ ∑ _b : ↥B, m := Finset.sum_le_sum (fun b _ => by simpa only [Nat.card_eq_fintype_card] using hm b.val)
    _ = m * B.card := by simp [Nat.mul_comm]

theorem closure_card_le [Finite V] (C : Structure L V) {K : Class.{u,v} L}
    (hCompleted : CompletedClass K) (hK : C.IrreduciblesIn K)
    {m : ℕ} (hm : UniformOneGeneratedBound K m) (B : Finset V) :
    Nat.card (C.closure (B : Set V)) ≤ m * B.card :=
  C.closure_card_le_of_singleton (C.singleton_card_le hCompleted hK hm) B

/-- The no-constants convention includes the empty generator case exactly. -/
theorem closure_card_empty (C : Structure L V) : Nat.card (C.closure ∅) = 0 := by
  rw [C.closure_empty]
  simp

/-- Empty input sorts and an empty source require no nonemptiness gate. -/
theorem total_of_isEmpty [IsEmpty V] (C : Structure L V) : C.Total := by
  intro F x
  exact isEmptyElim x

theorem satisfies_of_isEmpty [IsEmpty V] (C : Structure L V) {i j : L.Sorts}
    (t s : Term L i j) : C.Satisfies t s := by
  intro x
  exact isEmptyElim x

theorem closure_card_of_isEmpty [IsEmpty V] (C : Structure L V) (B : Set V) :
    Nat.card (C.closure B) = 0 := by
  have h : C.closure B = ∅ := by ext x; exact isEmptyElim x
  rw [h]
  simp

/-- A supplied zero completed-one-generator bound forces the source empty. -/
theorem isEmpty_of_zero_bound [Finite V] (C : Structure L V) {K : Class.{u,v} L}
    (hCompleted : CompletedClass K) (hK : C.IrreduciblesIn K)
    (hm : UniformOneGeneratedBound K 0) : IsEmpty V := by
  constructor
  intro x
  let : Nonempty (C.closureAt x) := ⟨⟨x,C.mem_closureAt x⟩⟩
  exact (Nat.not_lt_of_ge (C.singleton_card_le hCompleted hK hm x)) Nat.card_pos

/-- C29 / the second source export. All completed diagrams are ACTUAL
members, all identities have ONE variable, and the size clause remains
conditional on the supplied completed-one-generator class bound. -/
theorem hn_irreducible_forces_unary_admissible [Finite V] (C : Structure L V)
    {K : Class.{u,v} L} (hCompleted : CompletedClass K) (hK : C.IrreduciblesIn K) :
    (∀ x : V, K (C.singletonStructure x) ∧ (C.singletonStructure x).OneGenerated) ∧
    C.Total ∧
    (∀ {i j : L.Sorts} (t s : Term L i j), ValidInClass K t s → C.Satisfies t s) ∧
    C.FullUnaryAdmissible K ∧
    ∀ m : ℕ, UniformOneGeneratedBound K m →
      (∀ x : V, Nat.card (C.closureAt x) ≤ m) ∧
      (∀ B : Finset V, Nat.card (C.closure (B : Set V)) ≤ m * B.card) ∧
      (m = 0 → IsEmpty V) := by
  refine ⟨fun x => ⟨C.singleton_mem_class hK x,C.singleton_oneGenerated x⟩,
    C.total_of_irreducibles hCompleted hK,
    fun t s h => C.identities_of_irreducibles hK t s h,
    C.full_unary_admissible hCompleted hK,?_⟩
  intro m hm
  refine ⟨C.singleton_card_le hCompleted hK hm,
    C.closure_card_le hCompleted hK hm,?_⟩
  rintro rfl
  exact C.isEmpty_of_zero_bound hCompleted hK hm

end CCO.UnarySupport.Structure
