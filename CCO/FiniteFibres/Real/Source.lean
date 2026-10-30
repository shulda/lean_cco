import CCO.FiniteFibres.Real.Count
import CCO.FiniteFibres.Real.PaletteChain
import CCO.FiniteFibres.Real.Definability

/-! Assemble the actual REAL fibre source conclusions from the independent
finite symmetric CCO cardinal theorem. `FiniteAtomicCard` is a transparent
interface for that one theorem, not a new mathematical assumption: the final
B042 export instantiates it by its proved generic finite-target theorem. -/
universe v w t z
namespace CCO.FiniteFibres.Real
open RealHull.Geometry

def FiniteAtomicCard : Prop :=
  ∀ {F : Type v} (T : AtomicSource.{0,v,w} Unit (fun _ => F))
    [Finite F] [Nonempty F] {K : Type v} [Group K] [MulAction K F],
    HomogeneousSource T K → SemanticCCO.{0,v,0,w} T →
      ∃ m : ℕ, Nat.card F = 2 ^ m ∧ m ≤ Nat.card (T.Atom () ())

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]
variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
include H cco

/-- C30: selected original C09/C10 providers, before ANY finite Hasse or
finite cardinal theorem is used. -/
theorem fibre_source_properties (A : Finset M) (q : ↥A → Atom S)
    [Nonempty (FibreSet S A q)] :
    HomogeneousSource (fibreSource S A q) (inducedAut S () (FibreSet S A q)) ∧
      SemanticCCO.{0,v,z,w} (fibreSource S A q) :=
  ⟨fibre_homogeneous S A q H,fibre_semanticCCO S A q H cco⟩

theorem finite_fibre_power (hCard : FiniteAtomicCard.{v,w})
    (A : Finset M) (q : ↥A → Atom S)
    [Nonempty (FibreSet S A q)] [Finite (FibreSet S A q)] :
    ∃ m : ℕ, Nat.card (FibreSet S A q) = 2 ^ m ∧ m ≤ Nat.card (Atom S) := by
  obtain ⟨m,hm,hbound⟩ := hCard (fibreSource S A q)
    (fibre_homogeneous S A q H) (fibre_semanticCCO S A q H cco)
  exact ⟨m,hm,hbound.trans (fibre_palette_card_le S A q)⟩

theorem selected_fibre_bound (hCard : FiniteAtomicCard.{v,w})
    (A : Finset M) (q : FiniteType S A) :
    Nat.card (FibreSet S A q.val) ≤ 2 ^ Nat.card (Atom S) := by
  classical
  by_cases hq : Nonempty (FibreSet S A q.val)
  · letI := hq
    obtain ⟨m,hm,hbound⟩ := finite_fibre_power S H cco hCard A q.val
    rw [hm]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hbound
  · letI : IsEmpty (FibreSet S A q.val) := not_nonempty_iff.mp hq
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _

theorem uniform_real_bound (hCard : FiniteAtomicCard.{v,w})
    (A : Finset M) (hA : A.Nonempty) :
    (acl S A).Finite ∧
      Nat.card ↥(acl S A) ≤ A.card + (Nat.card (Atom S)) ^ A.card * 2 ^ Nat.card (Atom S) :=
  ⟨acl_finite S A H,acl_card_bound S A H hA (selected_fibre_bound S H cco hCard A)⟩

/-- The inhabited finite empty-base branch uses the finite theorem directly,
without evaluating a spoke count or `0^0`. -/
theorem empty_finite_power (hCard : FiniteAtomicCard.{v,w}) [Finite M] :
    acl S ∅ = Set.univ ∧
      ∃ m : ℕ, Nat.card M = 2 ^ m ∧ m ≤ Nat.card (Atom S) ∧ Nat.card M ≤ 2 ^ Nat.card (Atom S) := by
  letI : Nonempty M := S.nonemptySort ()
  obtain ⟨m,hm,hbound⟩ := hCard S (fullHomogeneous S H) cco
  refine ⟨acl_finite_source S ∅,m,hm,hbound,?_⟩
  rw [hm]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hbound

omit H cco in
theorem zero_palette_singleton (hD : Nat.card (Atom S) = 0) : Nat.card M = 1 := by
  letI := subsingleton_of_zero_palette S hD
  letI : Unique M := ⟨⟨Classical.choice (S.nonemptySort ())⟩,fun x => Subsingleton.elim _ _⟩
  exact Nat.card_unique

/-- The complete source-level real algebraicity package. The caller supplies
the independently proved FINITE TARGET theorem exactly once. -/
theorem real_source_package (hCard : FiniteAtomicCard.{v,w}) (A : Finset M) :
    (∀ q : ↥A → Atom S, ∀ [Nonempty (FibreSet S A q)] [Finite (FibreSet S A q)],
      ∃ m : ℕ, Nat.card (FibreSet S A q) = 2 ^ m ∧ m ≤ Nat.card (Atom S)) ∧
    (acl S A).Finite ∧
    (A.Nonempty → Nat.card ↥(acl S A) ≤
      A.card + (Nat.card (Atom S)) ^ A.card * 2 ^ Nat.card (Atom S)) ∧
    (∀ [Infinite M], acl S ∅ = ∅) ∧
    (∀ [Finite M], acl S ∅ = Set.univ ∧
      ∃ m : ℕ, Nat.card M = 2 ^ m ∧ m ≤ Nat.card (Atom S) ∧ Nat.card M ≤ 2 ^ Nat.card (Atom S)) ∧
    (∀ x : M, (∃ Z : Set M, Z.Finite ∧
      (A : Set M).Definable₁ (originalLanguage S) Z ∧ x ∈ Z) ↔ x ∈ acl S A) := by
  exact ⟨fun q _ _ => finite_fibre_power S H cco hCard A q,
    acl_finite S A H,
    fun hA => (uniform_real_bound S H cco hCard A hA).2,
    (by intro hi; exact empty_acl_infinite S H),
    (by intro hi; exact empty_finite_power S H cco hCard),
    usual_algebraic_iff S A H⟩

end CCO.FiniteFibres.Real
