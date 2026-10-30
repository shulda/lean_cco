import CCO.FiniteFibres.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Count the ACTUAL real outside types by diversity spoke vectors. The
finite-fibre bound is an explicit local hypothesis here; the final receiving
source theorem supplies it from the independently proved finite CCO theorem. -/
universe v w t
namespace CCO.FiniteFibres.Real
open RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]
variable (A : Finset M)

abbrev SpokeType := ↥A → Atom S

noncomputable instance spokeTypeFintype : Fintype (SpokeType S A) := by
  letI := S.finiteAtom () ()
  infer_instance

def FiniteType := {q : SpokeType S A // (FibreSet S A q).Finite}

noncomputable instance finiteTypeFintype : Fintype (FiniteType S A) := by
  classical
  unfold FiniteType
  exact Fintype.ofFinite _

instance selectedFibreFinite (q : FiniteType S A) : Finite (FibreSet S A q.val) :=
  q.property.to_subtype

/-- Literal fibre labels, including unrealized labels, need no consistency
oracle. The number of realized labels is at most this full function type. -/
theorem spoke_type_count (hA : A.Nonempty) :
    Nat.card (SpokeType S A) = (Nat.card (Atom S)) ^ A.card := by
  letI := S.finiteAtom () ()
  simp only [Nat.card_eq_fintype_card,SpokeType,Fintype.card_fun,Fintype.card_coe]

theorem finite_type_count (hA : A.Nonempty) :
    Nat.card (FiniteType S A) ≤ (Nat.card (Atom S)) ^ A.card := by
  rw [←spoke_type_count S A hA]
  exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

abbrev AlgebraicCover := ↥A ⊕ (Σ q : FiniteType S A, FibreSet S A q.val)

noncomputable instance algebraicCoverFintype : Fintype (AlgebraicCover S A) :=
  Fintype.ofFinite _

variable {G : Type t} [Group G] [MulAction G M]

def coverPoint (H : HomogeneousSource S G) : AlgebraicCover S A → ↥(acl S A)
  | Sum.inl a => ⟨a.val,parameter_mem_acl S A a.property⟩
  | Sum.inr ⟨q,x⟩ => ⟨x.val,by
      rw [acl_eq_anchor_union_finite_fibres S H A]
      exact Or.inr ⟨q.val,q.property,x.property⟩⟩

theorem coverPoint_surjective (H : HomogeneousSource S G) :
    Function.Surjective (coverPoint S A H) := by
  intro x
  by_cases hx : x.val ∈ A
  · exact ⟨Sum.inl ⟨x.val,hx⟩,Subtype.ext rfl⟩
  · let q := spokes S A x.val hx
    have hq : (FibreSet S A q).Finite :=
      (algebraic_iff_finite_fibre S H A x.val hx).mp x.property
    exact ⟨Sum.inr ⟨⟨q,hq⟩,fibrePoint S A x.val hx⟩,Subtype.ext rfl⟩

theorem acl_finite (H : HomogeneousSource S G) : (acl S A).Finite := by
  have hi : Finite ↥(acl S A) := Finite.of_surjective (coverPoint S A H)
    (coverPoint_surjective S A H)
  exact Set.finite_coe_iff.mp hi

theorem cover_card : Nat.card (AlgebraicCover S A) =
    A.card + ∑ q : FiniteType S A, Nat.card (FibreSet S A q.val) := by
  rw [Nat.card_sum,Nat.card_sigma]
  congr 1
  simp

/-- C38: count anchors and disjoint finite actual fibres over a NONEMPTY
real base. No arbitrary imaginary/type space or stronger closure is used. -/
theorem acl_card_bound (H : HomogeneousSource S G) (hA : A.Nonempty)
    (hFibres : ∀ q : FiniteType S A,
      Nat.card (FibreSet S A q.val) ≤ 2 ^ Nat.card (Atom S)) :
    Nat.card ↥(acl S A) ≤ A.card + (Nat.card (Atom S)) ^ A.card * 2 ^ Nat.card (Atom S) := by
  calc
    Nat.card ↥(acl S A) ≤ Nat.card (AlgebraicCover S A) :=
      Nat.card_le_card_of_surjective (coverPoint S A H) (coverPoint_surjective S A H)
    _ = A.card + ∑ q : FiniteType S A, Nat.card (FibreSet S A q.val) := cover_card S A
    _ ≤ A.card + ∑ _q : FiniteType S A, 2 ^ Nat.card (Atom S) := by
      exact Nat.add_le_add_left (Finset.sum_le_sum (fun q _ => hFibres q)) _
    _ = A.card + Nat.card (FiniteType S A) * 2 ^ Nat.card (Atom S) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ A.card + (Nat.card (Atom S)) ^ A.card * 2 ^ Nat.card (Atom S) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (finite_type_count S A hA)) _

/-- Completeness makes a zero-diversity inhabited source a singleton, so
there are no outside types over a nonempty real base. -/
theorem subsingleton_of_zero_palette (hD : Nat.card (Atom S) = 0) : Subsingleton M := by
  letI := S.finiteAtom () ()
  refine ⟨fun x y => ?_⟩
  by_contra hxy
  obtain ⟨a,_⟩ := col_some_of_ne S hxy
  have hp : 0 < Nat.card (Atom S) := Nat.card_pos_iff.mpr ⟨⟨a⟩,inferInstance⟩
  omega

theorem no_outside_of_zero_palette (hD : Nat.card (Atom S) = 0) (hA : A.Nonempty) :
    ∀ x : M, x ∈ A := by
  letI := subsingleton_of_zero_palette S hD
  obtain ⟨a,ha⟩ := hA
  intro x
  exact Subsingleton.elim a x ▸ ha

end CCO.FiniteFibres.Real
