import CCO.FiniteKernel.Named.LinearSource
import CCO.FiniteKernel.Named.RankCount
import Mathlib.Data.Fintype.Pi

/-! The actual finite full-group IMAGE on entire named axes is the kernel
of its actual unordered pair checks. Rank-nullity counts THIS finite image,
never the full potentially infinite original automorphism group. -/

universe u v w z a
namespace CCO.FiniteKernel.NamedAxes
noncomputable section

variable {X : Type u} {S : BinaryStructure.{u,v,w} X} {I : Type z}
variable (P : NamedAxes S I)
variable {V : I → Type a} [∀ i,AddCommGroup (V i)] [∀ i,Module F2 (V i)]
variable (e : ∀ i,Multiplicative (V i) ≃* P.Intrinsic i)

def coordinateCode (_P : NamedAxes S I) (A : Finset I) (i : ↥A) : ℕ := (Fintype.equivFin ↥A i).val

theorem coordinateCode_injective (A : Finset I) : Function.Injective (P.coordinateCode A) := by
  intro i j he
  exact (Fintype.equivFin ↥A).injective (Fin.ext he)

/-- Exactly one orientation of each distinct pair of selected axes. This
uses only an enumeration of the FINITE selected set; no order on all I.
-/
def CheckPairs (A : Finset I) := {ij : ↥A × ↥A // P.coordinateCode A ij.1 < P.coordinateCode A ij.2}

abbrev CheckSpace (A : Finset I) (p : P.CheckPairs A) :=
  P.PairSpace e p.val.1.val p.val.2.val

def pairRow (H : S.Homogeneous) (A : Finset I) (p : P.CheckPairs A) :
    (∀ i : ↥A,V i.val) →ₗ[F2] P.CheckSpace e A p :=
  (P.pairLeft e p.val.1.val p.val.2.val).comp (LinearMap.proj p.val.1) +
    (P.pairRight e H p.val.1.val p.val.2.val).comp (LinearMap.proj p.val.2)

def checkMap (H : S.Homogeneous) (A : Finset I) :
    (∀ i : ↥A,V i.val) →ₗ[F2] (∀ p : P.CheckPairs A,P.CheckSpace e A p) :=
  LinearMap.pi (P.pairRow e H A)

theorem pairRow_eq_zero (H : S.Homogeneous) (A : Finset I) (p : P.CheckPairs A)
    (x : ∀ i : ↥A,V i.val) :
    P.pairRow e H A p x = 0 ↔
      (e p.val.1.val (Multiplicative.ofAdd (x p.val.1)),
        e p.val.2.val (Multiplicative.ofAdd (x p.val.2))) ∈
          P.actualPair p.val.1.val p.val.2.val := by
  change P.pairLeft e _ _ (x p.val.1) + P.pairRight e H _ _ (x p.val.2) = 0 ↔ _
  rw [← ZModModule.sub_eq_add,sub_eq_zero]
  exact (P.actual_pair_goursat e H _ _ _ _).symm

theorem actualPair_swap (i j : I) (a : P.Intrinsic i) (b : P.Intrinsic j) :
    (a,b) ∈ P.actualPair i j ↔ (b,a) ∈ P.actualPair j i := by
  constructor <;> rintro ⟨g,hg⟩ <;> exact ⟨g,congrArg Prod.swap hg⟩

/-- This is the actual source TQ3 instantiated with the genuine A07 group
representations and canonical subdirect Goursat checks. No finite projection
or linearity provider remains as an assumption.
-/
theorem linearImage_eq_check_kernel (H : S.Homogeneous) (A : Finset I) :
    P.linearImage e A = (P.checkMap e H A).ker := by
  ext x
  rw [P.mem_linearImage,P.finite_projection H]
  change (∀ i j : ↥A,i.val ≠ j.val →
      (e i.val (Multiplicative.ofAdd (x i)),e j.val (Multiplicative.ofAdd (x j))) ∈
        P.actualPair i.val j.val) ↔ (fun p => P.pairRow e H A p x) = 0
  rw [funext_iff]
  constructor
  · intro hx p
    apply (P.pairRow_eq_zero e H A p x).mpr
    exact hx p.val.1 p.val.2 (fun he =>
      (Nat.ne_of_lt p.property) (congrArg (P.coordinateCode A) (Subtype.ext he)))
  · intro hx i j hij
    have hne : P.coordinateCode A i ≠ P.coordinateCode A j := by
      intro he
      exact hij (congrArg Subtype.val (P.coordinateCode_injective A he))
    by_cases hlt : P.coordinateCode A i < P.coordinateCode A j
    · exact (P.pairRow_eq_zero e H A ⟨(i,j),hlt⟩ x).mp (hx ⟨(i,j),hlt⟩)
    · have hgt : P.coordinateCode A j < P.coordinateCode A i := by omega
      exact (P.actualPair_swap i.val j.val _ _).mpr
        ((P.pairRow_eq_zero e H A ⟨(j,i),hgt⟩ x).mp (hx ⟨(j,i),hgt⟩))

/-- The finite IMAGE has an actual finiteness proof independently of Nat.card.
No finiteness is asserted for the original full Gamma or the complement.
-/
theorem actualImage_finite (A : Finset I) : Finite (P.actualImage A) := by
  classical
  letI : ∀ i : ↥A,Fintype (P.Intrinsic i.val) := fun _ => Fintype.ofFinite _
  change Finite {g : ∀ i : ↥A,P.Intrinsic i.val // g ∈ P.actualImage A}
  infer_instance

variable [∀ i,FiniteDimensional F2 (V i)]

/-- C19 counts the finite actual full-group restriction image. The rows are
the canonical UNORDERED actual pair checks; empty/singleton S have no rows.
-/
theorem actualImage_rank_count (H : S.Homogeneous) (A : Finset I) :
    Nat.card (P.actualImage A) =
      2 ^ ((∑ i : ↥A,Module.finrank F2 (V i.val)) -
        Module.finrank F2 (P.checkMap e H A).range) := by
  calc
    Nat.card (P.actualImage A) = Nat.card (P.linearImage e A) :=
      Nat.card_congr (P.linearImageEquivActual e A).symm
    _ = Nat.card (P.checkMap e H A).ker := by rw [P.linearImage_eq_check_kernel e H A]
    _ = _ := Named.check_kernel_card (fun i : ↥A => V i.val) (P.checkMap e H A)

end
end CCO.FiniteKernel.NamedAxes
