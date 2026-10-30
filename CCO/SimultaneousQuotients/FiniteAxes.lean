import CCO.SimultaneousQuotients.FullAut

/-! The selected new finite-axis consequence, using the FULL actual quotient
binary automorphism group. All generic whole-axis and Goursat arguments remain
owned by accepted B017; here their source hypotheses are actually discharged. -/

universe u v w t z a
namespace CCO.SimultaneousQuotients
open RawExact
noncomputable section
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (J : ∀ i, Setoid (X i)) (E : ∀ i, NonemptyExact S i i)
variable (represents : ∀ i, evaluate S (E i).words = (J i).r)
variable [∀ i, Countable (X i)]
include cco

abbrev fullBinary := FullAut.binary (source S H J E represents)

/-- The finite-axis provider is applied to this actual full binary quotient,
not to the generally smaller image of the earlier source action. -/
theorem fullBinary_homogeneous : (fullBinary S H J E represents).Homogeneous := by
  letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
  exact FullAut.homogeneous (source S H J E represents)
    (homogeneous S H J E represents cco)

variable {I : Type z} (origin : I ↪ ι)
variable (hFinite : ∀ i, Finite (Carrier J (origin i)))

abbrev entireAxes := FullAut.axes (source S H J E represents) origin hFinite

theorem entire_axis_surjective (i : I) :
    Function.Surjective ((entireAxes S H J E represents origin hFinite).restrict i) :=
  (entireAxes S H J E represents origin hFinite).restrict_surjective
    (fullBinary_homogeneous S H cco J E represents) i

theorem entire_pair_subdirect (i j : I) :
    (∀ x : (entireAxes S H J E represents origin hFinite).Intrinsic i,
      ∃ y, (x, y) ∈ (entireAxes S H J E represents origin hFinite).actualPair i j) ∧
    (∀ y : (entireAxes S H J E represents origin hFinite).Intrinsic j,
      ∃ x, (x, y) ∈ (entireAxes S H J E represents origin hFinite).actualPair i j) :=
  ⟨(entireAxes S H J E represents origin hFinite).actual_pair_subdirect_left
      (fullBinary_homogeneous S H cco J E represents) i j,
   (entireAxes S H J E represents origin hFinite).actual_pair_subdirect_right
      (fullBinary_homogeneous S H cco J E represents) i j⟩

theorem entire_finite_projection (A : Finset I)
    (p : ∀ i : ↥A, (entireAxes S H J E represents origin hFinite).Intrinsic i.val) :
    p ∈ (entireAxes S H J E represents origin hFinite).actualImage A ↔
      ∀ i j : ↥A, i.val ≠ j.val → (p i, p j) ∈
        (entireAxes S H J E represents origin hFinite).actualPair i.val j.val :=
  (entireAxes S H J E represents origin hFinite).finite_projection
    (fullBinary_homogeneous S H cco J E represents) A p

variable {V : I → Type a} [∀ i, AddCommGroup (V i)]
variable [∀ i, Module FiniteKernel.F2 (V i)]
variable (e : ∀ i, Multiplicative (V i) ≃*
  (entireAxes S H J E represents origin hFinite).Intrinsic i)

theorem entire_pair_goursat (i j : I) (x : V i) (y : V j) :
    (e i (Multiplicative.ofAdd x), e j (Multiplicative.ofAdd y)) ∈
      (entireAxes S H J E represents origin hFinite).actualPair i j ↔
    (entireAxes S H J E represents origin hFinite).pairLeft e i j x =
      (entireAxes S H J E represents origin hFinite).pairRight e
        (fullBinary_homogeneous S H cco J E represents) i j y :=
  (entireAxes S H J E represents origin hFinite).actual_pair_goursat e
    (fullBinary_homogeneous S H cco J E represents) i j x y

theorem entire_linear_image (A : Finset I) :
    (entireAxes S H J E represents origin hFinite).linearImage e A =
      ((entireAxes S H J E represents origin hFinite).checkMap e
        (fullBinary_homogeneous S H cco J E represents) A).ker :=
  (entireAxes S H J E represents origin hFinite).linearImage_eq_check_kernel e
    (fullBinary_homogeneous S H cco J E represents) A

variable [∀ i, FiniteDimensional FiniteKernel.F2 (V i)]

/-- Only the finite coordinate IMAGE is counted; full Aut(Q) can be infinite.
The elementary-abelian intrinsic representations are the explicit extra premise
`e`. They are not inferred from CCO or full exactness. -/
theorem entire_image_rank_count (A : Finset I) :
    Nat.card ((entireAxes S H J E represents origin hFinite).actualImage A) =
      2 ^ ((∑ i : ↥A, Module.finrank FiniteKernel.F2 (V i.val)) -
        Module.finrank FiniteKernel.F2
          ((entireAxes S H J E represents origin hFinite).checkMap e
            (fullBinary_homogeneous S H cco J E represents) A).range) :=
  (entireAxes S H J E represents origin hFinite).actualImage_rank_count e
    (fullBinary_homogeneous S H cco J E represents) A

end
end CCO.SimultaneousQuotients
