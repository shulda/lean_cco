import CCO.ParityHasse.Relative.Exact
import CCO.ParityHasse.Relative.TwoSheet
import Mathlib.Order.Preorder.Finite

/-! Finite maximal ORIGINAL exact candidates and their genuine two-sheet
gates. This file imports neither relative closure separation nor Hasse;
U itself is never assumed exact. -/
universe u v w t
namespace CCO.ParityHasse.Relative
open Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

def Candidate (Y U K : ColourEq S i) : Prop := Exact S K ∧ Y ≤ K ∧ K ⊓ U = Y

/-- C22: the finite candidate set contains Y; maximality ranges over all
original full-exact equivalences, not just a chosen list of presentations. -/
theorem exists_maximal_candidate (Y U : ColourEq S i) (hY : Exact S Y) (hYU : Y ≤ U) :
    ∃ K, Maximal (Candidate S Y U) K := by
  have hy : Candidate S Y U Y := ⟨hY,le_rfl,inf_eq_left.mpr hYU⟩
  obtain ⟨K,_,hK⟩ := Finite.exists_le_maximal hy
  exact ⟨K,hK⟩

def gate (K U Y : ColourEq S i) : Rel (X i) := mul (mul K (odd Y.val U.val)) K

 theorem gate_eq_complement (Y U K : ColourEq S i) (hYK : Y ≤ K)
    (hKU : K ⊓ U = Y) :
    gate S K U Y = odd K.val (ColourEq.join S H K U).val := by
  funext x y; apply propext
  constructor
  · rintro ⟨v,⟨u,hxu,huv⟩,hvy⟩
    have hF : (ColourEq.join S H K U) x y := by
      have hK : K.val ≤ K.val ⊔ U.val := le_sup_left
      have hU : U.val ≤ K.val ⊔ U.val := le_sup_right
      exact (K.val ⊔ U.val).trans (hK hxu) ((K.val ⊔ U.val).trans (hU huv.1) (hK hvy))
    refine ⟨hF,?_⟩
    intro hxy
    have huk : K u v := K.val.trans (K.val.symm hxu) (K.val.trans hxy (K.val.symm hvy))
    have huy : Y u v := by rw [← hKU]; exact ⟨huk,huv.1⟩
    exact huv.2 huy
  · rintro ⟨hF,hnK⟩
    obtain ⟨z,hxz,hzy⟩ := (sup_relation_iff S H K U x y).mp hF
    refine ⟨y,⟨z,hxz,hzy,?_⟩,K.val.refl y⟩
    intro hYzy
    exact hnK (K.val.trans hxz (hYK hYzy))

include H in
 theorem gate_bisaturated (Y U K : ColourEq S i) (hYK : Y ≤ K) (hKU : K ⊓ U = Y) :
    Bisaturated K.val (gate S K U Y) := by
  rw [gate_eq_complement S H Y U K hYK hKU]
  exact odd_bisaturated K.val (ColourEq.join S H K U).val le_sup_left

include H cco in
 theorem gate_exact (Y U K : ColourEq S i) (hK : Exact S K)
    (hO : Exact S (odd Y.val U.val)) : Exact S (gate S K U Y) :=
  exact_comp S H cco (exact_comp S H cco hK hO) hK

 theorem gate_partition (Y U K : ColourEq S i) (hYK : Y ≤ K) (hKU : K ⊓ U = Y)
    (x y : X i) :
    (ColourEq.join S H K U) x y ↔ K x y ∨ gate S K U Y x y := by
  rw [gate_eq_complement S H Y U K hYK hKU]
  constructor
  · intro h
    by_cases hk : K x y
    · exact Or.inl hk
    · exact Or.inr ⟨h,hk⟩
  · rintro (h|h)
    · exact (show K.val ≤ K.val ⊔ U.val from le_sup_left) h
    · exact h.1

include H in
 theorem gate_disjoint (Y U K : ColourEq S i) (hYK : Y ≤ K) (hKU : K ⊓ U = Y) :
    ∀ x y, gate S K U Y x y → ¬K x y := by
  rw [gate_eq_complement S H Y U K hYK hKU]
  exact fun _ _ h => h.2

include H in
 theorem gate_square (Y U K : ColourEq S i) (hYK : Y ≤ K) (hKU : K ⊓ U = Y)
    (a : X i) (htwo : relativeIndex Y.val U.val a = 2) :
    mul (gate S K U Y) (gate S K U Y) = K := by
  rw [gate_eq_complement S H Y U K hYK hKU]
  apply odd_square K.val (ColourEq.join S H K U).val le_sup_left
  intro x
  exact (relativeIndex_uniform S H K (ColourEq.join S H K U) a x).symm.trans
    (maximal_transposition_index S H Y U K hKU a htwo)

include H in
/-- C24: maximality is among ALL original exact Z. No closure separation,
exact lattice distributivity, exactness of U, or quotient descent is used. -/
theorem gate_dominance (Y U K : ColourEq S i) (hYU : Y ≤ U)
    (a : X i) (htwo : relativeIndex Y.val U.val a = 2)
    (hmax : Maximal (Candidate S Y U) K)
    (Z : ColourEq S i) (hZ : Exact S Z) (hKZ : K < Z) :
    gate S K U Y ≤ Z := by
  have cov := covBy_of_relativeIndex_two S H Y U hYU a htwo
  have hyz : Y ≤ Z := hmax.1.2.1.trans hKZ.le
  have hz : Z ⊓ U = Y ∨ Z ⊓ U = U := cov.eq_or_eq (le_inf hyz hYU) inf_le_right
  rcases hz with hz | hz
  · have hc : Candidate S Y U Z := ⟨hZ,hyz,hz⟩
    exact False.elim (hKZ.not_ge (hmax.2 hc hKZ.le))
  · intro x y hxy
    obtain ⟨v,⟨u,hxu,huv⟩,hvy⟩ := hxy
    have huvZ : Z u v := by
      have hzU : U ≤ Z := by rw [← hz]; exact inf_le_left
      exact hzU huv.1
    exact Z.val.trans (hKZ.le hxu) (Z.val.trans huvZ (hKZ.le hvy))

/-- All old-level conclusions packaged without making an arbitrary old
relation functional or requiring the upper parity equivalence exact. -/
structure MaximalGate (Y U : ColourEq S i) where
  kernel : ColourEq S i
  maximal : Maximal (Candidate S Y U) kernel
  exact : Exact S (gate S kernel U Y)
  bisaturated : Bisaturated kernel.val (gate S kernel U Y)
  square : mul (gate S kernel U Y) (gate S kernel U Y) = kernel
  split : ∀ x y, (ColourEq.join S H kernel U) x y ↔
    kernel x y ∨ gate S kernel U Y x y
  disjoint : ∀ x y, gate S kernel U Y x y → ¬kernel x y
  relative_index : relativeIndex kernel.val (ColourEq.join S H kernel U).val (Classical.choice (S.nonemptySort i)) = 2
  dominant : ∀ Z : ColourEq S i, Exact S Z → kernel < Z → gate S kernel U Y ≤ Z

include H cco in
/-- C21–24 source theorem: genuine original maximal exact gate. -/
theorem exists_maximalGate (Y U : ColourEq S i) (hY : Exact S Y) (hYU : Y ≤ U)
    (hO : Exact S (odd Y.val U.val)) (a : X i)
    (htwo : relativeIndex Y.val U.val a = 2) : Nonempty (MaximalGate S H Y U) := by
  obtain ⟨K,hK⟩ := exists_maximal_candidate S Y U hY hYU
  refine ⟨⟨K,hK,gate_exact S H cco Y U K hK.1.1 hO,
    gate_bisaturated S H Y U K hK.1.2.1 hK.1.2.2,
    gate_square S H Y U K hK.1.2.1 hK.1.2.2 a htwo,
    gate_partition S H Y U K hK.1.2.1 hK.1.2.2,
    gate_disjoint S H Y U K hK.1.2.1 hK.1.2.2,?_,?_⟩⟩
  · exact (relativeIndex_uniform S H K (ColourEq.join S H K U) a _).symm.trans
      (maximal_transposition_index S H Y U K hK.1.2.2 a htwo)
  · exact gate_dominance S H Y U K hYU a htwo hK

end CCO.ParityHasse.Relative
