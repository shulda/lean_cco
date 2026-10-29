import CCO.FiniteLift.OwnerCover
import CCO.FiniteLift.Closure
import Mathlib.Data.Set.Card

/-! B029 C19 quantitative completeness. ANY real K-class above a common
owner projects ONTO its ENTIRE H-owner fibre. Uniform finite K class size
therefore bounds every owner-cover fibre and every complete finite packet. -/

universe v w t
namespace CCO.FiniteLift
variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A]
variable (HS : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (K H : ExactKernel S G)
namespace OwnerCover

/-- The map is the actual H projection restricted to ONE whole K-class;
its codomain is the complete owner-cover fibre, with no representatives removed. -/
def classToOwnerFibre (q : K.Q) :
    {x : A // K.proj x = q} →
      ((rH S HS cco K H) ⁻¹' {rK S HS cco K H q}) :=
  fun x => ⟨H.proj x.val, by
    change rH S HS cco K H (H.proj x.val) = rK S HS cco K H q
    exact congrArg (rK S HS cco K H) x.property⟩

/-- Complete incidence proves actual surjectivity for EVERY chosen K-class. -/
theorem classToOwnerFibre_onto (q : K.Q) :
    Function.Surjective (classToOwnerFibre S HS cco K H q) := by
  intro b
  have hb : rK S HS cco K H q = rH S HS cco K H b.val := b.property.symm
  obtain ⟨a, ha, ha'⟩ := class_incidence S HS cco K H q b.val hb
  exact ⟨⟨a, ha⟩, Subtype.ext ha'⟩

/-- Each COMPLETE owner fibre has at most as many elements as ANY real
K-class over it. Neither class transversals nor fibre permutations are assumed. -/
theorem fibre_card_le_any_class (finiteK : K.FiniteClasses) (q : K.Q) :
    Nat.card ((rH S HS cco K H) ⁻¹' {rK S HS cco K H q}) ≤
      Nat.card {x : A // K.proj x = q} := by
  letI : Finite {x : A // K.proj x = q} := (K.finite_fibre finiteK q).to_subtype
  exact Nat.card_le_card_of_surjective (classToOwnerFibre S HS cco K H q)
    (classToOwnerFibre_onto S HS cco K H q)

/-- The uniform finite K-class cardinal k bounds every common-owner fibre. -/
theorem fibre_card_le (finiteK : K.FiniteClasses) (k : ℕ)
    (hk : ∀ q : K.Q, Nat.card {x : A // K.proj x = q} = k)
    (c : (J S HS cco K H).Q) :
    Nat.card ((rH S HS cco K H) ⁻¹' {c}) ≤ k := by
  obtain ⟨q, rfl⟩ := toJoinK_onto S HS cco K H c
  exact (fibre_card_le_any_class S HS cco K H finiteK q).trans_eq (hk q)

/-- The complete inverse owner packet has at most k times the number of
its coarse owners. The empty packet is included in the same quantified bound. -/
theorem complete_packet_card_le (finiteK : K.FiniteClasses) (k : ℕ)
    (hk : ∀ q : K.Q, Nat.card {x : A // K.proj x = q} = k)
    (Bbar : Set (J S HS cco K H).Q) (finiteBbar : Bbar.Finite) :
    Nat.card ((rH S HS cco K H) ⁻¹' Bbar) ≤ k * Nat.card Bbar := by
  classical
  letI : Fintype Bbar := finiteBbar.fintype
  letI : ∀ c : Bbar, Finite ((rH S HS cco K H) ⁻¹' {c.val}) :=
    fun c => (fibre_finite S HS cco K H finiteK c.val).to_subtype
  let e : ((rH S HS cco K H) ⁻¹' Bbar) ≃
      Σ c : Bbar, ((rH S HS cco K H) ⁻¹' {c.val}) := {
    toFun := fun b => ⟨⟨rH S HS cco K H b.val, b.property⟩, ⟨b.val, rfl⟩⟩
    invFun := fun c => ⟨c.2.val, by
      change rH S HS cco K H c.2.val ∈ Bbar
      rw [c.2.property]
      exact c.1.property⟩
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨⟨c, hc⟩, b, hb⟩
      change rH S HS cco K H b = c at hb
      cases hb
      rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  calc
    _ ≤ ∑ _c : Bbar, k := Finset.sum_le_sum (fun c _ =>
      fibre_card_le S HS cco K H finiteK k hk c.val)
    _ = k * Nat.card Bbar := by
      simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
        Nat.card_eq_fintype_card]
      exact Nat.mul_comm _ _

/-- The positive uniform bound is proved from original transitivity and
finite K alone, simultaneously for ALL finite complete owner packets. -/
theorem uniform_complete_packet_bound (finiteK : K.FiniteClasses) :
    ∃ k : ℕ, 0 < k ∧
      (∀ c : (J S HS cco K H).Q,
        Nat.card ((rH S HS cco K H) ⁻¹' {c}) ≤ k) ∧
      (∀ (Bbar : Set (J S HS cco K H).Q), Bbar.Finite →
        Nat.card ((rH S HS cco K H) ⁻¹' Bbar) ≤ k * Nat.card Bbar) := by
  obtain ⟨k, hkpos, hk⟩ := K.uniform_fibre_card HS finiteK
  exact ⟨k, hkpos, fibre_card_le S HS cco K H finiteK k hk,
    complete_packet_card_le S HS cco K H finiteK k hk⟩

end OwnerCover
end CCO.FiniteLift
