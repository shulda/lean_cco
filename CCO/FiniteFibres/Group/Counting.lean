import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Elementary finite orbit counting for B042. The Cauchy and p-group
normalizer conclusions are not imported. The fixed-point congruence is proved
directly by the orbit partition and orbit-stabilizer; auxiliary actions need
not be faithful. -/

namespace CCO.FiniteFibres.Group
open MulAction Fintype

variable {G : Type*} [Group G] [Finite G]
variable {p n : ℕ}

theorem orbit_card_power [hp : Fact p.Prime] (hG : Nat.card G = p ^ n)
    {A : Type*} [MulAction G A] [Finite A] (a : A) :
    ∃ k, Nat.card (orbit G a) = p ^ k := by
  classical
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite (orbit G a)
  letI := Fintype.ofFinite (stabilizer G a)
  have hd : Fintype.card (orbit G a) ∣ Fintype.card G :=
    ⟨Fintype.card (stabilizer G a), (card_orbit_mul_card_stabilizer_eq_card_group G a).symm⟩
  have hd' : Nat.card (orbit G a) ∣ Nat.card G := by simpa only [Nat.card_eq_fintype_card] using hd
  rw [hG] at hd'
  obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow hp.out).mp hd'
  exact ⟨k,by simpa only [Nat.card_eq_fintype_card] using hk⟩

/-- The cardinal of a finite p-power-group action is congruent to its fixed
points. The proof expands the orbit partition rather than using p-group facts. -/
theorem fixed_card_modEq [hp : Fact p.Prime] (hG : Nat.card G = p ^ n)
    (A : Type*) [MulAction G A] [Finite A] :
    Nat.card A ≡ Nat.card (fixedPoints G A) [MOD p] := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite (fixedPoints G A)
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  calc
    card A = card (Σ y : Quotient (orbitRel G A), {x // Quotient.mk'' x = y}) :=
      card_congr (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbitRel G A))).symm
    _ = ∑ a : Quotient (orbitRel G A),card {x // Quotient.mk'' x = a} := card_sigma
    _ ≡ ∑ _a : fixedPoints G A,1 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff _ _ p,Nat.cast_sum,Nat.cast_sum]
      have key : ∀ x,
          card {y // (Quotient.mk'' y : Quotient (orbitRel G A)) = Quotient.mk'' x} =
            card (orbit G x) := fun x => by simp only [Quotient.eq'']; congr
      refine Eq.symm (Finset.sum_bij_ne_zero
        (fun a _ _ => Quotient.mk'' a.1) (fun _ _ _ => Finset.mem_univ _)
        (fun a₁ _ _ a₂ _ _ h =>
          Subtype.ext (mem_fixedPoints'.mp a₂.2 a₁.1 (Quotient.exact' h)))
        (fun b => Quotient.inductionOn' b fun b _ hb => ?_) fun a _ _ => by
          rw [key,mem_fixedPoints_iff_card_orbit_eq_one.mp a.2])
      obtain ⟨k,hk⟩ := orbit_card_power hG b
      rw [Nat.card_eq_fintype_card] at hk
      have hk0 : k = 0 := by
        contrapose! hb
        simp [key,hk,hb]
      exact ⟨⟨b,mem_fixedPoints_iff_card_orbit_eq_one.2 (by rw [hk,hk0,pow_zero])⟩,
        Finset.mem_univ _,ne_of_eq_of_ne Nat.cast_one one_ne_zero,rfl⟩
    _ = _ := by simp

theorem second_fixed [hp : Fact p.Prime] (hG : Nat.card G = p ^ n)
    {A : Type*} [MulAction G A] [Finite A]
    (hd : p ∣ Nat.card A) {a : A} (ha : a ∈ fixedPoints G A) :
    ∃ b, b ∈ fixedPoints G A ∧ b ≠ a := by
  classical
  have hd' : p ∣ Nat.card (fixedPoints G A) :=
    Nat.modEq_zero_iff_dvd.mp ((fixed_card_modEq hG A).symm.trans hd.modEq_zero_nat)
  have hn : 1 < Nat.card (fixedPoints G A) :=
    hp.out.one_lt.trans_le (Nat.le_of_dvd (Finite.card_pos_iff.2 ⟨⟨a,ha⟩⟩) hd')
  haveI : Nontrivial (fixedPoints G A) := Finite.one_lt_card_iff_nontrivial.mp hn
  obtain ⟨b,hb⟩ := exists_ne (⟨a,ha⟩ : fixedPoints G A)
  exact ⟨b.val,b.property,fun h => hb (Subtype.ext h)⟩

end CCO.FiniteFibres.Group
