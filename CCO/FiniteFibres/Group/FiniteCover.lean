import CCO.FiniteFibres.Group.FiniteAction
import CCO.FiniteFibres.Group.Chain
import CCO.FiniteFibres.Group.Correspondence.Counting

/-! C25–C27/C32–C33: every cover in the FULL invariant equivalence
lattice has actual relative index two, and a saturated chain telescopes
to the cardinality of the transitive target. The action may be nonfaithful. -/
namespace CCO.FiniteFibres.Group
open Correspondence

variable {G A : Type*} [Group G] [MulAction G A] [Finite A]

noncomputable def invariantSaturatedChain :
    SaturatedChain (⊥ : InvEq G A) ⊤ :=
  Classical.choice (SaturatedChain.exists_between _ _ bot_le)

theorem quotient_bot_card : Nat.card (Quotient (⊥ : InvEq G A).val) = Nat.card A := by
  have hb : (⊥ : InvEq G A).val = (⊥ : Setoid A) :=
    Setoid.ext (fun x y => InvEq.bot_apply x y)
  rw [hb]
  exact Nat.card_congr Setoid.quotientBotEquiv

theorem quotient_top_card (a : A) : Nat.card (Quotient (⊤ : InvEq G A).val) = 1 := by
  haveI : Subsingleton (Quotient (⊤ : InvEq G A).val) :=
    ⟨fun x y => Quotient.inductionOn₂ x y fun u v => Quotient.sound ((InvEq.top_apply u v).mpr trivial)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance,⟨Quotient.mk _ a⟩⟩

variable [Finite G]

/-- C26: use actual subgroup maximality inside H_V, then the proved local
p-group index theorem, then the literal class/coset bijection. -/
theorem cover_relative_card_two {n : ℕ} (hG : Nat.card G = 2^n)
    (trans : ∀ x y : A, ∃ g : G, g • x = y) (a : A)
    {U V : InvEq G A} (h : U ⋖ V) :
    Nat.card (RelativeClass U V h.le a) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k,hk⟩ := subgroup_card_power hG (V.subgroup a)
  obtain ⟨hne,hmax⟩ := relative_subgroup_maximal trans a h
  rw [relative_card_eq_index trans a U V h.le]
  exact maximal_index hk _ hne hmax

/-- C33: actual U-class counts along EVERY cover of the finite saturated
chain telescope from equality to top. No chain-length/cardinality oracle is
assumed. The zero-step singleton chain is included. -/
theorem chain_card_two_power {n : ℕ} (hG : Nat.card G = 2^n)
    (trans : ∀ x y : A, ∃ g : G, g • x = y) (a : A)
    (C : SaturatedChain (⊥ : InvEq G A) ⊤) : Nat.card A = 2^C.length := by
  let w : InvEq G A → ℕ := fun U => Nat.card (Quotient U.val)
  have hstep : ∀ i : Fin C.length,w (C.point i.castSucc) = 2*w (C.point i.succ) := by
    intro i
    have h := quotient_card_mul_relative trans a (C.point i.castSucc) (C.point i.succ) (C.covers i).le
    rw [cover_relative_card_two hG trans a (C.covers i)] at h
    exact h.trans (Nat.mul_comm _ _)
  have ht := C.telescope w 2 hstep
  change Nat.card (Quotient (⊥ : InvEq G A).val) =
    2^C.length*Nat.card (Quotient (⊤ : InvEq G A).val) at ht
  simpa only [quotient_bot_card,quotient_top_card a,Nat.mul_one] using ht

theorem actual_chain_card_two_power {n : ℕ} (hG : Nat.card G = 2^n)
    (trans : ∀ x y : A, ∃ g : G, g • x = y) (a : A) :
    Nat.card A = 2^(invariantSaturatedChain (G := G) (A := A)).length :=
  chain_card_two_power hG trans a _

end CCO.FiniteFibres.Group
