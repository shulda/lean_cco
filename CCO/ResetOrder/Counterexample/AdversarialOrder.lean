import CCO.ResetOrder.Counterexample.Successor
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Prod.Lex

/-! For EVERY finite nested-equivalence host, order its P-components and
Q-blocks consecutively, with non-singleton Q-blocks after singleton blocks.
This is an actual legal competitor, constructed from the given host. -/
universe u
namespace CCO.ResetOrder.Counterexample

private noncomputable def finiteCode (T : Type*) [Finite T] : T ↪ ℕ := by
  letI := Fintype.ofFinite T
  exact (Fintype.equivFin T).toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩

namespace Nested
variable {X : Type u} [Finite X] (A : Nested X)

noncomputable def pCode (x : X) : ℕ := finiteCode (Quotient A.P) (Quotient.mk A.P x)
noncomputable def qCode (x : X) : ℕ := finiteCode (Quotient A.Q) (Quotient.mk A.Q x)
noncomputable def vCode (_A : Nested X) (x : X) : ℕ := finiteCode X x

theorem pCode_eq_iff {x y : X} : A.pCode x = A.pCode y ↔ A.P.r x y := by
  rw [pCode, pCode, (finiteCode _).injective.eq_iff, Quotient.eq_iff_equiv]

theorem qCode_eq_iff {x y : X} : A.qCode x = A.qCode y ↔ A.Q.r x y := by
  rw [qCode, qCode, (finiteCode _).injective.eq_iff, Quotient.eq_iff_equiv]

def LargeQ (x : X) : Prop := ∃ y, A.Q.r x y ∧ y ≠ x

theorem largeQ_iff_of_q {x y : X} (h : A.Q.r x y) : A.LargeQ x ↔ A.LargeQ y := by
  constructor
  · rintro ⟨z, hxz, hzx⟩
    by_cases hzy : z = y
    · subst z
      exact ⟨x, A.Q.symm h, hzx.symm⟩
    · exact ⟨z, A.Q.trans (A.Q.symm h) hxz, hzy⟩
  · rintro ⟨z, hyz, hzy⟩
    by_cases hzx : z = x
    · subst z
      exact ⟨y, h, hzy.symm⟩
    · exact ⟨z, A.Q.trans h hyz, hzx⟩

noncomputable def sizeFlag (x : X) : ℕ := by
  classical
  exact if A.LargeQ x then 1 else 0

theorem sizeFlag_eq_of_q {x y : X} (h : A.Q.r x y) : A.sizeFlag x = A.sizeFlag y := by
  classical
  simp only [sizeFlag, A.largeQ_iff_of_q h]

private abbrev Key := ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ))

private noncomputable def key (x : X) : Key :=
  toLex (A.pCode x, toLex (A.sizeFlag x, toLex (A.qCode x, A.vCode x)))

private theorem key_injective : Function.Injective A.key := by
  intro x y h
  have hv := congrArg (fun k : Key => (ofLex (ofLex (ofLex k).2).2).2) h
  exact (finiteCode X).injective hv

noncomputable def adversarialLinearOrder : LinearOrder X :=
  LinearOrder.lift' A.key A.key_injective

private theorem key_le_p {x y : X} (h : A.key x ≤ A.key y) : A.pCode x ≤ A.pCode y :=
  Prod.Lex.monotone_fst _ _ h

private theorem key_le_tail {x y : X} (hp : A.pCode x = A.pCode y)
    (h : A.key x ≤ A.key y) :
    toLex (A.sizeFlag x, toLex (A.qCode x, A.vCode x)) ≤
      toLex (A.sizeFlag y, toLex (A.qCode y, A.vCode y)) := by
  exact (Prod.Lex.toLex_le_toLex'.mp h).2 hp

private theorem key_le_flag {x y : X} (hp : A.pCode x = A.pCode y)
    (h : A.key x ≤ A.key y) : A.sizeFlag x ≤ A.sizeFlag y :=
  Prod.Lex.monotone_fst _ _ (A.key_le_tail hp h)

private theorem key_le_q {x y : X} (hp : A.pCode x = A.pCode y)
    (hf : A.sizeFlag x = A.sizeFlag y) (h : A.key x ≤ A.key y) :
    A.qCode x ≤ A.qCode y :=
  Prod.Lex.monotone_fst _ _ ((Prod.Lex.toLex_le_toLex'.mp (A.key_le_tail hp h)).2 hf)

noncomputable def adversarialOrder : ConvexOrder A where
  order := A.adversarialLinearOrder
  convexP := by
    intro a b c hab hbc hac
    have hpac := A.pCode_eq_iff.mpr hac
    exact A.pCode_eq_iff.mp (le_antisymm (A.key_le_p hab)
      (hpac ▸ A.key_le_p hbc))
  convexQ := by
    intro a b c hab hbc hac
    have hpac := A.pCode_eq_iff.mpr (A.refine hac)
    have hpab : A.pCode a = A.pCode b :=
      le_antisymm (A.key_le_p hab) (hpac ▸ A.key_le_p hbc)
    have hpbc : A.pCode b = A.pCode c := hpab.symm.trans hpac
    have hfac := A.sizeFlag_eq_of_q hac
    have hfab : A.sizeFlag a = A.sizeFlag b :=
      le_antisymm (A.key_le_flag hpab hab) (hfac ▸ A.key_le_flag hpbc hbc)
    have hfbc : A.sizeFlag b = A.sizeFlag c := hfab.symm.trans hfac
    have hqac := A.qCode_eq_iff.mpr hac
    exact A.qCode_eq_iff.mp (le_antisymm (A.key_le_q hpab hfab hab)
      (hqac ▸ A.key_le_q hpbc hfbc hbc))

/-- In a P-component the order cannot pass from a large Q-block to a
singleton Q-block. Thus a last Q-block is large whenever any is large. -/
theorem largeQ_of_adversarial_lt {x y : X} (hP : A.P.r x y)
    (hxy : A.adversarialOrder.order.lt x y) (hx : A.LargeQ x) : A.LargeQ y := by
  classical
  have hflag := A.key_le_flag (A.pCode_eq_iff.mpr hP) (le_of_lt hxy)
  by_contra hy
  simpa [sizeFlag, hx, hy] using hflag

/-- The forbidden three-point successor pattern cannot occur in this
competitor, for any size or shape of the original finite host. -/
theorem adversarial_no_pattern
    (s : A.adversarialOrder.Successor) {a b c : X}
    (hab : A.adversarialOrder.order.lt a b)
    (hbc : A.adversarialOrder.order.lt b c)
    (hP : A.P.r b c) (hQab : A.Q.r a b) (hQbc : ¬ A.Q.r b c)
    (hnext : s.next b = c) (hfix : s.next c = c) : False := by
  letI := A.adversarialOrder.order
  have hb : A.LargeQ b := ⟨a, A.Q.symm hQab, ne_of_lt hab⟩
  have hc : A.LargeQ c := A.largeQ_of_adversarial_lt hP hbc hb
  obtain ⟨y, hQcy, hyc⟩ := hc
  have hPy : A.P.r c y := A.refine hQcy
  have hyc' : y < c := lt_of_le_of_ne ((s.fixed_iff c).1 hfix y hPy) hyc
  have hby : b < y := by
    by_contra! h
    have hQyb : A.Q.r y b :=
      A.adversarialOrder.convexQ h hbc.le (A.Q.symm hQcy)
    exact hQbc (A.Q.trans (A.Q.symm hQyb) (A.Q.symm hQcy))
  have hPby : A.P.r b y := A.P.trans hP hPy
  have hle := s.least b y hPby hby
  rw [hnext] at hle
  exact (not_le_of_gt hyc') hle

end Nested
end CCO.ResetOrder.Counterexample
