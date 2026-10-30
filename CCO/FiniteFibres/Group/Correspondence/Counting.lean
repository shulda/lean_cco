import CCO.FiniteFibres.Group.Correspondence.Relative
import Mathlib.SetTheory.Cardinal.Finite

/-! The actual quotient-map fibre count used to telescope finite invariant
chains. All fibres are related by actual group motions; there is no assumed
constant-size callback. -/

universe u v
namespace CCO.FiniteFibres.Group.Correspondence
variable {G : Type u} [Group G] {A : Type v} [MulAction G A] [Finite A]
variable (trans : ∀ x y : A, ∃ g : G, g • x = y) (a : A)

include trans in
theorem quotient_card_mul_relative (U V : InvEq G A) (h : U ≤ V) :
    Nat.card (Quotient U.val) =
      Nat.card (Quotient V.val) * Nat.card (RelativeClass U V h a) := by
  classical
  letI := Fintype.ofFinite (Quotient V.val)
  let f : Quotient U.val → Quotient V.val := Quotient.map id (fun {_ _} hxy => h hxy)
  have hfib : ∀ q : Quotient V.val,
      Nat.card {x : Quotient U.val // f x = q} = Nat.card (RelativeClass U V h a) := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => exact relative_card_uniform trans U V h x a
  calc
    Nat.card (Quotient U.val) =
        Nat.card (Σ q : Quotient V.val,{x : Quotient U.val // f x = q}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ q : Quotient V.val,Nat.card {x : Quotient U.val // f x = q} := Nat.card_sigma
    _ = _ := by
      simp only [hfib,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

end CCO.FiniteFibres.Group.Correspondence
