import CCO.ParityHasse.Original.ParityPowers
import Mathlib.Tactic.Omega

/-!
# B051 TWP: actual invariant RAW relation powers with odd loops

For a symmetric SERIAL original same-sort colour-invariant relation R,
the ORIGINAL finite optional orbit palette implies stabilization of its
even and odd RAW powers independently. If EVERY old real point has an
actual odd closed R-walk, each stabilized even power equals its odd
neighbour, hence ALL sufficiently long RAW powers are identical.
Their common relation is precisely actual finite R-walk connectivity.

This is an original-sort theorem, NOT quotient homogeneity, a synthetic
STRONG identity, or an assumption of source SAP/CCO. Actual nr2 and SAP
will supply the odd walks in a separate positive-word consumer.
-/

universe u v w t

namespace CCO.TerminalProfiles

open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- SOURCE09 C15: an original invariant same-sort relation with a
genuine odd closed walk at EVERY real point has eventual one-period
RAW powers, not merely separate two-period even/odd stabilization.

The common power equals literal finite R-walk connectivity, including
the real diagonal through length-zero paths. -/
theorem original_odd_loop_raw_powers_eventually_connected
    (H : HomogeneousSource S G)
    {i : ι} (R : X i → X i → Prop)
    (hColour : ColourInvariant S i R)
    (hSymm : ∀ x y, R x y → R y x)
    (hSerial : ∀ x, ∃ y, R x y)
    (hOdd : ∀ x : X i, ∃ m : Nat, Odd m ∧ relPow R m x x) :
    ∃ N : Nat, 0 < N ∧
      ∀ n, N ≤ n →
        relPow R n =
          (fun x y => ∃ k : Nat, relPow R k x y) := by
  obtain ⟨M,hM,hEvenUpper,hOddUpper,hEvenStable,hOddStable⟩ :=
    exists_positive_parity_stabilization S H hColour hSymm hSerial
  have hEqual : relPow R (2*M) = relPow R (2*M+1) := by
    funext x y
    apply propext
    constructor
    · intro hEven
      obtain ⟨m,hmOdd,hmLoop⟩ := hOdd x
      obtain ⟨k,hk⟩ := hmOdd
      have hLong : relPow R (m+2*M) x y := by
        rw [relPow_add]
        exact ⟨x,hmLoop,hEven⟩
      have hmEq : m+2*M = 2*(M+k)+1 := by omega
      rw [hmEq] at hLong
      rw [hOddStable (M+k) (by omega)]
      exact hLong
    · intro hOddXY
      obtain ⟨m,hmOdd,hmLoop⟩ := hOdd x
      obtain ⟨k,hk⟩ := hmOdd
      have hLong : relPow R (m+(2*M+1)) x y := by
        rw [relPow_add]
        exact ⟨x,hmLoop,hOddXY⟩
      have hmEq : m+(2*M+1) = 2*(M+k+1) := by omega
      rw [hmEq] at hLong
      rw [hEvenStable (M+k+1) (by omega)]
      exact hLong
  have hSubset (k : Nat) (x y : X i) :
      relPow R k x y → relPow R (2*M) x y := by
    intro hk
    rcases Nat.even_or_odd k with hEven | hOddK
    · obtain ⟨s,hs⟩ := hEven
      have hke : k = 2*s := by omega
      exact hEvenUpper s x y (hke ▸ hk)
    · obtain ⟨s,hs⟩ := hOddK
      have hke : k = 2*s+1 := by omega
      have hOddPart : relPow R (2*M+1) x y :=
        hOddUpper s x y (hke ▸ hk)
      rw [←hEqual] at hOddPart
      exact hOddPart
  have hStable (n : Nat) (hn : 2*M+1 ≤ n) :
      relPow R n = relPow R (2*M) := by
    rcases Nat.even_or_odd n with hEven | hOddN
    · obtain ⟨k,hk⟩ := hEven
      have hEq : n = 2*k := by omega
      have hMk : M ≤ k := by omega
      calc
        relPow R n = relPow R (2*k) := by rw [hEq]
        _ = relPow R (2*M) := (hEvenStable k hMk).symm
    · obtain ⟨k,hk⟩ := hOddN
      have hEq : n = 2*k+1 := by omega
      have hMk : M ≤ k := by omega
      calc
        relPow R n = relPow R (2*k+1) := by rw [hEq]
        _ = relPow R (2*M+1) := (hOddStable k hMk).symm
        _ = relPow R (2*M) := hEqual.symm
  refine ⟨2*M+1, by omega, ?_⟩
  intro n hn
  rw [hStable n hn]
  funext x y
  apply propext
  constructor
  · intro h
    exact ⟨2*M,h⟩
  · rintro ⟨k,hk⟩
    exact hSubset k x y hk

end CCO.TerminalProfiles
