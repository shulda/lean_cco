import CCO.TerminalProfiles.OriginalWholeProfileOddLoops
import CCO.TerminalProfiles.OriginalWholeProfileWordPowers
import CCO.TerminalLattice.StrongPaletteBridge

/-!
# B051 TWP: all large STRONG powers of an arbitrary typed old word

The actual RAW relation of the WHOLE word stabilizes to its real walk
connectivity by B032 original NR2 and finite old orbital parity. The
accepted SAP full atomic-occurrence word semantics turns those RAW
relations into STRONG word powers without assuming quotient SAP or
dropping the intermediate named sorts.
-/

universe u v w t

namespace CCO.TerminalProfiles

open CCO.ParityHasse.Original
open CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Complete old diversity palette of literal finite whole-word
walk connectivity; the true old diagonal is not a STRONG atom. -/
def originalWholeProfileConnectedPalette
    {i : ι} (word : PositiveWord S i i) : S.Menu i i :=
  S.diversityGuard (fun x y => ∃ n : Nat,
    relPow (PositiveWord.represented S word) n x y)

/-- SOURCE09 selected TWP: one uniform threshold works for all
later old STRONG same-sort powers, even though each step W is an
arbitrary positive typed word visiting any original named sorts. -/
theorem original_whole_positive_profile_powers_stabilize
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : CCO.Selectors.OriginalNR2 S)
    {i : ι} (word : PositiveWord S i i) :
    ∃ N : Nat, 0 < N ∧ ∀ n, N ≤ n →
      originalStrongPalettePower S (PositiveWord.profile S word) n =
        originalWholeProfileConnectedPalette S word := by
  obtain ⟨N,hN,hStable⟩ :=
    original_whole_positive_word_raw_eventually_connected S H sap nr2 word
  refine ⟨N,hN,?_⟩
  intro n hn
  calc
    originalStrongPalettePower S (PositiveWord.profile S word) n =
        S.diversityGuard
          (relPow (PositiveWord.represented S word) (n+1)) :=
      (originalWholeProfilePower_guard S H sap word n).symm
    _ = originalWholeProfileConnectedPalette S word := by
      change S.diversityGuard
          (relPow (PositiveWord.represented S word) (n+1)) =
        S.diversityGuard (fun x y => ∃ k : Nat,
          relPow (PositiveWord.represented S word) k x y)
      rw [hStable (n+1) (by omega)]

end CCO.TerminalProfiles
