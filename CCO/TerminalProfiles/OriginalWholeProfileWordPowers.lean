import CCO.TerminalPowers.PositivePower
import CCO.TerminalLattice.StrongPaletteBridge
import CCO.PositiveWords
import CCO.ParityHasse.Original.ParityPowers

/-!
# B051 TWP: ALL atomic positions in arbitrary positive OLD words

For an arbitrary genuine positive typed old a-to-a word w, one step of
its profile W may traverse MANY original named sorts. Literal repeated
concatenation of the WHOLE word, not a selected same-sort atomic
surrogate, represents the RAW W-relation powers.

Original SAP's accepted endpoint-preserving full atomic-word
injectivisation proves that the diversity guard of these RAW powers
equals the STRONG power W^(n+1). In particular neither coarse-path
vertices alone nor a synthetic identity factor is inserted.

This is the real flattening/semantics prerequisite of source09
C13–C18; eventual stabilization itself is separate.
-/

universe u v w t

namespace CCO.TerminalProfiles

open CCO.TerminalLattice
open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A genuine positive a-to-a typed word repeated n+1 times.
The zero index denotes ONE word, never the empty STRONG word. -/
def originalRepeatedPositiveWord
    {i : ι} (word : PositiveWord S i i) :
    Nat → PositiveWord S i i
  | 0 => word
  | n+1 => PositiveWord.append S word (originalRepeatedPositiveWord word n)

/-- Literal RAW semantics: every occurrence of every original typed
atomic letter of w is retained by the n+1-fold append. -/
theorem originalRepeatedPositiveWord_represented
    {i : ι} (word : PositiveWord S i i) (n : Nat) :
    PositiveWord.represented S (originalRepeatedPositiveWord S word n) =
      relPow (PositiveWord.represented S word) (n+1) := by
  induction n with
  | zero =>
      funext x y
      apply propext
      exact (relPow_one (PositiveWord.represented S word) x y).symm
  | succ n ih =>
      change PositiveWord.represented S
          (PositiveWord.append S word (originalRepeatedPositiveWord S word n)) =
        relPow (PositiveWord.represented S word) ((n+1)+1)
      rw [PositiveWord.represented_append S word
        (originalRepeatedPositiveWord S word n), ih]
      rfl

/-- Literal STRONG powers via SAP-supported POSITIVE word
concatenation, not RAW associativity with a fictitious STRONG unit. -/
theorem originalRepeatedPositiveWord_profile
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (word : PositiveWord S i i) (n : Nat) :
    PositiveWord.profile S (originalRepeatedPositiveWord S word n) =
      originalStrongPalettePower S (PositiveWord.profile S word) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change PositiveWord.profile S
          (PositiveWord.append S word (originalRepeatedPositiveWord S word n)) =
        S.product (PositiveWord.profile S word)
          (originalStrongPalettePower S (PositiveWord.profile S word) n)
      rw [PositiveWord.profile_append_of_SAP S H sap
        word (originalRepeatedPositiveWord S word n), ih]

/-- SOURCE09 TWP C14/C16 semantic firewall:
for EACH n, the old STRONG whole-profile power is EXACTLY
the diversity guard of n+1 literal RAW whole-word concatenations,
including all genuinely typed interior atomic occurrences. -/
theorem originalWholeProfilePower_guard
    {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (word : PositiveWord S i i) (n : Nat) :
    S.diversityGuard
      (relPow (PositiveWord.represented S word) (n+1)) =
      originalStrongPalettePower S (PositiveWord.profile S word) n := by
  calc
    S.diversityGuard
        (relPow (PositiveWord.represented S word) (n+1)) =
      S.diversityGuard
        (PositiveWord.represented S (originalRepeatedPositiveWord S word n)) := by
          rw [originalRepeatedPositiveWord_represented]
    _ = PositiveWord.profile S (originalRepeatedPositiveWord S word n) :=
      PositiveWord.diversityGuard_represented_eq_profile_of_SAP S H sap _
    _ = originalStrongPalettePower S (PositiveWord.profile S word) n :=
      originalRepeatedPositiveWord_profile S H sap word n

end CCO.TerminalProfiles
