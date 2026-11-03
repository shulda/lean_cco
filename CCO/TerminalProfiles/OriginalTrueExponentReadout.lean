import CCO.TerminalProfiles.OriginalWholeProfileGraph

/-!
# B051 — exact source09 TWP exponent convention

The accepted positive STRONG power implementation
`originalStrongPalettePower S W k` has exponent k+1: zero means
ONE positive word, never a STRONG identity. The printed source09
`W^{star n}=F_W` uses a genuinely positive exponent n>=N_W.

This theorem expresses that frozen quantifier exactly, by indexing the
actual STRONG power at n.val-1 for n : ℕ+, and identifies F_W with
connectedness of the true original OLD W-graph (not only RAW word
connectivity before removal of possible logical diagonal loops).
Original SAP expands ALL atomic positions of the whole typed word;
the actual original FULL NR2 supplies eventual aperiodicity.

No extra CCO, quotient SAP, positive identity, or sort commutation.
-/

universe u v w t

namespace CCO.TerminalProfiles

open CCO.TerminalLattice
open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- SOURCE09 selected `lem:typed-profile-pure-power`, exact
positive-exponent statement (TWP): every actual n>=N reaches the
same STRONG diversity palette of original OLD W-graph connectedness.

The raw semantic stabilization, full-word SAP flattening, and
equality of RAW versus STRONG graph connectivity are all actual
compiled provider instances, not new assumptions. -/
theorem original_terminal_whole_profile_true_exponents
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : CCO.Selectors.OriginalNR2 S)
    {i : ι} (word : PositiveWord S i i) :
    ∃ N : ℕ+, ∀ n : ℕ+, N.val ≤ n.val →
      originalStrongPalettePower S (PositiveWord.profile S word) (n.val - 1) =
        S.diversityGuard
          (fun x y : X i => ∃ k : Nat,
            relPow (S.menuRel (PositiveWord.profile S word)) k x y) := by
  obtain ⟨N, hN, hStable⟩ :=
    original_whole_positive_profile_powers_stabilize S H sap nr2 word
  refine ⟨⟨N+1, Nat.succ_pos N⟩, ?_⟩
  intro n hn
  change N+1 ≤ n.val at hn
  have hIndex : N ≤ n.val - 1 := by omega
  calc
    originalStrongPalettePower S (PositiveWord.profile S word) (n.val-1) =
        originalWholeProfileConnectedPalette S word :=
      hStable (n.val-1) hIndex
    _ = S.diversityGuard
          (fun x y : X i => ∃ k : Nat,
            relPow (S.menuRel (PositiveWord.profile S word)) k x y) :=
      originalWholeProfileConnectedPalette_eq_strong_graph S H sap word

end CCO.TerminalProfiles
