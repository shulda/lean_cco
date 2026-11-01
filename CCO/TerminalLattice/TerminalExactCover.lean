import CCO.TerminalLattice.FullCoverDichotomy
import CCO.RealClosure.Bounds.TerminalLattice

/-!
# B050 C20: terminal exact covers are actual FULL original covers

Under FULL sortwise original NR2 every original invariant same-sort
equivalence has an equality-inclusive RAW word from ACCEPTED B011,
independently of CCO. Thus the pre-existing original exact-sublattice
cover is a FULL invariant-equivalence cover. This is the ONLY use of
terminal RAW exactness here. The actual original SAP and local NR2
then yield eventual OLD STRONG powers of the complete external
J-semantic quotient orbital using the CCO-free C19 theorem.

No B049 cylinder/quotient theorem or alternate automorphism group is
imported. Semantic CCO appears only in the type of the original exact
sublattice (and its proved lattice structure), not in the graph powers.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- C20 provider: under actual original full sort NR2 an EXACT cover
is a cover of the FULL original colour-invariant equivalence lattice.
The exact-to-full order iso reuses the ACCEPTED B011 one-word theorem;
no CCO distributivity result is used in constructing the isomorphism. -/
theorem original_full_cover_of_terminal_exact_cover
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S) {i : ι}
    (nr2 : RealClosure.Bounds.SortNR2 S i)
    (J K : ExactCRT.ExactEq S H cco i)
    (hJK : J ⋖ K) :
    let e := RealClosure.Bounds.terminalExactOrderIso S H cco nr2
    e.symm J ⋖ e.symm K := by
  let e := RealClosure.Bounds.terminalExactOrderIso S H cco nr2
  exact (apply_covBy_apply_iff e.symm).mpr hJK

/-- A nonzero exact original equivalence remains genuinely nonidentity
when interpreted in the FULL invariant-equivalence lattice. -/
theorem original_nonzero_of_terminal_exact_nonzero
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S) {i : ι}
    (nr2 : RealClosure.Bounds.SortNR2 S i)
    (J : ExactCRT.ExactEq S H cco i)
    (hJ : (⊥ : ExactCRT.ExactEq S H cco i) < J) :
    let e := RealClosure.Bounds.terminalExactOrderIso S H cco nr2
    (⊥ : ColourEq S i) < e.symm J := by
  let e := RealClosure.Bounds.terminalExactOrderIso S H cco nr2
  have h : e.symm (⊥ : ExactCRT.ExactEq S H cco i) < e.symm J :=
    e.symm.strictMono hJ
  have hBot : e.symm (⊥ : ExactCRT.ExactEq S H cco i) =
      (⊥ : ColourEq S i) := by
    apply Subtype.ext
    rfl
  rw [hBot] at h
  exact h

/-- SOURCE C20 terminal relative pure powers for a NONZERO represented
original exact cover. T is one genuinely complete OLD quotient G-orbital
specified by the actual original real pair a,b with aKb and not aJb.

For some positive N, ALL original fine-atom STRONG powers of T are
exactly Kᵒ for ALL n≥N. The hypothesis `J ⋖ K` is taken in the
ACTUAL original exact-sublattice; this theorem proves rather than
assumes its promotion to a FULL invariant cover.

The source's meet-irreducibility/unique-successor construction supplies
this exact-cover input, so no fictitious cover or B049 oracle is used. -/
theorem terminal_exact_relative_strong_powers
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S) {i : ι}
    (nr2 : RealClosure.Bounds.SortNR2 S i)
    (J K : ExactCRT.ExactEq S H cco i)
    (hJK : J ⋖ K)
    (hJ : (⊥ : ExactCRT.ExactEq S H cco i) < J)
    (a b : X i) (hab : K.val a b) (hne : ¬ J.val a b) :
    let e := RealClosure.Bounds.terminalExactOrderIso S H cco nr2
    let Jf : ColourEq S i := e.symm J
    let Kf : ColourEq S i := e.symm K
    ∃ N : Nat, 0 < N ∧
      ∀ n : Nat, N ≤ n →
        originalStrongPalettePower S
          (originalQuotientOrbitalPalette S (G := G) Jf a b) (n-1) =
        originalEquivDiversityPalette S Kf := by
  let e := RealClosure.Bounds.terminalExactOrderIso S H cco nr2
  let Jf : ColourEq S i := e.symm J
  let Kf : ColourEq S i := e.symm K
  have hFull : Jf ⋖ Kf :=
    original_full_cover_of_terminal_exact_cover S H cco nr2 J K hJK
  have hNonzero : (⊥ : ColourEq S i) < Jf :=
    original_nonzero_of_terminal_exact_nonzero S H cco nr2 J hJ
  have hLocalNotTwo : relativeIndex Jf.val Kf.val a ≠ 2 :=
    nr2 Jf Kf hFull.le a
  exact originalQuotient_uniform_strong_palette_powers S H sap
    Jf Kf hFull hNonzero a b hab hne hLocalNotTwo

end CCO.TerminalLattice
