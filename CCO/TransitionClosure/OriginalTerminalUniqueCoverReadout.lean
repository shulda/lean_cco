import CCO.TransitionClosure.OriginalTerminalRepresentedWrappers

/-!
# B049 source07 C19/C23: FULL unique-cover existence, without a cover input

The pinned represented source lemmata speak of THE unique cover J⁺
of a proper original FULL meet-irreducible J. In the finite original
colour-invariant equivalence lattice, existence follows from finite
strong atomicity; uniqueness follows from the proven FULL meet
irreducibility/cover lemma, not a new premise or quotient SAP.

The preceding direct terminal NR2 wrappers accepted J,K with a
separately supplied FULL cover proof. The two new receiving readouts
eliminate that cover assumption by constructing K = J⁺ inside the
ACTUAL complete original equivalence lattice. This is essential
to use the source lemma without smuggling the conclusion into a
hypothesis or mistaking a restricted represented lattice for FULL.

All positive STRONG J/K presentations, original old CCO/SAP and
B003 strongly completable PC domain obligations remain discharged
by the previous source-level results. The identity J=Id case is
handled by those results as an empty diversity intersection.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- Every proper meet-irreducible of the ACTUAL original FULL
finite colour-invariant lattice has exactly one FULL cover.
This constructs the source's J⁺; neither its existence nor
its uniqueness is postulated. The lattice includes ALL old
invariant equivalences, not merely those previously represented. -/
theorem original_full_infIrred_exists_unique_cover
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq S i)
    (hMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred J) :
    ∃ K : ColourEq S i,
      (letI : Lattice (ColourEq S i) :=
        ColourEq.lattice S H (i := i); J ⋖ K) ∧
      ∀ L : ColourEq S i,
        (letI : Lattice (ColourEq S i) :=
          ColourEq.lattice S H (i := i); J ⋖ L) → L = K := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
  have hJnotTop : J ≠ (⊤ : ColourEq S i) := by
    intro heq
    apply hMI.1
    rw [heq]
    exact isMax_top
  have hJtop : J < (⊤ : ColourEq S i) :=
    lt_of_le_of_ne le_top hJnotTop
  obtain ⟨K,hJK,_⟩ := hJtop.exists_covby_le
  refine ⟨K,hJK,?_⟩
  intro L hJL
  apply le_antisymm
  · exact original_meet_irred_full_cover_le hMI hJL hJK.lt
  · exact original_meet_irred_full_cover_le hMI hJK hJL.lt

/-- SOURCE07 selected typed-cover-interpolation, including
the ACTUAL uniquely constructed J⁺ and without assuming a
particular full cover K as an external input. It is proved
using old visible SAP, old CCO and B011 terminal FULL NR2,
with arbitrary mixed original interior sorts of the P word. -/
theorem original_terminal_represented_cover_interpolation_unique
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (J : ColourEq S i)
    (hMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred J)
    (P : PositiveWord S i i)
    (hMeet : (PositiveWord.profile S P ∩
      originalEquivDiversityPalette S J).Nonempty)
    (hExit : ∃ a : S.Atom i i,
      a ∈ PositiveWord.profile S P ∧
      a ∉ originalEquivDiversityPalette S J) :
    ∃ K : ColourEq S i,
      (letI : Lattice (ColourEq S i) :=
        ColourEq.lattice S H (i := i); J ⋖ K) ∧
      (∀ L : ColourEq S i,
        (letI : Lattice (ColourEq S i) :=
          ColourEq.lattice S H (i := i); J ⋖ L) → L = K) ∧
      (PositiveWord.profile S P ∩
        (originalEquivDiversityPalette S K \
          originalEquivDiversityPalette S J)).Nonempty := by
  obtain ⟨K,hJK,hUnique⟩ :=
    original_full_infIrred_exists_unique_cover S H J hMI
  exact ⟨K,hJK,hUnique,
    original_terminal_represented_cover_interpolation
      S H sap cco nr2 J K hMI hJK P hMeet hExit⟩

/-- SOURCE07 selected typed-prime-intersection with NO
extra cover hypothesis. The unique full cover is obtained
inside the true finite FULL original invariant lattice, then
the previously compiled represented-PC wrapper applies.

The premises are precisely original old SAP, semantic HOM CCO,
terminal full NR2, original proper meet-irreducibility and
actual canonical typed PC fixed-point domains A,B, whose
nonempty intersection is contained in J° (logical equality
is separately absent from every strong diversity menu). -/
theorem original_terminal_represented_prime_intersection_no_cover
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (J : ColourEq S i)
    (hMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred J)
    (A B : S.Menu i i)
    (hA : StrongExact.CanonicalThetaDomain S A)
    (hB : StrongExact.CanonicalThetaDomain S B)
    (hAB : (A ∩ B).Nonempty)
    (hInside : (A ∩ B) ⊆ originalEquivDiversityPalette S J) :
    A ⊆ originalEquivDiversityPalette S J ∨
      B ⊆ originalEquivDiversityPalette S J := by
  obtain ⟨K,hJK,_⟩ :=
    original_full_infIrred_exists_unique_cover S H J hMI
  exact original_terminal_represented_prime_intersection
    S H sap cco nr2 J K hMI hJK A B hA hB hAB hInside

end CCO.TransitionClosure
