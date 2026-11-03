import CCO.TerminalProfiles.OriginalTerminalCoverLayer
import CCO.RealClosure.Bounds.TerminalNR2
import CCO.ExactCRT.SourceLattice

/-!
# B051 C23–C25: EXACT represented MI is the FULL original MI

Source09 starts with a genuinely represented proper meet-irreducible
original equivalence, not an additional FULL meet-irreducibility
hypothesis. The accepted B011 `terminalExactOrderIso` proves that
under actual original FULL NR2, represented exact equivalences and
ALL original colour-invariant equivalences are ORDER-ISOMORPHIC.

We explicitly transport the represented `InfIrred` through this
bijection to the original FULL invariant-equivalence lattice, and
only then invoke the already compiled CCO/SAP full-cover positive
word provider. No additional FULL-MI assumption, quotient SAP,
synthetic identity atom, or choice of an unproved represented cover.
-/

universe u v w t

namespace CCO.TerminalProfiles

open CCO.ParityHasse.Original
open CCO.ExactCRT
open CCO.RealClosure.Bounds
open CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- The literal original FULL invariant equivalence underlying an
actual represented EXACT source relation; B011 supplies the inverse
order isomorphism from terminal original FULL NR2. -/
noncomputable def originalRepresentedToFull
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : CCO.Selectors.OriginalNR2 S)
    {i : ι} (J : ExactEq S H cco i) : ColourEq S i :=
  (terminalExactOrderIso S H cco
    (sortNR2_of_originalNR2 S H nr2)).symm J

/-- Inf-irreducibility of an ACTUAL represented exact equivalence
transfers to the WHOLE original invariant-equivalence lattice under
the precisely accepted terminal order isomorphism. -/
theorem original_represented_MI_is_full_MI
    (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : CCO.Selectors.OriginalNR2 S)
    {i : ι} (J : ExactEq S H cco i)
    (hMI :
      letI : DistribLattice (ExactEq S H cco i) :=
        exactDistribLattice S H cco i
      InfIrred J) :
    letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
    InfIrred (originalRepresentedToFull S H cco nr2 J) := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
  letI : DistribLattice (ExactEq S H cco i) :=
    exactDistribLattice S H cco i
  let iso : ColourEq S i ≃o ExactEq S H cco i :=
    terminalExactOrderIso S H cco
      (sortNR2_of_originalNR2 S H nr2)
  let Jfull : ColourEq S i := iso.symm J
  change InfIrred Jfull
  constructor
  · intro hMax
    apply hMI.1
    intro E hJE
    have hFullLE : Jfull ≤ iso.symm E :=
      iso.symm.monotone hJE
    have hEFull : iso.symm E ≤ Jfull := hMax hFullLE
    have hEJ : iso (iso.symm E) ≤ iso (iso.symm J) :=
      iso.monotone hEFull
    simpa only [OrderIso.apply_symm_apply] using hEJ
  · intro E F hInf
    have hMapInf : iso E ⊓ iso F = J := by
      calc
        iso E ⊓ iso F = iso (E ⊓ F) := (iso.map_inf E F).symm
        _ = iso (iso.symm J) := congrArg iso hInf
        _ = J := iso.apply_symm_apply J
    rcases hMI.2 hMapInf with hE | hF
    · left
      calc
        E = iso.symm (iso E) := (iso.symm_apply_apply E).symm
        _ = iso.symm J := congrArg iso.symm hE
    · right
      calc
        F = iso.symm (iso F) := (iso.symm_apply_apply F).symm
        _ = iso.symm J := congrArg iso.symm hF

/-- SOURCE09 selected represented-MI cover-layer source theorem:
the input is a proper actual represented FULL EXACT MI, as printed.
The output is the unique FULL original cover, also genuinely
represented by B011, with ONE nonempty positive old typed word for
its entire external diversity layer. This is not an extra FULL-MI
source assumption or a conditional B050 external-layer provider. -/
theorem original_terminal_represented_MI_cover_layer_reachable
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : CCO.Selectors.OriginalNR2 S)
    {i : ι} (J : ExactEq S H cco i)
    (hJ : (⊥ : ColourEq S i) <
      originalRepresentedToFull S H cco nr2 J)
    (hMI :
      letI : DistribLattice (ExactEq S H cco i) :=
        exactDistribLattice S H cco i
      InfIrred J) :
    let Jfull := originalRepresentedToFull S H cco nr2 J
    ∃ K : ColourEq S i,
      (letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
       Jfull ⋖ K) ∧
      (∀ L : ColourEq S i,
         (letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
          Jfull ⋖ L) → L = K) ∧
      IsExactEq S K.val ∧
      ∃ word : PositiveWord S i i,
        PositiveWord.profile S word =
          originalEquivDiversityPalette S K \
            originalEquivDiversityPalette S Jfull ∧
        (PositiveWord.profile S word).Nonempty := by
  let Jfull := originalRepresentedToFull S H cco nr2 J
  have hFullMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred Jfull :=
    original_represented_MI_is_full_MI S H cco nr2 J hMI
  obtain ⟨K,hCover,hUnique,word,hWord,hPos⟩ :=
    original_terminal_full_MI_cover_layer_reachable
      S H sap cco nr2 Jfull hJ hFullMI
  refine ⟨K,hCover,hUnique,?_,word,hWord,hPos⟩
  exact terminal_all_exact S H (sortNR2_of_originalNR2 S H nr2) K

end CCO.TerminalProfiles
