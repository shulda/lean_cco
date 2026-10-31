import CCO.TerminalLattice.OldAbsorption
import CCO.TerminalLattice.OriginalStrongAlgebra
import CCO.TerminalLattice.FibreSAP

/-!
# B050 C28: original K-diversity spoke absorbs ANY finite old K-path

The source's centre-cycle argument does not need one positive exact
word per intermediate edge yet. Its strictly algebraic assertion is:
a genuine K^circ spoke followed by ANY finite sequence of nonempty
same-sort OLD STRONG menus inside K^circ still has endpoint spectrum
exactly K^circ. The final closing K^circ spoke also preserves it.

This module consumes the already green SOURCE C24 absorption proof
from original SAP and does not use CCO, reset conclusion, NR2,
mixed-sort commutation or an exact-domain identity. A separate
private-word graph module must still realize each specified cycle.
-/

universe u v w t
namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Original K-diversity spoke followed by a finite list of literal
same-sort STRONG menus. The empty list represents a SPOKE, not a
new fictitious identity menu. -/
def originalKSpokePath {i : ι}
    (K : ColourEq S i) (ds : List (S.Menu i i)) : S.Menu i i :=
  ds.foldl (fun U V => S.product U V)
    (originalEquivDiversityPalette S K)

/-- SOURCE C28 algebraic core: for each finite nonempty-factor path
inside the original K-equivalence, K^circ absorbs the whole path.
No application of full CCO completion is made here. -/
theorem originalKSpokePath_absorbed
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (K : ColourEq S i) (ds : List (S.Menu i i))
    (hAll : ∀ D ∈ ds,
      D.Nonempty ∧ D ⊆ originalEquivDiversityPalette S K) :
    originalKSpokePath S K ds =
      originalEquivDiversityPalette S K := by
  induction ds with
  | nil =>
      rfl
  | cons D ds ih =>
      have hD : D.Nonempty ∧ D ⊆ originalEquivDiversityPalette S K :=
        hAll D (List.mem_cons_self)
      have hTail : ∀ E ∈ ds,
          E.Nonempty ∧ E ⊆ originalEquivDiversityPalette S K :=
        fun E hE => hAll E (List.mem_cons_of_mem D hE)
      change ds.foldl (fun U V => S.product U V)
        (S.product (originalEquivDiversityPalette S K) D) =
          originalEquivDiversityPalette S K
      rw [original_equiv_diversity_absorbs S H sap K D hD.1 hD.2]
      exact ih hTail

/-- Strict nonzero original invariant equivalences have a genuinely
nonempty OLD diversity palette; the witness is an ACTUAL original fine
colour of two distinct points, never an equality atom. -/
theorem original_nonzero_Kdiv_nonempty
    {i : ι} (K : ColourEq S i)
    (hK : (⊥ : ColourEq S i) < K) :
    (originalEquivDiversityPalette S K).Nonempty := by
  obtain ⟨x, y, hKxy, hxy⟩ := actual_nontrivial_equiv_pair S K hK
  have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
    intro heq
    have h : x = y := by
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using heq
    exact hxy h
  obtain ⟨c, hc⟩ := S.some_colour_of_ne x y hTag
  exact ⟨c, x, y, hKxy, hc⟩

/-- Original K-diversity is itself an absorbing right closing spoke.
This is not a synthetic STRONG identity: K^circ is nonempty because
K is a genuinely nonzero ORIGINAL invariant equivalence. -/
theorem originalKSpokePath_closed_by_K
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (K : ColourEq S i) (hK : (⊥ : ColourEq S i) < K)
    (ds : List (S.Menu i i))
    (hAll : ∀ D ∈ ds,
      D.Nonempty ∧ D ⊆ originalEquivDiversityPalette S K) :
    S.product (originalKSpokePath S K ds)
        (originalEquivDiversityPalette S K) =
      originalEquivDiversityPalette S K := by
  have hPath := originalKSpokePath_absorbed S H sap K ds hAll
  have hNe := original_nonzero_Kdiv_nonempty S K hK
  rw [hPath]
  exact original_equiv_diversity_absorbs S H sap K
    (originalEquivDiversityPalette S K) hNe (fun _ h => h)

/-- The endpoint spectra of the two OLD K spokes and any intervening
nonempty K-path have a genuine common OLD diversity atom. This is a
cycle-by-cycle menu fact only, not a simultaneous CCO completion. -/
theorem original_centre_cycle_common_fine_atom
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (K : ColourEq S i) (hK : (⊥ : ColourEq S i) < K)
    (ds : List (S.Menu i i))
    (hAll : ∀ D ∈ ds,
      D.Nonempty ∧ D ⊆ originalEquivDiversityPalette S K) :
    (S.product (originalKSpokePath S K ds)
       (originalEquivDiversityPalette S K)).Nonempty := by
  rw [originalKSpokePath_closed_by_K S H sap K hK ds hAll]
  exact original_nonzero_Kdiv_nonempty S K hK

end CCO.TerminalLattice
