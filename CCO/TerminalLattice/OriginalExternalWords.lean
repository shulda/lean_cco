import CCO.TerminalLattice.OriginalExternalLabels
import CCO.TerminalLattice.CompleteOrbitalWord

/-!
# B050 C31: one ACTUAL positive old typed word for every external graph label

Every finite index of the original external fine-atom family has a
genuine OLD real representative. The already-proved narrow same-J
saturation constructs one positive OLD atomic word with exactly its
COMPLETE original-G quotient-orbital STRONG endpoint profile.

Only the source premises original homogeneity + SAP + J>Id + one
positive word for J-diversity are used. No K-positivity, CCO,
NR2, quotient SAP, B049 import or invented word provider.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- The finite external-index family supplies actual original typed
positive words for ALL labels, selected from the previously proved
source C23 complete-orbital positive-word theorem. Their private
interiors may have arbitrary original named sorts. -/
noncomputable def originalIndexedExternalPositiveWords
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J K : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J) :
    Fin (Fintype.card (OriginalExternalAtom S J K)) →
      PositiveWord S i i :=
  fun j =>
    let c : OriginalExternalAtom S J K :=
      (Fintype.equivFin (OriginalExternalAtom S J K)).symm j
    let p := originalExternalAtomWitness S J K c
    Classical.choose
      (originalQuotientOrbital_positive_word
        S H sap J hJ wJ hwJ c.val
          p.val.1 p.val.2 p.property.2.2)

/-- Exact source C31 word-to-labelled-complete-menu equality, with
the actual old source09 C23 theorem discharging every individual
word, not a hypothetical finite word oracle. -/
theorem originalIndexedExternalPositiveWords_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J K : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (j : Fin (Fintype.card (OriginalExternalAtom S J K))) :
    PositiveWord.profile S
      (originalIndexedExternalPositiveWords
        S H sap J K hJ wJ hwJ j) =
      originalIndexedExternalOrbitalMenus S (G := G) J K j := by
  let c : OriginalExternalAtom S J K :=
    (Fintype.equivFin (OriginalExternalAtom S J K)).symm j
  let p := originalExternalAtomWitness S J K c
  change PositiveWord.profile S
      (Classical.choose
        (originalQuotientOrbital_positive_word
          S H sap J hJ wJ hwJ c.val
            p.val.1 p.val.2 p.property.2.2)) =
      originalQuotientOrbitalPalette S (G := G)
        J p.val.1 p.val.2
  exact Classical.choose_spec
    (originalQuotientOrbital_positive_word
      S H sap J hJ wJ hwJ c.val
        p.val.1 p.val.2 p.property.2.2)

end CCO.TerminalLattice
