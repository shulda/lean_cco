import CCO.Selectors.PriorityLex
import Mathlib.Data.Fintype.EquivFin

/-!
# Converse-invariant deterministic tie-breaking on original atom palettes

Choose a finite index of all globally tagged atoms. Each atom and its
converse represent one unoriented orbit; take the smaller index of those
two tagged representatives. This produces an injective code within every
individual original hom-palette and the very same code under converse.
No new symmetry of mixed-sort palettes is assumed.
-/

universe u v w
namespace CCO.Selectors
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

abbrev TaggedAtom := Σ i : ι, Σ j : ι, S.Atom i j

def flipAtom (p : TaggedAtom S) : TaggedAtom S :=
  ⟨p.2.1, p.1, S.conv p.2.2⟩

theorem flipAtom_invol (p : TaggedAtom S) :
    flipAtom S (flipAtom S p) = p := by
  rcases p with ⟨i,j,a⟩
  simp only [flipAtom, S.conv_invol]

noncomputable instance taggedAtomFintype : Fintype (TaggedAtom S) := by
  letI := S.finiteSort
  letI : ∀ i j, Fintype (S.Atom i j) := S.finiteAtom
  exact Fintype.ofFinite _

noncomputable def taggedAtomCode (p : TaggedAtom S) : Nat :=
  ((Fintype.equivFin (TaggedAtom S)) p).val

theorem taggedAtomCode_injective :
    Function.Injective (taggedAtomCode S) := by
  intro p q h
  exact (Fintype.equivFin (TaggedAtom S)).injective (Fin.ext h)

theorem taggedAtom_eq_same {i j : ι} {a b : S.Atom i j}
    (h : (⟨i,j,a⟩ : TaggedAtom S) = ⟨i,j,b⟩) : a = b := by
  simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using h

theorem taggedAtom_eq_flip {i j : ι} {a b : S.Atom i j}
    (h : (⟨i,j,a⟩ : TaggedAtom S) = flipAtom S ⟨i,j,b⟩) : a = b := by
  have hij : i = j := congrArg Sigma.fst h
  subst j
  change (⟨i,i,a⟩ : TaggedAtom S) = ⟨i,i,S.conv b⟩ at h
  have hs : (⟨i,i,a⟩ : TaggedAtom S) = ⟨i,i,b⟩ := by
    simpa only [S.symmetricLoop] using h
  exact taggedAtom_eq_same S hs

/-- The canonical index of the unordered two-element converse orbit.
It is an index of original atoms, not of output menus. -/
noncomputable def atomTie {i j : ι} (a : S.Atom i j) : Nat :=
  min (taggedAtomCode S ⟨i,j,a⟩)
      (taggedAtomCode S ⟨j,i,S.conv a⟩)

theorem atomTie_reverse {i j : ι} (a : S.Atom i j) :
    atomTie S (S.conv a) = atomTie S a := by
  simp only [atomTie, S.conv_invol, Nat.min_comm]

theorem atomTie_injective (i j : ι) :
    Function.Injective (atomTie S (i := i) (j := j)) := by
  intro a b h
  let ta : TaggedAtom S := ⟨i,j,a⟩
  let tb : TaggedAtom S := ⟨i,j,b⟩
  change min (taggedAtomCode S ta) (taggedAtomCode S (flipAtom S ta)) =
    min (taggedAtomCode S tb) (taggedAtomCode S (flipAtom S tb)) at h
  rcases le_total (taggedAtomCode S ta)
      (taggedAtomCode S (flipAtom S ta)) with ha | ha
  · rw [min_eq_left ha] at h
    rcases le_total (taggedAtomCode S tb)
        (taggedAtomCode S (flipAtom S tb)) with hb | hb
    · rw [min_eq_left hb] at h
      exact taggedAtom_eq_same S (taggedAtomCode_injective S h)
    · rw [min_eq_right hb] at h
      exact taggedAtom_eq_flip S (taggedAtomCode_injective S h)
  · rw [min_eq_right ha] at h
    rcases le_total (taggedAtomCode S tb)
        (taggedAtomCode S (flipAtom S tb)) with hb | hb
    · rw [min_eq_left hb] at h
      exact (taggedAtom_eq_flip S (taggedAtomCode_injective S h.symm)).symm
    · rw [min_eq_right hb] at h
      have hflip := taggedAtomCode_injective S h
      have htags : ta = tb := by
        have hf := congrArg (flipAtom S) hflip
        simpa only [flipAtom_invol] using hf
      exact taggedAtom_eq_same S htags

end CCO.Selectors
