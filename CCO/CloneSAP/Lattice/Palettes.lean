import CCO.ParityHasse.Original.OrbitalAlgebra
import CCO.ParityHasse.Original.RelativeIndices
import Mathlib.Data.Fintype.Powerset

/-! B045 D07–D08, C27–C33. The independent symmetric palette lattice.
Only the original finite atomic source and its homogeneity occur. -/

universe u v w t
namespace CCO.CloneSAP.Lattice
open CCO.ParityHasse.Original
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X) (i : ι)

/-- Logical equality is added to the diversity palette, not made a colour. -/
def relation (P : Set (S.Atom i i)) (x y : X i) : Prop :=
  x = y ∨ ∃ a ∈ P, S.colour x y = some a

abbrev Palette := {P : Set (S.Atom i i) // Equivalence (relation S i P)}

def paletteOf (E : ColourEq S i) : Set (S.Atom i i) :=
  {a | ∃ x y, E x y ∧ S.colour x y = some a}

theorem relation_paletteOf (E : ColourEq S i) (x y : X i) :
    relation S i (paletteOf S i E) x y ↔ E x y := by
  constructor
  · rintro (rfl | ⟨a, ⟨p, q, hpq, hc⟩, hxy⟩)
    · exact E.val.refl x
    · exact (E.2 p q x y (hc.trans hxy.symm)).mp hpq
  · intro h
    by_cases he : x = y
    · exact Or.inl he
    · cases hc : S.colour x y with
      | none => exact False.elim (he (by simpa using (S.colour_none_iff x y).mp hc))
      | some a => exact Or.inr ⟨a, ⟨x, y, h, hc⟩, hc⟩

theorem relation_invariant (P : Set (S.Atom i i)) :
    ColourInvariant S i (relation S i P) := by
  intro x y z q hc
  have he : x = y ↔ z = q := by
    have hh : S.colour x y = none ↔ S.colour z q = none := by rw [hc]
    simpa only [S.colour_none_iff, Sigma.mk.injEq, heq_eq_eq, true_and] using hh
  simp only [relation, hc, he]

def toColourEq (P : Palette S i) : ColourEq S i :=
  ⟨⟨relation S i P.val, P.property⟩, relation_invariant S i P.val⟩

def ofColourEq (E : ColourEq S i) : Palette S i :=
  ⟨paletteOf S i E, by
    refine ⟨?_, ?_, ?_⟩
    · intro x; exact (relation_paletteOf S i E x x).mpr (E.val.refl x)
    · intro x y h; exact (relation_paletteOf S i E y x).mpr
        (E.val.symm ((relation_paletteOf S i E x y).mp h))
    · intro x y z h k; exact (relation_paletteOf S i E x z).mpr
        (E.val.trans ((relation_paletteOf S i E x y).mp h)
          ((relation_paletteOf S i E y z).mp k))⟩

@[simp] theorem to_of (E : ColourEq S i) : toColourEq S i (ofColourEq S i E) = E := by
  apply ColourEq.ext
  exact relation_paletteOf S i E

@[simp] theorem of_to (P : Palette S i) : ofColourEq S i (toColourEq S i P) = P := by
  apply Subtype.ext
  ext a
  constructor
  · rintro ⟨x, y, (he | ⟨b, hb, hc⟩), ha⟩
    · subst y
      have hn := (S.colour_none_iff x x).mpr rfl
      rw [hn] at ha
      cases ha
    · exact Option.some.inj (hc.symm.trans ha) ▸ hb
  · intro ha
    obtain ⟨x, y, hxy⟩ := S.realized a
    exact ⟨x, y, Or.inr ⟨a, ha, hxy⟩, hxy⟩

instance : PartialOrder (Palette S i) := inferInstanceAs (PartialOrder {P : Set _ // _})

/-- Unique palette representation of ALL colour-invariant equivalences. -/
def paletteOrderIso : Palette S i ≃o ColourEq S i where
  toFun := toColourEq S i
  invFun := ofColourEq S i
  left_inv := of_to S i
  right_inv := to_of S i
  map_rel_iff' := by
    intro P Q
    constructor
    · intro h a ha
      obtain ⟨x, y, hxy⟩ := S.realized a
      have hh := h (show toColourEq S i P x y from Or.inr ⟨a, ha, hxy⟩)
      rcases hh with he | ⟨b, hb, hc⟩
      · subst y
        have hn := (S.colour_none_iff x x).mpr rfl
        rw [hn] at hxy
        cases hxy
      · exact Option.some.inj (hc.symm.trans hxy) ▸ hb
    · intro h x y hh
      rcases hh with he | ⟨a, ha, hc⟩
      · exact Or.inl he
      · exact Or.inr ⟨a, h ha, hc⟩

instance : Finite (Palette S i) := Finite.of_injective _ (paletteOrderIso S i).injective

theorem palette_card_bound :
    Nat.card (Palette S i) ≤ 2 ^ Nat.card (S.Atom i i) := by
  letI := S.finiteAtom i i
  have h := Nat.card_le_card_of_injective
    (fun P : Palette S i => P.val) Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card, Fintype.card_set] using h

def bottom : Palette S i := ofColourEq S i ⊥
def top : Palette S i := ofColourEq S i ⊤

theorem bottom_eq_empty : (bottom S i).val = ∅ := by
  ext a
  constructor
  · rintro ⟨x, y, h, hc⟩
    change x = y at h
    subst y
    have hn := (S.colour_none_iff x x).mpr rfl
    rw [hn] at hc
    cases hc
  · exact False.elim

theorem top_eq_univ : (top S i).val = Set.univ := by
  ext a
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨x, y, hc⟩ := S.realized a
    exact ⟨x, y, trivial, hc⟩

/-- C30 exposes the logical-diagonal cases rather than discarding them. -/
theorem degenerate_reverse (P Q : Palette S i) (x y z : X i)
    (hP : relation S i P.val x y) (hQ : relation S i Q.val y z)
    (he : x = y ∨ y = z ∨ x = z) :
    ∃ a, relation S i Q.val x a ∧ relation S i P.val a z := by
  rcases he with rfl | rfl | rfl
  · exact ⟨z, hQ, P.property.refl z⟩
  · exact ⟨x, Q.property.refl x, hP⟩
  · exact ⟨x, Q.property.refl x, P.property.refl x⟩

variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]
variable (H : HomogeneousSource S G)

/-- The finite lattice is transported along the literal palette order. -/
@[instance_reducible] def lattice : Lattice (Palette S i) := by
  letI := ColourEq.lattice S H (i := i)
  exact
    { (inferInstance : PartialOrder (Palette S i)) with
      sup := fun P Q => ofColourEq S i (toColourEq S i P ⊔ toColourEq S i Q)
      inf := fun P Q => ofColourEq S i (toColourEq S i P ⊓ toColourEq S i Q)
      le_sup_left := fun P Q => (paletteOrderIso S i).le_iff_le.mp (by
        change toColourEq S i P ≤ toColourEq S i (ofColourEq S i _)
        rw [to_of]; exact le_sup_left)
      le_sup_right := fun P Q => (paletteOrderIso S i).le_iff_le.mp (by
        change toColourEq S i Q ≤ toColourEq S i (ofColourEq S i _)
        rw [to_of]; exact le_sup_right)
      sup_le := fun P Q R hP hQ => (paletteOrderIso S i).le_iff_le.mp (by
        change toColourEq S i (ofColourEq S i _) ≤ toColourEq S i R
        rw [to_of]; exact sup_le ((paletteOrderIso S i).monotone hP) ((paletteOrderIso S i).monotone hQ))
      inf_le_left := fun P Q => (paletteOrderIso S i).le_iff_le.mp (by
        change toColourEq S i (ofColourEq S i _) ≤ toColourEq S i P
        rw [to_of]; exact inf_le_left)
      inf_le_right := fun P Q => (paletteOrderIso S i).le_iff_le.mp (by
        change toColourEq S i (ofColourEq S i _) ≤ toColourEq S i Q
        rw [to_of]; exact inf_le_right)
      le_inf := fun P Q R hQ hR => (paletteOrderIso S i).le_iff_le.mp (by
        change toColourEq S i P ≤ toColourEq S i (ofColourEq S i _)
        rw [to_of]; exact le_inf ((paletteOrderIso S i).monotone hQ) ((paletteOrderIso S i).monotone hR)) }

/-- Literal palette intersection, including the empty diversity palette. -/
theorem meet_eq_inter (P Q : Palette S i) :
    letI := lattice S i H
    (P ⊓ Q).val = P.val ∩ Q.val := by
  letI := lattice S i H
  change paletteOf S i (toColourEq S i P ⊓ toColourEq S i Q) = P.val ∩ Q.val
  ext a
  constructor
  · rintro ⟨x, y, ⟨hP, hQ⟩, hc⟩
    have hPM : a ∈ paletteOf S i (toColourEq S i P) := ⟨x, y, hP, hc⟩
    have hQM : a ∈ paletteOf S i (toColourEq S i Q) := ⟨x, y, hQ, hc⟩
    have p := congrArg Subtype.val (of_to S i P)
    have q := congrArg Subtype.val (of_to S i Q)
    exact ⟨p ▸ hPM, q ▸ hQM⟩
  · intro ha
    obtain ⟨x, y, hc⟩ := S.realized a
    exact ⟨x, y, ⟨Or.inr ⟨a, ha.1, hc⟩, Or.inr ⟨a, ha.2, hc⟩⟩, hc⟩

/-- Full represented product includes all equality and degenerate witnesses. -/
theorem join_composition (P Q : Palette S i) (x z : X i) :
    letI := lattice S i H
    relation S i (P ⊔ Q).val x z ↔
      ∃ y, relation S i P.val x y ∧ relation S i Q.val y z := by
  letI := ColourEq.lattice S H (i := i)
  letI := lattice S i H
  change toColourEq S i (ofColourEq S i (toColourEq S i P ⊔ toColourEq S i Q)) x z ↔ _
  rw [to_of]
  exact sup_relation_iff S H (toColourEq S i P) (toColourEq S i Q) x z

/-- C30/C31: the same-sort endpoint swap reverses even degenerate paths. -/
theorem composition_commutes (H : HomogeneousSource S G) (P Q : Palette S i) :
    RawSymmetric.compose (relation S i P.val) (relation S i Q.val) =
      RawSymmetric.compose (relation S i Q.val) (relation S i P.val) :=
  invariant_relations_commute S H (relation_invariant S i P.val) (relation_invariant S i Q.val)

/-- Actual relative class sets are in bijection on every base class;
no finite-index assumption occurs. -/
noncomputable def relativeClassEquiv (P Q : Palette S i) (a b : X i) :
    RelativeClass (toColourEq S i P).val (toColourEq S i Q).val a ≃
      RelativeClass (toColourEq S i P).val (toColourEq S i Q).val b :=
  uniformRelativeClassEquiv S H (toColourEq S i P) (toColourEq S i Q) a b

end CCO.CloneSAP.Lattice
