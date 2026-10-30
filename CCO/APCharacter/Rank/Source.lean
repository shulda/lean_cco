import CCO.PairHomogeneity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.Finite

/-! Canonical unary refinements retain every old binary name.  Their palette
consists of the old colours which actually occur between the selected children.
No homogeneity, AP or CCO is used to construct this actual source. -/

universe u v w t
namespace CCO.APCharacter.Rank

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable (β : ι → Type t) (tag : ∀ i, X i → β i)

abbrev Child := Sigma β
abbrev Point (c : Child β) := {x : X c.1 // tag c.1 x = c.2}

def forget (p : Sigma (Point β tag)) : Sigma X := ⟨p.1.1, p.2.val⟩

theorem forget_injective : Function.Injective (forget β tag) := by
  rintro ⟨⟨i,b⟩,⟨x,hx⟩⟩ ⟨⟨j,c⟩,⟨y,hy⟩⟩ h
  have hij : i = j := congrArg Sigma.fst h
  subst j
  have hxy : x = y := by simpa [forget] using h
  subst y
  have hbc : b = c := hx.symm.trans hy
  subst c
  rfl

def Occurs (c d : Child β) (a : S.Atom c.1 d.1) : Prop :=
  ∃ x : Point β tag c, ∃ y : Point β tag d, S.colour x.val y.val = some a

abbrev Colour (c d : Child β) := {a : S.Atom c.1 d.1 // Occurs S β tag c d a}

noncomputable def colour {c d : Child β} (x : Point β tag c) (y : Point β tag d) :
    Option (Colour S β tag c d) :=
  match h : S.colour x.val y.val with
  | none => none
  | some a => some ⟨a, x, y, h⟩

theorem colour_map {c d : Child β} (x : Point β tag c) (y : Point β tag d) :
    (colour S β tag x y).map Subtype.val = S.colour x.val y.val := by
  unfold colour
  split <;> simp_all

theorem colour_some_iff {c d : Child β} (x : Point β tag c) (y : Point β tag d)
    (a : Colour S β tag c d) :
    colour S β tag x y = some a ↔ S.colour x.val y.val = some a.val := by
  unfold colour
  split <;> simp_all [Subtype.ext_iff]

theorem colour_none_iff {c d : Child β} (x : Point β tag c) (y : Point β tag d) :
    colour S β tag x y = none ↔ (⟨c,x⟩ : Sigma (Point β tag)) = ⟨d,y⟩ := by
  have hm : colour S β tag x y = none ↔ S.colour x.val y.val = none := by
    unfold colour
    split <;> simp_all
  rw [hm, S.colour_none_iff]
  exact ⟨fun h => forget_injective β tag h, fun h => congrArg (forget β tag) h⟩

noncomputable def source [∀ i, Fintype (β i)]
    (inhabited : ∀ c, Nonempty (Point β tag c)) :
    AtomicSource (Child β) (Point β tag) := by
  classical
  letI := S.finiteSort
  letI := S.finiteAtom
  exact {
    Atom := Colour S β tag
    finiteSort := inferInstance
    finiteAtom := fun _ _ => inferInstance
    nonemptySort := inhabited
    conv := fun a => ⟨S.conv a.val, by
      obtain ⟨x,y,h⟩ := a.property
      exact ⟨y,x,(S.colour_swap x.val y.val a.val).mp h⟩⟩
    conv_invol := fun a => Subtype.ext (S.conv_invol a.val)
    symmetricLoop := fun a => Subtype.ext (S.symmetricLoop a.val)
    colour := colour S β tag
    colour_none_iff := colour_none_iff S β tag
    colour_swap := by
      intro c d x y a
      rw [colour_some_iff, colour_some_iff]
      exact S.colour_swap x.val y.val a.val
    realized := by
      intro c d a
      obtain ⟨x,y,h⟩ := a.property
      exact ⟨x,y,(colour_some_iff S β tag x y a).mpr h⟩ }

/-- Missing a single old diversity colour strictly decreases the palette.
The palette is an actual occurring-colour subtype, not a supplied cardinal. -/
theorem child_card_lt [∀ i, Fintype (β i)]
    (inhabited : ∀ c, Nonempty (Point β tag c)) (c : Child β)
    (a : S.Atom c.1 c.1) (missing : ¬ Occurs S β tag c c a) :
    Nat.card ((source S β tag inhabited).Atom c c) < Nat.card (S.Atom c.1 c.1) := by
  classical
  change Nat.card (Colour S β tag c c) < Nat.card (S.Atom c.1 c.1)
  letI := S.finiteAtom
  simpa only [Nat.card_eq_fintype_card, Colour] using
    (Fintype.card_subtype_lt missing)

theorem child_card_le_pred [∀ i, Fintype (β i)]
    (inhabited : ∀ c, Nonempty (Point β tag c)) (c : Child β)
    (a : S.Atom c.1 c.1) (missing : ¬ Occurs S β tag c c a) :
    Nat.card ((source S β tag inhabited).Atom c c) ≤ Nat.card (S.Atom c.1 c.1) - 1 :=
  Nat.le_sub_one_of_lt (child_card_lt S β tag inhabited c a missing)

/-- An inactive parent with one unary label keeps its entire actual palette. -/
theorem inactive_card [∀ i, Fintype (β i)]
    (inhabited : ∀ c, Nonempty (Point β tag c)) (i : ι) (b : β i)
    [Subsingleton (β i)] :
    Nat.card ((source S β tag inhabited).Atom ⟨i,b⟩ ⟨i,b⟩) = Nat.card (S.Atom i i) := by
  classical
  change Nat.card (Colour S β tag ⟨i,b⟩ ⟨i,b⟩) = Nat.card (S.Atom i i)
  apply Nat.card_congr
  apply Equiv.ofBijective (fun a : Colour S β tag ⟨i,b⟩ ⟨i,b⟩ => a.val)
  refine ⟨Subtype.coe_injective,?_⟩
  intro a
  obtain ⟨x,y,h⟩ := S.realized a
  exact ⟨⟨a,⟨⟨x,Subsingleton.elim _ _⟩,⟨y,Subsingleton.elim _ _⟩,h⟩⟩,rfl⟩

end CCO.APCharacter.Rank
