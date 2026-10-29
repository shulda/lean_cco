import CCO.FinitePackets.Normalization.Examples.TwinExact
import CCO.RawExact.QuotientSourcePalette
import CCO.RawExact.CanonicalQuotients

/-! The literal quotient by the finite twin packets. Its actual induced
pair-orbital palette has three diversity atoms, strictly below the four
original atoms. No quotient-source inheritance is needed for this count. -/
namespace CCO.FinitePackets.Normalization.Examples.Twin
open Colour

abbrev Cell := ℕ × ℕ
def cell (x : Point) : Cell := (row x,column x)

noncomputable instance cellMulAction : MulAction Aut Cell where
  smul g p := (autRow g p.1,autColumn g p.2)
  one_smul p := by
    change (autRow 1 p.1,autColumn 1 p.2) = p
    have hr := aut_row (1 : Aut) (p.1,p.2,false)
    have hc := aut_column (1 : Aut) (p.1,p.2,false)
    simp only [one_smul] at hr hc
    exact Prod.ext hr.symm hc.symm
  mul_smul g h p := by
    change (autRow (g*h) p.1,autColumn (g*h) p.2) =
      (autRow g (autRow h p.1),autColumn g (autColumn h p.2))
    have hr := aut_row (g*h) (p.1,p.2,false)
    have hc := aut_column (g*h) (p.1,p.2,false)
    simp only [mul_smul,aut_row,aut_column] at hr hc
    exact Prod.ext hr.symm hc.symm

@[simp] theorem cell_equivariant (g : Aut) (x : Point) : cell (g • x) = g • cell x :=
  Prod.ext (aut_row g x) (aut_column g x)

theorem cell_surjective : Function.Surjective cell := fun p => ⟨(p.1,p.2,false),rfl⟩

@[simp] theorem cell_kernel (x y : Point) : cell x = cell y ↔ packetEq x y :=
  by change (row x,column x) = (row y,column y) ↔ row x = row y ∧ column x = column y; simp only [Prod.mk.injEq]

/-- This is the actual Quotient of the proved full finite packet relation. -/
def packetQuotientEquiv : Quotient packetEq.val ≃ Cell where
  toFun := Quotient.lift cell (fun _ _ h => (cell_kernel _ _).mpr h)
  invFun p := Quotient.mk'' (p.1,p.2,false)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ x => exact Quotient.sound (show packetEq (row x,column x,false) x from ⟨rfl,rfl⟩)
  right_inv _ := rfl

instance packetInvariant : RawExact.CanonicalQuotients.Invariant Aut packetEq.val where
  invariant g x y h := by
    change row (g • x) = row (g • y) ∧ column (g • x) = column (g • y)
    simp only [aut_row,aut_column]
    exact ⟨congrArg (autRow g) h.1,congrArg (autColumn g) h.2⟩

@[simp] theorem packetQuotientEquiv_equivariant (g : Aut) (q : Quotient packetEq.val) :
    packetQuotientEquiv (g • q) = g • packetQuotientEquiv q := by
  induction q using Quotient.inductionOn with
  | _ x => exact cell_equivariant g x

def cellColour (p q : Cell) : Option Colour :=
  if p.1 = q.1 then if p.2 = q.2 then none else some Colour.row
  else if p.2 = q.2 then some Colour.column else some apart

@[simp] theorem cellColour_none (p q : Cell) : cellColour p q = none ↔ p = q := by
  simp only [cellColour,Prod.mk.injEq]
  split_ifs <;> simp_all [Prod.ext_iff]

@[simp] theorem cellColour_ne_twin (p q : Cell) : cellColour p q ≠ some twin := by
  unfold cellColour
  split_ifs <;> decide

private theorem coordinates_of_cellColour_eq {p q p' q' : Cell}
    (h : cellColour p q = cellColour p' q') :
    (p.1 = q.1 ↔ p'.1 = q'.1) ∧ (p.2 = q.2 ↔ p'.2 = q'.2) := by
  have hc : colour (p.1,p.2,false) (q.1,q.2,false) =
      colour (p'.1,p'.2,false) (q'.1,q'.2,false) := by
    simpa only [colour,row,column,bit,ite_true,cellColour] using h
  exact coordinates_of_colour_eq hc

private theorem cellColour_eq_of_coordinates {p q p' q' : Cell}
    (hr : p.1 = q.1 ↔ p'.1 = q'.1) (hc : p.2 = q.2 ↔ p'.2 = q'.2) :
    cellColour p q = cellColour p' q' := by
  simp only [cellColour,hr,hc]

/-- Pair colours classify the actual induced G-orbits on the entire quotient,
including the diagonal. Arbitrary pairs are moved by genuine original motions. -/
theorem cell_orbital_iff (p q p' q' : Cell) :
    GroupActions.orbital (G := Aut) p q p' q' ↔ cellColour p q = cellColour p' q' := by
  constructor
  · rintro ⟨g,rfl,rfl⟩
    apply cellColour_eq_of_coordinates
    · exact (autRow g).injective.eq_iff.symm
    · exact (autColumn g).injective.eq_iff.symm
  · intro h
    obtain ⟨hr,hc⟩ := coordinates_of_cellColour_eq h
    let f (b : Bool) : ℕ := if b then q.1 else p.1
    let f' (b : Bool) : ℕ := if b then q'.1 else p'.1
    let k (b : Bool) : ℕ := if b then q.2 else p.2
    let k' (b : Bool) : ℕ := if b then q'.2 else p'.2
    obtain ⟨ρ,hρ⟩ := SIR.Positive.Direct.exists_perm_of_kernel f f' (by
      intro b c
      cases b <;> cases c <;> simp_all [f,f',eq_comm])
    obtain ⟨κ,hκ⟩ := SIR.Positive.Direct.exists_perm_of_kernel k k' (by
      intro b c
      cases b <;> cases c <;> simp_all [k,k',eq_comm])
    refine ⟨motion ρ κ (fun _ _ => false),?_,?_⟩
    · change (ρ p.1,κ p.2) = p'
      exact Prod.ext (by simpa only [f,f',Bool.false_eq_true,ite_false] using hρ false)
        (by simpa only [k,k',Bool.false_eq_true,ite_false] using hκ false)
    · change (ρ q.1,κ q.2) = q'
      exact Prod.ext (by simpa only [f,f',ite_true] using hρ true)
        (by simpa only [k,k',ite_true] using hκ true)

abbrev CellColour := {a : Colour // a ≠ twin}

@[simp] theorem cellColour_card : Fintype.card CellColour = 3 := by decide

def cellRepresentative (a : CellColour) : Cell :=
  match a.val with
  | twin => (0,0)
  | Colour.row => (0,1)
  | Colour.column => (1,0)
  | apart => (1,1)

theorem cellRepresentative_colour (a : CellColour) :
    cellColour (0,0) (cellRepresentative a) = some a.val := by
  rcases a with ⟨a,ha⟩
  cases a
  · exact False.elim (ha rfl)
  · rfl
  · rfl
  · rfl

abbrev ActualCellAtom := RawExact.QuotientPalette.DiversityAtom (G := Aut) (fun _ : Unit => Cell) () ()

def cellAtom (a : CellColour) : ActualCellAtom := by
  refine ⟨fun p q => cellColour p q = some a.val,?_,?_⟩
  · refine ⟨(0,0),cellRepresentative a,?_⟩
    funext p q
    exact propext ((cell_orbital_iff (0,0) (cellRepresentative a) p q).trans
      (by rw [cellRepresentative_colour]; exact eq_comm)).symm
  · intro p q hp he
    have hpq : p = q := congrArg (fun s : Sigma (fun _ : Unit => Cell) => s.2) he
    subst q
    have hz := (cellColour_none p p).mpr rfl
    rw [hz] at hp
    cases hp

/-- The names correspond bijectively to ACTUAL orbital relations, rather than
merely being a three-element language decorating the quotient. -/
noncomputable def actualCellAtomEquiv : ActualCellAtom ≃ CellColour := by
  let e : CellColour ≃ ActualCellAtom := Equiv.ofBijective cellAtom (by
    constructor
    · intro a b hab
      apply Subtype.ext
      have ha := cellRepresentative_colour a
      have hb : cellColour (0,0) (cellRepresentative a) = some b.val := by
        have he := congrArg (fun c : ActualCellAtom => c.val (0,0) (cellRepresentative a)) hab
        exact Eq.mp he ha
      exact Option.some.inj (ha.symm.trans hb)
    · intro a
      obtain ⟨p,q,hpq⟩ := a.property.1
      have horb := GroupActions.orbital_nonempty (G := Aut) p q
      have hne : p ≠ q := by
        intro he
        apply a.property.2 p q (by rw [hpq]; exact horb)
        exact Sigma.ext rfl (heq_of_eq he)
      cases hc : cellColour p q with
      | none => exact False.elim (hne ((cellColour_none p q).mp hc))
      | some c =>
        let b : CellColour := ⟨c,fun ht => cellColour_ne_twin p q (hc.trans (congrArg some ht))⟩
        refine ⟨b,?_⟩
        apply Subtype.ext
        funext u v
        rw [hpq]
        exact propext ((cell_orbital_iff p q u v).trans
          (by rw [hc]; exact eq_comm)).symm)
  exact e.symm

theorem quotient_diversity_card : Nat.card ActualCellAtom = 3 := by
  rw [Nat.card_congr actualCellAtomEquiv]
  exact Nat.card_eq_fintype_card.trans cellColour_card

theorem quotient_palette_strictly_decreases : Nat.card ActualCellAtom < Nat.card Colour := by
  rw [quotient_diversity_card,Nat.card_eq_fintype_card,colour_card]
  decide

end CCO.FinitePackets.Normalization.Examples.Twin
