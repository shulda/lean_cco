import CCO.RealClosure.Bounds.Examples.CycleConsistency
import CCO.SIR.Positive.Direct.Homogeneity
import CCO.StrongExact.AgeAP
import Mathlib.Data.Fintype.Prod

/-! The actual infinite twin-cell source. Only the twin colour sees the bit;
all other colours forget it. The automorphism group is the FULL colour-
preserving group, with independent flips in every cell. -/
namespace CCO.FinitePackets.Normalization.Examples.Twin

abbrev Point := ℕ × ℕ × Bool
abbrev row (x : Point) : ℕ := x.1
abbrev column (x : Point) : ℕ := x.2.1
abbrev bit (x : Point) : Bool := x.2.2

inductive Colour | twin | row | column | apart
  deriving DecidableEq

open Colour

instance : Fintype Colour where
  elems := {twin,Colour.row,Colour.column,apart}
  complete a := by cases a <;> simp

@[simp] theorem colour_card : Fintype.card Colour = 4 := by decide

def colour (x y : Point) : Option Colour :=
  if row x = row y then
    if column x = column y then if bit x = bit y then none else some twin
    else some Colour.row
  else if column x = column y then some Colour.column else some apart

@[simp] theorem colour_none (x y : Point) : colour x y = none ↔ x = y := by
  rcases x with ⟨r,c,b⟩; rcases y with ⟨s,d,e⟩
  simp only [colour,row,column,bit,Prod.mk.injEq]
  split_ifs <;> simp_all

@[simp] theorem colour_twin (x y : Point) : colour x y = some twin ↔
    row x = row y ∧ column x = column y ∧ bit x ≠ bit y := by
  unfold colour
  split_ifs <;> simp_all

@[simp] theorem colour_row (x y : Point) : colour x y = some Colour.row ↔
    row x = row y ∧ column x ≠ column y := by
  unfold colour
  split_ifs <;> simp_all

@[simp] theorem colour_column (x y : Point) : colour x y = some Colour.column ↔
    row x ≠ row y ∧ column x = column y := by
  unfold colour
  split_ifs <;> simp_all

@[simp] theorem colour_apart (x y : Point) : colour x y = some apart ↔
    row x ≠ row y ∧ column x ≠ column y := by
  unfold colour
  split_ifs <;> simp_all

def rowRead : Colour → Bool | twin | Colour.row => true | _ => false
def columnRead : Colour → Bool | twin | Colour.column => true | _ => false

theorem row_reader (x y : Point) (a : Colour) (h : colour x y = some a) :
    row x = row y ↔ rowRead a = true := by
  cases a <;> simp_all [rowRead]

theorem column_reader (x y : Point) (a : Colour) (h : colour x y = some a) :
    column x = column y ↔ columnRead a = true := by
  cases a <;> simp_all [columnRead]

theorem coordinates_of_colour_eq {x y x' y' : Point}
    (h : colour x y = colour x' y') :
    (row x = row y ↔ row x' = row y') ∧
    (column x = column y ↔ column x' = column y') := by
  cases hc : colour x y with
  | none =>
    have he := (colour_none x y).mp hc
    have he' := (colour_none x' y').mp (h.symm.trans hc)
    subst y; subst y'; simp
  | some a =>
    exact ⟨(row_reader x y a hc).trans (row_reader x' y' a (h.symm.trans hc)).symm,
      (column_reader x y a hc).trans (column_reader x' y' a (h.symm.trans hc)).symm⟩

theorem bits_of_colour_eq {x y x' y' : Point}
    (h : colour x y = colour x' y') (hr : row x = row y) (hc : column x = column y) :
    (bit x ^^ bit y) = (bit x' ^^ bit y') := by
  have hr' := (coordinates_of_colour_eq h).1.mp hr
  have hc' := (coordinates_of_colour_eq h).2.mp hc
  cases hx : bit x <;> cases hy : bit y <;> cases hx' : bit x' <;> cases hy' : bit y' <;>
    simp_all [colour]

theorem colour_symm (x y : Point) : colour x y = colour y x := by
  simp only [colour,eq_comm]

def source : AtomicSource Unit (fun _ => Point) where
  Atom := fun _ _ => Colour
  finiteSort := inferInstance
  finiteAtom := fun _ _ => inferInstance
  nonemptySort := fun _ => ⟨0,0,false⟩
  conv := id
  conv_invol := fun _ => rfl
  symmetricLoop := fun _ => rfl
  colour := colour
  colour_none_iff := by intro i j x y; cases i; cases j; simpa using colour_none x y
  colour_swap := by intro i j x y a; exact congrArg (· = some a) (colour_symm x y) |>.to_iff
  realized := by
    intro i j a
    cases a
    · exact ⟨(0,0,false),(0,0,true),rfl⟩
    · exact ⟨(0,0,false),(0,1,false),rfl⟩
    · exact ⟨(0,0,false),(1,0,false),rfl⟩
    · exact ⟨(0,0,false),(1,1,false),rfl⟩

@[simp] theorem source_colour {i j : Unit} (x y : Point) :
    source.colour (i := i) (j := j) x y = colour x y := rfl

def autGroup : Subgroup (Equiv.Perm Point) where
  carrier := {g | ∀ x y, colour (g x) (g y) = colour x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by intro g h hg hh x y; exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have h := hg (g⁻¹ x) (g⁻¹ y)
    simpa using h.symm
abbrev Aut := autGroup

@[simp] theorem aut_colour (g : Aut) (x y : Point) : colour (g • x) (g • y) = colour x y := g.property x y

def motionPerm (ρ κ : Equiv.Perm ℕ) (δ : ℕ → ℕ → Bool) : Equiv.Perm Point where
  toFun x := (ρ (row x),κ (column x),δ (row x) (column x) ^^ bit x)
  invFun x := (ρ.symm (row x),κ.symm (column x),δ (ρ.symm (row x)) (κ.symm (column x)) ^^ bit x)
  left_inv := by rintro ⟨r,c,b⟩; simp [row,column,bit,Bool.xor_assoc]
  right_inv := by rintro ⟨r,c,b⟩; simp [row,column,bit,Bool.xor_assoc]

@[simp] theorem motionPerm_row (ρ κ : Equiv.Perm ℕ) (δ : ℕ → ℕ → Bool) (x : Point) :
    row (motionPerm ρ κ δ x) = ρ (row x) := rfl
@[simp] theorem motionPerm_column (ρ κ : Equiv.Perm ℕ) (δ : ℕ → ℕ → Bool) (x : Point) :
    column (motionPerm ρ κ δ x) = κ (column x) := rfl
@[simp] theorem motionPerm_bit (ρ κ : Equiv.Perm ℕ) (δ : ℕ → ℕ → Bool) (x : Point) :
    bit (motionPerm ρ κ δ x) = (δ (row x) (column x) ^^ bit x) := rfl

theorem motionPerm_colour (ρ κ : Equiv.Perm ℕ) (δ : ℕ → ℕ → Bool) (x y : Point) :
    colour (motionPerm ρ κ δ x) (motionPerm ρ κ δ y) = colour x y := by
  unfold colour
  simp only [motionPerm_row,motionPerm_column,motionPerm_bit,ρ.injective.eq_iff,κ.injective.eq_iff]
  by_cases hr : row x = row y
  · by_cases hc : column x = column y
    · simp [hr,hc]
    · simp [hr,hc]
  · simp [hr]

def motion (ρ κ : Equiv.Perm ℕ) (δ : ℕ → ℕ → Bool) : Aut :=
  ⟨motionPerm ρ κ δ,motionPerm_colour ρ κ δ⟩

@[simp] theorem motion_row (ρ κ : Equiv.Perm ℕ) (δ : ℕ → ℕ → Bool) (x : Point) :
    row (motion ρ κ δ • x) = ρ (row x) := rfl
@[simp] theorem motion_column (ρ κ : Equiv.Perm ℕ) (δ : ℕ → ℕ → Bool) (x : Point) :
    column (motion ρ κ δ • x) = κ (column x) := rfl
@[simp] theorem motion_bit (ρ κ : Equiv.Perm ℕ) (δ : ℕ → ℕ → Bool) (x : Point) :
    bit (motion ρ κ δ • x) = (δ (row x) (column x) ^^ bit x) := rfl

theorem finite_extension {V : Type*} [Finite V] (f h : V → Point)
    (hc : ∀ v w, colour (f v) (f w) = colour (h v) (h w)) :
    ∃ g : Aut, ∀ v, g • f v = h v := by
  classical
  obtain ⟨ρ,hρ⟩ := SIR.Positive.Direct.exists_perm_of_kernel (fun v => row (f v))
    (fun v => row (h v)) (fun v w => (coordinates_of_colour_eq (hc v w)).1)
  obtain ⟨κ,hκ⟩ := SIR.Positive.Direct.exists_perm_of_kernel (fun v => column (f v))
    (fun v => column (h v)) (fun v w => (coordinates_of_colour_eq (hc v w)).2)
  let occupied (r c : ℕ) := ∃ v, row (f v) = r ∧ column (f v) = c
  let δ (r c : ℕ) : Bool := if he : occupied r c then
    bit (h (Classical.choose he)) ^^ bit (f (Classical.choose he)) else false
  refine ⟨motion ρ κ δ,fun v => ?_⟩
  apply Prod.ext (hρ v)
  apply Prod.ext (hκ v)
  change (δ (row (f v)) (column (f v)) ^^ bit (f v)) = bit (h v)
  have hv : occupied (row (f v)) (column (f v)) := ⟨v,rfl,rfl⟩
  let w := Classical.choose hv
  have hw := Classical.choose_spec hv
  have hg := bits_of_colour_eq (hc v w) hw.1.symm hw.2.symm
  simp only [δ,dif_pos hv]
  change ((bit (h w) ^^ bit (f w)) ^^ bit (f v)) = bit (h v)
  cases hvb : bit (f v) <;> cases hwb : bit (f w) <;> cases hvh : bit (h v) <;> cases hwh : bit (h w) <;> simp_all

theorem homogeneous : HomogeneousSource source Aut where
  preserves_sort := by intro g p; rcases p with ⟨i,x⟩; cases i; rfl
  preserves_colours := by
    intro g p q
    rcases p with ⟨i,x⟩; rcases q with ⟨j,y⟩
    cases i; cases j
    simp only [taggedColour,Sigma.smul_mk,source_colour,aut_colour]
  extends_finite_diagram := by
    intro V _ f h hc
    have hh : ∀ v w, colour (f v).2 (f w).2 = colour (h v).2 (h w).2 := by
      intro v w
      exact congrArg (fun z : Σ _ : Unit, Σ _ : Unit, Option Colour => z.2.2) (hc v w)
    obtain ⟨g,hg⟩ := finite_extension (fun v => (f v).2) (fun v => (h v).2) hh
    refine ⟨g,fun v => Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (hg v))⟩

theorem ageAP : AgeAP source := source.ageAP_of_homogeneous homogeneous

theorem infinite_twin_source : Infinite Point := Infinite.of_injective (fun n : ℕ => (n,0,false))
  (fun _ _ h => congrArg Prod.fst h)

private theorem row_motion (g : Aut) (x : Point) :
    row (g • x) = row (g • (row x,0,false)) :=
  (coordinates_of_colour_eq (aut_colour g x (row x,0,false))).1.mpr rfl
private theorem column_motion (g : Aut) (x : Point) :
    column (g • x) = column (g • (0,column x,false)) :=
  (coordinates_of_colour_eq (aut_colour g x (0,column x,false))).2.mpr rfl

noncomputable def autRow (g : Aut) : Equiv.Perm ℕ :=
  Equiv.ofBijective (fun n => row (g • (n,0,false))) (by
    constructor
    · intro a b hab
      exact (coordinates_of_colour_eq (aut_colour g (a,0,false) (b,0,false))).1.mp hab
    · intro n
      let x : Point := g⁻¹ • (n,0,false)
      refine ⟨row x,?_⟩
      have hh := row_motion g x
      rw [show g • x = (n,0,false) from smul_inv_smul g _] at hh
      exact hh.symm)

noncomputable def autColumn (g : Aut) : Equiv.Perm ℕ :=
  Equiv.ofBijective (fun n => column (g • (0,n,false))) (by
    constructor
    · intro a b hab
      exact (coordinates_of_colour_eq (aut_colour g (0,a,false) (0,b,false))).2.mp hab
    · intro n
      let x : Point := g⁻¹ • (0,n,false)
      refine ⟨column x,?_⟩
      have hh := column_motion g x
      rw [show g • x = (0,n,false) from smul_inv_smul g _] at hh
      exact hh.symm)

@[simp] theorem aut_row (g : Aut) (x : Point) : row (g • x) = autRow g (row x) := row_motion g x
@[simp] theorem aut_column (g : Aut) (x : Point) : column (g • x) = autColumn g (column x) := column_motion g x

def autShift (g : Aut) (r c : ℕ) : Bool := bit (g • (r,c,false))

@[simp] theorem aut_bit (g : Aut) (x : Point) :
    bit (g • x) = (autShift g (row x) (column x) ^^ bit x) := by
  have hh := bits_of_colour_eq (aut_colour g x (row x,column x,false))
    ((coordinates_of_colour_eq (aut_colour g x (row x,column x,false))).1.mpr rfl)
    ((coordinates_of_colour_eq (aut_colour g x (row x,column x,false))).2.mpr rfl)
  change (bit (g • x) ^^ autShift g (row x) (column x)) = (bit x ^^ false) at hh
  cases hgb : bit (g • x) <;> cases hs : autShift g (row x) (column x) <;> cases hxb : bit x <;> simp_all

theorem aut_representation (g : Aut) : g = motion (autRow g) (autColumn g) (autShift g) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change g • x = motion (autRow g) (autColumn g) (autShift g) • x
  exact Prod.ext (aut_row g x) (Prod.ext (aut_column g x) (aut_bit g x))

/-- The parameterisation exhausts the FULL group, and cell shifts are unique. -/
theorem motion_injective : Function.Injective
    (fun p : (Equiv.Perm ℕ) × (Equiv.Perm ℕ) × (ℕ → ℕ → Bool) => motion p.1 p.2.1 p.2.2) := by
  intro p q he
  have hh (x : Point) : motion p.1 p.2.1 p.2.2 • x = motion q.1 q.2.1 q.2.2 • x :=
    congrArg (fun g : Aut => g • x) he
  have hr : p.1 = q.1 := by
    apply Equiv.ext
    intro n
    exact congrArg row (hh (n,0,false))
  have hc : p.2.1 = q.2.1 := by
    apply Equiv.ext
    intro n
    exact congrArg column (hh (0,n,false))
  have hs : p.2.2 = q.2.2 := by
    funext r c
    simpa only [motion_bit,bit,Bool.xor_false] using congrArg bit (hh (r,c,false))
  exact Prod.ext hr (Prod.ext hc hs)

theorem motion_bijective : Function.Bijective
    (fun p : (Equiv.Perm ℕ) × (Equiv.Perm ℕ) × (ℕ → ℕ → Bool) => motion p.1 p.2.1 p.2.2) :=
  ⟨motion_injective,fun g => ⟨(autRow g,autColumn g,autShift g),(aut_representation g).symm⟩⟩

end CCO.FinitePackets.Normalization.Examples.Twin
