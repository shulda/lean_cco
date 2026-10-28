import CCO.RealClosure.Bounds.Examples.CycleConsistency
import CCO.SIR.Positive.Direct.Homogeneity
import CCO.StrongExact.AgeAP
import Mathlib.Data.Fintype.Prod

/-! The literal infinite Cartesian phase source: two independent natural
coordinates and one global Boolean phase. Its automorphism group, finite
homogeneity and homomorphic CCO are actual source theorems. -/
namespace CCO.RealClosure.Bounds.Examples.Phase

abbrev Point := ℕ × ℕ × Bool
abbrev Pattern := Bool × Bool × Bool
abbrev row (x : Point) : ℕ := x.1
abbrev column (x : Point) : ℕ := x.2.1
abbrev phase (x : Point) : Bool := x.2.2

def diagonal : Pattern := (true,true,false)
abbrev Colour := {c : Pattern // c ≠ diagonal}

theorem colour_card : Fintype.card Colour = 7 := by decide

def pattern (x y : Point) : Pattern :=
  (decide (row x = row y),decide (column x = column y),phase x ^^ phase y)

@[simp] theorem pattern_diag_iff (x y : Point) : pattern x y = diagonal ↔ x = y := by
  rcases x with ⟨r,c,b⟩
  rcases y with ⟨r',c',b'⟩
  cases b <;> cases b' <;> simp [pattern,diagonal,Prod.ext_iff,row,column,phase]

theorem pattern_symm (x y : Point) : pattern x y = pattern y x := by
  simp only [pattern,eq_comm,Bool.xor_comm]

def colour (x y : Point) : Option Colour :=
  if h : x = y then none else some ⟨pattern x y,fun he => h ((pattern_diag_iff x y).mp he)⟩

@[simp] theorem colour_none (x y : Point) : colour x y = none ↔ x = y := by simp [colour]

@[simp] theorem colour_some (x y : Point) (a : Colour) :
    colour x y = some a ↔ pattern x y = a.val := by
  by_cases h : x = y
  · subst y
    have hn : pattern x x ≠ a.val := by
      intro he
      exact a.property (he.symm.trans ((pattern_diag_iff x x).mpr rfl))
    simp [colour,hn]
  · simp only [colour,dif_neg h,Option.some.injEq,Subtype.ext_iff]

theorem pattern_of_colour (x y x' y' : Point)
    (h : colour x y = colour x' y') : pattern x y = pattern x' y' := by
  cases hc : colour x y with
  | none =>
    have he : x = y := (colour_none x y).mp hc
    have he' : x' = y' := (colour_none x' y').mp (h.symm.trans hc)
    subst y; subst y'
    exact ((pattern_diag_iff x x).mpr rfl).trans ((pattern_diag_iff x' x').mpr rfl).symm
  | some a =>
    exact ((colour_some x y a).mp hc).trans ((colour_some x' y' a).mp (h.symm.trans hc)).symm

theorem coordinates_of_colour_eq {x y x' y' : Point}
    (h : colour x y = colour x' y') :
    (row x = row y ↔ row x' = row y') ∧
    (column x = column y ↔ column x' = column y') ∧
    (phase x ^^ phase y) = (phase x' ^^ phase y') := by
  have hp := pattern_of_colour x y x' y' h
  have hr : decide (row x = row y) = decide (row x' = row y') := congrArg Prod.fst hp
  have hc : decide (column x = column y) = decide (column x' = column y') :=
    congrArg (fun p : Pattern => p.2.1) hp
  exact ⟨decide_eq_decide.mp hr,decide_eq_decide.mp hc,congrArg (fun p : Pattern => p.2.2) hp⟩

theorem colour_symm (x y : Point) : colour x y = colour y x := by
  cases hc : colour x y with
  | none =>
    have he := (colour_none x y).mp hc
    subst y
    exact ((colour_none x x).mpr rfl).symm
  | some a =>
    exact ((colour_some y x a).mpr ((pattern_symm y x).trans ((colour_some x y a).mp hc))).symm

/-- Exactly seven actual diversity atoms; the omitted eighth pattern is REAL equality. -/
def source : AtomicSource Unit (fun _ => Point) where
  Atom := fun _ _ => Colour
  finiteSort := inferInstance
  finiteAtom := fun _ _ => inferInstance
  nonemptySort := fun _ => ⟨0,0,false⟩
  conv := id
  conv_invol := fun _ => rfl
  symmetricLoop := fun _ => rfl
  colour := colour
  colour_none_iff := by
    intro i j x y
    cases i; cases j
    simpa using colour_none x y
  colour_swap := by
    intro i j x y a
    exact congrArg (· = some a) (colour_symm x y) |>.to_iff
  realized := by
    intro i j a
    let x : Point := (0,0,false)
    let y : Point := (if a.val.1 then 0 else 1,if a.val.2.1 then 0 else 1,a.val.2.2)
    refine ⟨x,y,(colour_some x y a).mpr ?_⟩
    rcases a with ⟨⟨b,c,d⟩,ha⟩
    cases b <;> cases c <;> cases d <;> rfl

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

def motionPerm (ρ κ : Equiv.Perm ℕ) (δ : Bool) : Equiv.Perm Point where
  toFun x := (ρ (row x),κ (column x),δ ^^ phase x)
  invFun x := (ρ.symm (row x),κ.symm (column x),δ ^^ phase x)
  left_inv := by rintro ⟨r,c,b⟩; cases δ <;> cases b <;> simp [row,column,phase]
  right_inv := by rintro ⟨r,c,b⟩; cases δ <;> cases b <;> simp [row,column,phase]

@[simp] theorem motionPerm_row (ρ κ : Equiv.Perm ℕ) (δ : Bool) (x : Point) :
    row (motionPerm ρ κ δ x) = ρ (row x) := rfl
@[simp] theorem motionPerm_column (ρ κ : Equiv.Perm ℕ) (δ : Bool) (x : Point) :
    column (motionPerm ρ κ δ x) = κ (column x) := rfl
@[simp] theorem motionPerm_phase (ρ κ : Equiv.Perm ℕ) (δ : Bool) (x : Point) :
    phase (motionPerm ρ κ δ x) = (δ ^^ phase x) := rfl

theorem motionPerm_pattern (ρ κ : Equiv.Perm ℕ) (δ : Bool) (x y : Point) :
    pattern (motionPerm ρ κ δ x) (motionPerm ρ κ δ y) = pattern x y := by
  simp only [pattern,motionPerm_row,motionPerm_column,motionPerm_phase,ρ.injective.eq_iff,κ.injective.eq_iff]
  cases δ <;> cases hx : phase x <;> cases hy : phase y <;> rfl

theorem motionPerm_colour (ρ κ : Equiv.Perm ℕ) (δ : Bool) (x y : Point) :
    colour (motionPerm ρ κ δ x) (motionPerm ρ κ δ y) = colour x y := by
  cases h : colour x y with
  | none =>
    have he := (colour_none x y).mp h
    subst y
    simp
  | some a =>
    apply (colour_some _ _ a).mpr
    exact (motionPerm_pattern ρ κ δ x y).trans ((colour_some x y a).mp h)

def motion (ρ κ : Equiv.Perm ℕ) (δ : Bool) : Aut :=
  ⟨motionPerm ρ κ δ,motionPerm_colour ρ κ δ⟩

@[simp] theorem motion_row (ρ κ : Equiv.Perm ℕ) (δ : Bool) (x : Point) :
    row (motion ρ κ δ • x) = ρ (row x) := rfl
@[simp] theorem motion_column (ρ κ : Equiv.Perm ℕ) (δ : Bool) (x : Point) :
    column (motion ρ κ δ • x) = κ (column x) := rfl
@[simp] theorem motion_phase (ρ κ : Equiv.Perm ℕ) (δ : Bool) (x : Point) :
    phase (motion ρ κ δ • x) = (δ ^^ phase x) := rfl

theorem finite_extension {V : Type*} [Finite V] (f h : V → Point)
    (hc : ∀ v w, colour (f v) (f w) = colour (h v) (h w)) :
    ∃ g : Aut, ∀ v, g • f v = h v := by
  classical
  obtain ⟨ρ,hρ⟩ := SIR.Positive.Direct.exists_perm_of_kernel (fun v => row (f v))
    (fun v => row (h v)) (fun v w => (coordinates_of_colour_eq (hc v w)).1)
  obtain ⟨κ,hκ⟩ := SIR.Positive.Direct.exists_perm_of_kernel (fun v => column (f v))
    (fun v => column (h v)) (fun v w => (coordinates_of_colour_eq (hc v w)).2.1)
  by_cases hv : Nonempty V
  · let v0 := Classical.choice hv
    let δ := phase (h v0) ^^ phase (f v0)
    refine ⟨motion ρ κ δ,fun v => ?_⟩
    apply Prod.ext (hρ v)
    apply Prod.ext (hκ v)
    have hg := (coordinates_of_colour_eq (hc v v0)).2.2
    change (δ ^^ phase (f v)) = phase (h v)
    dsimp only [δ]
    cases hf : phase (f v) <;> cases hh : phase (h v) <;>
      cases hf0 : phase (f v0) <;> cases hh0 : phase (h v0) <;> simp_all
  · exact ⟨1,fun v => False.elim (hv ⟨v⟩)⟩

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

/-- Every actual full automorphism induces one permutation of each entire
infinite coordinate set, rather than just preserving a finite snapshot. -/
private theorem row_motion (g : Aut) (x : Point) :
    row (g • x) = row (g • (row x,0,false)) :=
  (coordinates_of_colour_eq (aut_colour g x (row x,0,false))).1.mpr rfl

private theorem column_motion (g : Aut) (x : Point) :
    column (g • x) = column (g • (0,column x,false)) :=
  (coordinates_of_colour_eq (aut_colour g x (0,column x,false))).2.1.mpr rfl

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
      exact (coordinates_of_colour_eq (aut_colour g (0,a,false) (0,b,false))).2.1.mp hab
    · intro n
      let x : Point := g⁻¹ • (0,n,false)
      refine ⟨column x,?_⟩
      have hh := column_motion g x
      rw [show g • x = (0,n,false) from smul_inv_smul g _] at hh
      exact hh.symm)

@[simp] theorem aut_row (g : Aut) (x : Point) : row (g • x) = autRow g (row x) :=
  row_motion g x
@[simp] theorem aut_column (g : Aut) (x : Point) :
    column (g • x) = autColumn g (column x) := column_motion g x

def autShift (g : Aut) : Bool := phase (g • (0,0,false))

@[simp] theorem aut_phase (g : Aut) (x : Point) :
    phase (g • x) = (autShift g ^^ phase x) := by
  have hh := (coordinates_of_colour_eq (aut_colour g x (0,0,false))).2.2
  change (phase (g • x) ^^ autShift g) = (phase x ^^ false) at hh
  cases hg : phase (g • x) <;> cases hs : autShift g <;> cases hx : phase x <;> simp_all

/-- This identifies the FULL group: there are no additional point
permutations beyond independent coordinate permutations and one common bit. -/
theorem aut_representation (g : Aut) : g = motion (autRow g) (autColumn g) (autShift g) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change g • x = motion (autRow g) (autColumn g) (autShift g) • x
  apply Prod.ext
  · change row (g • x) = autRow g (row x)
    exact aut_row g x
  · apply Prod.ext
    · change column (g • x) = autColumn g (column x)
      exact aut_column g x
    · change phase (g • x) = (autShift g ^^ phase x)
      exact aut_phase g x

theorem motion_injective : Function.Injective
    (fun p : (Equiv.Perm ℕ) × (Equiv.Perm ℕ) × Bool => motion p.1 p.2.1 p.2.2) := by
  intro p q h
  have hp : ∀ x : Point, motion p.1 p.2.1 p.2.2 • x = motion q.1 q.2.1 q.2.2 • x :=
    fun x => congrArg (fun g : Aut => g • x) h
  have hr : p.1 = q.1 := by
    apply Equiv.ext
    intro n
    exact congrArg row (hp (n,0,false))
  have hc : p.2.1 = q.2.1 := by
    apply Equiv.ext
    intro n
    exact congrArg column (hp (0,n,false))
  have hs : p.2.2 = q.2.2 := by
    have hh := congrArg phase (hp (0,0,false))
    simpa only [motion_phase,phase,Bool.xor_false] using hh
  exact Prod.ext hr (Prod.ext hc hs)

theorem motion_bijective : Function.Bijective
    (fun p : (Equiv.Perm ℕ) × (Equiv.Perm ℕ) × Bool => motion p.1 p.2.1 p.2.2) :=
  ⟨motion_injective,fun g => ⟨(autRow g,autColumn g,autShift g),(aut_representation g).symm⟩⟩

end CCO.RealClosure.Bounds.Examples.Phase
