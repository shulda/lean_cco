import CCO.OrbitalCover.Example.Core
import CCO.SIR.Positive.Direct.Homogeneity
import Mathlib.Tactic.Abel

namespace CCO.OrbitalCover.Example

abbrev Owner := (ℕ × Bit) × (ℕ × Bit)
def owner (x : Point) : Owner := ((x.u, x.p), (x.v, x.q))

def pointEquiv : Point ≃ Owner × ℕ where
  toFun x := (owner x, x.n)
  invFun x := ⟨x.1.1.1, x.1.2.1, x.1.1.2, x.1.2.2, x.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by rintro ⟨⟨⟨u,p⟩,⟨v,q⟩⟩,n⟩; rfl

def coordinatePerm (ρ : Equiv.Perm ℕ) (δ : ℕ → Bit) : Equiv.Perm (ℕ × Bit) where
  toFun x := (ρ x.1, δ x.1 + x.2)
  invFun x := (ρ.symm x.1, δ (ρ.symm x.1) + x.2)
  left_inv := by rintro ⟨u,p⟩; simp [← add_assoc, CharTwo.add_self_eq_zero]
  right_inv := by rintro ⟨u,p⟩; simp [← add_assoc, CharTwo.add_self_eq_zero]

def ownerPerm (ρ κ : Equiv.Perm ℕ) (δ ε : ℕ → Bit) : Equiv.Perm Owner :=
  Equiv.prodCongr (coordinatePerm ρ δ) (coordinatePerm κ ε)

def ownerFibrePerm (π : Equiv.Perm Owner) (τ : Owner → Equiv.Perm ℕ) :
    Equiv.Perm (Owner × ℕ) where
  toFun x := (π x.1, τ x.1 x.2)
  invFun x := (π.symm x.1, (τ (π.symm x.1)).symm x.2)
  left_inv := by rintro ⟨x,n⟩; simp
  right_inv := by rintro ⟨x,n⟩; simp

def motionPerm (ρ κ : Equiv.Perm ℕ) (δ ε : ℕ → Bit)
    (τ : Owner → Equiv.Perm ℕ) : Equiv.Perm Point :=
  pointEquiv.trans (ownerFibrePerm (ownerPerm ρ κ δ ε) τ) |>.trans pointEquiv.symm

@[simp] theorem motion_u (ρ κ : Equiv.Perm ℕ) (δ ε : ℕ → Bit)
    (τ : Owner → Equiv.Perm ℕ) (x : Point) :
    (motionPerm ρ κ δ ε τ x).u = ρ x.u := rfl
@[simp] theorem motion_v (ρ κ : Equiv.Perm ℕ) (δ ε : ℕ → Bit)
    (τ : Owner → Equiv.Perm ℕ) (x : Point) :
    (motionPerm ρ κ δ ε τ x).v = κ x.v := rfl
@[simp] theorem motion_p (ρ κ : Equiv.Perm ℕ) (δ ε : ℕ → Bit)
    (τ : Owner → Equiv.Perm ℕ) (x : Point) :
    (motionPerm ρ κ δ ε τ x).p = δ x.u + x.p := rfl
@[simp] theorem motion_q (ρ κ : Equiv.Perm ℕ) (δ ε : ℕ → Bit)
    (τ : Owner → Equiv.Perm ℕ) (x : Point) :
    (motionPerm ρ κ δ ε τ x).q = ε x.v + x.q := rfl
@[simp] theorem motion_n (ρ κ : Equiv.Perm ℕ) (δ ε : ℕ → Bit)
    (τ : Owner → Equiv.Perm ℕ) (x : Point) :
    (motionPerm ρ κ δ ε τ x).n = τ (owner x) x.n := rfl

theorem coordinatePerm_colour (ρ : Equiv.Perm ℕ) (δ : ℕ → Bit)
    (b b' : ℕ) (p p' : Bit) :
    coordinateColour (ρ b) (δ b + p) (ρ b') (δ b' + p') =
      coordinateColour b p b' p' := by
  by_cases h : b = b'
  · subst b'
    simp only [coordinateColour, if_pos rfl]
    change some (δ b + p + (δ b + p')) = some (p + p')
    apply congrArg some
    calc
      δ b + p + (δ b + p') = (δ b + δ b) + (p + p') := by abel
      _ = p + p' := by rw [CharTwo.add_self_eq_zero, zero_add]
  · simp [coordinateColour, h, ρ.injective.ne h]

theorem motion_pattern (ρ κ : Equiv.Perm ℕ) (δ ε : ℕ → Bit)
    (τ : Owner → Equiv.Perm ℕ) (x y : Point) :
    pattern (motionPerm ρ κ δ ε τ x) (motionPerm ρ κ δ ε τ y) = pattern x y := by
  simp only [pattern, motion_u, motion_v, motion_p, motion_q, coordinatePerm_colour]

theorem motion_colour (ρ κ : Equiv.Perm ℕ) (δ ε : ℕ → Bit)
    (τ : Owner → Equiv.Perm ℕ) (x y : Point) :
    colour (motionPerm ρ κ δ ε τ x) (motionPerm ρ κ δ ε τ y) = colour x y := by
  simp only [colour, (motionPerm ρ κ δ ε τ).injective.eq_iff, motion_pattern]

def autGroup : Subgroup (Equiv.Perm Point) where
  carrier := {g | ∀ x y, colour (g x) (g y) = colour x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by intro g h hg hh x y; exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have h := hg (g⁻¹ x) (g⁻¹ y)
    simpa using h.symm

abbrev Aut := autGroup

@[simp] theorem aut_colour (g : Aut) (x y : Point) :
    colour (g • x) (g • y) = colour x y := g.property x y

def motion (ρ κ : Equiv.Perm ℕ) (δ ε : ℕ → Bit)
    (τ : Owner → Equiv.Perm ℕ) : Aut :=
  ⟨motionPerm ρ κ δ ε τ, motion_colour ρ κ δ ε τ⟩

theorem coordinates_of_colour_eq {x y x' y' : Point}
    (h : colour x y = colour x' y') :
    (x.u = y.u ↔ x'.u = y'.u) ∧ (x.v = y.v ↔ x'.v = y'.v) ∧
      (x.u = y.u → x.p + y.p = x'.p + y'.p) ∧
      (x.v = y.v → x.q + y.q = x'.q + y'.q) := by
  have hp := pattern_of_colour h
  have hu := congrArg Prod.fst hp
  have hv := congrArg Prod.snd hp
  change coordinateColour x.u x.p y.u y.p = coordinateColour x'.u x'.p y'.u y'.p at hu
  change coordinateColour x.v x.q y.v y.q = coordinateColour x'.v x'.q y'.v y'.q at hv
  have hku : x.u = y.u ↔ x'.u = y'.u := by
    have hi := congrArg Option.isSome hu
    simpa only [coordinateColour_isSome] using congrArg (· = true) hi |>.to_iff
  have hkv : x.v = y.v ↔ x'.v = y'.v := by
    have hi := congrArg Option.isSome hv
    simpa only [coordinateColour_isSome] using congrArg (· = true) hi |>.to_iff
  refine ⟨hku, hkv, ?_, ?_⟩
  · intro he
    simpa only [coordinateColour, if_pos he, if_pos (hku.mp he), Option.some.injEq]
      using hu
  · intro he
    simpa only [coordinateColour, if_pos he, if_pos (hkv.mp he), Option.some.injEq]
      using hv

theorem finite_extension_controlled {V : Type*} [Finite V] (f h : V → Point)
    (hc : ∀ v w, colour (f v) (f w) = colour (h v) (h w))
    (keepP keepQ : Bool)
    (hP : keepP = true → ∀ v, (f v).p = (h v).p)
    (hQ : keepQ = true → ∀ v, (f v).q = (h v).q) :
    ∃ g : Aut, (∀ v, g • f v = h v) ∧
      (keepP = true → ∀ x : Point, (g • x).p = x.p) ∧
      (keepQ = true → ∀ x : Point, (g • x).q = x.q) := by
  classical
  have hr := fun v w => coordinates_of_colour_eq (hc v w)
  obtain ⟨ρ, hρ⟩ := SIR.Positive.Direct.exists_perm_of_kernel
    (fun v => (f v).u) (fun v => (h v).u) (fun v w => (hr v w).1)
  obtain ⟨κ, hκ⟩ := SIR.Positive.Direct.exists_perm_of_kernel
    (fun v => (f v).v) (fun v => (h v).v) (fun v w => (hr v w).2.1)
  let usedU (b : ℕ) := ∃ v, (f v).u = b
  let usedV (b : ℕ) := ∃ v, (f v).v = b
  let δ (b : ℕ) : Bit := if he : usedU b then
    (h (Classical.choose he)).p + (f (Classical.choose he)).p else 0
  let ε (b : ℕ) : Bit := if he : usedV b then
    (h (Classical.choose he)).q + (f (Classical.choose he)).q else 0
  have hδ (v : V) : δ (f v).u + (f v).p = (h v).p := by
    have he : usedU (f v).u := ⟨v, rfl⟩
    let w := Classical.choose he
    have hw : (f w).u = (f v).u := Classical.choose_spec he
    have hg := (hr v w).2.2.1 hw.symm
    simp only [δ, dif_pos he]
    change (h w).p + (f w).p + (f v).p = (h v).p
    calc
      _ = (h w).p + ((f v).p + (f w).p) := by abel
      _ = (h w).p + ((h v).p + (h w).p) := by rw [hg]
      _ = (h v).p := by simp [add_left_comm, ← add_assoc, CharTwo.add_self_eq_zero]
  have hε (v : V) : ε (f v).v + (f v).q = (h v).q := by
    have he : usedV (f v).v := ⟨v, rfl⟩
    let w := Classical.choose he
    have hw : (f w).v = (f v).v := Classical.choose_spec he
    have hg := (hr v w).2.2.2 hw.symm
    simp only [ε, dif_pos he]
    change (h w).q + (f w).q + (f v).q = (h v).q
    calc
      _ = (h w).q + ((f v).q + (f w).q) := by abel
      _ = (h w).q + ((h v).q + (h w).q) := by rw [hg]
      _ = (h v).q := by simp [add_left_comm, ← add_assoc, CharTwo.add_self_eq_zero]
  have hτ : ∀ a : Owner, ∃ τ : Equiv.Perm ℕ,
      ∀ v : {v // owner (f v) = a}, τ (f v).n = (h v).n := by
    intro a
    apply SIR.Positive.Direct.exists_perm_of_kernel
    intro v w
    have ho : owner (f v) = owner (f w) := v.property.trans w.property.symm
    have hu : (f v).u = (f w).u := congrArg (fun a : Owner => a.1.1) ho
    have hv : (f v).v = (f w).v := congrArg (fun a : Owner => a.2.1) ho
    have hp : (f v).p = (f w).p := congrArg (fun a : Owner => a.1.2) ho
    have hq : (f v).q = (f w).q := congrArg (fun a : Owner => a.2.2) ho
    have hu' : (h v).u = (h w).u := (hr v w).1.mp hu
    have hv' : (h v).v = (h w).v := (hr v w).2.1.mp hv
    have hp' : (h v).p = (h w).p := by rw [← hδ v, ← hδ w, hu, hp]
    have hq' : (h v).q = (h w).q := by rw [← hε v, ← hε w, hv, hq]
    have hi : f v = f w ↔ h v = h w := by
      have he := congrArg (· = none) (hc v w) |>.to_iff
      simpa only [colour_none] using he
    have ho' : owner (h v) = owner (h w) :=
      Prod.ext (Prod.ext hu' hp') (Prod.ext hv' hq')
    constructor
    · intro hn
      have hf : f v = f w := pointEquiv.injective (Prod.ext ho hn)
      exact congrArg Point.n (hi.mp hf)
    · intro hn
      have hh : h v = h w := pointEquiv.injective (Prod.ext ho' hn)
      exact congrArg Point.n (hi.mpr hh)
  choose τ ht using hτ
  refine ⟨motion ρ κ δ ε τ, ?_, ?_, ?_⟩
  · intro v
    have hn := ht (owner (f v)) ⟨v, rfl⟩
    change motionPerm ρ κ δ ε τ (f v) = h v
    apply pointEquiv.injective
    exact Prod.ext (Prod.ext (Prod.ext (hρ v) (hδ v)) (Prod.ext (hκ v) (hε v))) hn
  · intro hk x
    change δ x.u + x.p = x.p
    have hd : δ x.u = 0 := by
      dsimp only [δ]
      split_ifs with he
      · rw [← hP hk (Classical.choose he), CharTwo.add_self_eq_zero]
      · rfl
    rw [hd, zero_add]
  · intro hk x
    change ε x.v + x.q = x.q
    have he : ε x.v = 0 := by
      dsimp only [ε]
      split_ifs with he
      · rw [← hQ hk (Classical.choose he), CharTwo.add_self_eq_zero]
      · rfl
    rw [he, zero_add]

theorem finite_extension {V : Type*} [Finite V] (f h : V → Point)
    (hc : ∀ v w, colour (f v) (f w) = colour (h v) (h w)) :
    ∃ g : Aut, ∀ v, g • f v = h v := by
  obtain ⟨g, hg, _, _⟩ := finite_extension_controlled f h hc false false
    (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h)
  exact ⟨g, hg⟩

theorem homogeneous : HomogeneousSource source Aut where
  preserves_sort := by intro g p; rcases p with ⟨i, x⟩; cases i; rfl
  preserves_colours := by
    intro g p q
    rcases p with ⟨i,x⟩; rcases q with ⟨j,y⟩
    cases i; cases j
    simp only [taggedColour, Sigma.smul_mk, source_colour, aut_colour]
  extends_finite_diagram := by
    intro V _ f h hc
    have hh : ∀ v w, colour (f v).2 (f w).2 = colour (h v).2 (h w).2 := by
      intro v w
      exact congrArg (fun z : Σ _ : Unit, Σ _ : Unit, Option Colour => z.2.2) (hc v w)
    obtain ⟨g,hg⟩ := finite_extension (fun v => (f v).2) (fun v => (h v).2) hh
    exact ⟨g, fun v => Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (hg v))⟩

end CCO.OrbitalCover.Example
