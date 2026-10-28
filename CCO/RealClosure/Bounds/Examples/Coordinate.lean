import CCO.SIR.Positive.Direct.Homogeneity
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Group.Pi.Basic

/-! The actual infinite named-coordinate source, with exactly the nonempty
sets of changed coordinates as diversity atoms. -/
universe u
namespace CCO.RealClosure.Bounds.Examples.Coordinate
variable (I : Type u) [Fintype I] [DecidableEq I]

abbrev Point := I → ℕ
abbrev Colour := {s : Finset I // s.Nonempty}

noncomputable instance : Fintype (Colour I) := Fintype.ofFinite _

def support (x y : Point I) : Finset I := Finset.univ.filter (fun i => x i ≠ y i)

@[simp] theorem mem_support (x y : Point I) (i : I) : i ∈ support I x y ↔ x i ≠ y i := by
  simp [support]

theorem support_symm (x y : Point I) : support I x y = support I y x := by
  ext i
  simp only [mem_support,ne_comm]

@[simp] theorem support_empty (x y : Point I) : support I x y = ∅ ↔ x = y := by
  constructor
  · intro h
    funext i
    by_contra hi
    have hm := (mem_support I x y i).mpr hi
    rw [h] at hm
    exact Finset.notMem_empty i hm
  · rintro rfl
    ext i
    simp

noncomputable def colour (x y : Point I) : Option (Colour I) :=
  if h : (support I x y).Nonempty then some ⟨support I x y,h⟩ else none

@[simp] theorem colour_none (x y : Point I) : colour I x y = none ↔ x = y := by
  classical
  simp only [colour]
  split_ifs with h
  · simp only [reduceCtorEq, false_iff]
    intro he
    exact h.ne_empty ((support_empty I x y).mpr he)
  · simp only [true_iff]
    exact (support_empty I x y).mp (Finset.not_nonempty_iff_eq_empty.mp h)

@[simp] theorem colour_some (x y : Point I) (a : Colour I) :
    colour I x y = some a ↔ support I x y = a.val := by
  classical
  unfold colour
  split_ifs with h
  · simp only [Option.some.injEq,Subtype.ext_iff]
  · simp only [reduceCtorEq,false_iff]
    intro he
    exact h (he ▸ a.property)

theorem colour_symm (x y : Point I) : colour I x y = colour I y x := by
  classical
  unfold colour
  simp only [support_symm I x y]

theorem colour_eq_iff (x y x' y' : Point I) :
    colour I x y = colour I x' y' ↔ support I x y = support I x' y' := by
  constructor
  · intro hc
    cases hxy : colour I x y with
    | none =>
      have he := (colour_none I x y).mp hxy
      have he' := (colour_none I x' y').mp (hc.symm.trans hxy)
      rw [(support_empty I x y).mpr he,(support_empty I x' y').mpr he']
    | some a =>
      exact ((colour_some I x y a).mp hxy).trans
        ((colour_some I x' y' a).mp (hc.symm.trans hxy)).symm
  · intro hs
    classical
    unfold colour
    simp only [hs]

theorem coordinates_of_colour_eq {x y x' y' : Point I}
    (hc : colour I x y = colour I x' y') (i : I) :
    x i = y i ↔ x' i = y' i := by
  have hs := (colour_eq_iff I x y x' y').mp hc
  have hm := Finset.ext_iff.mp hs i
  simpa only [mem_support,not_iff_not] using hm

noncomputable def source : AtomicSource Unit (fun _ => Point I) where
  Atom := fun _ _ => Colour I
  finiteSort := inferInstance
  finiteAtom := fun _ _ => inferInstance
  nonemptySort := fun _ => ⟨fun _ => 0⟩
  conv := id
  conv_invol := fun _ => rfl
  symmetricLoop := fun _ => rfl
  colour := colour I
  colour_none_iff := by
    intro i j x y
    cases i; cases j
    simpa using colour_none I x y
  colour_swap := by
    intro i j x y a
    change colour I x y = some a ↔ colour I y x = some a
    rw [colour_symm]
  realized := by
    intro i j a
    classical
    refine ⟨fun _ => 0,fun i => if i ∈ a.val then 1 else 0,?_⟩
    apply (colour_some I _ _ a).mpr
    ext i
    simp only [mem_support]
    by_cases hi : i ∈ a.val <;> simp [hi]

@[simp] theorem source_colour {i j : Unit} (x y : Point I) :
    (source I).colour (i := i) (j := j) x y = colour I x y := rfl

/-- Full automorphisms, not a chosen subgroup of coordinate motions. -/
def autGroup : Subgroup (Equiv.Perm (Point I)) where
  carrier := {g | ∀ x y, colour I (g x) (g y) = colour I x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by intro g h hg hh x y; exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have hh := hg (g⁻¹ x) (g⁻¹ y)
    simpa using hh.symm

abbrev Aut := autGroup I

@[simp] theorem aut_colour (g : Aut I) (x y : Point I) :
    colour I (g • x) (g • y) = colour I x y := g.property x y

def coordinatePerm (g : I → Equiv.Perm ℕ) : Equiv.Perm (Point I) where
  toFun x i := g i (x i)
  invFun x i := (g i).symm (x i)
  left_inv x := by funext i; exact (g i).left_inv (x i)
  right_inv x := by funext i; exact (g i).right_inv (x i)

theorem coordinatePerm_colour (g : I → Equiv.Perm ℕ) (x y : Point I) :
    colour I (coordinatePerm I g x) (coordinatePerm I g y) = colour I x y := by
  apply (colour_eq_iff I _ _ _ _).mpr
  ext i
  exact (mem_support I _ _ i).trans
    (not_congr (g i).injective.eq_iff) |>.trans (mem_support I x y i).symm

def coordinateAut (g : I → Equiv.Perm ℕ) : Aut I :=
  ⟨coordinatePerm I g,coordinatePerm_colour I g⟩

theorem finite_extension {V : Type u} [Finite V]
    (f h : V → Point I) (hc : ∀ x y, colour I (f x) (f y) = colour I (h x) (h y)) :
    ∃ g : Aut I, ∀ v, g • f v = h v := by
  classical
  have he : ∀ i : I, ∃ p : Equiv.Perm ℕ, ∀ v, p (f v i) = h v i := by
    intro i
    exact SIR.Positive.Direct.exists_perm_of_kernel (fun v => f v i) (fun v => h v i)
      (fun v w => coordinates_of_colour_eq I (hc v w) i)
  choose p hp using he
  exact ⟨coordinateAut I p,fun v => funext (fun i => hp i v)⟩

theorem homogeneous : HomogeneousSource (source I) (Aut I) where
  preserves_sort := by intro g p; cases p with | mk i p => cases i; rfl
  preserves_colours := by
    intro g p q
    cases p with | mk i p => cases q with | mk j q =>
      cases i; cases j
      simp only [taggedColour,Sigma.smul_mk,source_colour,aut_colour]
  extends_finite_diagram := by
    intro V _ f h hc
    have hh : ∀ v w, colour I (f v).2 (f w).2 = colour I (h v).2 (h w).2 := by
      intro v w
      exact congrArg (fun z : Σ _ : Unit, Σ _ : Unit, Option (Colour I) => z.2.2) (hc v w)
    obtain ⟨g,hg⟩ := finite_extension I (fun v => (f v).2) (fun v => (h v).2) hh
    exact ⟨g,fun v => Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (hg v))⟩
end CCO.RealClosure.Bounds.Examples.Coordinate
