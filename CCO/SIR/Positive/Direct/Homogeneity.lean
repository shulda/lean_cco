import CCO.SIR.Positive.Direct.Source
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Algebra.Group.Action.End

namespace CCO.SIR.Positive.Direct

/-- Finite tuples with the same equality kernel are related by a permutation.
Repeated entries are allowed. -/
theorem exists_perm_of_kernel {V A : Type*} [Finite V]
    (f h : V → A) (hk : ∀ v w, f v = f w ↔ h v = h w) :
    ∃ π : Equiv.Perm A, ∀ v, π (f v) = h v := by
  classical
  let c : Set.range f → V := fun a => Classical.choose a.2
  have hc (a : Set.range f) : f (c a) = a := Classical.choose_spec a.2
  let k : Set.range f → Set.range h := fun a => ⟨h (c a), ⟨c a, rfl⟩⟩
  have hi : Function.Injective k := by
    intro a b hab
    apply Subtype.ext
    have hh : h (c a) = h (c b) := congrArg Subtype.val hab
    exact (hc a).symm.trans (((hk _ _).mpr hh).trans (hc b))
  have hs : Function.Surjective k := by
    rintro ⟨b, v, rfl⟩
    refine ⟨⟨f v, ⟨v, rfl⟩⟩, Subtype.ext ?_⟩
    exact (hk _ _).mp (hc _)
  letI : Finite (Set.range f) := (Set.finite_range f).to_subtype
  obtain ⟨π,hπ⟩ := Equiv.Perm.exists_extending_pair
    (fun a : Set.range f => a.val) (fun a : Set.range f => h (c a))
    Subtype.val_injective (by
      intro a b hab
      exact hi (Subtype.ext hab))
  refine ⟨π, fun v => ?_⟩
  exact (hπ ⟨f v,⟨v,rfl⟩⟩).trans ((hk _ _).mp (hc _))

/-- The whole original-language colour automorphism group. -/
def autGroup : Subgroup (Equiv.Perm Point) where
  carrier := {g | ∀ x y, colour (g x) (g y) = colour x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro a b ha hb x y
    exact (ha (b x) (b y)).trans (hb x y)
  inv_mem' := by
    intro a ha x y
    have h := ha (a⁻¹ x) (a⁻¹ y)
    simpa using h.symm

abbrev Aut := autGroup

@[simp] theorem aut_colour (g : Aut) (x y : Point) :
    colour (g • x) (g • y) = colour x y := g.2 x y

/-- Independent parent, sheet and fibre permutations give actual old
language automorphisms. The sheet choices depend on the OLD parent. -/
def wreathPerm (π : Equiv.Perm ℕ) (σ : ℕ → Equiv.Perm Bool)
    (τ : ℕ → Bool → Equiv.Perm ℕ) : Equiv.Perm Point where
  toFun x := (π (parent x), σ (parent x) (sheet x), τ (parent x) (sheet x) (index x))
  invFun x := (π.symm (parent x), σ (π.symm (parent x)) |>.symm <| sheet x,
    τ (π.symm (parent x)) ((σ (π.symm (parent x))).symm (sheet x)) |>.symm <| index x)
  left_inv := by rintro ⟨p,b,n⟩; simp [parent,sheet,index]
  right_inv := by rintro ⟨p,b,n⟩; simp [parent,sheet,index]

@[simp] theorem wreath_parent (π : Equiv.Perm ℕ) (σ : ℕ → Equiv.Perm Bool)
    (τ : ℕ → Bool → Equiv.Perm ℕ) (x : Point) :
    parent (wreathPerm π σ τ x) = π (parent x) := rfl
@[simp] theorem wreath_sheet (π : Equiv.Perm ℕ) (σ : ℕ → Equiv.Perm Bool)
    (τ : ℕ → Bool → Equiv.Perm ℕ) (x : Point) :
    sheet (wreathPerm π σ τ x) = σ (parent x) (sheet x) := rfl

/-- Coordinate recovery, rather than an extra sheet predicate in the
language, verifies colour preservation. -/
theorem wreath_colour (π : Equiv.Perm ℕ) (σ : ℕ → Equiv.Perm Bool)
    (τ : ℕ → Bool → Equiv.Perm ℕ) (x y : Point) :
    colour (wreathPerm π σ τ x) (wreathPerm π σ τ y) = colour x y := by
  unfold colour
  simp only [(wreathPerm π σ τ).injective.eq_iff]
  simp only [F, wreath_parent, π.injective.eq_iff, wreath_sheet]
  by_cases hp : parent x = parent y
  · simp only [hp, ↓reduceIte]
    simp only [hp, (σ (parent y)).injective.eq_iff]
  · simp only [hp, ↓reduceIte]

def wreath (π : Equiv.Perm ℕ) (σ : ℕ → Equiv.Perm Bool)
    (τ : ℕ → Bool → Equiv.Perm ℕ) : Aut :=
  ⟨wreathPerm π σ τ, wreath_colour π σ τ⟩

/-- Every finite old-colour partial isomorphism extends. No sheet names
or parent names are added to the real language. -/
theorem finite_extension {V : Type*} [Finite V]
    (f h : V → Point) (hcol : ∀ v w, colour (f v) (f w) = colour (h v) (h w)) :
    ∃ g : Aut, ∀ v, g • f v = h v := by
  classical
  have hc := fun v w => coordinates_of_colour_eq (hcol v w)
  obtain ⟨π, hπ⟩ := exists_perm_of_kernel (fun v => parent (f v))
    (fun v => parent (h v)) (fun v w => (hc v w).2.1)
  have hσ : ∀ p, ∃ σ : Equiv.Perm Bool,
      ∀ v : {v // parent (f v) = p}, σ (sheet (f v)) = sheet (h v) := by
    intro p
    apply exists_perm_of_kernel
    intro v w
    have hp : F (f v) (f w) := v.2.trans w.2.symm
    have hq : F (h v) (h w) := (hc v w).2.1.mp hp
    simpa only [E, hp, hq, true_and] using (hc v w).2.2
  choose σ hs using hσ
  have hτ : ∀ p b, ∃ τ : Equiv.Perm ℕ,
      ∀ v : {v // parent (f v) = p ∧ sheet (f v) = b},
        τ (index (f v)) = index (h v) := by
    intro p b
    apply exists_perm_of_kernel
    intro v w
    have hp : parent (f v) = parent (f w) := v.2.1.trans w.2.1.symm
    have hb : sheet (f v) = sheet (f w) := v.2.2.trans w.2.2.symm
    have he : E (f v) (f w) := ⟨hp,hb⟩
    have hhe := (hc v w).2.2.mp he
    have hhp : (h v).1 = (h w).1 := hhe.1
    have hhb : (h v).2.1 = (h w).2.1 := hhe.2
    have hi := (hc v w).1
    simpa only [Prod.ext_iff, parent, sheet, index, hp, hb, hhe.1, hhe.2,
      hhp, hhb, true_and] using hi
  choose τ ht using hτ
  refine ⟨wreath π σ τ, fun v => ?_⟩
  change (π (parent (f v)), σ (parent (f v)) (sheet (f v)),
    τ (parent (f v)) (sheet (f v)) (index (f v))) = h v
  apply Prod.ext
  · exact hπ v
  apply Prod.ext
  · exact hs _ ⟨v,rfl⟩
  · exact ht _ _ ⟨v,⟨rfl,rfl⟩⟩

theorem homogeneous : HomogeneousSource source Aut where
  preserves_sort := by intro g p; cases p with | mk i p => cases i; rfl
  preserves_colours := by
    intro g p q
    cases p with | mk i p => cases q with | mk j q =>
      cases i; cases j
      simp only [taggedColour, Sigma.smul_mk, source_colour, aut_colour]
  extends_finite_diagram := by
    intro V _ f h hc
    have hh : ∀ v w, colour (f v).2 (f w).2 = colour (h v).2 (h w).2 := by
      intro v w
      have hv := hc v w
      exact congrArg (fun z : Σ _ : Unit, Σ _ : Unit, Option Colour => z.2.2) hv
    obtain ⟨g,hg⟩ := finite_extension (fun v => (f v).2) (fun v => (h v).2) hh
    refine ⟨g, fun v => ?_⟩
    exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (hg v))

end CCO.SIR.Positive.Direct
