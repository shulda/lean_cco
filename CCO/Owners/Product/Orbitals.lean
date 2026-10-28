import CCO.FiniteKernel.BinarySource
import CCO.GroupQuotient
import Mathlib.Algebra.Group.Subgroup.Actions

/-! Full automorphisms in the actual original-action orbital language.
The language is pulled back along the displayed inclusion, not chosen
independently on quotient coordinates. No homogeneity of an imaginary or
extension of its automorphisms is presumed. -/

universe u v w
namespace CCO.Owners.Product
open CCO.FiniteKernel

variable {G A U : Type*} [Group G] [MulAction G A]

def orbitalStructure (G : Type*) [Group G] (A : Type*) [MulAction G A]
    {U : Type*} (ι : U → A) : BinaryStructure U where
  Unary := Empty
  Binary := A × A
  unary e := nomatch e
  binary p x y := GroupActions.orbital (G := G) p.1 p.2 (ι x) (ι y)

abbrev OrbitalAut (G : Type*) [Group G] (A : Type*) [MulAction G A]
    {U : Type*} (ι : U → A) := (orbitalStructure G A ι).Aut

theorem orbitalAut_pair {ι : U → A} (g : OrbitalAut G A ι) (x y : U) :
    GroupActions.orbital (G := G) (ι x) (ι y) (ι (g.val x)) (ι (g.val y)) :=
  (g.property.2 (ι x, ι y) x y).mpr (GroupActions.orbital_nonempty _ _)

theorem mem_orbitalAut_iff {ι : U → A} (g : Equiv.Perm U) :
    g ∈ (orbitalStructure G A ι).autGroup ↔
      ∀ x y, GroupActions.orbital (G := G) (ι x) (ι y) (ι (g x)) (ι (g y)) := by
  constructor
  · intro h; exact orbitalAut_pair ⟨g,h⟩
  · intro h
    constructor
    · intro e; cases e
    · intro p x y
      change GroupActions.orbital (G := G) p.1 p.2 (ι (g x)) (ι (g y)) ↔
        GroupActions.orbital (G := G) p.1 p.2 (ι x) (ι y)
      have he := GroupActions.orbital_eq_of_mem (ι x) (ι y) _ _ (h x y)
      constructor
      · intro hh
        have h' := GroupActions.orbital_eq_of_mem p.1 p.2 _ _ hh
        have hrefl := GroupActions.orbital_nonempty (G := G) (ι x) (ι y)
        rw [h'.trans he.symm]
        exact hrefl
      · intro hh
        obtain ⟨k,hk,hk'⟩ := hh
        obtain ⟨l,hl,hl'⟩ := h x y
        exact ⟨l*k,by simpa only [mul_smul,hk] using hl,
          by simpa only [mul_smul,hk'] using hl'⟩

/-- Same original-action pair orbit implies equality of coordinate images
precisely when it did so before. This proves named-kernel preservation and
reflection without invoking any imaginary homogeneity. -/
theorem equivariant_kernel_iff {B : Type*} [MulAction G B]
    (π : A → B) (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    {a b x y : A} (h : GroupActions.orbital (G := G) a b x y) :
    π x = π y ↔ π a = π b := by
  obtain ⟨g,rfl,rfl⟩ := h
  rw [equivπ,equivπ]
  exact (MulAction.injective g).eq_iff

theorem equivariant_pair {B : Type*} [MulAction G B]
    (π : A → B) (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    {a b x y : A} (h : GroupActions.orbital (G := G) a b x y) :
    GroupActions.orbital (G := G) (π a) (π b) (π x) (π y) := by
  obtain ⟨g,rfl,rfl⟩ := h
  exact ⟨g,(equivπ _ _).symm,(equivπ _ _).symm⟩

end CCO.Owners.Product
