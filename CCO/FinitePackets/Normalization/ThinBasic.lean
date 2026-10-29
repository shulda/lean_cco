import CCO.FinitePackets.Geometry.Basic

/-! Equality-inclusive thin original colours.  This elementary interface
uses the actual old palette and represented real points, with no CCO,
exactness, SAP, or countability premise. -/
universe v w t
namespace CCO.FinitePackets.Normalization
open CCO.RealHull.Geometry CCO.ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def ThinColour (c : FullColour S) : Prop :=
  ∀ x : M, ∃! y : M, col S x y = c

def FullColourBelow (F : ColourEq S ()) (c : FullColour S) : Prop :=
  ∀ x y : M, col S x y = c → F x y

def ThinBottom (F : ColourEq S ()) : Prop :=
  ∀ c : FullColour S, FullColourBelow S F c → ThinColour S c

theorem thin_none : ThinColour S none := by
  intro x
  exact ⟨x,(col_none S x x).mpr rfl,fun y hy => ((col_none S x y).mp hy).symm⟩

theorem fullColourBelow_none (F : ColourEq S ()) : FullColourBelow S F none := by
  intro x y h
  exact ((col_none S x y).mp h) ▸ F.val.refl x

theorem fullColourBelow_at (F : ColourEq S ()) (x y : M) (hxy : F x y) :
    FullColourBelow S F (col S x y) := by
  intro a b hab
  exact (F.property x y a b hab.symm).mp hxy

theorem fullColourBelow_some_iff (F : ColourEq S ()) (a : Atom S) :
    FullColourBelow S F (some a) ↔ Geometry.AtomBelow S F a := Iff.rfl

noncomputable def thinNeighbour (c : FullColour S) (hc : ThinColour S c) (x : M) : M :=
  Classical.choose (hc x)

@[simp] theorem thinNeighbour_colour (c : FullColour S) (hc : ThinColour S c) (x : M) :
    col S x (thinNeighbour S c hc x) = c := (Classical.choose_spec (hc x)).1

theorem thinNeighbour_eq (c : FullColour S) (hc : ThinColour S c) {x y : M}
    (hxy : col S x y = c) : thinNeighbour S c hc x = y :=
  ((Classical.choose_spec (hc x)).2 y hxy).symm

theorem thinNeighbour_involutive (c : FullColour S) (hc : ThinColour S c) :
    Function.Involutive (thinNeighbour S c hc) := by
  intro x
  apply thinNeighbour_eq S c hc
  exact (col_symm S _ _).trans (thinNeighbour_colour S c hc x)

noncomputable def thinPerm (c : FullColour S) (hc : ThinColour S c) : Equiv.Perm M where
  toFun := thinNeighbour S c hc
  invFun := thinNeighbour S c hc
  left_inv := thinNeighbour_involutive S c hc
  right_inv := thinNeighbour_involutive S c hc

@[simp] theorem thinPerm_apply (c : FullColour S) (hc : ThinColour S c) (x : M) :
    thinPerm S c hc x = thinNeighbour S c hc x := rfl

@[simp] theorem thinPerm_colour (c : FullColour S) (hc : ThinColour S c) (x : M) :
    col S x (thinPerm S c hc x) = c := thinNeighbour_colour S c hc x

theorem thinPerm_involutive (c : FullColour S) (hc : ThinColour S c) :
    Function.Involutive (thinPerm S c hc) := thinNeighbour_involutive S c hc

@[simp] theorem thinPerm_none : thinPerm S none (thin_none S) = 1 := by
  ext x
  exact thinNeighbour_eq S none (thin_none S) ((col_none S x x).mpr rfl)

variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)

theorem thinPerm_equivariant (c : FullColour S) (hc : ThinColour S c)
    (g : G) (x : M) : thinPerm S c hc (g • x) = g • thinPerm S c hc x := by
  change thinNeighbour S c hc (g • x) = g • thinPerm S c hc x
  apply thinNeighbour_eq S c hc
  exact (col_invariant S H g x (thinPerm S c hc x)).trans (thinPerm_colour S c hc x)

end CCO.FinitePackets.Normalization
