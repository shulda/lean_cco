import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Equiv.Set

/-! Pure finite diagrams used by the owner master.  The ambient objects
are fixed throughout the construction, so finite stages are actual subsets
and their maps are literal restrictions of the ambient projections. -/

universe u v z
namespace CCO.Owners.Master.Diagram

variable {P : Type u} [DecidableEq P]

structure Ambient (P : Type u) [DecidableEq P] where
  X : Finset P → Type v
  r : ∀ {V W : Finset P}, W ⊆ V → X V → X W
  r_id : ∀ (V : Finset P) (x : X V), r (Finset.Subset.refl V) x = x
  r_comp : ∀ {V W T : Finset P} (h : W ⊆ V) (k : T ⊆ W) (x : X V),
    r k (r h x) = r (k.trans h) x

namespace Ambient
variable (A : Ambient.{u,v} P)

@[simp] theorem project_self (V : Finset P) (x : A.X V) :
    A.r (Finset.Subset.refl V) x = x := A.r_id V x

@[simp] theorem project_comp {V W T : Finset P} (h : W ⊆ V) (k : T ⊆ W)
    (x : A.X V) : A.r k (A.r h x) = A.r (k.trans h) x := A.r_comp h k x

def Compatible {I : Type z} (f : I → Finset P) (b : ∀ i, A.X (f i)) : Prop :=
  ∀ i j, A.r (Finset.inter_subset_left : f i ∩ f j ⊆ f i) (b i) =
    A.r (Finset.inter_subset_right : f i ∩ f j ⊆ f j) (b j)

theorem projected_compatible {I : Type z} (f : I → Finset P)
    (V : Finset P) (h : ∀ i, f i ⊆ V) (x : A.X V) :
    A.Compatible f (fun i => A.r (h i) x) := by
  intro i j
  simp only [project_comp]

end Ambient

structure Stage (A : Ambient.{u,v} P) (Valid : Finset P → Prop) (U : Finset P) where
  B : ∀ V, Set (A.X V)
  finite : ∀ V, Valid V → V ⊆ U → (B V).Finite
  nonempty : ∀ V, Valid V → V ⊆ U → (B V).Nonempty
  mapsTo : ∀ {V W} (hV : Valid V) (hW : Valid W) (hVU : V ⊆ U)
    (hWV : W ⊆ V), ∀ x ∈ B V, A.r hWV x ∈ B W
  onto : ∀ {V W} (hV : Valid V) (hW : Valid W) (hVU : V ⊆ U)
    (hWV : W ⊆ V), ∀ y ∈ B W, ∃ x ∈ B V, A.r hWV x = y

namespace Stage
variable {A : Ambient.{u,v} P} {Valid : Finset P → Prop} {U : Finset P}
variable (B : Stage A Valid U)

abbrev Point (V : Finset P) := B.B V

/-- Canonical finite maps are constructed before CRT or group actions. -/
def r {V W} (hV : Valid V) (hW : Valid W) (hVU : V ⊆ U) (hWV : W ⊆ V) :
    B.Point V → B.Point W :=
  fun x => ⟨A.r hWV x.val, B.mapsTo hV hW hVU hWV x.val x.property⟩

@[simp] theorem r_self {V} (hV : Valid V) (hVU : V ⊆ U) (x : B.Point V) :
    B.r hV hV hVU (Finset.Subset.refl V) x = x := by
  apply Subtype.ext
  exact A.r_id V x.val

@[simp] theorem r_comp {V W T} (hV : Valid V) (hW : Valid W) (hT : Valid T)
    (hVU : V ⊆ U) (hWV : W ⊆ V) (hTW : T ⊆ W) (x : B.Point V) :
    B.r hW hT (hWV.trans hVU) hTW (B.r hV hW hVU hWV x) =
      B.r hV hT hVU (hTW.trans hWV) x := by
  apply Subtype.ext
  exact A.r_comp hWV hTW x.val

theorem r_surjective {V W} (hV : Valid V) (hW : Valid W)
    (hVU : V ⊆ U) (hWV : W ⊆ V) :
    Function.Surjective (B.r hV hW hVU hWV) := by
  intro y
  obtain ⟨x,hx,he⟩ := B.onto hV hW hVU hWV y.val y.property
  exact ⟨⟨x,hx⟩,Subtype.ext he⟩

/-- ALL finite indexed compatibility families, with empty and repeated
indices retained.  Existence and uniqueness concern the actual union object. -/
def CRT : Prop :=
  ∀ {I : Type z} [Fintype I] (f : I → Finset P)
    (valid : ∀ i, Valid (f i)) (within : ∀ i, f i ⊆ U)
    (b : ∀ i, A.X (f i)), (∀ i, b i ∈ B.B (f i)) → A.Compatible f b →
      ∃! x : A.X (Finset.univ.biUnion f),
        x ∈ B.B (Finset.univ.biUnion f) ∧
          ∀ i, A.r (Finset.subset_biUnion_of_mem f (Finset.mem_univ i)) x = b i

end Stage

end CCO.Owners.Master.Diagram
