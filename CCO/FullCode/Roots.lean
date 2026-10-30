import CCO.FullCode.Terms
import Mathlib.Basic.Finite.Sigma

/-! Literal tagged root tuples, marked objects, and the complete finite code. -/
universe u v w a b
namespace CCO.FullCode
variable {L : Language.{u}} {V : Type v} {W : Type w}

structure RootScheme (L : Language.{u}) where
  Tag : Type u
  finiteTag : Finite Tag
  arity : Tag → ℕ
  coordinateSort : ∀ tag, Fin (arity tag) → L.Sorts
  delta : ∀ tag, Formula L (coordinateSort tag)

attribute [instance] RootScheme.finiteTag

structure Root (C : Structure L V) (S : RootScheme L) where
  tag : S.Tag
  coordinate : Fin (S.arity tag) → V
  sorted : ∀ j, C.sort (coordinate j) = S.coordinateSort tag j
  valid : (S.delta tag).eval C coordinate

namespace Root
variable {C : Structure L V} {D : Structure L W} {S : RootScheme L}

def map (f : Structure.Embedding C D) (r : Root C S) : Root D S where
  tag := r.tag
  coordinate := f.point ∘ r.coordinate
  sorted j := (f.sort_eq _).trans (r.sorted j)
  valid := ((S.delta r.tag).transport f r.coordinate).mpr r.valid

theorem map_injective (f : Structure.Embedding C D) : Function.Injective (map (S := S) f) := by
  intro r s h
  cases r with | mk rt rc rs rv =>
    cases s with | mk st sc ss sv =>
      have ht := congrArg Root.tag h
      change rt = st at ht
      cases ht
      have htup : (⟨rt, f.point ∘ rc⟩ : (t : S.Tag) × (Fin (S.arity t) → W)) =
          ⟨rt, f.point ∘ sc⟩ := congrArg (fun r : Root D S =>
            (⟨r.tag, r.coordinate⟩ : (t : S.Tag) × (Fin (S.arity t) → W))) h
      have hc : f.point ∘ rc = f.point ∘ sc := eq_of_heq (Sigma.mk.inj htup).2
      have he : rc = sc := funext (fun j => f.injective (congrFun hc j))
      cases he
      rfl

def restrict {T : Set V} (hT : C.IsClosed T) (r : Root C S)
    (hr : ∀ j, r.coordinate j ∈ T) : Root (C.induce T hT) S where
  tag := r.tag
  coordinate j := ⟨r.coordinate j, hr j⟩
  sorted j := r.sorted j
  valid := ((S.delta r.tag).transport (C.inclusion T hT) _).mp r.valid

@[simp] theorem map_restrict {T : Set V} (hT : C.IsClosed T) (r : Root C S)
    (hr : ∀ j, r.coordinate j ∈ T) :
    (r.restrict hT hr).map (C.inclusion T hT) = r := by
  cases r; rfl

end Root

abbrev Coordinate (S : RootScheme L) := (tag : S.Tag) × Fin (S.arity tag)

def Root.coordinateGraph {C : Structure L V} {S : RootScheme L}
    (r : Root C S) (q : Coordinate S) : Set V :=
  {x | ∃ h : r.tag = q.1, r.coordinate (h.symm ▸ q.2) = x}

theorem Root.coordinateGraph_functional {C : Structure L V} {S : RootScheme L}
    (r : Root C S) (q : Coordinate S) : (r.coordinateGraph q).Subsingleton := by
  rintro x ⟨h, hx⟩ y ⟨h', hy⟩
  exact hx.symm.trans hy

@[simp] theorem Root.coordinateGraph_self {C : Structure L V} {S : RootScheme L}
    (r : Root C S) (j : Fin (S.arity r.tag)) :
    r.coordinateGraph ⟨r.tag, j⟩ = {r.coordinate j} := by
  ext x
  constructor
  · rintro ⟨h, hx⟩; exact hx.symm
  · intro hx; exact ⟨rfl, hx.symm⟩

theorem Root.coordinateGraph_transport {C : Structure L V} {D : Structure L W}
    {S : RootScheme L} (f : Structure.Embedding C D) (r : Root C S)
    (q : Coordinate S) (y : W) :
    y ∈ (r.map f).coordinateGraph q ↔ ∃ x, x ∈ r.coordinateGraph q ∧ f.point x = y := by
  constructor
  · rintro ⟨h, hy⟩
    exact ⟨r.coordinate (h.symm ▸ q.2), ⟨h, rfl⟩, hy⟩
  · rintro ⟨x, ⟨h, hx⟩, hy⟩
    exact ⟨h, (congrArg f.point hx).trans hy⟩

abbrev Presentation (N : NormalForms L) (S : RootScheme L) :=
  (q : Coordinate S) × (t : L.Sorts) × Fin (N.count (S.coordinateSort q.1 q.2) t)

def Root.presentation {C : Structure L V} {S : RootScheme L}
    (r : Root C S) (N : NormalForms L) (p : Presentation N S) : Set V :=
  {y | ∃ x, x ∈ r.coordinateGraph p.1 ∧
    y ∈ (N.form _ _ p.2.2).eval C x}

theorem Root.presentation_functional {C : Structure L V} {S : RootScheme L}
    (r : Root C S) (N : NormalForms L) (p : Presentation N S) :
    (r.presentation N p).Subsingleton := by
  rintro y ⟨x, hx, hy⟩ z ⟨t, ht, hz⟩
  have hxt := r.coordinateGraph_functional p.1 hx ht
  exact (N.form _ _ p.2.2).functional C x hy (hxt ▸ hz)

theorem Root.presentation_transport {C : Structure L V} {D : Structure L W}
    {S : RootScheme L} (f : Structure.Embedding C D) (r : Root C S)
    (N : NormalForms L) (p : Presentation N S) (y : W) :
    y ∈ (r.map f).presentation N p ↔ ∃ x, x ∈ r.presentation N p ∧ f.point x = y := by
  constructor
  · rintro ⟨z, hz, hy⟩
    obtain ⟨t, ht, rfl⟩ := (r.coordinateGraph_transport f p.1 z).mp hz
    obtain ⟨x, hx, hxy⟩ := ((N.form _ _ p.2.2).transport f t y).mp hy
    exact ⟨x, ⟨t, ht, hx⟩, hxy⟩
  · rintro ⟨x, ⟨z, hz, hx⟩, rfl⟩
    exact ⟨f.point z, (r.coordinateGraph_transport f p.1 _).mpr ⟨z, hz, rfl⟩,
      ((N.form _ _ p.2.2).map_iff f z x).mpr hx⟩

def EqualityCode {C : Structure L V} {S : RootScheme L} (N : NormalForms L)
    (r s : Root C S) (p q : Presentation N S) : Prop :=
  ∃ x, x ∈ r.presentation N p ∧ x ∈ s.presentation N q

def UnaryCode {C : Structure L V} {S : RootScheme L} (N : NormalForms L)
    (U : L.Unary) (r : Root C S) (p : Presentation N S) : Prop :=
  ∃ x, x ∈ r.presentation N p ∧ C.unary U x

def BinaryCode {C : Structure L V} {S : RootScheme L} (N : NormalForms L)
    (R : L.Binary) (r s : Root C S) (p q : Presentation N S) : Prop :=
  ∃ x y, x ∈ r.presentation N p ∧ y ∈ s.presentation N q ∧ C.binary R x y

theorem definedness_diagonal {C : Structure L V} {S : RootScheme L}
    (N : NormalForms L) (r : Root C S) (p : Presentation N S) :
    EqualityCode N r r p p ↔ (r.presentation N p).Nonempty := by
  constructor
  · rintro ⟨x, hx, _⟩; exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩; exact ⟨x, hx, hx⟩

structure Object (C : Structure L V) (S : RootScheme L) (A : Type a) where
  root : A → Root C S
  injective : Function.Injective root

namespace Object
variable {C : Structure L V} {D : Structure L W} {S : RootScheme L} {A : Type a} {B : Type b}

def coordinates (O : Object C S A) : Set V :=
  {x | ∃ a j, (O.root a).coordinate j = x}

def support (O : Object C S A) : Set V := C.closure O.coordinates

def supportStructure (O : Object C S A) : Structure L O.support :=
  C.induce O.support (C.isClosed_closure O.coordinates)

theorem coordinate_mem_support (O : Object C S A) (a : A) (j : Fin (S.arity (O.root a).tag)) :
    (O.root a).coordinate j ∈ O.support := C.subset_closure _ ⟨a, j, rfl⟩

def markedRoot (O : Object C S A) (a : A) : Root O.supportStructure S :=
  (O.root a).restrict (C.isClosed_closure O.coordinates) (O.coordinate_mem_support a)

def markedObject (O : Object C S A) : Object O.supportStructure S A where
  root := O.markedRoot
  injective := by
    intro a b hab
    apply O.injective
    have := congrArg (Root.map (C.inclusion O.support (C.isClosed_closure O.coordinates))) hab
    have ha : Root.map (C.inclusion O.support (C.isClosed_closure O.coordinates))
        (O.markedRoot a) = O.root a := Root.map_restrict _ _ _
    have hb : Root.map (C.inclusion O.support (C.isClosed_closure O.coordinates))
        (O.markedRoot b) = O.root b := Root.map_restrict _ _ _
    exact ha.symm.trans (this.trans hb)

def full (C : Structure L V) (S : RootScheme L) : Object C S (Root C S) where
  root r := r
  injective := Function.injective_id

structure Embedding (N : NormalForms L) (O : Object C S A) (P : Object D S B) where
  point : A → B
  injective : Function.Injective point
  tag_eq : ∀ a, (P.root (point a)).tag = (O.root a).tag
  equality_iff : ∀ a b p q, EqualityCode N (P.root (point a)) (P.root (point b)) p q ↔
    EqualityCode N (O.root a) (O.root b) p q
  unary_iff : ∀ U a p, UnaryCode N U (P.root (point a)) p ↔ UnaryCode N U (O.root a) p
  binary_iff : ∀ R a b p q, BinaryCode N R (P.root (point a)) (P.root (point b)) p q ↔
    BinaryCode N R (O.root a) (O.root b) p q

end Object
end CCO.FullCode
