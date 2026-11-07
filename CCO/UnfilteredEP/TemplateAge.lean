import CCO.UnfilteredEP.FiniteTemplate
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.EquivFin

/-! The independent finite-age and actual singleton Ramsey interfaces of
A01. Objects have finite carriers and retain their complete old colour
and original sort tables. The provider is an expansion on these same
objects, with actual expanded embeddings. -/

universe u v w z p q r
namespace CCO.UnfilteredEP

structure FiniteAge (OldSort : Type u) (Atom : Type v) where
  Obj : Type w
  Point : Obj → Type z
  finitePoint : ∀ A, Finite (Point A)
  sort : ∀ A, Point A → OldSort
  colour : ∀ A, Point A → Point A → Option Atom
  diagonal : ∀ A x y, colour A x y = none ↔ x = y

namespace FiniteAge
variable {OldSort : Type u} {Atom : Type v} {Label : Type p}
variable (K : FiniteAge.{u,v,w,z} OldSort Atom) (T : FiniteTemplate OldSort Atom Label)

structure Embedding (A B : K.Obj) where
  toFun : K.Point A → K.Point B
  injective : Function.Injective toFun
  sorted : ∀ x, K.sort B (toFun x) = K.sort A x
  colours : ∀ x y, K.colour B (toFun x) (toFun y) = K.colour A x y

namespace Embedding
variable {K} {A B C : K.Obj}

def id (A : K.Obj) : K.Embedding A A :=
  ⟨_root_.id,fun _ _ h => h,fun _ => rfl,fun _ _ => rfl⟩

def comp (g : K.Embedding B C) (f : K.Embedding A B) : K.Embedding A C :=
  ⟨g.toFun ∘ f.toFun,g.injective.comp f.injective,
    fun x => (g.sorted (f.toFun x)).trans (f.sorted x),
    fun x y => (g.colours _ _).trans (f.colours x y)⟩

@[ext] theorem ext {f g : K.Embedding A B} (h : f.toFun = g.toFun) : f = g := by
  cases f
  cases g
  cases h
  rfl

end Embedding

/-- Pair-locality includes all old off-diagonal atoms and original sorts.
Repeated labels on distinct points are permitted precisely by the table. -/
structure Marking (A : K.Obj) where
  label : K.Point A → Label
  sorted : ∀ x, T.sort (label x) = K.sort A x
  pairs : ∀ x y a, K.colour A x y = some a → T.rel a (label x) (label y)

namespace Marking
variable {K T} {A B : K.Obj}

/-- The exact old embedding restricts every allowed pair-local marking. -/
def restrict (e : K.Embedding A B) (b : K.Marking T B) : K.Marking T A where
  label := b.label ∘ e.toFun
  sorted x := (b.sorted _).trans (e.sorted x)
  pairs x y r h := b.pairs _ _ r ((e.colours x y).trans h)

def postcompose (a : K.Marking T A) (f : Label → Label) (hf : T.Endomorphism f) :
    K.Marking T A where
  label := f ∘ a.label
  sorted x := (hf.1 (a.label x)).trans (a.sorted x)
  pairs x y r h := hf.2 r _ _ (a.pairs x y r h)

end Marking

structure MarkedEmbedding {A B : K.Obj} (a : K.Marking T A) (b : K.Marking T B) where
  old : K.Embedding A B
  labels : ∀ x, b.label (old.toFun x) = a.label x

namespace MarkedEmbedding
variable {K T} {A B C : K.Obj}
variable {a : K.Marking T A} {b : K.Marking T B} {c : K.Marking T C}

def id (a : K.Marking T A) : K.MarkedEmbedding T a a :=
  ⟨Embedding.id A,fun _ => rfl⟩

def comp (g : K.MarkedEmbedding T b c) (f : K.MarkedEmbedding T a b) :
    K.MarkedEmbedding T a c :=
  ⟨g.old.comp f.old,fun x => (g.labels _).trans (f.labels x)⟩

@[ext] theorem ext {f g : K.MarkedEmbedding T a b} (h : f.old.toFun = g.old.toFun) :
    f = g := by
  have he : f.old = g.old := Embedding.ext h
  cases f
  cases g
  cases he
  rfl

end MarkedEmbedding

/-- The old host is selected before every competing legal unary marking. -/
def UnaryEP : Prop :=
  ∀ (A : K.Obj) (a : K.Marking T A),
    ∃ B : K.Obj, ∀ b : K.Marking T B, Nonempty (K.MarkedEmbedding T a b)

/-- Realized-label and realized-pair clauses in A01. A repeated-label
pair is explicitly witnessed at two distinct actual vertices. -/
def AllPairsRealized : Prop :=
  ∀ a s t, T.rel a s t →
    ∃ (A : K.Obj) (m : K.Marking T A) (x y : K.Point A),
      x ≠ y ∧ K.colour A x y = some a ∧ m.label x = s ∧ m.label y = t

/-- Reasonableness extends a prescribed legal marking along the SAME
old induced embedding. This property is not needed for the independent
core criterion, but is retained for the core-retract fallback. -/
def Reasonable : Prop :=
  ∀ {A B : K.Obj} (e : K.Embedding A B) (a : K.Marking T A),
    ∃ b : K.Marking T B, ∀ x, b.label (e.toFun x) = a.label x

/-- Reduct-surjectivity of the unary expansion. -/
def ReductSurjective : Prop := ∀ A : K.Obj, Nonempty (K.Marking T A)

/-- Actual expanded finite objects and their extra induced-map conditions.
The extra conditions describe the Ramsey expansion; composition retains
all of them. They are not allowed to supply expansion property. -/
structure RamseyProvider where
  Obj : Type q
  old : Obj → K.Obj
  marking : ∀ A, K.Marking T (old A)
  allowed : ∀ A B, K.MarkedEmbedding T (marking A) (marking B) → Prop
  id_allowed : ∀ A, allowed A A (MarkedEmbedding.id (marking A))
  comp_allowed : ∀ {A B C} (g : K.MarkedEmbedding T (marking B) (marking C))
    (f : K.MarkedEmbedding T (marking A) (marking B)),
    allowed B C g → allowed A B f → allowed A C (g.comp f)

namespace RamseyProvider
variable {K T} (P : K.RamseyProvider.{u,v,w,z,p,q} T)

def Embedding (A B : P.Obj) :=
  {f : K.MarkedEmbedding T (P.marking A) (P.marking B) // P.allowed A B f}

namespace Embedding
variable {P} {A B C D : P.Obj}

def id (A : P.Obj) : P.Embedding A A :=
  ⟨MarkedEmbedding.id (P.marking A),P.id_allowed A⟩

def comp (g : P.Embedding B C) (f : P.Embedding A B) : P.Embedding A C :=
  ⟨g.val.comp f.val,P.comp_allowed g.val f.val g.property f.property⟩

@[ext] theorem ext {f g : P.Embedding A B}
    (h : f.val.old.toFun = g.val.old.toFun) : f = g := by
  apply Subtype.ext
  exact MarkedEmbedding.ext h

theorem comp_assoc (h : P.Embedding C D) (g : P.Embedding B C)
    (f : P.Embedding A B) : (h.comp g).comp f = h.comp (g.comp f) := by
  apply ext
  rfl

end Embedding

/-- Every legal marked old object has an actual provider expansion.
The isomorphism is displayed on the whole old carrier, avoiding equality
transports between two presentations of the same finite object. -/
def ReductSurjective : Prop :=
  ∀ (A : K.Obj) (a : K.Marking T A),
    ∃ (D : P.Obj) (e : K.MarkedEmbedding T a (P.marking D)), Function.Surjective e.old.toFun

def JEP : Prop :=
  ∀ A B : P.Obj, ∃ D : P.Obj, Nonempty (P.Embedding A D) ∧ Nonempty (P.Embedding B D)

def Ramsey : Prop :=
  ∀ (A B : P.Obj) (n : Nat), 0 < n →
    ∃ C : P.Obj, ∀ colour : P.Embedding A C → Fin n,
      ∃ g : P.Embedding B C,
        ∀ f h : P.Embedding A B, colour (g.comp f) = colour (g.comp h)

/-- Exactly one actual one-point shape per realized label, and every
vertex induces that shape. Its embeddings are genuine provider embeddings. -/
structure Singletons where
  object : Label → P.Obj
  point : ∀ t, K.Point (P.old (object t))
  only_point : ∀ t x, x = point t
  labelled : ∀ t, (P.marking (object t)).label (point t) = t
  at_vertex : ∀ A x, ∃ e : P.Embedding (object ((P.marking A).label x)) A,
    e.val.old.toFun (point ((P.marking A).label x)) = x

/-- Iterated ordinary JEP for one finite list; overlaps are permitted. -/
theorem joint_list (jep : P.JEP) (base : P.Obj) :
    ∀ objects : List P.Obj,
      ∃ D : P.Obj, ∀ A ∈ objects, Nonempty (P.Embedding A D) := by
  intro objects
  induction objects with
  | nil => exact ⟨base,by simp⟩
  | cons A objects ih =>
    obtain ⟨D,hD⟩ := ih
    obtain ⟨E,⟨eA⟩,⟨eD⟩⟩ := jep A D
    refine ⟨E,?_⟩
    intro B hB
    rcases List.mem_cons.mp hB with h | h
    · subst B
      exact ⟨eA⟩
    · obtain ⟨eB⟩ := hD B h
      exact ⟨eD.comp eB⟩

/-- Finite families of inverse targets, all labels and all realized
pair witnesses can therefore be placed in one genuine provider object. -/
theorem joint_finite {I : Type r} [Finite I] (jep : P.JEP)
    (base : P.Obj) (objects : I → P.Obj) :
    ∃ D : P.Obj, ∀ i, Nonempty (P.Embedding (objects i) D) := by
  classical
  let _ := Fintype.ofFinite I
  obtain ⟨D,hD⟩ := P.joint_list jep base ((Finset.univ.toList).map objects)
  exact ⟨D,fun i => hD (objects i) (List.mem_map.mpr ⟨i,by simp,rfl⟩)⟩

end RamseyProvider
end FiniteAge
end CCO.UnfilteredEP
