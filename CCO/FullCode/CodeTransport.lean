import CCO.FullCode.Presentations

universe u v w z a b c
namespace CCO.FullCode
variable {L : Language.{u}} {V : Type v} {W : Type w} {Z : Type z}

theorem equalityCode_map {C : Structure L V} {D : Structure L W} {S : RootScheme L}
    (N : NormalForms L) (f : Structure.Embedding C D) (r s : Root C S)
    (p q : Presentation N S) :
    EqualityCode N (r.map f) (s.map f) p q ↔ EqualityCode N r s p q := by
  constructor
  · rintro ⟨y, hy, hz⟩
    obtain ⟨x, hx, rfl⟩ := (r.presentation_transport f N p y).mp hy
    obtain ⟨z, hzp, hzx⟩ := (s.presentation_transport f N q _).mp hz
    exact ⟨x, hx, f.injective hzx ▸ hzp⟩
  · rintro ⟨x, hx, hy⟩
    exact ⟨f.point x, (r.presentation_transport f N p _).mpr ⟨x, hx, rfl⟩,
      (s.presentation_transport f N q _).mpr ⟨x, hy, rfl⟩⟩

theorem unaryCode_map {C : Structure L V} {D : Structure L W} {S : RootScheme L}
    (N : NormalForms L) (f : Structure.Embedding C D) (U : L.Unary) (r : Root C S)
    (p : Presentation N S) : UnaryCode N U (r.map f) p ↔ UnaryCode N U r p := by
  constructor
  · rintro ⟨y, hy, hU⟩
    obtain ⟨x, hx, rfl⟩ := (r.presentation_transport f N p y).mp hy
    exact ⟨x, hx, (f.unary_iff U x).mp hU⟩
  · rintro ⟨x, hx, hU⟩
    exact ⟨f.point x, (r.presentation_transport f N p _).mpr ⟨x, hx, rfl⟩,
      (f.unary_iff U x).mpr hU⟩

theorem binaryCode_map {C : Structure L V} {D : Structure L W} {S : RootScheme L}
    (N : NormalForms L) (f : Structure.Embedding C D) (R : L.Binary) (r s : Root C S)
    (p q : Presentation N S) :
    BinaryCode N R (r.map f) (s.map f) p q ↔ BinaryCode N R r s p q := by
  constructor
  · rintro ⟨x, y, hx, hy, hR⟩
    obtain ⟨z, hz, rfl⟩ := (r.presentation_transport f N p x).mp hx
    obtain ⟨t, ht, rfl⟩ := (s.presentation_transport f N q y).mp hy
    exact ⟨z, t, hz, ht, (f.binary_iff R z t).mp hR⟩
  · rintro ⟨x, y, hx, hy, hR⟩
    exact ⟨f.point x, f.point y,
      (r.presentation_transport f N p _).mpr ⟨x, hx, rfl⟩,
      (s.presentation_transport f N q _).mpr ⟨y, hy, rfl⟩,
      (f.binary_iff R x y).mpr hR⟩

namespace Object
variable {C : Structure L V} {D : Structure L W} {E : Structure L Z} {S : RootScheme L}
  {A : Type a} {B : Type b} {F : Type c}

@[ext] theorem Embedding.ext {N : NormalForms L} {O : Object C S A} {P : Object D S B}
    {f g : Embedding N O P} (h : ∀ x, f.point x = g.point x) : f = g := by
  cases f; cases g
  have hp := funext h
  cases hp
  rfl

def Embedding.id (N : NormalForms L) (O : Object C S A) : Embedding N O O where
  point x := x
  injective := Function.injective_id
  tag_eq _ := rfl
  equality_iff _ _ _ _ := Iff.rfl
  unary_iff _ _ _ := Iff.rfl
  binary_iff _ _ _ _ _ := Iff.rfl

def Embedding.comp {N : NormalForms L} {O : Object C S A} {P : Object D S B}
    {Q : Object E S F} (g : Embedding N P Q) (f : Embedding N O P) : Embedding N O Q where
  point := g.point ∘ f.point
  injective := g.injective.comp f.injective
  tag_eq a := (g.tag_eq _).trans (f.tag_eq a)
  equality_iff _a _b p q := (g.equality_iff _ _ p q).trans (f.equality_iff _ _ p q)
  unary_iff U _a p := (g.unary_iff U _ p).trans (f.unary_iff U _ p)
  binary_iff R _a _b p q := (g.binary_iff R _ _ p q).trans (f.binary_iff R _ _ p q)

def rootEmbedding (N : NormalForms L) (O : Object C S A)
    (f : Structure.Embedding C D) : Embedding N O (full D S) where
  point a := (O.root a).map f
  injective := (Root.map_injective f).comp O.injective
  tag_eq _ := rfl
  equality_iff a b p q := equalityCode_map N f _ _ p q
  unary_iff U a p := unaryCode_map N f U _ p
  binary_iff R a b p q := binaryCode_map N f R _ _ p q

def marking (N : NormalForms L) (O : Object C S A) : Embedding N O O.markedObject where
  point x := x
  injective := Function.injective_id
  tag_eq _ := rfl
  equality_iff a b p q := by
    have h := equalityCode_map N (C.inclusion O.support (C.isClosed_closure O.coordinates))
      (O.markedRoot a) (O.markedRoot b) p q
    have ha : (O.markedRoot a).map (C.inclusion O.support (C.isClosed_closure O.coordinates)) =
        O.root a := Root.map_restrict _ _ _
    have hb : (O.markedRoot b).map (C.inclusion O.support (C.isClosed_closure O.coordinates)) =
        O.root b := Root.map_restrict _ _ _
    rw [ha, hb] at h
    exact h.symm
  unary_iff U a p := by
    have h := unaryCode_map N (C.inclusion O.support (C.isClosed_closure O.coordinates)) U
      (O.markedRoot a) p
    have ha : (O.markedRoot a).map (C.inclusion O.support (C.isClosed_closure O.coordinates)) =
        O.root a := Root.map_restrict _ _ _
    rw [ha] at h
    exact h.symm
  binary_iff R a b p q := by
    have h := binaryCode_map N (C.inclusion O.support (C.isClosed_closure O.coordinates)) R
      (O.markedRoot a) (O.markedRoot b) p q
    have ha : (O.markedRoot a).map (C.inclusion O.support (C.isClosed_closure O.coordinates)) =
        O.root a := Root.map_restrict _ _ _
    have hb : (O.markedRoot b).map (C.inclusion O.support (C.isClosed_closure O.coordinates)) =
        O.root b := Root.map_restrict _ _ _
    rw [ha, hb] at h
    exact h.symm

def fromHidden (N : NormalForms L) (O : Object C S A)
    (f : Structure.Embedding O.supportStructure D) : Embedding N O (full D S) :=
  (rootEmbedding N O.markedObject f).comp (marking N O)

end Object
end CCO.FullCode
