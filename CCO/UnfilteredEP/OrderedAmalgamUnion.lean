import CCO.UnfilteredEP.ProperFreshAmalgam

/-! Restrict the actual unordered strong amalgam to the unary-closed
UNION of its two whole factor images. No extra ambient point then needs
an independently prescribed task order. All original function domains,
relations, commutation and off-base freshness are retained. -/

universe u v w z
namespace CCO.UnfilteredEP
namespace OrderedAmalgamUnion
open UnarySupport HiddenSAPReadings.SourceSupport
noncomputable section
variable {L : Signature.{u}} {V : Type v} {W : Type w} {Y : Type z}
variable {A : Structure L V} {T : Structure L W} {C : Structure L Y}

def unionSet (f : A.Embedding C) (g : T.Embedding C) : Set Y :=
  Set.range f.point ∪ Set.range g.point

theorem union_closed (f : A.Embedding C) (g : T.Embedding C) : C.IsClosed (unionSet f g) := by
  intro F x hx y hy
  rcases hx with hx | hx
  · exact Or.inl (embedding_range_closed f F x hx hy)
  · exact Or.inr (embedding_range_closed g F x hx hy)

def left (f : A.Embedding C) (g : T.Embedding C) :
    A.Embedding (C.induce (unionSet f g) (union_closed f g)) where
  point x := ⟨f.point x,Or.inl ⟨x,rfl⟩⟩
  sort_eq := f.sort_eq
  map_func := f.map_func
  map_rel := f.map_rel
  injective _ _ he := f.injective (congrArg Subtype.val he)
  reflect_func F x y hy := by
    obtain ⟨a,ha,he⟩ := f.reflect_func F x y.val hy
    exact ⟨a,ha,Subtype.ext he⟩
  reflect_rel := f.reflect_rel

def right (f : A.Embedding C) (g : T.Embedding C) :
    T.Embedding (C.induce (unionSet f g) (union_closed f g)) where
  point x := ⟨g.point x,Or.inr ⟨x,rfl⟩⟩
  sort_eq := g.sort_eq
  map_func := g.map_func
  map_rel := g.map_rel
  injective _ _ he := g.injective (congrArg Subtype.val he)
  reflect_func F x y hy := by
    obtain ⟨a,ha,he⟩ := g.reflect_func F x y.val hy
    exact ⟨a,ha,Subtype.ext he⟩
  reflect_rel := g.reflect_rel

theorem cover (f : A.Embedding C) (g : T.Embedding C) (y : unionSet f g) :
    (∃ x, (left f g).point x = y) ∨ ∃ x, (right f g).point x = y := by
  rcases y.property with ⟨x,hx⟩ | ⟨x,hx⟩
  · exact Or.inl ⟨x,Subtype.ext hx⟩
  · exact Or.inr ⟨x,Subtype.ext hx⟩

theorem fresh (f : A.Embedding C) (g : T.Embedding C) (z : W)
    (hz : g.point z ∉ Set.range f.point) :
    (right f g).point z ∉ Set.range (left f g).point := by
  rintro ⟨x,hx⟩
  exact hz ⟨x,congrArg Subtype.val hx⟩

/-- At most one new point per target sort is an actual consequence of
whole-base overlap and the one-generator normal form, not an ordered-SAP
premise. The final source application supplies precisely these facts. -/
theorem new_sort_singleton (f : A.Embedding C) (g : T.Embedding C)
    (base : Set W)
    (baseCovered : ∀ x ∈ base, g.point x ∈ Set.range f.point)
    (singleOff : ∀ x y, x ∉ base → y ∉ base → T.sort x = T.sort y → x = y)
    (x y : unionSet f g)
    (freshX : x ∉ Set.range (left f g).point)
    (freshY : y ∉ Set.range (left f g).point)
    (same : (C.induce (unionSet f g) (union_closed f g)).sort x =
      (C.induce (unionSet f g) (union_closed f g)).sort y) : x = y := by
  rcases cover f g x with hx | ⟨a,ha⟩
  · exact (freshX hx).elim
  rcases cover f g y with hy | ⟨b,hb⟩
  · exact (freshY hy).elim
  have haOff : a ∉ base := by
    intro h
    obtain ⟨z,hz⟩ := baseCovered a h
    apply freshX
    refine ⟨z,?_⟩
    exact (Subtype.ext hz).trans ha
  have hbOff : b ∉ base := by
    intro h
    obtain ⟨z,hz⟩ := baseCovered b h
    apply freshY
    refine ⟨z,?_⟩
    exact (Subtype.ext hz).trans hb
  have sort : T.sort a = T.sort b := by
    have hA := (right f g).sort_eq a
    have hB := (right f g).sort_eq b
    rw [ha] at hA
    rw [hb] at hB
    exact hA.symm.trans (same.trans hB)
  exact ha.symm.trans ((congrArg (right f g).point (singleOff a b haOff hbOff sort)).trans hb)

end
end OrderedAmalgamUnion

open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.UnarySupport

noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- Actual proper hidden strong amalgamation can be chosen to have
EXACTLY the unary-closed factor union, retaining whole-base commutation
and a midpoint fresh over all of the first factor. -/
theorem proper_hidden_fresh_union
    (P D T : Set (Values B))
    (hP : (Target B ht).IsClosed P) (hD : (Target B ht).IsClosed D)
    (hT : (Target B ht).IsClosed T) (hPD : P ⊆ D) (hPT : P ⊆ T)
    (finiteD : D.Finite) (finiteT : T.Finite)
    (properD : ∀ x ∈ D, ProperSort B ht ((Target B ht).sort x))
    (properT : ∀ x ∈ T, ProperSort B ht ((Target B ht).sort x))
    (z : T) (hz : z.val ∉ P) :
    ∃ (V : Type (max u v)) (_ : Finite V)
      (C : Structure (Sig B ht) V), ProperAge B ht C ∧
      ∃ (f : ((Target B ht).induce D hD).Embedding C)
        (g : ((Target B ht).induce T hT).Embedding C),
        (∀ p : P, f.point ⟨p.val,hPD p.property⟩ = g.point ⟨p.val,hPT p.property⟩) ∧
        g.point z ∉ Set.range f.point ∧
        (∀ x, (∃ d, f.point d = x) ∨ ∃ t, g.point t = x) := by
  obtain ⟨V,hV,C,hC,f,g,hcomm,hfresh⟩ :=
    proper_hidden_fresh_amalgam B ht P D T hP hD hT hPD hPT finiteD finiteT properD properT z hz
  let U := OrderedAmalgamUnion.unionSet f g
  let closed := OrderedAmalgamUnion.union_closed f g
  let C' := C.induce U closed
  let left := OrderedAmalgamUnion.left f g
  let right := OrderedAmalgamUnion.right f g
  have mem : ProperAge B ht C' :=
    (proper_hidden_age_sap B ht).hereditary hC (C.inclusion U closed)
  refine ⟨U,mem.1.1,C',mem,left,right,?_,OrderedAmalgamUnion.fresh f g z hfresh,?_⟩
  · intro p
    exact Subtype.ext (hcomm p)
  · exact OrderedAmalgamUnion.cover f g

end
end CCO.UnfilteredEP
