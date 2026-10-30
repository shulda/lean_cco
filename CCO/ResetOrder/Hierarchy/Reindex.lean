import CCO.ResetOrder.Hierarchy.Synchronize

/-! Canonical reindexing by transition orbits.  No orbit, chart or compatible
order is assumed to exist as a principal theorem provider. -/
universe u v w
namespace CCO.ResetOrder.Hierarchy

namespace Schedule
variable {I K : Type u}
noncomputable def reindex (H : Schedule I) (e : K ≃ I) : Schedule K where
  rank i := H.rank (e i)
  count i := H.count (e i)
  coordinate i a := e.symm (H.coordinate (e i) a)
  coordinate_rank i a := by
    simpa only [Equiv.apply_symm_apply] using H.coordinate_rank (e i) a
end Schedule

namespace System
variable {I K : Type u} {H : Schedule I} {X : I → Type v} (S : System H X) (e : K ≃ I)

noncomputable def reindexUp (i : K) (a : Fin (H.count (e i))) (x : X (e i)) :
    X (e (e.symm (H.coordinate (e i) a))) :=
  (Equiv.cast (congrArg X (e.apply_symm_apply (H.coordinate (e i) a)).symm)) (S.up (e i) a x)

theorem reindexUp_eq_iff (i : K) (a : Fin (H.count (e i))) (x y : X (e i)) :
    S.reindexUp e i a x = S.reindexUp e i a y ↔ S.up (e i) a x = S.up (e i) a y :=
  (Equiv.cast _).injective.eq_iff

noncomputable def reindex : System (H.reindex e) (fun i => X (e i)) where
  parent i := S.parent (e i)
  parent_refl i := S.parent_refl (e i)
  parent_symm i := by intro x y h; exact S.parent_symm (e i) h
  parent_trans i := by intro x y z h h'; exact S.parent_trans (e i) h h'
  up := S.reindexUp e
  key_parent i x y := by
    change (∀ a, S.reindexUp e i a x = S.reindexUp e i a y) ↔ S.parent (e i) x y
    rw [← S.key_parent]
    exact forall_congr' (fun a => S.reindexUp_eq_iff e i a x y)
end System

namespace TransitionPaths
variable {I : Type u} {X : I → Type v} (T : TransitionPaths.{u,v,w} I X)

def comap {K : Type u} (f : K → I) : TransitionPaths K (fun i => X (f i)) where
  Path i j := T.Path (f i) (f j)
  identity i := T.identity (f i)
  compose := T.compose
  inverse := T.inverse
  map := T.map
  map_identity i := T.map_identity (f i)
  map_compose := T.map_compose
  map_inverse := T.map_inverse
  holonomy := T.holonomy

def orbitSetoid : Setoid I where
  r := T.SameOrbit
  iseqv := ⟨T.sameOrbit_refl, T.sameOrbit_symm, T.sameOrbit_trans⟩

def Orbit := Quotient T.orbitSetoid
def orbit (i : I) : T.Orbit := Quotient.mk _ i
def InOrbit (r : T.Orbit) := {i : I // T.orbit i = r}

def orbitEquiv : Sigma T.InOrbit ≃ I where
  toFun i := i.2.val
  invFun i := ⟨T.orbit i,i,rfl⟩
  left_inv := by
    rintro ⟨r,i,hi⟩
    cases hi
    rfl
  right_inv _ := rfl

noncomputable def canonicalRepresentative (r : T.Orbit) : T.InOrbit r :=
  ⟨Quotient.out r, Quotient.out_eq r⟩

theorem path_of_same_orbit {i j : I} (h : T.orbit i = T.orbit j) : Nonempty (T.Path i j) :=
  Quotient.exact h

noncomputable def representativePath (rep : ∀ r, T.InOrbit r) (r : T.Orbit) (j : T.InOrbit r) :
    T.Path (rep r).val j.val :=
  Classical.choice (T.path_of_same_orbit ((rep r).property.trans j.property.symm))

end TransitionPaths
end CCO.ResetOrder.Hierarchy
