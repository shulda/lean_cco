import CCO.RelationalCompletion.Atomic.Class
import CCO.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Range

/-! Finite symmetric complete atomic targets with an ARBITRARY set of colour
names. Only occurring colours need be finite. The full automorphism group
preserves the original complete optional colour, with no extra predicates. -/

universe u v
namespace CCO.FiniteFibres
open RelationalCompletion

def palette (C : Type v) : Atomic.Palette.{0,v} where
  Sorts := Unit
  Atom := C
  src := fun _ => ()
  tgt := fun _ => ()
  conv := id
  conv_conv := fun _ => rfl
  src_conv := fun _ => rfl
  tgt_conv := fun _ => rfl

abbrev Target (C : Type v) := Atomic.Model (palette C)

variable {C : Type v} (T : Target C)

theorem edge_none (x y : Fin T.size) : T.edge x y = none ↔ x = y := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨a,ha⟩ := T.complete x y hn
    change T.edge x y = some a at ha
    rw [h] at ha
    cases ha
  · rintro rfl
    exact T.diagram.edge_self x

theorem edge_symm (x y : Fin T.size) : T.edge x y = T.edge y x := by
  have h := T.diagram.edge_reverse x y
  simpa only [palette,Option.map_id,id_eq] using h.symm

def atomGraph (a : C) : SimpleGraph (Fin T.size) where
  Adj x y := T.edge x y = some a
  symm := ⟨fun _ _ h => (edge_symm T _ _).symm.trans h⟩
  loopless := ⟨fun x h => T.ne_of_edge h rfl⟩

/-- Original semantic homomorphic simple-cycle CCO for this ONE actual target.
Missing edges assert no inequality; nonadjacent vertices may collide. -/
def SemanticCCO : Prop :=
  ∀ {n : Nat} (D : Atomic.Diagram (palette C) n),
    (∀ K : Atomic.SimpleCycle D, Atomic.CycleHomInto K T) →
      Nonempty (Atomic.Hom D T)

def Aut : Subgroup (Equiv.Perm (Fin T.size)) where
  carrier := {g | ∀ x y, T.edge (g x) (g y) = T.edge x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro g h hg hh x y
    exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have h := hg (g.symm x) (g.symm y)
    simpa using h.symm

theorem aut_edge (g : Aut T) (x y : Fin T.size) :
    T.edge (g • x) (g • y) = T.edge x y := g.property x y

def Occurring := {a : C // ∃ x y : Fin T.size, T.edge x y = some a}

instance occurringFinite : Finite (Occurring T) := by
  classical
  let witness : Occurring T → Fin T.size × Fin T.size := fun a =>
    ⟨a.property.choose,a.property.choose_spec.choose⟩
  apply Finite.of_injective witness
  intro a b h
  apply Subtype.ext
  have ha : T.edge (witness a).1 (witness a).2 = some a.val :=
    a.property.choose_spec.choose_spec
  have hb : T.edge (witness b).1 (witness b).2 = some b.val :=
    b.property.choose_spec.choose_spec
  rw [h] at ha
  exact Option.some.inj (ha.symm.trans hb)

/-- The complete atom on a distinct pair is an actually occurring colour. -/
noncomputable def pairAtom (x y : Fin T.size) (h : x ≠ y) : Occurring T :=
  ⟨(T.complete x y h).choose,x,y,(T.complete x y h).choose_spec⟩

section AtomicAdapter
variable {A : Type u} (S : AtomicSource Unit (fun _ => A)) [Fintype A]

/-- Enumeration of a finite actual original source, retaining every old name. -/
noncomputable def targetOfAtomic : Target (S.Atom () ()) where
  size := Fintype.card A
  diagram := {
    tag := fun _ => ()
    edge := fun x y => S.colour (i := ()) (j := ()) ((Fintype.equivFin A).symm x) ((Fintype.equivFin A).symm y)
    edge_self := fun x => (S.colour_none_iff (i := ()) (j := ()) _ _).mpr rfl
    edge_reverse := by
      intro x y
      cases hc : S.colour (i := ()) (j := ()) ((Fintype.equivFin A).symm x) ((Fintype.equivFin A).symm y) with
      | none =>
        have he := (S.colour_none_iff (i := ()) (j := ()) _ _).mp hc
        exact (S.colour_none_iff (i := ()) (j := ()) _ _).mpr he.symm
      | some a =>
        have h := (S.colour_swap _ _ a).mp hc
        simpa only [palette,S.symmetricLoop,Option.map_id,id_eq,Option.map_some] using h
    typed := fun _ _ _ _ => ⟨rfl,rfl⟩ }
  complete := by
    intro x y hn
    cases hc : S.colour (i := ()) (j := ()) ((Fintype.equivFin A).symm x) ((Fintype.equivFin A).symm y) with
    | none =>
      have he := (S.colour_none_iff (i := ()) (j := ()) _ _).mp hc
      have hv : (Fintype.equivFin A).symm x = (Fintype.equivFin A).symm y := by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using he
      exact (hn ((Fintype.equivFin A).symm.injective hv)).elim
    | some a => exact ⟨a,hc⟩

@[simp] theorem targetOfAtomic_edge (x y : A) :
    (targetOfAtomic S).edge (Fintype.equivFin A x) (Fintype.equivFin A y) =
      S.colour (i := ()) (j := ()) x y := by
  change S.colour (i := ()) (j := ()) ((Fintype.equivFin A).symm (Fintype.equivFin A x))
    ((Fintype.equivFin A).symm (Fintype.equivFin A y)) = _
  simp only [Equiv.symm_apply_apply]

end AtomicAdapter
end CCO.FiniteFibres
