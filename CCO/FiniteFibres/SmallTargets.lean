import CCO.FiniteFibres.Bipartite
import Mathlib.SetTheory.Cardinal.Finite

/-! C28/C42/C47: actual empty, singleton and one-colour triangle targets.
The palette may have arbitrarily many unused names. The local-allowedness
gate is retained: it rules out a nonempty input for the empty target and
any specified diversity edge for the singleton. -/
namespace CCO.FiniteFibres.SmallTargets
open RelationalCompletion

variable (C : Type*)

private def noEdges (n : ℕ) : Atomic.Diagram (palette C) n where
  tag := fun _ => ()
  edge := fun _ _ => none
  edge_self := fun _ => rfl
  edge_reverse := fun _ _ => rfl
  typed := by intro x y a h; cases h

def emptyTarget : Target C where
  size := 0
  diagram := noEdges C 0
  complete := fun x => Fin.elim0 x

def singletonTarget : Target C where
  size := 1
  diagram := noEdges C 1
  complete := fun x y hn => False.elim (hn (Subsingleton.elim x y))

/-- This is honest even for an empty target: allowedness supplies an actual
point for every displayed input vertex. -/
theorem empty_semanticCCO : SemanticCCO (emptyTarget C) := by
  intro n D hLocal _hCycles
  classical
  let f : Fin n → Fin 0 := fun x => Classical.choice (hLocal.1 x)
  refine ⟨{ vertex := f,tag_eq := fun x => Fin.elim0 (f x),edge_eq := ?_ }⟩
  intro x y a ha
  exact Fin.elim0 (f x)

/-- Every locally allowed singleton request has no specified edge; its
arbitrarily many nonadjacent vertices may all have the same image. -/
theorem singleton_semanticCCO : SemanticCCO (singletonTarget C) := by
  intro n D hLocal _hCycles
  let f : Fin n → Fin 1 := fun _ => 0
  refine ⟨{ vertex := f,tag_eq := ?_,edge_eq := ?_ }⟩
  · intro x
    change (() : Unit) = D.tag x
    exact Subsingleton.elim _ _
  intro x y a ha
  obtain ⟨b,c,hbc⟩ := hLocal.2 x y a ha
  change (none : Option C) = some a at hbc
  cases hbc

theorem empty_occurring : IsEmpty (Occurring (emptyTarget C)) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨x,y,_⟩ := a.property
  exact Fin.elim0 x

theorem singleton_occurring : IsEmpty (Occurring (singletonTarget C)) := by
  refine ⟨fun a => ?_⟩
  obtain ⟨x,y,hxy⟩ := a.property
  change (none : Option C) = some a.val at hxy
  cases hxy

variable {C}

theorem aut_eq_one_of_subsingleton (T : Target C) [Subsingleton (Fin T.size)]
    (g : Aut T) : g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  exact Subsingleton.elim _ _

theorem aut_card_of_subsingleton (T : Target C) [Subsingleton (Fin T.size)] :
    Nat.card (Aut T) = 1 := by
  letI : Unique (Aut T) := ⟨⟨1⟩,fun g => aut_eq_one_of_subsingleton T g⟩
  exact Nat.card_unique

theorem all_setoids_equal {A : Type*} [Subsingleton A] (E F : Setoid A) : E = F := by
  apply Setoid.ext
  intro x y
  have he : x = y := Subsingleton.elim x y
  subst y
  exact iff_of_true (E.refl x) (F.refl x)

/-- There is no proper equivalence cover at all, hence in particular no
proper full-invariant-equivalence cover on an empty or singleton target. -/
theorem no_equivalence_cover {A : Type*} [Subsingleton A] (E F : Setoid A) : ¬ E ⋖ F := by
  rw [all_setoids_equal E F]
  intro h
  exact h.lt.ne rfl

theorem no_invariant_equivalence_cover {A : Type*} [Subsingleton A]
    (P : Setoid A → Prop) (E F : {R : Setoid A // P R}) : ¬ E ⋖ F := by
  have hEF : E = F := Subtype.ext (all_setoids_equal E.val F.val)
  rw [hEF]
  intro h
  exact h.lt.ne rfl

theorem empty_aut_card : Nat.card (Aut (emptyTarget C)) = 1 := by
  letI : Subsingleton (Fin (emptyTarget C).size) :=
    (show Subsingleton (Fin 0) from inferInstance)
  exact aut_card_of_subsingleton _

theorem singleton_aut_card : Nat.card (Aut (singletonTarget C)) = 1 := by
  letI : Subsingleton (Fin (singletonTarget C).size) :=
    (show Subsingleton (Fin 1) from inferInstance)
  exact aut_card_of_subsingleton _

/-- Completeness with zero diversity names forces at most one point. -/
theorem subsingleton_of_empty_palette [IsEmpty C] (T : Target C) :
    Subsingleton (Fin T.size) := by
  refine ⟨fun x y => ?_⟩
  by_contra hn
  obtain ⟨a,_⟩ := T.complete x y hn
  exact isEmptyElim (show C from a)

def triangle : Target Unit where
  size := 3
  diagram := {
    tag := fun _ => ()
    edge := fun x y => if x = y then none else some ()
    edge_self := by intro x; simp
    edge_reverse := by intro x y; simp only [palette,Option.map_id,id_eq,eq_comm]
    typed := fun _ _ _ _ => ⟨rfl,rfl⟩ }
  complete := fun x y hn => ⟨(),by simp [hn]⟩

/-- C47: the actual complete one-colour triangle fails HOM CCO. A hypothetical
CCO would bipartition its complete atom graph, injecting three points into two. -/
theorem triangle_not_semanticCCO : ¬ SemanticCCO triangle := by
  intro hcco
  let colour := (atom_bipartite triangle hcco ()).some
  have hinj : Function.Injective colour := by
    intro x y hxy
    by_contra hn
    have hadj : (atomGraph triangle ()).Adj x y := by
      change (if x = y then (none : Option Unit) else some ()) = some ()
      simp [hn]
    exact (colour.map_rel' hadj) hxy
  have hcard : Fintype.card (Fin 3) ≤ Fintype.card (Fin 2) :=
    Fintype.card_le_of_injective (show Fin 3 → Fin 2 from colour) hinj
  have hbad : 3 ≤ 2 := by
    simpa only [Fintype.card_fin] using hcard
  omega

end CCO.FiniteFibres.SmallTargets
