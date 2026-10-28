import CCO.PairHomogeneity
import CCO.RawExact.DiagramReindex
import CCO.GroupActions
import CCO.ParityHasse.Original.Equivalences
import CCO.RawWords

/-! A named original sort is viewed as a one-sort atomic source while the
acting group stays the WHOLE original ambient G. Only finite same-sort tuple
extension is transported; no full reduct automorphism extension is asserted.
-/
universe u v w t z
namespace CCO.RealClosure.Bounds
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)

def sortSource : AtomicSource.{0,v,w} Unit (fun _ => X i) where
  Atom _ _ := S.Atom i i
  finiteSort := inferInstance
  finiteAtom _ _ := S.finiteAtom i i
  nonemptySort _ := S.nonemptySort i
  conv := S.conv
  conv_invol := S.conv_invol
  symmetricLoop := S.symmetricLoop
  colour := S.colour
  colour_none_iff := by
    intro j k x y
    cases j; cases k
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using S.colour_none_iff x y
  colour_swap := S.colour_swap
  realized := S.realized

@[simp] theorem sortSource_colour (x y : X i) :
    (sortSource S i).colour (i := ()) (j := ()) x y = S.colour x y := rfl

variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]

/-- Actual finite same-sort isomorphisms extend by the SAME ambient group.
ULift accommodates the original sort-index universe without a stronger H. -/
theorem sortSource_homogeneous (H : HomogeneousSource S G) :
    HomogeneousSource (sortSource S i) G where
  preserves_sort _ _ := rfl
  preserves_colours := by
    intro g p q
    cases p with | mk j x =>
      cases j
      cases q with | mk k y =>
        cases k
        exact congrArg (fun c : Option (S.Atom i i) =>
          (⟨(),(),c⟩ : Σ j : Unit, Σ k : Unit, Option (S.Atom i i)))
          (S.colourInvariant_of_homogeneous H g x y)
  extends_finite_diagram := by
    intro V _ f h hp
    let f' : ULift.{u} V → Sigma X := fun p => ⟨i,(f p.down).2⟩
    let h' : ULift.{u} V → Sigma X := fun p => ⟨i,(h p.down).2⟩
    have hp' : ∀ p q, taggedColour S (f' p) (f' q) = taggedColour S (h' p) (h' q) := by
      intro p q
      have hc := congrArg (fun c : Σ j : Unit, Σ k : Unit, Option (S.Atom i i) => c.2.2)
        (hp p.down q.down)
      exact congrArg (fun c : Option (S.Atom i i) =>
        (⟨i,i,c⟩ : Σ j : ι, Σ k : ι, Option (S.Atom j k))) hc
    obtain ⟨g,hg⟩ := H.extends_finite_diagram f' h' hp'
    refine ⟨g,fun p => ?_⟩
    have ht : (⟨i,g • (f p).2⟩ : Sigma X) = ⟨i,(h p).2⟩ := hg (ULift.up p)
    have hv : g • (f p).2 = (h p).2 := eq_of_heq (Sigma.mk.inj ht).2
    exact Sigma.ext (Unit.ext _ _) (heq_of_eq hv)

variable {V : Type z}

def sortDiagram (D : PartialDiagram (sortSource S i) V) : PartialDiagram S V where
  finite_type := D.finite_type
  vertexSort _ := i
  edge := D.edge
  edge_reverse := D.edge_reverse

def sortCycle (D : PartialDiagram (sortSource S i) V) (C : SimpleCycle (sortDiagram S i D)) :
    SimpleCycle D where
  length := C.length
  length_ge_three := C.length_ge_three
  length_pos := C.length_pos
  vertices := C.vertices
  next_ne := C.next_ne
  specified := C.specified

/-- Actual original semantic homomorphic CCO restricts to pure-i diagrams.
All specified simple cycles and literal old atoms are retained. -/
theorem sortSource_semanticCCO (cco : SemanticCCO.{u,v,z,w} S) :
    SemanticCCO.{0,v,z,w} (sortSource S i) := by
  intro V D hcycles
  obtain ⟨f⟩ := cco V (sortDiagram S i D) (fun C => hcycles (sortCycle S i D C))
  exact ⟨{point := f.point,preserves_edge := f.preserves_edge}⟩
end CCO.RealClosure.Bounds

namespace CCO.RealClosure.Bounds
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X) (i : ι)

/-- The full original G-pair-colour equivalence poset is literally preserved. -/
def originalColourEqIso : ColourEq S i ≃o ColourEq (sortSource S i) () where
  toFun E := ⟨E.val,E.property⟩
  invFun E := ⟨E.val,E.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Every restricted letter is the SAME literal original i-to-i atom. -/
def liftSortWord {j k : Unit} : RawWord (sortSource S i) j k → RawWord S i i
  | .nil _ => .nil i
  | .identity tail => .identity (liftSortWord tail)
  | .atom a tail => .atom a (liftSortWord tail)

theorem liftSortWord_relation {j k : Unit} (word : RawWord (sortSource S i) j k) :
    RawWord.relation S (liftSortWord S i word) = RawWord.relation (sortSource S i) word := by
  induction word with
  | nil _ => rfl
  | identity tail ih => exact ih
  | atom a tail ih =>
    change TRel.comp (S.atomRel a) (RawWord.relation S (liftSortWord S i tail)) = _
    rw [ih]
    rfl
end CCO.RealClosure.Bounds
