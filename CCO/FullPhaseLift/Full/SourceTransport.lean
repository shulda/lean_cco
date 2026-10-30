import CCO.FullPhaseLift.Full.SourceIso
import CCO.APCharacter.Rank.Potential
import CCO.ParityHasse.Original.Equivalences

/-! Mechanical transport through an ACTUAL complete typed source
isomorphism. Formal vertices and every specified edge/cycle are unchanged.
The isomorphism is constructed from the actual full marked model; none
of these statements is an extra source-level provider assumption. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w u' v' w' z
namespace CCO.FullPhaseLift.Full
open ParityHasse.Original
noncomputable section
variable {κ : Type u} {Y : κ → Type v} {ι : Type u'} {X : ι → Type v'}
variable {T : AtomicSource.{u,v,w} κ Y} {S : AtomicSource.{u',v',w'} ι X}
namespace SourceIso
variable (e : SourceIso T S)
include e

/-- Rename exactly the already specified atomic edges. Missing edges,
formal equality and the complete simple-cycle support stay unchanged. -/
def mapDiagram {V : Type z} (D : CCO.PartialDiagram T V) : CCO.PartialDiagram S V where
  finite_type := D.finite_type
  vertexSort x := e.sort (D.vertexSort x)
  edge x y h := (D.edge x y h).map (e.atom _ _)
  edge_reverse := by
    intro x y h a
    constructor
    · intro ha
      obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
      rw [(D.edge_reverse x y h b).mp hb]
      exact congrArg some (e.atom_conv _ _ b)
    · intro ha
      let b := (e.atom _ _).symm a
      have hb : e.atom _ _ b = a := (e.atom _ _).apply_symm_apply a
      have hr : D.edge y x h.symm = some (T.conv b) := by
        apply (Option.map_injective (e.atom _ _).injective)
        rw [Option.map_some,e.atom_conv,hb]
        exact ha
      rw [(D.edge_reverse x y h b).mpr hr]
      exact congrArg some hb

/-- Source CCO transfers by the literal renamed diagram and literal
cycle support; no triangle or completion oracle is introduced. -/
theorem semanticCCO (cco : SemanticCCO.{u',v',z,w'} S) :
    SemanticCCO.{u,v,z,w} T := by
  intro V D hcycles
  let d := e.mapDiagram D
  have hlegal : ∀ C : SimpleCycle d, CycleHom C := by
    intro C
    let C' : SimpleCycle D := {
      length := C.length
      length_ge_three := C.length_ge_three
      length_pos := C.length_pos
      vertices := C.vertices
      next_ne := C.next_ne
      specified := by
        intro p
        obtain ⟨a,ha⟩ := C.specified p
        obtain ⟨b,hb,_⟩ := Option.map_eq_some_iff.mp ha
        exact ⟨b,hb⟩ }
    obtain ⟨point,hpoint⟩ := hcycles C'
    refine ⟨(fun p => e.point _ (point p)),?_⟩
    intro p a ha
    obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
    exact (e.colours _ _ (point p) (point (cyclicNext C.length_pos p))).symm.trans
      (congrArg (Option.map (e.atom _ _)) (hpoint p b hb))
  obtain ⟨f⟩ := cco V d hlegal
  refine ⟨⟨fun x => (e.point _).symm (f.point x),?_⟩⟩
  intro x y h a ha
  apply Option.map_injective (e.atom _ _).injective
  rw [Option.map_some,e.colours]
  simp only [Equiv.apply_symm_apply]
  exact f.preserves_edge x y h (e.atom _ _ a) (by
    change (D.edge x y h).map (e.atom _ _) = some (e.atom _ _ a)
    rw [ha]
    rfl)

/-- Numerical weights count whole occurring self-pair palettes and are
unchanged under the actual sort/atom bijections. -/
theorem potential_eq :
    letI := T.finiteSort
    letI := S.finiteSort
    APCharacter.Rank.potential (fun k => Nat.card (T.Atom k k)) =
      APCharacter.Rank.potential (fun i => Nat.card (S.Atom i i)) := by
  letI := T.finiteSort
  letI := S.finiteSort
  unfold APCharacter.Rank.potential
  calc
    (∑ k, 3 ^ Nat.card (T.Atom k k)) =
        ∑ k, 3 ^ Nat.card (S.Atom (e.sort k) (e.sort k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Nat.card_congr (e.atom k k)]
    _ = ∑ i, 3 ^ Nat.card (S.Atom i i) := e.sort.sum_comp (fun i => (3 : ℕ) ^ Nat.card (S.Atom i i))

end SourceIso
end
end CCO.FullPhaseLift.Full
