import CCO.Finite

/-! Transport of semantic CCO across a literal renaming of the complete
atomic palette. Real carriers, equality, specified edges and cycles stay
unchanged. -/
universe u v w w' z
namespace CCO.AclOwners
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,v,w'} ι X)
variable (e : ∀ i j, S.Atom i j ≃ T.Atom i j)
variable (hconv : ∀ i j (a : S.Atom i j), e j i (S.conv a) = T.conv (e i j a))
variable (hcol : ∀ i j (x : X i) (y : X j),
  Option.map (e i j) (S.colour x y) = T.colour x y)

private def renameDiagram {V : Type z} (D : PartialDiagram S V) : PartialDiagram T V where
  finite_type := D.finite_type
  vertexSort := D.vertexSort
  edge x y h := (D.edge x y h).map (e _ _)
  edge_reverse := by
    intro x y h a
    constructor
    · intro ha
      obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
      rw [(D.edge_reverse x y h b).mp hb]
      exact congrArg some (hconv _ _ b)
    · intro ha
      let b := (e _ _).symm a
      have hb : e _ _ b = a := (e _ _).apply_symm_apply a
      have hr : D.edge y x h.symm = some (S.conv b) := by
        apply (Option.map_injective (e _ _).injective)
        rw [Option.map_some,hconv,hb]
        exact ha
      rw [(D.edge_reverse x y h b).mpr hr]
      exact congrArg some hb

include e hconv hcol in
/-- A complete-language palette equivalence preserves genuine cycle CCO. -/
theorem semanticCCO_of_colourEquiv (cco : SemanticCCO.{u,v,z,w'} T) :
    SemanticCCO.{u,v,z,w} S := by
  intro V D hcycles
  let d := renameDiagram S T e hconv D
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
    refine ⟨point,?_⟩
    intro p a ha
    obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp ha
    exact (hcol _ _ (point p) (point (cyclicNext C.length_pos p))).symm.trans
      (congrArg (Option.map (e _ _)) (hpoint p b hb))
  obtain ⟨f⟩ := cco V d hlegal
  refine ⟨⟨f.point,?_⟩⟩
  intro x y h a ha
  apply (Option.map_injective (e _ _).injective)
  change Option.map (e _ _) (S.colour (f.point x) (f.point y)) = some (e _ _ a)
  apply (hcol _ _ (f.point x) (f.point y)).trans
  exact f.preserves_edge x y h (e _ _ a) (by
    change Option.map (e _ _) (D.edge x y h) = some (e _ _ a)
    rw [ha]
    rfl)
end CCO.AclOwners
