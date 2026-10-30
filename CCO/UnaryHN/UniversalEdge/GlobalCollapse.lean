import CCO.UnaryHN.UniversalEdge.Boundaries

/-! Completed complete-graph members are rigid. A reducible incomplete
two-point source can nevertheless retain its constant completion map. -/

namespace CCO.UnaryHN.Native.UniversalEdgeBoundaries

open StructuralRamsey
open StructuralRamsey.Structure

instance {L : Language} [IsEmpty L.FuncSymbol] :
    IsEmpty (edgeLanguage L).FuncSymbol := by
  change IsEmpty L.FuncSymbol
  infer_instance

theorem isolated_constant_HE_to {L : Language} [IsEmpty L.FuncSymbol]
    (H : Structure L Unit) (hNoRel : ∀ R xs, ¬ H.rel R xs) :
    HE (isolated L Bool) H (fun _ => ()) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro R xs h
    exact False.elim h
  · intro F
    exact isEmptyElim F
  · intro X E hE e
    letI : Subsingleton X := irreducible_in_isolatedBool_subsingleton E hE e
    refine ⟨{ toFun := fun _ => (), injective := fun _ _ _ => Subsingleton.elim _ _,
               map_rel_iff := ?_, map_func := ?_ }, fun _ => rfl⟩
    · intro R xs
      constructor
      · intro h
        exact False.elim (hNoRel R _ h)
      · intro h
        exact False.elim ((e.map_rel_iff R xs).mpr h)
    · intro F
      exact isEmptyElim F

def finiteGraphClass : Class.{0,0} graphLanguage :=
  fun {X} C => Finite X ∧ ∀ xs : Fin 2 → X, C.rel () xs ↔ xs 0 ≠ xs 1

theorem complete_graph_irreducible {V : Type} (C : Structure graphLanguage V)
    (hC : ∀ xs : Fin 2 → V, C.rel () xs ↔ xs 0 ≠ xs 1) : C.Irreducible := by
  classical
  intro G E F Z Root Left Right Whole sL sR iL iR hFree e
  by_cases hLeft : ∀ a, ∃ x, e a = iL x
  · exact Or.inl hLeft
  · right
    obtain ⟨a, ha⟩ := not_forall.mp hLeft
    have hRight : ∃ x, e a = iR x := by
      rcases hFree.covers (e a) with h | h
      · exact False.elim (ha h)
      · exact h
    intro b
    by_cases hab : a = b
    · subst b
      exact hRight
    · have hTuple : Whole.rel () (e ∘ ![a, b]) :=
        (e.map_rel_iff () _).mpr ((hC _).mpr hab)
      rcases (hFree.rel_iff () _).mp hTuple with ⟨ys, _, hEq⟩ | ⟨ys, _, hEq⟩
      · exact False.elim (ha ⟨ys 0, congrFun hEq 0⟩)
      · exact ⟨ys 1, congrFun hEq 1⟩

theorem complete_graph_class_rigid : CompletedMapRigidity finiteGraphClass :=
  completedMapRigidity_of_irreducible (fun C hC => complete_graph_irreducible C hC.2)

theorem isolated_expanded_graph_local_membership :
    IrreduciblesIn (ExpandedClass finiteGraphClass)
      (isolated (edgeLanguage graphLanguage) Bool) := by
  intro X E hE e
  letI : Subsingleton X := irreducible_in_isolatedBool_subsingleton E hE e
  apply ExpandedClass.of_edge_iff
  · refine ⟨Finite.of_injective e e.injective, ?_⟩
    intro xs
    constructor
    · intro h
      exact False.elim ((e.map_rel_iff (.inl ()) xs).mpr h)
    · intro h
      exact False.elim (h (Subsingleton.elim _ _))
  · intro xs
    constructor
    · intro h
      exact False.elim ((e.map_rel_iff (.inr ()) xs).mpr h)
    · intro h
      exact False.elim (h (Subsingleton.elim _ _))

/-- C44: all completed members are irreducible and rigid, every actual
expanded irreducible source is completed, yet the SAME expanded HE collapses
the incomplete source's two points. -/
theorem rigidity_does_not_force_global_injection :
    CompletedMapRigidity finiteGraphClass ∧
    IrreduciblesIn (ExpandedClass finiteGraphClass)
      (isolated (edgeLanguage graphLanguage) Bool) ∧
    HE (isolated (edgeLanguage graphLanguage) Bool)
      (expandEdge (completeGraph Unit)) (fun _ => ()) ∧
    ¬ Function.Injective (fun _ : Bool => ()) := by
  refine ⟨complete_graph_class_rigid, isolated_expanded_graph_local_membership, ?_, ?_⟩
  · apply same_map_universal_edge complete_graph_class_rigid
      isolated_expanded_graph_local_membership
    · exact ⟨inferInstance, fun _ => Iff.rfl⟩
    · exact isolated_constant_HE_to (completeGraph Unit)
        (fun _ xs h => h (Subsingleton.elim _ _))
  · intro h
    have bad : false = true := h (a₁ := false) (a₂ := true) rfl
    cases bad

end CCO.UnaryHN.Native.UniversalEdgeBoundaries
