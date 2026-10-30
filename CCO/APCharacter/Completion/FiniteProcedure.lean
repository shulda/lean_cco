import CCO.APCharacter.Completion.Legality
import CCO.APCharacter.Completion.Measure
import CCO.APCharacter.Completion.Insertion
import CCO.APCharacter.Completion.PathChoice

/-! Actual finite completion by the lexicographic measure (vertices, missing
unordered pairs). The pure graph identity-folding law is kept explicit here;
the following receiving wrapper must instantiate it by the proved cycle lemma.
No assertion that this conditional helper alone closes B044 is made. -/
universe u v w t
namespace CCO.APCharacter.Completion
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable (M : MaskData S)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (laws : M.Calculus)
variable (seeds : M.FiniteSeedExtension) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (folds : FoldCycleLaw.{u,v,w,max u v} (S := S))

include H laws seeds cco folds in
/-- The terminating procedure preserves literal bits and constructs one global
marking. Identity choices contract vertices immediately, never add fake edges. -/
theorem finite_marked_completion {V : Type (max u v)} (D : PartialDiagram S V)
    (bits : V → Bit) (legal : M.LocalLegal D bits)
    (cycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ f : DiagramHom D, ∃ mark, M.GlobalMarking mark ∧
      ∀ x, mark (f.image x) = bits x := by
  classical
  letI : Finite V := D.finite_type
  obtain ⟨f⟩ := cco V D cycles
  by_cases complete : D.IsComplete
  · obtain ⟨mark,hm,hbits⟩ := terminal_marking M D bits legal complete seeds f
    exact ⟨f,mark,hm,hbits⟩
  · have missingPair : ∃ x y, ∃ hxy : x ≠ y, D.edge x y hxy = none := by
      unfold PartialDiagram.IsComplete at complete
      push_neg at complete
      obtain ⟨x,y,hxy,h⟩ := complete
      refine ⟨x,y,hxy,?_⟩
      cases he : D.edge x y hxy with
      | none => rfl
      | some a => exact False.elim (h a he)
    obtain ⟨x,y,hxy,missing⟩ := missingPair
    obtain ⟨rx,ry,bound,allowed⟩ := choose_allowed_endpoint D M bits legal H laws f x y
    cases colour : S.colour rx ry with
    | some a =>
      let E := D.withPair x y hxy a
      have legalE : M.LocalLegal E bits := insertion_legal M D bits legal x y hxy a (colour ▸ allowed)
      have cyclesE : ∀ C : SimpleCycle E, CycleHom C :=
        diversity_insertion_cycles D f x y hxy a (fun p =>
          ⟨rx,ry,graph_bound_specified_bound D rx ry bound p,colour⟩)
      obtain ⟨g,mark,hm,hbits⟩ := finite_marked_completion E bits legalE cyclesE
      have compatible : ∀ b, D.edge x y hxy = some b → a = b := by
        intro b hb
        rw [missing] at hb
        cases hb
      exact ⟨D.forgetPairHom x y hxy a compatible g,mark,hm,hbits⟩
    | none =>
      have sameSort : D.vertexSort x = D.vertexSort y :=
        congrArg Sigma.fst ((S.colour_none_iff rx ry).mp colour)
      have sameBits : bits x = bits y := real_none_same_bits M rx ry _ _ colour allowed
      obtain ⟨idBound,idBoundRev⟩ := identity_bounds_of_graph D rx ry colour bound
      let E := foldDiagram D f x y hxy sameSort missing idBound
      let newBits := fun a : Identified y => bits a.val
      have legalE : M.LocalLegal E newBits := fold_legal M D bits f legal
        x y hxy sameSort sameBits missing idBound
      have cyclesE : ∀ C : SimpleCycle E, CycleHom C :=
        folds D f x y hxy sameSort missing idBound idBoundRev
      obtain ⟨g,mark,hm,hbits⟩ := finite_marked_completion E newBits legalE cyclesE
      let q := identify x y hxy
      let sort := fun a : Identified y => D.vertexSort a.val
      let typed := fun a => (identify_sorts x y hxy D sameSort a).symm
      let compatible := pushCompatible_of_edgeCoherent D f q sort typed
        (identify_edge_coherent D f x y hxy missing idBound)
      let noCollapse := identify_no_collapse D x y hxy missing
      change DiagramHom (pushDiagram D f q sort typed compatible) at g
      let oldHom := pullPushHom D f q sort typed compatible noCollapse g
      refine ⟨oldHom,mark,hm,?_⟩
      intro a
      dsimp only [oldHom]
      rw [pullPushHom_image D f q sort typed compatible noCollapse g a]
      exact (hbits (q a)).trans (identify_bits x y hxy bits sameBits a)
termination_by (Nat.card V,missingCount D)
decreasing_by
  all_goals
    letI : Finite V := D.finite_type
    first
    | exact Prod.Lex.right _ (insertion_missingCount_lt D x y hxy missing a)
    | exact Prod.Lex.left _ _ (identify_card_lt y)

end CCO.APCharacter.Completion
