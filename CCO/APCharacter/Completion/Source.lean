import CCO.APCharacter.Completion.Small
import CCO.APCharacter.Completion.FoldCycles

/-! The old graph identity law is now ACTUALLY discharged. These finite
completion exports require only the source mask totality/primality and the
accepted finite seed theorem; no identity-folding or marked-CCO provider is
left as a hypothesis. No SAP, infinitude or triangle-fullness premise occurs. -/
universe u v w z t
namespace CCO.APCharacter.Completion
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}

theorem actual_fold_cycle_law : FoldCycleLaw.{u,v,w,z} (S := S) := by
  intro V D f x y hxy sameSort missing bound boundRev C
  exact fold_cycleHom D f x y hxy sameSort missing bound boundRev C

/-- C27 in its ORIGINAL one-direction formulation. The reverse-path input
of the pure combinatorial helper is derived, rather than imposed. -/
theorem identity_folding_cycles {V : Type z} (D : PartialDiagram S V)
    (f : DiagramHom D) (x y : V) (hxy : x ≠ y)
    (sameSort : D.vertexSort x = D.vertexSort y)
    (missing : D.edge x y hxy = none) (bound : IdentityBound D x y) :
    ∀ C : SimpleCycle (foldDiagram D f x y hxy sameSort missing bound), CycleHom C :=
  fold_cycleHom D f x y hxy sameSort missing bound (identity_bound_reverse D x y hxy bound)

/-- C33's separation uses only completeness and the irreflexivity of actual
original diversity atoms, independently of SAP and triangle-definedness. -/
theorem terminal_injective {V : Type z} (D : PartialDiagram S V)
    (complete : D.IsComplete) (f : DiagramHom D) : f.IsInjective := by
  intro x y he
  by_contra hxy
  obtain ⟨a,ha⟩ := complete x y hxy
  exact S.atomRel_ne (f.preserves_edge x y hxy a ha) he

/-- On every distinct terminal pair the whole optional old colour is its
specified atom. This is induced full binary readout, not merely a positive
map on a partial diagram. Equality pairs are the source's actual diagonal. -/
theorem terminal_full_pair {V : Type z} (D : PartialDiagram S V)
    (complete : D.IsComplete) (f : DiagramHom D) (x y : V) (hxy : x ≠ y) :
    S.colour (f.point x) (f.point y) = D.edge x y hxy := by
  obtain ⟨a,ha⟩ := complete x y hxy
  exact (f.preserves_edge x y hxy a ha).trans ha.symm

variable (M : MaskData S)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (laws : M.Calculus)
variable (seeds : M.FiniteSeedExtension) (cco : SemanticCCO.{u,v,max u v,w} S)

include H laws seeds cco in
/-- C36: every finite locally legal partial graph whose old simple cycles
are feasible has one actual homomorphism with its prescribed bits realized by
ONE global marking. The selected Id outputs are actual contractions. -/
theorem marked_completion {V : Type (max u v)} (D : PartialDiagram S V)
    (bits : V → Bit) (legal : M.LocalLegal D bits)
    (cycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ f : DiagramHom D, ∃ mark, M.GlobalMarking mark ∧
      ∀ x, mark (f.image x) = bits x :=
  finite_marked_completion M H laws seeds cco actual_fold_cycle_law D bits legal cycles

include H laws seeds cco in
/-- The SAME theorem on finite ordinary chart carriers, including empty and
singleton charts. The lift changes no original source or hypothesis. -/
theorem marked_completion_small {V : Type} (D : PartialDiagram S V)
    (bits : V → Bit) (legal : M.LocalLegal D bits)
    (cycles : ∀ C : SimpleCycle D, CycleHom C) :
    ∃ f : DiagramHom D, ∃ mark, M.GlobalMarking mark ∧
      ∀ x, mark (f.image x) = bits x :=
  finite_marked_completion_small D M bits H laws seeds cco actual_fold_cycle_law legal cycles

end CCO.APCharacter.Completion
