import CCO.UnaryFreshFrames.ClosureActions
import CCO.UnaryFreshFrames.Quotient.Avoidance
import CCO.UnaryFreshFrames.Quotient.Necessity

/-! Actual named well-sorted terms instantiate the elementary fibre lemmas.
Semantic functions retain their output sort, recovered by evaluating at any
real point. Syntactic term families and the signature may be infinite. -/
universe u v
namespace CCO.UnaryFreshFrames
namespace Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

abbrev Carrier (i : L.Sorts) := {x : V // H.sort x = i}

instance carrierAction (i : L.Sorts) : MulAction H.Aut (H.Carrier i) where
  smul g x := ⟨g • x.val, (H.aut_sort g x.val).trans x.property⟩
  one_smul x := Subtype.ext (one_smul H.Aut x.val)
  mul_smul g h x := Subtype.ext (mul_smul g h x.val)

/-- Literal evaluation of one ACTUAL typed named term. -/
def termFunction {i j : L.Sorts} (t : Term L i j) : H.Carrier i → V :=
  fun x => H.eval t x.val

def typedEval {i j : L.Sorts} (t : Term L i j) : H.Carrier i → H.Carrier j :=
  fun x => ⟨H.eval t x.val, H.eval_sort t x.property⟩

def NamedFunctions (i : L.Sorts) : Set (H.Carrier i → V) :=
  {f | ∃ j : L.Sorts, ∃ t : Term L i j, f = H.termFunction t}

theorem termFunction_equivariant (G : Subgroup H.Aut) {i j : L.Sorts}
    (t : Term L i j) : Quotient.Equivariant (G := G) (H.termFunction t) := by
  intro g x
  exact (H.aut_eval g.val t x.val).symm

theorem typedEval_equivariant (G : Subgroup H.Aut) {i j : L.Sorts}
    (t : Term L i j) : Quotient.Equivariant (G := G) (H.typedEval t) := by
  intro g x
  apply Subtype.ext
  exact (H.aut_eval g.val t x.val).symm

theorem termFunction_full_equivariant {i j : L.Sorts} (t : Term L i j) :
    Quotient.Equivariant (G := H.Aut) (H.termFunction t) := by
  intro g x
  exact (H.aut_eval g t x.val).symm

theorem typedEval_full_equivariant {i j : L.Sorts} (t : Term L i j) :
    Quotient.Equivariant (G := H.Aut) (H.typedEval t) := by
  intro g x
  apply Subtype.ext
  exact (H.aut_eval g t x.val).symm

/-- Each semantic function has exactly the output sort of its term. -/
theorem termFunction_output {i j : L.Sorts} (t : Term L i j) (x : H.Carrier i) :
    H.sort (H.termFunction t x) = j := H.eval_sort t x.property

/-- C18: actual singleton closure is EXACTLY the values of all existing named
real-source terms, not the values of every conceivable equivariant map. -/
theorem namedValues_eq_closureAt {i : L.Sorts} (x : H.Carrier i) :
    (fun f : H.Carrier i → V => f x) '' H.NamedFunctions i = H.closureAt x.val := by
  rcases x with ⟨x, hx⟩
  subst i
  ext y
  constructor
  · rintro ⟨f, ⟨j, t, rfl⟩, rfl⟩
    exact ⟨x, rfl, j, t, rfl⟩
  · rintro ⟨z, hz, j, t, he⟩
    change z = x at hz
    subst z
    exact ⟨H.termFunction t, ⟨j, t, rfl⟩, he⟩

theorem namedFunctions_finite (G : Subgroup H.Aut) {i : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i)) (x : H.Carrier i)
    (hfin : (H.closureAt x.val).Finite) : (H.NamedFunctions i).Finite := by
  apply Quotient.finite_semantic_functions ht x (H.NamedFunctions i)
  · rintro f ⟨j, t, rfl⟩
    exact H.termFunction_equivariant G t
  · rwa [H.namedValues_eq_closureAt x]

/-- C20: named terms have exactly the stated actual stabilizer orbit. -/
theorem named_orbit_eq_fibreValues (G : Subgroup H.Aut) {i j k : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i))
    (p : Term L i j) (t : Term L i k) (x : H.Carrier i) :
    MulAction.orbit (MulAction.stabilizer G (H.typedEval p x)) (H.termFunction t x) =
      Quotient.FibreValues (H.typedEval p) (H.termFunction t) (H.typedEval p x) :=
  Quotient.orbit_eq_fibreValues ht _ (H.typedEval_equivariant G p)
    _ (H.termFunction_equivariant G t) x

/-- Source A07: forced values must factor through an ACTUAL named term. -/
def ForcedNamedFactors {i j : L.Sorts} (p : Term L i j) : Prop :=
  ∀ (k : L.Sorts) (t : Term L i k),
    Quotient.KernelLe (H.typedEval p) (H.termFunction t) →
    ∃ s : Term L j k, ∀ x : H.Carrier i,
      H.termFunction t x = H.eval s (H.eval p x.val)

/-- Source A08 is cardinal infinitude of the actual fibre image. Its kernel
quotient interpretation is the explicit equivalence `fibreKernelEquivValues`. -/
def InfiniteUnforcedIndex {i j : L.Sorts} (p : Term L i j) : Prop :=
  ∀ (k : L.Sorts) (t : Term L i k),
    ¬ Quotient.KernelLe (H.typedEval p) (H.termFunction t) →
    ∀ b : H.Carrier j, (Quotient.FibreValues (H.typedEval p) (H.termFunction t) b).Infinite

/-- Actual named projection values belong to singleton term closure. -/
theorem typedEval_mem_closureAt {i j : L.Sorts} (p : Term L i j) (x : H.Carrier i) :
    (H.typedEval p x).val ∈ H.closureAt x.val := by
  rcases x with ⟨x, hx⟩
  subst i
  exact ⟨x, rfl, j, p, rfl⟩

theorem closureAt_mono_of_mem {x b : V} (hb : b ∈ H.closureAt x) :
    H.closureAt b ⊆ H.closureAt x := by
  apply H.closure_minimal (H.closure_closed {x})
  intro z hz
  exact hz ▸ hb

end Structure
end CCO.UnaryFreshFrames
