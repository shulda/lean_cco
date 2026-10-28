import CCO.SIR.Negative.Consumers
import CCO.ParityHasse.Original.SourceHasse

/-!
# The genuine original-source finite-global SIR obstruction

The FULL relative Hasse provider is instantiated by the proved original
orbital/parity/transposition theorem and the proved finite sparse graph
construction. The final theorem has only actual homogeneity, semantic
CCO, a proper invariant finite global quotient, and the necessary real
SIR singleton axioms. No SAP, countability, endpoint exactness, or
uninstantiated provider remains in this source-facing statement.
-/

universe u v w t
namespace CCO.SIR.Negative

open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) (i : ι)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- C18: the explicit provider is genuinely discharged from the standing
original source, including ALL invariant equivalence endpoints. -/
theorem fullRelativeHasseProvider_of_source (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S) : FullRelativeHasseProvider S i := by
  constructor
  · intro E F hEF a hfin
    letI := hfin
    exact full_relative_hasse S H cco E F hEF a
  · intro E F hEF a hfin
    letI := hfin
    exact finite_relative_power_two S H cco E F hEF a

/-- The source's finite covers have index two and its finite relative
indices are powers of two, without exactness assumptions. -/
theorem original_full_relative_Hasse (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S)
    (E F : ColourEq S i) (a : X i) [Finite (RelativeClass E.val F.val a)] :
    (E ⋖ F → relativeIndex E.val F.val a = 2) ∧
      (E ≤ F → ∃ k : Nat, relativeIndex E.val F.val a = 2 ^ k) :=
  full_relative_Hasse_corollary S i (fullRelativeHasseProvider_of_source S i H cco)
    E F a inferInstance

/-- C19: a proper original invariant equivalence of finite GLOBAL index
obstructs any real SIR with empty-base existence and stationarity. -/
theorem original_finite_global_obstruction
    (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,0,w} S)
    (E : Setoid (X i))
    (hInv : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (hE : E < ⊤) [Finite (Quotient E)]
    (I : Finset (X i) → Finset (X i) → Finset (X i) → Prop) :
    ¬ EmptyBaseSingletonAxioms (G := G) I :=
  original_finite_global_obstruction_of_provider S i H
    (fullRelativeHasseProvider_of_source S i H cco) E hInv hE I

/-- A finite-valued quotient map is a direct downstream consumer of the
fully instantiated source theorem. Its fibres are never new language names. -/
theorem finite_quotient_map_obstruction
    (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,0,w} S)
    {Q : Type*} [Finite Q] (π : X i → Q)
    (hInv : ∀ (g : G) x y, π x = π y → π (g • x) = π (g • y))
    (x y : X i) (hne : π x ≠ π y)
    (I : Finset (X i) → Finset (X i) → Finset (X i) → Prop) :
    ¬ EmptyBaseSingletonAxioms (G := G) I :=
  finite_quotient_map_obstruction_of_provider S i H
    (fullRelativeHasseProvider_of_source S i H cco) π hInv x y hne I

end CCO.SIR.Negative
