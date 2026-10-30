import CCO.SimultaneousQuotients.CCOBranch.Menus
import CCO.SimultaneousQuotients.CCOBranch.CycleWitnesses
import CCO.RawExact.DiagramReindex

/-!
# Actual typed simultaneous quotient HOM CCO

The proof expands quotient diversity edges into private original word
paths. Every raw cycle is handled by the two-whole-path / genuine simple
marked-cycle dichotomy and ONE quotient witness for that WHOLE cycle.
Independent real word witnesses are then glued along its marked variables.
Original semantic CCO completes the whole expanded diagram. Projection
recovers every exact endpoint block, including empty/top presentations.

No quotient homogeneity, AP, triangle fullness, SAP, quotient word-Helly,
quotient convolution or quotient FullWord criterion occurs in this branch.
-/

universe u v w q r t z
namespace CCO.SimultaneousQuotients.CCOBranch

open CCO.RawExact

variable {ι : Type u} {X : ι → Type v} {Q : ι → Type q}
variable (S : AtomicSource.{u,v,w} ι X) (T : AtomicSource.{u,q,r} ι Q)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)] [∀ i, MulAction G (Q i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
variable (π : ∀ i, X i → Q i) (surjπ : ∀ i, Function.Surjective (π i))
variable (equivπ : ∀ i (g : G) x, π i (g • x) = g • π i x)
variable (E : ∀ i, NonemptyExact S i i)
variable (hE : ∀ i, GroupActions.kernel (π i) = evaluate S (E i).words)
variable (hT : ∀ {i j} (x : Q i) (y : Q j) (x' : Q i) (y' : Q j),
  T.colour x y = T.colour x' y' ↔ GroupActions.orbital (G := G) x y x' y')

include H cco surjπ equivπ E hE hT

/-- C29-C39 for every finite ordinal input, with no presumed globally
coherent quotient realization or representatives. -/
theorem semanticCCO_fin (n : Nat) (D : PartialDiagram T (Fin n))
    (hCycles : ∀ C : SimpleCycle D, CycleHom C) : Nonempty (DiagramHom D) := by
  classical
  let P := Menus.menus S T H cco π surjπ equivπ E hE hT D
  have hNonempty := Menus.menus_nonempty S T H cco π surjπ equivπ E hE hT D
  have hRepresents := Menus.menus_represents S T H cco π surjπ equivπ E hE hT D
  change QuotientExpansion.RepresentsEdges S T D id π P at hRepresents
  have hRaw := all_raw_cycles_of_typed_cycles S T D P hNonempty π surjπ
    (Menus.occurrence_specified S T H cco π surjπ equivπ E hE hT D)
    hRepresents (Menus.menus_positive S T H cco π surjπ equivπ E hE hT D) hCycles
  obtain ⟨f⟩ := (semanticCCO_change_universe S cco) _
    (QuotientExpansion.diagram S D.vertexSort P hNonempty) hRaw
  exact ⟨Menus.project_completed S T H cco π surjπ equivπ E hE hT D f⟩

/-- Genuine semantic HOM CCO over arbitrary finite vertex types and
universes. Independent kernels may be chosen in every original sort. -/
theorem semanticCCO : SemanticCCO.{u,q,z,r} T :=
  semanticCCO_of_fin T (semanticCCO_fin S T H cco π surjπ equivπ E hE hT)

end CCO.SimultaneousQuotients.CCOBranch

namespace CCO.SimultaneousQuotients
open CCO.RawExact

/-- The source instance for literal independent quotients. All projection,
exactness, positivity, palette, cycle and expansion providers are discharged.
No quotient property is passed as a premise. -/
theorem canonical_semanticCCO
    {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
    {G : Type t} [Group G] [∀ i, MulAction G (X i)]
    (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)
    (J : ∀ i, Setoid (X i)) (E : ∀ i, NonemptyExact S i i)
    (represents : ∀ i, evaluate S (E i).words = (J i).r) :
    SemanticCCO.{u,v,z,v} (ExactCRT.CanonicalTyped.source S H J E represents) := by
  letI := S.finiteSort
  letI : ∀ i, MulAction G (Quotient (J i)) := ExactCRT.CanonicalTyped.action S H J E represents
  exact CCOBranch.semanticCCO S (ExactCRT.CanonicalTyped.source S H J E represents) H cco
    (ExactCRT.CanonicalTyped.projection J) (ExactCRT.CanonicalTyped.projection_surjective J)
    (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents) E
    (ExactCRT.CanonicalTyped.projection_kernel S J E represents)
    (ExactCRT.TypedPalette.source_colour_eq_iff_orbital (fun i => Quotient (J i)) S H id
      (ExactCRT.CanonicalTyped.projection J) (ExactCRT.CanonicalTyped.projection_surjective J)
      (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents))

end CCO.SimultaneousQuotients
