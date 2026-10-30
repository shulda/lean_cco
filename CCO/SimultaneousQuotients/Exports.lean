import CCO.SimultaneousQuotients.Source
import CCO.SimultaneousQuotients.CCOBranch.Semantics
import CCO.SimultaneousQuotients.FullOrbitals
import CCO.SimultaneousQuotients.FiniteAxes

/-! The selected simultaneous quotient theorem, with every source property
proved for the SAME actual literal independent quotient structure. Each proof
branch keeps its source dependencies: in particular HOM CCO is proved separately
by private word paths and ORIGINAL CCO, before this record is assembled. -/

universe u v w t z
namespace CCO.SimultaneousQuotients
open RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable (J : ∀ i, Setoid (X i)) (E : ∀ i, NonemptyExact S i i)
variable (represents : ∀ i, evaluate S (E i).words = (J i).r)

/-- Full actual source conclusion. No SAP, injective CCO, representative
section, or surjection from the old group onto full quotient Aut is a field. -/
structure SourceProperties : Prop where
  finite_sorts : Finite ι
  nonempty : ∀ i, Nonempty (Carrier J i)
  countable : Countable (Sigma (Carrier J))
  transitive :
    letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
    ∀ i (x y : Carrier J i), ∃ g : G, g • x = y
  actual_pair_orbits :
    letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
    ∀ {i j} (x : Carrier J i) (y : Carrier J j)
      (x' : Carrier J i) (y' : Carrier J j),
      (source S H J E represents).colour x y =
        (source S H J E represents).colour x' y' ↔
      GroupActions.orbital (G := G) x y x' y'
  homogeneous :
    letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
    HomogeneousSource (source S H J E represents) G
  triangles :
    letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
    ∀ {V : Type z} [Finite V] (D : ActualOrbitalDiagram G (Carrier J) V),
      D.TrianglesLegal → ∃ point : ∀ p, Carrier J (D.sort p),
        (∀ p q, D.relation p q (point p) (point q)) ∧
        Function.Injective (fun p => (⟨D.sort p, point p⟩ : Sigma (Carrier J)))
  amalgamation : AgeAP (source S H J E represents)
  joint_embedding : ∀ A B : FiniteInduced (X := Carrier J),
    ∃ (D : FiniteInduced (X := Carrier J))
      (_ : InducedEmbedding (source S H J E represents) A D)
      (_ : InducedEmbedding (source S H J E represents) B D), True
  cycles : SemanticCCO.{u,v,z,v} (source S H J E represents)

/-- `thm:typed-simultaneous-exact-quotients`, with arbitrary original sorts
and independent full exact kernels, including equality/top and arbitrary
finite formal vertex universes. All providers are actual proved instances. -/
theorem simultaneous_exact_quotients [∀ i, Countable (X i)]
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    SourceProperties.{u,v,w,t,z} S H J E represents := by
  letI := S.finiteSort
  exact ⟨inferInstance, empty_centre_request S J, countable_tagged S J,
    transitive S H J E represents, actual_colours S H J E represents,
    homogeneous S H J E represents cco, triangle_fullness S H J E represents cco,
    ageAP S H J E represents cco, ageJEP S H J E represents,
    canonical_semanticCCO S H cco J E represents⟩

end CCO.SimultaneousQuotients
