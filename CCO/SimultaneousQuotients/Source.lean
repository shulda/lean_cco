import CCO.ExactCRT.CanonicalTypedQuotients
import CCO.RawExact.QuotientHomogeneousSource
import CCO.RawExact.QuotientTriangleFullness
import CCO.RigidGroupoid.Geometry.Quotient.Blocks

/-! B041 C19–C28: the literal simultaneous quotients of independently typed
original sorts. The finite palette and actions are already constructed in the
accepted typed quotient API. The new source inheritance instantiates the genuine
original exact-ball and joint-lifting theorems, on the displayed quotient points.
It neither adds real representatives to a partial map nor assumes quotient CCO. -/

universe u v w t z
namespace CCO.SimultaneousQuotients
open RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable (J : ∀ i, Setoid (X i)) (E : ∀ i, NonemptyExact S i i)
variable (represents : ∀ i, evaluate S (E i).words = (J i).r)

abbrev Carrier (i : ι) := Quotient (J i)
abbrev projection (i : ι) : X i → Carrier J i := ExactCRT.CanonicalTyped.projection J i

@[instance_reducible] noncomputable def action (i : ι) : MulAction G (Carrier J i) :=
  ExactCRT.CanonicalTyped.action S H J E represents i

noncomputable abbrev source : AtomicSource ι (Carrier J) :=
  ExactCRT.CanonicalTyped.source S H J E represents

theorem onto (i : ι) : Function.Surjective (projection J i) :=
  ExactCRT.CanonicalTyped.projection_surjective J i

include represents in
theorem exact_kernel (i : ι) :
    GroupActions.kernel (projection J i) = evaluate S (E i).words :=
  ExactCRT.CanonicalTyped.projection_kernel S J E represents i

theorem equivariant :
    letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
    ∀ i (g : G) x, projection J i (g • x) = g • projection J i x := by
  intro i g x
  rfl

theorem actual_colours :
    letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
    ∀ {i j} (x : Carrier J i) (y : Carrier J j)
      (x' : Carrier J i) (y' : Carrier J j),
      (source S H J E represents).colour x y =
        (source S H J E represents).colour x' y' ↔
      GroupActions.orbital (G := G) x y x' y' := by
  letI := S.finiteSort
  letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
  intro i j x y x' y'
  exact ExactCRT.TypedPalette.source_colour_eq_iff_orbital (Carrier J) S H id
    (projection J) (onto J) (equivariant S H J E represents) x y x' y'

theorem transitive :
    letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
    ∀ i (x y : Carrier J i), ∃ g : G, g • x = y := by
  letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
  intro i x y
  exact ExactCRT.TypedPalette.quotient_transitive (Carrier J) S H id
    (projection J) (onto J) (equivariant S H J E represents) i x y

theorem countable_carrier [∀ i, Countable (X i)] (i : ι) : Countable (Carrier J i) :=
  (onto J i).countable

include S in
theorem countable_tagged [∀ i, Countable (X i)] : Countable (Sigma (Carrier J)) := by
  letI := S.finiteSort
  letI : Encodable ι := Encodable.ofCountable _
  letI : ∀ i, Encodable (Carrier J i) := fun i =>
    @Encodable.ofCountable _ (countable_carrier J i)
  infer_instance

/-- Arbitrary anchored requests, including empty/singleton centre families.
The original heterogeneous ball theorem works with arbitrary fixed real
representatives, since each requested block is the FULL inverse image. -/
theorem request_helly (cco : SemanticCCO.{u,v,max u v,w} S)
    {I : Type z} [Finite I] (m : ι) (sort : I → ι) :
    letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
    ∀ (R : ∀ p, Carrier J m → Carrier J (sort p) → Prop),
    (∀ p, ∃ a b, R p = GroupActions.orbital (G := G) a b) →
    ∀ centres : ∀ p, Carrier J (sort p),
    (∀ p q, ∃ a, R p a (centres p) ∧ R q a (centres q)) →
      ∃ a, ∀ p, R p a (centres p) := by
  letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
  intro R actual centres hPair
  exact actual_quotient_request_helly_of_CCO S H cco
    (Carrier J m) (projection J m) (onto J m) (equivariant S H J E represents m)
    (E m) (exact_kernel S J E represents m) sort (fun p => Carrier J (sort p))
    (fun p => projection J (sort p)) (fun p => onto J (sort p))
    (fun p => equivariant S H J E represents (sort p))
    (fun p => E (sort p)) (fun p => exact_kernel S J E represents (sort p))
    R actual centres hPair

/-- Actual finite triangle fullness, for ANY finite vertex universe. Its proof
uses original pair alignment followed by original ball Helly, not quotient
homogeneity or quotient CCO. Injectivity follows from requested diversity. -/
theorem triangle_fullness (cco : SemanticCCO.{u,v,max u v,w} S) :
    letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
    ∀ {V : Type z} [Finite V] (D : ActualOrbitalDiagram G (Carrier J) V),
      D.TrianglesLegal → ∃ point : ∀ p, Carrier J (D.sort p),
        (∀ p q, D.relation p q (point p) (point q)) ∧
        Function.Injective (fun p => (⟨D.sort p, point p⟩ : Sigma (Carrier J))) := by
  letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
  intro V _ D hTriangles
  exact actual_quotient_triangle_fullness_of_CCO S H cco (Carrier J) id
    (projection J) (onto J) (equivariant S H J E represents)
    E (exact_kernel S J E represents) D hTriangles

/-- Only the same displayed quotient vertices occur in the finite joint map.
The individual original lift is constructed by accepted C21; no fine points
are silently added, and no coherent group section is chosen. -/
theorem homogeneous [∀ i, Countable (X i)]
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
    HomogeneousSource (source S H J E represents) G := by
  letI := S.finiteSort
  letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
  exact actual_quotient_homogeneous_of_CCO S H cco (Carrier J) id
    (projection J) (onto J) (equivariant S H J E represents)
    E (exact_kernel S J E represents) (source S H J E represents)
    (actual_colours S H J E represents)

theorem ageAP [∀ i, Countable (X i)]
    (cco : SemanticCCO.{u,v,max u v,w} S) : AgeAP (source S H J E represents) := by
  letI : ∀ i, MulAction G (Carrier J i) := action S H J E represents
  exact ageAP_of_homogeneous (source S H J E represents)
    (homogeneous S H J E represents cco)

/-- Ordinary JEP uses the literal finite induced union. Additional common
points are allowed; this is deliberately not strong amalgamation. -/
theorem ageJEP (A B : FiniteInduced (X := Carrier J)) :
    ∃ (D : FiniteInduced (X := Carrier J))
      (_ : InducedEmbedding (source S H J E represents) A D)
      (_ : InducedEmbedding (source S H J E represents) B D), True := by
  let D : FiniteInduced (X := Carrier J) :=
    ⟨A.vertices ∪ B.vertices, A.finite_vertices.union B.finite_vertices⟩
  let eA : InducedEmbedding (source S H J E represents) A D :=
    { toEmbedding := ⟨fun a => ⟨a.val, Or.inl a.property⟩,
        fun a b h => Subtype.ext (congrArg (fun p : ↥D.vertices => p.val) h)⟩
      preserves_sort := fun _ => rfl
      preserves_colours := fun _ _ => rfl }
  let eB : InducedEmbedding (source S H J E represents) B D :=
    { toEmbedding := ⟨fun b => ⟨b.val, Or.inr b.property⟩,
        fun a b h => Subtype.ext (congrArg (fun p : ↥D.vertices => p.val) h)⟩
      preserves_sort := fun _ => rfl
      preserves_colours := fun _ _ => rfl }
  exact ⟨D, eA, eB, trivial⟩

end CCO.SimultaneousQuotients
