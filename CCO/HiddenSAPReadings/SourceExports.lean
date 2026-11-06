import CCO.HiddenSAPReadings.FullOriginalLift
import CCO.HiddenSAPReadings.Rigidity
import CCO.HiddenSAPReadings.Anchors
import CCO.HiddenSAPReadings.SourceSupport
import CCO.HiddenSAPReadings.OrbitalNamedTerms
import CCO.HiddenSAPReadings.PartialSplitting
import CCO.UnaryFreshFrames.UniformBounds

/-! Source13 on the ACTUAL FULL original automorphism group. The
homogeneity/SAP branch alone uses semantic CCO. Orbital kernels, positive
pullbacks, named comparisons and their partition have no CCO premise.
The standing FULL cover hypothesis derives NR2 in every named signature.
Higher-arity frozen-factor interfaces remain separate from these binary
exports. -/

universe u v w r z t
namespace CCO.HiddenSAPReadings.Source
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.TerminalPowers CCO.GroupActions
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))

local notation "HF" => full_homogeneous S H
local notation "NR2" => original_nr2_of_all_full_covers_infinite S hCover
local notation "Lang" => originalCompletedLanguage S HF sap NR2
local notation "Hidden" => originalCompletedStructure S HF sap NR2
local notation "Values" => OriginalCompletedNamedCarrier S HF

/-- Actual hidden countability comes from finitely many real/quotient
sorts of the original countable source, including every orphan value. -/
theorem typed_hidden_countable [∀ i, Countable (X i)] : Countable Values := by
  letI : Fintype ι := S.finiteSort
  letI (i : ι) : Finite (OriginalNamedHiddenCoordinate S HF i) :=
    original_named_hidden_coordinates_finite S HF
  letI : Finite (OriginalCompletedCoordinateCode S HF) := inferInstance
  letI (C : OriginalCompletedCoordinateCode S HF) : Countable (CoordinateValue S HF C) :=
    inferInstance
  exact Countable.of_equiv _ (coordinateEquiv S HF)

/-- The exact source C05 linear bound holds for EVERY finite hidden
parameter set, including sets with only orphan quotient vertices. -/
theorem typed_hidden_finite_closure_bound (T : Finset Values) :
    ((Hidden).closure (T : Set Values)).ncard ≤
      T.card * originalSourceUniformNormalCodeBudget S HF :=
  Structure.closure_ncard_le_mul Hidden (originalSourceUniformNormalCodeBudget S HF)
    (fun _ => True)
    (fun x _ => CCO.HereditaryHiddenOrbits.singleton_bound S HF sap hCover x)
    T (fun _ _ => True.intro)

/-- No nullary generator is added by the actual named interpretation. -/
theorem typed_hidden_empty_closure : (Hidden).closure ∅ = ∅ := (Hidden).closure_empty

/-- Joint exact lifting retains ONE genuine FULL original g on the
entire finite closed hidden map, including orphan-only and empty domains. -/
theorem typed_hidden_full_original_lift [∀ i, Countable (X i)]
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (A : (Hidden).Piece) (f g : A.Embedding Set.univ) :
    ∃ h : FullAut S, ∀ a, originalCompletedNamedAct S HF h (f.point a) = g.point a :=
  closed_embeddings_full_original_lift S HF sap NR2 cco A f g

/-- Source thm:typed-hidden-sap. Homogeneity through one ORIGINAL g is
established first; accepted arbitrary closed-base orbit infinitude then
discharges the hereditary SAP criterion on the ENTIRE actual closed age. -/
theorem typed_hidden_sap [∀ i, Countable (X i)]
    (cco : SemanticCCO.{u,v,max u v,w} S) :
    (Hidden).Homogeneous ∧ (Hidden).LocallyFinite ∧ (Hidden).AgeSAP := by
  have hom := hidden_homogeneous_via_full_original S HF sap NR2 cco
  exact ⟨hom,CCO.HereditaryHiddenOrbits.locally_finite S HF sap hCover,
    Structure.ageSAP_of_infiniteClosedOrbits _ hom
      (CCO.HereditaryHiddenOrbits.full_closed_orbits S HF sap hCover cco)⟩

/-- Source lem:typed-hidden-rigidity in the actual completed binary
language: a homomorphism is the point map of an induced embedding. -/
theorem typed_hidden_rigidity (A B : (Hidden).Piece)
    (f : CompletedHom S HF sap NR2 A B.points) :
    Function.Injective f.point ∧ ∃ e : A.Embedding B.points, e.point = f.point :=
  ⟨f.injective, f.toEmbedding,rfl⟩

/-- Source ACR and lem:typed-anchored-real-clone-readout, for every
actual named proper coordinate and every retained mixed cylinder. -/
theorem typed_anchored_real_clone_readout {i : ι} (p p' : X i)
    {Q : Set Values} (B : AnchorFrame S HF p Q)
    (hFine : SameFineToFrame S p p' B.points) :
    (∀ D : OriginalNamedHiddenCoordinate S HF i,
      Quotient.mk D.val.val p' = Quotient.mk D.val.val p) ∧
    (∀ {C : (Lang).Sorts} (t : Term Lang ⟨⟨i,.inl ()⟩⟩ C),
      C ≠ ⟨⟨i,.inl ()⟩⟩ →
      (Hidden).eval t (.inl ⟨i,p'⟩) = (Hidden).eval t (.inl ⟨i,p⟩)) ∧
    (∀ {j : ι} (D : OriginalNamedHiddenCoordinate S HF j) (q : Quotient D.val.val),
      originalCompletedNamedHiddenNode S HF D q ∈ Q →
      ∀ R : OriginalCompletedCylinderBinaryName S HF,
        originalCompletedCylinderBinaryPredicate S HF R (.inl ⟨i,p'⟩)
            (originalCompletedNamedHiddenNode S HF D q) ↔
          originalCompletedCylinderBinaryPredicate S HF R (.inl ⟨i,p⟩)
            (originalCompletedNamedHiddenNode S HF D q)) :=
  CCO.HiddenSAPReadings.typed_anchored_real_clone_readout S HF sap NR2 p p' B hFine

/-- Source lem:typed-real-sort-splitting. All displayed relations and
actual typed unary graphs are preserved in one finite visible extension;
proper hidden images stay literal, while real positions and designated
proper representatives become distinct as recorded in SplitAssignment.
The construction works for every homomorphism, hence for the source's
homomorphism-embeddings without a stronger completion premise. -/
theorem typed_real_sort_splitting {P : Type z} [Finite P]
    (C : CCO.UnarySupport.Structure (originalPartialSignature S HF sap NR2) P)
    (f : CCO.UnarySupport.Structure.Hom C (originalPartialTarget S HF sap NR2))
    (A : Set (Sigma X)) (hA : A.Finite) :
    ∃ r : SplitAssignment S HF f.point A,
      ∃ (D : (Hidden).Piece) (hD : (originalPartialTarget S HF sap NR2).IsClosed D.points),
        ∃ g : CCO.UnarySupport.Structure.Hom C
          ((originalPartialTarget S HF sap NR2).induce D.points hD),
          (∀ p, (g.point p).val = r.point p) ∧
          D.points = (Hidden).closure (Sum.inl '' r.world.vertices) :=
  typed_partial_real_sort_splitting S HF sap NR2 C f A hA

/-- Source lem:typed-joined-source-support. The original partial source
must really be irreducible on its whole closed support, with the stated
singleton bounds. The completed image is in the ACTUAL interpreted H. -/
theorem typed_joined_source_support {P : Type z} [Finite P]
    (C : CCO.UnarySupport.Structure (originalPartialSignature S HF sap NR2) P)
    (B : Finset P) {k m : ℕ} (hB : B.card ≤ k)
    (hm : ∀ b ∈ B, Nat.card (C.closureAt b) ≤ m)
    (hirr : (C.closureStructure (B : Set P)).Irreducible)
    (f : CCO.UnarySupport.Structure.Hom C (originalPartialTarget S HF sap NR2))
    (hf : f.HomEmbedding) :
    Nat.card (C.closure (B : Set P)) ≤ k * m ∧
    ∃ e : CCO.UnarySupport.Structure.Embedding
        (C.closureStructure (B : Set P)) (originalPartialTarget S HF sap NR2),
      (∀ x, e.point x = f.point x.val) ∧ (Set.range e.point).Finite ∧
      (Hidden).Closed (Set.range e.point) ∧
      Nonempty (CCO.UnarySupport.Structure.DiagramIso
        (C.closureStructure (B : Set P))
        ((originalPartialTarget S HF sap NR2).induce (Set.range e.point)
          (SourceSupport.embedding_range_closed e))) :=
  typed_joined_source_support_actual S HF sap hCover C B hB hm hirr f hf

section ArbitraryMaps
variable {i j : ι} {Q : Type z} {R : Type t}
variable [MulAction (FullAut S) Q] [MulAction (FullAut S) R]

/-- Source orbital dichotomy, BEFORE positivity: exact true-real-Id
exception, with no SAP, CCO, hidden homogeneity or MI requirement. -/
theorem typed_term_orbit_diagonal_dichotomy
    (τ : X i → Q) (σ : X j → R)
    (ontoτ : Function.Surjective τ) (ontoσ : Function.Surjective σ)
    (equivτ : ∀ (g : FullAut S) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : FullAut S) y, σ (g • y) = g • σ y)
    (q : Q) (r : R) :
    ((orbitalPalette (G := FullAut S) S τ σ q r).Nonempty ∧
      ∀ (a : S.Atom i j) (x : X i) (y : X j),
        S.atomRel a x y → orbital (G := FullAut S) q r (τ x) (σ y) →
        orbitalPalette (G := FullAut S) S τ σ q r =
          originalTypedCylinderName S (equivariantKernel S HF τ equivτ)
            (equivariantKernel S HF σ equivσ) a) ∨
    (orbitalPalette (G := FullAut S) S τ σ q r = ∅ ∧
      RealIdentityException (X := X) (G := FullAut S) τ σ q r) := by
  classical
  by_cases hn : (orbitalPalette (G := FullAut S) S τ σ q r).Nonempty
  · exact Or.inl ⟨hn,fun a x y hxy hOut =>
      orbitalPalette_eq_cylinder S HF τ σ equivτ equivσ q r a x y hxy hOut⟩
  · have he := Set.not_nonempty_iff_eq_empty.mp hn
    exact Or.inr ⟨he,(orbitalPalette_empty_iff S HF τ σ ontoτ ontoσ equivτ equivσ q r).mp he⟩

include sap hCover in
/-- Source lem:typed-complete-orbital-positive-NR2-SAP. Arbitrary actual
equivariant surjections have FULL original kernels, including Id and Top.
The whole-word positive result uses old SAP and full terminal indices,
and explicitly has NO CCO hypothesis. -/
theorem typed_complete_orbital_positive_NR2_SAP
    (τ : X i → Q) (σ : X j → R)
    (ontoτ : Function.Surjective τ) (ontoσ : Function.Surjective σ)
    (equivτ : ∀ (g : FullAut S) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : FullAut S) y, σ (g • y) = g • σ y)
    (q : Q) (r : R) :
    ((orbitalPalette (G := FullAut S) S τ σ q r).Nonempty ∧
      (∃ word : PositiveWord S i j,
        PositiveWord.profile S word = orbitalPalette (G := FullAut S) S τ σ q r) ∧
      ∀ (a : S.Atom i j) (x : X i) (y : X j),
        S.atomRel a x y → orbital (G := FullAut S) q r (τ x) (σ y) →
        orbitalPalette (G := FullAut S) S τ σ q r =
          originalTypedCylinderName S (equivariantKernel S HF τ equivτ)
            (equivariantKernel S HF σ equivσ) a) ∨
    (orbitalPalette (G := FullAut S) S τ σ q r = ∅ ∧
      RealIdentityException (X := X) (G := FullAut S) τ σ q r) :=
  complete_orbital_diversity_dichotomy S HF sap hCover τ σ ontoτ ontoσ equivτ equivσ q r

end ArbitraryMaps

/-- Source TOP / lem:typed-term-pair-orbit-pullback. The comparison is
one of the ACTUAL named binary, equality or equivariant unary graph
forms; its single-orbital property and all term inputs are discharged. -/
theorem typed_term_pair_orbit_pullback
    {i j : ι} {C D : (Lang).Sorts}
    (t : Term Lang ⟨⟨i,.inl ()⟩⟩ C) (s : Term Lang ⟨⟨j,.inl ()⟩⟩ D)
    (Θ : (Hidden).Carrier C → (Hidden).Carrier D → Prop)
    (hComp : NamedComparison S HF sap NR2 C D Θ)
    (a : S.Atom i j) (x : X i) (y : X j) (hxy : S.atomRel a x y)
    (hOut : Θ (namedRealTermMap S HF sap NR2 t x) (namedRealTermMap S HF sap NR2 s y)) :
    letI : MulAction (FullAut S) ((Hidden).Carrier C) := completedSortAction S HF sap NR2 C
    letI : MulAction (FullAut S) ((Hidden).Carrier D) := completedSortAction S HF sap NR2 D
    let τ := namedRealTermMap S HF sap NR2 t
    let σ := namedRealTermMap S HF sap NR2 s
    comparisonSpectrum S τ σ Θ =
        originalTypedCylinderName S
          (equivariantKernel S HF τ (namedRealTermMap_equivariant S HF sap NR2 t))
          (equivariantKernel S HF σ (namedRealTermMap_equivariant S HF sap NR2 s)) a ∧
      (comparisonSpectrum S τ σ Θ).Nonempty ∧
      ∃ word : PositiveWord S i j,
        PositiveWord.profile S word = comparisonSpectrum S τ σ Θ := by
  letI : MulAction (FullAut S) ((Hidden).Carrier C) := completedSortAction S HF sap NR2 C
  letI : MulAction (FullAut S) ((Hidden).Carrier D) := completedSortAction S HF sap NR2 D
  exact named_term_pair_TOP S HF sap NR2 hCover t s Θ hComp a x y hxy hOut

/-- Source partition corollary. Nonempty parts are one full cylinder
and one positive STRONG word; distinct orbital parts are disjoint and
the unique possible empty part is the same-original-real-point graph. -/
theorem typed_complete_orbital_pullback_partition
    {i j : ι} {C D : (Lang).Sorts}
    (t : Term Lang ⟨⟨i,.inl ()⟩⟩ C) (s : Term Lang ⟨⟨j,.inl ()⟩⟩ D) :
    letI : MulAction (FullAut S) ((Hidden).Carrier C) := completedSortAction S HF sap NR2 C
    letI : MulAction (FullAut S) ((Hidden).Carrier D) := completedSortAction S HF sap NR2 D
    let τ := namedRealTermMap S HF sap NR2 t
    let σ := namedRealTermMap S HF sap NR2 s
    (∀ a : S.Atom i j, ∃ q r, a ∈ orbitalPalette (G := FullAut S) S τ σ q r) ∧
    (∀ q q' r r',
      Disjoint (orbitalPalette (G := FullAut S) S τ σ q r)
        (orbitalPalette (G := FullAut S) S τ σ q' r') ∨
      orbital (G := FullAut S) q r = orbital (G := FullAut S) q' r') ∧
    (∀ q r, (orbitalPalette (G := FullAut S) S τ σ q r).Nonempty →
      ∃ (a : S.Atom i j) (word : PositiveWord S i j),
        orbitalPalette (G := FullAut S) S τ σ q r =
          originalTypedCylinderName S
            (equivariantKernel S HF τ (namedRealTermMap_equivariant S HF sap NR2 t))
            (equivariantKernel S HF σ (namedRealTermMap_equivariant S HF sap NR2 s)) a ∧
        PositiveWord.profile S word = orbitalPalette (G := FullAut S) S τ σ q r) ∧
    (∀ q r, orbitalPalette (G := FullAut S) S τ σ q r = ∅ ↔
      RealIdentityException (X := X) (G := FullAut S) τ σ q r) ∧
    (∀ q q' r r', orbitalPalette (G := FullAut S) S τ σ q r = ∅ →
      orbitalPalette (G := FullAut S) S τ σ q' r' = ∅ →
      orbital (G := FullAut S) q r = orbital (G := FullAut S) q' r') := by
  classical
  letI : MulAction (FullAut S) ((Hidden).Carrier C) := completedSortAction S HF sap NR2 C
  letI : MulAction (FullAut S) ((Hidden).Carrier D) := completedSortAction S HF sap NR2 D
  dsimp only
  let τ := namedRealTermMap S HF sap NR2 t
  let σ := namedRealTermMap S HF sap NR2 s
  have hτ := namedRealTermMap_equivariant S HF sap NR2 t
  have hσ := namedRealTermMap_equivariant S HF sap NR2 s
  have hτonto := namedRealTermMap_surjective S HF sap NR2 t
  have hσonto := namedRealTermMap_surjective S HF sap NR2 s
  refine ⟨orbital_palettes_cover S τ σ,?_,?_,?_,?_⟩
  · intro q q' r r'
    by_cases he : orbital (G := FullAut S) q r = orbital (G := FullAut S) q' r'
    · exact Or.inr he
    · exact Or.inl (orbital_palettes_disjoint S HF τ σ hτ hσ q q' r r' he)
  · rintro q r ⟨a,x,y,hOut,hxy⟩
    obtain ⟨_,hCylinder,word,hWord⟩ := complete_orbital_positive_pullback
      S HF sap hCover τ σ hτ hσ q r a x y hxy hOut
    exact ⟨a,word,hCylinder,hWord⟩
  · exact orbitalPalette_empty_iff S HF τ σ hτonto hσonto hτ hσ
  · exact empty_orbital_palette_unique S HF τ σ hτonto hσonto hτ hσ

end
end CCO.HiddenSAPReadings.Source
