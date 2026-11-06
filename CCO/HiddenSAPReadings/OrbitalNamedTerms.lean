import CCO.HiddenSAPReadings.OrbitalReadout
import CCO.TypedOrbitFrames.RealTermKernels

/-! Actual named terms discharge the arbitrary-map hypotheses. Every
named output sort is its literal original real or represented quotient
carrier, acted on by the ORIGINAL group. Surjectivity follows from actual
equivariance and output-sort transitivity; kernel normal form additionally
identifies real Id versus an existing proper FULL MI coordinate. -/

universe u v w r
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.UnaryTermsReturn
open CCO.TypedOrbitFrames CCO.UnaryFreshFrames CCO.GroupActions
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)

/-- The original group, not an assumed homogeneous hidden group, acts
on every actual named output-sort carrier. -/
def completedSortAction (C : (originalCompletedLanguage S H sap nr2).Sorts) :
    MulAction G ((originalCompletedStructure S H sap nr2).Carrier C) where
  smul g x := ⟨originalCompletedNamedAct S H g x.val,
    (congrArg ULift.up (original_completed_vertex_sort_invariant S H g x.val)).trans
      x.property⟩
  one_smul x := Subtype.ext (original_completed_named_act_one S H x.val)
  mul_smul g h x := Subtype.ext (original_completed_named_act_mul S H g h x.val)

local instance (C : (originalCompletedLanguage S H sap nr2).Sorts) :
    MulAction G ((originalCompletedStructure S H sap nr2).Carrier C) :=
  completedSortAction S H sap nr2 C

/-- Every genuine named real/quotient output sort is transitive under
the ORIGINAL group, by actual quotient representatives. -/
theorem completed_sort_transitive (C : (originalCompletedLanguage S H sap nr2).Sorts) :
    ∀ x y : (originalCompletedStructure S H sap nr2).Carrier C,
      ∃ g : G, g • x = y := by
  rcases C with ⟨⟨i,c⟩⟩
  cases c with
  | inl unit =>
    cases unit
    intro x y
    obtain ⟨a,ha⟩ := original_completed_real_carrier_exists S H sap nr2 x
    obtain ⟨b,hb⟩ := original_completed_real_carrier_exists S H sap nr2 y
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i a b
    refine ⟨g,Subtype.ext ?_⟩
    change originalCompletedNamedAct S H g x.val = y.val
    rw [ha,hb]
    exact congrArg (fun z : X i => (Sum.inl ⟨i,z⟩ : OriginalCompletedNamedCarrier S H)) hg
  | inr D =>
    intro x y
    obtain ⟨q,hq⟩ := original_completed_hidden_carrier_exists S H sap nr2 D x
    obtain ⟨r,hr⟩ := original_completed_hidden_carrier_exists S H sap nr2 D y
    obtain ⟨a,ha⟩ := Quotient.exists_rep q
    obtain ⟨b,hb⟩ := Quotient.exists_rep r
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i a b
    refine ⟨g,Subtype.ext ?_⟩
    change originalCompletedNamedAct S H g x.val = y.val
    rw [hq,hr,← ha,← hb]
    exact congrArg (fun z : X i => originalCompletedNamedHiddenNode S H D
      (Quotient.mk D.val.val z)) hg

/-- The ACTUAL named term function, with its actual typed output. -/
def namedRealTermMap {i : ι} {C : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C) :
    X i → (originalCompletedStructure S H sap nr2).Carrier C :=
  fun x => ⟨(originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩),
    (originalCompletedStructure S H sap nr2).eval_sort t rfl⟩

theorem namedRealTermMap_equivariant {i : ι}
    {C : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C) :
    ∀ (g : G) x, namedRealTermMap S H sap nr2 t (g • x) =
      g • namedRealTermMap S H sap nr2 t x := by
  intro g x
  apply Subtype.ext
  exact ((originalCompletedStructure S H sap nr2).aut_eval
    (originalCompletedMotionHom S H sap nr2 g) t (.inl ⟨i,x⟩)).symm

/-- C52: every actual named real-source term is onto its named sort. -/
theorem namedRealTermMap_surjective {i : ι}
    {C : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C) :
    Function.Surjective (namedRealTermMap S H sap nr2 t) := by
  obtain ⟨x⟩ := S.nonemptySort i
  intro q
  obtain ⟨g,hg⟩ := completed_sort_transitive S H sap nr2 C
    (namedRealTermMap S H sap nr2 t x) q
  exact ⟨g • x,(namedRealTermMap_equivariant S H sap nr2 t g x).trans hg⟩

/-- C52/QT-NF: literal real Id or an EXISTING represented proper full
MI is the kernel of every actual named real-source term. -/
theorem named_real_term_kernel_id_or_MI {i : ι}
    {C : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C) :
    equivariantKernel S H (namedRealTermMap S H sap nr2 t)
        (namedRealTermMap_equivariant S H sap nr2 t) = ⊥ ∨
      ∃ K : OriginalNamedHiddenCoordinate S H i,
        equivariantKernel S H (namedRealTermMap S H sap nr2 t)
          (namedRealTermMap_equivariant S H sap nr2 t) = K.val := by
  rcases original_real_term_literal_named_form S H sap nr2 t with
    ⟨_,hId⟩ | ⟨j,D,E,s,_,hVal⟩
  · left
    apply (equivariantKernel_eq_bot_iff S H (namedRealTermMap S H sap nr2 t)
      (namedRealTermMap_equivariant S H sap nr2 t)).mpr
    intro x y h
    have hv := congrArg Subtype.val h
    change (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) =
      (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,y⟩) at hv
    rw [hId x,hId y] at hv
    exact sigma_mk_injective (Sum.inl.inj hv)
  · obtain ⟨K,_,theta,_,_,hKernel⟩ := original_real_named_term_literal_QTNF S H sap nr2 D E s
    right
    refine ⟨K,?_⟩
    apply ColourEq.ext
    intro x y
    change namedRealTermMap S H sap nr2 t x = namedRealTermMap S H sap nr2 t y ↔ K.val x y
    rw [Subtype.ext_iff]
    change (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,x⟩) =
      (originalCompletedStructure S H sap nr2).eval t (.inl ⟨i,y⟩) ↔ K.val x y
    rw [hVal x,hVal y]
    exact (original_completed_hidden_node_injective S H E).eq_iff.trans (hKernel x y)

/-- Actual completed binary predicates discharge the single-orbital
hypothesis on their named output-sort carriers. -/
theorem completed_binary_is_one_orbital
    {C D : (originalCompletedLanguage S H sap nr2).Sorts}
    (name : OriginalCompletedCylinderBinaryName S H)
    (q : (originalCompletedStructure S H sap nr2).Carrier C)
    (r : (originalCompletedStructure S H sap nr2).Carrier D)
    (h : originalCompletedCylinderBinaryPredicate S H name q.val r.val) :
    (fun x : (originalCompletedStructure S H sap nr2).Carrier C =>
      fun y : (originalCompletedStructure S H sap nr2).Carrier D =>
        originalCompletedCylinderBinaryPredicate S H name x.val y.val) =
      orbital (G := G) q r := by
  funext x y
  apply propext
  constructor
  · intro h'
    obtain ⟨g,hgx,hgy⟩ := same_binary_motion S H name h h'
    exact ⟨g,Subtype.ext hgx,Subtype.ext hgy⟩
  · rintro ⟨g,rfl,rfl⟩
    exact (original_completed_binary_equivariant S H g name q.val r.val).mpr h

/-- Every actual named unary term graph (in particular projections,
upward maps and quotient transitions) is one original output orbital. -/
theorem completed_term_graph_is_one_orbital
    {C D : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) C D)
    (q : (originalCompletedStructure S H sap nr2).Carrier C) :
    (fun x y => (originalCompletedStructure S H sap nr2).typedEval t x = y) =
      orbital (G := G) q ((originalCompletedStructure S H sap nr2).typedEval t q) := by
  apply equivariant_graph_is_one_orbital _ _ (completed_sort_transitive S H sap nr2 C) q
  intro g x
  apply Subtype.ext
  exact ((originalCompletedStructure S H sap nr2).aut_eval
    (originalCompletedMotionHom S H sap nr2 g) t x.val).symm

/-- Named real-source terms and a complete named binary comparison:
ALL arbitrary-map and single-orbital inputs of TOP are now discharged. -/
theorem named_binary_term_pair_TOP
    (hCover : ∀ k : ι, OriginalAllFullCoversInfinite S (i := k))
    {i j : ι} {C D : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C)
    (s : Term (originalCompletedLanguage S H sap nr2) ⟨⟨j,.inl ()⟩⟩ D)
    (name : OriginalCompletedCylinderBinaryName S H)
    (a : S.Atom i j) (x : X i) (y : X j) (hxy : S.atomRel a x y)
    (hOutput : originalCompletedCylinderBinaryPredicate S H name
      (namedRealTermMap S H sap nr2 t x).val (namedRealTermMap S H sap nr2 s y).val) :
    let τ := namedRealTermMap S H sap nr2 t
    let σ := namedRealTermMap S H sap nr2 s
    let Θ := fun (q : (originalCompletedStructure S H sap nr2).Carrier C)
      (r : (originalCompletedStructure S H sap nr2).Carrier D) =>
        originalCompletedCylinderBinaryPredicate S H name q.val r.val
    comparisonSpectrum S τ σ Θ =
        originalTypedCylinderName S
          (equivariantKernel S H τ (namedRealTermMap_equivariant S H sap nr2 t))
          (equivariantKernel S H σ (namedRealTermMap_equivariant S H sap nr2 s)) a ∧
      (comparisonSpectrum S τ σ Θ).Nonempty ∧
      ∃ word : PositiveWord S i j,
        PositiveWord.profile S word = comparisonSpectrum S τ σ Θ := by
  dsimp only
  exact single_comparison_positive_TOP S H sap hCover _ _
    (namedRealTermMap_equivariant S H sap nr2 t)
    (namedRealTermMap_equivariant S H sap nr2 s) _ _ _
    (completed_binary_is_one_orbital S H sap nr2 name _ _ hOutput) a x y hxy hOutput

/-- Exactly the three allowed complete named comparison forms. The
constructors retain their actual interpretations, rather than a supplied
unverified assertion that an arbitrary relation is one orbital. -/
inductive NamedComparison :
    (C D : (originalCompletedLanguage S H sap nr2).Sorts) →
    ((originalCompletedStructure S H sap nr2).Carrier C →
      (originalCompletedStructure S H sap nr2).Carrier D → Prop) → Prop where
  | binary {C D} (name : OriginalCompletedCylinderBinaryName S H) :
      NamedComparison C D (fun x y =>
        originalCompletedCylinderBinaryPredicate S H name x.val y.val)
  | equality (C) : NamedComparison C C (fun x y => x = y)
  | graph {C D} (t : Term (originalCompletedLanguage S H sap nr2) C D) :
      NamedComparison C D (fun x y =>
        (originalCompletedStructure S H sap nr2).typedEval t x = y)

theorem named_comparison_is_one_orbital
    {C D : (originalCompletedLanguage S H sap nr2).Sorts}
    {Θ : (originalCompletedStructure S H sap nr2).Carrier C →
      (originalCompletedStructure S H sap nr2).Carrier D → Prop}
    (hComp : NamedComparison S H sap nr2 C D Θ)
    (q : (originalCompletedStructure S H sap nr2).Carrier C)
    (r : (originalCompletedStructure S H sap nr2).Carrier D) (h : Θ q r) :
    Θ = orbital (G := G) q r := by
  cases hComp with
  | binary name => exact completed_binary_is_one_orbital S H sap nr2 name q r h
  | equality =>
      change q = r at h
      subst r
      exact equality_is_one_orbital (completed_sort_transitive S H sap nr2 C) q
  | graph t =>
      change (originalCompletedStructure S H sap nr2).typedEval t q = r at h
      subst r
      exact completed_term_graph_is_one_orbital S H sap nr2 t q

/-- Source TOP for EVERY allowed named comparison, including the hidden
equality diagonal and transition graphs. A distinct old fine witness
selects positivity even when the two output values themselves are equal. -/
theorem named_term_pair_TOP
    (hCover : ∀ k : ι, OriginalAllFullCoversInfinite S (i := k))
    {i j : ι} {C D : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C)
    (s : Term (originalCompletedLanguage S H sap nr2) ⟨⟨j,.inl ()⟩⟩ D)
    (Θ : (originalCompletedStructure S H sap nr2).Carrier C →
      (originalCompletedStructure S H sap nr2).Carrier D → Prop)
    (hComp : NamedComparison S H sap nr2 C D Θ)
    (a : S.Atom i j) (x : X i) (y : X j) (hxy : S.atomRel a x y)
    (hOutput : Θ (namedRealTermMap S H sap nr2 t x) (namedRealTermMap S H sap nr2 s y)) :
    let τ := namedRealTermMap S H sap nr2 t
    let σ := namedRealTermMap S H sap nr2 s
    comparisonSpectrum S τ σ Θ =
        originalTypedCylinderName S
          (equivariantKernel S H τ (namedRealTermMap_equivariant S H sap nr2 t))
          (equivariantKernel S H σ (namedRealTermMap_equivariant S H sap nr2 s)) a ∧
      (comparisonSpectrum S τ σ Θ).Nonempty ∧
      ∃ word : PositiveWord S i j,
        PositiveWord.profile S word = comparisonSpectrum S τ σ Θ := by
  dsimp only
  exact single_comparison_positive_TOP S H sap hCover _ _
    (namedRealTermMap_equivariant S H sap nr2 t)
    (namedRealTermMap_equivariant S H sap nr2 s) _ _ _
    (named_comparison_is_one_orbital S H sap nr2 hComp _ _ hOutput) a x y hxy hOutput

/-- Source partition: every realized old atom is in one part; common
atoms identify the output orbital; every nonempty part is one positive
full cylinder, and every empty part is precisely real Id. -/
theorem named_term_orbital_partition
    (hCover : ∀ k : ι, OriginalAllFullCoversInfinite S (i := k))
    {i j : ι} {C D : (originalCompletedLanguage S H sap nr2).Sorts}
    (t : Term (originalCompletedLanguage S H sap nr2) ⟨⟨i,.inl ()⟩⟩ C)
    (s : Term (originalCompletedLanguage S H sap nr2) ⟨⟨j,.inl ()⟩⟩ D) :
    let τ := namedRealTermMap S H sap nr2 t
    let σ := namedRealTermMap S H sap nr2 s
    (∀ a : S.Atom i j, ∃ q r, a ∈ orbitalPalette (G := G) S τ σ q r) ∧
    (∀ q q' r r',
      (orbitalPalette (G := G) S τ σ q r ∩ orbitalPalette (G := G) S τ σ q' r').Nonempty →
      orbital (G := G) q r = orbital (G := G) q' r') ∧
    (∀ q r,
      ((orbitalPalette (G := G) S τ σ q r).Nonempty ∧
        (∃ word : PositiveWord S i j,
          PositiveWord.profile S word = orbitalPalette (G := G) S τ σ q r) ∧
        ∀ (a : S.Atom i j) (x : X i) (y : X j),
          S.atomRel a x y → orbital (G := G) q r (τ x) (σ y) →
          orbitalPalette (G := G) S τ σ q r =
            originalTypedCylinderName S
              (equivariantKernel S H τ (namedRealTermMap_equivariant S H sap nr2 t))
              (equivariantKernel S H σ (namedRealTermMap_equivariant S H sap nr2 s)) a) ∨
      (orbitalPalette (G := G) S τ σ q r = ∅ ∧
        RealIdentityException (X := X) (G := G) τ σ q r)) ∧
    (∀ q q' r r', orbitalPalette (G := G) S τ σ q r = ∅ →
      orbitalPalette (G := G) S τ σ q' r' = ∅ →
      orbital (G := G) q r = orbital (G := G) q' r') := by
  dsimp only
  refine ⟨orbital_palettes_cover S _ _,?_,?_,?_⟩
  · exact orbital_palettes_overlap_eq S H _ _
      (namedRealTermMap_equivariant S H sap nr2 t)
      (namedRealTermMap_equivariant S H sap nr2 s)
  · exact complete_orbital_diversity_dichotomy S H sap hCover _ _
      (namedRealTermMap_surjective S H sap nr2 t)
      (namedRealTermMap_surjective S H sap nr2 s)
      (namedRealTermMap_equivariant S H sap nr2 t)
      (namedRealTermMap_equivariant S H sap nr2 s)
  · exact empty_orbital_palette_unique S H _ _
      (namedRealTermMap_surjective S H sap nr2 t)
      (namedRealTermMap_surjective S H sap nr2 s)
      (namedRealTermMap_equivariant S H sap nr2 t)
      (namedRealTermMap_equivariant S H sap nr2 s)

end
end CCO.HiddenSAPReadings
