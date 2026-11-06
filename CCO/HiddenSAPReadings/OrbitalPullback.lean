import CCO.QuotientTransport.SharedActions.Orbitals
import CCO.TypedOrbitFrames.FullCoverNR2
import CCO.TransitionClosure.OriginalTypedCylinderStrong
import CCO.TransitionClosure.OriginalFiniteCylinderPartition
import CCO.PositiveWords

/-!
# Full original orbital pullback, then diversity and positive words

The output maps are arbitrary actual equivariant surjections. Their kernels
range over the FULL original invariant lattice, including Id and Top; they
are not added to the MI-only hidden signature. No theorem in this file has
a CCO, exact-ball, hidden homogeneity or hidden SAP premise.
-/

universe u v w r z t
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.GroupActions
open CCO.QuotientTransport.SharedActions CCO.TypedOrbitFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G)

/-- The actual fibre equivalence, admitted into the FULL old lattice by
fine pair homogeneity. No representedness or MI assumption is made. -/
def equivariantKernel {i : ι} {Q : Type z} [MulAction G Q]
    (τ : X i → Q) (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x) :
    ColourEq S i :=
  ⟨⟨kernel τ,⟨fun _ => rfl,fun h => h.symm,fun h k => h.trans k⟩⟩,by
    intro x y x' y' hcol
    obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' hcol
    constructor
    · intro h
      change τ x' = τ y'
      rw [← hgx,← hgy,equivτ,equivτ,h]
    · intro h
      apply MulAction.injective g
      change g • τ x = g • τ y
      rw [← equivτ,← equivτ,hgx,hgy]
      exact h⟩

theorem equivariantKernel_eq_bot_iff {i : ι} {Q : Type z} [MulAction G Q]
    (τ : X i → Q) (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x) :
    equivariantKernel S H τ equivτ = ⊥ ↔ Function.Injective τ := by
  constructor
  · intro h x y hxy
    have he : equivariantKernel S H τ equivτ x y := hxy
    rw [h] at he
    exact he
  · intro h
    apply ColourEq.ext
    intro x y
    change τ x = τ y ↔ x = y
    exact ⟨fun he => h he,congrArg τ⟩

include H in
theorem fine_orbital_eq {i j : ι} (a : S.Atom i j)
    (x : X i) (y : X j) (hxy : S.atomRel a x y) :
    orbital (G := G) x y = S.atomRel a := by
  funext x' y'
  apply propext
  constructor
  · rintro ⟨g,rfl,rfl⟩
    exact (S.colourInvariant_of_homogeneous H g x y).trans hxy
  · intro h
    exact S.pair_homogeneous_of_homogeneous H x x' y y' (hxy.trans h.symm)

variable {i j : ι} {Q : Type z} {R : Type t}
variable [MulAction G Q] [MulAction G R]

/-- The old diversity atomic spectrum. FULL pullback is computed before
this guard discards equal original real endpoints. -/
def orbitalPalette (τ : X i → Q) (σ : X j → R) (q : Q) (r : R) : S.Menu i j :=
  S.diversityGuard (pullback τ σ (orbital (G := G) q r))

/-- C40: one fine witness describes the FULL equality-inclusive relation. -/
theorem orbital_full_pullback_eq_sandwich
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q : Q) (r : R) (a : S.Atom i j)
    (x : X i) (y : X j) (hxy : S.atomRel a x y)
    (hOutput : orbital (G := G) q r (τ x) (σ y)) :
    pullback τ σ (orbital (G := G) q r) =
      originalRawTypedSandwich S (equivariantKernel S H τ equivτ)
        (equivariantKernel S H σ equivσ) a := by
  rw [saturation_of_any_root_witness τ σ equivτ equivσ hOutput,
    fine_orbital_eq S H a x y hxy]
  rfl

/-- C41: ANY diversity witness gives the SAME exact full cylinder. -/
theorem orbitalPalette_eq_cylinder
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q : Q) (r : R) (a : S.Atom i j)
    (x : X i) (y : X j) (hxy : S.atomRel a x y)
    (hOutput : orbital (G := G) q r (τ x) (σ y)) :
    orbitalPalette (G := G) S τ σ q r =
      originalTypedCylinderName S (equivariantKernel S H τ equivτ)
        (equivariantKernel S H σ equivσ) a := by
  unfold orbitalPalette originalTypedCylinderName
  rw [orbital_full_pullback_eq_sandwich S H τ σ equivτ equivσ q r a x y hxy hOutput]

/-- The only empty-diversity case uses literally the SAME original sort
and same original point; output sorts themselves may differ. -/
def RealIdentityException (τ : X i → Q) (σ : X j → R) (q : Q) (r : R) : Prop :=
  ∃ hij : i = j, Function.Bijective τ ∧ Function.Bijective σ ∧
    orbital (G := G) q r =
      (fun u v => ∃ x : X i, u = τ x ∧ v = σ (hij ▸ x))

include H in
/-- C42–43, independent of SAP/CCO/words: exact real-identity exception. -/
theorem orbitalPalette_empty_iff
    (τ : X i → Q) (σ : X j → R)
    (ontoτ : Function.Surjective τ) (ontoσ : Function.Surjective σ)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q : Q) (r : R) :
    orbitalPalette (G := G) S τ σ q r = ∅ ↔ RealIdentityException (X := X) (G := G) τ σ q r := by
  constructor
  · intro hEmpty
    have hNo : ∀ x y, ¬ diversityPullback τ σ typedRootDiversity
        (orbital (G := G) q r) x y := by
      rintro x y ⟨hOutput,hne⟩
      obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hne
      have hm : a ∈ orbitalPalette (G := G) S τ σ q r := ⟨x,y,hOutput,ha⟩
      rw [hEmpty] at hm
      exact hm
    have hij := empty_typed_diversity_forces_same_sort τ σ ontoτ ontoσ q r hNo
    cases hij
    have hSame : ∀ x y, x ≠ y → ¬ pullback τ σ (orbital (G := G) q r) x y := by
      intro x y hxy hOutput
      exact hNo x y ⟨hOutput,fun he => hxy (sigma_mk_injective he)⟩
    have h := (same_root_empty_diversity_iff τ σ ontoτ ontoσ equivτ equivσ
      (S.original_sort_transitive_of_homogeneous H i) q r).mp hSame
    exact ⟨rfl,h⟩
  · rintro ⟨hij,hτ,hσ,hGraph⟩
    cases hij
    unfold orbitalPalette
    rw [hGraph,graph_pullback_identity τ σ hτ.1 hσ.1]
    exact S.diversityGuard_ident i

/-- Both exceptional source kernels are actual bottom, not quotient equality. -/
theorem identity_exception_kernels
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q : Q) (r : R) (h : RealIdentityException (X := X) (G := G) τ σ q r) :
    equivariantKernel S H τ equivτ = ⊥ ∧ equivariantKernel S H σ equivσ = ⊥ := by
  obtain ⟨_,hτ,hσ,_⟩ := h
  exact ⟨(equivariantKernel_eq_bot_iff S H τ equivτ).mpr hτ.1,
    (equivariantKernel_eq_bot_iff S H σ equivσ).mpr hσ.1⟩

include H in
/-- C47–49: one WHOLE original RAW word, then its positive STRONG
profile. Equality exteriors are permitted and normalization deletes them;
the middle fine atom guarantees the positive alternative. -/
theorem cylinder_positive_word (sap : AgeSAP S)
    (hCover : ∀ k : ι, OriginalAllFullCoversInfinite S (i := k))
    (J : ColourEq S i) (K : ColourEq S j) (a : S.Atom i j) :
    ∃ word : PositiveWord S i j,
      PositiveWord.profile S word = originalTypedCylinderName S J K a := by
  let nr2 := original_nr2_of_all_full_covers_infinite S hCover
  obtain ⟨left,hLeft⟩ := RealClosure.Bounds.terminal_raw_word_of_originalNR2 S H nr2 J
  obtain ⟨right,hRight⟩ := RealClosure.Bounds.terminal_raw_word_of_originalNR2 S H nr2 K
  let whole := RawWord.append S left (RawWord.atom a right)
  have hWhole : RawWord.relation S whole = originalRawTypedSandwich S J K a := by
    rw [RawWord.relation_append S,hLeft]
    change TRel.comp J.val.r (TRel.comp (S.atomRel a) (RawWord.relation S right)) = _
    rw [hRight]
    funext x y
    apply propext
    constructor
    · rintro ⟨u,hJu,v,hA,hKv⟩
      exact ⟨u,v,hJu,hA,hKv⟩
    · rintro ⟨u,v,hJu,hA,hKv⟩
      exact ⟨u,hJu,v,hA,hKv⟩
  rcases PositiveWord.raw_guard_empty_or_positive_profile_of_SAP S H sap whole with
    hEmpty | ⟨word,hWord⟩
  · have hm := originalTypedCylinderName_contains_atom S J K a
    change a ∈ S.diversityGuard (originalRawTypedSandwich S J K a) at hm
    rw [← hWhole,hEmpty] at hm
    exact False.elim hm
  · rw [hWhole] at hWord
    exact ⟨word,hWord.symm⟩

/-- C51: CCO-free positive pullback for ANY complete output orbital
with a distinct-real witness. Kernels need not be represented or proper. -/
theorem complete_orbital_positive_pullback (sap : AgeSAP S)
    (hCover : ∀ k : ι, OriginalAllFullCoversInfinite S (i := k))
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q : Q) (r : R) (a : S.Atom i j)
    (x : X i) (y : X j) (hxy : S.atomRel a x y)
    (hOutput : orbital (G := G) q r (τ x) (σ y)) :
    (orbitalPalette (G := G) S τ σ q r).Nonempty ∧
      orbitalPalette (G := G) S τ σ q r =
        originalTypedCylinderName S (equivariantKernel S H τ equivτ)
          (equivariantKernel S H σ equivσ) a ∧
      ∃ word : PositiveWord S i j,
        PositiveWord.profile S word = orbitalPalette (G := G) S τ σ q r := by
  have hCylinder := orbitalPalette_eq_cylinder S H τ σ equivτ equivσ q r a x y hxy hOutput
  obtain ⟨word,hWord⟩ := cylinder_positive_word S H sap hCover
    (equivariantKernel S H τ equivτ) (equivariantKernel S H σ equivσ) a
  exact ⟨⟨a,x,y,hOutput,hxy⟩,hCylinder,word,hWord.trans hCylinder.symm⟩

end
end CCO.HiddenSAPReadings
