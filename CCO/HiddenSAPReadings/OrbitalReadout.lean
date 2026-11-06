import CCO.HiddenSAPReadings.OrbitalPartition
import CCO.HiddenSAPReadings.PairOrbitals

/-! A comparison must first be proved to be ONE actual output orbital.
The universal fine-atom spectrum then equals its full kernel cylinder.
Equality diagonals and actual equivariant transition graphs are included.
No arbitrary definable union is asserted to be a complete orbital. -/

universe u v w r z t
namespace CCO.HiddenSAPReadings
open CCO.ParityHasse.Original CCO.TransitionClosure CCO.GroupActions
open CCO.QuotientTransport.SharedActions CCO.TypedOrbitFrames
noncomputable section

section GroupFacts
variable {G Q R : Type*} [Group G] [MulAction G Q] [MulAction G R]

/-- C54: the equality diagonal is the orbital of one transitive point. -/
theorem equality_is_one_orbital (trans : ∀ x y : Q, ∃ g : G, g • x = y) (q : Q) :
    (fun x y : Q => x = y) = orbital (G := G) q q := by
  funext x y
  apply propext
  constructor
  · rintro rfl
    obtain ⟨g,hg⟩ := trans q x
    exact ⟨g,hg,hg⟩
  · rintro ⟨g,hgx,hgy⟩
    exact hgx.symm.trans hgy

/-- C54: an actual equivariant unary graph is a single orbital of
its transitive domain. A named quotient bijection is a special case. -/
theorem equivariant_graph_is_one_orbital
    (f : Q → R) (equiv : ∀ (g : G) x, f (g • x) = g • f x)
    (trans : ∀ x y : Q, ∃ g : G, g • x = y) (q : Q) :
    (fun x y => f x = y) = orbital (G := G) q (f q) := by
  funext x y
  apply propext
  constructor
  · intro h
    obtain ⟨g,hg⟩ := trans q x
    exact ⟨g,hg,(equiv g q).symm.trans ((congrArg f hg).trans h)⟩
  · rintro ⟨g,rfl,rfl⟩
    exact equiv g q

end GroupFacts

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ k : ι, MulAction G (X k)]
variable (H : HomogeneousSource S G)

/-- C53: the already named FULL semantic cylinder is exactly one
original pair orbital, proved by common actual fine representatives. -/
theorem semantic_cylinder_is_one_orbital {i j : ι}
    (J : ColourEq S i) (K : ColourEq S j)
    (P : S.Menu i j) (hP : P ∈ originalTypedCylinderNames S J K)
    (q : Quotient J.val) (r : Quotient K.val)
    (h : originalTypedCylinderSemanticRelation S J K P q r) :
    letI : MulAction G (Quotient J.val) := (originalColourEqAsInvEq S H J).quotientAction
    letI : MulAction G (Quotient K.val) := (originalColourEqAsInvEq S H K).quotientAction
    originalTypedCylinderSemanticRelation S J K P = orbital (G := G) q r := by
  letI : MulAction G (Quotient J.val) := (originalColourEqAsInvEq S H J).quotientAction
  letI : MulAction G (Quotient K.val) := (originalColourEqAsInvEq S H K).quotientAction
  funext q' r'
  apply propext
  constructor
  · intro h'
    exact same_cylinder_motion S H J K P hP q q' r r' h h'
  · rintro ⟨g,rfl,rfl⟩
    change P = originalTypedQuotientPairSpectrum S J K
      ((originalColourEqAsInvEq S H J).act g q)
      ((originalColourEqAsInvEq S H K).act g r)
    rw [original_typed_cylinder_spectrum_equivariant S H g]
    exact h

variable {i j : ι} {Q : Type z} {R : Type t}
variable [MulAction G Q] [MulAction G R]

/-- The literal universal `whenever col(x,y)=a` spectrum in source TOP. -/
def comparisonSpectrum (τ : X i → Q) (σ : X j → R) (Θ : Q → R → Prop) : S.Menu i j :=
  {a | ∀ x y, S.atomRel a x y → Θ (τ x) (σ y)}

include H in
/-- Existential and universal fine spectra agree because each fine atom
is one original orbit and the comparison is ONE actual output orbital. -/
theorem comparisonSpectrum_orbital
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (q : Q) (r : R) :
    comparisonSpectrum S τ σ (orbital (G := G) q r) =
      orbitalPalette (G := G) S τ σ q r := by
  ext a
  constructor
  · intro h
    obtain ⟨x,y,hxy⟩ := S.realized a
    exact ⟨x,y,h x y hxy,hxy⟩
  · rintro ⟨x,y,hOutput,hxy⟩ x' y' hxy'
    obtain ⟨g,hgx,hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y'
      (hxy.trans hxy'.symm)
    have h := output_orbital_pullback_invariant τ σ equivτ equivσ q r g hOutput
    change orbital (G := G) q r (τ (g • x)) (σ (g • y)) at h
    simpa only [hgx,hgy] using h

/-- C55–56 / TOP: after verifying the comparison is ONE orbital,
its exact universal atom spectrum is one nonempty positive cylinder. -/
theorem single_comparison_positive_TOP (sap : AgeSAP S)
    (hCover : ∀ k : ι, OriginalAllFullCoversInfinite S (i := k))
    (τ : X i → Q) (σ : X j → R)
    (equivτ : ∀ (g : G) x, τ (g • x) = g • τ x)
    (equivσ : ∀ (g : G) y, σ (g • y) = g • σ y)
    (Θ : Q → R → Prop) (q : Q) (r : R)
    (hΘ : Θ = orbital (G := G) q r)
    (a : S.Atom i j) (x : X i) (y : X j)
    (hxy : S.atomRel a x y) (hOutput : Θ (τ x) (σ y)) :
    comparisonSpectrum S τ σ Θ =
        originalTypedCylinderName S (equivariantKernel S H τ equivτ)
          (equivariantKernel S H σ equivσ) a ∧
      (comparisonSpectrum S τ σ Θ).Nonempty ∧
      ∃ word : PositiveWord S i j,
        PositiveWord.profile S word = comparisonSpectrum S τ σ Θ := by
  subst Θ
  rw [comparisonSpectrum_orbital S H τ σ equivτ equivσ q r]
  obtain ⟨hNonempty,hCylinder,hPositive⟩ := complete_orbital_positive_pullback
    S H sap hCover τ σ equivτ equivσ q r a x y hxy hOutput
  exact ⟨hCylinder,hNonempty,hPositive⟩

end
end CCO.HiddenSAPReadings
