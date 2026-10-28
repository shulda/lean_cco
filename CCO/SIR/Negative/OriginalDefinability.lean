import CCO.ParityHasse.Original.Equivalences
import CCO.PairHomogeneity
import Mathlib.Data.Finset.Option

/-!
# Finite original-language formulas for the full invariant interval

A formula below is a finite disjunction of the ORIGINAL named diversity
atoms and logical equality. No class or sheet predicate is introduced.
Pair homogeneity identifies actual invariant relations with these formulas.
-/

universe u v w

namespace CCO.SIR.Negative

open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X) (i : ι)

/-- A finite disjunction of old binary atoms, with `none` denoting equality. -/
abbrev OriginalPairFormula := Finset (Option (S.Atom i i))

/-- Literal interpretation uses logical equality for the diagonal. -/
def OriginalLiteralHolds (c : Option (S.Atom i i)) (x y : X i) : Prop :=
  match c with
  | none => x = y
  | some a => S.colour x y = some a

/-- A finite original disjunction, with no parameters or added symbols. -/
def OriginalPairFormula.Holds (φ : OriginalPairFormula S i) (x y : X i) : Prop :=
  ∃ c ∈ φ, OriginalLiteralHolds S i c x y

theorem originalLiteralHolds_iff (c : Option (S.Atom i i)) (x y : X i) :
    OriginalLiteralHolds S i c x y ↔ S.colour x y = c := by
  cases c with
  | none =>
    simpa only [OriginalLiteralHolds, S.colour_none_iff, Sigma.mk.injEq,
      heq_eq_eq, true_and]
  | some a => exact Iff.rfl

theorem originalPairFormula_holds_iff (φ : OriginalPairFormula S i) (x y : X i) :
    φ.Holds S i x y ↔ S.colour x y ∈ φ := by
  simp only [OriginalPairFormula.Holds, originalLiteralHolds_iff]
  constructor
  · rintro ⟨c, hc, hcol⟩
    exact hcol ▸ hc
  · intro h
    exact ⟨_, h, rfl⟩

/-- C17: every relation constant on actual pair orbitals is a finite
parameter-free disjunction in the original equality/diversity language. -/
theorem original_formula_of_colourInvariant (R : X i → X i → Prop)
    (hR : ColourInvariant S i R) :
    ∃ φ : OriginalPairFormula S i, ∀ x y, φ.Holds S i x y ↔ R x y := by
  classical
  letI := S.finiteAtom i i
  let φ : OriginalPairFormula S i := (S.rawSupport R).toFinite.toFinset
  refine ⟨φ, ?_⟩
  intro x y
  rw [originalPairFormula_holds_iff]
  change S.colour x y ∈ (S.rawSupport R).toFinite.toFinset ↔ R x y
  rw [Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨a, b, hab, hcol⟩
    exact (hR a b x y hcol).mp hab
  · intro hxy
    exact ⟨x, y, hxy, rfl⟩

/-- A last full-lattice cover remains originally definable. Its existence
uses the finite FULL poset, rather than a chosen exact sublattice. -/
theorem last_cover_original_definable {E : ColourEq S i} (hE : E < ⊤) :
    ∃ F : ColourEq S i, E ≤ F ∧ F ⋖ ⊤ ∧
      ∃ φ : OriginalPairFormula S i, ∀ x y, φ.Holds S i x y ↔ F x y := by
  obtain ⟨F, hEF, hF⟩ := ColourEq.exists_last_cover S i hE
  exact ⟨F, hEF, hF, original_formula_of_colourInvariant S i F F.2⟩

section ActualHomogeneous

variable {G : Type*} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Full actual group invariance is equivalent to constancy on the actual
original pair colours, so the poset omits no invariant equivalence. -/
theorem invariant_iff_colourInvariant (H : HomogeneousSource S G)
    (R : X i → X i → Prop) :
    (∀ (g : G) x y, R x y → R (g • x) (g • y)) ↔ ColourInvariant S i R := by
  constructor
  · intro hInv x y x' y' hcol
    obtain ⟨g, hgx, hgy⟩ :=
      S.pair_homogeneous_of_homogeneous H x x' y y' hcol
    constructor
    · intro hxy
      simpa only [hgx, hgy] using hInv g x y hxy
    · intro hxy
      have hback := hInv g⁻¹ x' y' hxy
      rw [← hgx, ← hgy] at hback
      simpa only [inv_smul_smul] using hback
  · intro hR g x y hxy
    exact (hR (g • x) (g • y) x y
      (S.colourInvariant_of_homogeneous H g x y)).mpr hxy

/-- C17 in terms of actual automorphisms: the FULL poset of invariant
original equivalences is finite, hence so is every finite-global interval. -/
theorem finite_actual_invariant_equivalences (H : HomogeneousSource S G) :
    Finite { E : Setoid (X i) //
      ∀ (g : G) x y, E x y → E (g • x) (g • y) } := by
  let f : { E : Setoid (X i) //
      ∀ (g : G) x y, E x y → E (g • x) (g • y) } → ColourEq S i :=
    fun E => ⟨E.val, (invariant_iff_colourInvariant S i H E.val).mp E.2⟩
  apply Finite.of_injective f
  intro E F h
  exact Subtype.ext (congrArg (fun T : ColourEq S i => T.val) h)

/-- The original formula theorem applies to every actual invariant binary
relation, not just equivalences or exact supports. -/
theorem original_formula_of_invariant (H : HomogeneousSource S G)
    (R : X i → X i → Prop)
    (hR : ∀ (g : G) x y, R x y → R (g • x) (g • y)) :
    ∃ φ : OriginalPairFormula S i, ∀ x y, φ.Holds S i x y ↔ R x y :=
  original_formula_of_colourInvariant S i R
    ((invariant_iff_colourInvariant S i H R).mp hR)

end ActualHomogeneous

end CCO.SIR.Negative
