import CCO.SIR.Negative.TwoClass
import CCO.SIR.Negative.OriginalDefinability

/-!
# The finite-global obstruction, with the full relative Hasse input explicit

`FullRelativeHasseProvider` is the upstream theorem interface for the FULL
original invariant lattice, including nonexact endpoints. This file does
not claim to prove or instantiate it from CCO. The final implication uses
only its cover-index-two field, and its conclusion is already impossible
for the three singleton consequences of a real SIR.
-/

universe u v w

namespace CCO.SIR.Negative

open CCO.ParityHasse.Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X) (i : ι)

/-- Explicit upstream FULL relative Hasse theorem; exactness is absent. -/
structure FullRelativeHasseProvider : Prop where
  cover_index_two : ∀ (E F : ColourEq S i), E ⋖ F → ∀ a : X i,
    Finite (RelativeClass E.val F.val a) → relativeIndex E.val F.val a = 2
  finite_index_power_two : ∀ (E F : ColourEq S i), E ≤ F → ∀ a : X i,
    Finite (RelativeClass E.val F.val a) →
      ∃ k : Nat, relativeIndex E.val F.val a = 2 ^ k

/-- C18: the local SIR-facing corollary explicitly applies the upstream
provider. In particular neither endpoint must be exact. -/
theorem full_relative_Hasse_corollary (P : FullRelativeHasseProvider S i)
    (E F : ColourEq S i) (a : X i) (hfin : Finite (RelativeClass E.val F.val a)) :
    (E ⋖ F → relativeIndex E.val F.val a = 2) ∧
      (E ≤ F → ∃ k : Nat, relativeIndex E.val F.val a = 2 ^ k) :=
  ⟨fun h => P.cover_index_two E F h a hfin,
   fun h => P.finite_index_power_two E F h a hfin⟩

/-- The actual global quotient map induced by E ≤ F. -/
def coarseningQuotientMap {A : Type v} (E F : Setoid A) (hEF : E ≤ F) :
    Quotient E → Quotient F :=
  Quotient.map id (fun _ _ h => hEF h)

theorem coarseningQuotientMap_surjective {A : Type v}
    (E F : Setoid A) (hEF : E ≤ F) :
    Function.Surjective (coarseningQuotientMap E F hEF) := by
  intro q
  induction q using Quotient.inductionOn with | _ x =>
    exact ⟨Quotient.mk E x, rfl⟩

/-- Every coarsening of a finite-global-index equivalence still has
finite global index. This is an actual quotient argument. -/
theorem finite_quotient_of_le {A : Type v} (E F : Setoid A) (hEF : E ≤ F)
    [Finite (Quotient E)] : Finite (Quotient F) :=
  Finite.of_surjective _ (coarseningQuotientMap_surjective E F hEF)

/-- Cardinal two supplies two representatives covering every actual class. -/
theorem two_class_representatives {A : Type v} (E : Setoid A)
    (hcard : Nat.card (Quotient E) = 2) :
    ∃ a₀ a₁ : A, ¬ E a₀ a₁ ∧ ∀ x, E x a₀ ∨ E x a₁ := by
  obtain ⟨q₀, q₁, hne, hcover⟩ := Nat.card_eq_two_iff.mp hcard
  obtain ⟨a₀, rfl⟩ := Quotient.exists_rep q₀
  obtain ⟨a₁, rfl⟩ := Quotient.exists_rep q₁
  refine ⟨a₀, a₁, (fun h => hne (Quotient.sound h)), ?_⟩
  intro x
  have hx : Quotient.mk E x ∈ ({Quotient.mk E a₀, Quotient.mk E a₁} : Set (Quotient E)) := by
    rw [hcover]
    trivial
  rcases hx with hx | hx
  · exact Or.inl (Quotient.exact hx)
  · exact Or.inr (Quotient.exact hx)

section OriginalSource

variable {G : Type*} [Group G] [∀ j : ι, MulAction G (X j)]

/-- C19 on the full original equivalence poset. The last cover is obtained
in the full finite interval and is a finite old-language disjunction.
Its index-two conclusion then feeds the actual pointwise obstruction. -/
theorem finite_global_obstruction_of_provider
    (H : HomogeneousSource S G) (P : FullRelativeHasseProvider S i)
    (E : ColourEq S i) (hE : E < ⊤) [Finite (Quotient E.val)]
    (I : Finset (X i) → Finset (X i) → Finset (X i) → Prop) :
    ¬ EmptyBaseSingletonAxioms (G := G) I := by
  obtain ⟨F, hEF, hF, _φ, _hφ⟩ := last_cover_original_definable S i hE
  letI : Finite (Quotient F.val) := finite_quotient_of_le E.val F.val hEF
  obtain ⟨a⟩ := S.nonemptySort i
  have htwo : Nat.card (Quotient F.val) = 2 := by
    have h := P.cover_index_two F ⊤ hF a
      (inferInstance : Finite (RelativeClass F.val (⊤ : ColourEq S i).val a))
    exact (relativeIndex_top F.val a).symm.trans h
  obtain ⟨a₀, a₁, hne, hclasses⟩ := two_class_representatives F.val htwo
  have hInv : ∀ (g : G) x y, F x y → F (g • x) (g • y) :=
    (invariant_iff_colourInvariant S i H F).mpr F.2
  exact original_two_class_obstruction S H F.val hInv a₀ a₁ hne hclasses I

/-- Every actual group-invariant equivalence is admitted. This source-facing
statement has the original finite-global hypothesis and no endpoint
exactness or new sheet names. The Hasse provider remains an explicit input. -/
theorem original_finite_global_obstruction_of_provider
    (H : HomogeneousSource S G) (P : FullRelativeHasseProvider S i)
    (E : Setoid (X i))
    (hInv : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (hE : E < ⊤) [Finite (Quotient E)]
    (I : Finset (X i) → Finset (X i) → Finset (X i) → Prop) :
    ¬ EmptyBaseSingletonAxioms (G := G) I := by
  let E' : ColourEq S i := ⟨E, (invariant_iff_colourInvariant S i H E).mp hInv⟩
  have hE' : E' < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro heq
    exact hE.ne (congrArg Subtype.val heq)
  exact finite_global_obstruction_of_provider S i H P E' hE' I

end OriginalSource

end CCO.SIR.Negative
