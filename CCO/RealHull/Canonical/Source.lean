import CCO.RealHull.Canonical.Hull
import CCO.RealHull.Geometry.Boundaries

/-! Actual old-point source consumers. The nonparameter one-point type is
read literally from the source; the parameter case uses TRUE equality only.
The empty base gives the whole source and is treated separately. -/
universe v w t
namespace CCO.RealHull.Canonical
open Geometry ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]

noncomputable def actualSpokes (A : Finset M) (x : M) (hx : x ∉ A) : ↥A → Atom S :=
  fun a => (col_some_of_ne S (x := x) (y := a.val) (fun he => hx (he.symm ▸ a.property))).choose

theorem actualSpokes_colour (A : Finset M) (x : M) (hx : x ∉ A) (a : ↥A) :
    col S x a.val = some (actualSpokes S A x hx a) :=
  (col_some_of_ne S (x := x) (y := a.val) (fun he => hx (he.symm ▸ a.property))).choose_spec

def actualFibrePoint (A : Finset M) (x : M) (hx : x ∉ A) :
    FibreSet S A (actualSpokes S A x hx) := ⟨x,actualSpokes_colour S A x hx⟩

noncomputable def actualHull (A : Finset M) (x : M) : Set M :=
  if hx : x ∈ A then {x} else canonicalHull S A (actualSpokes S A x hx)

@[simp] theorem actualHull_parameter (A : Finset M) (x : M) (hx : x ∈ A) :
    actualHull S A x = {x} := by simp [actualHull,hx]

/-- C35: when x is an actual parameter the hull is literally the equality
singleton; no diversity Gamma is evaluated at an identity colour. -/
theorem actualHull_parameter_singleton (A : Finset M) (x : M) (hx : x ∈ A) :
    Finite (actualHull S A x) ∧ Nat.card (actualHull S A x) = 1 := by
  rw [actualHull_parameter S A x hx]
  exact ⟨inferInstance,Nat.card_unique⟩

theorem canonicalHull_empty (q : ↥(∅ : Finset M) → Atom S) :
    canonicalHull S ∅ q = Set.univ := by
  ext y
  constructor
  · intro _; trivial
  · intro _ a
    exact isEmptyElim a

theorem canonicalSupport_empty (q : ↥(∅ : Finset M) → Atom S) :
    (canonicalSupport S ∅ q).val = Set.univ := by
  ext r
  constructor
  · intro _; trivial
  · intro _ a
    exact isEmptyElim a

variable {G : Type t} [Group G] [MulAction G M]

/-- C35: finite empty-base source is loop-free by the SAME actual anchored
clique argument. Only afterward does finite triangle Ramsey give its bound. -/
theorem finite_empty_source_package (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) [Finite M] :
    (∀ r : Atom S, ¬ Looped S r) ∧ Nat.card M < sourceTriangleRamsey S ∧
      ∃ n : ℕ, Nat.card M = 2^n ∧ n ≤ Nat.card (Atom S) := by
  classical
  let q : ↥(∅ : Finset M) → Atom S := fun a => isEmptyElim a
  letI : Nonempty (FibreSet S ∅ q) := by
    obtain ⟨x⟩ := S.nonemptySort ()
    exact ⟨x,fun a => isEmptyElim a⟩
  letI : Finite (FibreSet S ∅ q) := Finite.of_injective Subtype.val Subtype.val_injective
  have hl : ∀ r : Atom S, ¬ Looped S r := fun r =>
    finite_fibre_excludes_looped S ∅ q H cco r (fun a => isEmptyElim a)
  exact ⟨hl,(finite_source_of_no_looped S hl).2,finite_sort_size_power_two S () H cco
    (Classical.choice (S.nonemptySort ()))⟩

/-- Actual stabilizer algebraicity supplies the FINITE literal fibre, rather
than an assumed finite abstract replacement or a vacuous Nat.card statement. -/
theorem actual_algebraic_hull (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,0,w} S) (A : Finset M) (x : M) (hx : x ∉ A)
    (halg : {y : M | ∃ g : G, (∀ a ∈ A, g • a = a) ∧ g • x = y}.Finite) :
    Finite (actualHull S A x) ∧
      Nat.card (actualHull S A x) < sourceTriangleRamsey S ∧
      (∃ n : ℕ, Nat.card (actualHull S A x) = 2^n ∧
        n ≤ Nat.card (canonicalSupport S A (actualSpokes S A x hx)).val ∧
        2^n ≤ 2^(Nat.card (canonicalSupport S A (actualSpokes S A x hx)).val) ∧
        2^(Nat.card (canonicalSupport S A (actualSpokes S A x hx)).val) ≤ 2^(Nat.card (Atom S))) ∧
      {y : M | ∃ g : G, (∀ a ∈ A, g • a = a) ∧ g • x = y} ⊆ actualHull S A x := by
  let q := actualSpokes S A x hx
  let xp : FibreSet S A q := actualFibrePoint S A x hx
  letI : Nonempty (FibreSet S A q) := ⟨xp⟩
  have horbit : {y : M | ∃ g : G, (∀ a ∈ A, g • a = a) ∧ g • x = y} = FibreSet S A q :=
    fibre_orbit_eq S A q H xp
  have hfin : (FibreSet S A q).Finite := horbit ▸ halg
  letI : Finite (FibreSet S A q) := hfin.to_subtype
  have hhull : actualHull S A x = canonicalHull S A q := by simp only [actualHull,dif_neg hx,q]
  rw [hhull]
  exact ⟨(canonical_hull_finite_bound S A q H cco xp).1,
    (canonical_hull_finite_bound S A q H cco xp).2,
    canonical_hull_two_power S A q H cco xp,horbit ▸ fibre_subset_canonicalHull S A q⟩

/-- Converse: the actual stabilizer orbit sits inside its canonical hull, so
finiteness of that hull implies the original real algebraicity condition. -/
theorem finite_hull_implies_finite_orbit (H : HomogeneousSource S G)
    (A : Finset M) (x : M) (hx : x ∉ A) (hfin : (actualHull S A x).Finite) :
    {y : M | ∃ g : G, (∀ a ∈ A, g • a = a) ∧ g • x = y}.Finite := by
  have hhull : actualHull S A x = canonicalHull S A (actualSpokes S A x hx) := by
    simp only [actualHull,dif_neg hx]
  rw [hhull] at hfin
  apply hfin.subset
  have horbit : {y : M | ∃ g : G, (∀ a ∈ A, g • a = a) ∧ g • x = y} =
      FibreSet S A (actualSpokes S A x hx) :=
    fibre_orbit_eq S A (actualSpokes S A x hx) H (actualFibrePoint S A x hx)
  rw [horbit]
  exact fibre_subset_canonicalHull S A _
end CCO.RealHull.Canonical
