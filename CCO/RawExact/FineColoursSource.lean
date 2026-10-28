import CCO.RawExact.ExactCalculusSource
import CCO.RawExact.FineColours
import CCO.RawExact.AtomicExact
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.OfFn

/-!
# Finite fine-colour reconstruction from original source CCO

Finite exact equivalences have a nonempty exact meet because their
common diagonal remains. Source C10 therefore supplies the precise
meet-distribution equation needed by the same-sort symmetric algebra.
This discharges that provider, including the genuine identity atom.
-/

universe u v w z q

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]
variable (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

/-- Every same-sort optional original atom, including `none`, has
an actual nonempty exact presentation. -/
theorem optional_original_atom_exact {i : ι} (a : Option (S.Atom i i)) :
    ∃ A : NonemptyExact S i i, evaluate S A.words = S.rawAtomRel a := by
  cases a with
  | none => exact ⟨exactIdentityAtom S i, exactIdentityAtom_is_optional_none S i⟩
  | some a => exact ⟨exactDiversityAtom S a, exactDiversityAtom_relation S a⟩

include H cco

/-- C15: the meet of the projected atomic saturations is exactly
the saturation by the finite meet of the actual exact equivalences. -/
theorem fine_colour_reconstruction_of_CCO
    {i : ι} {I : Type z} [Finite I]
    (E : I → NonemptyExact S i i)
    (hE : ∀ t, RawSymmetric.EquivRel (evaluate S (E t).words))
    (a : Option (S.Atom i i)) :
    (fun x y => ∀ t, saturate (evaluate S (E t).words)
      (S.rawAtomRel a) (evaluate S (E t).words) x y) =
      saturate (familyMeet (fun t => evaluate S (E t).words))
        (S.rawAtomRel a) (familyMeet (fun t => evaluate S (E t).words)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let e := Fintype.equivFin I
  let L : List (NonemptyExact S i i) := List.ofFn (fun k => E (e.symm k))
  have hForall : ∀ P : NonemptyExact S i i → Prop,
      (∀ d, d ∈ L → P d) ↔ ∀ t, P (E t) := by
    intro P
    constructor
    · intro h t
      apply h (E t)
      exact List.mem_ofFn.mpr ⟨e t, by simp only [Equiv.symm_apply_apply]⟩
    · intro h d hd
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hd
      exact h (e.symm k)
  have hFamily :
      (fun x y => ∀ d, d ∈ L → evaluate S d.words x y) =
        familyMeet (fun t => evaluate S (E t).words) := by
    funext x y
    exact propext (hForall (fun d => evaluate S d.words x y))
  obtain ⟨x⟩ := S.nonemptySort i
  have hMeet : TRel.Nonempty (fun x y => ∀ d, d ∈ L → evaluate S d.words x y) :=
    ⟨x, x, (hForall (fun d => evaluate S d.words x x)).mpr (fun t => (hE t).refl x)⟩
  obtain ⟨A, hA⟩ := optional_original_atom_exact S a
  have hDist :
      RawSymmetric.compose (familyMeet (fun t => evaluate S (E t).words)) (S.rawAtomRel a) =
        (fun x y => ∀ t, RawSymmetric.compose (evaluate S (E t).words) (S.rawAtomRel a) x y) := by
    have hList := comp_exact_meet_left_of_CCO S H cco L hMeet A
    rw [hFamily, hA] at hList
    exact hList.trans (by
      funext x y
      exact propext (hForall (fun d => TRel.comp (evaluate S d.words) (S.rawAtomRel a) x y)))
  exact finite_fine_colour_from_distribution
    (fun t => evaluate S (E t).words) (S.rawAtomRel a) hE
    (fun t => presentation_invariant_of_homogeneous S H (E t).words)
    (S.rawAtomRel_invariant a (S.colourInvariant_of_homogeneous H))
    (S.pair_flip_of_homogeneous H) hDist

/-- Actual C15 quotient-colour reconstruction. Equality of all projected
pair orbitals determines the pair orbital on the common finer quotient.
No assertion realizes arbitrary tuples of quotient classes. -/
theorem actual_fine_pair_orbit_of_CCO
    {i : ι} {I : Type z} [Finite I]
    (E : I → NonemptyExact S i i)
    (Q : I → Type q) [∀ t, MulAction G (Q t)]
    {K : Type*} [MulAction G K]
    (π : ∀ t, X i → Q t) (κ : X i → K)
    (equivπ : ∀ t (g : G) x, π t (g • x) = g • π t x)
    (equivκ : ∀ (g : G) x, κ (g • x) = g • κ x)
    (hπ : ∀ t, GroupActions.kernel (π t) = evaluate S (E t).words)
    (hκ : GroupActions.kernel κ = familyMeet (fun t => evaluate S (E t).words))
    (a b x y : X i) :
    (∀ t, GroupActions.orbital (G := G) (π t a) (π t b) (π t x) (π t y)) ↔
      GroupActions.orbital (G := G) (κ a) (κ b) (κ x) (κ y) := by
  have hEquiv : ∀ t, RawSymmetric.EquivRel (evaluate S (E t).words) := by
    intro t
    rw [← hπ t]
    exact kernel_equiv (π t)
  have hSat := fine_colour_reconstruction_of_CCO S H cco E hEquiv (S.colour a b)
  have hProjected : ∀ t, GroupActions.pullback (π t) (π t)
      (GroupActions.orbital (G := G) (π t a) (π t b)) =
        saturate (evaluate S (E t).words) (S.rawAtomRel (S.colour a b))
          (evaluate S (E t).words) := by
    intro t
    have h := equivariant_orbit_pullback (π t) (π t) (equivπ t) (equivπ t) a b
    rw [hπ t, actual_pair_orbital_of_homogeneous S H a b] at h
    exact h
  have hFine := equivariant_orbit_pullback κ κ equivκ equivκ a b
  rw [hκ, actual_pair_orbital_of_homogeneous S H a b] at hFine
  change (∀ t, GroupActions.pullback (π t) (π t)
      (GroupActions.orbital (G := G) (π t a) (π t b)) x y) ↔
    GroupActions.pullback κ κ (GroupActions.orbital (G := G) (κ a) (κ b)) x y
  rw [hFine]
  have hAt := congrArg (fun R : X i → X i → Prop => R x y) hSat
  constructor
  · intro h
    apply (Iff.of_eq hAt).mp
    intro t
    rw [← hProjected t]
    exact h t
  · intro h t
    rw [hProjected t]
    exact (Iff.of_eq hAt).mpr h t

end CCO.RawExact
