import CCO.RelationalCompletion.Relational.Profiles
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Set.Card

/-! C31, C32 and C35: actual scope boundaries for collision unfolding. -/
namespace CCO.RelationalCompletion.Relational
namespace Boundaries

open Structure

universe u v

def emptyStructure (L : Language.{u}) (V : Type v) : Structure L V where
  rel _ _ := False

/-- In an edgeless relational source every irreducible piece has at most one point. -/
theorem empty_irreducible_subsingleton {L : Language.{u}} {V : Type v} (S : Set V)
    (hirr : ((emptyStructure L V).induce S).Irreducible) :
    ∀ x ∈ S, ∀ y ∈ S, x = y := by
  classical
  intro x hx y hy
  let a : S := ⟨x, hx⟩
  have hsplit : ((emptyStructure L V).induce S).FreeSplit {a} ({a}ᶜ) := by
    refine ⟨Set.union_compl_self _, ?_⟩
    intro n R xs hr
    exact False.elim hr
  rcases hirr {a} ({a}ᶜ) hsplit with hleft | hright
  · have hm : (⟨y, hy⟩ : S) ∈ ({a} : Set S) := by rw [hleft]; trivial
    exact (congrArg Subtype.val (Set.mem_singleton_iff.mp hm)).symm
  · have hm : a ∈ ({a}ᶜ : Set S) := by rw [hright]; trivial
    exact False.elim (hm (Set.mem_singleton a))

inductive EdgeRel : ℕ → Type
  | edge : EdgeRel 2

def edgeLanguage : Language := ⟨EdgeRel⟩

def graphStructure {V : Type v} (E : V → V → Prop) : Structure edgeLanguage V where
  rel R xs := match R with | .edge => E (xs 0) (xs 1)

/-- The same map of two isolated source points is a HE in every loop-free
graph target. This includes the random-graph instance without requiring its
construction for this local diagnostic. -/
theorem isolated_isHE {W : Type v} (E : W → W → Prop) (hirr : ∀ z, ¬ E z z)
    (f : Bool → W) (hinj : Function.Injective f) :
    (emptyStructure edgeLanguage Bool).IsHE (graphStructure E) f := by
  refine ⟨fun _ _ hr => False.elim hr, ?_⟩
  intro S hS
  refine ⟨fun _ _ _ _ he => hinj he, ?_⟩
  intro n R xs hxs
  cases R
  have he := empty_irreducible_subsingleton S hS (xs 0) (hxs 0) (xs 1) (hxs 1)
  change E (f (xs 0)) (f (xs 1)) ↔ False
  rw [he]
  exact ⟨fun hh => hirr _ hh, False.elim⟩

/-- C31: a displayed target edge prevents reflection for this injective HE. -/
theorem isolated_not_embedding {W : Type v} (E : W → W → Prop) (f : Bool → W)
    (hedge : E (f false) (f true)) :
    ¬ (∀ {n} (R : edgeLanguage.Rel n) xs,
      (graphStructure E).rel R (f ∘ xs) ↔ (emptyStructure edgeLanguage Bool).rel R xs) := by
  intro he
  exact (he .edge (fun i => if i = 0 then false else true)).mp hedge

/-- A fully concrete two-point instance of C31. -/
theorem two_isolated_into_edge :
    Function.Injective (id : Bool → Bool) ∧
      (emptyStructure edgeLanguage Bool).IsHE (graphStructure (fun a b : Bool => a ≠ b)) id ∧
      ¬ (∀ {n} (R : edgeLanguage.Rel n) xs,
        (graphStructure (fun a b : Bool => a ≠ b)).rel R (id ∘ xs) ↔
          (emptyStructure edgeLanguage Bool).rel R xs) := by
  exact ⟨Function.injective_id, isolated_isHE _ (fun _ he => he rfl) id
    Function.injective_id, isolated_not_embedding _ _ (by decide)⟩

def pureLanguage : Language where
  Rel _ := Empty

def pureNat : Structure pureLanguage ℕ := emptyStructure pureLanguage ℕ

def collapsed : Bool → ℕ := fun _ => 0

def separated : Bool → ℕ := fun b => if b then 1 else 0

theorem separated_injective : Function.Injective separated := by
  intro x y he
  cases x <;> cases y <;> simp_all [separated]

theorem collapsed_isHE : (emptyStructure pureLanguage Bool).IsHE pureNat collapsed := by
  refine ⟨?_, ?_⟩
  · intro n R
    exact nomatch R
  · intro S hS
    refine ⟨fun x hx y hy _ => empty_irreducible_subsingleton S hS x hx y hy, ?_⟩
    intro n R
    exact nomatch R

theorem separate_singleton_image_type (b : Bool) :
    pureNat.SameImageType collapsed separated {b} := by
  intro n R
  exact nomatch R

/-- C32: the actual separately protected induced target images are isomorphic. -/
noncomputable def separate_singleton_image_iso (b : Bool) :
    Iso (pureNat.induce (collapsed '' ({b} : Set Bool)))
      (pureNat.induce (separated '' ({b} : Set Bool))) :=
  Structure.SameImageType.imageIso (separate_singleton_image_type b)
    (Set.injOn_singleton _ _) separated_injective.injOn

theorem collapsed_joint_image : Set.range collapsed = ({0} : Set ℕ) := by
  ext n
  simp [collapsed]

theorem separated_joint_image : Set.range separated = ({0, 1} : Set ℕ) := by
  ext n
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, rfl⟩
    cases b <;> simp [separated]
  · rintro (rfl | rfl)
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

theorem joint_image_card_changes :
    (Set.range collapsed).ncard = 1 ∧ (Set.range separated).ncard = 2 := by
  rw [collapsed_joint_image, separated_joint_image]
  simp

/-- The two joint induced images are not isomorphic, despite all separately
protected singleton images being isomorphic. -/
theorem joint_images_not_isomorphic :
    ¬ Nonempty (Iso (pureNat.induce (Set.range collapsed))
      (pureNat.induce (Set.range separated))) := by
  rintro ⟨e⟩
  let a : Set.range separated := ⟨0, ⟨false, rfl⟩⟩
  let b : Set.range separated := ⟨1, ⟨true, rfl⟩⟩
  have hsmall : ∀ x y : Set.range collapsed, x = y := by
    rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    rfl
  have he : a = b := e.point.symm.injective (hsmall _ _)
  exact Nat.zero_ne_one (congrArg Subtype.val he)

/-- Literal preservation of both old positions would retain the collision. -/
theorem cannot_fix_all_old_positions (f : Bool → ℕ) (hinj : Function.Injective f) :
    ¬ (∀ b, f b = collapsed b) := by
  intro h
  have he : false = true := hinj ((h false).trans (h true).symm)
  exact Bool.false_ne_true he

/-- C35 is a failure of the deletion step for functions, not a counterexample
to independent functional injectivization results. -/
theorem functional_deletion_not_closed :
    ¬ (∀ x ∈ ({false} : Set Bool), (fun _ : Bool => true) x ∈ ({false} : Set Bool)) := by
  intro h
  have he := h false (Set.mem_singleton false)
  exact Bool.false_ne_true (Set.mem_singleton_iff.mp he).symm

end Boundaries
end CCO.RelationalCompletion.Relational
