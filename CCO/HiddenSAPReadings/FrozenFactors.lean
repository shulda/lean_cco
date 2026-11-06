import CCO.PairHomogeneity
import CCO.HiddenSAPReadings.SourceSupport
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# The SEPARATE finite-arity frozen-factor interface

This file is the conditional A08 addendum. Its original-group clone
interface preserves the actual complete tuple language, including sort
and equality patterns. The binary source theorem does not supply it.
Every clone fixes the complement of ONE ACTUAL collided old point and
the prechosen actual anchors. Other formal positions still at that point
are unchanged positions, rather than invented distinct base elements.

The finite induction is proved here. It terminates with injective old
real assignments and preserves every designated OLD source factor.
Neither tuple completion nor the stronger clone interface is inferred
from binary anchor readout, binary SAP, or a completed hidden provider.
-/

universe u v w r z
namespace CCO.HiddenSAPReadings.FrozenFactors
noncomputable section

variable {ι : Type u} {X : ι → Type v}

/-- Actual canonical tuple types up to the stated maximum arity. Every
named old relation is decoded from its complete type; actual sort and
equality patterns are retained explicitly. These are A08 DATA. -/
structure CanonicalTupleFamily (X : ι → Type v) (N : ℕ) where
  Name : Fin (N + 1) → Type w
  finiteName : ∀ n, Finite (Name n)
  typeOf : ∀ n, (Fin n.val → Sigma X) → Name n
  sortPattern : ∀ n, Name n → Fin n.val → ι
  sort_correct : ∀ n xs j, sortPattern n (typeOf n xs) j = (xs j).1
  equalityPattern : ∀ n, Name n → Fin n.val → Fin n.val → Prop
  equality_correct : ∀ n xs j k,
    equalityPattern n (typeOf n xs) j k ↔ xs j = xs k
  Relation : Fin (N + 1) → Type w
  finiteRelation : ∀ n, Finite (Relation n)
  relation : ∀ n, Relation n → (Fin n.val → Sigma X) → Prop
  decode : ∀ n, Relation n → Name n → Prop
  relation_correct : ∀ n R xs, relation n R xs ↔ decode n R (typeOf n xs)

variable {I : Type z} {N : ℕ}

/-- The actual FULL type on each designated old factor, for all tuples
through maximum arity. This includes missing as well as positive data. -/
def SameFactors (K : CanonicalTupleFamily X N) (factors : Set (Set I))
    (f g : I → Sigma X) : Prop :=
  ∀ D ∈ factors, ∀ n (xs : Fin n.val → I), (∀ j, xs j ∈ D) →
    K.typeOf n (g ∘ xs) = K.typeOf n (f ∘ xs)

def FactorInjective (factors : Set (Set I)) (f : I → Sigma X) : Prop :=
  ∀ D ∈ factors, Set.InjOn f D

namespace SameFactors
variable {K : CanonicalTupleFamily X N} {factors : Set (Set I)}
variable {f g h : I → Sigma X}

theorem refl (f : I → Sigma X) : SameFactors K factors f f :=
  fun _ _ _ _ _ => rfl

theorem trans (hfg : SameFactors K factors f g) (hgh : SameFactors K factors g h) :
    SameFactors K factors f h := by
  intro D hD n xs hxs
  exact (hgh D hD n xs hxs).trans (hfg D hD n xs hxs)

/-- The encoded equality pattern transports genuine source-factor
injectivity. It is not an independent stronger step premise. -/
theorem factor_injective (hN : 2 ≤ N) (hfg : SameFactors K factors f g)
    (hf : FactorInjective factors f) : FactorInjective factors g := by
  intro D hD x hx y hy hxy
  let n : Fin (N + 1) := ⟨2,by omega⟩
  let xs : Fin n.val → I := ![x,y]
  have hxs : ∀ j, xs j ∈ D := by intro j; fin_cases j; exact hx; exact hy
  have hcode := hfg D hD n xs hxs
  have hpattern : K.equalityPattern n (K.typeOf n (g ∘ xs)) 0 1 :=
    (K.equality_correct n (g ∘ xs) 0 1).mpr hxy
  rw [hcode] at hpattern
  exact hf D hD hx hy ((K.equality_correct n (f ∘ xs) 0 1).mp hpattern)

/-- Every old higher-support relation decoded from the complete type
is preserved AND reflected on every designated actual old factor. -/
theorem relation_iff (hfg : SameFactors K factors f g)
    (D : Set I) (hD : D ∈ factors) (n) (R : K.Relation n)
    (xs : Fin n.val → I) (hxs : ∀ j, xs j ∈ D) :
    K.relation n R (g ∘ xs) ↔ K.relation n R (f ∘ xs) := by
  rw [K.relation_correct,K.relation_correct,hfg D hD n xs hxs]

end SameFactors

variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]

/-- ONE actual original-group clone, over the complete base omitting
the actual point f u. Equal formal images are not extra base points. -/
structure OriginalClone (anchors : Set (Sigma X)) (f : I → Sigma X) (u : I) where
  motion : G
  fixes_complement : ∀ p ∈ Set.range f, p ≠ f u → motion • p = p
  fixes_anchors : ∀ a ∈ anchors, motion • a = a
  fresh : motion • f u ∉ anchors ∪ Set.range f

def OriginalClone.assignment {anchors : Set (Sigma X)} {f : I → Sigma X} {u : I}
    (c : OriginalClone (G := G) anchors f u) (i : I) : Sigma X := by
  classical
  exact if i = u then c.motion • f u else f i

theorem OriginalClone.at_moved {anchors : Set (Sigma X)} {f : I → Sigma X} {u : I}
    (c : OriginalClone (G := G) anchors f u) : c.assignment u = c.motion • f u := by
  classical
  simp [OriginalClone.assignment]

theorem OriginalClone.at_other {anchors : Set (Sigma X)} {f : I → Sigma X} {u : I}
    (c : OriginalClone (G := G) anchors f u) {i : I} (hi : i ≠ u) :
    c.assignment i = f i := by
  classical
  simp [OriginalClone.assignment,hi]

/-- A08 contains both the actual higher-language automorphism property
and the separately supplied original SAP/frozen-factor clone interface.
No binary theorem is asserted to construct these fields. -/
structure FrozenFactorSAPInterface (K : CanonicalTupleFamily X N)
    (sort : I → ι) (factors : Set (Set I)) (anchors : Set (Sigma X)) : Prop where
  finite_anchors : anchors.Finite
  tuple_invariant : ∀ (g : G) n (xs : Fin n.val → Sigma X),
    K.typeOf n (fun j => g • xs j) = K.typeOf n xs
  clone : ∀ (f : I → Sigma X), (∀ i, (f i).1 = sort i) →
    (∀ i, f i ∉ anchors) → FactorInjective factors f →
    ∀ u v, u ≠ v → f u = f v → Nonempty (OriginalClone (G := G) anchors f u)

variable {K : CanonicalTupleFamily X N} {sort : I → ι}
variable {factors : Set (Set I)} {anchors : Set (Sigma X)}

/-- A clone's effect on a factor is either literal identity, or the
SAME original automorphism on the entire factor. Factor injectivity
ensures only its actual moved position maps to the collided point. -/
theorem clone_preserves_factors
    (J : FrozenFactorSAPInterface (G := G) K sort factors anchors)
    {f : I → Sigma X} (hf : FactorInjective factors f) {u : I}
    (c : OriginalClone (G := G) anchors f u) :
    SameFactors K factors f c.assignment := by
  classical
  intro D hD n xs hxs
  by_cases hu : u ∈ D
  · have he : c.assignment ∘ xs = fun j => c.motion • f (xs j) := by
      funext j
      by_cases hj : xs j = u
      · rw [Function.comp_apply,hj,c.at_moved]
      · rw [Function.comp_apply,c.at_other hj]
        exact (c.fixes_complement (f (xs j)) ⟨xs j,rfl⟩
          (fun h => hj (hf D hD (hxs j) hu h))).symm
    rw [he]
    exact J.tuple_invariant c.motion n (f ∘ xs)
  · have he : c.assignment ∘ xs = f ∘ xs := by
      funext j
      exact c.at_other (fun h => hu (h ▸ hxs j))
    rw [he]

def CloneStep (anchors : Set (Sigma X)) (f g : I → Sigma X) : Prop :=
  ∃ u v, u ≠ v ∧ f u = f v ∧
    ∃ c : OriginalClone (G := G) anchors f u, g = c.assignment

private theorem process_finset [Fintype I]
    (hN : 2 ≤ N) (J : FrozenFactorSAPInterface (G := G) K sort factors anchors)
    (f₀ : I → Sigma X) (hTyped : ∀ i, (f₀ i).1 = sort i)
    (hAvoid : ∀ i, f₀ i ∉ anchors) (hFactors : FactorInjective factors f₀)
    (processed : Finset I) :
    ∃ f : I → Sigma X,
      (∀ i, (f i).1 = sort i) ∧ (∀ i, f i ∉ anchors) ∧
      SameFactors K factors f₀ f ∧
      Relation.ReflTransGen (CloneStep (G := G) anchors) f₀ f ∧
      ∀ u ∈ processed, ∀ v, u ≠ v → f u ≠ f v := by
  classical
  induction processed using Finset.induction_on with
  | empty => exact ⟨f₀,hTyped,hAvoid,SameFactors.refl f₀,.refl,by simp⟩
  | @insert u processed hunot ih =>
    obtain ⟨f,hTyped',hAvoid',hType,hHistory,hDone⟩ := ih
    by_cases hUnique : ∀ v, u ≠ v → f u ≠ f v
    · refine ⟨f,hTyped',hAvoid',hType,hHistory,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hUnique
      · exact hDone x hx
    · push Not at hUnique
      obtain ⟨v,huv,hCollision⟩ := hUnique
      have hf : FactorInjective factors f := hType.factor_injective hN hFactors
      obtain ⟨c⟩ := J.clone f hTyped' hAvoid' hf u v huv hCollision
      let g := c.assignment
      have hNew : g u ∉ anchors ∪ Set.range f := by
        change c.assignment u ∉ anchors ∪ Set.range f
        rw [c.at_moved]
        exact c.fresh
      have hTypedG : ∀ i, (g i).1 = sort i := by
        intro i
        by_cases hi : i = u
        · subst i
          change (c.assignment u).1 = sort u
          rw [c.at_moved]
          exact hTyped' u
        · change (c.assignment i).1 = sort i
          rw [c.at_other hi]
          exact hTyped' i
      have hAvoidG : ∀ i, g i ∉ anchors := by
        intro i
        by_cases hi : i = u
        · subst i
          exact fun h => hNew (Or.inl h)
        · change c.assignment i ∉ anchors
          rw [c.at_other hi]
          exact hAvoid' i
      refine ⟨g,hTypedG,hAvoidG,hType.trans (clone_preserves_factors J hf c),
        hHistory.tail ⟨u,v,huv,hCollision,c,rfl⟩,?_⟩
      intro x hx y hxy hEq
      rcases Finset.mem_insert.mp hx with hxu | hx
      · subst x
        have hyu : y ≠ u := Ne.symm hxy
        exact hNew (Or.inr ⟨y,(c.at_other hyu).symm.trans hEq.symm⟩)
      · have hxu : x ≠ u := fun h => hunot (h ▸ hx)
        by_cases hyu : y = u
        · subst y
          exact hNew (Or.inr ⟨x,(c.at_other hxu).symm.trans hEq⟩)
        · have he : f x = f y := (c.at_other hxu).symm.trans
            (hEq.trans (c.at_other hyu))
          exact hDone x hx y hxy he

/-- C33/C65, explicitly CONDITIONAL on separate A08. The actual finite
sequence of one-collided-point moves ends injective and preserves the
FULL old factor types. Fixed anchors remain the same literal old points. -/
theorem finite_frozen_factor_splitting [Finite I]
    (hN : 2 ≤ N) (J : FrozenFactorSAPInterface (G := G) K sort factors anchors)
    (old : I → Sigma X) (hTyped : ∀ i, (old i).1 = sort i)
    (hAvoid : ∀ i, old i ∉ anchors) (hFactors : FactorInjective factors old) :
    ∃ fresh : I → Sigma X,
      (∀ i, (fresh i).1 = sort i) ∧ Function.Injective fresh ∧
      (∀ i, fresh i ∉ anchors) ∧ SameFactors K factors old fresh ∧
      Relation.ReflTransGen (CloneStep (G := G) anchors) old fresh := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨f,hTyped',hAvoid',hType,hHistory,hDone⟩ :=
    process_finset hN J old hTyped hAvoid hFactors Finset.univ
  refine ⟨f,hTyped',?_,hAvoid',hType,hHistory⟩
  intro u v h
  by_contra huv
  exact hDone u (Finset.mem_univ u) v huv h

/-- The final visible extension is the actual finite induced old set
containing the original visible target, the original real images, the
fixed anchors and all clones. No arbitrary completion is asserted. -/
theorem finite_frozen_factor_visible_extension [Finite I]
    (hN : 2 ≤ N) (J : FrozenFactorSAPInterface (G := G) K sort factors anchors)
    (old : I → Sigma X) (hTyped : ∀ i, (old i).1 = sort i)
    (hAvoid : ∀ i, old i ∉ anchors) (hFactors : FactorInjective factors old)
    (visible : Set (Sigma X)) (hVisible : visible.Finite) :
    ∃ (fresh : I → Sigma X) (extension : Set (Sigma X)),
      extension.Finite ∧ visible ⊆ extension ∧ anchors ⊆ extension ∧
      Set.range old ⊆ extension ∧ Set.range fresh ⊆ extension ∧
      (∀ i, (fresh i).1 = sort i) ∧ Function.Injective fresh ∧
      (∀ i, fresh i ∉ anchors) ∧ SameFactors K factors old fresh ∧
      Relation.ReflTransGen (CloneStep (G := G) anchors) old fresh := by
  obtain ⟨fresh,hTyped',hInj,hAvoid',hType,hHistory⟩ :=
    finite_frozen_factor_splitting hN J old hTyped hAvoid hFactors
  let extension := (visible ∪ anchors) ∪ (Set.range old ∪ Set.range fresh)
  refine ⟨fresh,extension,(hVisible.union J.finite_anchors).union
    ((Set.finite_range _).union (Set.finite_range _)),
    fun _ h => Or.inl (Or.inl h),fun _ h => Or.inl (Or.inr h),
    fun _ h => Or.inr (Or.inl h),fun _ h => Or.inr (Or.inr h),
    hTyped',hInj,hAvoid',hType,hHistory⟩

section ActualSource
open CCO.ParityHasse.Original CCO.TypedOrbitFrames CCO.UnaryTermsReturn
variable (S : AtomicSource.{u,v,w} ι X)
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (hCover : ∀ i : ι, OriginalAllFullCoversInfinite S (i := i))
local notation "nr2" => CCO.HereditaryHiddenOrbits.terminalNR2 S hCover

/-- A07 supplies initial factor injectivity on the FULL CLOSED source
supports. A relation merely between descendants supplies no such premise.
This is a discharge from the ACTUAL HE map, rather than an assumed
factor-injectivity provider attached to the original source. -/
theorem factor_injective_of_actual_HE {P : Type z}
    (C : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (f : CCO.UnarySupport.Structure.Hom C (originalPartialTarget S H sap nr2))
    (hf : f.HomEmbedding) (roots : I ↪ P) (old : I → Sigma X)
    (hReal : ∀ i, f.point (roots i) = Sum.inl (old i))
    (hIrred : ∀ D ∈ factors,
      (C.closureStructure (roots '' D)).Irreducible) :
    FactorInjective factors old := by
  intro D hD i hi j hj hij
  apply roots.injective
  apply (hf _ (C.isClosed_closure _) (hIrred D hD)).1
  · exact C.subset_closure _ ⟨i,hi,rfl⟩
  · exact C.subset_closure _ ⟨j,hj,rfl⟩
  · rw [hReal i,hReal j,hij]

/-- The conditional higher-support source addendum, with all ordinary
initial-source premises discharged. The only added interface is the
SEPARATE A08 complete-tuple/SAP-clone interface J, never a premise of
binary hidden SAP, binary anchor readout or binary representative splitting. -/
theorem actual_HE_frozen_factor_splitting [Finite I] {P : Type z} [Finite P]
    (C : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (f : CCO.UnarySupport.Structure.Hom C (originalPartialTarget S H sap nr2))
    (hf : f.HomEmbedding) (roots : I ↪ P) (old : I → Sigma X)
    (hReal : ∀ i, f.point (roots i) = Sum.inl (old i))
    (hSort : ∀ i, C.sort (roots i) = ⟨⟨sort i,Sum.inl ()⟩⟩)
    (hIrred : ∀ D ∈ factors,
      (C.closureStructure (roots '' D)).Irreducible)
    (hAvoid : ∀ i, old i ∉ anchors) (hN : 2 ≤ N)
    (J : FrozenFactorSAPInterface (G := G) K sort factors anchors) :
    ∃ fresh : I → Sigma X,
      (∀ i, (fresh i).1 = sort i) ∧ Function.Injective fresh ∧
      (∀ i, fresh i ∉ anchors) ∧ SameFactors K factors old fresh ∧
      Relation.ReflTransGen (CloneStep (G := G) anchors) old fresh := by
  have hTyped : ∀ i, (old i).1 = sort i := by
    intro i
    have h := congrArg
      (fun q : (originalCompletedLanguage S H sap nr2).Sorts => q.down.1)
      ((f.sort_eq (roots i)).trans (hSort i))
    change (originalCompletedVertexSort S H (f.point (roots i))).1 = sort i at h
    rw [hReal i] at h
    exact h
  exact finite_frozen_factor_splitting hN J old hTyped hAvoid
    (factor_injective_of_actual_HE S H sap hCover C f hf roots old hReal hIrred)

end ActualSource

end
end CCO.HiddenSAPReadings.FrozenFactors
