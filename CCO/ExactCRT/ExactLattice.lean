import CCO.RawExact.ActualQuotientSource
import CCO.RawExact.FineColoursSource
import CCO.ParityHasse.Original.OrbitalAlgebra
import Mathlib.Order.Sublattice

/-!
# The actual full-exact equivalence sublattice

C11 and C12 use the original RAW calculus. The ambient invariant equivalence
lattice need not be distributive. Finiteness reuses the finite actual optional
palette injection; no Hasse, finite-index, SAP or countability result is used.
-/

universe u v w t
namespace CCO.ExactCRT
open RawExact
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]

/-- Exactness is a property of the actual equivalence, independent of its
chosen finite word presentation. Equality and Top keep their RAW meanings. -/
def IsExactEq {i : ι} (E : Setoid (X i)) : Prop :=
  ∃ D : NonemptyExact S i i, evaluate S D.words = E.r

noncomputable def exactPresentation {i : ι} {E : Setoid (X i)}
    (hE : IsExactEq S E) : NonemptyExact S i i := Classical.choose hE

theorem exactPresentation_represents {i : ι} {E : Setoid (X i)}
    (hE : IsExactEq S E) : evaluate S (exactPresentation S hE).words = E.r :=
  Classical.choose_spec hE

theorem isExactEq_bot (i : ι) : IsExactEq S (⊥ : Setoid (X i)) :=
  ⟨exactIdentityAtom S i, exactIdentityAtom_relation S i⟩

theorem isExactEq_top (i : ι) : IsExactEq S (⊤ : Setoid (X i)) :=
  ⟨NonemptyExact.top S i i, evaluate_nil S⟩

theorem isExactEq_inf {i : ι} {E F : Setoid (X i)}
    (hE : IsExactEq S E) (hF : IsExactEq S F) : IsExactEq S (E ⊓ F) := by
  obtain ⟨D, hD⟩ := hE
  obtain ⟨P, hP⟩ := hF
  obtain ⟨x⟩ := S.nonemptySort i
  have hn : TRel.Nonempty (fun x y => evaluate S D.words x y ∧ evaluate S P.words x y) :=
    ⟨x, x, by simpa only [hD] using E.refl x, by simpa only [hP] using F.refl x⟩
  refine ⟨NonemptyExact.meet S D P hn, ?_⟩
  rw [NonemptyExact.meet_relation S, hD, hP]
  rfl

theorem isExactEq_colourInvariant (H : HomogeneousSource S G)
    {i : ι} {E : Setoid (X i)} (hE : IsExactEq S E) : ColourInvariant S i E := by
  obtain ⟨D, hD⟩ := hE
  apply groupInvariant_colourInvariant S H
  intro g x y hxy
  rw [← hD] at hxy ⊢
  exact presentation_invariant_of_homogeneous S H D.words g x y hxy

theorem isExactEq_sup (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} {E F : Setoid (X i)}
    (hE : IsExactEq S E) (hF : IsExactEq S F) : IsExactEq S (E ⊔ F) := by
  obtain ⟨D, hD⟩ := hE
  obtain ⟨P, hP⟩ := hF
  let e : ColourEq S i := ⟨E, isExactEq_colourInvariant S H ⟨D, hD⟩⟩
  let f : ColourEq S i := ⟨F, isExactEq_colourInvariant S H ⟨P, hP⟩⟩
  refine ⟨convolutionExact S H D P, ?_⟩
  rw [convolutionExact_represents S H (heterogeneousExactBallHelly_of_CCO S H cco), hD, hP]
  funext x y
  exact propext (sup_relation_iff S H e f x y).symm

/-- The actual exact equivalences are closed under AMBIENT binary meet and
join. Its bottom and top are proved separately, not assumed for abstract CRT. -/
def exactSublattice (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S) (i : ι) : Sublattice (Setoid (X i)) where
  carrier := {E | IsExactEq S E}
  infClosed' := fun _ hE _ hF => isExactEq_inf S hE hF
  supClosed' := fun _ hE _ hF => isExactEq_sup S H cco hE hF

abbrev ExactEq (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S) (i : ι) := exactSublattice S H cco i

instance exactEqFinite (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S) (i : ι) : Finite (ExactEq S H cco i) := by
  let f : ExactEq S H cco i → ColourEq S i :=
    fun E => ⟨E.val, isExactEq_colourInvariant S H E.property⟩
  apply Finite.of_injective f
  intro E F h
  exact Subtype.ext (congrArg (fun E : ColourEq S i => E.val) h)

instance exactEqOrderBot (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S) (i : ι) : OrderBot (ExactEq S H cco i) where
  bot := ⟨⊥, isExactEq_bot S i⟩
  bot_le := fun E => show (⊥ : Setoid (X i)) ≤ E.val from bot_le

instance exactEqOrderTop (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S) (i : ι) : OrderTop (ExactEq S H cco i) where
  top := ⟨⊤, isExactEq_top S i⟩
  le_top := fun E => show E.val ≤ (⊤ : Setoid (X i)) from le_top

/-- All pairs in this sublattice really commute as represented relations;
only the source pair-flip theorem is used here. -/
theorem exactEq_commutes (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S) (i : ι)
    (E F : ExactEq S H cco i) :
    RawSymmetric.compose E.val.r F.val.r = RawSymmetric.compose F.val.r E.val.r :=
  invariant_relations_commute S H (isExactEq_colourInvariant S H E.property)
    (isExactEq_colourInvariant S H F.property)

/-- C12: classes at DISTINCT OR REPEATED actual centres are exact balls.
This consumes the different-centre ball theorem, not support Helly. -/
theorem exactEq_classHelly (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,max u v,w} S) {i : ι}
    {I : Type*} [Finite I] (E : I → ExactEq S H cco i) (centre : I → X i)
    (hPair : ∀ p q, ∃ x, (E p).val (centre p) x ∧ (E q).val (centre q) x) :
    ∃ x, ∀ p, (E p).val (centre p) x := by
  let D : I → NonemptyExact S i i := fun p => exactPresentation S (E p).property
  have hD : ∀ p, evaluate S (D p).words = (E p).val.r :=
    fun p => exactPresentation_represents S (E p).property
  have hp : ∀ p q, (ball (evaluate S (D p).words) (centre p) ∩
      ball (evaluate S (D q).words) (centre q)).Nonempty := by
    intro p q
    obtain ⟨x, hx, hy⟩ := hPair p q
    refine ⟨x, ?_, ?_⟩
    · change evaluate S (D p).words x (centre p)
      rw [hD]
      exact (E p).val.symm hx
    · change evaluate S (D q).words x (centre q)
      rw [hD]
      exact (E q).val.symm hy
  classical
  letI : Fintype I := Fintype.ofFinite I
  let e := Fintype.equivFin I
  obtain ⟨x, hx⟩ := heterogeneousExactBallHelly_of_CCO S H cco
    (fun _ : Fin (Fintype.card I) => i) (fun k => D (e.symm k))
    (fun k => centre (e.symm k)) (fun p q => hp (e.symm p) (e.symm q))
  refine ⟨x, fun p => ?_⟩
  have h := hx (e p)
  simp only [Equiv.symm_apply_apply] at h
  rw [hD] at h
  exact (E p).val.symm h

end CCO.ExactCRT
