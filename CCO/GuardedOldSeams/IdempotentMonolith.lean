import CCO.PairSafeSplit.Infinity.TypeFibres
import Mathlib.Order.Preorder.Finite

/-! The genuine original SAP monolith on ANY named sort, with the whole
original ambient group retained. No CCO or NR2 premise is used. -/

universe u v w t
namespace CCO.GuardedOldSeams
open CCO.ParityHasse.Original CCO.PairSafeSplit.Infinity

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
include H sap

/-- Stabilize the two actual other class points. Their common original
stabilizer orbit lies in the fixed intersection class and is infinite. -/
theorem nonidentity_inf_class_infinite {i : ι} (E F : ColourEq S i)
    (hE : ⊥ < E) (hF : ⊥ < F) (x : X i) :
    Set.Infinite {z | (E ⊓ F) x z} := by
  classical
  obtain ⟨y,he,hy⟩ := class_has_other S H E hE x
  obtain ⟨z,hf,hz⟩ := class_has_other S H F hF x
  let B : FiniteInduced (X := X) :=
    ⟨{(⟨i,y⟩ : Sigma X),⟨i,z⟩},(Set.finite_singleton _).insert _⟩
  have hx : (⟨i,x⟩ : Sigma X) ∉ B.vertices := by
    intro h
    rcases h with h | h
    · exact hy (eq_of_heq (Sigma.mk.inj h).2)
    · exact hz (eq_of_heq (Sigma.mk.inj h).2)
  apply (typeFibre_infinite S H sap B x hx).mono
  intro a ha
  obtain ⟨g,hg,hga⟩ := (typeFibre_iff_orbit S H B x a).mp ha
  have hgy : g • y = y := by
    simpa only [Sigma.smul_mk,Sigma.mk.injEq,heq_eq_eq,true_and]
      using hg ⟨i,y⟩ (Or.inl rfl)
  have hgz : g • z = z := by
    simpa only [Sigma.smul_mk,Sigma.mk.injEq,heq_eq_eq,true_and]
      using hg ⟨i,z⟩ (Or.inr rfl)
  have hga' : g • x = a := eq_of_heq (Sigma.mk.inj hga).2
  constructor
  · have h := colourInvariant_groupInvariant S H E.property g x y he
    rw [hga',hgy] at h
    exact E.val.trans he (E.val.symm h)
  · have h := colourInvariant_groupInvariant S H F.property g x z hf
    rw [hga',hgz] at h
    exact F.val.trans hf (F.val.symm h)

theorem nonidentity_inf_gt_bot {i : ι} (E F : ColourEq S i)
    (hE : ⊥ < E) (hF : ⊥ < F) : ⊥ < E ⊓ F := by
  apply lt_of_le_of_ne bot_le
  intro heq
  obtain ⟨x⟩ := S.nonemptySort i
  have hi := nonidentity_inf_class_infinite S H sap E F hE hF x
  rw [← heq] at hi
  exact hi (by simpa only [ColourEq.bot_apply,Set.setOf_eq_eq_singleton']
    using Set.finite_singleton x)

theorem original_top_gt_bot (i : ι) : (⊥ : ColourEq S i) < ⊤ := by
  apply lt_of_le_of_ne bot_le
  intro heq
  obtain ⟨x⟩ := S.nonemptySort i
  let B : FiniteInduced (X := X) := ⟨∅,Set.finite_empty⟩
  have hi := typeFibre_infinite S H sap B x (by simp [B])
  apply hi
  apply (Set.finite_singleton x).subset
  intro y _
  have hb : (⊥ : ColourEq S i) x y := by rw [heq]; trivial
  exact hb.symm

theorem exists_original_monolith (i : ι) :
    ∃ L : ColourEq S i, ⊥ < L ∧ ∀ E : ColourEq S i, ⊥ < E → L ≤ E := by
  obtain ⟨L,hL,hmin⟩ := wellFounded_lt.has_min
    {E : ColourEq S i | ⊥ < E} ⟨⊤,original_top_gt_bot S H sap i⟩
  refine ⟨L,hL,?_⟩
  intro E hE
  have hm : L ⊓ E = L := by
    apply le_antisymm inf_le_left
    by_contra hn
    exact hmin (L ⊓ E) (nonidentity_inf_gt_bot S H sap L E hL hE)
      (lt_of_le_of_ne inf_le_left (Ne.symm (ne_of_not_le hn)))
  rw [← hm]
  exact inf_le_right

noncomputable def originalMonolith (i : ι) : ColourEq S i :=
  Classical.choose (exists_original_monolith S H sap i)

theorem originalMonolith_gt_bot (i : ι) : ⊥ < originalMonolith S H sap i :=
  (Classical.choose_spec (exists_original_monolith S H sap i)).1

theorem originalMonolith_le {i : ι} (E : ColourEq S i) (hE : ⊥ < E) :
    originalMonolith S H sap i ≤ E :=
  (Classical.choose_spec (exists_original_monolith S H sap i)).2 E hE

theorem originalMonolith_unique {i : ι} (L : ColourEq S i) (hL : ⊥ < L)
    (least : ∀ E : ColourEq S i, ⊥ < E → L ≤ E) :
    L = originalMonolith S H sap i :=
  le_antisymm (least _ (originalMonolith_gt_bot S H sap i))
    (originalMonolith_le S H sap L hL)

end CCO.GuardedOldSeams
