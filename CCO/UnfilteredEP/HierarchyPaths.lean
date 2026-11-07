import CCO.UnfilteredEP.HierarchyKeys
import CCO.UnfilteredEP.TerminalHolonomy
import CCO.TypedOrbitFrames.ActualNamedTerms
import CCO.TransitionClosure.OriginalNamedRawInverse

/-!
# B064 C44: genuine named invertible paths on the proper hidden cuts

Each path carries its actual equivariant quotient bijection and forward
and inverse terms in the EXISTING unary signature, with their exact
values. Thus composition, inversion and restriction to arbitrary finite
closed actual members do not require new transition-function symbols.
Closed holonomy is discharged by actual FULL terminality.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ParityHasse.Original
open CCO.ResetOrder.Hierarchy CCO.UnaryTermsReturn CCO.TypedOrbitFrames
open CCO.TransitionClosure CCO.TerminalLattice CCO.TerminalPowers
noncomputable section

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

abbrev HiddenCutPoint (D : HiddenCut B) := Quotient D.2.val.val

/-- The original quotient action of the SAME actual full clone group. -/
def cutAct (D : HiddenCut B) (g : FullAut (cloneSource B)) (q : HiddenCutPoint B D) :
    HiddenCutPoint B D :=
  @SMul.smul _ _ (originalQuotientAction (cloneSource B) (cloneHomogeneous B) D.2.val).toSMul g q

/-- This is actual named syntax, together with its semantic map. Neither
an inverse-function symbol nor a quotient-action section is introduced. -/
structure NamedCutPath (D E : HiddenCut B) where
  quotientEquiv : HiddenCutPoint B D ≃ HiddenCutPoint B E
  equivariant : ∀ g q, quotientEquiv (cutAct B D g q) = cutAct B E g (quotientEquiv q)
  forward : CCO.UnaryFreshFrames.Term (Lang B ht) (hiddenCutSort B ht D) (hiddenCutSort B ht E)
  backward : CCO.UnaryFreshFrames.Term (Lang B ht) (hiddenCutSort B ht E) (hiddenCutSort B ht D)
  forward_value : ∀ q, (Hidden B ht).eval forward (namedNode B D.2 q) =
    namedNode B E.2 (quotientEquiv q)
  backward_value : ∀ q, (Hidden B ht).eval backward (namedNode B E.2 q) =
    namedNode B D.2 (quotientEquiv.symm q)

namespace NamedCutPath
variable {B ht}

def identity (D : HiddenCut B) : NamedCutPath B ht D D where
  quotientEquiv := Equiv.refl _
  equivariant _ _ := rfl
  forward := .id _
  backward := .id _
  forward_value _ := rfl
  backward_value _ := rfl

def inverse {D E : HiddenCut B} (p : NamedCutPath B ht D E) : NamedCutPath B ht E D where
  quotientEquiv := p.quotientEquiv.symm
  equivariant g q := by
    apply p.quotientEquiv.injective
    rw [Equiv.apply_symm_apply,p.equivariant,Equiv.apply_symm_apply]
  forward := p.backward
  backward := p.forward
  forward_value := p.backward_value
  backward_value := p.forward_value

def compose {D E F : HiddenCut B} (p : NamedCutPath B ht D E)
    (q : NamedCutPath B ht E F) : NamedCutPath B ht D F where
  quotientEquiv := p.quotientEquiv.trans q.quotientEquiv
  equivariant g x := by
    change q.quotientEquiv (p.quotientEquiv (cutAct B D g x)) = _
    rw [p.equivariant,q.equivariant]
    rfl
  forward := q.forward.comp p.forward
  backward := p.backward.comp q.backward
  forward_value x := by rw [CCO.UnaryFreshFrames.Structure.eval_comp,p.forward_value,q.forward_value]; rfl
  backward_value x := by rw [CCO.UnaryFreshFrames.Structure.eval_comp,q.backward_value,p.backward_value]; rfl

/-- Actual terminality kills every equivariant closed path, before any
hidden order, Ramsey or expansion-property argument. -/
theorem holonomy {D : HiddenCut B} (p : NamedCutPath B ht D D) (q : HiddenCutPoint B D) :
    p.quotientEquiv q = q := by
  let f : QuotientFunctionalGroup (cloneSource B) (cloneHomogeneous B) D.2.val :=
    ⟨p.quotientEquiv,p.equivariant⟩
  exact terminal_quotient_holonomy_apply B ht D.2.val f q

/-- The complete actual ambient path groupoid. -/
def ambientPaths : TransitionPaths (HiddenCut B) (HiddenCutPoint B) where
  Path := NamedCutPath B ht
  identity := identity
  compose := compose
  inverse := inverse
  map := quotientEquiv
  map_identity _ _ := rfl
  map_compose _ _ _ := rfl
  map_inverse p x := p.quotientEquiv.symm_apply_apply x
  holonomy := holonomy

end NamedCutPath

/-- An exact support-language rendering of an existing fresh unary term. -/
def freshSupportTerm {s t : (Lang B ht).Sorts}
    (q : CCO.UnaryFreshFrames.Term (Lang B ht) s t) :
    CCO.UnarySupport.Structure.Term (Sig B ht) s t :=
  CCO.TerminalHiddenHN.fullTermToSupport (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht))
    (CCO.TerminalHiddenHN.freshTermToFull (Lang B ht)
      (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)) q)

theorem freshSupportTerm_target_eval {s t : (Lang B ht).Sorts}
    (q : CCO.UnaryFreshFrames.Term (Lang B ht) s t) (x y : Values B)
    (hx : (Target B ht).sort x = s) :
    y ∈ (Target B ht).eval (freshSupportTerm B ht q) x ↔
      y = (Hidden B ht).eval q x := by
  let hbin := CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
    (cloneSAP B) (fullCovers B ht)
  have hs := CCO.TerminalHiddenHN.supportTermToFull_eval (Sig B ht) hbin (Target B ht)
    (freshSupportTerm B ht q) x
  rw [freshSupportTerm,CCO.TerminalHiddenHN.supportTermToFull_fullTermToSupport] at hs
  exact (Iff.of_eq (congrArg (fun A => y ∈ A) hs.symm)).trans
    (CCO.TerminalHiddenHN.freshTermToFull_eval (Lang B ht) hbin (Hidden B ht) q x y hx)

variable {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (hC : ActualAge B ht C)

/-- The value is evaluated INSIDE the arbitrary actual finite member.
Its domain is the prescribed sort, including orphan quotient vertices. -/
def finitePathValue {D E : HiddenCut B} (p : NamedCutPath B ht D E) :
    HiddenCutCarrier B ht C D → HiddenCutCarrier B ht C E :=
  C.value (CCO.TerminalHiddenHN.actualAge_total _ _ _ _ hC) (freshSupportTerm B ht p.forward)

/-- Exact ambient realization of a finite-member path value. -/
theorem finitePathValue_realization
    (e : C.Embedding (Target B ht)) {D E : HiddenCut B} (p : NamedCutPath B ht D E)
    (x : HiddenCutCarrier B ht C D) (q : HiddenCutPoint B D)
    (hx : e.point x.val = namedNode B D.2 q) :
    e.point (finitePathValue B ht C hC p x).val = namedNode B E.2 (p.quotientEquiv q) := by
  have hmem := e.toHom.map_eval (freshSupportTerm B ht p.forward)
    (C.value_mem (CCO.TerminalHiddenHN.actualAge_total _ _ _ _ hC) _ x)
  have hsort : (Target B ht).sort (e.point x.val) = hiddenCutSort B ht D :=
    (e.sort_eq x.val).trans x.property
  have he := (freshSupportTerm_target_eval B ht p.forward _ _ hsort).mp hmem
  rw [hx,p.forward_value] at he
  exact he

/-- Every vertex of the declared proper sort has its existing quotient
class in any whole realization. -/
theorem finite_cut_point_realized
    (e : C.Embedding (Target B ht)) (D : HiddenCut B) (x : HiddenCutCarrier B ht C D) :
    ∃ q : HiddenCutPoint B D, e.point x.val = namedNode B D.2 q := by
  exact original_completed_hidden_carrier_exists (cloneSource B) (HF B) (cloneSAP B)
    (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) D.2
    ⟨e.point x.val,(e.sort_eq x.val).trans x.property⟩

/-- The named inverse stays inside the SAME closed finite object. -/
def finitePathEquiv {D E : HiddenCut B} (p : NamedCutPath B ht D E) :
    HiddenCutCarrier B ht C D ≃ HiddenCutCarrier B ht C E where
  toFun := finitePathValue B ht C hC p
  invFun := finitePathValue B ht C hC p.inverse
  left_inv x := by
    obtain ⟨e⟩ := hC.2
    obtain ⟨q,hq⟩ := finite_cut_point_realized B ht C e D x
    apply Subtype.ext
    apply e.injective
    rw [finitePathValue_realization B ht C hC e p.inverse _ _
      (finitePathValue_realization B ht C hC e p x q hq)]
    exact (congrArg (namedNode B D.2) (p.quotientEquiv.symm_apply_apply q)).trans hq.symm
  right_inv x := by
    obtain ⟨e⟩ := hC.2
    obtain ⟨q,hq⟩ := finite_cut_point_realized B ht C e E x
    apply Subtype.ext
    apply e.injective
    rw [finitePathValue_realization B ht C hC e p _ _
      (finitePathValue_realization B ht C hC e p.inverse x q hq)]
    exact (congrArg (namedNode B E.2) (p.quotientEquiv.apply_symm_apply q)).trans hq.symm

/-- Restricting the entire actual path groupoid uses named inverse terms,
so no finite host is assumed closed under an unnamed semantic inverse. -/
def finiteCutPaths : TransitionPaths (HiddenCut B) (HiddenCutCarrier B ht C) where
  Path := NamedCutPath B ht
  identity := NamedCutPath.identity
  compose := NamedCutPath.compose
  inverse := NamedCutPath.inverse
  map := finitePathEquiv B ht C hC
  map_identity D x := by
    obtain ⟨e⟩ := hC.2
    obtain ⟨q,hq⟩ := finite_cut_point_realized B ht C e D x
    apply Subtype.ext
    apply e.injective
    exact (finitePathValue_realization B ht C hC e _ x q hq).trans hq.symm
  map_compose p q x := by
    obtain ⟨e⟩ := hC.2
    obtain ⟨r,hr⟩ := finite_cut_point_realized B ht C e _ x
    apply Subtype.ext
    apply e.injective
    change e.point (finitePathValue B ht C hC (p.compose q) x).val =
      e.point (finitePathValue B ht C hC q (finitePathValue B ht C hC p x)).val
    rw [finitePathValue_realization B ht C hC e _ x r hr,
      finitePathValue_realization B ht C hC e q _ _
        (finitePathValue_realization B ht C hC e p x r hr)]
    rfl
  map_inverse p x := by
    exact (finitePathEquiv B ht C hC p).left_inv x
  holonomy p x := by
    obtain ⟨e⟩ := hC.2
    obtain ⟨q,hq⟩ := finite_cut_point_realized B ht C e _ x
    apply Subtype.ext
    apply e.injective
    change e.point (finitePathValue B ht C hC p x).val = e.point x.val
    rw [finitePathValue_realization B ht C hC e p x q hq,p.holonomy]
    exact hq.symm

/-- Old induced embeddings commute with ALL actual named paths. -/
theorem finitePathValue_embedding_commutes {W : Type*}
    {D : CCO.UnarySupport.Structure (Sig B ht) W} (hD : ActualAge B ht D)
    (e : C.Embedding D) {i j : HiddenCut B} (p : NamedCutPath B ht i j)
    (x : HiddenCutCarrier B ht C i) :
    e.point (finitePathValue B ht C hC p x).val =
      (finitePathValue B ht D hD p ⟨e.point x.val,(e.sort_eq x.val).trans x.property⟩).val :=
  e.value_map _ _ _ x

end
end CCO.UnfilteredEP
