import CCO.GuardedOldSeams.BranchEquation
import CCO.GuardedOldSeams.OldSeams
import CCO.GuardedOldSeams.LiftMenus

/-! OLD equations restrict to closed boundary supports. One-variable
semantic identities are reflected only through the actual valid singleton,
without a completion of the surrounding partial source. -/

universe u v w r z
namespace CCO.OldIdempotentForest
open CCO.GuardedOldSeams CCO.HiddenSAPReadings CCO.UnaryTermsReturn
open CCO.UnaryFreshFrames CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.TypedOrbitFrames CCO.GuardedTwoRoot

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
local notation "Lang" => originalCompletedLanguage S H sap nr2
local notation "Hidden" => originalCompletedStructure S H sap nr2

theorem gap_oldTerm_comp {C D E : (Lang).Sorts}
    (outer : CCO.UnaryFreshFrames.Term Lang D E)
    (inner : CCO.UnaryFreshFrames.Term Lang C D) :
    oldTerm S H sap nr2 (outer.comp inner) =
      composeOldTerms (oldTerm S H sap nr2 outer) (oldTerm S H sap nr2 inner) := by
  induction outer with
  | id => rfl
  | func U tail ih =>
    change CCO.UnarySupport.Structure.Term.func
        (L := originalPartialSignature S H sap nr2) U
        (oldTerm S H sap nr2 (tail.comp inner)) =
      CCO.UnarySupport.Structure.Term.func
        (L := originalPartialSignature S H sap nr2) U
        (composeOldTerms (oldTerm S H sap nr2 tail) (oldTerm S H sap nr2 inner))
    exact congrArg (fun t : CCO.UnarySupport.Structure.Term
      (originalPartialSignature S H sap nr2) C
      ((originalPartialSignature S H sap nr2).input U) =>
        CCO.UnarySupport.Structure.Term.func
          (L := originalPartialSignature S H sap nr2) U t) ih

/-- Two actual OLD side equations compose through one and the same
canonical OLD intermediate readout. The accepted literal seam telescope
identifies the composite's actual value; no equality of target images is
used as a seam and no completion of the ambient source is assumed. -/
theorem gap_literal_compose {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (hTotal : F.Total)
    {C0 C1 C2 J0 J1 J2 : (Lang).Sorts}
    (τ0 : CCO.UnaryFreshFrames.Term Lang C0 J0)
    (τ1 : CCO.UnaryFreshFrames.Term Lang C1 J1)
    (τ2 : CCO.UnaryFreshFrames.Term Lang C2 J2)
    (σ0 : CCO.UnaryFreshFrames.Term Lang J0 J1)
    (σ1 : CCO.UnaryFreshFrames.Term Lang J1 J2)
    (b c d : P) (hb : F.sort b = C0) (hc : F.sort c = C1) (hd : F.sort d = C2)
    (h01 : LiteralOldEquation S H sap nr2 F (σ0.comp τ0) τ1 b c)
    (h12 : LiteralOldEquation S H sap nr2 F (σ1.comp τ1) τ2 c d) :
    LiteralOldEquation S H sap nr2 F ((σ1.comp σ0).comp τ0) τ2 b d := by
  obtain ⟨v0,hv0⟩ := F.eval_nonempty hTotal (oldTerm S H sap nr2 τ0) hb
  obtain ⟨v1,hv1⟩ := F.eval_nonempty hTotal (oldTerm S H sap nr2 τ1) hc
  obtain ⟨v2,hv2⟩ := F.eval_nonempty hTotal (oldTerm S H sap nr2 τ2) hd
  have hσ0 : v1 ∈ F.eval (oldTerm S H sap nr2 σ0) v0 := by
    obtain ⟨q,hq,hq'⟩ := h01
    rw [gap_oldTerm_comp S H sap nr2] at hq
    obtain ⟨p,hp,hpq⟩ := (eval_composeOldTerms F
      (oldTerm S H sap nr2 σ0) (oldTerm S H sap nr2 τ0) b q).mp hq
    have hpv : p = v0 := F.eval_functional _ hp hv0
    have hqv : q = v1 := F.eval_functional _ hq' hv1
    simpa only [hpv,hqv] using hpq
  have hσ1 : v2 ∈ F.eval (oldTerm S H sap nr2 σ1) v1 := by
    obtain ⟨q,hq,hq'⟩ := h12
    rw [gap_oldTerm_comp S H sap nr2] at hq
    obtain ⟨p,hp,hpq⟩ := (eval_composeOldTerms F
      (oldTerm S H sap nr2 σ1) (oldTerm S H sap nr2 τ1) c q).mp hq
    have hpv : p = v1 := F.eval_functional _ hp hv1
    have hqv : q = v2 := F.eval_functional _ hq' hv2
    simpa only [hpv,hqv] using hpq
  let q0 : OldReadout F Set.univ J0 := {
    input := C0, root := b, root_mem := trivial, root_sort := hb
    term := oldTerm S H sap nr2 τ0, value := v0, defined := hv0 }
  let q1 : OldReadout F Set.univ J1 := {
    input := C1, root := c, root_mem := trivial, root_sort := hc
    term := oldTerm S H sap nr2 τ1, value := v1, defined := hv1 }
  let q2 : OldReadout F Set.univ J2 := {
    input := C2, root := d, root_mem := trivial, root_sort := hd
    term := oldTerm S H sap nr2 τ2, value := v2, defined := hv2 }
  let side0 : OldUnarySide F q0 q1 := {
    transition := oldTerm S H sap nr2 σ0
    output := v1, defined := hσ0, equation := rfl }
  let side1 : OldUnarySide F q1 q2 := {
    transition := oldTerm S H sap nr2 σ1
    output := v2, defined := hσ1, equation := rfl }
  let chain : OldSeamChain F Set.univ q0 q2 :=
    .cons side0 (.cons side1 (.nil q2))
  obtain ⟨v,hv⟩ := F.eval_nonempty hTotal
    (oldTerm S H sap nr2 ((σ1.comp σ0).comp τ0)) hb
  have hvChain : v ∈ F.eval chain.term q0.value := by
    have h := hv
    rw [gap_oldTerm_comp S H sap nr2, gap_oldTerm_comp S H sap nr2] at h
    obtain ⟨p,hp,hpv⟩ := (eval_composeOldTerms F
      (composeOldTerms (oldTerm S H sap nr2 σ1) (oldTerm S H sap nr2 σ0))
      (oldTerm S H sap nr2 τ0) b v).mp h
    have hpv0 : p = v0 := F.eval_functional _ hp hv0
    change v ∈ F.eval
      (composeOldTerms (oldTerm S H sap nr2 σ1) (oldTerm S H sap nr2 σ0)) v0
    simpa only [hpv0] using hpv
  have hv2eq : v = v2 :=
    (old_seam_telescope F F.isClosed_univ chain hvChain).1
  exact ⟨v,hv,hv2eq.symm ▸ hv2⟩

theorem gap_literal_restrict {P : Type z}
    {F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P}
    {A : Set P} (hA : F.IsClosed A)
    {C D E : (Lang).Sorts} {left : CCO.UnaryFreshFrames.Term Lang C E}
    {right : CCO.UnaryFreshFrames.Term Lang D E}
    {b c : P} (hb : b ∈ A) (hc : c ∈ A)
    (h : LiteralOldEquation S H sap nr2 F left right b c) :
    LiteralOldEquation S H sap nr2 (F.induce A hA) left right ⟨b,hb⟩ ⟨c,hc⟩ := by
  obtain ⟨a,ha,ha'⟩ := h
  let e := F.inclusion A hA
  obtain ⟨aA,hAleft,heA⟩ := e.reflect_eval (oldTerm S H sap nr2 left) (x := ⟨b,hb⟩) ha
  obtain ⟨aB,hBright,heB⟩ := e.reflect_eval (oldTerm S H sap nr2 right) (x := ⟨c,hc⟩) ha'
  have hAB : aA = aB := e.injective (heA.trans heB.symm)
  exact ⟨aA,hAleft,hAB.symm ▸ hBright⟩

/-- Actual singleton admissibility, rather than a hypothetical global
completion, transfers the displayed identity on one OLD source variable. -/
theorem gap_unary_admissible_identity {P : Type z} [Finite P]
    (F : CCO.UnarySupport.Structure (originalPartialSignature S H sap nr2) P)
    (hUnary : UnaryAdmissible F (originalPartialTarget S H sap nr2))
    {C D : (Lang).Sorts} (left right : CCO.UnaryFreshFrames.Term Lang C D)
    (same : ∀ x : OriginalCompletedNamedCarrier S H,
      (Hidden).sort x = C → (Hidden).eval left x = (Hidden).eval right x)
    (b : P) (hb : F.sort b = C) :
    LiteralOldEquation S H sap nr2 F left right b b := by
  obtain ⟨e⟩ := hUnary b
  have hLocal : LiteralOldEquation S H sap nr2 (F.singletonStructure b) left right
      ⟨b,F.mem_closureAt b⟩ ⟨b,F.mem_closureAt b⟩ := by
    apply literalOldEquation_of_embedding S H sap nr2 (F.singletonStructure b) e left right
      ⟨b,F.mem_closureAt b⟩ ⟨b,F.mem_closureAt b⟩ hb hb
    exact same _ ((e.sort_eq ⟨b,F.mem_closureAt b⟩).trans hb)
  exact LiteralOldEquation.of_closed_support S H sap nr2 (F.isClosed_closure {b}) hLocal

end CCO.OldIdempotentForest
