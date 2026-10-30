import CCO.UnaryHN.RankStep

/-! Genuine iteration of the constructed closed-rank pass. Each new control
is the previous ACTUAL finite picture; maps to the ORIGINAL Ramsey witness
are composed, never identified with arbitrary new control labels. -/

universe u v w
namespace CCO.UnaryHN.Native

open StructuralRamsey
open StructuralRamsey.Structure

namespace PartiteTransfer

structure RankStage {L : Language.{u}} (K : Class.{u,v} L)
    {U V P : Type v} (A : Structure L U) (B : Structure L V)
    (D : Structure L P) (κ : Type w) (n : ℕ) where
  Carrier : Type v
  finiteCarrier : Finite Carrier
  C : Structure L Carrier
  admissible : admissibleClass K C
  arrow : Structure.Arrow A B C κ
  projection : Carrier → P
  projectionHE : HE C D projection
  local : ClosedSmallCompletable K C n

attribute [instance] RankStage.finiteCarrier

variable {L : Language.{u}} {K : Class.{u,v} L} {U V P : Type v}

theorem first (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    (hUnary : Unary L) (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P] (hA : K A) (hB : K B)
    (κ : Type w) [Fintype κ] [Nonempty κ] (hArrow : Structure.Arrow A B D κ) :
    Nonempty (RankStage K A B D κ 1) := by
  classical
  obtain ⟨beta0, _⟩ := hArrow (fun _ => Classical.choice (inferInstance : Nonempty κ))
  have hZero := closed_small_zero_of_placement hK hB beta0
  obtain ⟨T, hT, hTArrow⟩ := closed_rank_pass hK hIrr hUnary A B hA hB κ hArrow 0 hZero
  exact ⟨{
    Carrier := T.Carrier
    finiteCarrier := T.finiteCarrier
    C := T.system.toStructure
    admissible := T.mem
    arrow := hTArrow
    projection := T.system.part
    projectionHE := T.isPartite
    local := hT
  }⟩

theorem next (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    (hUnary : Unary L) (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] (hA : K A) (hB : K B)
    (κ : Type w) [Fintype κ] [Nonempty κ] (n : ℕ) (S : RankStage K A B D κ n) :
    Nonempty (RankStage K A B D κ (n + 1)) := by
  obtain ⟨T, hT, hTArrow⟩ :=
    closed_rank_pass hK hIrr hUnary A B hA hB κ S.arrow n S.local
  exact ⟨{
    Carrier := T.Carrier
    finiteCarrier := T.finiteCarrier
    C := T.system.toStructure
    admissible := T.mem
    arrow := hTArrow
    projection := S.projection ∘ T.system.part
    projectionHE := S.projectionHE.comp T.isPartite
    local := hT
  }⟩

theorem build (hK : FiniteHereditarySAP K) (hIrr : AllIrreducible K)
    (hUnary : Unary L) (A : Structure L U) (B : Structure L V) (D : Structure L P)
    [Finite U] [Finite V] [Finite P] (hA : K A) (hB : K B)
    (κ : Type w) [Fintype κ] [Nonempty κ] (hArrow : Structure.Arrow A B D κ)
    (n : ℕ) (hn : 0 < n) : Nonempty (RankStage K A B D κ n) := by
  induction n with
  | zero => omega
  | succ m ih =>
      by_cases hm : m = 0
      · subst m
        exact first hK hIrr hUnary A B D hA hB κ hArrow
      · obtain ⟨S⟩ := ih (Nat.pos_of_ne_zero hm)
        exact next hK hIrr hUnary A B D hA hB κ m S

end PartiteTransfer

theorem arrow_of_HE_completion {L : Language.{u}} {U V W X : Type v}
    {A : Structure L U} {B : Structure L V} {C : Structure L W} {D : Structure L X}
    (hA : A.Irreducible) (hB : B.Irreducible) {p : W → X} (hp : HE C D p)
    (κ : Type w) (hArrow : Structure.Arrow A B C κ) : Structure.Arrow A B D κ := by
  classical
  let transport (e : Embedding A C) : Embedding A D := Classical.choose (hp.2 A hA e)
  have hTransport (e : Embedding A C) (a : U) : transport e a = p (e a) :=
    Classical.choose_spec (hp.2 A hA e) a
  intro chi
  obtain ⟨eB, hColor⟩ := hArrow (fun e => chi (transport e))
  obtain ⟨eT, heT⟩ := hp.2 B hB eB
  have hComp (e : Embedding A B) : transport (eB.comp e) = eT.comp e := by
    apply Embedding.ext
    intro a
    exact (hTransport (eB.comp e) a).trans (heT (e a)).symm
  refine ⟨eT, ?_⟩
  intro e1 e2
  simpa only [hComp] using hColor e1 e2

/-- Original functional HN 2.11 in the required UNARY partial-function case.
Only the actual Definition 2.8 local-finiteness hypothesis is retained; all
Picture/rank construction inputs have been proved above. -/
theorem original_unary_locally_finite_ramsey {L : Language.{u}} {K R : Class.{u,v} L}
    (hUnary : Unary L) (hK : FiniteHereditarySAP K)
    (hSub : ∀ {V : Type v} (C : Structure L V), K C → R C)
    (hRirred : AllIrreducible R) (hRamsey : Ramsey.{u,v,w} R)
    (hLocal : LocallyFinite K R) : Ramsey.{u,v,w} K := by
  intro U V hU hV A B hA hB κ hκ hκnonempty
  have hIrr : AllIrreducible K := fun C hC => hRirred C (hSub C hC)
  obtain ⟨P, hP, D, hD, hArrow⟩ := hRamsey A B (hSub A hA) (hSub B hB) κ
  letI : Finite P := hP
  obtain ⟨n, hn⟩ := hLocal D hD
  obtain ⟨S⟩ := PartiteTransfer.build hK hIrr hUnary A B D hA hB κ hArrow (n + 1) (by omega)
  have hComplete : HasCompletion K S.C :=
    hn S.C S.admissible.1 ⟨S.projection, S.projectionHE⟩ S.admissible.2
      (S.local.mono (Nat.le_succ n))
  obtain ⟨X, hX, T, hT, p, hp⟩ := hComplete
  exact ⟨X, hX, T, hT, arrow_of_HE_completion (hIrr A hA) (hIrr B hB) hp κ S.arrow⟩

end CCO.UnaryHN.Native
