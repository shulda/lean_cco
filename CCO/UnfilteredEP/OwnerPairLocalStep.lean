import CCO.UnfilteredEP.OwnerTemplate
import CCO.CloneTupleGeometry.OwnerFiniteBaseTypes

/-! B064 C85–C86, one genuine character step. Pointwise actual pair
compatibility supplies all true old phase masks. B044 realizes the whole
finite marked diagram at once; its clone-constant tags descend to owners. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open CCO.CloneTupleGeometry CCO.APCharacter CCO.APCharacter.SourceAge
open CCO.APCharacter.Towers CCO.RigidGroupoid.Geometry CCO.TerminalPowers
noncomputable section

variable (B : OwnerStage.{u,v,w})
variable {i : B.Sorts} {K : Kernel (CloneSAP.source B.source) i}
variable (P : SourcePhase (CloneSAP.source B.source)
  (CloneSAP.homogeneous B.source B.homogeneous)
  (exactCalculus_of_homogeneous_CCO B.cloneCurrent.source B.cloneCurrent.homogeneous B.cloneCurrent.cco) K)

/-- ANY pair-compatible list of proposed child labels is realized on
one finite actual successor tuple, retaining its entire old fine matrix. -/
theorem owner_successor_pairLocal {n : Nat}
    (old : Fin n → Sigma B.Point) (hinj : Function.Injective old)
    (labels : Fin n → (B.successor P).Sorts)
    (compatible : PairCompatible (B.successorReduct P) old labels) :
    ∃ f : Fin n ↪ Sigma (B.successor P).Point,
      (∀ x, (f x).1 = labels x) ∧
      ∀ x y, taggedColour B.source ((B.successorReduct P).project (f x))
        ((B.successorReduct P).project (f y)) = taggedColour B.source (old x) (old y) := by
  let C := exactCalculus_of_homogeneous_CCO B.cloneCurrent.source B.cloneCurrent.homogeneous B.cloneCurrent.cco
  let I := B.identification P
  let pr := B.successorReduct P
  let bits : Fin n → Bit := fun x => (labels x).2.val
  have hsort (x : Fin n) : (labels x).1 = (old x).1 := by
    obtain ⟨p,q,hp,_,hc⟩ := compatible x x
    exact (congrArg Sigma.fst hp).symm.trans
      (congrArg (fun c : Age.Colour B.source => c.1) hc)
  have hglobal (p q : Sigma (B.successor P).Point) :
      P.allows ((CloneSAP.source B.source).colour
        (zeroClonePoint (pr.project p)).2 (zeroClonePoint (pr.project q)).2)
        p.1.2.val q.1.2.val := by
    have hh := (UnarySource.global_marking
      (completion := P.completion_property B.cloneCurrent.cco) I).2
        (zeroClonePoint (pr.project p)) (zeroClonePoint (pr.project q))
    have hbp : UnarySource.mark
        (completion := P.completion_property B.cloneCurrent.cco) I
        (zeroClonePoint (pr.project p)) = p.1.2.val :=
      owner_zero_bit B.source B.homogeneous B.ap C P B.cco I p
    have hbq : UnarySource.mark
        (completion := P.completion_property B.cloneCurrent.cco) I
        (zeroClonePoint (pr.project q)) = q.1.2.val :=
      owner_zero_bit B.source B.homogeneous B.ap C P B.cco I q
    rw [hbp,hbq] at hh
    exact hh
  have hlegal : Age.Legal (CloneSAP.source B.source) P.masks (zeroClonePoint ∘ old) bits := by
    constructor
    · intro x
      have h := (labels x).2.property
      change P.validBit (labels x).1 (bits x) at h
      rw [hsort x] at h
      exact h
    · intro x y
      obtain ⟨p,q,hp,hq,hc⟩ := compatible x y
      have hg := hglobal p q
      rw [hp,hq] at hg
      exact phase_allowed_of_tagged (CloneSAP.source B.source) P.masks
        (zeroClonePoint_tagged B.source hc.symm) (bits x) (bits y) hg
  obtain ⟨f,hf,hcol⟩ := owner_marked_age_embeds B.source B.homogeneous B.ap C P B.cco I
    old bits hinj hlegal
  refine ⟨f,?_,hcol⟩
  intro x
  apply UnarySource.childLabel_injective I
  exact (hf x).trans (Prod.ext (hsort x).symm rfl)

end
end CCO.UnfilteredEP
