import CCO.ExactEPGeometry.ExactMeetSupport
import CCO.ExactEPGeometry.CertifiedGateTower

/-!
# B062 C48: finite RAW-exact meet primality along certified safe towers

All stages are the ACTUAL original-gate-certified finite AP-character
history. Each Step carries the SAME original source, selected current
odd orbital, maximal old exact gate and real SourcePhase. The theorem
composes the proven one-step AP-only exact-meet property with the
previous prefix's real two-way exact trace transport.

There is no axiom, arbitrary ActualStep primality, quotient SAP,
unproved global automorphism section, or unguarded empty intersection.
-/

universe u v w t

namespace CCO.ExactEPGeometry.CertifiedGateTower

open APCharacter.SourceAge
open APCharacter.Towers
open CCO.ExactEPGeometry

noncomputable section

/-- The ACTUAL next gate-certified original-to-current source retains
guarded support of finite original RAW exact intersections. The old
original gate/phase is reused literally, with no independently selected
unary successor. -/
theorem step_meet_support
    {original : CurrentSource.{u,v,w,t}}
    {s q : ExactPrefix original}
    (hStep : Step s q)
    (hS : ExactMeetSupport original.source s.current.source s.reduct) :
    ExactMeetSupport original.source q.current.source q.reduct := by
  obtain ⟨choice,rfl⟩ := hStep
  exact ExactMeetSupport.compose
    s.reduct (SingleStep.projection s.current choice.phase)
    s.transport hS
    (ExactMeetSupport.canonical_step s.current choice.phase)

/-- Source C48 at EVERY prefix of any genuine certified finite safe
history: every finite family with a NONEMPTY original intersection
has simultaneous support on two final types whenever each individual
factor has support there. All witnesses are actual old/current pairs. -/
theorem history_meet_support
    {original : CurrentSource.{u,v,w,t}}
    {s q : ExactPrefix original}
    (history : History Step s q)
    (hS : ExactMeetSupport original.source s.current.source s.reduct) :
    ExactMeetSupport original.source q.current.source q.reduct := by
  exact History.preserves Step
    (fun b : ExactPrefix original =>
      ExactMeetSupport original.source b.current.source b.reduct)
    (fun {_ _} step h => step_meet_support step h)
    history hS

/-- The actually constructed terminal gate-certified source admits
both the bound on all real character stages and the fully guarded
finite exact-family support identity between every pair of realized
terminal unary types. This includes a zero-step terminal source. -/
theorem terminalisation_meet_support
    (original : CurrentSource.{u,v,w,t}) :
    ∃ terminal : ExactPrefix original,
      ∃ history : History Step (initial original) terminal,
        ¬terminal.current.Obstruction ∧
        history.length + terminal.current.potential ≤ original.potential ∧
        ExactMeetSupport original.source terminal.current.source
          terminal.reduct := by
  obtain ⟨terminal,h,ht,hbound,_,_⟩ := terminalisation original
  refine ⟨terminal,h,ht,hbound,?_⟩
  exact history_meet_support h
    (ExactMeetSupport.identity original.source)

end
end CCO.ExactEPGeometry.CertifiedGateTower
