import CCO.TerminalHiddenHN.ReadoutExpansion
import CCO.TerminalHiddenHN.ReadoutRamsey

/-! Conditional Ramsey transfer for the finite actual comparison language.
Only this implication consumes ordered hidden Ramsey; the finite language,
restriction and reasonableness are already constructed independently. -/

universe u v w r l k
namespace CCO.TerminalHiddenHN.RealInterpretation
open CCO.UnaryFreshFrames
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : CCO.AtomicSource.{u,v,w} ι X}
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable {U : Language.{max u l}} {V : Type k} {P : Structure U V}
variable (D : RealInterpretation (G := G) S U P) (H : CCO.HomogeneousSource S G)

/-- The actual hidden Ramsey input is discharged separately by the
terminal HN theorem. The readout transfer itself assumes only that input
on the SAME whole age, including arbitrary orphan-bearing hosts. -/
theorem readoutExpansion_ramsey
    (ramsey : CCO.FullCode.HasHiddenRamsey D.orderedAge) :
    (D.readoutExpansion H).Ramsey := by
  intro A B a b n hn
  obtain ⟨C,c,hC⟩ := D.readout_ramsey H ramsey A B a b n hn
  refine ⟨C,c,?_⟩
  intro colour
  obtain ⟨g,shade,hg⟩ := hC (fun f => colour (D.readoutToRelational H f))
  refine ⟨D.readoutToRelational H g,?_⟩
  intro f₁ f₂
  have h₁ := hg (D.relationalToReadout H f₁)
  have h₂ := hg (D.relationalToReadout H f₂)
  have eq₁ : D.readoutToRelational H (g.comp H (D.relationalToReadout H f₁)) =
      (D.readoutToRelational H g).comp f₁ := by
    ext x
    rfl
  have eq₂ : D.readoutToRelational H (g.comp H (D.relationalToReadout H f₂)) =
      (D.readoutToRelational H g).comp f₂ := by
    ext x
    rfl
  exact (congrArg colour eq₁).symm.trans (h₁.trans (h₂.symm.trans (congrArg colour eq₂)))

/-- Standalone source readout theorem: finite relationality and literal
precompact reasonableness use only A01/A02; Ramsey uses exactly A05. -/
theorem hasFiniteRelationalRamseyExpansion_of_hiddenRamsey
    (ramsey : CCO.FullCode.HasHiddenRamsey D.orderedAge) :
    CCO.TerminalHiddenHN.HasFiniteRelationalRamseyExpansion S :=
  ⟨D.readoutExpansion H,D.readoutExpansion_reasonable H,D.readoutExpansion_ramsey H ramsey⟩


end
end CCO.TerminalHiddenHN.RealInterpretation
