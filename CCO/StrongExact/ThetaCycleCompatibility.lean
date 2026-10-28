import CCO.StrongExact.ThetaWholeReadout

/-! Exact remaining C07 source seam: the constructed actual theta
already has single-valued original edges and whole-word readout.
Only pairwise-compatible simple-cycle homomorphisms remain open. -/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

def ThetaCycleCompatibility : Prop :=
  ∀ {i j : ι} (ws : List (PositiveWord S i j)),
    PairwiseWordProfiles S ws →
    3 ≤ ws.length →
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws) →
    ∀ C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram), CycleHom C

theorem hardThetaProvider_of_cycleCompatibility
    (h : ThetaCycleCompatibility S) : HardThetaProvider S := by
  intro i j ws hPair hLength hLong
  exact ⟨thetaEdgesOfLong S ws hLong,
    h ws hPair hLength hLong,
    thetaEdgesOfLong_representsWords S ws hLong⟩

end CCO.StrongExact
