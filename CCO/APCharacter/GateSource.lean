import CCO.APCharacter.Calculus

/-! Maximal gates are produced by the accepted original source theorem.
Their odd relation is converted to an actual full exact isotropy arrow;
character existence and transported dominance are then constructed. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)
variable {i : ι}

theorem cast_loop_dominant {K K' : Kernel S i} (e : K = K') (t : Arrow S K K)
    (hd : Dominant K t) : Dominant K' (kernelLoopCast S e t) := by
  cases e
  exact hd

theorem sourcePhase_of_dominant (K : Kernel S i) (t : Arrow S K K)
    (hne : t ≠ Arrow.id K) (hd : Dominant K t) : Nonempty (SourcePhase S H C K) := by
  let e := Reached.root_kernel H C (A := K)
  let t₀ := kernelLoopCast S e.symm t
  exact SourcePhase.exists_of_odd t₀ (kernelLoopCast_nonidentity S e.symm t hne)
    (cast_loop_dominant S e.symm t hd)

namespace MaximalGate
open ParityHasse.Original ParityHasse.Relative
variable (Y U : ColourEq S i) (M : ParityHasse.Relative.MaximalGate S H Y U)

def kernel : Kernel S i := ⟨M.kernel.val,M.maximal.1.1⟩

def oddArrow : Arrow S (kernel S H Y U M) (kernel S H Y U M) where
  rel := gate S M.kernel U Y
  exact := M.exact
  left := M.bisaturated.1
  right := M.bisaturated.2
  source := by
    change TRel.comp (gate S M.kernel U Y) (TRel.converse (gate S M.kernel U Y)) = _
    rw [FullExact.same_sort_converse S H M.exact]
    exact M.square
  target := by
    change TRel.comp (TRel.converse (gate S M.kernel U Y)) (gate S M.kernel U Y) = _
    rw [FullExact.same_sort_converse S H M.exact]
    exact M.square

theorem odd_nonidentity : oddArrow S H Y U M ≠ Arrow.id (kernel S H Y U M) := by
  intro he
  obtain ⟨x,y,hxy⟩ := M.exact.nonempty
  have hk : M.kernel x y := by
    have hr := congrFun (congrFun (congrArg Arrow.rel he) x) y
    exact Eq.mp hr hxy
  exact M.disjoint x y hxy hk

theorem odd_dominant : Dominant (kernel S H Y U M) (oddArrow S H Y U M) := by
  intro Z hZ x y hxy
  let Zc : ColourEq S i := ⟨Z.setoid,ParityHasse.Relative.Exact.colourInvariant S H Z.exact⟩
  have hs : M.kernel < Zc := by
    refine lt_iff_le_and_ne.mpr ⟨hZ.le,?_⟩
    intro he
    apply hZ.ne
    exact Kernel.ext_setoid S (congrArg Subtype.val he)
  exact M.dominant Zc Z.exact hs x y hxy

theorem actual_phase : Nonempty (SourcePhase S H C (kernel S H Y U M)) :=
  sourcePhase_of_dominant S H C (kernel S H Y U M) (oddArrow S H Y U M)
    (odd_nonidentity S H Y U M) (odd_dominant S H Y U M)

end MaximalGate

/-- Source-facing maximal gate and actual character. No caller supplies a
character, a groupoid, fork totality, or phase primality. -/
theorem actual_maximal_character (cco : SemanticCCO.{u,v,max u v,w} S)
    (Y U : ParityHasse.Original.ColourEq S i)
    (hY : ParityHasse.Relative.Exact S Y) (hYU : Y ≤ U)
    (hO : ParityHasse.Relative.Exact S (ParityHasse.Relative.odd Y.val U.val))
    (a : X i) (htwo : ParityHasse.Original.relativeIndex Y.val U.val a = 2) :
    ∃ K : Kernel S i, Nonempty (SourcePhase S H C K) := by
  obtain ⟨M⟩ := ParityHasse.Relative.exists_maximalGate S H cco Y U hY hYU hO a htwo
  exact ⟨MaximalGate.kernel S H Y U M,MaximalGate.actual_phase S H C Y U M⟩

end
end CCO.APCharacter
