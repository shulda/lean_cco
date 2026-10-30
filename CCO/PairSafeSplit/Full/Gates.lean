import CCO.OrbitalCover.Parity
import CCO.APCharacter.GateSource
import CCO.APCharacter.SeedSource
import CCO.RawExact.DiagramReindex

/-! B047 C06–C13: visible original parity, an actual original maximal
complement, detecting groupoid character and legal global real markings. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.PairSafeSplit.Full
open APCharacter RigidGroupoid.Geometry RigidGroupoid.Phase
open ParityHasse.Original
noncomputable section
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G) {i : ι}

/-- The displayed parity and maximality facts refer to the original source.
The chosen character is constructed below, not supplied as a field. -/
structure ParityGateData (c : S.Atom i i) (a : X i) where
  even_nontrivial : (⊥ : ColourEq S i) < evenColourEq S H c
  parity_cover : evenColourEq S H c ⋖ connectivityColourEq S H c
  parity_index : relativeIndex (evenColourEq S H c).val
    (connectivityColourEq S H c).val a = 2
  maximal : ParityHasse.Relative.MaximalGate S H (evenColourEq S H c)
    (connectivityColourEq S H c)
  named : ParityHasse.Relative.NamedGateData S H (evenColourEq S H c)
    (connectivityColourEq S H c) maximal

namespace ParityGateData
variable {S H} {c : S.Atom i i} {a : X i} (D : ParityGateData S H c a)

def kernel : Kernel S i := APCharacter.MaximalGate.kernel S H _ _ D.maximal

theorem root_kernel_nontrivial : (⊥ : ColourEq S i) < D.maximal.kernel :=
  lt_of_lt_of_le D.even_nontrivial D.maximal.maximal.1.2.1

/-- The actual maximal gate supplies all groupoid/character providers. -/
def phase (cco : SemanticCCO.{u,v,max u v,w} S) :
    SourcePhase S H (exactCalculus_of_homogeneous_CCO S H cco) D.kernel :=
  Classical.choice (APCharacter.MaximalGate.actual_phase S H
    (exactCalculus_of_homogeneous_CCO S H cco) _ _ D.maximal)

end ParityGateData

/-- A real residual interval constructs the actual original parity gate
with Y>Id, not merely an arbitrary quotient two-cover or supplied character. -/
theorem exists_parity_gate (cco : SemanticCCO.{u,v,max u v,w} S) (sap : AgeSAP S)
    (E F : ColourEq S i) (hEF : E < F) (a : X i)
    [Finite (RelativeClass E.val F.val a)] :
    ∃ c : S.Atom i i, Nonempty (ParityGateData S H c a) ∧
      connectivityColourEq S H c ≤ F ∧ ¬connectivityColourEq S H c ≤ E := by
  classical
  have ex : ∃ x y, F x y ∧ ¬E x y := by
    by_contra hn
    apply hEF.not_ge
    intro x y hF
    exact Classical.byContradiction fun hE => hn ⟨x,y,hF,hE⟩
  obtain ⟨x,y,hF,hE⟩ := ex
  have hn : S.colour x y ≠ none := by
    intro hc
    have he : x = y := by
      simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using (S.colour_none_iff x y).mp hc
    exact hE (he ▸ E.val.refl y)
  obtain ⟨c,hc⟩ := Option.ne_none_iff_exists'.mp hn
  have hFE : ∀ u v, S.atomRel c u v → F u v ∧ ¬E u v := by
    intro u v huv
    have heq : S.colour x y = S.colour u v := hc.trans huv.symm
    exact ⟨(F.property x y u v heq).mp hF,fun he => hE ((E.property x y u v heq).mpr he)⟩
  have cco0 : SemanticCCO.{u,v,0,w} S := semanticCCO_change_universe S cco
  obtain ⟨hcover,hidx,hUF,hnot,⟨EY,EO,hEY,hEO⟩,⟨p,q,hpq,hYpq⟩,_⟩ :=
    OrbitalCover.orbital_parity S H cco0 sap E F a c hFE
  let Y := evenColourEq S H c
  let U := connectivityColourEq S H c
  have hY : ParityHasse.Relative.Exact S Y := by
    refine ⟨EY,?_⟩
    funext x y
    exact propext (hEY x y)
  have hO : ParityHasse.Relative.Exact S (ParityHasse.Relative.odd Y.val U.val) := by
    refine ⟨EO,?_⟩
    funext x y
    exact propext ((hEO x y).trans (OrbitalCover.source_odd_sheet S H cco0 E F a c hFE x y))
  obtain ⟨M,hM,_⟩ := ParityHasse.Relative.source_maximal_exact_gate S H cco Y U hY hcover.le hO a hidx
  have hYne : (⊥ : ColourEq S i) ≠ Y := by
    intro he
    have hh : (⊥ : ColourEq S i) p q := he ▸ hYpq
    exact hpq hh
  exact ⟨c,⟨⟨lt_of_le_of_ne bot_le hYne,hcover,hidx,M,hM⟩⟩,hUF,hnot⟩

section Markings
variable {S H} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
variable (P : SourcePhase S H C A)

/-- Actual free-action seeds produce a legal global marking of real M.
This theorem asserts legality, never homogeneity of an arbitrary seed. -/
theorem legal_global_marking : ∃ mark, P.masks.GlobalMarking mark := by
  letI := Reached.groupoid H C (A := A)
  obtain ⟨mark,hm⟩ := actual_global_marking S H C A P.character
  exact ⟨originalMarking S H C A mark,P.original_global_marking mark hm⟩

theorem finite_legal_marking : P.masks.FiniteSeedExtension := P.finite_seed_extension

end Markings
end
end CCO.PairSafeSplit.Full
