import CCO.FinitePackets.Geometry.Sigma
import CCO.FinitePackets.Geometry.CoreWords
import CCO.FinitePackets.Geometry.LoopCriterion

/-! Every Sigma-packet is its ENTIRE original closed interval. No endpoint
exactness or distributivity is assumed; only its actual core is proved exact. -/
universe v w t
namespace CCO.FinitePackets.Geometry
open CCO.ParityHasse.Original CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,0,w} S)
include H cco

theorem finiteIndex_core (J : ColourEq S ()) : FiniteIndex S (core S J) J :=
  (finiteIndex_iff_no_looped S H cco (core S J) J (core_le S J)).mpr
    (fun _ ha hJ => looped_atom_core S ha hJ)

theorem core_eq_of_finiteIndex {J K : ColourEq S ()} (hJK : J ≤ K)
    (hfin : FiniteIndex S J K) : core S J = core S K := by
  apply core_eq_of_loopGenerators_eq S
  ext a
  constructor
  · rintro ⟨ha,hJ⟩
    exact ⟨ha,atomBelow_mono S hJK hJ⟩
  · rintro ⟨ha,hK⟩
    exact ⟨ha,finiteIndex_no_looped S H cco J K hfin a ha hK⟩

theorem sigma_core (J : ColourEq S ()) : sigma S H (core S J) = sigma S H J :=
  sigma_eq_of_finiteIndex S H (core_le S J) (finiteIndex_core S H cco J)

theorem core_sigma (J : ColourEq S ()) : core S (sigma S H J) = core S J :=
  (core_eq_of_finiteIndex S H cco (le_sigma S H J) (finiteIndex_sigma S H J)).symm

@[simp] theorem core_idempotent (J : ColourEq S ()) : core S (core S J) = core S J :=
  core_eq_of_finiteIndex S H cco (core_le S J) (finiteIndex_core S H cco J)

theorem same_sigma_same_core {J K : ColourEq S ()}
    (h : sigma S H J = sigma S H K) : core S J = core S K := by
  rw [← core_sigma S H cco J,← core_sigma S H cco K,h]

/-- C08 includes both Sigma inclusions. The finite total interval passes
through L, so closure equality follows from actual finite quotient towers. -/
theorem packet_interval (J L : ColourEq S ()) :
    sigma S H L = sigma S H J ↔ core S J ≤ L ∧ L ≤ sigma S H J := by
  constructor
  · intro h
    have hc : core S L = core S J := same_sigma_same_core S H cco h
    exact ⟨hc ▸ core_le S L,h ▸ le_sigma S H L⟩
  · rintro ⟨hcore,hL⟩
    have htot : FiniteIndex S (core S J) (sigma S H J) := by
      rw [← sigma_core S H cco J]
      exact finiteIndex_sigma S H (core S J)
    have hfin : FiniteIndex S L (sigma S H J) := finiteIndex_upper S hcore htot
    exact (sigma_eq_of_finiteIndex S H hL hfin).trans (sigma_idempotent S H J)

theorem packet_unique_least (J : ColourEq S ()) :
    sigma S H (core S J) = sigma S H J ∧
      ∀ L : ColourEq S (), sigma S H L = sigma S H J → core S J ≤ L :=
  ⟨sigma_core S H cco J,fun L h => ((packet_interval S H cco J L).mp h).1⟩

theorem finite_class_core_bottom (J : ColourEq S ()) (hfin : FiniteIndex S ⊥ J) :
    core S J = ⊥ := by
  have hc : core S (⊥ : ColourEq S ()) = ⊥ := le_antisymm (core_le S ⊥) bot_le
  rw [← core_eq_of_finiteIndex S H cco bot_le hfin,hc]

end CCO.FinitePackets.Geometry
