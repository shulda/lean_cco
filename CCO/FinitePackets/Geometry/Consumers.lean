import CCO.FinitePackets.Geometry.ExactCutSource
import CCO.FinitePackets.Geometry.CrossProjection

/-! Downstream source consumers and actual finite/identity/Top boundaries.
The source quotient consumer is kept separate from the elementary lattice
and interval conclusions, with exactly the countability it needs. -/
universe v w t z
namespace CCO.FinitePackets.Geometry
open CCO.ParityHasse.Original CCO.RealHull.Geometry
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

theorem loopAtoms_bottom_empty : loopAtoms S (⊥ : ColourEq S ()) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨x,y,hxy⟩ := colour_realized S (some a)
  have he : x = y := ((mem_loopAtoms S ⊥ a).mp ha).2 x y hxy
  have hn : col S x y = none := (col_none S x y).mpr he
  rw [hn] at hxy
  cases hxy

variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)

include H in
theorem bottom_core_actual_empty_word :
    core S (⊥ : ColourEq S ()) = ⊥ ∧
      RawWord.relation S (.nil ()) = (core S (⊥ : ColourEq S ())).val.r :=
  empty_core_actual_empty_word S H ⊥ (loopAtoms_bottom_empty S)

theorem sigma_of_finite_sort [Finite M] (J : ColourEq S ()) : sigma S H J = ⊤ := by
  have hfin : FiniteIndex S J (⊤ : ColourEq S ()) := by
    intro x
    unfold RelativeClass
    infer_instance
  have ht : sigma S H (⊤ : ColourEq S ()) = ⊤ := le_antisymm le_top (le_sigma S H ⊤)
  exact (sigma_eq_of_finiteIndex S H le_top hfin).trans ht

theorem finite_class_packet (J : ColourEq S ()) :
    sigma S H J = sigma S H (⊥ : ColourEq S ()) ↔
      ∀ x, Finite (ClassPoint S () J x) := by
  rw [← finiteIndex_bottom_iff_finite_classes S J]
  exact eq_comm.trans (sigma_eq_iff_finiteIndex S H bot_le)

variable (cco : SemanticCCO.{0,v,0,w} S)
include H cco

theorem packet_core_isLeast (J : ColourEq S ()) :
    IsLeast {L : ColourEq S () | sigma S H L = sigma S H J} (core S J) := by
  refine ⟨sigma_core S H cco J,?_⟩
  intro L hL
  exact ((packet_interval S H cco J L).mp hL).1

theorem core_of_finite_sort [Finite M] (J : ColourEq S ()) : core S J = ⊥ := by
  apply finite_class_core_bottom S H cco J
  intro x
  unfold RelativeClass
  infer_instance

/-- Genuine consumer of all three distinct outputs: elementary interval,
positive exact kernel, and the separately instantiated actual quotient source. -/
theorem actual_minimal_cut_package [Countable M]
    (E : ColourEq S ()) (hE : MinimalInfiniteCut S E) :
    E ≠ ⊥ ∧ E = core S E ∧
      Set.Iic E = Set.Iic (E ⊓ sigma S H (⊥ : ColourEq S ())) ∪ {E} ∧
      (∃ word : PositiveWord S () (), PositiveWord.represented S word = E.val.r) ∧
      RawExact.CanonicalQuotients.SourceProperties.{v,w,t,z} S H
        (minimalCutQuotientData S H cco E hE) :=
  ⟨cut_nonidentity S hE,minimal_cut_eq_core S H cco hE,
    cut_lower_interval S hE (sigma_bottom_spec S H),minimal_cut_positive_word S H cco hE,
    minimal_cut_actual_quotient_source S H cco E hE⟩

/-- E=Top is allowed. Its ACTUAL quotient is a singleton and still carries
the full source-property record; a proper-top cut premise is never added. -/
theorem top_cut_actual_singleton_source [Countable M]
    (hTop : MinimalInfiniteCut S (⊤ : ColourEq S ())) :
    Subsingleton (Quotient (⊤ : ColourEq S ()).val) ∧
      RawExact.CanonicalQuotients.SourceProperties.{v,w,t,z} S H
        (minimalCutQuotientData S H cco ⊤ hTop) := by
  refine ⟨?_,minimal_cut_actual_quotient_source S H cco ⊤ hTop⟩
  constructor
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro x y
  exact Quotient.sound trivial

end CCO.FinitePackets.Geometry
