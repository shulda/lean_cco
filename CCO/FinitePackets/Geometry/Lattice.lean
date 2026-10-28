import CCO.FinitePackets.Geometry.Basic

/-! Full symmetric original lattice calculus and actual modular rerouting.
No endpoint exactness, distributivity, finite-index, CCO or cut premise. -/
universe u v w t
namespace CCO.FinitePackets.Geometry
open CCO.ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)]
variable (H : HomogeneousSource S G)

theorem full_lattice_finite : Finite (ColourEq S i) := inferInstance

include H in
theorem actual_invariant_commutation {R T : X i → X i → Prop}
    (hR : ColourInvariant S i R) (hT : ColourInvariant S i T) :
    RawSymmetric.compose R T = RawSymmetric.compose T R :=
  invariant_relations_commute S H hR hT

theorem actual_join_iff (E F : ColourEq S i) (x y : X i) :
    ColourEq.join S H E F x y ↔ ∃ z, E x z ∧ F z y :=
  sup_relation_iff S H E F x y

/-- C15: a represented E-then-J path whose endpoints are K-related can
be rerouted with its E-step inside K. This holds for EVERY original E. -/
theorem modular_path (E J K : ColourEq S i) (hJK : J ≤ K) :
    K ⊓ ColourEq.join S H E J = ColourEq.join S H J (E ⊓ K) := by
  apply ColourEq.ext
  intro x z
  constructor
  · rintro ⟨hxz,hpath⟩
    obtain ⟨y,hxy,hyz⟩ := (actual_join_iff S H E J x z).mp hpath
    have hKy : K x y := K.val.trans hxz (K.val.symm (hJK hyz))
    have hw : ColourEq.join S H (E ⊓ K) J x z :=
      (actual_join_iff S H (E ⊓ K) J x z).mpr ⟨y,⟨hxy,hKy⟩,hyz⟩
    change (J.val ⊔ (E ⊓ K).val) x z
    rw [sup_comm]
    exact hw
  · intro hpath
    obtain ⟨y,hxy,hyz⟩ := (actual_join_iff S H J (E ⊓ K) x z).mp hpath
    refine ⟨K.val.trans (hJK hxy) hyz.2,?_⟩
    change (E.val ⊔ J.val) x z
    rw [sup_comm]
    exact (actual_join_iff S H J E x z).mpr ⟨y,hxy,hyz.1⟩

end CCO.FinitePackets.Geometry
