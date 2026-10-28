import CCO.SIR.Negative.Source

/-! Source-facing consumers: an actual triangle-free graph obstructing
three-colourability, and exclusion of a full invariant cover of index three. -/
universe u v w t
namespace CCO.ParityHasse.Original

/-- A genuine finite connected triangle-free graph has a monochromatic
edge under EVERY three-colouring, from the proved finite probability source. -/
theorem exists_triangle_free_three_colour_obstruction :
    Nonempty (Sparse.ConnectedHighGirthChromatic 3 3) :=
  Sparse.connected_high_girth_chromatic_exists (by decide) 3

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- An actual cover of relative index three is impossible; finiteness is
proved from its stated index, not inserted as an additional premise. -/
theorem not_cover_of_index_three (H : HomogeneousSource S G)
    (cco : SemanticCCO.{u,v,0,w} S) (E F : ColourEq S i) (a : X i)
    (hthree : relativeIndex E.val F.val a = 3) : ¬ E ⋖ F := by
  have hpos : 0 < relativeIndex E.val F.val a := by omega
  letI : Finite (RelativeClass E.val F.val a) := (Nat.card_pos_iff.mp hpos).2
  intro hEF
  have htwo := full_relative_hasse S H cco E F hEF a
  omega

/-- The equality interval is correctly retained, including a singleton
original sort: its relative index is 1=2^0 without CCO or SAP. -/
theorem equality_interval_power_zero (E : ColourEq S i) (a : X i) :
    relativeIndex E.val E.val a = 2^0 := by
  simpa using relativeIndex_self E.val a

end CCO.ParityHasse.Original
