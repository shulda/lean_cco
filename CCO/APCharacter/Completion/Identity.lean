import CCO.RawWords
import CCO.Finite

/-! The old atomic equality test used before identifying nonadjacent vertices.
The identity here is literal real equality, never the whole gate kernel. -/
universe u v w
namespace CCO.APCharacter.Completion
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

/-- C23: a closed two-edge walk through the common neighbour forces the
original incident atom names to coincide. The witness may identify its ends. -/
theorem duplicate_labels_equal {i j : ι} (a b : S.Atom i j)
    (hId : ∃ x : X i, TRel.comp (S.atomRel a) (S.atomRel (S.conv b)) x x) :
    a = b := by
  obtain ⟨x,z,ha,hb⟩ := hId
  have hb' : S.colour x z = some b := (S.colour_swap x z b).mpr hb
  exact Option.some.inj (ha.symm.trans hb')

/-- Conversely equal labels admit a genuine closed two-edge walk by their
realization in the original source, independently of AP, CCO or homogeneity. -/
theorem duplicate_labels_equal_iff {i j : ι} (a b : S.Atom i j) :
    a = b ↔ ∃ x : X i, TRel.comp (S.atomRel a) (S.atomRel (S.conv b)) x x := by
  constructor
  · intro h
    subst b
    obtain ⟨x,z,hxz⟩ := S.realized a
    exact ⟨x,z,hxz,(S.colour_swap x z a).mp hxz⟩
  · exact duplicate_labels_equal S a b

/-- C24's loop check: identifying two nonadjacent vertices cannot turn an
old specified diversity edge into a loop. -/
theorem no_loop_after_identification {V W : Type*} {D : PartialDiagram S V}
    (q : V → W) (x y : V) (hxy : x ≠ y)
    (hFibre : ∀ a b, q a = q b → a = b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x))
    (hMissing : D.edge x y hxy = none) {a b : V} (hab : a ≠ b)
    (c : S.Atom (D.vertexSort a) (D.vertexSort b))
    (hc : D.edge a b hab = some c) : q a ≠ q b := by
  intro he
  rcases hFibre a b he with heq | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hab heq
  · rw [hMissing] at hc
    cases hc
  · have hc' := (D.edge_reverse _ _ hab c).mp hc
    rw [hMissing] at hc'
    cases hc'

end CCO.APCharacter.Completion
