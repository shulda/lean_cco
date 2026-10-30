import CCO.StabilizerSAP
import CCO.ParityHasse.Original.OrbitalAlgebra

/-! B047 C55. Original SAP excludes two nontrivial real invariant
equivalences meeting only in logical equality. The proof uses actual
pointwise-stabilizer motion; no algebraicity or quotient-SAP oracle occurs. -/

universe u v w t
namespace CCO.PairSafeSplit.Strong
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

include H sap in
theorem no_unique_crossing {i : ι} (E F : ColourEq S i) (x a b : X i)
    (hE : E x a) (hF : F x b) (hxa : x ≠ a) (hxb : x ≠ b)
    (hMeet : ∀ p q, E p q → F p q → p = q) : False := by
  let B : FiniteInduced (X := X) := {
    vertices := {(⟨i,a⟩ : Sigma X), ⟨i,b⟩}
    finite_vertices := (Set.finite_singleton _).insert _ }
  have hnot : (⟨i,x⟩ : Sigma X) ∉ B.vertices := by
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff,
      Sigma.mk.injEq, heq_eq_eq, true_and]
    exact not_or.mpr ⟨hxa,hxb⟩
  obtain ⟨y,⟨g,hg,hgx⟩,hfresh⟩ := RealAction.orbit_has_fresh_point_of_SAP
    S H sap B (⟨i,x⟩ : Sigma X) hnot {(⟨i,x⟩ : Sigma X)} (Set.finite_singleton _)
  have ha : g • a = a := by
    have hh := hg (⟨i,a⟩ : Sigma X) (Set.mem_insert _ _)
    simpa only [Sigma.smul_mk, Sigma.mk.injEq, heq_eq_eq, true_and] using hh
  have hb : g • b = b := by
    have hh := hg (⟨i,b⟩ : Sigma X) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    simpa only [Sigma.smul_mk, Sigma.mk.injEq, heq_eq_eq, true_and] using hh
  have he : E (g • x) a := by
    simpa only [ha] using colourInvariant_groupInvariant S H E.2 g x a hE
  have hf : F (g • x) b := by
    simpa only [hb] using colourInvariant_groupInvariant S H F.2 g x b hF
  have fixed : x = g • x := hMeet x (g • x)
    (E.val.trans hE (E.val.symm he)) (F.val.trans hF (F.val.symm hf))
  apply hfresh
  rw [← hgx]
  change (⟨i,g • x⟩ : Sigma X) ∈ {(⟨i,x⟩ : Sigma X)}
  rw [← fixed]
  exact Set.mem_singleton _

theorem exists_distinct_related {i : ι} (E : ColourEq S i) (hne : E ≠ ⊥) :
    ∃ x a, E x a ∧ x ≠ a := by
  classical
  by_contra h
  apply hne
  apply ColourEq.ext S i
  intro x y
  constructor
  · intro hxy
    exact Classical.byContradiction (fun hn => h ⟨x,y,hxy,hn⟩)
  · intro hxy
    exact hxy ▸ E.val.refl x

include H sap in
/-- No countability, CCO, exactness, triangle class or finite-index premise. -/
theorem nontrivial_equivalences_meet {i : ι} (E F : ColourEq S i)
    (hE : E ≠ ⊥) (hF : F ≠ ⊥) : E ⊓ F ≠ ⊥ := by
  intro hm
  obtain ⟨x,a,hxa,hne⟩ := exists_distinct_related S E hE
  obtain ⟨p,q,hpq,hpqne⟩ := exists_distinct_related S F hF
  obtain ⟨g,hgx⟩ := S.original_sort_transitive_of_homogeneous H i p x
  have hxb : F x (g • q) := by
    simpa only [hgx] using colourInvariant_groupInvariant S H F.2 g p q hpq
  have hxne : x ≠ g • q := by
    intro he
    exact hpqne (MulAction.injective g (hgx.trans he))
  apply no_unique_crossing S H sap E F x a (g • q) hxa hxb hne hxne
  intro p q hp hq
  have hh : (E ⊓ F) p q := ⟨hp,hq⟩
  rw [hm] at hh
  exact hh

end CCO.PairSafeSplit.Strong
