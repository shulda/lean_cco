import CCO.AclOwners.ClosedAmalgamation
import CCO.AclOwners.AnchorTest

/-! The unsafe concentration proof uses strong amalgamation of the three
actual absolute closures. Complete original spokes and exact meet readout
force the NEW cross edge to keep its literal OLD unsafe colour. -/
universe v w t
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)
variable (normalized : NoFiniteExactKernel S)
include normalized

/-- C13: actual unsafe pairs lie in one of every two DISTINCT original
correspondences. No SAP over arbitrary finite bases is assumed. -/
theorem unsafe_pair_concentrated (safe : Set (Atom S))
    (amalgamate : StrongClosedAmalgamation S G safe)
    (D E : Direction S) (hne : D ≠ E)
    {x y : M} {a : Atom S} (hcol : col S x y = some a) (hunsafe : a ∉ safe) :
    oldCorrespondence S H cco D x y ∨ oldCorrespondence S H cco E x y := by
  classical
  by_contra hn
  have hnD : ¬ oldCorrespondence S H cco D x y := fun h => hn (Or.inl h)
  have hnE : ¬ oldCorrespondence S H cco E x y := fun h => hn (Or.inr h)
  obtain ⟨u,hxu,hnotxu⟩ := direction_point_outside_packet S H D x
  obtain ⟨v,hyv,hnotyv⟩ := direction_point_outside_packet S H E y
  have hDyv : oldCorrespondence S H cco D y v :=
    direction_le_other_correspondence S H cco normalized D E hne hyv
  have hExu : oldCorrespondence S H cco E x u :=
    direction_le_other_correspondence S H cco normalized E D hne.symm hxu
  have hnDxv : ¬ oldCorrespondence S H cco D x v := fun h =>
    hnD ((oldCorrespondence S H cco D).val.trans h ((oldCorrespondence S H cco D).val.symm hDyv))
  have hnEyu : ¬ oldCorrespondence S H cco E y u := fun h =>
    hnE ((oldCorrespondence S H cco E).val.trans hExu ((oldCorrespondence S H cco E).val.symm h))
  have hnx : x ∉ Acl G ({u,v} : Finset M) := fun h =>
    hnDxv ((anchor_algebraic_iff S H cco normalized D hxu hnotxu).mp h)
  have hny : y ∉ Acl G ({u,v} : Finset M) := by
    intro h
    apply hnEyu
    apply (anchor_algebraic_iff S H cco normalized E hyv hnotyv).mp
    simpa only [Finset.pair_comm] using h
  let A := closureFinset S H {u,v}
  let L := closureFinset S H (insert x {u,v})
  let R := closureFinset S H (insert y {u,v})
  have hAL : A ⊆ L := closureFinset_mono S H (Finset.subset_insert _ _)
  have hAR : A ⊆ R := closureFinset_mono S H (Finset.subset_insert _ _)
  have huA : u ∈ A := subset_closureFinset S H _ (by simp)
  have hvA : v ∈ A := subset_closureFinset S H _ (by simp)
  have hxL : x ∈ L := subset_closureFinset S H _ (by simp)
  have hyR : y ∈ R := subset_closureFinset S H _ (by simp)
  have hxA : x ∉ A := fun h => hnx ((mem_closureFinset S H _ x).mp h)
  have hyA : y ∉ A := fun h => hny ((mem_closureFinset S H _ y).mp h)
  obtain ⟨f,g,hagree,_,hcross⟩ := amalgamate A L R
    (closed_closureFinset S H _) (closed_closureFinset S H _) (closed_closureFinset S H _)
    hAL hAR
  have huy : col S (f.map u) (g.map y) = col S u y := by
    rw [hagree u huA]
    exact g.colours u (hAR huA) y hyR
  have hvy : col S (f.map v) (g.map y) = col S v y := by
    rw [hagree v hvA]
    exact g.colours v (hAR hvA) y hyR
  have hread := fine_colour_of_two_anchor_spokes S H cco D.val E.val
    (direction_exact S H cco D) (direction_exact S H cco E)
    (distinct_directions_meet_identity S H cco normalized D E hne)
    x y u v (f.map x) (g.map y) (f.map u) (f.map v) hxu hyv
    (f.colours x hxL u (hAL huA)) huy (f.colours x hxL v (hAL hvA)) hvy
  obtain ⟨b,hbs,hb⟩ := hcross x hxL hxA y hyR hyA
  have hba : b = a := Option.some.inj (hb.symm.trans (hread.trans hcol))
  exact hunsafe (hba ▸ hbs)

def UnsafeClique (safe : Set (Atom S)) (Z : Set M) : Prop :=
  ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → ∃ a : Atom S, col S x y = some a ∧ a ∉ safe

/-- C14, including empty and singleton cliques. -/
theorem unsafe_clique_two_correspondences (safe : Set (Atom S))
    (amalgamate : StrongClosedAmalgamation S G safe) (Z : Set M) (hZ : UnsafeClique S safe Z)
    (D E : Direction S) (hne : D ≠ E) :
    Concentrated (oldCorrespondence S H cco D).val Z ∨
      Concentrated (oldCorrespondence S H cco E).val Z := by
  apply two_equivalence_rook
  intro x hx y hy
  by_cases he : x = y
  · exact Or.inl (he ▸ (oldCorrespondence S H cco D).val.refl x)
  · obtain ⟨a,ha,hs⟩ := hZ x hx y hy he
    exact unsafe_pair_concentrated S H cco normalized safe amalgamate D E hne ha hs

/-- The SAME selected clique root supplies all nonexceptional classes.
Only this palette-conditional branch uses closed safe amalgamation. -/
theorem unsafe_clique_one_exception [Nonempty (Direction S)] (safe : Set (Atom S))
    (amalgamate : StrongClosedAmalgamation S G safe) (Z : Set M) (hZ : UnsafeClique S safe Z) :
    ∃ D₀ : Direction S, ∀ E : Direction S, E ≠ D₀ → ∀ z ∈ Z,
      Z ⊆ {x | oldCorrespondence S H cco E z x} :=
  all_but_one_root_classes (fun D => (oldCorrespondence S H cco D).val) Z
    (fun D E hne => unsafe_clique_two_correspondences S H cco normalized safe amalgamate Z hZ D E hne)

end CCO.AclOwners
