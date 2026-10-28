import CCO.RealClosure.Bounds.PacketBounds

/-! Empty real bases and singleton closure. The rank-one consequence uses
bounded character, independently of the sharper exponential palette count. -/
universe v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original RealHull.Geometry RealHull.Canonical
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M)) [DecidableEq M]
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)

include H in
theorem orbitOver_empty (x : M) : orbitOver G ∅ x = Set.univ := by
  ext y
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H () x y
    exact ⟨g,fun a ha => False.elim (Finset.notMem_empty _ ha),hg⟩

include H in
theorem acl_empty_infinite [Infinite M] : Acl G (∅ : Finset M) = ∅ := by
  ext x
  change (orbitOver G ∅ x).Finite ↔ False
  rw [orbitOver_empty S H]
  exact ⟨fun h => Set.infinite_univ h,False.elim⟩

/-- C11: singleton real algebraic closure is the ACTUAL greatest finite
packet class, including its named parameter by true equality. -/
theorem acl_singleton (cco : SemanticCCO.{0,v,0,w} S) (a : M) :
    Acl G {a} = {x : M | finitePacket S H a x} := by
  classical
  ext x
  constructor
  · intro hx
    by_cases hxa : x = a
    · subst x
      exact (finitePacket S H).val.refl a
    · have hxA : x ∉ ({a} : Finset M) := by simpa only [Finset.mem_singleton] using hxa
      let q := actualSpokes S {a} x hxA
      let aa : ↥({a} : Finset M) := ⟨a,Finset.mem_singleton_self _⟩
      have hcanon := (algebraic_iff_canonical_finite S H cco {a} x hxA).mp hx
      have hle : gammaEq S (q aa) ≤ supportEquiv S (canonicalSupport S {a} q) := by
        intro u v huv
        apply (canonical_equiv_iff S {a} q u v).mpr
        intro b
        have hb : b = aa := Subtype.ext (Finset.mem_singleton.mp b.property)
        rw [hb]
        exact huv
      have hγF := le_finitePacket S H (gammaEq S (q aa)) (finiteClasses_of_le S hle hcanon)
      exact (finitePacket S H).val.symm (hγF (fibre_anchor_connected S {a} q
        (actualFibrePoint S {a} x hxA) aa))
  · intro hax
    exact packetClosure_subset_acl S H {a} ⟨a,Finset.mem_singleton_self _,hax⟩

include H in
theorem singleton_algebraic_iff_gamma_finite (cco : SemanticCCO.{0,v,0,w} S)
    (a x : M) (hxa : x ≠ a) :
    x ∈ Acl G {a} ↔ FiniteClasses S
      (gammaEq S (actualSpokes S {a} x (by simpa only [Finset.mem_singleton] using hxa)
        ⟨a,Finset.mem_singleton_self _⟩)) := by
  let hxA : x ∉ ({a} : Finset M) := by simpa only [Finset.mem_singleton] using hxa
  let q := actualSpokes S {a} x hxA
  have heq : supportEquiv S (canonicalSupport S {a} q) =
      gammaEq S (q ⟨a,Finset.mem_singleton_self _⟩) := by
    apply ColourEq.ext
    intro u v
    rw [canonical_equiv_iff]
    constructor
    · exact fun h => h ⟨a,Finset.mem_singleton_self _⟩
    · intro h b
      have hb : b = (⟨a,Finset.mem_singleton_self _⟩ : ↥({a} : Finset M)) :=
        Subtype.ext (Finset.mem_singleton.mp b.property)
      rw [hb]
      exact h
  exact (algebraic_iff_canonical_finite S H cco {a} x hxA).trans (by rw [heq])

/-- When r=1 the bounded real character collapses to singleton packet closure. -/
theorem acl_rank_one (cco : SemanticCCO.{0,v,0,w} S) [Infinite M]
    (hr : directionCount S = 1) (A : Finset M) : Acl G A = packetClosure S H A := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨B,hBA,hB,hxB⟩ := bounded_character S H cco A hx
    have hBne : B.Nonempty := by
      by_contra hn
      have hBe : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      rw [hBe,acl_empty_infinite S H] at hxB
      exact hxB
    obtain ⟨a,ha⟩ := hBne
    have hBsingle : B = {a} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      exact ⟨ha,fun b hb => (Finset.card_le_one.mp (by simpa only [hr] using hB)) b hb a ha⟩
    have hxFa : finitePacket S H a x := by
      rw [hBsingle,acl_singleton S H cco] at hxB
      exact hxB
    exact ⟨a,hBA ha,hxFa⟩
  · exact packetClosure_subset_acl S H A
end CCO.RealClosure.Bounds
