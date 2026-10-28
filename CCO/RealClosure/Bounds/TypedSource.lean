import CCO.RealClosure.Bounds.SortRestriction
import CCO.RealClosure.Bounds.SourceCore
import CCO.RealClosure.Bounds.Growth

/-! The selected named original sort retains its SAME ambient automorphism
G in every real closure, finite-packet and palette-count source instance.
No extension of arbitrary automorphisms of a one-sort reduct is asserted. -/
universe u v w t
namespace CCO.RealClosure.Bounds
open ParityHasse.Original RealHull.Geometry
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X) (i : ι)
variable {G : Type t} [Group G] [∀ j, MulAction G (X j)] (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{u,v,0,w} S)

include H cco in
/-- Actual positive-direction words transport to ORIGINAL typed RAW words. -/
theorem named_sort_direction_raw_word (D : Direction (sortSource S i)) :
    ∃ word : RawWord S i i, RawWord.relation S word = D.val.val.r := by
  obtain ⟨p,n,hn⟩ := direction_positive_word (sortSource S i) (sortSource_homogeneous S i H)
    (sortSource_semanticCCO S i cco) D
  exact ⟨liftSortWord S i (RealHull.Canonical.positiveEvenWord (sortSource S i) p n),
    (liftSortWord_relation S i _).trans hn⟩

include H cco in
/-- Full RAW exactness here concerns the original source's actual words. -/
theorem named_sort_direction_exact (D : Direction (sortSource S i)) :
    ExactCRT.IsExactEq S (i := i) D.val.val := by
  obtain ⟨word,hw⟩ := named_sort_direction_raw_word S i H cco D
  obtain ⟨x⟩ := S.nonemptySort i
  have hne : TRel.Nonempty (RawWord.relation S word) := by
    refine ⟨x,x,?_⟩
    exact congrFun (congrFun hw.symm x) x ▸ D.val.val.refl x
  refine ⟨RawExact.singletonExact S word hne,?_⟩
  change RawExact.evaluate S [word] = D.val.val.r
  exact (RawExact.evaluate_single S word).trans hw

variable [DecidableEq (X i)]

include H cco in
/-- N00 source instance: the finite base and all stabilizer orbits are on
one named original sort, with the ENTIRE original ambient group unchanged. -/
theorem named_sort_real_closure_bounds [Infinite (X i)] (A : Finset (X i)) :
    let N := sortSource S i
    let hN := sortSource_homogeneous S i H
    (2^(directionCount N) - 1 ≤ outsideAtomCount N hN) ∧
    (directionCount N ≤ Nat.log 2 (outsideAtomCount N hN + 1)) ∧
    (Finite (Acl G A) ∧ Nat.card (Acl G A) ≤ packetSize N hN *
      closurePolynomial (directionCount N) (outsideAtomCount N hN) A.card) ∧
    (Finite (AclPackets N hN A) ∧ Nat.card (AclPackets N hN A) ≤
      closurePolynomial (directionCount N) (outsideAtomCount N hN) A.card) ∧
    (∃ C : ℕ, ∀ B : Finset (X i), 1 ≤ B.card → Finite (Acl G B) ∧
      Nat.card (Acl G B) ≤ C * B.card^(directionCount N)) := by
  let N := sortSource S i
  let hN := sortSource_homogeneous S i H
  let cN := sortSource_semanticCCO S i cco
  exact ⟨direction_palette_bound N hN cN,direction_log_bound N hN cN,
    acl_finite_polynomial_bound N hN cN A,acl_packet_count_bound N hN cN A,
    acl_eventual_power_bound N hN cN⟩

/-- Finite ambient sorts use the constant r=0 branch, including empty bases. -/
theorem named_sort_finite_closure [Finite (X i)] (A : Finset (X i)) :
    Acl G A = Set.univ ∧ directionCount (sortSource S i) = 0 ∧
      Nat.card (Acl G A) = packetSize (sortSource S i) (sortSource_homogeneous S i H) :=
  finite_source_closure_bound (sortSource S i) (sortSource_homogeneous S i H) A
end CCO.RealClosure.Bounds
