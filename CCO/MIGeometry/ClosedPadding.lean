import CCO.MIGeometry.ClosedOwners
import CCO.MIGeometry.ActionClosure
import CCO.MIGeometry.ClosedAvoidance

/-! Owner-preserving placement, absolute closure, and realignment of the
whole right padded factor over the closed common helper. -/
universe v w o t
namespace CCO.MIGeometry
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds AclOwners
variable {Y : Type v} {O : Type o} {G : Type t} [Group G]
variable [MulAction G Y] [MulAction G O] [DecidableEq Y] [DecidableEq O]
variable (T : AtomicSource.{0,v,w} Unit (fun _ => Y)) (HT : HomogeneousSource T G)
variable (owner : Y → O)

structure OwnerPadding (B : Finset O) (A L R : Finset Y) where
  base : Finset Y
  left : Finset Y
  right : Finset Y
  leftMove : G
  rightMove : G
  base_closed : Closed G base
  left_closed : Closed G left
  right_closed : Closed G right
  base_contains : A ⊆ base
  base_left : base ⊆ left
  base_right : base ⊆ right
  left_contains : ∀ x ∈ L, leftMove • x ∈ left
  right_contains : ∀ x ∈ R, rightMove • x ∈ right
  left_fixes : ∀ a ∈ A, leftMove • a = a
  right_fixes : ∀ a ∈ A, rightMove • a = a
  left_off : ∀ x ∈ L, x ∉ A → leftMove • x ∉ base
  right_off : ∀ x ∈ R, x ∉ A → rightMove • x ∉ base
  left_owners : ∀ y ∈ left, owner y ∈ B
  right_owners : ∀ y ∈ right, owner y ∈ B
  onto_base : ∀ b ∈ B, ∃ y ∈ base, owner y = b
  separated : ∀ y ∈ left, y ∈ right → y ∈ base

include HT
/-- C16–C18: both original spans are placed over the original closed base,
then the WHOLE closed right padding is moved over the closed helper. No
claim of disjointness is made before the second closure is realigned. -/
theorem closed_owner_padding
    (K : ColourEq T ()) (harmless : FullHarmless T K)
    (surj : Function.Surjective owner)
    (equiv : ∀ (g : G) y, owner (g • y) = g • owner y)
    (kernel : ∀ y z, K y z ↔ owner y = owner z)
    (projection : ∀ A : Finset Y, ∀ y ∈ Acl G A, owner y ∈ Acl G (A.image owner))
    (B : Finset O) (hB : Closed G B) (A L R : Finset Y)
    (closedA : Closed G A) (hAL : A ⊆ L)
    (ownersL : ∀ y ∈ L, owner y ∈ B) (ownersR : ∀ y ∈ R, owner y ∈ B) :
    Nonempty (OwnerPadding (G := G) owner B A L R) := by
  classical
  obtain ⟨D,closedD,hAD,ownersD,ontoD⟩ := closed_owner_helper T HT owner surj projection B hB A
    (fun y hy => ownersL y (hAL hy))
  let q : ↥B → O := Subtype.val
  obtain ⟨l,r,fixl,fixr,fixlB,fixrB,offl,offr,_⟩ :=
    harmless_owner_map_two_placements T HT K harmless owner surj equiv kernel q A D L R closedA
  have fixlB' : ∀ b ∈ B, l • b = b := fun b hb => fixlB ⟨b,hb⟩
  have fixrB' : ∀ b ∈ B, r • b = b := fun b hb => fixrB ⟨b,hb⟩
  let FL := D ∪ L.image (fun x => l • x)
  let FR := D ∪ R.image (fun x => r • x)
  let LL := closureFinset T HT FL
  let RR := closureFinset T HT FR
  have hDLL : D ⊆ LL := fun y hy => subset_closureFinset T HT FL (Finset.mem_union_left _ hy)
  have hDRR : D ⊆ RR := fun y hy => subset_closureFinset T HT FR (Finset.mem_union_left _ hy)
  have ownFL : ∀ y ∈ FL, owner y ∈ B := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact ownersD y hy
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      rw [equiv,fixlB' _ (ownersL x hx)]
      exact ownersL x hx
  have ownFR : ∀ y ∈ FR, owner y ∈ B := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact ownersD y hy
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      rw [equiv,fixrB' _ (ownersR x hx)]
      exact ownersR x hx
  have ownLL := owner_closure_contained T HT owner projection B hB FL ownFL
  have ownRR := owner_closure_contained T HT owner projection B hB FR ownFR
  obtain ⟨d,fixd,avoidd⟩ := closed_base_avoidance (G := G) D RR LL closedD
  have fixdB' : ∀ b ∈ B, d • b = b := by
    intro b hb
    obtain ⟨y,hy,hyb⟩ := ontoD b hb
    calc
      d • b = d • owner y := congrArg (fun z => d • z) hyb.symm
      _ = owner (d • y) := (equiv d y).symm
      _ = owner y := congrArg owner (fixd y hy)
      _ = b := hyb
  let R' := RR.image (fun y => d • y)
  refine ⟨{
    base := D
    left := LL
    right := R'
    leftMove := l
    rightMove := d * r
    base_closed := closedD
    left_closed := closed_closureFinset T HT FL
    right_closed := closed_image_smul d RR (closed_closureFinset T HT FR)
    base_contains := hAD
    base_left := hDLL
    base_right := ?_
    left_contains := ?_
    right_contains := ?_
    left_fixes := fixl
    right_fixes := ?_
    left_off := offl
    right_off := ?_
    left_owners := ownLL
    right_owners := ?_
    onto_base := ontoD
    separated := ?_ }⟩
  · intro y hy
    exact Finset.mem_image.mpr ⟨y,hDRR hy,fixd y hy⟩
  · intro x hx
    exact subset_closureFinset T HT FL (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
  · intro x hx
    exact Finset.mem_image.mpr ⟨r • x,subset_closureFinset T HT FR
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)),(mul_smul d r x).symm⟩
  · intro a ha
    rw [mul_smul,fixr a ha,fixd a (hAD ha)]
  · intro x hx hxA hmem
    have hdmem : d • (r • x) ∈ D := by simpa only [mul_smul] using hmem
    exact offr x hx hxA ((smul_mem_iff_of_fixes d D fixd _).mp hdmem)
  · intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    rw [equiv,fixdB' _ (ownRR x hx)]
    exact ownRR x hx
  · intro y hyL hyR
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hyR
    by_cases hxD : x ∈ D
    · exact he ▸ ((fixd x hxD).symm ▸ hxD)
    · exact False.elim (avoidd x hx hxD y hyL he)

end CCO.MIGeometry
