import CCO.MIGeometry.NestedProjection
import CCO.MIGeometry.OwnerAvoidance

/-! Finite nonempty closed owner bases and closed owner-complete helpers.
Algebraicity projection controls the opposite helper, without opposite
harmlessness. -/
universe v w o p t
namespace CCO.MIGeometry
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds AclOwners
variable {Y : Type v} {O : Type o} {G : Type t} [Group G]
variable [MulAction G Y] [MulAction G O]
variable (T : AtomicSource.{0,v,w} Unit (fun _ => Y)) (HT : HomogeneousSource T G)
variable (U : AtomicSource.{0,o,p} Unit (fun _ => O)) (HU : HomogeneousSource U G)
variable (owner : Y → O)

include U HU

/-- C14: a nonempty absolutely closed finite owner base covers any finite
input. One arbitrary actual owner is added before closure, also for empty
input spans. -/
theorem closed_owner_base [DecidableEq O] (L R : Finset Y) :
    ∃ B : Finset O, B.Nonempty ∧ Closed G B ∧
      (∀ y ∈ L, owner y ∈ B) ∧ (∀ y ∈ R, owner y ∈ B) := by
  classical
  obtain ⟨b⟩ := U.nonemptySort ()
  let A := (L ∪ R).image owner ∪ {b}
  refine ⟨closureFinset U HU A,?_,closed_closureFinset U HU A,?_,?_⟩
  · exact ⟨b,subset_closureFinset U HU A (Finset.mem_union_right _ (Finset.mem_singleton_self _))⟩
  · intro y hy
    exact subset_closureFinset U HU A (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨y,Finset.mem_union_left _ hy,rfl⟩))
  · intro y hy
    exact subset_closureFinset U HU A (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨y,Finset.mem_union_right _ hy,rfl⟩))

omit U HU
include T HT

/-- Owner containment survives absolute closure by APJ into an absolutely
closed owner base. -/
theorem owner_closure_contained [DecidableEq Y] [DecidableEq O]
    (projection : ∀ A : Finset Y, ∀ y ∈ Acl G A,
      owner y ∈ Acl G (A.image owner))
    (B : Finset O) (hB : Closed G B) (A : Finset Y)
    (hA : ∀ y ∈ A, owner y ∈ B) :
    ∀ y ∈ closureFinset T HT A, owner y ∈ B := by
  intro y hy
  have hp := projection A y ((mem_closureFinset T HT A y).mp hy)
  have hi : A.image owner ⊆ B := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact hA a ha
  have h := acl_mono hi hp
  rw [hB] at h
  exact h

/-- C16: a closed recipient helper contains the original base and covers
exactly all displayed owners. Harmlessness is not needed for this step. -/
theorem closed_owner_helper [DecidableEq Y] [DecidableEq O]
    (surj : Function.Surjective owner)
    (projection : ∀ A : Finset Y, ∀ y ∈ Acl G A,
      owner y ∈ Acl G (A.image owner))
    (B : Finset O) (hB : Closed G B) (A : Finset Y)
    (hA : ∀ y ∈ A, owner y ∈ B) :
    ∃ D : Finset Y, Closed G D ∧ A ⊆ D ∧
      (∀ y ∈ D, owner y ∈ B) ∧ (∀ b ∈ B, ∃ y ∈ D, owner y = b) := by
  classical
  choose rep hrep using fun b : ↥B => surj b.val
  let F := A ∪ Finset.univ.image rep
  have hF : ∀ y ∈ F, owner y ∈ B := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hA y hy
    · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hy
      exact hrep b ▸ b.property
  refine ⟨closureFinset T HT F,closed_closureFinset T HT F,
    fun y hy => subset_closureFinset T HT F (Finset.mem_union_left _ hy),
    owner_closure_contained T HT owner projection B hB F hF,?_⟩
  intro b hb
  exact ⟨rep ⟨b,hb⟩,subset_closureFinset T HT F
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨b,hb⟩,Finset.mem_univ _,rfl⟩)),hrep ⟨b,hb⟩⟩

/-- C10/C15: a complete helper spectrum can be closed while retaining
EXACTLY the given closed owner set. No harmlessness in this factor occurs. -/
theorem closed_complete_owner_spectrum [DecidableEq Y] [DecidableEq O]
    (surj : Function.Surjective owner)
    (projection : ∀ A : Finset Y, ∀ y ∈ Acl G A,
      owner y ∈ Acl G (A.image owner))
    (B : Finset O) (hB : Closed G B) :
    ∃ P : Finset Y, Closed G P ∧ OwnerSpectrum T owner B P := by
  apply closed_owner_spectrum T owner HT surj B
  intro P hP y hy
  have hp := projection P y hy
  have hi : P.image owner ⊆ B := by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
    exact hP a ha
  have h := acl_mono hi hp
  rw [hB] at h
  exact h

end CCO.MIGeometry
