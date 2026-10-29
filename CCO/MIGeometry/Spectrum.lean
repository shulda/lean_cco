import CCO.AclOwners.AclCore
import CCO.AclOwners.Rectangle
import CCO.AclOwners.QuotientSource
import CCO.RawExact.FineColoursSource

/-! Equality-inclusive complementary owner spectra.  The witness table is
indexed by actual owners and complete pair colours, including equality. -/
universe v w o t
namespace CCO.MIGeometry
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds AclOwners

variable {X : Type v} {O : Type o}
variable (T : AtomicSource.{0,v,w} Unit (fun _ => X)) (owner : X → O)

/-- Every complete pair colour realized above an ordered owner pair occurs
inside the helper. Equality witnesses are included by `FullColour`. -/
def OwnerSpectrum (B : Finset O) (P : Finset X) : Prop :=
  (∀ x ∈ P, owner x ∈ B) ∧
  (∀ b ∈ B, ∃ x ∈ P, owner x = b) ∧
  ∀ b ∈ B, ∀ b' ∈ B, ∀ x x', owner x = b → owner x' = b' →
    ∃ p ∈ P, ∃ p' ∈ P, owner p = b ∧ owner p' = b' ∧ col T p p' = col T x x'

/-- Finite complete owner tables exist without a harmlessness or closure
premise. The diagonal is automatically part of the finite colour index. -/
theorem finite_owner_spectrum [DecidableEq X] [DecidableEq O]
    (surj : Function.Surjective owner) (B : Finset O) :
    ∃ P : Finset X, OwnerSpectrum T owner B P := by
  classical
  letI := T.finiteAtom () ()
  let I := {i : ↥B × ↥B × FullColour T //
    ∃ x x', owner x = i.1.val ∧ owner x' = i.2.1.val ∧ col T x x' = i.2.2}
  let x : I → X := fun i => i.property.choose
  let x' : I → X := fun i => i.property.choose_spec.choose
  have hx (i : I) : owner (x i) = i.val.1.val ∧
      owner (x' i) = i.val.2.1.val ∧ col T (x i) (x' i) = i.val.2.2 :=
    i.property.choose_spec.choose_spec
  let P := Finset.univ.image x ∪ Finset.univ.image x'
  refine ⟨P,?_,?_,?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
      exact (hx i).1 ▸ i.val.1.property
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
      exact (hx i).2.1 ▸ i.val.2.1.property
  · intro b hb
    obtain ⟨a,ha⟩ := surj b
    let i : I := ⟨(⟨b,hb⟩,⟨b,hb⟩,col T a a),a,a,ha,ha,rfl⟩
    exact ⟨x i,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),(hx i).1⟩
  · intro b hb c hc a a' ha ha'
    let i : I := ⟨(⟨b,hb⟩,⟨c,hc⟩,col T a a'),a,a',ha,ha',rfl⟩
    refine ⟨x i,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),
      x' i,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩),?_⟩
    exact hx i

/-- Enlarging a helper preserves its full spectrum provided no new owner
is introduced. This is the exact interface used when taking absolute acl. -/
theorem OwnerSpectrum.mono {B : Finset O} {P Q : Finset X}
    (hP : OwnerSpectrum T owner B P) (hPQ : P ⊆ Q)
    (hQ : ∀ q ∈ Q, owner q ∈ B) : OwnerSpectrum T owner B Q := by
  refine ⟨hQ,?_,?_⟩
  · intro b hb
    obtain ⟨x,hx,hxb⟩ := hP.2.1 b hb
    exact ⟨x,hPQ hx,hxb⟩
  · intro b hb b' hb' x x' hx hx'
    obtain ⟨p,hp,p',hp',he⟩ := hP.2.2 b hb b' hb' x x' hx hx'
    exact ⟨p,hPQ hp,p',hPQ hp',he⟩

/-- A closed helper follows from algebraicity projection to a closed owner
set. The projection condition will be discharged on the actual exact split. -/
theorem closed_owner_spectrum {G : Type t} [Group G] [MulAction G X]
    (HT : HomogeneousSource T G) [DecidableEq X] [DecidableEq O]
    (surj : Function.Surjective owner) (B : Finset O)
    (projection : ∀ P : Finset X, (∀ x ∈ P, owner x ∈ B) →
      ∀ x ∈ Acl G P, owner x ∈ B) :
    ∃ P : Finset X, Closed G P ∧ OwnerSpectrum T owner B P := by
  obtain ⟨P,hP⟩ := finite_owner_spectrum T owner surj B
  refine ⟨closureFinset T HT P,closed_closureFinset T HT P,
    hP.mono T owner (subset_closureFinset T HT P) ?_⟩
  intro x hx
  exact projection P hP.1 x ((mem_closureFinset T HT P x).mp hx)

end CCO.MIGeometry
