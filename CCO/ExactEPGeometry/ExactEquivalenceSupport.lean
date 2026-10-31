import CCO.ExactEPGeometry.FullExactSupport
import CCO.ExactEPGeometry.ExactEquivalenceLattice

/-!
# B062 C50: actual original ExactEq finite-meet type supports

For two current named sorts over ONE original sort, every finite
family of ORIGINAL full-RAW-exact invariant equivalences has an actual
common diagonal pair. Thus the source's nonempty-old-intersection
guard is AUTOMATIC for this family, and the full C48 exact-family
support theorem gives preservation of arbitrary finite meets.

The sort identification is an explicit equality of the two actual
parent names; it does NOT assume that arbitrary differently sorted
relations or quotient kernels can be identified.
-/

universe u v w

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

variable {ι κ : Type u} {X : ι → Type v} {Y : κ → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {T : AtomicSource.{u,v,w} κ Y}

/-- Transport one real exact relation across equality of its SECOND
original sort, retaining its complete nonempty RAW presentation. This
is just dependent type transport, not mixed quotient exact descent. -/
private theorem right_transport_fullExact
    {r s : ι} (h : r = s)
    (R : TRel X r r) (hR : FullExact S R) :
    FullExact S (fun x : X r => fun y : X s =>
      R x (h.symm ▸ y)) := by
  cases h
  exact hR

private theorem cast_back
    {r s : ι} (h : r = s) (x : X r) :
    h.symm ▸ (h ▸ x) = x := by
  cases h
  rfl

/-- Source C50 at exact-original-equivalence strength: for any finite
family of actual original ExactEq members and two CURRENT realized
types with the SAME original parent, one CURRENT pair belongs to ALL
equivalences iff EACH equivalence has some CURRENT pair. All original
equivalences contain the actual logical identity, hence the OLD
intersection nonemptiness is proved, not postulated.

In the B062 one-original-sort source the same-parent condition is
automatic. The empty family means Top and is covered as well. -/
theorem exactEq_family_support_iff
    (P : UnaryReduct S T)
    (hMeet : ExactMeetSupport S T P)
    {i j : κ} (hParent : P.parent i = P.parent j)
    {F : Type} [Fintype F]
    (E : F → ExactEq S (P.parent i)) :
    (∃ x : Y i, ∃ y : Y j,
      ∀ f : F, E f (P.point i x)
        (hParent.symm ▸ P.point j y)) ↔
      ∀ f : F, ∃ x : Y i, ∃ y : Y j,
        E f (P.point i x)
          (hParent.symm ▸ P.point j y) := by
  classical
  let R : F → TRel X (P.parent i) (P.parent j) :=
    fun f a b => E f a (hParent.symm ▸ b)
  have hExact : ∀ f : F, FullExact S (R f) := by
    intro f
    exact right_transport_fullExact (S := S) hParent
      (fun x y => E f x y) (E f).property
  let a : X (P.parent i) :=
    Classical.choice (S.nonemptySort (P.parent i))
  let b : X (P.parent j) := hParent ▸ a
  have hOld :
      ∃ a' : X (P.parent i), ∃ b' : X (P.parent j),
        ∀ f : F, R f a' b' := by
    refine ⟨a,b,?_⟩
    intro f
    change E f a (hParent.symm ▸ b)
    rw [cast_back (X := X) hParent a]
    exact (E f).val.val.refl a
  change (∃ x : Y i, ∃ y : Y j,
      ∀ f : F, R f (P.point i x) (P.point j y)) ↔
    ∀ f : F, ∃ x : Y i, ∃ y : Y j,
      R f (P.point i x) (P.point j y)
  exact fullExact_family_support_iff P hMeet R hExact hOld

end
end CCO.ExactEPGeometry
