import CCO.ExactEPGeometry.ActualUnaryTrace

/-!
# B062 C23–C24: decode a real marked middle point to its EXACT child

A genuine current unary child is a subtype of ORIGINAL points, and its
finite owner name is the actual pair of original sort and character bit.
The accepted `UnarySource.newEquiv` is a bijection between the ENTIRE
tagged child source and the actual marked Fraïssé limit.

Hence an actual middle point furnished by the AP-only C22 marked trace
whose owner is a specified child label lies in THAT child, uniquely.
The proof uses the canonical old-reduct identification and injectivity
of literal child labels, never an unrelated choice of quotient section.
This is the equality-preserving middle-sort decoder needed for the
general current RAW-word reverse inclusion C24–C27.
-/

universe u v w t

namespace CCO.ExactEPGeometry.ActualUnaryDecode

open APCharacter
open APCharacter.SourceAge

noncomputable section

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
variable {H : HomogeneousSource S G}
variable {M : MaskData S} {completion : Age.CompletionProperty S M}
variable (I : SourceAge.UnarySource.Identification S H completion)

/-- Recover the literal child point from a point of the genuine marked
limit with the stated current child owner. It is NOT merely some
isomorphic copy or a group-orbit representative. -/
theorem decode_child_of_owner
    (c : Rank.Child (SourceAge.UnarySource.β I))
    (b : Age.Limit S H completion)
    (hOwner : (Age.limitCoding S H completion).table.owner b =
      Age.ownerEquiv S (SourceAge.UnarySource.childLabel I c)) :
    ∃ x : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) c,
      SourceAge.UnarySource.newEquiv I
        (⟨c,x⟩ : SourceAge.UnarySource.NewPoint I) = b := by
  let p : SourceAge.UnarySource.NewPoint I :=
    (SourceAge.UnarySource.newEquiv I).symm b
  have hBack : SourceAge.UnarySource.newEquiv I p = b :=
    (SourceAge.UnarySource.newEquiv I).apply_symm_apply b
  have hOwnerP : (Age.limitCoding S H completion).table.owner
        (SourceAge.UnarySource.newEquiv I p) =
      Age.ownerEquiv S (SourceAge.UnarySource.childLabel I p.1) :=
    SourceAge.UnarySource.new_owner I p
  have hLabelEq :
      Age.ownerEquiv S (SourceAge.UnarySource.childLabel I p.1) =
        Age.ownerEquiv S (SourceAge.UnarySource.childLabel I c) :=
    hOwnerP.symm.trans ((congrArg
      (Age.limitCoding S H completion).table.owner hBack).trans hOwner)
  have hChildEq : p.1 = c :=
    SourceAge.UnarySource.childLabel_injective I
      ((Age.ownerEquiv S).injective hLabelEq)
  rcases p with ⟨d,x⟩
  change d = c at hChildEq
  subst d
  exact ⟨x,hBack⟩

/-- For a REAL marked point with the literal bit c.2, the decoded point
lies in c itself. The equality of complete current owner codes is
derived from the actual marked-age table. -/
theorem decode_child_of_bit
    (c : Rank.Child (SourceAge.UnarySource.β I))
    (b : Age.Limit S H completion)
    (hOwner : (Age.limitCoding S H completion).table.owner b =
      Age.ownerEquiv S (c.1,c.2.val)) :
    ∃ x : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) c,
      SourceAge.UnarySource.newEquiv I
        (⟨c,x⟩ : SourceAge.UnarySource.NewPoint I) = b :=
  decode_child_of_owner I c b hOwner

/-- A real marked point has at MOST one representative in its specified
child; uniqueness follows from the accepted entire-structure equivalence.
Thus a repeated endpoint cannot be silently split into two new vertices. -/
theorem child_embedding_injective
    (c : Rank.Child (SourceAge.UnarySource.β I))
    (x y : Rank.Point (SourceAge.UnarySource.β I) (SourceAge.UnarySource.tag I) c) :
    SourceAge.UnarySource.newEquiv I (⟨c,x⟩ : SourceAge.UnarySource.NewPoint I) =
      SourceAge.UnarySource.newEquiv I (⟨c,y⟩ : SourceAge.UnarySource.NewPoint I) ↔
        x = y := by
  constructor
  · intro h
    have hp : (⟨c,x⟩ : SourceAge.UnarySource.NewPoint I) = ⟨c,y⟩ :=
      (SourceAge.UnarySource.newEquiv I).injective h
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hp
  · intro h
    rw [h]

end
end CCO.ExactEPGeometry.ActualUnaryDecode
