import CCO.OwnerTransversal.ExactOwnerLifting

/-! Finite real maps with their ENTIRE recorded exact-owner component.
Mixed pairs are checked by the actual nested-orbital theorem before the
accepted joint exact-sort lifting theorem is applied. -/
universe v w t z r
namespace CCO.OwnerTransversal
open ParityHasse.Original RawExact FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M]

/-- C13. The index J includes unused owners, and I may be empty.  Thus
the conclusion extends the whole specified owner component at once. -/
theorem finite_real_owner_lifting
    (cco : SemanticCCO.{0,v,0,w} S) (E : ColourEq S ())
    (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    {I : Type z} [Finite I] {J : Type r} [Finite J]
    (source target : I → M) (q q' : J → Quotient E.val)
    (hReal : ∀ i j, S.colour (i := ()) (j := ()) (source i) (source j) =
      S.colour (target i) (target j))
    (hOwners : letI := originalQuotientAction S H E
      ∀ j k, GroupActions.orbital (G := G) (q j) (q k) (q' j) (q' k))
    (hCover : ∀ i, ∃ j, q j = Quotient.mk'' (source i) ∧
      q' j = Quotient.mk'' (target i)) :
    letI := originalQuotientAction S H E
    ∃ g : G, (∀ i, g • source i = target i) ∧ (∀ j, g • q j = q' j) :=
  actual_joint_real_owner_lifting S H cco E hE source target q q' hReal hOwners hCover

end CCO.OwnerTransversal
