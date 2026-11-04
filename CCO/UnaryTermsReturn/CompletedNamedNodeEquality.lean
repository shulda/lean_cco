import CCO.UnaryTermsReturn.CompletedNamedCarrier

universe u v w t
namespace CCO.UnaryTermsReturn
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]
open CCO.TransitionClosure
open CCO.ParityHasse.Original

theorem original_completed_named_node_heq
    (H : HomogeneousSource S G)
    {i j : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val)
    (E : OriginalNamedHiddenCoordinate S H j)
    (r : Quotient E.val.val)
    (h : originalCompletedNamedHiddenNode S H D q =
      originalCompletedNamedHiddenNode S H E r) :
    ∃ hSort : i = j, HEq D E ∧ HEq q r := by
  have hv : (⟨i,⟨D.val,q⟩⟩ : OriginalNormalCodeTargetValue S) =
      ⟨j,⟨E.val,r⟩⟩ := by
    exact Sum.inr.inj
      (congrArg (originalCompletedCarrierForget S H) h)
  have hi : i = j := congrArg Sigma.fst hv
  cases hi
  have hp : (⟨D.val,q⟩ :
      Σ K : ColourEq S i, Quotient K.val) = ⟨E.val,r⟩ := by
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hv
  have hDE : D = E := Subtype.ext (congrArg Sigma.fst hp)
  cases hDE
  have hqr : q = r := by
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hp
  cases hqr
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩

end CCO.UnaryTermsReturn
