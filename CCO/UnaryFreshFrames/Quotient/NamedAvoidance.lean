import CCO.UnaryFreshFrames.Quotient.Named

/-! The actual source quotient-fibre lemma, including exact closure equality.
Only accepted finite-action avoidance is external; the representative is
constructed from one stabilizer element acting on all unforced values. -/
universe u v
namespace CCO.UnaryFreshFrames.Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

/-- C18–C26: one actual named quotient representative avoids every unforced
term, preserves all forced values, has the exact singleton-closure intersection,
and is itself fresh. No homogeneity, SAP, finite language or orbit-base premise. -/
theorem named_fibre_avoidance (G : Subgroup H.Aut) {i j : L.Sorts}
    (ht : Quotient.Transitive (G := G) (M := H.Carrier i))
    (p : Term L i j) (hsurj : Function.Surjective (H.typedEval p))
    (hstrict : ¬ Function.Injective (H.typedEval p))
    (hfinite : ∀ x : V, (H.closureAt x).Finite)
    (hfactor : H.ForcedNamedFactors p) (hindex : H.InfiniteUnforcedIndex p)
    (b : H.Carrier j) (Z : Set V) (hZ : Z.Finite) :
    ∃ x : H.Carrier i, H.typedEval p x = b ∧
      H.closureAt x.val ∩ Z = H.closureAt b.val ∩ Z ∧ x.val ∉ Z ∧
      ∀ (k : L.Sorts) (t : Term L i k),
        ¬ Quotient.KernelLe (H.typedEval p) (H.termFunction t) → H.termFunction t x ∉ Z := by
  classical
  obtain ⟨x₀, hx₀⟩ := hsurj b
  have hvals : ((fun f : H.Carrier i → V => f x₀) '' H.NamedFunctions i).Finite := by
    rw [H.namedValues_eq_closureAt x₀]
    exact hfinite x₀.val
  obtain ⟨x, hpx, havoid⟩ := Quotient.common_fibre_avoidance ht
    (H.typedEval p) (H.typedEval_equivariant G p) (H.NamedFunctions i)
    (by rintro f ⟨k, t, rfl⟩; exact H.termFunction_equivariant G t) x₀ hvals
    (by rintro f ⟨k, t, rfl⟩ hn; exact hindex k t hn _) hZ.toFinset
  have hxb : H.typedEval p x = b := hpx.trans hx₀
  have hterm (k : L.Sorts) (t : Term L i k)
      (hn : ¬ Quotient.KernelLe (H.typedEval p) (H.termFunction t)) :
      H.termFunction t x ∉ Z := by
    intro hz
    exact havoid _ ⟨k, t, rfl⟩ hn (hZ.mem_toFinset.mpr hz)
  have hclb : H.closureAt b.val ⊆ H.closureAt x.val := by
    apply H.closureAt_mono_of_mem
    rw [← hxb]
    exact H.typedEval_mem_closureAt p x
  have heq : H.closureAt x.val ∩ Z = H.closureAt b.val ∩ Z := by
    apply Set.Subset.antisymm
    · rintro y ⟨hy, hz⟩
      obtain ⟨f, ⟨k, t, rfl⟩, hty⟩ := (H.namedValues_eq_closureAt x).symm ▸ hy
      change H.termFunction t x = y at hty
      have hforced : Quotient.KernelLe (H.typedEval p) (H.termFunction t) := by
        by_contra hn
        exact hterm k t hn (hty.symm ▸ hz)
      obtain ⟨s, hs⟩ := hfactor k t hforced
      refine ⟨?_, hz⟩
      rw [← hty, hs x]
      have hbval : H.eval p x.val = b.val := congrArg Subtype.val hxb
      rw [hbval]
      exact H.eval_mem_closed (H.closure_closed {b.val}) s
        (H.subset_closure {b.val} rfl)
    · exact fun _ h => ⟨hclb h.1, h.2⟩
  have hid : ¬ Quotient.KernelLe (H.typedEval p) (H.termFunction (.id i)) :=
    Quotient.identity_unforced _ Subtype.val Subtype.val_injective hstrict
  exact ⟨x, hxb, heq, hterm i (.id i) hid, hterm⟩

end CCO.UnaryFreshFrames.Structure
