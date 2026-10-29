import CCO.MIGeometry.SelectedNormalization

/-! Residual atoms computed in the exact distributive sublattice. The
result is then transported to ALL invariant minimal infinite directions. -/
universe v w t
namespace CCO.MIGeometry
open ParityHasse.Original RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization RawExact AclOwners

section FiniteOrder
variable {L : Type*} [DistribLattice L] [OrderBot L]
/-- A surviving atom gives an atom in an upper interval. -/
theorem atom_interval_dichotomy (a k e : L) (ha : IsAtom a)
    (hke : k ≤ e) (hea : e ≤ a ⊔ k) : e = k ∨ e = a ⊔ k := by
  have he : e = (e ⊓ a) ⊔ k := by
    calc e = e ⊓ (a ⊔ k) := (inf_eq_left.mpr hea).symm
         _ = (e ⊓ a) ⊔ (e ⊓ k) := inf_sup_left e a k
         _ = (e ⊓ a) ⊔ k := by rw [inf_eq_right.mpr hke]
  by_cases h : e ⊓ a = ⊥
  · exact Or.inl (by simpa [h] using he)
  · have hae : a ≤ e := by
      have hh : e ⊓ a = a := by
        by_contra hn
        exact h (ha.2 _ (lt_of_le_of_ne inf_le_right hn))
      rw [← hh]
      exact inf_le_left
    exact Or.inr (le_antisymm hea (sup_le hae hke))
end FiniteOrder

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (cco : SemanticCCO.{0,v,0,w} S)

include H cco in
/-- Source form of the normalized atom/full-direction bridge, requiring
minimality only against ACTUAL exact equivalences. -/
theorem direction_of_exact_minimal (normalized : NoFiniteExactKernel S)
    (E : ColourEq S ()) (hE : ExactCRT.IsExactEq S (i := ()) E.val) (hne : E ≠ ⊥)
    (hmin : ∀ F : ColourEq S (), ExactCRT.IsExactEq S (i := ()) F.val →
      F ≤ E → F = ⊥ ∨ F = E) : IsDirection S E := by
  refine ⟨?_,?_⟩
  · intro hf
    exact hne (normalized_exact_finite S normalized E hE hf)
  · intro F hF
    by_contra hf
    obtain ⟨D,hD⟩ := exists_direction_le S hf
    obtain hz | he := hmin D.val (direction_exact S H cco D) (hD.trans hF.le)
    · exact D.property.1 (hz ▸ finiteClasses_bot S)
    · exact hF.not_ge (he ▸ hD)

include H cco in
/-- The interval calculation uses distributivity ONLY for exact E,K,D. -/
theorem direction_join_interval (normalized : NoFiniteExactKernel S)
    (D : Direction S) (K E : ColourEq S ())
    (hK : ExactCRT.IsExactEq S (i := ()) K.val)
    (hE : ExactCRT.IsExactEq S (i := ()) E.val)
    (hKE : K ≤ E) (hED : E ≤ ColourEq.join S H D.val K) :
    E = K ∨ E = ColourEq.join S H D.val K := by
  letI := ExactCRT.exactDistribLattice S H (semanticCCO_change_universe S cco) ()
  let d : ExactL S H cco := ⟨D.val.val,direction_exact S H cco D⟩
  let k : ExactL S H cco := ⟨K.val,hK⟩
  let e : ExactL S H cco := ⟨E.val,hE⟩
  have hh := atom_interval_dichotomy d k e (direction_exact_atom S H cco normalized D)
    hKE hED
  exact hh.imp (fun h => Subtype.ext (congrArg (fun z : ExactL S H cco => z.val) h))
    (fun h => Subtype.ext (congrArg (fun z : ExactL S H cco => z.val) h))

end CCO.MIGeometry
