import CCO.SimultaneousQuotients.Towers.Rank
import CCO.ExactCRT.CanonicalTypedQuotients

/-! Actual canonical simultaneous quotient instances of the rank theorem.
There is no supplied partition map or cardinal-drop hypothesis. -/

universe u v w t
namespace CCO.SimultaneousQuotients.Towers
open RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable (J : ∀ i, Setoid (X i)) (E : ∀ i, NonemptyExact S i i)
variable (represents : ∀ i, evaluate S (E i).words = (J i).r)

/-- No typed diversity palette grows under a current exact quotient. -/
theorem canonicalRank_le :
    diversityRank (ExactCRT.CanonicalTyped.source S H J E represents) ≤ diversityRank S := by
  letI := S.finiteSort
  letI : ∀ i, MulAction G (Quotient (J i)) :=
    ExactCRT.CanonicalTyped.action S H J E represents
  exact diversityRank_le S _ H
    (ExactCRT.CanonicalTyped.projection J)
    (ExactCRT.CanonicalTyped.projection_surjective J)
    (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents)
    (ExactCRT.TypedPalette.source_colour_eq_iff_orbital _ S H id
      (ExactCRT.CanonicalTyped.projection J)
      (ExactCRT.CanonicalTyped.projection_surjective J)
      (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents))

/-- A genuinely nonidentity CURRENT kernel swallows an old diversity atom
and forces strict total rank loss. Id and top are both permitted kernels. -/
theorem canonicalRank_lt
    (h : ∃ i, ∃ x y : X i, x ≠ y ∧ J i x y) :
    diversityRank (ExactCRT.CanonicalTyped.source S H J E represents) < diversityRank S := by
  letI := S.finiteSort
  letI : ∀ i, MulAction G (Quotient (J i)) :=
    ExactCRT.CanonicalTyped.action S H J E represents
  apply diversityRank_lt_of_nonidentity S _ H
    (ExactCRT.CanonicalTyped.projection J)
    (ExactCRT.CanonicalTyped.projection_surjective J)
    (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents)
    (ExactCRT.TypedPalette.source_colour_eq_iff_orbital _ S H id
      (ExactCRT.CanonicalTyped.projection J)
      (ExactCRT.CanonicalTyped.projection_surjective J)
      (ExactCRT.CanonicalTyped.projection_equivariant S H J E represents))
  obtain ⟨i,x,y,hxy,hJ⟩ := h
  exact ⟨i,x,y,hxy,Quotient.sound hJ⟩

/-- The same strict theorem stated directly as a kernel strictly above Id. -/
theorem canonicalRank_lt_of_nonidentity (h : ∃ i, J i ≠ ⊥) :
    diversityRank (ExactCRT.CanonicalTyped.source S H J E represents) < diversityRank S := by
  apply canonicalRank_lt S H J E represents
  obtain ⟨i,hi⟩ := h
  obtain ⟨x,y,hxy,hJ⟩ := (kernel_ne_bot_iff (J i)).mp hi
  exact ⟨i,x,y,hxy,hJ⟩

end CCO.SimultaneousQuotients.Towers
