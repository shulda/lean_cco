import CCO.SafeReadings.ReturnNormalForm

/-! Parallel generated-family separation from actual positive-cycle
saturation. The final source instance is supplied by primitive loop powers. -/
universe u v w z t
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {Λ : Type z} [Group Λ] {N : Type t} (A : PureTagAction S Λ N)

/-- No exactness predicate is used by this path invariant. -/
def NonemptyMenu (D : TaggedMenu S) : Prop := D.2.2.Nonempty

 theorem PositiveGenerated.nonempty {Q : Family S}
    (point : S.RealPointGluing)
    (hne : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → D.Nonempty)
    {seed D : TaggedMenu S} {p} (h : PositiveGenerated S A Q seed D p)
    (hs : NonemptyMenu S seed) : NonemptyMenu S D := by
  induction h with
  | seed => exact hs
  | @opposite D p h ih =>
    rcases D with ⟨i,j,D⟩
    obtain ⟨a,ha⟩ := ih
    refine ⟨S.conv a,?_⟩
    change S.conv (S.conv a) ∈ D
    simpa only [S.conv_invol] using ha
  | left P hP h ih => exact S.product_nonempty_of_point_gluing point (hne hP) ih
  | right P hP h ih => exact S.product_nonempty_of_point_gluing point ih (hne hP)
  | @action g D p h ih =>
    obtain ⟨a,ha⟩ := ih
    have hm : A.label a ∈ names S A.label (A.act g D) := by
      rw [A.literal]
      exact ⟨a,ha,rfl⟩
    obtain ⟨b,hb,_⟩ := hm
    exact ⟨b,hb⟩

/-- The graph argument uses only nonempty multiplication profiles and the
proved positive-cycle lemma. It works equally for original and safe generators. -/
theorem noReturn_of_positiveClosed_full {Q : Family S}
    (point : S.RealPointGluing)
    (hne : ∀ {i j} {D : S.Menu i j}, (⟨i,j,D⟩ : TaggedMenu S) ∈ Q → D.Nonempty)
    (hc : LiteralConverse S A)
    (hcycle : ∀ (D : TaggedMenu S), NonemptyMenu S D →
      PositiveGenerated S A Q D D true → Full S D) : NoReturn S Q A := by
  intro seed hs D E hD hE hp he
  have hDE : Generated S Q A D E := by
    change E ∈ generatedFamily S Q A D
    rw [he]
    exact .seed
  have hED : Generated S Q A E D := by
    change D ∈ generatedFamily S Q A E
    rw [← he]
    exact .seed
  obtain ⟨p,hpDE⟩ := generated_positive S A hDE
  obtain ⟨q,hpED⟩ := generated_positive S A hED
  have hDn : NonemptyMenu S D := by
    obtain ⟨r,hr⟩ := generated_positive S A hD
    exact hr.nonempty S A point hne (hne hs)
  by_cases hDf : Full S D
  · have hEf := hpDE.full S A point hne hDf
    rcases D with ⟨i,j,D⟩
    rcases E with ⟨i',j',E⟩
    rcases hp with ⟨hi,hj⟩
    cases hi; cases hj
    congr 2
    exact hDf.trans hEf.symm
  · have hfalse : p = false := by
      cases p
      · rfl
      · have hz : PositiveGenerated S A Q D D true := by
          simpa using hpDE.trans S A hpED
        exact False.elim (hDf (hcycle D hDn hz))
    exact A.tagged_names_injective hp (hpDE.names_of_false S A hc hfalse).symm

end CCO.SafeReadings
