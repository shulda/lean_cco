import CCO.StrongExact.ProfileSemantics
import CCO.TerminalLattice.StrongPaletteBridge
import CCO.ExactCRT.ExactLattice

/-! The direct B057 idempotent envelope. Logical equality is restored as
an actual diagonal relation, never as a diversity atom. The literal RAW
word square is proved without CCO, NR2 or an all-equivalences-exact premise. -/

universe u v w t
namespace CCO.GuardedOldSeams
open CCO.ParityHasse.Original CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

theorem menuRel_colourInvariant {i : ι} (e : S.Menu i i) :
    ColourInvariant S i (S.menuRel e) := by
  intro x y x' y' hcol
  constructor
  · rintro ⟨a,ha,hxy⟩
    exact ⟨a,ha,hcol.symm.trans hxy⟩
  · rintro ⟨a,ha,hxy⟩
    exact ⟨a,ha,hcol.trans hxy⟩

theorem menuRel_ne {i : ι} {e : S.Menu i i} {x y : X i}
    (h : S.menuRel e x y) : x ≠ y := by
  rintro rfl
  obtain ⟨a,_,ha⟩ := h
  exact S.atomRel_ne ha rfl

/-- The FULL equivalence envelope of a strong diversity idempotent. -/
def envelope {i : ι} (e : S.Menu i i) (he : S.product e e = e) : ColourEq S i := by
  refine ⟨{ r := fun x y => x = y ∨ S.menuRel e x y
            iseqv := ⟨fun _ => Or.inl rfl, ?_, ?_⟩ }, ?_⟩
  · intro x y h
    exact h.elim (fun h => Or.inl h.symm)
      (fun h => Or.inr (colourInvariant_symmetric S (menuRel_colourInvariant S e) x y h))
  · intro x y z hxy hyz
    rcases hxy with rfl | hxy
    · exact hyz
    rcases hyz with rfl | hyz
    · exact Or.inr hxy
    by_cases hxz : x = z
    · exact Or.inl hxz
    have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,z⟩ := by
      intro h
      exact hxz (by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h)
    obtain ⟨c,hc⟩ := S.some_colour_of_ne x z hTag
    obtain ⟨a,ha,hxy⟩ := hxy
    obtain ⟨b,hb,hyz⟩ := hyz
    have hprod : c ∈ S.product e e := ⟨a,ha,b,hb,x,y,z,hxy,hyz,hc⟩
    exact Or.inr ⟨c,he ▸ hprod,hc⟩
  · intro x y x' y' hcol
    exact or_congr ((⊥ : ColourEq S i).property x y x' y' hcol)
      (menuRel_colourInvariant S e x y x' y' hcol)

@[simp] theorem envelope_apply {i : ι} (e : S.Menu i i)
    (he : S.product e e = e) (x y : X i) :
    envelope S e he x y ↔ x = y ∨ S.menuRel e x y := Iff.rfl

theorem envelope_distinct_iff {i : ι} (e : S.Menu i i)
    (he : S.product e e = e) {x y : X i} (hne : x ≠ y) :
    envelope S e he x y ↔ S.menuRel e x y := by
  exact ⟨fun h => h.resolve_left hne, Or.inr⟩

@[simp] theorem envelope_diversity {i : ι} (e : S.Menu i i)
    (he : S.product e e = e) :
    originalEquivDiversityPalette S (envelope S e he) = e := by
  ext a
  constructor
  · rintro ⟨x,y,(hEq | ⟨b,hb,hxy⟩),hcol⟩
    · subst y
      exact False.elim (S.atomRel_ne hcol rfl)
    · have hba : b = a := Option.some.inj (hxy.symm.trans hcol)
      exact hba ▸ hb
  · intro ha
    obtain ⟨x,y,hxy⟩ := S.realized a
    exact ⟨x,y,Or.inr ⟨a,ha,hxy⟩,hxy⟩

theorem envelope_gt_bot {i : ι} (e : S.Menu i i)
    (he : S.product e e = e) (hne : e.Nonempty) :
    (⊥ : ColourEq S i) < envelope S e he := by
  apply lt_of_le_of_ne bot_le
  intro hEq
  obtain ⟨a,ha⟩ := hne
  obtain ⟨x,y,hxy⟩ := S.realized a
  have hb : (⊥ : ColourEq S i) x y := by
    rw [hEq]
    exact Or.inr ⟨a,ha,hxy⟩
  exact S.atomRel_ne hxy (congrArg (Sigma.mk i) hb)

theorem envelope_le_iff {i : ι} (e f : S.Menu i i)
    (he : S.product e e = e) (hf : S.product f f = f) :
    envelope S e he ≤ envelope S f hf ↔ e ⊆ f := by
  constructor
  · intro h a ha
    obtain ⟨x,y,hxy⟩ := S.realized a
    have hF := h (show envelope S e he x y from Or.inr ⟨a,ha,hxy⟩)
    rcases hF with hEq | ⟨b,hb,hbxy⟩
    · exact False.elim (S.atomRel_ne hxy (congrArg (Sigma.mk i) hEq))
    · have hba : b = a := Option.some.inj (hbxy.symm.trans hxy)
      exact hba ▸ hb
  · intro h x y hxy
    rcases hxy with hEq | ⟨a,ha,hxy⟩
    · exact Or.inl hEq
    · exact Or.inr ⟨a,h ha,hxy⟩

section OriginalWord
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
include H

theorem represented_colourInvariant {i : ι} (word : PositiveWord S i i) :
    ColourInvariant S i (PositiveWord.represented S word) :=
  groupInvariant_colourInvariant S H
    (PositiveWord.represented_invariant_of_homogeneous S H word)

theorem represented_symmetric {i : ι} (word : PositiveWord S i i) :
    Symmetric (PositiveWord.represented S word) :=
  colourInvariant_symmetric S (represented_colourInvariant S H word)

/-- The true RAW diagonal is all or empty, by ORIGINAL transitivity. -/
theorem represented_diagonal_all_or_none {i : ι} (word : PositiveWord S i i) :
    (∀ x, PositiveWord.represented S word x x) ∨
      (∀ x, ¬PositiveWord.represented S word x x) := by
  classical
  by_cases h : ∃ x, PositiveWord.represented S word x x
  · obtain ⟨x,hx⟩ := h
    left
    intro y
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i x y
    simpa only [hg] using
      PositiveWord.represented_invariant_of_homogeneous S H word g x x hx
  · exact Or.inr (fun x hx => h ⟨x,hx⟩)

include sap

/-- Exact actual endpoints, retaining the diagonal distinction. -/
theorem positive_profile_pair_iff {i : ι} (word : PositiveWord S i i) (x y : X i) :
    S.menuRel (PositiveWord.profile S word) x y ↔
      x ≠ y ∧ PositiveWord.represented S word x y := by
  constructor
  · rintro ⟨a,ha,hxy⟩
    obtain ⟨p,q,hpq,hcol⟩ :=
      (StrongExact.positive_profile_iff_represented S H sap word a).mp ha
    exact ⟨menuRel_ne S ⟨a,ha,hxy⟩,
      (represented_colourInvariant S H word p q x y (hcol.trans hxy.symm)).mp hpq⟩
  · rintro ⟨hne,hxy⟩
    have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
      intro h
      exact hne (by simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h)
    obtain ⟨a,ha⟩ := S.some_colour_of_ne x y hTag
    exact ⟨a,(StrongExact.positive_profile_iff_represented S H sap word a).mpr
      ⟨x,y,hxy,ha⟩,ha⟩

/-- C22's literal alternative: RAW w is its diversity or that diversity
with ALL of real equality restored. -/
theorem represented_eq_diversity_or_restore {i : ι} (word : PositiveWord S i i) :
    PositiveWord.represented S word = S.menuRel (PositiveWord.profile S word) ∨
    PositiveWord.represented S word =
      (fun x y => x = y ∨ S.menuRel (PositiveWord.profile S word) x y) := by
  classical
  rcases represented_diagonal_all_or_none S H word with hall | hnone
  · right
    funext x y
    apply propext
    constructor
    · intro hxy
      by_cases hEq : x = y
      · exact Or.inl hEq
      · exact Or.inr ((positive_profile_pair_iff S H sap word x y).mpr ⟨hEq,hxy⟩)
    · rintro (rfl | hxy)
      · exact hall x
      · exact ((positive_profile_pair_iff S H sap word x y).mp hxy).2
  · left
    funext x y
    apply propext
    constructor
    · intro hxy
      apply (positive_profile_pair_iff S H sap word x y).mpr
      refine ⟨?_,hxy⟩
      rintro rfl
      exact hnone x hxy
    · intro hxy
      exact ((positive_profile_pair_iff S H sap word x y).mp hxy).2

/-- C23: nonempty genuine strong words have DISTINCT RAW neighbours
at every original point. This uses only actual old transitivity. -/
theorem positive_word_distinct_serial {i : ι} (word : PositiveWord S i i) :
    ∀ x : X i, ∃ y, x ≠ y ∧ PositiveWord.represented S word x y := by
  obtain ⟨a,ha⟩ := PositiveWord.profile_nonempty_of_SAP S H sap word
  obtain ⟨p,q,hpq,hcol⟩ :=
    (StrongExact.positive_profile_iff_represented S H sap word a).mp ha
  intro x
  obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous H i p x
  refine ⟨g • q,?_,?_⟩
  · intro hEq
    have h := MulAction.injective g (hg.trans hEq)
    exact S.atomRel_ne hcol (congrArg (Sigma.mk i) h)
  · simpa only [hg] using
      PositiveWord.represented_invariant_of_homogeneous S H word g p q hpq

/-- C24--C28: the ACTUAL RAW square, including every true diagonal,
is exactly Id union the strong idempotent. No CCO or NR2. -/
theorem raw_square_envelope {i : ι} (word : PositiveWord S i i)
    (he : S.product (PositiveWord.profile S word) (PositiveWord.profile S word) =
      PositiveWord.profile S word) :
    TRel.comp (PositiveWord.represented S word) (PositiveWord.represented S word) =
      (envelope S (PositiveWord.profile S word) he).val.r := by
  let E := envelope S (PositiveWord.profile S word) he
  have hInside : ∀ x y, PositiveWord.represented S word x y → E x y := by
    intro x y hxy
    by_cases hEq : x = y
    · exact Or.inl hEq
    · exact Or.inr ((positive_profile_pair_iff S H sap word x y).mpr ⟨hEq,hxy⟩)
  funext x z
  apply propext
  constructor
  · rintro ⟨y,hxy,hyz⟩
    exact E.val.trans (hInside _ _ hxy) (hInside _ _ hyz)
  · rintro (hEq | hMenu)
    · subst z
      obtain ⟨y,_,hxy⟩ := positive_word_distinct_serial S H sap word x
      exact ⟨y,hxy,colourInvariant_symmetric S (represented_colourInvariant S H word) x y hxy⟩
    · have hProd : S.menuRel
          (S.product (PositiveWord.profile S word) (PositiveWord.profile S word)) x z := by
        rw [he]
        exact hMenu
      rw [menuRel_product_eq_strongCompose S H] at hProd
      obtain ⟨_,y,_,_,hxy,hyz⟩ := hProd
      exact ⟨y,(positive_profile_pair_iff S H sap word x y).mp hxy |>.2,
        (positive_profile_pair_iff S H sap word y z).mp hyz |>.2⟩

/-- The representing word is literally ww, not a replacement word. -/
theorem represented_word_square_envelope {i : ι} (word : PositiveWord S i i)
    (he : S.product (PositiveWord.profile S word) (PositiveWord.profile S word) =
      PositiveWord.profile S word) :
    PositiveWord.represented S (PositiveWord.append S word word) =
      (envelope S (PositiveWord.profile S word) he).val.r := by
  rw [PositiveWord.represented_append]
  exact raw_square_envelope S H sap word he

/-- FULL RAW exactness is supplied by the singleton presentation ww
before any represented-MI reconstruction is invoked. -/
theorem envelope_raw_exact {i : ι} (word : PositiveWord S i i)
    (he : S.product (PositiveWord.profile S word) (PositiveWord.profile S word) =
      PositiveWord.profile S word) :
    ExactCRT.IsExactEq S (envelope S (PositiveWord.profile S word) he).val := by
  let ww := PositiveWord.toRawWord S (PositiveWord.append S word word)
  have hww : RawWord.relation S ww =
      (envelope S (PositiveWord.profile S word) he).val.r :=
    (PositiveWord.represented_toRawWord S _).symm.trans
      (represented_word_square_envelope S H sap word he)
  let D : RawExact.NonemptyExact S i i := {
    words := [ww]
    nonempty := by
      obtain ⟨x⟩ := S.nonemptySort i
      refine ⟨x,x,?_⟩
      intro v hv
      have hvw : v = ww := List.mem_singleton.mp hv
      subst v
      rw [hww]
  }
  refine ⟨D,?_⟩
  funext x y
  apply propext
  change (∀ v, v ∈ [ww] → RawWord.relation S v x y) ↔ _
  simp only [List.mem_singleton,forall_eq,hww]

end OriginalWord
end CCO.GuardedOldSeams
