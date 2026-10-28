import CCO.StrongExact.AgeAP
import Mathlib.Data.Finset.Union

/-!
# Prescribed finite maps and pointwise union extensions

These are finite homogeneity lemmas, independent of any independence relation.
The cross-colour premise is an explicit verification obligation at the caller.
Both the common parameters and the whole second side are fixed pointwise.
-/

universe u v w t

namespace CCO.SIR.Positive

variable {ι : Type u} {X : ι → Type v}
variable {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [MulAction G (Sigma X)]
variable [DecidableEq (Sigma X)]

/-- Glue the restriction of a prescribed automorphism on `A` to the identity
on `B ∪ C`. Cross colours and the literal overlap are checked explicitly.
No injectivity or range hypothesis is added: full pair colours include equality.
-/
theorem extends_union_fixing (H : HomogeneousSource S G)
    (A B C : Finset (Sigma X)) (g : G)
    (hfix : ∀ c ∈ C, g • c = c)
    (hoverlap : ∀ x ∈ A, x ∈ B → x ∈ C)
    (hcross : ∀ a ∈ A, ∀ b ∈ B,
      taggedColour S (g • a) b = taggedColour S a b) :
    ∃ h : G, (∀ b ∈ B ∪ C, h • b = b) ∧
      ∀ a ∈ A, h • a = g • a := by
  classical
  let D := A ∪ (B ∪ C)
  let f : ↥D → Sigma X := fun x => if x.val ∈ A then g • x.val else x.val
  have hfA (x : ↥D) (hx : x.val ∈ A) : f x = g • x.val := if_pos hx
  have hfBC (x : ↥D) (hx : x.val ∈ B ∪ C) : f x = x.val := by
    by_cases ha : x.val ∈ A
    · rw [hfA x ha]
      apply hfix
      rcases Finset.mem_union.mp hx with hb | hc
      · exact hoverlap x.val ha hb
      · exact hc
    · exact if_neg ha
  have hpair : ∀ a b : ↥D,
      taggedColour S a.val b.val = taggedColour S (f a) (f b) := by
    intro a b
    by_cases ha : a.val ∈ A
    · rw [hfA a ha]
      by_cases hb : b.val ∈ A
      · rw [hfA b hb]
        exact (H.preserves_colours g a.val b.val).symm
      · have hbBC : b.val ∈ B ∪ C :=
          (Finset.mem_union.mp b.property).resolve_left hb
        rw [hfBC b hbBC]
        rcases Finset.mem_union.mp hbBC with hbB | hbC
        · exact (hcross a.val ha b.val hbB).symm
        · simpa only [hfix b.val hbC] using
            (H.preserves_colours g a.val b.val).symm
    · have haBC : a.val ∈ B ∪ C :=
        (Finset.mem_union.mp a.property).resolve_left ha
      rw [hfBC a haBC]
      by_cases hb : b.val ∈ A
      · rw [hfA b hb]
        apply taggedColour_reverse_eq
        rcases Finset.mem_union.mp haBC with haB | haC
        · exact (hcross b.val hb a.val haB).symm
        · simpa only [hfix a.val haC] using
            (H.preserves_colours g b.val a.val).symm
      · have hbBC : b.val ∈ B ∪ C :=
          (Finset.mem_union.mp b.property).resolve_left hb
        rw [hfBC b hbBC]
  obtain ⟨h, hh⟩ := H.extends_finite_diagram (fun x : ↥D => x.val) f hpair
  refine ⟨h, ?_, ?_⟩
  · intro b hb
    let x : ↥D := ⟨b, Finset.mem_union_right A hb⟩
    exact (hh x).trans (hfBC x hb)
  · intro a ha
    let x : ↥D := ⟨a, Finset.mem_union_left (B ∪ C) ha⟩
    exact (hh x).trans (hfA x ha)

/-- Every particular induced finite map fixing the named parameters is the
restriction of an automorphism fixing those parameters pointwise. The actual
given map is retained, rather than replaced by an existential isomorphism.
-/
theorem extends_prescribed_map (H : HomogeneousSource S G)
    (A A' C : Finset (Sigma X))
    (f : ↥(A ∪ C) ≃ ↥(A' ∪ C))
    (hcol : ∀ x y, taggedColour S x.val y.val =
      taggedColour S (f x).val (f y).val)
    (hfix : ∀ c (hc : c ∈ C),
      (f ⟨c, Finset.mem_union_right A hc⟩).val = c) :
    ∃ g : G, (∀ c ∈ C, g • c = c) ∧
      ∀ x : ↥(A ∪ C), g • x.val = (f x).val := by
  obtain ⟨g, hg⟩ := H.extends_finite_diagram
    (fun x : ↥(A ∪ C) => x.val) (fun x => (f x).val) hcol
  refine ⟨g, ?_, hg⟩
  intro c hc
  exact (hg ⟨c, Finset.mem_union_right A hc⟩).trans (hfix c hc)

end CCO.SIR.Positive
