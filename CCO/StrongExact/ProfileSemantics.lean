import CCO.StrongExact.ExactMenus
import CCO.PairHomogeneity
import CCO.PositiveWords

/-!
# Exact positive-profile endpoint semantics and nonempty STRONG products

This is a direct *source-level* corollary of the accepted B001 guarded
represented-word theorem. A strongly supported fine atom is realized by
a real walk with DISTINCT endpoints, and every such represented walk
gives precisely the same fine atom, without introducing equality as a
STRONG letter.

The converse below operates on literal original homogeneous/SAP
hypotheses. No unproved theta Helly or PC fixed-point provider is used.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j k : ι}
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- B001 SAP injectivization implies full literal endpoint semantics:
each STRONG profile atom is exactly an ACTUAL endpoint colour of a
represented positive diversity walk. Distinctness follows from
`some a` and `colour_none_iff`, including i=j. -/
theorem positive_profile_iff_represented
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (w : PositiveWord S i j) (a : S.Atom i j) :
    a ∈ PositiveWord.profile S w ↔
      ∃ x : X i, ∃ y : X j,
        PositiveWord.represented S w x y ∧
        S.colour x y = some a := by
  have h := PositiveWord.diversityGuard_represented_eq_profile_of_SAP S H sap w
  rw [← h]
  rfl

/-- Any menu presentation obtained by finite intersection of positive
profiles constrains actual realized endpoint colours pointwise. -/
theorem represented_colour_in_present
    (ws : List (PositiveWord S i j))
    (a : S.Atom i j)
    (h : ∀ w ∈ ws,
      ∃ x : X i, ∃ y : X j,
        PositiveWord.represented S w x y ∧
        S.colour x y = some a)
    (H : HomogeneousSource S G) (sap : AgeSAP S) :
    a ∈ present S ws := by
  intro w hw
  exact (positive_profile_iff_represented S H sap w a).2 (h w hw)

/-- Nonempty STRONG composition holds for arbitrary nonempty menus
under actual original homogeneous SAP, irrespective of exactness.
This is the existence component of C08, NOT exact closure. -/
theorem product_nonempty_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (A : S.Menu i j) (B : S.Menu j k)
    (ha : A.Nonempty) (hb : B.Nonempty) :
    (S.product A B).Nonempty :=
  S.product_nonempty_of_point_gluing
    (S.realPointGluing_of_SAP H sap) ha hb

/-- Two singleton atomic exact domains compose to the one positive
two-letter word profile, an unconditional exact presentation whose
nonemptiness uses the genuinely distinct-point SAP gluing provider. -/
theorem exact_product_singletons_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (a : S.Atom i j) (b : S.Atom j k) :
    Exact S (S.product ({a} : S.Menu i j) ({b} : S.Menu j k)) := by
  have hne : (S.product ({a} : S.Menu i j) ({b} : S.Menu j k)).Nonempty :=
    product_nonempty_of_SAP S H sap _ _ ⟨a, by simp⟩ ⟨b, by simp⟩
  refine ⟨hne, ⟨[.cons a (.single b)], ?_⟩⟩
  ext c
  simp only [present, List.mem_singleton, forall_eq]
  rfl

end CCO.StrongExact
