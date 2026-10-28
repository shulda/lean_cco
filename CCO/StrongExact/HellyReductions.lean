import CCO.StrongExact.HellyConvolution

/-!
# C07: flattening positive-word theta Helly to full exact-menu Helly

The difficult geometry of C07 is exactly the positive-word theta
2-Helly property `WordHelly S`, retained as a *visible theorem
hypothesis* until the theta combinatorics are kernel-checked.

This file proves the nontrivial but purely finite bookkeeping step:
any finite pairwise-intersecting family of ORIGINAL nonempty exact
menus can be flattened into a pairwise-intersecting finite list
of genuinely positive word profiles. One application of word Helly
then yields a literal diversity atom common to every exact menu.
The empty list requires the original typed palette nonempty, already
part of the strong source C07 provider.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j : ι}

/-- Finite meet of literal original exact menus, including typed Top
for the empty list. -/
def meetMenus (menus : List (S.Menu i j)) : S.Menu i j :=
  {a | ∀ A ∈ menus, a ∈ A}

/-- Choose a genuine finite positive-word presentation only when one
exists. The fallback is irrelevant whenever the menu is exact. -/
noncomputable def wordsOfExact (A : S.Menu i j) :
    List (PositiveWord S i j) := by
  classical
  exact if h : Exact S A then Classical.choose h.2 else []

theorem wordsOfExact_spec {A : S.Menu i j}
    (h : Exact S A) :
    A = present S (wordsOfExact S A) := by
  classical
  simpa only [wordsOfExact, dif_pos h] using
    (Classical.choose_spec h.2)

/-- C07's exact-menu 2-Helly consequence, CONDITIONAL only on
positive word 2-Helly. This is not counted as a completed C07 source
instance until the latter is proved from SAP+CCO theta diagrams. -/
theorem exact_helly_of_wordHelly
    (hHelly : WordHelly S)
    (menus : List (S.Menu i j))
    (hExact : ∀ A ∈ menus, Exact S A)
    (hPair : ∀ A ∈ menus, ∀ B ∈ menus, (A ∩ B).Nonempty) :
    (meetMenus S menus).Nonempty := by
  classical
  let allWords : List (PositiveWord S i j) :=
    menus.flatMap (wordsOfExact S)
  have hWordPair : ∀ u ∈ allWords, ∀ v ∈ allWords,
      (PositiveWord.profile S u ∩
        PositiveWord.profile S v).Nonempty := by
    intro u hu v hv
    obtain ⟨A, hA, huA⟩ := List.mem_flatMap.mp hu
    obtain ⟨B, hB, hvB⟩ := List.mem_flatMap.mp hv
    obtain ⟨c, hcA, hcB⟩ := hPair A hA B hB
    have hAwords : c ∈ present S (wordsOfExact S A) := by
      rw [← wordsOfExact_spec S (hExact A hA)]
      exact hcA
    have hBwords : c ∈ present S (wordsOfExact S B) := by
      rw [← wordsOfExact_spec S (hExact B hB)]
      exact hcB
    exact ⟨c, hAwords u huA, hBwords v hvB⟩
  obtain ⟨c, hcWords⟩ := hHelly allWords hWordPair
  refine ⟨c, ?_⟩
  intro A hA
  have hcPresented : c ∈ present S (wordsOfExact S A) := by
    intro u hu
    exact hcWords u
      (List.mem_flatMap.mpr ⟨A, hA, hu⟩)
  rw [← wordsOfExact_spec S (hExact A hA)] at hcPresented
  exact hcPresented

end CCO.StrongExact
