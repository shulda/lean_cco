import CCO.TerminalLattice.OptionalPositiveLengths
import CCO.RawExact.QuotientExpansionCycleRealization
import CCO.RawExact.QuotientExpansionReadout
import CCO.StrongExact.ProfileSemantics

/-!
# B050 C27/C35: actual OLD private-word expansion readout and cycle realization

These bridges consume the accepted B002 private expansion and its
literal positive-length word/cycle interfaces, with ALL required
positive-length hypotheses now PROVED by the original one-word-per-pair
construction. They do not postulate an old diagram completion or CCO.

Any original diagram homomorphism realizes the true positive word
between each marked pair with a specified word. For a genuinely
injective realization, the real fine endpoint atom belongs to that
word's actual old STRONG profile. Conversely an assignment of real
marked vertices satisfying every USED edge's original whole-word
constraint yields one homomorphism of the original specified cycle.
The remaining obligation is to construct such assignments for every
sparse-star projected cycle, before invoking original CCO once.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Source C27 direct receiving theorem: the accepted B002 actual
finite private-cycle gluing works for our ORIGINAL old word network.
All marked real-pair constraints here concern ONLY USED source edges;
omitted marked edges have no positive occurrence. The required
positive-word length guard has been genuinely discharged. -/
theorem oldOptionalPositiveCycleHom_of_marked_values
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (C : SimpleCycle (oldOptionalPositiveDiagram S H sap words))
    (b : Fin n → X i)
    (hUsed : ∀ e,
      CCO.RawExact.QuotientExpansion.CycleUsesEdge S
        (fun _ : Fin n => i)
        (oldOptionalPositivePresentations S words)
        (oldOptionalPositivePresentations_nonempty S H sap words)
        C e →
      CCO.RawExact.evaluate S
        (oldOptionalPositivePresentations S words e)
        (b (CCO.RawExact.QuotientExpansion.left e))
        (b (CCO.RawExact.QuotientExpansion.right e))) :
    CycleHom C := by
  exact CCO.RawExact.QuotientExpansion.cycleHom_of_marked_edge_realization
    S (fun _ : Fin n => i) (oldOptionalPositivePresentations S words)
    (oldOptionalPositivePresentations_nonempty S H sap words)
    C b hUsed
    (oldOptionalPositivePresentations_all_occurrences_positive S words)

/-- The B002 global original diagram readout specializes to the TRUE
old RAW represented positive word for ANY present marked pair.
There is no assumption that a global diagram homomorphism exists;
it is an explicit input to be discharged later by original CCO.
No quotient homogeneity or imaginary SAP is involved. -/
theorem oldOptionalPositiveDiagram_hom_word
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (f : DiagramHom (oldOptionalPositiveDiagram S H sap words))
    (e : CCO.RawExact.QuotientExpansion.Edge n)
    (word : PositiveWord S i i)
    (hWord : words e = some word) :
    PositiveWord.represented S word
      (f.point (CCO.RawExact.QuotientExpansion.mark S
        (fun _ : Fin n => i) (oldOptionalPositivePresentations S words)
          (CCO.RawExact.QuotientExpansion.left e)))
      (f.point (CCO.RawExact.QuotientExpansion.mark S
        (fun _ : Fin n => i) (oldOptionalPositivePresentations S words)
          (CCO.RawExact.QuotientExpansion.right e))) := by
  let P := oldOptionalPositivePresentations S words
  let hNE := oldOptionalPositivePresentations_nonempty S H sap words
  have hEval :=
    CCO.RawExact.QuotientExpansion.hom_all_menus
      S (fun _ : Fin n => i) P hNE f
      (oldOptionalPositivePresentations_all_occurrences_positive S words) e
  have hMem : PositiveWord.toRawWord S word ∈ P e := by
    simp [P,oldOptionalPositivePresentations,hWord]
  have hRaw := hEval (PositiveWord.toRawWord S word) hMem
  rw [PositiveWord.represented_toRawWord S word]
  exact hRaw

/-- With the actual original SAP injectivization, a realized marked
pair has genuinely distinct OLD endpoints. The original old fine
colour of the pair is therefore in the exact STRONG positive-word
endpoint profile, rather than being a RAW equality output. This
will feed the actual finite original orbital and centre colour table.
-/
theorem oldOptionalPositiveDiagram_hom_strong_profile
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {n : Nat}
    (words : CCO.RawExact.QuotientExpansion.Edge n →
      Option (PositiveWord S i i))
    (f : DiagramHom (oldOptionalPositiveDiagram S H sap words))
    (hInj : f.IsInjective)
    (e : CCO.RawExact.QuotientExpansion.Edge n)
    (word : PositiveWord S i i)
    (hWord : words e = some word) :
    S.menuRel (PositiveWord.profile S word)
      (f.point (CCO.RawExact.QuotientExpansion.mark S
        (fun _ : Fin n => i) (oldOptionalPositivePresentations S words)
          (CCO.RawExact.QuotientExpansion.left e)))
      (f.point (CCO.RawExact.QuotientExpansion.mark S
        (fun _ : Fin n => i) (oldOptionalPositivePresentations S words)
          (CCO.RawExact.QuotientExpansion.right e))) := by
  let P := oldOptionalPositivePresentations S words
  let sort : Fin n → ι := fun _ => i
  let root : Fin n → X i :=
    fun v => f.point (CCO.RawExact.QuotientExpansion.mark S sort P v)
  have hNe : root (CCO.RawExact.QuotientExpansion.left e) ≠
      root (CCO.RawExact.QuotientExpansion.right e) := by
    intro hEq
    have hImage : f.image
        (CCO.RawExact.QuotientExpansion.mark S sort P
          (CCO.RawExact.QuotientExpansion.left e)) =
      f.image
        (CCO.RawExact.QuotientExpansion.mark S sort P
          (CCO.RawExact.QuotientExpansion.right e)) := by
      change (⟨i,root (CCO.RawExact.QuotientExpansion.left e)⟩ : Sigma X) =
        ⟨i,root (CCO.RawExact.QuotientExpansion.right e)⟩
      rw [hEq]
    have hMark := hInj hImage
    exact CCO.RawExact.QuotientExpansion.left_ne_right e (Sum.inl.inj hMark)
  have hTag : (⟨i,root (CCO.RawExact.QuotientExpansion.left e)⟩ : Sigma X) ≠
      ⟨i,root (CCO.RawExact.QuotientExpansion.right e)⟩ := by
    intro hh
    have heq : root (CCO.RawExact.QuotientExpansion.left e) =
        root (CCO.RawExact.QuotientExpansion.right e) := by
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hh
    exact hNe heq
  obtain ⟨a, hCol⟩ :=
    S.some_colour_of_ne
      (root (CCO.RawExact.QuotientExpansion.left e))
      (root (CCO.RawExact.QuotientExpansion.right e)) hTag
  have hRep := oldOptionalPositiveDiagram_hom_word
    S H sap words f e word hWord
  change PositiveWord.represented S word
      (root (CCO.RawExact.QuotientExpansion.left e))
      (root (CCO.RawExact.QuotientExpansion.right e)) at hRep
  have ha : a ∈ PositiveWord.profile S word :=
    (StrongExact.positive_profile_iff_represented S H sap word a).mpr
      ⟨root (CCO.RawExact.QuotientExpansion.left e),
       root (CCO.RawExact.QuotientExpansion.right e),hRep,hCol⟩
  exact ⟨a,ha,hCol⟩

end CCO.TerminalLattice
