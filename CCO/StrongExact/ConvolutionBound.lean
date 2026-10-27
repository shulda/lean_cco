import CCO.StrongExact.ProfileSemantics

/-!
# C08: the exact upper bound for STRONG convolution

For two finite STRONG word-profile presentations, the convolution
upper bound consists of atoms supported by EVERY pair of positive
word profiles. This upper bound is exactly a finite positive-word
presentation obtained by concatenating all pairs of original words,
even if either original list is empty. Hence under source SAP the bound
is itself a nonempty ORIGINAL exact menu whenever both factors have
nonempty evaluations.

The easy inclusion (product of intersections ⊆ intersection of products)
is unconditional. The reverse inclusion is the substantive twice-Helly
step of C08 and is **NOT** asserted here before proving C07.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j k : ι}

/-- Pairwise convolution constraints for two finite original
positive-word lists. Empty lists create NO restrictions. -/
def convolutionBound
    (ws : List (PositiveWord S i j))
    (vs : List (PositiveWord S j k)) : S.Menu i k :=
  {c | ∀ w ∈ ws, ∀ v ∈ vs,
    c ∈ S.product (PositiveWord.profile S w)
      (PositiveWord.profile S v)}

/-- All pairwise concatenations retain their genuine endpoint tags and
never introduce a STRONG identity factor. -/
def concatenationWords
    (ws : List (PositiveWord S i j))
    (vs : List (PositiveWord S j k)) :
    List (PositiveWord S i k) :=
  ws.flatMap (fun w => vs.map (PositiveWord.append S w))

/-- Monotonicity proves the forward C08 convolution inclusion without
SAP, CCO, exactness or any pairwise Helly property. -/
theorem product_present_subset_convolutionBound
    (ws : List (PositiveWord S i j))
    (vs : List (PositiveWord S j k)) :
    S.product (present S ws) (present S vs) ⊆
      convolutionBound S ws vs := by
  intro c hc w hw v hv
  exact S.product_mono
    (fun _ ha => ha w hw) (fun _ hb => hb v hv) hc

/-- Literal presentation of the convolution upper bound. B001
strong associativity under SAP proves the required profile-concatenation
law; there are no empty positive words. -/
theorem convolutionBound_eq_present_of_SAP
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (ws : List (PositiveWord S i j))
    (vs : List (PositiveWord S j k)) :
    convolutionBound S ws vs =
      present S (concatenationWords S ws vs) := by
  ext c
  change (∀ w ∈ ws, ∀ v ∈ vs,
    c ∈ S.product (PositiveWord.profile S w)
      (PositiveWord.profile S v)) ↔
    (∀ q ∈ concatenationWords S ws vs,
      c ∈ PositiveWord.profile S q)
  constructor
  · intro hh q hq
    obtain ⟨w, hw, hq'⟩ := List.mem_flatMap.mp hq
    obtain ⟨v, hv, heq⟩ := List.mem_map.mp hq'
    subst q
    rw [PositiveWord.profile_append_of_SAP S H sap w v]
    exact hh w hw v hv
  · intro hh w hw v hv
    have hq : PositiveWord.append S w v ∈ concatenationWords S ws vs :=
      List.mem_flatMap.mpr ⟨w, hw,
        List.mem_map.mpr ⟨v, hv, rfl⟩⟩
    have hc := hh (PositiveWord.append S w v) hq
    rw [PositiveWord.profile_append_of_SAP S H sap w v] at hc
    exact hc

/-- Under source SAP the convolution upper bound is a NONEMPTY
original exact menu whenever its two input presentations evaluate
nonemptily. No circular use of the unproved C08 reverse inclusion. -/
theorem exact_convolutionBound_of_SAP
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (ws : List (PositiveWord S i j))
    (vs : List (PositiveWord S j k))
    (hws : (present S ws).Nonempty)
    (hvs : (present S vs).Nonempty) :
    Exact S (convolutionBound S ws vs) := by
  obtain ⟨c, hc⟩ :=
    product_nonempty_of_SAP S H sap
      (present S ws) (present S vs) hws hvs
  refine ⟨⟨c, product_present_subset_convolutionBound S ws vs hc⟩,
    ⟨concatenationWords S ws vs, ?_⟩⟩
  exact convolutionBound_eq_present_of_SAP S H sap ws vs

end CCO.StrongExact
