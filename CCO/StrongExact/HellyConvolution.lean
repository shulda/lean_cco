import CCO.StrongExact.ConvolutionBound
import CCO.StrongExact.ExactConverse

/-!
# C08 exact STRONG convolution: the nontrivial twice-Helly reduction

The only missing external mathematical ingredient is EXACTLY the
positive-word theta 2-Helly property (C07), retained as an explicit
premise `WordHelly S`. We prove the full reverse convolution inclusion
from it and the actual homogeneous SAP source, using two applications
of word-profile Helly and true typed Peirce rotations.

This is a conditional theorem, NOT the unconditional C08 source instance
until C07's theta 2-Helly has a compiled source proof. No global axiom,
partial provider, RAW identity or unsupported arbitrary-menu
distributivity is added.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j k : ι}

/-- The positive word 2-Helly property from source C07. This is only
a named quantified PROP, never asserted as a theorem or axiom here. -/
def WordHelly : Prop :=
  ∀ {i j : ι} (ws : List (PositiveWord S i j)),
    (∀ u ∈ ws, ∀ v ∈ ws,
      (PositiveWord.profile S u ∩ PositiveWord.profile S v).Nonempty) →
    (present S ws).Nonempty

/-- C08's difficult inclusion under the EXACT missing C07 premise.
The true source conclusion follows once theta Helly is proved. -/
theorem convolutionBound_subset_product_of_wordHelly
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hHelly : WordHelly S)
    (ws : List (PositiveWord S i j))
    (vs : List (PositiveWord S j k))
    (hA : (present S ws).Nonempty)
    (hB : (present S vs).Nonempty) :
    convolutionBound S ws vs ⊆
      S.product (present S ws) (present S vs) := by
  intro z hz
  let hPoint : S.RealPointGluing := S.realPointGluing_of_SAP H sap
  let hEdge : S.RealEdgeGluing := S.realEdgeGluing_of_SAP H sap
  obtain ⟨aA, haA⟩ := hA
  obtain ⟨bB, hbB⟩ := hB
  have hBbase : (S.product ({z} : S.Menu i k)
      ({S.conv bB} : S.Menu k j)).Nonempty :=
    S.product_nonempty_of_point_gluing hPoint
      ⟨z, by simp⟩ ⟨S.conv bB, by simp⟩
  obtain ⟨aBase, haBase⟩ := hBbase
  let rotate : PositiveWord S j k → PositiveWord S i j :=
    fun v => .cons z (reverseWord S v)
  have hBaseRot (v : PositiveWord S j k) (hv : v ∈ vs) :
      aBase ∈ PositiveWord.profile S (rotate v) := by
    change aBase ∈ S.product ({z} : S.Menu i k)
      (PositiveWord.profile S (reverseWord S v))
    rw [profile_reverse_of_gluing S hEdge v]
    have hb : bB ∈ PositiveWord.profile S v := hbB v hv
    have hOne : ({S.conv bB} : S.Menu k j) ⊆
        S.opposite (PositiveWord.profile S v) := by
      intro d hd
      have heq : d = S.conv bB := Set.mem_singleton_iff.mp hd
      subst d
      exact S.mem_opposite hb
    exact S.product_mono (fun _ h => h) hOne haBase
  have hCross (w : PositiveWord S i j) (hw : w ∈ ws)
      (v : PositiveWord S j k) (hv : v ∈ vs) :
      (PositiveWord.profile S w ∩
        PositiveWord.profile S (rotate v)).Nonempty := by
    obtain ⟨a, ha, b, hb, htri⟩ := hz w hw v hv
    refine ⟨a, ha, ?_⟩
    change a ∈ S.product ({z} : S.Menu i k)
      (PositiveWord.profile S (reverseWord S v))
    rw [profile_reverse_of_gluing S hEdge v]
    exact ⟨z, by simp, S.conv b, S.mem_opposite hb,
      S.triangle_rotate htri⟩
  let family : List (PositiveWord S i j) := ws ++ vs.map rotate
  have hPairs : ∀ p ∈ family, ∀ q ∈ family,
      (PositiveWord.profile S p ∩
        PositiveWord.profile S q).Nonempty := by
    intro p hp q hq
    rcases List.mem_append.mp hp with hpW | hpV
    · rcases List.mem_append.mp hq with hqW | hqV
      · exact ⟨aA, haA p hpW, haA q hqW⟩
      · obtain ⟨v, hv, heq⟩ := List.mem_map.mp hqV
        subst q
        exact hCross p hpW v hv
    · obtain ⟨v, hv, heq⟩ := List.mem_map.mp hpV
      subst p
      rcases List.mem_append.mp hq with hqW | hqV
      · obtain ⟨a, ha, hr⟩ := hCross q hqW v hv
        exact ⟨a, hr, ha⟩
      · obtain ⟨v', hv', heq'⟩ := List.mem_map.mp hqV
        subst q
        exact ⟨aBase, hBaseRot v hv, hBaseRot v' hv'⟩
  obtain ⟨a, haFamily⟩ := hHelly family hPairs
  have haInA : a ∈ present S ws := by
    intro w hw
    exact haFamily w (List.mem_append.mpr (Or.inl hw))
  have haRotate (v : PositiveWord S j k) (hv : v ∈ vs) :
      a ∈ PositiveWord.profile S (rotate v) := by
    exact haFamily (rotate v)
      (List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨v, hv, rfl⟩)))
  let extra : PositiveWord S j k := .cons (S.conv a) (.single z)
  have hExtra : (PositiveWord.profile S extra).Nonempty :=
    S.product_nonempty_of_point_gluing hPoint
      ⟨S.conv a, by simp⟩ ⟨z, by simp⟩
  have hMeetExtra (v : PositiveWord S j k) (hv : v ∈ vs) :
      (PositiveWord.profile S v ∩
        PositiveWord.profile S extra).Nonempty := by
    have hrot := haRotate v hv
    change a ∈ S.product ({z} : S.Menu i k)
      (PositiveWord.profile S (reverseWord S v)) at hrot
    obtain ⟨z', hz', b', hb', ht⟩ := hrot
    have hzEq : z' = z := Set.mem_singleton_iff.mp hz'
    subst z'
    have hbOpp : b' ∈ S.opposite (PositiveWord.profile S v) := by
      rw [← profile_reverse_of_gluing S hEdge v]
      exact hb'
    have hbIn : S.conv b' ∈ PositiveWord.profile S v := hbOpp
    have htri : S.Triangle (S.conv a) z (S.conv b') := by
      rcases ht with ⟨x, t, y, hxt, hty, hxy⟩
      exact ⟨y, x, t, (S.colour_swap x y a).mp hxy, hxt,
        (S.colour_swap t y b').mp hty⟩
    exact ⟨S.conv b', hbIn,
      ⟨S.conv a, by simp, z, by simp, htri⟩⟩
  let second : List (PositiveWord S j k) := vs ++ [extra]
  have hPairs2 : ∀ p ∈ second, ∀ q ∈ second,
      (PositiveWord.profile S p ∩
        PositiveWord.profile S q).Nonempty := by
    intro p hp q hq
    rcases List.mem_append.mp hp with hpW | hpExtra
    · rcases List.mem_append.mp hq with hqW | hqExtra
      · exact ⟨bB, hbB p hpW, hbB q hqW⟩
      · have hqEq : q = extra := List.mem_singleton.mp hqExtra
        subst q
        exact hMeetExtra p hpW
    · have hpEq : p = extra := List.mem_singleton.mp hpExtra
      subst p
      rcases List.mem_append.mp hq with hqW | hqExtra
      · obtain ⟨b, hb, he⟩ := hMeetExtra q hqW
        exact ⟨b, he, hb⟩
      · have hqEq : q = extra := List.mem_singleton.mp hqExtra
        subst q
        obtain ⟨b, hb⟩ := hExtra
        exact ⟨b, hb, hb⟩
  obtain ⟨b, hbSecond⟩ := hHelly second hPairs2
  have hbInB : b ∈ present S vs := by
    intro v hv
    exact hbSecond v (List.mem_append.mpr (Or.inl hv))
  have hbExtra : b ∈ PositiveWord.profile S extra :=
    hbSecond extra
      (List.mem_append.mpr (Or.inr (by simp)))
  change b ∈ S.product ({S.conv a} : S.Menu j i)
    ({z} : S.Menu i k) at hbExtra
  obtain ⟨a', ha', z', hz', ht⟩ := hbExtra
  have haEq : a' = S.conv a := Set.mem_singleton_iff.mp ha'
  have hzEq : z' = z := Set.mem_singleton_iff.mp hz'
  subst a'
  subst z'
  have hrot : S.Triangle z (S.conv b) a := by
    simpa only [S.conv_invol] using S.triangle_cycle ht
  exact ⟨a, haInA, b, hbInB, S.triangle_rotate_back hrot⟩

/-- Full finite-presented C08 convolution *conditional only on C07*.
Once theta Helly is proved, the premise can be discharged from the
actual homogeneous SAP+CCO source. -/
theorem exact_convolution_of_wordHelly
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hHelly : WordHelly S)
    (ws : List (PositiveWord S i j))
    (vs : List (PositiveWord S j k))
    (hws : (present S ws).Nonempty)
    (hvs : (present S vs).Nonempty) :
    S.product (present S ws) (present S vs) =
      convolutionBound S ws vs := by
  apply Set.Subset.antisymm
  · exact product_present_subset_convolutionBound S ws vs
  · exact convolutionBound_subset_product_of_wordHelly
      S H sap hHelly ws vs hws hvs

end CCO.StrongExact
