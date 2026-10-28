import CCO.StrongExact.HellyConvolution

/-!
# C08 product closure in the ORIGINAL exact family

This short corollary packages the fully formalized twice-Helly
convolution identity and the proof that its finite positive-word
upper-bound is an exact domain.

The ONLY uninstantiated mathematical provider is explicitly the
precise positive-profile 2-Helly property `WordHelly S`, which belongs
to C07. The theorem does not claim an unconditional source instance
before theta Helly has been proved.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j k : ι}

/-- C08 original exact-product closure, conditional precisely on C07.
The result is a nonempty positive-word finite-meet presentation, not
an equality-inclusive RAW completion. -/
theorem exact_product_of_wordHelly
    {G : Type*} [Group G] [∀ s : ι, MulAction G (X s)]
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (hHelly : WordHelly S)
    {A : S.Menu i j} {B : S.Menu j k}
    (hA : Exact S A) (hB : Exact S B) :
    Exact S (S.product A B) := by
  obtain ⟨hAn, ws, hws⟩ := hA
  obtain ⟨hBn, vs, hvs⟩ := hB
  rw [hws] at hAn
  rw [hvs] at hBn
  rw [hws, hvs]
  rw [exact_convolution_of_wordHelly S H sap hHelly
    ws vs hAn hBn]
  exact exact_convolutionBound_of_SAP S H sap ws vs hAn hBn

end CCO.StrongExact
