import CCO.UnaryHN.RawEncoding.Free

/-! Concrete typed ages and original homomorphism-embeddings. All closed
irreducible source diagrams are tested; no selected-support proxy is used. -/
universe u v
namespace CCO.UnaryHN.Raw
open CCO.UnarySupport (Signature)

abbrev Class (L : Signature.{u}) := CCO.UnarySupport.Structure.Class.{u,v} L
abbrev CompletedClass {L : Signature.{u}} (K : Class.{u,v} L) :=
  CCO.UnarySupport.Structure.CompletedClass K

def Hereditary {L : Signature.{u}} (K : Class.{u,v} L) : Prop :=
  ∀ {V W : Type v} {A : Typed L V} {B : Typed L W}, K B → A.Embedding B → K A

structure FiniteHereditarySAP {L : Signature.{u}} (K : Class.{u,v} L) : Prop where
  finite : ∀ {V : Type v} (C : Typed L V), K C → Finite V
  hereditary : Hereditary K
  strong : ∀ {H V W : Type v} {Root : Typed L H} {Left : Typed L V} {Right : Typed L W},
    K Left → K Right → ∀ (sL : Root.Embedding Left) (sR : Root.Embedding Right),
    ∃ (X : Type v) (_ : Finite X) (Target : Typed L X), K Target ∧
      ∃ (jL : Left.Embedding Target) (jR : Right.Embedding Target),
        (∀ h, jL.point (sL.point h) = jR.point (sR.point h)) ∧
        (∀ x y, jL.point x = jR.point y → ∃ h, x = sL.point h ∧ y = sR.point h)

def AllIrreducible {L : Signature.{u}} (K : Class.{u,v} L) : Prop :=
  ∀ {V : Type v} (C : Typed L V), K C → C.Irreducible

def IrreduciblesIn {L : Signature.{u}} (K : Class.{u,v} L)
    {V : Type v} (C : Typed L V) : Prop :=
  ∀ {X : Type v} (E : Typed L X), E.Irreducible → E.Embedding C → K E

structure HE {L : Signature.{u}} {V W : Type v}
    (C : Typed L V) (D : Typed L W) (f : V → W) : Prop where
  sort_eq : ∀ x, D.sort (f x) = C.sort x
  map_func : ∀ F x y, y ∈ C.func F x → f y ∈ D.func F (f x)
  map_rel : ∀ R xs, C.rel R xs → D.rel R (f ∘ xs)
  irreducibles : ∀ {X : Type v} (E : Typed L X), E.Irreducible →
    ∀ e : E.Embedding C, ∃ g : E.Embedding D, ∀ x, g.point x = f (e.point x)

def HasCompletion {L : Signature.{u}} (K : Class.{u,v} L)
    {V : Type v} (C : Typed L V) : Prop :=
  ∃ (W : Type v) (_ : Finite W) (D : Typed L W), K D ∧ ∃ f : V → W, HE C D f

def EncodedClass {L : Signature.{u}} (K : Class.{u,v} L) : Native.Class.{u,v} (language L) :=
  fun {V} D => ∃ C : Typed L V, K C ∧ encode C = D

theorem encoded_finiteHereditarySAP {L : Signature.{u}} {K : Class.{u,v} L}
    (hK : FiniteHereditarySAP K) : Native.FiniteHereditarySAP (EncodedClass K) where
  finite D hD := by obtain ⟨C, hC, rfl⟩ := hD; exact hK.finite C hC
  singleton D hD := by obtain ⟨C, _, rfl⟩ := hD; exact singleton_encode C
  hereditary := by
    intro V W A B hB e
    obtain ⟨B, hB, rfl⟩ := hB
    exact ⟨pullbackTyped B e, hK.hereditary hB (pullbackTypedEmbedding B e),
      encode_pullbackTyped B e⟩
  strong := by
    intro H V W Root Left Right hL hR sL sR
    obtain ⟨Left, hL, rfl⟩ := hL
    obtain ⟨Right, hR, rfl⟩ := hR
    let P := pullbackTyped Left sL
    let tL : P.Embedding Left := pullbackTypedEmbedding Left sL
    let tR : P.Embedding Right :=
      decodeEmbedding (castEmbedding sR (encode_pullbackTyped Left sL).symm rfl)
    have hTL (x : H) : tL.point x = sL x := rfl
    have hTR (x : H) : tR.point x = sR x :=
      castEmbedding_apply sR (encode_pullbackTyped Left sL).symm rfl x
    obtain ⟨X, hX, Target, hT, jL, jR, hComm, hInt⟩ := hK.strong hL hR tL tR
    refine ⟨X, hX, encode Target, ⟨Target, hT, rfl⟩,
      encodeEmbedding jL, encodeEmbedding jR, ?_, ?_⟩
    · intro x
      change jL.point (sL x) = jR.point (sR x)
      simpa only [hTL, hTR] using hComm x
    · intro x y hxy
      obtain ⟨z, hzL, hzR⟩ := hInt x y hxy
      exact ⟨z, hzL.trans (hTL z), hzR.trans (hTR z)⟩

theorem encoded_allIrreducible {L : Signature.{u}} {K : Class.{u,v} L}
    (hK : AllIrreducible K) : Native.AllIrreducible (EncodedClass K) := by
  intro V D hD
  obtain ⟨C, hC, rfl⟩ := hD
  exact (irreducible_encode_iff C).mpr (hK C hC)

theorem HE.to_native {L : Signature.{u}} {V W : Type v}
    {C : Typed L V} {D : Typed L W} {f : V → W} (h : HE C D f) :
    Native.HE (encode C) (encode D) f := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro R xs hx
    cases R with
    | inl R => exact h.map_rel R xs hx
    | inr s => change D.sort (f (xs 0)) = s; rw [h.sort_eq]; exact hx
  · intro F xs y hy
    exact h.map_func F (xs 0) y hy
  · intro X E hE e
    let P := pullbackTyped C e
    have hEncode : encode P = E := encode_pullbackTyped C e
    have hP : P.Irreducible := (irreducible_encode_iff P).mp (by rw [hEncode]; exact hE)
    obtain ⟨g, hg⟩ := h.irreducibles P hP (pullbackTypedEmbedding C e)
    refine ⟨castEmbedding (encodeEmbedding g) hEncode rfl, ?_⟩
    intro x
    exact (castEmbedding_apply (encodeEmbedding g) hEncode rfl x).trans (hg x)

theorem HE.of_native {L : Signature.{u}} {V W : Type v}
    {C : Typed L V} {D : Typed L W} {f : V → W}
    (h : Native.HE (encode C) (encode D) f) : HE C D f where
  sort_eq x := h.1.1 (.inr (C.sort x)) (fun _ => x) rfl
  map_func F x y := h.1.2 F (fun _ => x) y
  map_rel R xs := h.1.1 (.inl R) xs
  irreducibles E hE e := by
    obtain ⟨g, hg⟩ := h.2 (encode E) ((irreducible_encode_iff E).mpr hE) (encodeEmbedding e)
    exact ⟨decodeEmbedding g, hg⟩

theorem he_encode_iff {L : Signature.{u}} {V W : Type v}
    (C : Typed L V) (D : Typed L W) (f : V → W) :
    Native.HE (encode C) (encode D) f ↔ HE C D f := ⟨HE.of_native, HE.to_native⟩

theorem completion_encode_iff {L : Signature.{u}} {K : Class.{u,v} L}
    {V : Type v} (C : Typed L V) :
    Native.HasCompletion (EncodedClass K) (encode C) ↔ HasCompletion K C := by
  constructor
  · rintro ⟨W, hW, D, ⟨T, hT, rfl⟩, f, hf⟩
    exact ⟨W, hW, T, hT, f, HE.of_native hf⟩
  · rintro ⟨W, hW, D, hD, f, hf⟩
    exact ⟨W, hW, encode D, ⟨D, hD, rfl⟩, f, hf.to_native⟩

theorem irreduciblesIn_encode_iff {L : Signature.{u}} {K : Class.{u,v} L}
    {V : Type v} (C : Typed L V) :
    Native.IrreduciblesIn (EncodedClass K) (encode C) ↔ IrreduciblesIn K C := by
  constructor
  · intro h X E hE e
    obtain ⟨T, hT, hEq⟩ := h (encode E) ((irreducible_encode_iff E).mpr hE) (encodeEmbedding e)
    have ht : T = E := encode_injective hEq
    exact ht ▸ hT
  · intro h X E hE e
    let P := pullbackTyped C e
    have hEncode : encode P = E := encode_pullbackTyped C e
    have hP : P.Irreducible := (irreducible_encode_iff P).mp (by rw [hEncode]; exact hE)
    exact ⟨P, h P hP (pullbackTypedEmbedding C e), hEncode⟩

/-- Exact B034 subset-domain interface, derived from all actual induced tests. -/
theorem irreduciblesIn_subsets {L : Signature.{u}} {K : Class.{u,v} L}
    {V : Type v} {C : Typed L V} (h : IrreduciblesIn K C) : C.IrreduciblesIn K :=
  fun S hS hIr => h (C.induce S hS) hIr (CCO.UnarySupport.Structure.inclusion C S hS)

theorem b034_singleton_and_total {L : Signature.{u}} {K : Class.{u,v} L}
    (hK : CompletedClass K) {V : Type v} [Finite V] {C : Typed L V}
    (h : IrreduciblesIn K C) : (∀ x, K (C.singletonStructure x)) ∧ C.Total :=
  ⟨fun x => C.singleton_mem_class (irreduciblesIn_subsets h) x,
    C.total_of_irreducibles hK (irreduciblesIn_subsets h)⟩

end CCO.UnaryHN.Raw
