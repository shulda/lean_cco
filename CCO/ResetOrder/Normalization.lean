import CCO.ResetOrder.Generic.FiniteAge

/-! The generic inheritance theorem works for arbitrary fixed partial-function
signatures, not just unary languages. The only functor data assumed are exactly
the source's universe/map preservation and strict idempotence. -/
universe u v
namespace CCO.ResetOrder.Generic
variable {S : Type u} {L : Language S} (K : Age.{u,v} L)

structure Normalizer where
  normalize : (A : Object.{u,v} L) → Structure L A.Carrier
  member : ∀ A, K A → K (A.withData (normalize A))
  map : ∀ {A B}, K A → K B → Object.Embedding A B →
    Object.Embedding (A.withData (normalize A)) (B.withData (normalize B))
  map_point : ∀ {A B} (hA : K A) (hB : K B) (e : Object.Embedding A B),
    (map hA hB e).point = e.point
  idempotent : ∀ A, K A → normalize (A.withData (normalize A)) = normalize A

namespace Normalizer
variable {K} (N : Normalizer K)

def object (A : Object.{u,v} L) : Object.{u,v} L := A.withData (N.normalize A)
def Fixed (A : Object.{u,v} L) : Prop := N.normalize A = A.data
def fixedClass : Age.{u,v} L := fun A => K A ∧ N.Fixed A

theorem normalized_fixed (A : Object.{u,v} L) (hA : K A) : N.Fixed (N.object A) :=
  N.idempotent A hA

/-- Strict structure equality also gives equality of the bundled finite object. -/
theorem fixed_object_eq {A : Object.{u,v} L} (hA : N.Fixed A) : N.object A = A := by
  change A.withData (N.normalize A) = A
  rw [hA]
  cases A
  rfl

def fromFixed {A B : Object.{u,v} L} (hA : K A) (hB : K B)
    (hfix : N.Fixed A) (e : Object.Embedding A B) : Object.Embedding A (N.object B) :=
  (N.map hA hB e).cast hfix rfl

@[simp] theorem fromFixed_point {A B : Object.{u,v} L} (hA : K A) (hB : K B)
    (hfix : N.Fixed A) (e : Object.Embedding A B) :
    (N.fromFixed hA hB hfix e).point = e.point := by
  exact (Structure.Embedding.point_cast (N.map hA hB e) hfix rfl).trans
    (N.map_point hA hB e)

/-- No categorical same-image uniqueness axiom: actual inducedness proves it. -/
theorem hereditary (hK : Hereditary L K) : Hereditary L N.fixedClass := by
  intro A B hB e
  have hA : K A := hK hB.1 e
  refine ⟨hA, ?_⟩
  let g : Object.Embedding (N.object A) B := (N.map hA hB.1 e).cast rfl hB.2
  exact Structure.Embedding.same_map_domain_unique g e (by
    exact (Structure.Embedding.point_cast (N.map hA hB.1 e) rfl hB.2).trans
      (N.map_point hA hB.1 e))

/-- Functoriality with a fixed source/intermediate object follows on literal maps. -/
theorem fromFixed_comp {A B C : Object.{u,v} L} (hA : K A) (hB : K B) (hC : K C)
    (hfixA : N.Fixed A) (hfixB : N.Fixed B)
    (g : Object.Embedding B C) (f : Object.Embedding A B) :
    N.fromFixed hA hC hfixA (g.compose f) =
      (N.fromFixed hB hC hfixB g).compose f := by
  apply Structure.Embedding.ext
  simp only [N.fromFixed_point, Structure.Embedding.compose]
  rfl

/-- Pull back a colouring; surjectivity onto the normalized embedding set is unused. -/
theorem arrow {A B C : Object.{u,v} L} (hA : K A) (hB : K B) (hC : K C)
    (hfixA : N.Fixed A) (hfixB : N.Fixed B) {k : ℕ} (h : Arrow L A B C k) :
    Arrow L A B (N.object C) k := by
  intro χ
  obtain ⟨g, c, hg⟩ := h (fun e => χ (N.fromFixed hA hC hfixA e))
  refine ⟨N.fromFixed hB hC hfixB g, c, ?_⟩
  intro f
  rw [← N.fromFixed_comp hA hB hC hfixA hfixB g f]
  exact hg f

theorem ramsey (hK : Ramsey L K) : Ramsey L N.fixedClass := by
  intro A B hA hB k
  obtain ⟨C, hC, hArrow⟩ := hK A B hA.1 hB.1 k
  exact ⟨N.object C, ⟨N.member C hC, N.normalized_fixed C hC⟩,
    N.arrow hA.1 hB.1 hC hA.2 hB.2 hArrow⟩

theorem jointEmbedding (hK : JointEmbedding L K) : JointEmbedding L N.fixedClass := by
  intro A B hA hB
  obtain ⟨C, hC, ⟨f⟩, ⟨g⟩⟩ := hK A B hA.1 hB.1
  exact ⟨N.object C, ⟨N.member C hC, N.normalized_fixed C hC⟩,
    ⟨N.fromFixed hA.1 hC hA.2 f⟩, ⟨N.fromFixed hB.1 hC hB.2 g⟩⟩

/-- The complete generic normalization export. SAP is deliberately not asserted. -/
theorem foundational_ramsey_normalization (hH : Hereditary L K) (hR : Ramsey L K) :
    Hereditary L N.fixedClass ∧ Ramsey L N.fixedClass ∧
      (JointEmbedding L K → JointEmbedding L N.fixedClass) :=
  ⟨N.hereditary hH, N.ramsey hR, N.jointEmbedding⟩

end Normalizer
end CCO.ResetOrder.Generic
