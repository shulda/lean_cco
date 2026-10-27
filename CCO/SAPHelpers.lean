import CCO.Finite
import CCO.FiniteHelpers

/-!
# Exact-overlap form of real age-SAP

This is a *proved* conversion of the finite induced-age SAP interface,
not a new amalgamation provider. In the result the common vertices are
exactly those coming from the specified COMPLETE old base, including
when the named sorts repeat. This form is used for strong triangles,
Set-Pasch, and fresh pointwise-stabilizer orbits.
-/

universe u v

namespace CCO

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)

/-- In an actual strong amalgam, two factor images coincide if and only
if the corresponding vertices come from one and the same old base point.
The reverse direction is an explicit consequence of the commuting
amalgamation square; it is not an AP-only property. -/
theorem AgeSAP.amalgamate_exact_overlap (hSAP : AgeSAP S)
    (C A B : FiniteInduced (X := X))
    (eCA : InducedEmbedding S C A)
    (eCB : InducedEmbedding S C B) :
    ∃ (D : FiniteInduced (X := X))
        (eAD : InducedEmbedding S A D)
        (eBD : InducedEmbedding S B D),
      (∀ c : ↥C.vertices,
        eAD.toEmbedding (eCA.toEmbedding c) =
          eBD.toEmbedding (eCB.toEmbedding c)) ∧
      (∀ (a : ↥A.vertices) (b : ↥B.vertices),
        eAD.toEmbedding a = eBD.toEmbedding b ↔
          ∃ c : ↥C.vertices,
            eCA.toEmbedding c = a ∧ eCB.toEmbedding c = b) := by
  obtain ⟨D, eAD, eBD, hbase, hcollision⟩ :=
    hSAP.strong_amalgamate C A B eCA eCB
  refine ⟨D, eAD, eBD, hbase, ?_⟩
  intro a b
  constructor
  · exact hcollision a b
  · rintro ⟨c, hca, hcb⟩
    calc
      eAD.toEmbedding a = eAD.toEmbedding (eCA.toEmbedding c) := by rw [hca]
      _ = eBD.toEmbedding (eCB.toEmbedding c) := hbase c
      _ = eBD.toEmbedding b := by rw [hcb]

/-- A chosen point of one factor outside the specified base remains
distinct from EVERY point of the other factor in an SAP amalgam. -/
theorem AgeSAP.amalgamate_avoiding_old_point (hSAP : AgeSAP S)
    (C A B : FiniteInduced (X := X))
    (eCA : InducedEmbedding S C A)
    (eCB : InducedEmbedding S C B)
    (a : ↥A.vertices)
    (ha : ∀ c : ↥C.vertices, eCA.toEmbedding c ≠ a) :
    ∃ (D : FiniteInduced (X := X))
        (eAD : InducedEmbedding S A D)
        (eBD : InducedEmbedding S B D),
      (∀ c : ↥C.vertices,
        eAD.toEmbedding (eCA.toEmbedding c) =
          eBD.toEmbedding (eCB.toEmbedding c)) ∧
      (∀ b : ↥B.vertices,
        eAD.toEmbedding a ≠ eBD.toEmbedding b) := by
  obtain ⟨D, eAD, eBD, hbase, hoverlap⟩ :=
    hSAP.amalgamate_exact_overlap S C A B eCA eCB
  refine ⟨D, eAD, eBD, hbase, ?_⟩
  intro b heq
  obtain ⟨c, hca, _⟩ := (hoverlap a b).mp heq
  exact ha c hca

end CCO
