import CCO.GuardedOldSeams.Envelope
import CCO.GuardedOldSeams.IdempotentMI

/-! Source TF1: first discharge actual FULL RAW exactness by the original
literal word ww; only THEN apply the represented exact lattice MI theorem. -/
universe u v w t
namespace CCO.GuardedOldSeams
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)
variable (cco : SemanticCCO.{u,v,max u v,w} S)
include sap

theorem envelope_mi_pointwise {i : ι} (word : PositiveWord S i i)
    (he : S.product (PositiveWord.profile S word) (PositiveWord.profile S word) =
      PositiveWord.profile S word) (x y : X i) :
    envelope S (PositiveWord.profile S word) he x y ↔
      ∀ J : ExactCRT.ExactEq S H cco i,
        (∀ a b, envelope S (PositiveWord.profile S word) he a b → J.val a b) →
          InfIrred J → J.val x y :=
  represented_exact_mi_of_isExact S H cco
    (envelope S (PositiveWord.profile S word) he).val
    (envelope_raw_exact S H sap word he) x y

theorem envelope_mi_intersection {i : ι} (word : PositiveWord S i i)
    (he : S.product (PositiveWord.profile S word) (PositiveWord.profile S word) =
      PositiveWord.profile S word) :
    representedExactMIIntersection S H cco
      ⟨(envelope S (PositiveWord.profile S word) he).val,envelope_raw_exact S H sap word he⟩ =
        (envelope S (PositiveWord.profile S word) he).val :=
  represented_exact_mi_intersection_eq S H cco _

end CCO.GuardedOldSeams
