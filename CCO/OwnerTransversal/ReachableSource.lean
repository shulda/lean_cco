import CCO.OwnerTransversal.TypedSAP
import CCO.OwnerTransversal.ConditionalEPPA

/-! Public reachable-owner source instances discharge exactness from
the represented word. Original SAP and typed-language EPPA remain in
their separate, explicitly conditional branches. -/
universe v w t
namespace CCO.OwnerTransversal
open ParityHasse.Original
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] (cco : SemanticCCO.{0,v,0,w} S)
variable (E : ColourEq S ()) (hne : E ≠ ⊥)
variable (word : RawWord S () ()) (hword : RawWord.relation S word = E.val.r)
variable {B : Type} [Fintype B] (q : B → Quotient E.val) (hq : Function.Injective q)
include cco hne word hword

/-- C14–16 under the ACTUAL A03 word, without an extra exactness or
typed-source provider. The optional SAP assertion retains both premises. -/
theorem reachable_typed_source :
    letI : ∀ b, MulAction (ownerFixer S H E q) (OwnerCarrier S E q b) := ownerCarrierAction S H E q
    HomogeneousSource (typedOwnerSource S E q hq) (ownerFixer S H E q) ∧
      AgeAP (typedOwnerSource S E q hq) ∧
      SemanticCCO.{0,v,0,w} (typedOwnerSource S E q hq) ∧
      (AgeSAP S → (∀ x : M, Set.Infinite {y : M | E x y}) →
        AgeSAP (typedOwnerSource S E q hq)) := by
  letI : ∀ b, MulAction (ownerFixer S H E q) (OwnerCarrier S E q b) := ownerCarrierAction S H E q
  have he := exact_of_represented_word S E word hword
  exact ⟨typedOwner_homogeneous S H E q hq cco he,
    typedOwner_ageAP S H E q hq cco he,
    typedOwner_CCO S H E q hq cco hne word hword,
    fun sap hinf => typedOwner_ageSAP S H E q hq cco he sap hinf⟩

end CCO.OwnerTransversal
