import CCO.RankInduction.Rank
import CCO.RankInduction.OrdinaryReadout
import CCO.RankInduction.OrbitalTransfer
import CCO.FinitePackets.Normalization.DescentSource

/-! Universal-source strong induction, with the actual order Pcl, O, U.
The rank constructor is an INTERNAL implication argument here; the final
source theorem supplies the constructed rank step, not an external axiom. -/

universe v w t
namespace CCO.RankInduction
noncomputable section
open RawExact ExactCRT Owners.Product Owners.Provider
open FinitePackets.Normalization

variable {G : Type t} [Group G]

/-- An original source may have diversity names in ANY universe. Its
actual exact quotient has names in the carrier universe and therefore
belongs to the universal induction family, also for the identity cut. -/
def namedQuotientNode {M : Type v} [MulAction G M] [Countable M]
    (S : AtomicSource.{0,v,w} Unit (fun _ => M)) (H : HomogeneousSource S G)
    (cco : SemanticCCO.{0,v,v,w} S) (E : ExactEq S H cco ()) : SourceNode.{v,t} G where
  Carrier := Quotient E.val
  source := Owners.Master.quotientSource S H cco E
  action := by
    letI : CanonicalQuotients.Invariant G E.val := Owners.Product.exactInvariant S H cco E
    infer_instance
  countable := Owners.Master.quotientSource_countable S H cco E
  homogeneous := Owners.Master.quotientSource_homogeneous S H cco E
  cycles := Owners.Master.quotientSource_cco S H cco E

def exactNode (N : SourceNode.{v,t} G)
    (E : ExactEq N.source N.homogeneous N.cycles ()) : SourceNode.{v,t} G where
  Carrier := Quotient E.val
  source := Owners.Master.quotientSource N.source N.homogeneous N.cycles E
  action := by
    letI : CanonicalQuotients.Invariant G E.val :=
      Owners.Product.exactInvariant N.source N.homogeneous N.cycles E
    infer_instance
  countable := Owners.Master.quotientSource_countable N.source N.homogeneous N.cycles E
  homogeneous := Owners.Master.quotientSource_homogeneous N.source N.homogeneous N.cycles E
  cycles := Owners.Master.quotientSource_cco N.source N.homogeneous N.cycles E

def PhaseComplete (N : SourceNode.{v,t} G) : Prop :=
  ClosedRooted N.source G ∧ OrdinaryEPPA G N.Carrier ∧
    MasterProperty N.source G N.homogeneous N.cycles

def AllAtRank (n : ℕ) : Prop :=
  ∀ N : SourceNode.{v,t} G, rank N.source = n → PhaseComplete N

abbrev Phase := Fin 3

def proofMeasure (x : ℕ × Phase) : ℕ := 3 * x.1 + x.2.val

def ProofOrder (x y : ℕ × Phase) : Prop := proofMeasure x < proofMeasure y

theorem proofOrder_lex (x y : ℕ × Phase) :
    ProofOrder x y ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2) := by
  have hx := x.2.isLt
  have hy := y.2.isLt
  simp only [ProofOrder,proofMeasure,Fin.lt_def]
  omega

theorem proofOrder_wellFounded : WellFounded ProofOrder :=
  InvImage.wf proofMeasure Nat.lt_wfRel.wf

/-- At rank n the induction hypothesis covers ALL sources at every
smaller rank. This is the exact scope needed by each actual quotient. -/
theorem phased_induction
    (step : ∀ N : SourceNode.{v,t} G,
      Lower N.source G N.homogeneous N.cycles →
      LowerClosed N.source G N.homogeneous N.cycles → ClosedRooted N.source G) :
    ∀ n, AllAtRank.{v,t} (G := G) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro N rankN
    have lower : Lower N.source G N.homogeneous N.cycles := by
      intro E proper
      let _ : CanonicalQuotients.Invariant G E.val :=
        Owners.Product.exactInvariant N.source N.homogeneous N.cycles E
      let Q := exactNode N E
      have smaller : rank Q.source < n :=
        (exact_quotient_rank_lt N.source N.homogeneous N.cycles E proper).trans_eq rankN
      have complete := ih (rank Q.source) smaller Q rfl
      exact ⟨ClosedRooted.rooted _ G complete.1,complete.2.1,complete.2.2⟩
    have lowerClosed : LowerClosed N.source G N.homogeneous N.cycles := by
      intro E proper
      let _ : CanonicalQuotients.Invariant G E.val :=
        Owners.Product.exactInvariant N.source N.homogeneous N.cycles E
      let Q := exactNode N E
      have smaller : rank Q.source < n :=
        (exact_quotient_rank_lt N.source N.homogeneous N.cycles E proper).trans_eq rankN
      exact (ih (rank Q.source) smaller Q rfl).1
    have pcl : ClosedRooted N.source G := step N lower lowerClosed
    have ordinary : OrdinaryEPPA G N.Carrier :=
      ordinary_from_rooted N.source N.homogeneous (ClosedRooted.rooted _ G pcl)
    have allQuotients : Owners.Master.AllQuotientsEPPA N.source N.homogeneous N.cycles := by
      intro E
      let _ : CanonicalQuotients.Invariant G E.val :=
        Owners.Product.exactInvariant N.source N.homogeneous N.cycles E
      by_cases identity : E = ⊥
      · subst E
        let K : ExactEq N.source N.homogeneous N.cycles () := ⊥
        let e : N.Carrier ≃ Quotient K.val :=
          (CanonicalQuotients.identityEquiv K.val (fun _ _ => Iff.rfl)).symm
        exact ordinaryEPPA_equiv e (fun _ _ => rfl) ordinary
      · exact (lower E identity).2.1
    have master : MasterProperty N.source G N.homogeneous N.cycles := by
      intro A0 finiteA nonemptyA
      exact Owners.Master.actual_owner_master N.source N.homogeneous N.cycles
        A0 finiteA nonemptyA allQuotients
    exact ⟨pcl,ordinary,master⟩

section ArbitraryNames
variable {M : Type v} [MulAction G M] [Countable M]
variable (S : AtomicSource.{0,v,w} Unit (fun _ => M)) (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{0,v,v,w} S)
variable (complete : ∀ N : SourceNode.{v,t} G, PhaseComplete N)
include complete

/-- AFTER the universal phased induction is closed, its completed actual
quotients discharge the lower schema for an arbitrary diversity-name
universe. This is not an induction call at the original source's rank. -/
theorem universal_lower : Lower S G H cco := by
  intro E _
  let _ : CanonicalQuotients.Invariant G E.val := Owners.Product.exactInvariant S H cco E
  have result := complete (namedQuotientNode S H cco E)
  exact ⟨ClosedRooted.rooted _ G result.1,result.2.1,result.2.2⟩

theorem universal_lower_closed : LowerClosed S G H cco := by
  intro E _
  exact (complete (namedQuotientNode S H cco E)).1

/-- Includes the identity quotient only AFTER the all-ranks conjunction
has been proved. No ordinary conclusion is fed back into its own P step. -/
theorem universal_all_quotients : Owners.Master.AllQuotientsEPPA S H cco := by
  intro E
  exact (complete (namedQuotientNode S H cco E)).2.1

end ArbitraryNames

end
end CCO.RankInduction
