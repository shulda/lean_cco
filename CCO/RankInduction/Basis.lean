import CCO.FiniteLift.Source
import CCO.Owners.Master.Assembly
import CCO.RelativeMI.Consumer

/-! Actual-source rank and the bound P/O/U predicates. Plain rooted
witnesses do not assert closure of their chosen carrier. The stronger
closed choice and its lower schema are separate predicates. -/

universe v w t
namespace CCO.RankInduction
open RawExact Owners.Product Owners.Provider

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable (G : Type t) [Group G] [MulAction G M]

/-- All named atoms are actual diversity pair orbitals; equality is `none`. -/
noncomputable def rank : ℕ := Nat.card (S.Atom () ())

abbrev Witness (safe : Set (S.Atom () ())) (A0 W : Set M) : Prop :=
  FiniteLift.OrdinaryWitness (G := G) (FiniteLift.aclSet G) (S.menuRel safe) A0 W

/-- The original, plain P predicate; the output need only contain acl(A0). -/
def Rooted : Prop :=
  ∀ safe : Set (S.Atom () ()),
    FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe) →
    ∀ A0 : Set M, A0.Finite → A0.Nonempty →
      ∃ W : Set M, Witness S G safe A0 W

/-- Internal strengthened constructor choice, on the SAME rooted carrier. -/
def ClosedRooted : Prop :=
  ∀ safe : Set (S.Atom () ()),
    FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe) →
    ∀ A0 : Set M, A0.Finite → A0.Nonempty →
      ∃ W : Set M, Witness S G safe A0 W ∧ FiniteLift.aclSet G W = W

theorem ClosedRooted.rooted (h : ClosedRooted S G) : Rooted S G := by
  intro safe hs A0 finiteA nonemptyA
  obtain ⟨W,hW,-⟩ := h safe hs A0 finiteA nonemptyA
  exact ⟨W,hW⟩

variable [Countable M] (H : HomogeneousSource S G)
variable (cco : SemanticCCO.{0,v,v,w} S)

/-- U is genuine existence of one full M1--M4 owner master, not its
conditional EPPA-antecedent implication. -/
def MasterProperty : Prop :=
  ∀ (A0 : Set M), A0.Finite → A0.Nonempty →
    Nonempty (Owners.Master.ActualMaster.{v,w,t,v} S H cco A0)

/-- The plain rank step's BOUND antecedent, only for nonidentity exact
quotients. It never assumes a current-rank conclusion. -/
def Lower : Prop :=
  ∀ E : ExactCRT.ExactEq S H cco (), E ≠ ⊥ →
    letI : CanonicalQuotients.Invariant G E.val := Owners.Product.exactInvariant S H cco E
    Rooted (Owners.Master.quotientSource S H cco E) G ∧
      OrdinaryEPPA G (Quotient E.val) ∧
      MasterProperty (Owners.Master.quotientSource S H cco E) G
        (Owners.Master.quotientSource_homogeneous S H cco E)
        (Owners.Master.quotientSource_cco S H cco E)

/-- Additional BOUND lower choice only for the strengthened constructor. -/
def LowerClosed : Prop :=
  ∀ E : ExactCRT.ExactEq S H cco (), E ≠ ⊥ →
    letI : CanonicalQuotients.Invariant G E.val := Owners.Product.exactInvariant S H cco E
    ClosedRooted (Owners.Master.quotientSource S H cco E) G

end CCO.RankInduction
