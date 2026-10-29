import CCO.Owners.Master.SourceActions
import CCO.Owners.Master.SourceEPPA
import CCO.Owners.Master.SourcePackets
import CCO.Owners.Master.SourceBase
import CCO.Owners.Master.SourceExport

/-! Actual finite source assembly. Each maximal-complement stage invokes
ONE already proved local owner provider. The callbacks, full group
identities, packet projections and actual singleton decorations are all
discharged before the headline theorem is exported.
-/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable {T : Set A} {U : Finset (Position S H cco)}

def sourceSuccessor (B : SourceStage.{v,w,t,z} S H cco T U)
    {p : Position S H cco} (next : Next U p) (upU : IsUpset U)
    (W : LocalFactor S H cco B next) :
    SourceStage.{v,w,t,z} S H cco T (insert p U) where
  finite := (sourceStep S H cco B next upU W).stage
  decorations := {
    contains := sourceStep_contains S H cco B next upU W
    closed := sourceStep_closed S H cco B next upU W
    eppa := sourceStep_eppa S H cco B next upU W
    m3 := sourceStep_m3 S H cco B next upU W }
  compatible := (sourceStep S H cco B next upU W).stage_crt (by
    intro I _ f valid p q hp hpq
    obtain ⟨i,hi,hpi⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_biUnion.mpr ⟨i,hi,valid i hpi hpq⟩) B.compatible

/-- Recursion follows a genuine max-first schedule. Exactly one local
provider is called at each cons, and none is called for the empty list. -/
theorem complete_from_schedule (finiteT : T.Finite) (ep : AllQuotientsEPPA S H cco)
    (l : List (Position S H cco)) (upU : IsUpset U) (order : ValidAfter U l)
    (B : SourceStage.{v,w,t,z} S H cco T U) :
    Nonempty (SourceStage.{v,w,t,z} S H cco T Finset.univ) := by
  induction l generalizing U with
  | nil =>
    change U = Finset.univ at order
    subst U
    exact ⟨B⟩
  | cons p rest ih =>
    obtain ⟨next,restOrder⟩ := order
    obtain ⟨W⟩ := exists_localFactor S H cco B next finiteT ep
    exact ih (next_insert_upset upU next) restOrder (sourceSuccessor S H cco B next upU W)

/-- Actual construction of the complete finite system, with no abstract
decorated-diagram callback left as a source hypothesis. -/
theorem complete_source_stage (T : Set A) (finiteT : T.Finite)
    (ep : AllQuotientsEPPA S H cco) :
    Nonempty (SourceStage.{v,w,t,z} S H cco T Finset.univ) := by
  obtain ⟨l,order,-,-,-⟩ := exists_schedule (P := Position S H cco)
  exact complete_from_schedule S H cco finiteT ep l empty_upset order
    (initialSourceStage S H cco T)

/-- The simultaneous finite exact-owner master: ONE actual finite real
carrier has all four clauses on its ENTIRE actual exact quotient system.
Ordinary EPPA of every exact quotient, INCLUDING Id, remains the explicit
source premise. This theorem proves no rooted or unconditional EPPA result. -/
theorem actual_owner_master (T : Set A) (finiteT : T.Finite) (nonemptyT : T.Nonempty)
    (ep : AllQuotientsEPPA S H cco) : Nonempty (ActualMaster.{v,w,t,z} S H cco T) := by
  obtain ⟨B⟩ := complete_source_stage S H cco T finiteT ep
  let M := B.actualMaster S H cco
  exact ⟨{ M with nonempty := nonemptyT.mono M.contains }⟩

end
end CCO.Owners.Master
