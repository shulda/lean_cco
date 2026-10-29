import CCO.ProfileHelly.FreeAmalgam
import CCO.ProfileHelly.FreeAmalgamCycles
import CCO.ProfileHelly.SpanCompletion
import CCO.ProfileHelly.Properties

/-! The exact ONE source result: positive-profile Helly implies semantic
CCO, and its optional distinct-fork SAP clause. All actual table/finite
class providers are discharged; no desired conclusion is an input. -/
universe u v z
namespace CCO.ProfileHelly
variable {ι : Type u} {T : Table.{u,v} ι}

theorem profile_helly_sap (laws : TableLaws T) (helly : Word.Helly (T := T)) :
    StrongAmalgamation.{u,v,z} T := by
  intro A L R hA hL hR sortA sortL sortR B C D f g
  let F := freeAmalgam B C D f g
  let : Finite F.Carrier := F.finiteCarrier
  have alg : F.network.Algebraic :=
    F.network.algebraic_of_complete_cover C D F.left F.right F.covered F.edge_factor laws
  obtain ⟨N,_,l,r,_,_,hcomm,hcross⟩ := complete_span laws helly B C D f g
    F.network alg F.left F.right F.commutes F.intersection
  exact ⟨F.Carrier,F.finiteCarrier,F.sort,N,l,r,hcomm,hcross⟩

/-- `lem:helly-to-cco`: the source optional fork premise occurs ONLY in
the SAP clause. It is not an assumption of the CCO/constructor branch. -/
theorem helly_to_cco (laws : TableLaws T) (helly : Word.Helly (T := T)) :
    ProfileHellyConverse.{u,v,z} T :=
  ⟨profile_helly_semantic laws helly,fun _ => profile_helly_sap laws helly⟩

/-- Under the intended nonempty-total FULL class, the required forks are
actually realized, so the source conditional SAP clause is discharged. -/
theorem source_providers (laws : TableLaws T) (helly : Word.Helly (T := T)) :
    SemanticHomCCO.{u,v,z} T ∧ DistinctForks T ∧ StrongAmalgamation.{u,v,z} T :=
  ⟨(helly_to_cco laws helly).1,distinct_forks laws,
    (helly_to_cco laws helly).2 (distinct_forks laws)⟩

end CCO.ProfileHelly
