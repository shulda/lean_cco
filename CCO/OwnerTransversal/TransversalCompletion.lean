import CCO.OwnerTransversal.OriginRepair
import CCO.OwnerTransversal.AnchoredCaps
import CCO.OwnerTransversal.TypedTriangle

/-! The actual residual source supplies the reachable owner word.
Anchored raw completion followed by actual collision descent discharges
protected packet-separated CCO, with no original real-age SAP input. -/
universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

def OriginPattern.records {V : Type} (P : OriginPattern S H R V) : RawRecords S V where
  edge := P.edge
  diagonal := P.diagonal
  symmetric := P.symmetric

/-- C31–33: all three actual ingredients are constructed: the residual
word, one owner-correct anchored homomorphism, and its packet separation. -/
theorem protected_transversal_completion [Infinite M]
    {V : Type} [Fintype V] [DecidableEq V] (P : OriginPattern S H R V)
    (overB : ∀ x, P.owner x ∈ B)
    (compatible : ∀ x y a, P.edge x y = some a →
      ownerSaturate R.E.val (S.atomRel a) (P.owner x).out (P.owner y).out)
    (A : Finset V) (complete : RawRecords.CompleteOn S P.records A)
    (raw : V → M) (hraw : RawRecords.Hom S P.records raw)
    (j : V → NamedCarrier S H R B)
    (hj : ∀ x ∈ A, ∀ y ∈ A, ∀ a, P.edge x y = some a →
      col S (j x).val (j y).val = some a)
    (hOwn : ∀ x ∈ A, owner S H R (j x).val = P.owner x)
    (hSep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ¬ finitePacket S H (j x).val (j y).val) :
    ∃ f : OriginMap S H R B P, (∀ x ∈ A, f.point x = j x) ∧ f.PacketSeparated := by
  obtain ⟨p,n,hword⟩ := R.positive_word S H
  obtain ⟨f,hf,howner,hfix⟩ := anchored_completion S H P.records R.cco R.E
    (R.owner_ne_identity S H) (RealHull.Canonical.positiveEvenWord S p n) hword A complete
    (fun x => (P.owner x).out) raw (fun x => (j x).val) hraw hj compatible (by
      intro x hx
      apply Quotient.exact
      exact (Quotient.out_eq (P.owner x)).trans (hOwn x hx).symm)
  have ho (x : V) : owner S H R (f x) = P.owner x :=
    (Quotient.sound (howner x)).symm.trans (Quotient.out_eq (P.owner x))
  let f₀ : OriginMap S H R B P := {
    point x := ⟨f x,by rw [ho x]; exact overB x⟩
    owner := ho
    edge := hf }
  have hfix₀ (x : V) (hx : x ∈ A) : f₀.point x = j x := Subtype.ext (hfix x hx)
  obtain ⟨f',hkeep,hseparated⟩ := OriginMap.separate f₀ A (by
    intro x hx y hy hxy
    rw [hfix₀ x hx,hfix₀ y hy]
    exact hSep x hx y hy hxy)
  exact ⟨f',fun x hx => (hkeep x hx).trans (hfix₀ x hx),hseparated⟩

/-- The protected semantic CCO statement checks EVERY specified cycle
of the whole diagram; the raw hom is obtained from semantic CCO here. -/
theorem protected_transversal_CCO [Infinite M]
    {V : Type} [Fintype V] [DecidableEq V] (P : OriginPattern S H R V)
    (overB : ∀ x, P.owner x ∈ B)
    (compatible : ∀ x y a, P.edge x y = some a →
      ownerSaturate R.E.val (S.atomRel a) (P.owner x).out (P.owner y).out)
    (cycles : ∀ C : SimpleCycle P.records.diagram, CycleHom C)
    (A : Finset V) (complete : RawRecords.CompleteOn S P.records A)
    (j : V → NamedCarrier S H R B)
    (hj : ∀ x ∈ A, ∀ y ∈ A, ∀ a, P.edge x y = some a →
      col S (j x).val (j y).val = some a)
    (hOwn : ∀ x ∈ A, owner S H R (j x).val = P.owner x)
    (hSep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ¬ finitePacket S H (j x).val (j y).val) :
    ∃ f : OriginMap S H R B P, (∀ x ∈ A, f.point x = j x) ∧ f.PacketSeparated := by
  obtain ⟨raw⟩ := R.cco V P.records.diagram cycles
  apply protected_transversal_completion S H R B P overB compatible A complete
    raw.point (fun x y a ha => raw.preserves_edge x y
      (by intro he; subst y; rw [P.records.diagonal] at ha; cases ha) a ha) j hj hOwn hSep

/-- C34: the ACTUAL finite transversal age is exactly raw triangle
legality together with the actual owner-pair nonthin palettes.  Boundary
sizes zero, one and two are included in the same finite statement. -/
theorem transversal_triangle_defined {V : Type} [Fintype V] [DecidableEq V]
    (P : OriginPattern S H R V) (overB : ∀ x, P.owner x ∈ B)
    (compatible : ∀ x y a, P.edge x y = some a →
      ownerSaturate R.E.val (S.atomRel a) (P.owner x).out (P.owner y).out)
    (complete : RawRecords.CompleteOn S P.records Finset.univ) :
    (∃ f : OriginMap S H R B P, f.PacketSeparated) ↔
      RawRecords.TrianglesLegal S P.records := by
  constructor
  · rintro ⟨f,hsep⟩ x y z
    have hc (u v : V) : col S (f.point u).val (f.point v).val = P.edge u v := by
      by_cases huv : u = v
      · subst v
        exact ((col_none S _ _).mpr rfl).trans (P.diagonal u).symm
      · obtain ⟨a,ha⟩ := complete u (Finset.mem_univ _) v (Finset.mem_univ _) huv
        exact (f.edge u v a ha).trans ha.symm
    exact ⟨(f.point x).val,(f.point y).val,(f.point z).val,hc x y,hc x z,hc y z⟩
  · intro ht
    obtain ⟨raw,hraw,_⟩ := raw_triangle_fullness S H R.cco P.records
      (fun x y hxy => complete x (Finset.mem_univ _) y (Finset.mem_univ _) hxy) ht
    obtain ⟨p,n,hword⟩ := R.positive_word S H
    obtain ⟨f,hf,howner,_⟩ := anchored_completion_of_aligned S H P.records R.cco R.E
      (R.owner_ne_identity S H) (RealHull.Canonical.positiveEvenWord S p n) hword
      ∅ (by simp [RawRecords.CompleteOn]) (fun x => (P.owner x).out) raw hraw compatible
      (by simp)
    have ho (x : V) : owner S H R (f x) = P.owner x :=
      (Quotient.sound (howner x)).symm.trans (Quotient.out_eq (P.owner x))
    let f₀ : OriginMap S H R B P := {
      point x := ⟨f x,by rw [ho x]; exact overB x⟩
      owner := ho
      edge := hf }
    refine ⟨f₀,?_⟩
    intro x y hxy
    obtain ⟨a,ha⟩ := complete x (Finset.mem_univ _) y (Finset.mem_univ _) hxy
    exact P.nonthin x y a ha (f x) (f y) (hf x y a ha)

end
end CCO.OwnerTransversal
