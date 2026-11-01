import CCO.TerminalLattice.OriginalSparseThetaNoCentreSpectrum
import CCO.TerminalLattice.CentrePathSpectrum

/-!
# B050 source08 C27–C30: centre-containing actual OLD theta cycles

A genuine B002 marked projection is an injective simple cyclic
enumeration, and the original sparse theta network has exactly ONE
formal centre, placed at its last marked graph index. If that centre
appears in a projected cycle, at least one of its two incident spokes
is among the first n edges after omission of the last cyclic edge.

Every used old guard is nonempty and lies inside the original K-diversity.
The surviving spoke guard equals ALL K-diversity, hence original SAP
absorption/commutativity saturates the complementary ordered STRONG
menu path. This requires neither graph girth nor original CCO; bare
unconstrained spokes carry NO private occurrence and cannot enter B002
projection.

No quotient action, positive-word EXACT-profile assumption, original
CCO or synthetic STRONG identity is used.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- A truly cyclic finite enumeration of n+1 positions with n>0
has the following boundary fact: a vertex in the cycle is incident
to at least one edge among the FIRST n consecutive edges, no matter
which final edge is omitted. This keeps the original cyclic order. -/
theorem original_cyclic_nonlast_incident
    {α : Type*} {n : Nat} (hn : 0 < n)
    (points : Fin (n+1) → α) (centre : α)
    (hCentre : ∃ j : Fin (n+1), points j = centre) :
    ∃ k : Fin n,
      points k.castSucc = centre ∨
      points (CCO.cyclicNext (Nat.succ_pos n) k.castSucc) = centre := by
  obtain ⟨j,hj⟩ := hCentre
  by_cases hjBefore : j.val < n
  · let k : Fin n := ⟨j.val,hjBefore⟩
    have hSame : k.castSucc = j := Fin.ext rfl
    exact ⟨k, Or.inl (by rw [hSame]; exact hj)⟩
  · have hjLast : j.val = n := by
      have hjBound := j.isLt
      omega
    let k : Fin n := ⟨n-1,by omega⟩
    have hSuccessor : k.succ = j := by
      apply Fin.ext
      dsimp [k]
      omega
    refine ⟨k, Or.inr ?_⟩
    rw [original_cyclicNext_castSucc hn k, hSuccessor]
    exact hj

/-- If a REAL B002 projected sparse-theta edge touches the unique
last centre at either end of its cyclic traversal, its actual
canonical unordered pair has that centre as its RIGHT endpoint.
It cannot be the LEFT endpoint because the other index is smaller.
This is a fact about the literal B002 edge, not an invented spoke. -/
theorem originalSparseTheta_projected_spoke_of_incidence
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
    (C : SimpleCycle
      (originalSparseThetaDiagram
        S H sap W K hK spokes menus families hSpec))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (originalThetaPresentations S
        (originalSparseThetaSelection S W spokes families))
      (originalThetaPresentations_nonempty S H sap
        (originalSparseThetaSelection S W spokes families)
        (originalSparseThetaGuard S W K menus)
        (originalSparseTheta_guards_valid
          S W K hK spokes menus families hSpec)) C)
    (k : Fin B.length)
    (hIncident :
      B.vertices k = oldSparseCentre W ∨
      B.vertices (CCO.cyclicNext B.length_pos k) = oldSparseCentre W) :
    (B.edges k).val.2.val = W.size := by
  have hLeftNe :
      CCO.RawExact.QuotientExpansion.left (B.edges k) ≠
        oldSparseCentre W := by
    intro hh
    have hv : (B.edges k).val.1.val = W.size := by
      have hh' := congrArg Fin.val hh
      simpa [CCO.RawExact.QuotientExpansion.left, oldSparseCentre] using hh'
    have hlt := (B.edges k).property
    have hbound := (B.edges k).val.2.isLt
    omega
  have hRightCentre (hh :
      CCO.RawExact.QuotientExpansion.right (B.edges k) =
        oldSparseCentre W) : (B.edges k).val.2.val = W.size := by
    have hh' := congrArg Fin.val hh
    simpa [CCO.RawExact.QuotientExpansion.right, oldSparseCentre] using hh'
  rcases B.endpoints k with ⟨hs,ht⟩ | ⟨hs,ht⟩
  · rcases hIncident with hc | hc
    · exact False.elim (hLeftNe (hs.symm.trans hc))
    · exact hRightCentre (ht.symm.trans hc)
  · rcases hIncident with hc | hc
    · exact hRightCentre (hs.symm.trans hc)
    · exact False.elim (hLeftNe (ht.symm.trans hc))

/-- On a genuine B002 projection of length n+1 containing the
original centre, a present ORIGINAL spoke lies among the first n
edges. This is the precise missing centre-star incidence fact after
deleting the last cyclic edge, regardless of its label/orientation.
-/
theorem originalSparseTheta_projected_nonlast_spoke
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g n : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
    (C : SimpleCycle
      (originalSparseThetaDiagram
        S H sap W K hK spokes menus families hSpec))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (originalThetaPresentations S
        (originalSparseThetaSelection S W spokes families))
      (originalThetaPresentations_nonempty S H sap
        (originalSparseThetaSelection S W spokes families)
        (originalSparseThetaGuard S W K menus)
        (originalSparseTheta_guards_valid
          S W K hK spokes menus families hSpec)) C)
    (hLength : B.length = n+1)
    (hCentre : ∃ j : Fin B.length,
      B.vertices j = oldSparseCentre W) :
    ∃ k : Fin n,
      (B.edges (Fin.cast hLength.symm k.castSucc)).val.2.val = W.size := by
  let points : Fin (n+1) → Fin (W.size+1) :=
    fun k => B.vertices (Fin.cast hLength.symm k)
  have hn : 0 < n := by
    have hthree := B.length_ge_three
    omega
  have hOn : ∃ j : Fin (n+1), points j = oldSparseCentre W := by
    obtain ⟨j,hj⟩ := hCentre
    refine ⟨Fin.cast hLength j, ?_⟩
    have hCast :
        Fin.cast hLength.symm (Fin.cast hLength j) = j := Fin.ext rfl
    change B.vertices (Fin.cast hLength.symm (Fin.cast hLength j)) =
      oldSparseCentre W
    rw [hCast]
    exact hj
  obtain ⟨k,hIncident⟩ :=
    original_cyclic_nonlast_incident hn points
      (oldSparseCentre W) hOn
  let t : Fin B.length := Fin.cast hLength.symm k.castSucc
  have hCastNext :
      Fin.cast hLength.symm
        (CCO.cyclicNext (Nat.succ_pos n) k.castSucc) =
      CCO.cyclicNext B.length_pos t := by
    apply Fin.ext
    change (k.val+1) % (n+1) = (k.val+1) % B.length
    rw [hLength]
  have hOriginalIncident :
      B.vertices t = oldSparseCentre W ∨
      B.vertices (CCO.cyclicNext B.length_pos t) = oldSparseCentre W := by
    rcases hIncident with hc | hc
    · exact Or.inl hc
    · right
      change B.vertices (Fin.cast hLength.symm
        (CCO.cyclicNext (Nat.succ_pos n) k.castSucc)) =
        oldSparseCentre W at hc
      rw [hCastNext] at hc
      exact hc
  exact ⟨k,originalSparseTheta_projected_spoke_of_incidence
    S H sap W K hK spokes menus families hSpec C B t hOriginalIncident⟩

/-- ACTUAL source C28 centre-containing C30 path: after deleting
the arbitrary final cyclic marked edge, the true ordered list still
contains an ORIGINAL K-diversity spoke. All other guards are genuine
nonempty original K-subpalettes, so the established SAP absorption
makes the complete complementary STRONG spectrum equal K-diversity.

This is not an extra premise that a projected root map exists.
-/
theorem originalSparseTheta_centre_complement_spectrum
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g n : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
    (hContained : ∀ j : Fin r,
      menus j ⊆ originalEquivDiversityPalette S K)
    (C : SimpleCycle
      (originalSparseThetaDiagram
        S H sap W K hK spokes menus families hSpec))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (originalThetaPresentations S
        (originalSparseThetaSelection S W spokes families))
      (originalThetaPresentations_nonempty S H sap
        (originalSparseThetaSelection S W spokes families)
        (originalSparseThetaGuard S W K menus)
        (originalSparseTheta_guards_valid
          S W K hK spokes menus families hSpec)) C)
    (hLength : B.length = n+1)
    (hCentre : ∃ j : Fin B.length,
      B.vertices j = oldSparseCentre W) :
    originalPositiveStrongPath S
      (List.ofFn (fun k : Fin n =>
        originalSparseThetaGuard S W K menus
          (B.edges (Fin.cast hLength.symm k.castSucc)))) =
      some (originalEquivDiversityPalette S K) := by
  classical
  let path : Fin n → S.Menu i i := fun k =>
    originalSparseThetaGuard S W K menus
      (B.edges (Fin.cast hLength.symm k.castSucc))
  have hEvery (k : Fin n) :
      (path k).Nonempty ∧
        path k ⊆ originalEquivDiversityPalette S K := by
    have hPresent :=
      originalTheta_projected_edge_has_branch S H sap
        (originalSparseThetaSelection S W spokes families)
        (originalSparseThetaGuard S W K menus)
        (originalSparseTheta_guards_valid
          S W K hK spokes menus families hSpec) C B
          (Fin.cast hLength.symm k.castSucc)
    exact originalSparseThetaGuard_present_in_K S W K hK
      spokes menus families hSpec hContained
        (B.edges (Fin.cast hLength.symm k.castSucc)) hPresent
  have hAll :
      ∀ D ∈ List.ofFn path,
        D.Nonempty ∧ D ⊆ originalEquivDiversityPalette S K :=
    List.forall_mem_ofFn_iff.mpr hEvery
  obtain ⟨k,hCentreEdge⟩ :=
    originalSparseTheta_projected_nonlast_spoke S H sap
      W K hK spokes menus families hSpec C B hLength hCentre
  have hSpoke : path k = originalEquivDiversityPalette S K :=
    originalSparseThetaGuard_centre S W K menus
      (B.edges (Fin.cast hLength.symm k.castSucc)) hCentreEdge
  have hMember :
      originalEquivDiversityPalette S K ∈ List.ofFn path := by
    rw [← hSpoke]
    exact List.mem_ofFn.mpr ⟨k,rfl⟩
  exact original_K_spoke_occurrence_saturates_path
    S H sap K (List.ofFn path) hAll hMember

end CCO.TerminalLattice
