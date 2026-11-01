import CCO.TerminalLattice.ResetFromOrbitalHits
import CCO.ParityHasse.Sparse.Labelled

/-!
# B050 C35 receiving bridge: an ACTUAL old network realization yields all orbital hits

This is intentionally conditional on the concrete output of the still-open
C27–C34 private-path construction and SINGLE original CCO completion.
It does not postulate the source reset or assert an unconstructed network
exists. Its inputs are just one actual centre, actual roots, their exact
old fine colours and original K-equivalence, together with the edge
profiles of the sparse graph. The same actual centre colour selected
by the accepted B006 graph works for EVERY external old-G quotient
orbital. All squares are literal original STRONG fine-atom products.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- An already REALIZED old private sparse network produces C35's
simultaneous hits. This is a receiving implication, not the source
existence statement for the network; in particular no semantic CCO
map or original SAP is asserted by this theorem. -/
theorem original_realized_sparse_network_orbital_hits
    {i : ι} (J K : ColourEq S i)
    {q r g : Nat} (hr : 0 < r)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (frame : Fin q → S.Atom i i)
    (κ : Fin W.size → Fin q)
    (o : X i) (root : Fin W.size → X i)
    (T : Fin r → S.Menu i i)
    (hSpokes : ∀ v, S.colour o (root v) = some (frame (κ v)))
    (hSpokeK : ∀ v, K o (root v))
    (hEdges : ∀ v w, W.graph.Adj v w →
      S.menuRel (T (W.label s(v, w))) (root v) (root w))
    (hExternal : ∀ j : Fin r, ∀ c ∈ T j,
      c ∉ originalEquivDiversityPalette S J)
    (hEnumerate : ∀ x y : X i, K x y → ¬ J x y →
      ∃ j : Fin r,
        T j = originalQuotientOrbitalPalette S (G := G) J x y) :
    ∃ p z : X i, K p z ∧ ¬ J p z ∧
      ∀ x y : X i, K x y → ¬ J x y →
        (S.product
          (originalQuotientOrbitalPalette S (G := G) J p z)
          (originalQuotientOrbitalPalette S (G := G) J p z)
          ∩ originalQuotientOrbitalPalette S (G := G) J x y).Nonempty := by
  obtain ⟨d, hd⟩ := W.monochromatic κ
  let j₀ : Fin r := ⟨0, hr⟩
  obtain ⟨v₀, w₀, hAdj₀, hLabel₀, hv₀, hw₀⟩ := hd j₀
  have hSpokeV₀ : S.colour o (root v₀) = some (frame d) := by
    simpa only [hv₀] using hSpokes v₀
  have hSpokeW₀ : S.colour o (root w₀) = some (frame d) := by
    simpa only [hw₀] using hSpokes w₀
  have hEdge₀ : S.menuRel (T j₀) (root v₀) (root w₀) := by
    simpa only [hLabel₀] using hEdges v₀ w₀ hAdj₀
  obtain ⟨c₀, hc₀, hColour₀⟩ := hEdge₀
  have hNotJ : ¬ J o (root v₀) := by
    intro hJv
    have hJw : J o (root w₀) :=
      (J.property o (root v₀) o (root w₀)
        (hSpokeV₀.trans hSpokeW₀.symm)).mp hJv
    have hJvw : J (root v₀) (root w₀) :=
      J.val.trans (J.val.symm hJv) hJw
    exact hExternal j₀ c₀ hc₀
      ⟨root v₀, root w₀, hJvw, hColour₀⟩
  have hDistinct : o ≠ root v₀ := by
    intro heq
    exact (S.atomRel_ne hSpokeV₀) (congrArg (Sigma.mk i) heq)
  have hM : frame d ∈
      originalQuotientOrbitalPalette S (G := G) J o (root v₀) :=
    ⟨o, root v₀, ⟨hDistinct,
      originalQuotientOrbital_root S (G := G) J o (root v₀)⟩,
      hSpokeV₀⟩
  refine ⟨o, root v₀, hSpokeK v₀, hNotJ, ?_⟩
  intro x y hKxy hNotJxy
  obtain ⟨j, hTj⟩ := hEnumerate x y hKxy hNotJxy
  obtain ⟨v, w, hAdj, hLabel, hv, hw⟩ := hd j
  have hEdge : S.menuRel (T j) (root v) (root w) := by
    simpa only [hLabel] using hEdges v w hAdj
  obtain ⟨c, hc, hCol⟩ := hEdge
  have hTarget :
      c ∈ originalQuotientOrbitalPalette S (G := G) J x y := by
    rw [← hTj]
    exact hc
  have hSpokeV : S.colour o (root v) = some (frame d) := by
    simpa only [hv] using hSpokes v
  have hSpokeW : S.colour o (root w) = some (frame d) := by
    simpa only [hw] using hSpokes w
  have hReverse : S.colour (root v) o = some (frame d) :=
    (colour_symmetric S o (root v)).symm.trans hSpokeV
  refine ⟨c, ?_, hTarget⟩
  exact ⟨frame d, hM, frame d, hM,
    root v, o, root w, hReverse, hSpokeW, hCol⟩

/-- Under the ORIGINAL homogeneous SAP/fibre bridge, a concrete
realized network satisfying the preceding exact conditions implies
the actual source reset, BOTH STRONG and equality-inclusive RAW.
No reset conclusion is an input. The still-open work must CONSTRUCT
such a network by the single global original CCO completion. -/
theorem original_reset_from_realized_sparse_network
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ≤ K) (hJ : (⊥ : ColourEq S i) < J)
    {q r g : Nat} (hr : 0 < r)
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (frame : Fin q → S.Atom i i)
    (κ : Fin W.size → Fin q)
    (o : X i) (root : Fin W.size → X i)
    (T : Fin r → S.Menu i i)
    (hSpokes : ∀ v, S.colour o (root v) = some (frame (κ v)))
    (hSpokeK : ∀ v, K o (root v))
    (hEdges : ∀ v w, W.graph.Adj v w →
      S.menuRel (T (W.label s(v, w))) (root v) (root w))
    (hExternal : ∀ j : Fin r, ∀ c ∈ T j,
      c ∉ originalEquivDiversityPalette S J)
    (hEnumerate : ∀ x y : X i, K x y → ¬ J x y →
      ∃ j : Fin r,
        T j = originalQuotientOrbitalPalette S (G := G) J x y) :
    ∃ p z : X i, K p z ∧ ¬ J p z ∧
      (S.product
        (originalQuotientOrbitalPalette S (G := G) J p z)
        (originalQuotientOrbitalPalette S (G := G) J p z) =
          originalEquivDiversityPalette S K) ∧
      (RawSymmetric.compose
        (S.menuRel (originalQuotientOrbitalPalette S (G := G) J p z))
        (S.menuRel (originalQuotientOrbitalPalette S (G := G) J p z)) =
          K.val.r) := by
  obtain ⟨p, z, hpz, hNotJ, hHits⟩ :=
    original_realized_sparse_network_orbital_hits
      S (G := G) J K hr W frame κ o root T
      hSpokes hSpokeK hEdges hExternal hEnumerate
  obtain ⟨hStrong, hRaw⟩ :=
    original_complete_reset_strong_and_RAW_of_all_hits
      S H sap J K hJK hJ p z hpz hNotJ hHits
  exact ⟨p, z, hpz, hNotJ, hStrong, hRaw⟩

end CCO.TerminalLattice
