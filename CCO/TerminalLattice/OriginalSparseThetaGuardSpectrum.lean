import CCO.TerminalLattice.OriginalSparseThetaProjection
import CCO.TerminalLattice.OriginalLabelListThreshold
import CCO.TerminalLattice.OriginalStrongMenuFiniteCycle

/-!
# B050 source08 C27–C30: ACTUAL fine menu classification and long labelled paths

In the original multi-branch theta network, a genuinely PRESENT old
private pair is either a centre spoke with assigned K-diversity, or
a true W graph edge with its actual indexed assigned fine menu.
No absent pair becomes a source edge, and no individual old positive
typed word is required to have EXACTLY its assigned menu as its profile.

The positive STRONG menu-path pigeonhole is independent of the
syntactic way a finite list of genuinely labelled W edges is built.
It uses the already accepted original same-sort SAP commutativity,
the actual repeated-label power theorem, and the original finite
list counting theorem. It does not reorder letters inside typed words.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- A truly present OLD theta spoke has assigned menu exactly the
original K-diversity palette, including when several private
positive branches have different larger profiles. -/
theorem originalSparseThetaGuard_centre
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (menus : Fin r → S.Menu i i)
    (e : CCO.RawExact.QuotientExpansion.Edge (W.size+1))
    (hCentre : e.val.2.val = W.size) :
    originalSparseThetaGuard S W K menus e =
      originalEquivDiversityPalette S K := by
  simp [originalSparseThetaGuard, hCentre]

/-- A genuinely present non-centre OLD theta marked pair is a REAL
labelled W graph edge; its fine guard equals the associated original
menu T_j. We use the ACTUAL nonempty family rather than assume
graph adjacency for an abstract edge. -/
theorem originalSparseThetaGuard_present_graph
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (e : CCO.RawExact.QuotientExpansion.Edge (W.size+1))
    (hPresent : originalSparseThetaSelection S W spokes families e ≠ [])
    (hNotCentre : e.val.2.val ≠ W.size) :
    ∃ j : Fin r,
      originalSparseThetaGuard S W K menus e = menus j := by
  classical
  let x : Fin W.size :=
    ⟨e.val.1.val, by
      have hl := e.property
      have hr := e.val.2.isLt
      omega⟩
  let y : Fin W.size :=
    ⟨e.val.2.val, by
      have hr := e.val.2.isLt
      omega⟩
  have hAdj : W.graph.Adj x y := by
    by_contra hNo
    have hNone : originalSparseThetaSelection S W spokes families e = [] := by
      simp [originalSparseThetaSelection, hNotCentre, x, y, hNo]
    exact hPresent hNone
  refine ⟨W.label s(x,y), ?_⟩
  simp [originalSparseThetaGuard, hNotCentre, x, y, hAdj]

/-- Every REAL present private theta pair carries a nonempty fine
STRONG guard inside the original K-diversity. Source08 explicitly
requires the graph menus T_j to be submenus of K-diversity; the
branch profile specification alone does NOT imply this. -/
theorem originalSparseThetaGuard_present_in_K
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (K : ParityHasse.Original.ColourEq S i)
    (hK : (⊥ : ParityHasse.Original.ColourEq S i) < K)
    (spokes : List (PositiveWord S i i))
    (menus : Fin r → S.Menu i i)
    (families : Fin r → List (PositiveWord S i i))
    (hSpec : OriginalSparseThetaBranchSpec S K spokes menus families)
    (hMenus : ∀ j, menus j ⊆ originalEquivDiversityPalette S K)
    (e : CCO.RawExact.QuotientExpansion.Edge (W.size+1))
    (hPresent : originalSparseThetaSelection S W spokes families e ≠ []) :
    (originalSparseThetaGuard S W K menus e).Nonempty ∧
      originalSparseThetaGuard S W K menus e ⊆
        originalEquivDiversityPalette S K := by
  by_cases hCentre : e.val.2.val = W.size
  · rw [originalSparseThetaGuard_centre S W K menus e hCentre]
    exact ⟨original_nonzero_Kdiv_nonempty S K hK, Set.Subset.rfl⟩
  · obtain ⟨j,hGuard⟩ :=
      originalSparseThetaGuard_present_graph
        S W K spokes menus families e hPresent hCentre
    rw [hGuard]
    exact ⟨(hSpec.2 j).2.1, hMenus j⟩

/-- Pointwise SOURCE graph labels on any finite ordered old-menu path
admit a literal list of true label indices. A repeated menu may have
multiple labels; choose one ACTUAL witness at each list occurrence. -/
theorem original_menu_list_to_labels
    {i : ι} {r : Nat}
    (menus : Fin r → S.Menu i i)
    (ds : List (S.Menu i i))
    (hLabels : ∀ D ∈ ds, ∃ j : Fin r, D = menus j) :
    ∃ labels : List (Fin r), labels.map menus = ds := by
  induction ds with
  | nil =>
      exact ⟨[], rfl⟩
  | cons D rest ih =>
      obtain ⟨j,hj⟩ := hLabels D (by simp)
      obtain ⟨labels,hMap⟩ := ih (by
        intro d hd
        exact hLabels d (List.mem_cons_of_mem _ hd))
      refine ⟨j :: labels, ?_⟩
      simp [← hj, hMap]

/-- Sharp SOURCE C29 saturation in the actual ordered list of
STRONG menus, using pointwise genuine finite W labels rather than
assuming that a list of labels was already supplied syntactically.
After deletion of a closing edge, length strictly above r*(N-1)
suffices. All same-sort STRONG products are genuine old SAP products;
no positive identity, synthetic equality or CCO is used. -/
theorem original_labelled_menu_list_saturates
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ParityHasse.Original.ColourEq S i)
    {r N : Nat} (hN : 0 < N)
    (menus : Fin r → S.Menu i i)
    (ds : List (S.Menu i i))
    (hLong : r * (N-1) < ds.length)
    (hAll : ∀ j : Fin r,
      (menus j).Nonempty ∧
      menus j ⊆ originalEquivDiversityPalette S K)
    (hPower : ∀ j : Fin r,
      originalStrongPalettePower S (menus j) (N-1) =
        originalEquivDiversityPalette S K)
    (hLabels : ∀ D ∈ ds, ∃ j : Fin r, D = menus j) :
    originalPositiveStrongPath S ds =
      some (originalEquivDiversityPalette S K) := by
  obtain ⟨labels,hMap⟩ :=
    original_menu_list_to_labels S menus ds hLabels
  have hLen : labels.length = ds.length := by
    have hl := congrArg List.length hMap
    simpa only [List.length_map] using hl
  have hLong' : r * (N-1) < labels.length := by omega
  have hSat := original_long_ordered_label_path_saturates
    S H sap K hN menus labels hLong' hAll hPower
  rw [hMap] at hSat
  exact hSat

end CCO.TerminalLattice
