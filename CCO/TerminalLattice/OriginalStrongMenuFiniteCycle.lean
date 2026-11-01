import CCO.TerminalLattice.OriginalStrongMenuChain
import CCO.TerminalLattice.PositiveFiniteChain
import Mathlib.Data.List.OfFn

/-!
# B050 source08 C26–C30: exact FIN-indexed old STRONG menu cycle witnesses

The independent theta guard may attach arbitrarily many original
positive typed word branches at one root pair. Only the ASSIGNED
nonempty fine STRONG menu T_e is common to their endpoint profiles;
no branch individually has to have exactly that profile.

Here we lift a finite OLD strong-menu chain to real root values at
each literal cyclic position. If the complementary path product is
K-diversity and one true fine closing menu D is nonempty and lies in
K-diversity, the entire cycle receives ONE simultaneous valuation
satisfying EVERY assigned menu at its true ordered pair of roots.

Neither original semantic CCO nor positive profile equality is used.
The empty-list equality case is only a metalevel recursion base;
it never becomes a STRONG identity factor.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Every genuine finite old menu path yields ACTUAL intermediate
original-sort root values, indexed by its exact edge list length,
with each consecutive pair satisfying its own STRONG menu relation. -/
theorem originalStrongMenuChain_fin_values
    {i : ι} (ds : List (S.Menu i i)) (x y : X i)
    (h : originalStrongMenuChain S ds x y) :
    ∃ values : Fin (ds.length + 1) → X i,
      values 0 = x ∧
      values (Fin.last ds.length) = y ∧
      ∀ k : Fin ds.length,
        S.menuRel (ds.get k) (values k.castSucc) (values k.succ) := by
  induction ds generalizing x y with
  | nil =>
      change x = y at h
      subst y
      refine ⟨fun _ => x, rfl, rfl, ?_⟩
      intro k
      exact Fin.elim0 k
  | cons D rest ih =>
      change ∃ z : X i,
        S.menuRel D x z ∧ originalStrongMenuChain S rest z y at h
      obtain ⟨z,hFirst,hRest⟩ := h
      obtain ⟨tail,htail0,htailLast,htailEdges⟩ := ih z y hRest
      let values : Fin (rest.length + 2) → X i := Fin.cons x tail
      refine ⟨values, ?_, ?_, ?_⟩
      · rfl
      · have hLastIndex :
          (Fin.last (rest.length + 1) : Fin (rest.length + 2)) =
            (Fin.last rest.length).succ := by
          apply Fin.ext
          rfl
        change values (Fin.last (rest.length + 1)) = y
        rw [hLastIndex]
        simpa only [values, Fin.cons_succ] using htailLast
      · intro k
        induction k using Fin.cases with
        | zero =>
            change S.menuRel D (values 0) (values 1)
            have hOne : (1 : Fin (rest.length+2)) =
                (0 : Fin (rest.length+1)).succ := Fin.ext rfl
            rw [hOne]
            change S.menuRel D x (tail 0)
            rw [htail0]
            exact hFirst
        | succ k =>
            change S.menuRel (rest.get k)
              (values k.succ.castSucc) (values k.succ.succ)
            have hCast :
                (k.succ.castSucc : Fin (rest.length+2)) =
                  (k.castSucc).succ := Fin.ext rfl
            rw [hCast]
            simpa only [values, Fin.cons_succ] using htailEdges k

/-- An ACTUAL list of consecutive original STRONG menus plus a
closing menu yields ONE old real valuation satisfying every edge
of the true Fin(n+1) cyclic enumeration. The closing relation is
oriented from the LAST root to the FIRST, never mistaken for an
identity factor. -/
theorem originalStrongMenuChain_cyclic_values
    {i : ι} {n : Nat}
    (menus : Fin (n+1) → S.Menu i i) (x y : X i)
    (hChain : originalStrongMenuChain S
      (List.ofFn (fun k : Fin n => menus k.castSucc)) x y)
    (hClosing : S.menuRel (menus (Fin.last n)) y x) :
    ∃ values : Fin (n+1) → X i,
      ∀ k : Fin (n+1),
        S.menuRel (menus k)
          (values k)
          (values (CCO.cyclicNext (Nat.succ_pos n) k)) := by
  let menuList : List (S.Menu i i) :=
    List.ofFn (fun t : Fin n => menus t.castSucc)
  have hLen : menuList.length = n := List.length_ofFn
  have hLenPlus : menuList.length + 1 = n + 1 :=
    congrArg (fun m : Nat => m + 1) hLen
  obtain ⟨raw,hRawFirst,hRawLast,hRawEdges⟩ :=
    originalStrongMenuChain_fin_values S menuList x y hChain
  let values : Fin (n+1) → X i :=
    fun k => raw (Fin.cast hLenPlus.symm k)
  have hFinite :
      values 0 = x ∧ values (Fin.last n) = y ∧
      ∀ t : Fin n,
        S.menuRel (menus t.castSucc)
          (values t.castSucc) (values t.succ) := by
    have hCastZero :
        Fin.cast hLenPlus.symm (0 : Fin (n+1)) =
          (0 : Fin (menuList.length+1)) := Fin.ext rfl
    have hCastLast :
        Fin.cast hLenPlus.symm (Fin.last n) =
          Fin.last menuList.length := by
      apply Fin.ext
      exact hLen.symm
    refine ⟨?_, ?_, ?_⟩
    · change raw (Fin.cast hLenPlus.symm 0) = x
      rw [hCastZero]
      exact hRawFirst
    · change raw (Fin.cast hLenPlus.symm (Fin.last n)) = y
      rw [hCastLast]
      exact hRawLast
    · intro t
      let t' : Fin menuList.length := Fin.cast hLen.symm t
      have hMenu : menuList.get t' = menus t.castSucc := by
        change (List.ofFn (fun p : Fin n => menus p.castSucc)).get
            (Fin.cast hLen.symm t) = menus t.castSucc
        rw [List.get_ofFn]
        exact congrArg (fun p : Fin n => menus p.castSucc) (Fin.ext rfl)
      have hCastStart :
          Fin.cast hLenPlus.symm t.castSucc = t'.castSucc :=
        Fin.ext rfl
      have hCastFinish :
          Fin.cast hLenPlus.symm t.succ = t'.succ :=
        Fin.ext rfl
      change S.menuRel (menus t.castSucc)
        (raw (Fin.cast hLenPlus.symm t.castSucc))
        (raw (Fin.cast hLenPlus.symm t.succ))
      rw [hCastStart,hCastFinish,← hMenu]
      exact hRawEdges t'
  rcases hFinite with ⟨hFirst,hLast,hEdges⟩
  refine ⟨values, ?_⟩
  intro k
  by_cases hkLast : k = Fin.last n
  · subst k
    rw [original_cyclicNext_last]
    simpa only [hFirst,hLast] using hClosing
  · let t : Fin n := ⟨k.val, by
      have hk := k.isLt
      have hkN : k.val ≠ n := by
        intro hkn
        exact hkLast (Fin.ext hkn)
      omega⟩
    have ht : t.castSucc = k := Fin.ext rfl
    have hNext :
        CCO.cyclicNext (Nat.succ_pos n) k = t.succ := by
      rw [← ht]
      exact original_cyclicNext_castSucc (by omega : 0 < n) t
    have hThis := hEdges t
    simpa only [ht,hNext] using hThis

/-- SOURCE C30, genuine MULTI-BRANCH menu-cycle closure. The true
complementary STRONG product of the first n menus equals original K°,
and the REAL last closing menu D is nonempty inside K°. The output
gives a SIMULTANEOUS real value for every root in cyclic order,
realizing each assigned original menu, not an arbitrary larger branch
profile. This is precisely the finite old root witness needed for
independent theta gadgets, no global CCO or exact private word. -/
theorem original_saturated_strong_menu_cyclic_values
    (H : HomogeneousSource S G)
    {i : ι} (K : ParityHasse.Original.ColourEq S i)
    {n : Nat} (hn : 0 < n)
    (menus : Fin (n+1) → S.Menu i i)
    (D : S.Menu i i)
    (hD : D.Nonempty)
    (hDinside : D ⊆ originalEquivDiversityPalette S K)
    (hClosing : D ⊆ menus (Fin.last n))
    (hSpectrum : originalPositiveStrongPath S
      (List.ofFn (fun k : Fin n => menus k.castSucc)) =
      some (originalEquivDiversityPalette S K)) :
    ∃ values : Fin (n+1) → X i,
      ∀ k : Fin (n+1),
        S.menuRel (menus k) (values k)
          (values (CCO.cyclicNext (Nat.succ_pos n) k)) := by
  cases hPath : List.ofFn (fun k : Fin n => menus k.castSucc) with
  | nil =>
      have hZero : n = 0 := by
        have hLength := congrArg List.length hPath
        simpa only [List.length_ofFn, List.length_nil] using hLength
      omega
  | cons first rest =>
      have hSpectrum' :
          originalPositiveStrongPath S (first :: rest) =
            some (originalEquivDiversityPalette S K) := by
        simpa only [hPath] using hSpectrum
      have hExact :
          rest.foldl (fun A B => S.product A B) first =
            originalEquivDiversityPalette S K := by
        have hActual :
            originalPositiveStrongPath S (first :: rest) =
              some (rest.foldl (fun A B => S.product A B) first) := by
          unfold originalPositiveStrongPath
          simp only [List.foldl_cons, originalOptionStrongStep]
          exact originalOptionStrongFold_some S first rest
        exact Option.some.inj (hActual.symm.trans hSpectrum')
      have hPathSub :
          D ⊆ rest.foldl (fun A B => S.product A B) first := by
        rw [hExact]
        exact hDinside
      obtain ⟨x,y,hChain,hClose⟩ :=
        originalStrongMenuPath_closes S H first rest
          (menus (Fin.last n)) D hD hPathSub hClosing
      have hChainActual :
          originalStrongMenuChain S
            (List.ofFn (fun k : Fin n => menus k.castSucc)) x y := by
        rw [hPath]
        exact hChain
      have hCloseRev : S.menuRel (menus (Fin.last n)) y x := by
        obtain ⟨a,ha,hcol⟩ := hClose
        exact ⟨a,ha,(colour_symmetric S y x).trans hcol⟩
      exact originalStrongMenuChain_cyclic_values
        S menus x y hChainActual hCloseRev

end CCO.TerminalLattice
