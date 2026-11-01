import CCO.TerminalLattice.PositivePathFold
import CCO.TerminalLattice.StrongPaletteBridge

/-!
# B050 source08 C26–C30: actual OLD root points for finite STRONG menu chains

The standalone typed theta-cycle guard uses genuine original same-sort
STRONG MENUS T_i. A private theta may contain several distinct positive
typed word branches, with each branch profile only CONTAINING T_i; no
single branch is assumed to have EXACT profile T_i.

Consequently a root valuation must realize the true T_i menus, rather
than arbitrary larger whole-word profiles. We extract actual intermediate
OLD source points directly from finite STRONG menu multiplication.
Original homogeneous pair transport for triangles supplies exactly the
real strong-composition semantics. This construction does not use
semantic CCO, quotient actions, or a one-word-per-pair assumption.

The empty chain means equality of endpoints as a metalevel notion;
it is never a positive old STRONG identity factor.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Actual old source points realizing EVERY listed same-sort STRONG
menu in the given linear order. No finite injectivity of all roots
is presumed; each specified diversity edge has distinct endpoints. -/
def originalStrongMenuChain {i : ι} :
    List (S.Menu i i) → X i → X i → Prop
  | [], x, y => x = y
  | D :: rest, x, y =>
      ∃ z : X i,
        S.menuRel D x z ∧
        originalStrongMenuChain rest z y

/-- A whole original STRONG product witness can be split into its
two ACTUAL same-sort source edges even in front of additional
menus. The strong three-point distinction comes from the actual
triangle semantics, not from synthetic identity. -/
theorem originalStrongMenuChain_split_first
    (H : HomogeneousSource S G)
    {i : ι} (A B : S.Menu i i)
    (rest : List (S.Menu i i)) (x y : X i)
    (h : originalStrongMenuChain S
      ((S.product A B) :: rest) x y) :
    originalStrongMenuChain S (A :: B :: rest) x y := by
  change ∃ z : X i,
      S.menuRel (S.product A B) x z ∧
      originalStrongMenuChain S rest z y at h
  obtain ⟨z,hAB,hRest⟩ := h
  rw [menuRel_product_eq_strongCompose S H A B] at hAB
  obtain ⟨_,mid,_,_,hA,hB⟩ := hAB
  exact ⟨mid,hA,z,hB,hRest⟩

/-- Any ACTUAL endpoint pair in a nonempty finite left-associated
OLD STRONG product has real intermediate points for every original
menu in the exact prescribed order. The menus need NOT be complete
old atom orbitals or profiles of individual positive words. -/
theorem originalStrongMenuPath_realized
    (H : HomogeneousSource S G)
    {i : ι} (first : S.Menu i i)
    (rest : List (S.Menu i i)) (x y : X i)
    (h : S.menuRel
      (rest.foldl (fun A B => S.product A B) first) x y) :
    originalStrongMenuChain S (first :: rest) x y := by
  induction rest generalizing first x y with
  | nil =>
      change ∃ z : X i, S.menuRel first x z ∧ z = y
      exact ⟨y,h,rfl⟩
  | cons D rest ih =>
      have hFront :
          originalStrongMenuChain S
            ((S.product first D) :: rest) x y :=
        ih (S.product first D) x y h
      exact originalStrongMenuChain_split_first
        S H first D rest x y hFront

/-- A genuine nonempty fine diversity menu in the intersection of
an OLD positive complementary STRONG product and the closing menu
gives ONE simultaneous root assignment realizing ALL ordered
complementary true MENUS and the closing menu on its SAME endpoint
pair. This is the exact menu-valued source C30 gluing operation
needed by theta gadgets with multiple private branches.

Neither word-profile equality nor semantic CCO is an input.
-/
theorem originalStrongMenuPath_closes
    (H : HomogeneousSource S G)
    {i : ι}
    (first : S.Menu i i) (rest : List (S.Menu i i))
    (closing D : S.Menu i i)
    (hD : D.Nonempty)
    (hPath : D ⊆
      rest.foldl (fun A B => S.product A B) first)
    (hClosing : D ⊆ closing) :
    ∃ x y : X i,
      originalStrongMenuChain S (first :: rest) x y ∧
      S.menuRel closing x y := by
  obtain ⟨a,ha⟩ := hD
  obtain ⟨x,y,hCol⟩ := S.realized a
  have hPathReal :
      S.menuRel
        (rest.foldl (fun A B => S.product A B) first) x y :=
    ⟨a,hPath ha,hCol⟩
  have hCloseReal : S.menuRel closing x y :=
    ⟨a,hClosing ha,hCol⟩
  exact ⟨x,y,originalStrongMenuPath_realized
      S H first rest x y hPathReal,hCloseReal⟩

end CCO.TerminalLattice
