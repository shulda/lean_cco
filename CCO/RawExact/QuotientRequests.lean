import CCO.RawExact.Saturation
import CCO.PairHomogeneity

/-!
# B002 C19: actual real-to-quotient orbit requests

With an equivariant quotient map, the mixed pair orbit is precisely
the equality-inclusive original pair orbit followed by the actual fibre
kernel. Finite exact presentation of that composite is a later C09
consequence, not an assumption here. Representatives are not chosen
functorially.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}

theorem kernel_equiv {i : ι} {Q : Type*} (π : X i → Q) :
    RawSymmetric.EquivRel (GroupActions.kernel π) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x y h
    exact h.symm
  · intro x y z hxy hyz
    exact hxy.trans hyz

/-- A real-to-quotient named pair orbit pulls back to the full
original pair orbit followed by the actual quotient kernel. -/
theorem original_quotient_request_pullback
    {i j : ι} {G Q : Type*} [Group G]
    [MulAction G (X i)] [MulAction G (X j)] [MulAction G Q]
    (π : X j → Q)
    (equivπ : ∀ (g : G) z, π (g • z) = g • π z)
    (x : X i) (c : X j) :
    GroupActions.pullback (fun z : X i => z) π
      (GroupActions.orbital (G := G) x (π c)) =
      TRel.comp (GroupActions.orbital (G := G) x c)
        (GroupActions.kernel π) := by
  have equivId : ∀ (g : G) (z : X i),
      (fun t : X i => t) (g • z) = g • (fun t : X i => t) z := by
    intro g z
    rfl
  calc
    GroupActions.pullback (fun z : X i => z) π
        (GroupActions.orbital (G := G) x (π c)) =
      saturate (GroupActions.kernel (fun z : X i => z))
        (GroupActions.orbital (G := G) x c)
        (GroupActions.kernel π) :=
      equivariant_orbit_pullback (fun z : X i => z) π
        equivId equivπ x c
    _ = TRel.comp (GroupActions.orbital (G := G) x c)
        (GroupActions.kernel π) :=
      identity_left_request (GroupActions.orbital (G := G) x c)
        (GroupActions.kernel π)

/-- The original atomic pair colour is the *entire* actual group
orbital, not merely one point in it; equality is a legitimate colour. -/
theorem actual_pair_orbital_of_homogeneous
    (S : AtomicSource ι X)
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {i j : ι} (x : X i) (c : X j) :
    GroupActions.orbital (G := G) x c =
      S.rawAtomRel (S.colour x c) := by
  funext y z
  apply propext
  constructor
  · rintro ⟨g, rfl, rfl⟩
    exact S.colourInvariant_of_homogeneous H g x c
  · intro h
    obtain ⟨g, hgx, hgc⟩ :=
      (S.pair_homogeneous_of_homogeneous H) x y c z h.symm
    exact ⟨g, hgx, hgc⟩

/-- Source-level C19 orbital request equality, with the original
source assumptions visible and no unproved Helly dependency. -/
theorem actual_request_of_homogeneous
    (S : AtomicSource ι X)
    {G Q : Type*} [Group G]
    [∀ t : ι, MulAction G (X t)] [MulAction G Q]
    (H : HomogeneousSource S G)
    {i j : ι} (π : X j → Q)
    (equivπ : ∀ (g : G) z, π (g • z) = g • π z)
    (x : X i) (c : X j) :
    GroupActions.pullback (fun z : X i => z) π
      (GroupActions.orbital (G := G) x (π c)) =
      TRel.comp (S.rawAtomRel (S.colour x c))
        (GroupActions.kernel π) := by
  calc
    GroupActions.pullback (fun z : X i => z) π
        (GroupActions.orbital (G := G) x (π c)) =
      TRel.comp (GroupActions.orbital (G := G) x c)
        (GroupActions.kernel π) :=
      original_quotient_request_pullback π equivπ x c
    _ = TRel.comp (S.rawAtomRel (S.colour x c))
        (GroupActions.kernel π) := by
      rw [actual_pair_orbital_of_homogeneous S H x c]

/-- For a fixed real point x, every real representative of one actual
quotient class gives the same complete mixed request predicate. -/
theorem actual_request_representative_independent
    (S : AtomicSource ι X)
    {G Q : Type*} [Group G]
    [∀ t : ι, MulAction G (X t)] [MulAction G Q]
    (H : HomogeneousSource S G)
    {i j : ι} (π : X j → Q)
    (equivπ : ∀ (g : G) z, π (g • z) = g • π z)
    (x : X i) (c c' : X j) (hπ : π c = π c') :
    TRel.comp (S.rawAtomRel (S.colour x c)) (GroupActions.kernel π) =
      TRel.comp (S.rawAtomRel (S.colour x c')) (GroupActions.kernel π) := by
  calc
    TRel.comp (S.rawAtomRel (S.colour x c)) (GroupActions.kernel π) =
      GroupActions.pullback (fun z : X i => z) π
        (GroupActions.orbital (G := G) x (π c)) :=
      (actual_request_of_homogeneous S H π equivπ x c).symm
    _ = GroupActions.pullback (fun z : X i => z) π
        (GroupActions.orbital (G := G) x (π c')) := by rw [hπ]
    _ = TRel.comp (S.rawAtomRel (S.colour x c'))
        (GroupActions.kernel π) :=
      actual_request_of_homogeneous S H π equivπ x c'

/-- The actual request is nonempty, including the diagonal pair x=c
when the two original sorts are the same. -/
theorem actual_request_nonempty
    (S : AtomicSource ι X) {i j : ι}
    {Q : Type*} (π : X j → Q)
    (x : X i) (c : X j) :
    TRel.Nonempty
      (TRel.comp (S.rawAtomRel (S.colour x c))
        (GroupActions.kernel π)) := by
  exact ⟨x, c, c, rfl, rfl⟩

end CCO.RawExact
