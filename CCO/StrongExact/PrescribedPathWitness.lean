import CCO.StrongExact.ProfileSemantics
import CCO.StrongExact.ExactMenus
import CCO.PairHomogeneity

/-!
# C07 preparation: every positive profile has prescribed literal endpoints

The actual homogeneous-source automorphism transports a represented
positive diversity walk from arbitrary realizing endpoints to ANY
specified pair of original real points of the same fine atom.

Consequently every finite positive-word menu has exact semantics as
simultaneous, potentially colliding, represented paths over the SAME
two literal real roots. This is the key real-root alignment needed in
the C07 private-theta cycle construction. It uses B001 genuine
pair-homogeneity and SAP guarded word semantics, not the yet-unproved
theta Helly theorem.

There is no RAW/STRONG identity confusion: all endpoint colours are
actual diversity atoms and the endpoints are therefore distinct.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j : ι}
variable {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]

/-- Any STRONG word-profile atom has a represented walk connecting
ANY PREASSIGNED literal old points carrying that atom. The proof
uses genuine original pair homogeneity to transport the whole walk,
not an independent choice of endpoints for each profile. -/
theorem profile_realizes_prescribed_pair_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (w : PositiveWord S i j) (a : S.Atom i j)
    (ha : a ∈ PositiveWord.profile S w)
    (x : X i) (y : X j)
    (hxy : S.colour x y = some a) :
    PositiveWord.represented S w x y := by
  obtain ⟨u, v, hwalk, huv⟩ :=
    (positive_profile_iff_represented S H sap w a).mp ha
  obtain ⟨g, hgu, hgv⟩ :=
    (S.pair_homogeneous_of_homogeneous H)
      u x v y (huv.trans hxy.symm)
  have htransport :=
    (PositiveWord.represented_invariant_of_homogeneous S H w)
      g u v hwalk
  simpa only [hgu, hgv] using htransport

/-- Exactly those atoms surviving every profile restriction admit
all prescribed positive word walks SIMULTANEOUSLY over any fixed
literal old root pair of that colour; each internal path may be
realized independently, since a homomorphism may identify interiors. -/
theorem present_iff_prescribed_pair_walks_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (ws : List (PositiveWord S i j)) (a : S.Atom i j)
    (x : X i) (y : X j)
    (hxy : S.colour x y = some a) :
    a ∈ present S ws ↔
      ∀ w ∈ ws, PositiveWord.represented S w x y := by
  constructor
  · intro ha w hw
    exact profile_realizes_prescribed_pair_of_SAP S H sap w a
      (ha w hw) x y hxy
  · intro hh
    intro w hw
    exact (positive_profile_iff_represented S H sap w a).2
      ⟨x, y, hh w hw, hxy⟩

/-- The two-branch elementary cycle witness: pairwise intersection
of actual STRONG profiles supplies ONE common literal pair of roots,
and homomorphic realisations of BOTH positive paths over those roots.
No pair of formal roots can collapse because their common output
is an actual diversity atom. -/
theorem intersecting_profiles_common_root_walks_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (w v : PositiveWord S i j)
    (hInter :
      (PositiveWord.profile S w ∩
        PositiveWord.profile S v).Nonempty) :
    ∃ (a : S.Atom i j) (x : X i) (y : X j),
      S.colour x y = some a ∧
      PositiveWord.represented S w x y ∧
      PositiveWord.represented S v x y := by
  obtain ⟨a, haW, haV⟩ := hInter
  obtain ⟨x, y, hwalk, hxy⟩ :=
    (positive_profile_iff_represented S H sap w a).mp haW
  exact ⟨a, x, y, hxy, hwalk,
    profile_realizes_prescribed_pair_of_SAP S H sap v a haV x y hxy⟩

/-- Exact semantics of finite presented strong menus: nonempty
profile intersection iff all positive paths can be realized over
the same literal diversity-coloured endpoints. The empty list
convention is included (then any realized diversity atom suffices).
This does not infer 2-Helly from pairwise profile intersections. -/
theorem present_nonempty_iff_common_root_walks_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (ws : List (PositiveWord S i j)) :
    (present S ws).Nonempty ↔
      ∃ (a : S.Atom i j) (x : X i) (y : X j),
        S.colour x y = some a ∧
        ∀ w ∈ ws, PositiveWord.represented S w x y := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨x, y, hxy⟩ := S.realized a
    exact ⟨a, x, y, hxy,
      (present_iff_prescribed_pair_walks_of_SAP S H sap
        ws a x y hxy).mp ha⟩
  · rintro ⟨a, x, y, hxy, hWalks⟩
    exact ⟨a, (present_iff_prescribed_pair_walks_of_SAP
      S H sap ws a x y hxy).mpr hWalks⟩

end CCO.StrongExact
