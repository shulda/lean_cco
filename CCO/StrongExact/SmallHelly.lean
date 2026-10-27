import CCO.StrongExact.PaletteNonempty
import CCO.StrongExact.DirectBranches

/-!
# C07 elementary finite Helly boundary: at most two positive profiles

The full theta statement concerns ARBITRARILY MANY pairwise
intersecting positive profiles. Its first two cardinalities are
mathematically elementary. The empty list evaluates to genuine
inhabited diversity Top (derived from source homogeneous SAP);
one profile is nonempty by B001 SAP path gluing, and two are
nonempty exactly when they intersect.

No homomorphic CCO, extra identity letter, or theorem asserting
general theta Helly is needed for these small-family cases.
-/

universe u v a

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, a} ι X)
variable {i j : ι}
variable {G : Type*} [Group G] [∀ p : ι, MulAction G (X p)]

theorem single_positive_present_nonempty_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (w : PositiveWord S i j) :
    (present S [w]).Nonempty := by
  obtain ⟨a, ha⟩ :=
    PositiveWord.profile_nonempty_of_SAP S H sap w
  refine ⟨a, ?_⟩
  intro v hv
  have heq : v = w := List.mem_singleton.mp hv
  subst v
  exact ha

theorem two_positive_present_nonempty
    (p q : PositiveWord S i j)
    (hpq : (PositiveWord.profile S p ∩
      PositiveWord.profile S q).Nonempty) :
    (present S [p, q]).Nonempty := by
  obtain ⟨a, ha, hb⟩ := hpq
  refine ⟨a, ?_⟩
  intro v hv
  simp only [List.mem_cons, List.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ha
  · exact hb

/-- Genuine C07 up to TWO positive restrictions. The hard arbitrary
size extension is precisely the pending CCO private-theta proof. -/
theorem wordHelly_at_most_two_of_SAP
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (ws : List (PositiveWord S i j))
    (hLength : ws.length ≤ 2)
    (hPair : PairwiseWordProfiles S ws) :
    (present S ws).Nonempty := by
  cases ws with
  | nil =>
      obtain ⟨a⟩ := palette_nonempty_of_SAP S H sap i j
      refine ⟨a, ?_⟩
      intro w hw
      cases hw
  | cons p ws =>
      cases ws with
      | nil =>
          exact single_positive_present_nonempty_of_SAP S H sap p
      | cons q ws =>
          cases ws with
          | nil =>
              exact two_positive_present_nonempty S p q
                (hPair p (by simp) q (by simp))
          | cons third rest =>
              have hFalse : False := by
                simp only [List.length_cons] at hLength
                omega
              exact hFalse.elim

end CCO.StrongExact
