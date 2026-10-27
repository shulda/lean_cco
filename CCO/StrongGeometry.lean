import CCO.Atomic

/-!
# STRONG triangle geometry with explicit real-point gluing obligations

The two gluing properties are semantic intermediates, not axioms, and
not themselves proved here from AgeSAP and finite homogeneity.
They describe real three-point and four-point amalgams and will be discharged
from the actual source's SAP in B001. Consequently all results taking
these hypotheses are CONDITIONAL until that bridge is supplied.
No RAW Helly, CCO, NR2, or selector premise occurs.
-/

universe u v w

namespace CCO.AtomicSource

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource ι X)
variable {i j k l : ι}

/-- Existence of a real, three-distinct-point triangle for any pair of
compatible represented diversity atoms (point-overlap SAP step). -/
def RealPointGluing : Prop :=
  ∀ {i j k : ι} (a : S.Atom i j) (b : S.Atom j k),
    ∃ c : S.Atom i k, S.Triangle a b c

/-- Actual gluing over a complete coloured edge. The two off-edge
vertices must remain distinct, even when their sorts coincide. -/
def RealEdgeGluing : Prop :=
  ∀ {i j k l : ι} (a : S.Atom i j) (b : S.Atom j k)
    (c : S.Atom i k) (d : S.Atom i l) (e : S.Atom k l),
    S.Triangle a b c → S.Triangle c e d →
      ∃ (x : X i) (y : X j) (z : X k) (t : X l),
        S.atomRel a x y ∧ S.atomRel b y z ∧
        S.atomRel c x z ∧ S.atomRel d x t ∧ S.atomRel e z t ∧
        (⟨j, y⟩ : Sigma X) ≠ ⟨l, t⟩

theorem triangle_cycle {a : S.Atom i j} {b : S.Atom j k}
    {c : S.Atom i k} (h : S.Triangle a b c) :
    S.Triangle b (S.conv c) (S.conv a) := by
  rcases h with ⟨x, y, z, hxy, hyz, hxz⟩
  exact ⟨y, z, x, hyz, (S.colour_swap x z c).mp hxz,
    (S.colour_swap x y a).mp hxy⟩

theorem some_colour_of_ne (x : X i) (y : X j)
    (h : (⟨i, x⟩ : Sigma X) ≠ ⟨j, y⟩) :
    ∃ a : S.Atom i j, S.colour x y = some a := by
  cases hc : S.colour x y with
  | none => exact False.elim (h ((S.colour_none_iff x y).mp hc))
  | some a => exact ⟨a, rfl⟩

theorem product_nonempty_of_point_gluing
    (hPoint : S.RealPointGluing)
    {A : S.Menu i j} {B : S.Menu j k}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (S.product A B).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨c, htri⟩ := hPoint a b
  exact ⟨c, a, ha, b, hb, htri⟩

/-- Set-Pasch via the actual new colour joining two off-edge points. -/
theorem set_pasch_of_edge_gluing
    (hEdge : S.RealEdgeGluing)
    (A : S.Menu i j) (B : S.Menu j k)
    (C : S.Menu i l) (D : S.Menu l k)
    (h : (S.product A B ∩ S.product C D).Nonempty) :
    (S.product (S.opposite A) C ∩
      S.product B (S.opposite D)).Nonempty := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨hzAB, hzCD⟩ := hz
  obtain ⟨a, ha, b, hb, htriAB⟩ := hzAB
  obtain ⟨c, hc, d, hd, htriCD⟩ := hzCD
  have htri : S.Triangle z (S.conv d) c := S.triangle_rotate htriCD
  obtain ⟨x, y, q, t, hxy, hyq, hxq, hxt, hqt, hne⟩ :=
    hEdge a b z c (S.conv d) htriAB htri
  obtain ⟨v, hyt⟩ := S.some_colour_of_ne y t hne
  refine ⟨v, ?_, ?_⟩
  · exact ⟨S.conv a, S.mem_opposite ha, c, hc,
      ⟨y, x, t, (S.colour_swap x y a).mp hxy, hxt, hyt⟩⟩
  · exact ⟨b, hb, S.conv d, S.mem_opposite hd,
      ⟨y, q, t, hyq, hqt, hyt⟩⟩

/-- STRONG associativity follows from actual edge-overlap gluing. -/
theorem product_assoc_of_edge_gluing
    (hEdge : S.RealEdgeGluing)
    (A : S.Menu i j) (B : S.Menu j k) (C : S.Menu k l) :
    S.product (S.product A B) C =
      S.product A (S.product B C) := by
  apply Set.Subset.antisymm
  · rintro d ⟨p, hp, c, hc, htri⟩
    obtain ⟨a, ha, b, hb, hfirst⟩ := hp
    obtain ⟨x, y, z, t, hxy, hyz, hxz, hxt, hzt, hne⟩ :=
      hEdge a b p d c hfirst htri
    obtain ⟨v, hyt⟩ := S.some_colour_of_ne y t hne
    refine ⟨a, ha, v, ?_, ?_⟩
    · exact ⟨b, hb, c, hc, ⟨y, z, t, hyz, hzt, hyt⟩⟩
    · exact ⟨x, y, t, hxy, hyt, hxt⟩
  · rintro d ⟨a, ha, p, hp, htri⟩
    obtain ⟨b, hb, c, hc, hfirst⟩ := hp
    have hrot : S.Triangle p (S.conv d) (S.conv a) :=
      S.triangle_cycle htri
    obtain ⟨x, y, z, t, hxy, hyz, hxz, hxt, hzt, hne⟩ :=
      hEdge b c p (S.conv a) (S.conv d) hfirst hrot
    obtain ⟨v, hyt⟩ := S.some_colour_of_ne y t hne
    have hty : S.colour t y = some (S.conv v) :=
      (S.colour_swap y t v).mp hyt
    have htx : S.colour t x = some a := by
      have hh := (S.colour_swap x t (S.conv a)).mp hxt
      simpa only [S.conv_invol] using hh
    have htz : S.colour t z = some d := by
      have hh := (S.colour_swap z t (S.conv d)).mp hzt
      simpa only [S.conv_invol] using hh
    refine ⟨S.conv v, ?_, c, hc, ?_⟩
    · exact ⟨a, ha, b, hb, ⟨t, x, y, htx, hxy, hty⟩⟩
    · exact ⟨t, y, z, hty, hyz, htz⟩

theorem loop_opposite (A : S.Menu i i) : S.opposite A = A := by
  ext a
  change S.conv a ∈ A ↔ a ∈ A
  rw [S.symmetricLoop a]

theorem loop_product_commute (A B : S.Menu i i) :
    S.product A B = S.product B A := by
  have h := S.product_opposite A B
  rw [S.loop_opposite, S.loop_opposite, S.loop_opposite] at h
  exact h

theorem top_product_of_point_gluing (hPoint : S.RealPointGluing)
    (B : S.Menu j k) (hB : B.Nonempty) :
    S.product (Set.univ : S.Menu i j) B = Set.univ := by
  ext d
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨b, hb⟩ := hB
    obtain ⟨a, htri⟩ := hPoint d (S.conv b)
    exact ⟨a, Set.mem_univ a, b, hb, S.triangle_rotate_back htri⟩

theorem product_top_of_point_gluing (hPoint : S.RealPointGluing)
    (A : S.Menu i j) (hA : A.Nonempty) :
    S.product A (Set.univ : S.Menu j k) = Set.univ := by
  ext d
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, htri⟩ := hPoint (S.conv a) d
    have hrot : S.Triangle d (S.conv b) a := by
      simpa only [S.conv_invol] using S.triangle_cycle htri
    exact ⟨a, ha, b, Set.mem_univ b, S.triangle_rotate_back hrot⟩

theorem supported_fork_of_gluing
    (hPoint : S.RealPointGluing)
    (hEdge : S.RealEdgeGluing)
    (c : S.Atom i k) (A : S.Menu i j) :
    A ⊆ S.product
      (S.product ({c} : S.Menu i k) ({S.conv c} : S.Menu k i)) A := by
  intro x hx
  obtain ⟨b, htri⟩ := hPoint (S.conv c) x
  have hrot : S.Triangle x (S.conv b) c := by
    simpa only [S.conv_invol] using S.triangle_cycle htri
  have hnew : S.Triangle c b x := S.triangle_rotate_back hrot
  have hin : x ∈ S.product ({c} : S.Menu i k)
      (S.product ({S.conv c} : S.Menu k i) A) :=
    ⟨c, by simp, b, ⟨S.conv c, by simp, x, hx, htri⟩, hnew⟩
  rw [S.product_assoc_of_edge_gluing hEdge
    ({c} : S.Menu i k) ({S.conv c} : S.Menu k i) A]
  exact hin

theorem loop_powers_three_of_gluing
    (hPoint : S.RealPointGluing) (hEdge : S.RealEdgeGluing)
    (P : S.Menu i i) (hP : P.Nonempty) :
    P ⊆ S.product (S.product P P) P := by
  obtain ⟨c, hc⟩ := hP
  have ha : ({c} : S.Menu i i) ⊆ P := by
    intro a h
    have he : a = c := Set.mem_singleton_iff.mp h
    simpa only [he] using hc
  have hb : ({S.conv c} : S.Menu i i) ⊆ P := by
    intro a h
    have he : a = S.conv c := Set.mem_singleton_iff.mp h
    simpa only [he, S.symmetricLoop c] using hc
  have hmono : S.product
      (S.product ({c} : S.Menu i i) ({S.conv c} : S.Menu i i)) P ⊆
      S.product (S.product P P) P :=
    S.product_mono (S.product_mono ha hb) (fun _ h => h)
  intro x hx
  exact hmono (S.supported_fork_of_gluing hPoint hEdge c P hx)

end CCO.AtomicSource
