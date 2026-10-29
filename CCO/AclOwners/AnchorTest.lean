import CCO.AclOwners.CorrespondenceLift
import CCO.AclOwners.HarmlessOwners

/-! The original two-anchor algebraicity test.  The direction is the
actual minimal infinite ORIGINAL equivalence.  Only the forward branch
uses finite-exact normalization; no amalgamation or safe palette is used. -/

universe v w t
namespace CCO.AclOwners
open ParityHasse.Original RealHull.Geometry RealHull.Canonical
open RealClosure.Bounds FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [DecidableEq M]
include H

/-- A nonpacket edge in a minimal infinite direction generates that
entire direction, not a merely chosen exact subequivalence. -/
theorem direction_gamma_of_nonpacket (D : Direction S) {x u : M}
    (hxu : D.val x u) (hnot : ¬ finitePacket S H x u) :
    ∃ p : Atom S, col S x u = some p ∧ gammaEq S p = D.val := by
  cases hc : col S x u with
  | none =>
    have hx : x = u := (col_none S x u).mp hc
    exact False.elim (hnot (hx ▸ (finitePacket S H).val.refl x))
  | some p =>
    have hle : gammaEq S p ≤ D.val :=
      gamma_le_of_atom S D.val ((mem_diversitySupport S D.val hc).mpr hxu)
    have hn : ¬ FiniteClasses S (gammaEq S p) := by
      intro hf
      exact hnot (le_finitePacket S H _ hf (atom_mem_gamma S p hc))
    refine ⟨p, rfl, ?_⟩
    by_contra hne
    exact hn (D.property.2 _ (lt_of_le_of_ne hle hne))

/-- The correspondence condition defines the point uniquely from its two
anchors. This direction needs neither exactness nor normalization. -/
theorem correspondence_implies_anchor_algebraic (E : ColourEq S ())
    {x u v : M} (hxu : E x u) (hcut : correspondence S E x v) :
    x ∈ Acl G {u, v} := by
  apply (Set.finite_singleton x).subset
  rintro y ⟨g, hg, rfl⟩
  apply Set.mem_singleton_iff.mpr
  have hgu : g • u = u := hg u (by simp)
  have hgv : g • v = v := hg v (by simp)
  have hge : E (g • x) u := by
    have hh := (class_group_invariant S () H E g x u).mpr hxu
    simpa only [hgu] using hh
  have hcol : col S (g • x) v = col S x v := by
    have hh := S.colourInvariant_of_homogeneous H (i := ()) (j := ()) g x v
    unfold col
    simpa only [hgv] using hh
  apply (cutColour_functional S E (col S x v) hcut
    ((col_symm S v x).trans rfl)
    ((col_symm S v (g • x)).trans hcol)
    (E.val.trans hxu (E.val.symm hge))).symm

/-- C11: actual original algebraicity over two anchors is exactly the
global correspondence relation, including the case where x is the
second named parameter. -/
theorem anchor_algebraic_iff
    (cco : SemanticCCO.{0,v,0,w} S) (normalized : NoFiniteExactKernel S)
    (D : Direction S) {x u v : M}
    (hxu : D.val x u) (hnot : ¬ finitePacket S H x u) :
    x ∈ Acl G {u, v} ↔ correspondence S D.val x v := by
  constructor
  · intro hx
    by_cases hxv : x = v
    · subst x
      exact correspondence_refl S D.val v
    obtain ⟨p, hp, hgamma⟩ := direction_gamma_of_nonpacket S H D hxu hnot
    have hxu' : x ≠ u := by
      rintro rfl
      exact hnot ((finitePacket S H).val.refl x)
    have hxA : x ∉ ({u, v} : Finset M) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using And.intro hxu' hxv
    let q := actualSpokes S {u, v} x hxA
    have hcanon := (algebraic_iff_canonical_finite S H cco {u, v} x hxA).mp hx
    cases hc : col S x v with
    | none => exact False.elim (hxv ((col_none S x v).mp hc))
    | some b =>
      have hle : D.val ⊓ gammaEq S b ≤ supportEquiv S (canonicalSupport S {u, v} q) := by
        apply (le_canonical_iff S _ {u, v} q).mpr
        intro a
        rcases (show a.val = u ∨ a.val = v by simpa only
          [Finset.mem_insert, Finset.mem_singleton] using a.property) with ha | ha
        · have hca : col S x a.val = some p := by rw [ha]; exact hp
          have hqa : q a = p := Option.some.inj
            ((actualSpokes_colour S {u, v} x hxA a).symm.trans hca)
          rw [hqa, hgamma]
          exact inf_le_left
        · have hca : col S x a.val = some b := by rw [ha]; exact hc
          have hqa : q a = b := Option.some.inj
            ((actualSpokes_colour S {u, v} x hxA a).symm.trans hca)
          rw [hqa]
          exact inf_le_right
      have hf : FiniteClasses S (D.val ⊓ gammaEq S b) := finiteClasses_of_le S hle hcanon
      have he := finite_exact_intersection S H cco normalized D.val
        (direction_exact S H cco D) (some b) (by
          intro a c hD hsq
          obtain ⟨z, haz, hzc⟩ := hsq
          exact le_finitePacket S H _ hf
            ⟨hD, (gammaEq S b).val.trans (atom_mem_gamma S b haz) (atom_mem_gamma S b hzc)⟩)
      change CutColour S D.val (col S x v)
      rw [hc]
      intro a c hD hsq
      have hh : (fun a c => D.val a c ∧ colourSquare S (some b) a c) a c := ⟨hD, hsq⟩
      rwa [he] at hh
  · exact correspondence_implies_anchor_algebraic S H D.val hxu

end CCO.AclOwners
