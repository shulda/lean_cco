import CCO.ProfileHelly.Words

/-! Pure algebra of cyclic cuts. These laws move a test first obtained
at a genuine diversity EDGE to arbitrary positive arc endpoints. -/
universe u v
namespace CCO.ProfileHelly
variable {ι : Type u} {T : Table.{u,v} ι}

theorem front_cut {i j k} (a : T.Atom i j) (B : T.Menu j k) (C : T.Menu i k) :
    (T.product {a} B ∩ C).Nonempty ↔ T.conv a ∈ T.product B (T.opposite C) := by
  constructor
  · rintro ⟨c,⟨a',ha,b,hb,htri⟩,hc⟩
    have hae : a' = a := ha
    subst a'
    refine ⟨b,hb,T.conv c,?_,?_⟩
    · simpa only [Table.opposite,Set.mem_ofPred_eq,T.conv_invol] using hc
    · have hh := (T.reverse c (T.conv b) a).mp ((T.peirce_left a b c).mp htri)
      simpa only [T.conv_invol] using hh
  · rintro ⟨b,hb,c,hc,htri⟩
    refine ⟨T.conv c,⟨a,rfl,b,hb,?_⟩,hc⟩
    have hr : T.triangle (T.conv c) (T.conv b) a := by
      simpa only [T.conv_invol] using (T.reverse b c (T.conv a)).mp htri
    have hh := (T.peirce_left (T.conv c) (T.conv b) a).mp hr
    simpa only [T.conv_invol] using hh

/-- C07: one closing-edge compatibility rotates through a positive middle
profile, with the exact typed converses. -/
theorem rotate_closing {i j k} (a : T.Atom i j) (B : T.Menu j k) (c : T.Atom k i) :
    T.conv c ∈ T.product {a} B ↔ T.conv a ∈ T.product B {c} := by
  have h := front_cut a B {T.conv c}
  simpa only [Set.inter_singleton_nonempty,Table.opposite_singleton,T.conv_invol] using h

/-- C08: two positive arcs intersect exactly when the first closing-edge
test holds. In particular this does not require distinct semantic images
at the arbitrarily chosen arc terminals. -/
theorem arc_cut {i j k} (a : T.Atom i j) (p : Word T j k) (q : Word T i k) :
    ((Word.cons a p).profile ∩ q.profile).Nonempty ↔
      T.conv a ∈ T.product p.profile (T.opposite q.profile) :=
  front_cut a p.profile q.profile

end CCO.ProfileHelly
