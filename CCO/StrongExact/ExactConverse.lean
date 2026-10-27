import CCO.StrongExact.ExactMenus
import CCO.PositiveWords

/-!
# C08 elementary STRONG exact converse closure

Reverse a genuinely positive typed word by reversing its order and
conversing every diversity letter. B001's actual SAP edge gluing
supplies strong product associativity, hence the reversed positive
word has exactly the opposite STRONG profile.

There is NO identity letter in either direction. This is only
converse closure; exact multiplication and nonempty exact-meet
distribution still need C07 theta Helly.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u, v, w} ι X)
variable {i j : ι}

/-- Reverse the actual typed order and converse every diversity letter. -/
def reverseWord : PositiveWord S i j → PositiveWord S j i
  | .single a => .single (S.conv a)
  | .cons a tail => PositiveWord.append S (reverseWord S tail)
      (.single (S.conv a))

private theorem singleton_opposite (a : S.Atom i j) :
    ({S.conv a} : S.Menu j i) =
      S.opposite ({a} : S.Menu i j) := by
  ext b
  change b = S.conv a ↔ S.conv b = a
  constructor
  · intro hb
    subst b
    exact S.conv_invol a
  · intro hb
    have h := congrArg (fun t => S.conv t) hb
    simpa only [S.conv_invol] using h

/-- STRONG word reversal agrees with the correct typed opposite menu.
Only real edge gluing is assumed, never RAW identity multiplication. -/
theorem profile_reverse_of_gluing
    (hEdge : S.RealEdgeGluing) (w : PositiveWord S i j) :
    PositiveWord.profile S (reverseWord S w) =
      S.opposite (PositiveWord.profile S w) := by
  induction w with
  | single a =>
      exact singleton_opposite S a
  | cons a tail ih =>
      change PositiveWord.profile S
          (PositiveWord.append S (reverseWord S tail)
            (.single (S.conv a))) =
        S.opposite (S.product ({a} : S.Menu _ _)
          (PositiveWord.profile S tail))
      rw [PositiveWord.profile_append S hEdge
        (reverseWord S tail) (.single (S.conv a))]
      change S.product (PositiveWord.profile S (reverseWord S tail))
          ({S.conv a} : S.Menu _ _) =
        S.opposite (S.product ({a} : S.Menu _ _)
          (PositiveWord.profile S tail))
      rw [ih, S.product_opposite]
      rw [singleton_opposite S a]

/-- The opposite of an arbitrary evaluated finite meet of positive
profiles is presented by reversing precisely those positive words. -/
theorem opposite_present_of_gluing
    (hEdge : S.RealEdgeGluing)
    (ws : List (PositiveWord S i j)) :
    S.opposite (present S ws) =
      present S (ws.map (reverseWord S)) := by
  ext b
  change (∀ w ∈ ws, S.conv b ∈ PositiveWord.profile S w) ↔
    (∀ w ∈ ws.map (reverseWord S),
      b ∈ PositiveWord.profile S w)
  constructor
  · intro hb w hw
    obtain ⟨v, hv, heq⟩ := List.mem_map.mp hw
    subst w
    have hvProfile := hb v hv
    have hOpp : b ∈ S.opposite (PositiveWord.profile S v) := hvProfile
    rw [← profile_reverse_of_gluing S hEdge v] at hOpp
    exact hOpp
  · intro hb w hw
    have hv : b ∈ PositiveWord.profile S (reverseWord S w) :=
      hb (reverseWord S w) (List.mem_map.mpr ⟨w, hw, rfl⟩)
    rw [profile_reverse_of_gluing S hEdge w] at hv
    exact hv

/-- C08 (converse part): any nonempty strong exact domain remains
a nonempty strong exact domain after reversing its typed endpoints. -/
theorem exact_opposite_of_gluing
    (hEdge : S.RealEdgeGluing) {A : S.Menu i j}
    (hA : Exact S A) : Exact S (S.opposite A) := by
  obtain ⟨⟨a, ha⟩, ws, hws⟩ := hA
  refine ⟨⟨S.conv a, S.mem_opposite ha⟩,
    ⟨ws.map (reverseWord S), ?_⟩⟩
  rw [hws]
  exact opposite_present_of_gluing S hEdge ws

end CCO.StrongExact
