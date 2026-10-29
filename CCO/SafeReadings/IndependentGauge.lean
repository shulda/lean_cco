import CCO.SafeReadings.MovingReadings

universe u v w z t r
namespace CCO.SafeReadings
open Selectors
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {Γ : Type z} [Group Γ] {N : Type t} {A : PureTagAction S Γ N}
variable {K : Type r} [CommGroup K] (E : EndpointGauge S A K)

theorem right_conv (hConv : LiteralConverse S A) (g : K) {i j : ι} (a : S.Atom i j) :
    E.right g (S.conv a) = S.conv (E.left g a) := by
  apply A.label_injective
  rw [E.right_label,hConv,hConv,E.left_label]

/-- Independent switching at the middle formal vertex follows by
rotating the actual triangle; its name may coincide with either endpoint. -/
theorem triangle_middle (hConv : LiteralConverse S A) (g : K) {i j k : ι}
    (a : S.Atom i j) (b : S.Atom j k) (c : S.Atom i k) :
    S.Triangle a b c ↔ S.Triangle (E.right g a) (E.left g b) c := by
  constructor
  · intro ht
    have hr := (E.triangle_right g c (S.conv b) a).mp (S.triangle_rotate ht)
    rw [right_conv E hConv] at hr
    exact S.triangle_rotate_back hr
  · intro ht
    have hr := S.triangle_rotate ht
    rw [←right_conv E hConv] at hr
    exact S.triangle_rotate_back ((E.triangle_right g c (S.conv b) a).mpr hr)

/-- Every switch at each of the three formal vertices is independent. -/
theorem triangle_independent_switch (hConv : LiteralConverse S A) (g k l : K)
    {i j m : ι} (a : S.Atom i j) (b : S.Atom j m) (c : S.Atom i m) :
    S.Triangle a b c ↔
      S.Triangle (E.left g (E.right k a)) (E.right l (E.left k b)) (E.right l (E.left g c)) :=
  (triangle_middle E hConv k a b c).trans
    ((E.triangle_left g (E.right k a) (E.left k b) c).trans
      (E.triangle_right l (E.left g (E.right k a)) (E.left k b) (E.left g c)))

end CCO.SafeReadings
