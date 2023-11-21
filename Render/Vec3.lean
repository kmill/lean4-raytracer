--import render.Algebra

structure Vec3 (α : Type _) :=
  (x y z : α)

namespace Vec3

@[inline] def map (f : α → β) (v : Vec3 α) : Vec3 β := ⟨f v.x, f v.y, f v.z⟩

@[inline] def map₂ (f : α → β → γ) (v : Vec3 α) (w : Vec3 β) : Vec3 γ :=
  ⟨f v.x w.x, f v.y w.y, f v.z w.z⟩

instance [Add α] : Add (Vec3 α) where
  add := map₂ (. + .)

instance [Sub α] : Sub (Vec3 α) where
  sub := map₂ (. - .)

instance [Mul α] : Mul (Vec3 α) where
  mul := map₂ (. * .)

instance [Div α] : Div (Vec3 α) where
  div := map₂ (. / .)

instance [Neg α] : Neg (Vec3 α) where
  neg := map (- .)

-- Scalar multiplication
@[default_instance]
instance [Mul α] : HMul α (Vec3 α) (Vec3 α) where
  hMul c := map (c * .)

-- Scalar division
@[default_instance]
instance [Div α] : HDiv (Vec3 α) α (Vec3 α) where
  hDiv v c := map (. / c) v

@[inline] def sum [Add α] (v : Vec3 α) : α := v.x + v.y + v.z

@[inline] def lengthSquared [Add α] [Mul α] (v : Vec3 α) : α := (v * v).sum

@[inline] def length (v : Vec3 Float) : Float := v.lengthSquared.sqrt

@[inline] def normalized (v : Vec3 Float) : Vec3 Float := v / v.length

@[inline] def dot [Add α] [Mul α] (v w : Vec3 α) : α := (v * w).sum

@[inline] def cross [Sub α] [Mul α] (v w : Vec3 α) : Vec3 α :=
  ⟨v.y*w.z - v.z*w.y, v.z*w.x - v.x*w.z, v.x*w.y - v.y*w.x⟩

/-- Reflect v over plane with normal vector n. -/
@[inline] def reflect (v n : Vec3 Float) : Vec3 Float := v - 2 * v.dot n * n

@[inline] def nearZero (v : Vec3 Float) (ε : Float := 1e-8) : Bool :=
  v.length < ε

end Vec3

abbrev Color (α : Type _) := Vec3 α

namespace Color

def mk (r g b : α) : Color α := ⟨r, g, b⟩
@[inline] def r (v : Color α) : α := v.x
@[inline] def g (v : Color α) : α := v.y
@[inline] def b (v : Color α) : α := v.z

@[inline] def white : Color Float := Color.mk 1.0 1.0 1.0
@[inline] def black : Color Float := Color.mk 0.0 0.0 0.0

instance : Inhabited (Color Float) := ⟨black⟩

end Color
