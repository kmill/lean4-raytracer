import render.vec

/-- Uniform at random in [0, 1)-/
def randomFloat {gen} [RandomGen gen] (g : gen) : Float × gen :=
  let (n, g') := RandomGen.next g
  let (lo, hi) := RandomGen.range g
  (Float.ofNat (n - lo) / Float.ofNat (hi - lo + 1), g')

def IO.randFloat : IO Float := do
  let gen ← IO.stdGenRef.get
  let (r, gen) := randomFloat gen
  IO.stdGenRef.set gen
  pure r

structure Ray (α : Type _) where
  origin : Vec3 α
  dir : Vec3 α

def Ray.at [Add α] [Mul α] (r : Ray α) (t : α) : Vec3 α := r.origin + t * r.dir

structure Camera where
  origin : Vec3 Float
  lowerLeftCorner : Vec3 Float
  horizontal : Vec3 Float
  vertical : Vec3 Float

def Camera.default (aspectRatio : Float): Camera :=
  let viewportHeight := 2.0
  let viewportWidth := aspectRatio * viewportHeight
  let focalLength := 1.0

  let origin := Vec3.mk 0.0 0.0 0.0
  let horizontal := Vec3.mk viewportWidth 0.0 0.0
  let vertical := Vec3.mk 0.0 viewportHeight 0.0
  let lowerLeftCorner := origin - horizontal/2.0 - vertical/2.0 - Vec3.mk 0.0 0.0 focalLength

  Camera.mk origin lowerLeftCorner horizontal vertical

def Camera.getRay (c : Camera) (u v : Float) : Ray Float :=
  Ray.mk c.origin (c.lowerLeftCorner + u*c.horizontal + v*c.vertical - c.origin)

structure HitRecord where
  p : Vec3 Float
  t : Float
  normal : Vec3 Float
  frontFace : Bool

def HitRecord.withNormal (p : Vec3 Float) (t : Float) (r : Ray Float) (outwardNormal : Vec3 Float) : HitRecord :=
  let frontFace : Bool := r.dir.dot outwardNormal < 0.0
  let normal : Vec3 Float := if frontFace then outwardNormal else -outwardNormal
  return {
    p := p
    t := t
    normal := normal
    frontFace := frontFace
  }

structure Hittable where
  hit : Ray Float → Float -> Float -> Option HitRecord

def mkSphere (center : Vec3 Float) (radius : Float) : Hittable where
  hit (r : Ray Float) (tmin tmax : Float) := Id.run <| do
    let oc := r.origin - center
    let a := r.dir.lengthSquared
    let halfb := Vec.dot oc r.dir
    let c := oc.lengthSquared - radius * radius
    let discr := halfb*halfb - a*c
    if discr < 0.0 then
      return none
    let sqrtd := discr.sqrt
    -- Find the nearest root that lies in the acceptable range
    let mut root := (-halfb - sqrtd) / a
    if root < tmin || tmax < root then
      root := (-halfb + sqrtd) / a
      if root < tmin || tmax < root then
        return none
    let t := root
    let p := r.at t
    let outwardNormal := (p - center) / radius
    return some <| HitRecord.withNormal p t r outwardNormal

def hitList (hs : List Hittable) (r : Ray Float) (tmin tmax : Float) : Option HitRecord := Id.run <| do
  let mut hitrec : Option HitRecord := none
  for obj in hs do
    let closest := (hitrec.map (HitRecord.t)).getD tmax
    hitrec := obj.hit r tmin closest <|> hitrec
  return hitrec

def rayColor (hs : List Hittable) (r : Ray Float) : Color Float := do
  match hitList hs r 0 1000000.0 with
  | some hitrec => do
    let v := hitrec.normal
    return 0.5 * Color.mk (v.x + 1.0) (v.y + 1.0) (v.z + 1.0)
  | none => do
    let unit : Vec3 Float := r.dir.normalized
    let t := 0.5 * (unit.y + 1.0)
    return (1.0 - t) * (Color.mk 1.0 1.0 1.0) + t * (Color.mk 0.5 0.7 1.0)

@[inline] def Float.max (x y : Float) : Float := if x ≤ y then y else x
@[inline] def Float.min (x y : Float) : Float := if x ≤ y then x else y

def Float.clampToUInt8 (x : Float) : UInt8 :=
  Float.toUInt8 <| Float.min 255 <| Float.max 0 x

def IO.FS.Handle.writeColor (handle : IO.FS.Handle) (c : Color Float) : IO Unit := do
  let r := Float.clampToUInt8 (256 * c.r)
  let g := Float.clampToUInt8 (256 * c.g)
  let b := Float.clampToUInt8 (256 * c.b)
  handle.putStrLn s!"{r} {g} {b}"

def writeTestImage (filename : String) : IO Unit := do
  let width : Nat := 400
  let height : Nat := width * 9 / 16
  let aspectRatio : Float := (Float.ofNat width) / (Float.ofNat height)
  let samplesPerPixel := 100

  let world : List Hittable := [
    mkSphere (Vec3.mk 0.0 0.0 (-1.0)) 0.5,
    mkSphere (Vec3.mk 0.0 (-100.5) (-1.0)) 100.0
  ]

  let cam := Camera.default aspectRatio

  IO.println s!"{Float.clampToUInt8 256}"
  IO.FS.withFile filename IO.FS.Mode.write λ handle => do
    handle.putStrLn "P3"
    handle.putStrLn s!"{width} {height} 255"
    for j' in [0:height] do
      let j := height - j' - 1
      for i in [0:width] do
        let mut pixelColor := Color.mk 0.0 0.0 0.0
        for s in [0:samplesPerPixel] do
          let u := (Float.ofNat i + (← IO.randFloat))/ Float.ofNat width
          let v := (Float.ofNat j + (← IO.randFloat))/ Float.ofNat height
          let ray := cam.getRay u v
          pixelColor := pixelColor + rayColor world ray
        handle.writeColor (pixelColor / Float.ofNat samplesPerPixel)

def main : List String → IO Unit
| [] => writeTestImage "out.ppm"
| (x::xs) => writeTestImage x
