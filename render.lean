import render.vec3

@[inline] def Float.max (x y : Float) : Float := if x ≤ y then y else x
@[inline] def Float.min (x y : Float) : Float := if x ≤ y then x else y
@[inline] def Float.abs (x : Float) : Float := if x ≤ 0 then -x else x

/-- Uniform at random in [0, 1)-/
def randomFloat {gen} [RandomGen gen] (g : gen) : Float × gen :=
  let (n, g') := RandomGen.next g
  let (lo, hi) := RandomGen.range g
  (Float.ofNat (n - lo) / Float.ofNat (hi - lo + 1), g')

def IO.randFloat (lo := 0.0) (hi := 1.0) : IO Float := do
  let gen ← IO.stdGenRef.get
  let (r, gen) := randomFloat gen
  IO.stdGenRef.set gen
  pure $ lo + (hi - lo) * r

def IO.randVec3 (lo := 0.0) (hi := 1.0) : IO (Vec3 Float) :=
  return ⟨←IO.randFloat lo hi, ←IO.randFloat lo hi, ←IO.randFloat lo hi⟩

def IO.randVec3InUnitSphere : IO (Vec3 Float) := do
  for i in [0:100] do -- 8e-29 probability of failure
    let p ← IO.randVec3 (-1.0) (1.0)
    if p.lengthSquared >= 1.0 then
      return p
  return ⟨1, 0, 0⟩

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

@[inline]
def HitRecord.withNormal (p : Vec3 Float) (t : Float) (r : Ray Float) (outwardNormal : Vec3 Float) : HitRecord :=
  let frontFace : Bool := r.dir.dot outwardNormal < 0.0
  let normal : Vec3 Float := if frontFace then outwardNormal else -outwardNormal
  return {
    p := p
    t := t
    normal := normal
    frontFace := frontFace
  }

inductive MaterialResponse
| absorb
| scatter (albedo : Color Float) (scattered : Ray Float)

structure Material where
  scatter : Ray Float → HitRecord → IO MaterialResponse

def lambertian (albedo : Color Float) : Material where
  scatter (r : Ray Float) (hitrec : HitRecord) := do
    let mut scatterDir := hitrec.normal + (←IO.randVec3InUnitSphere).normalized
    if scatterDir.nearZero then
      scatterDir := hitrec.normal
    let scattered := Ray.mk hitrec.p scatterDir
    return MaterialResponse.scatter albedo scattered

def metal (albedo : Color Float) (fuzz : Float := 0.0) : Material where
  scatter (r : Ray Float) (hitrec : HitRecord) := do
    let reflected := r.dir.normalized.reflect hitrec.normal
    let scattered := Ray.mk hitrec.p (reflected + fuzz * (← IO.randVec3InUnitSphere))
    if scattered.dir.dot hitrec.normal > 0.0 then
      return MaterialResponse.scatter albedo scattered
    else
      return MaterialResponse.absorb

def refract (uv : Vec3 Float) (n : Vec3 Float) (etai_over_etat : Float) : Vec3 Float :=
  let cos_theta := Float.min (- uv.dot n) 1.0
  let r_out_perp := etai_over_etat * (uv + cos_theta * n)
  let r_out_parallel := (-Float.sqrt (Float.abs (1.0 - r_out_perp.lengthSquared))) * n
  r_out_perp + r_out_parallel

def dialectric (indexOfRefraction : Float) : Material where
  scatter (r : Ray Float) (hitrec : HitRecord) := do
    let refractionRatio := if hitrec.frontFace then 1.0/indexOfRefraction else indexOfRefraction
    let unitDirection := r.dir.normalized
    let refracted := refract unitDirection hitrec.normal refractionRatio
    let scattered := Ray.mk hitrec.p refracted
    return MaterialResponse.scatter Color.white scattered

structure Hittable where
  hit : Ray Float → Float -> Float -> Option (HitRecord × Material)

def mkSphere (center : Vec3 Float) (radius : Float) (mat : Material) : Hittable where
  hit (r : Ray Float) (tmin tmax : Float) := Id.run <| do
    let oc := r.origin - center
    let a := r.dir.lengthSquared
    let halfb := Vec3.dot oc r.dir
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
    return some (HitRecord.withNormal p t r outwardNormal, mat)

def hitList (hs : List Hittable) (r : Ray Float) (tmin tmax : Float) : Option (HitRecord × Material) := Id.run <| do
  let mut hitrec : Option (HitRecord × Material) := none
  for obj in hs do
    let closest := (hitrec.map (HitRecord.t ∘ Prod.fst)).getD tmax
    hitrec := obj.hit r tmin closest <|> hitrec
  return hitrec

def rayColor (hs : List Hittable) (r : Ray Float) : (depth : Nat) → IO (Color Float)
| 0 => return ⟨0, 0, 0⟩ -- exceeded ray bounce limit, no more light gathered
| (depth+1) => do
  match hitList hs r 0.001 100000000.0 with
  | some (hitrec, mat) => do
    match ← mat.scatter r hitrec with
    | MaterialResponse.absorb =>
        return Color.black
    | MaterialResponse.scatter albedo scattered =>
        return albedo * (← rayColor hs scattered depth)
  | none => do
    let unit : Vec3 Float := r.dir.normalized
    let t := 0.5 * (unit.y + 1.0)
    return (1.0 - t) * Color.white + t * (Color.mk 0.5 0.7 1.0)

def Float.clampToUInt8 (x : Float) : UInt8 :=
  Float.toUInt8 <| Float.min 255 <| Float.max 0 x

def IO.FS.Handle.writeColor (handle : IO.FS.Handle) (c : Color Float) : IO Unit := do
  let r := Float.clampToUInt8 (256 * c.r.sqrt)
  let g := Float.clampToUInt8 (256 * c.g.sqrt)
  let b := Float.clampToUInt8 (256 * c.b.sqrt)
  handle.putStrLn s!"{r} {g} {b}"

def writeTestImage (filename : String) : IO Unit := do
  let width : Nat := 400
  let height : Nat := width * 9 / 16
  let aspectRatio : Float := (Float.ofNat width) / (Float.ofNat height)
  let samplesPerPixel := 50
  let maxDepth := 20

  let material_ground := lambertian (Color.mk 0.8 0.8 0.0)
  let material_center := lambertian (Color.mk 0.7 0.3 0.3)
  let material_left := metal (Color.mk 0.8 0.8 0.8) 0.3
  let material_right := metal (Color.mk 0.8 0.6 0.2) 1.0
  let material_center := dialectric 1.5

  let world : List Hittable := [
    mkSphere (Vec3.mk 0.0 (-100.5) (-1.0)) 100.0 material_ground,
    mkSphere (Vec3.mk 0.0 0.0 (-1.0)) 0.5 material_center,
    mkSphere (Vec3.mk (-1.0) 0.0 (-1.0)) 0.5 material_left,
    mkSphere (Vec3.mk 1.0 0.0 (-1.0)) 0.5 material_right
  ]

  let cam := Camera.default aspectRatio

  IO.println s!"{Float.clampToUInt8 256}"
  IO.FS.withFile filename IO.FS.Mode.write λ handle => do
    handle.putStrLn "P3"
    handle.putStrLn s!"{width} {height} 255"
    for j' in [0:height] do
      IO.println s!"line {j'+1} of {height}"
      let j := height - j' - 1
      for i in [0:width] do
        let mut pixelColor := Color.black
        for s in [0:samplesPerPixel] do
          let u := (Float.ofNat i + (← IO.randFloat))/ Float.ofNat width
          let v := (Float.ofNat j + (← IO.randFloat))/ Float.ofNat height
          let ray := cam.getRay u v
          pixelColor := pixelColor + (← rayColor world ray maxDepth)
        handle.writeColor (pixelColor / Float.ofNat samplesPerPixel)

def main : List String → IO Unit
| [] => writeTestImage "out.ppm"
| (x::xs) => writeTestImage x
