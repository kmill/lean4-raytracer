import render.vec3

@[inline] def Float.max (x y : Float) : Float := if x ≤ y then y else x
@[inline] def Float.min (x y : Float) : Float := if x ≤ y then x else y
@[inline] def Float.abs (x : Float) : Float := if x ≤ 0 then -x else x

def Float.pi : Float := 3.1415926535897932385
def Float.infinity : Float := 1e100 -- fix this

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
    if p.lengthSquared < 1.0 then
      return p
  return ⟨1, 0, 0⟩

def IO.randVec3InUnitDisk : IO (Vec3 Float) := do
  for i in [0:100] do -- 8e-29 probability of failure
    let p := Vec3.mk (← IO.randFloat (-1.0) (1.0)) (← IO.randFloat (-1.0) (1.0)) 0.0
    if p.lengthSquared < 1.0 then
      return p
  return ⟨0, 0, 0⟩

structure Ray (α : Type _) where
  origin : Vec3 α
  dir : Vec3 α

def Ray.at [Add α] [Mul α] (r : Ray α) (t : α) : Vec3 α := r.origin + t * r.dir

structure Camera where
  origin : Vec3 Float
  lowerLeftCorner : Vec3 Float
  horizontal : Vec3 Float
  vertical : Vec3 Float
  (u v w : Vec3 Float) /- right up back -/
  lensRadius : Float

/--
vfov is the vertical field of view (in degrees)
-/
def Camera.default
      (lookFrom lookAt vup : Vec3 Float)
      (vfov : Float)
      (aspectRatio : Float)
      (aperture : Float)
      (focusDist : Float) :
      Camera :=
  let theta := vfov / 180. * Float.pi
  let h := Float.tan (theta / 2)
  let viewportHeight := 2.0 * h
  let viewportWidth := aspectRatio * viewportHeight

  let w := (lookFrom - lookAt).normalized
  let u := (vup.cross w).normalized
  let v := w.cross u

  let origin := lookFrom
  let horizontal := focusDist * viewportWidth * u
  let vertical := focusDist * viewportHeight * v
  let lowerLeftCorner := origin - horizontal/2.0 - vertical/2.0 - focusDist * w

  Camera.mk origin lowerLeftCorner horizontal vertical u v w (aperture / 2.0)

def Camera.getRay (c : Camera) (s t : Float) : IO (Ray Float) := do
  let rd := c.lensRadius * (← IO.randVec3InUnitDisk)
  let offset := rd.x * c.u + rd.y * c.v
  Ray.mk (c.origin + offset) (c.lowerLeftCorner + s*c.horizontal + t*c.vertical - c.origin - offset)

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
  let cosTheta := Float.min (- uv.dot n) 1.0
  let rOutPerp := etai_over_etat * (uv + cosTheta * n)
  let rOutParallel := (-Float.sqrt (Float.abs (1.0 - rOutPerp.lengthSquared))) * n
  rOutPerp + rOutParallel

def dielectric (indexOfRefraction : Float) : Material where
  scatter (r : Ray Float) (hitrec : HitRecord) := do
    let refractionRatio := if hitrec.frontFace then 1.0/indexOfRefraction else indexOfRefraction
    let unitDirection := r.dir.normalized
    let cosTheta := Float.min (-unitDirection.dot hitrec.normal) 1.0
    let sinTheta := Float.sqrt (1.0 - cosTheta * cosTheta)
    let cannotRefract : Bool := refractionRatio * sinTheta > 1.0

    -- Schlick's approximation
    let reflectance (cosine : Float) (refIdx : Float) : Float :=
      let r0' := (1 - refIdx) / (1 + refIdx)
      let r0 := r0' * r0'
      r0 + (1 - r0) * Float.pow (1 - cosine) 5

    let direction : Vec3 Float :=
      if cannotRefract || reflectance cosTheta refractionRatio > (← IO.randFloat) then
        Vec3.reflect unitDirection hitrec.normal
      else
        refract unitDirection hitrec.normal refractionRatio

    let scattered := Ray.mk hitrec.p direction
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

def hitList (hs : Array Hittable) (r : Ray Float) (tmin tmax : Float) : Option (HitRecord × Material) := Id.run <| do
  let mut hitrec : Option (HitRecord × Material) := none
  for obj in hs do
    let closest := (hitrec.map (HitRecord.t ∘ Prod.fst)).getD tmax
    hitrec := obj.hit r tmin closest <|> hitrec
  return hitrec

def rayColor (hs : Array Hittable) (r : Ray Float) : (depth : Nat) → IO (Color Float)
| 0 => return ⟨0, 0, 0⟩ -- exceeded ray bounce limit, no more light gathered
| (depth+1) => do
  match hitList hs r 0.001 Float.infinity with
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

def randomScene : IO (Array Hittable) := do
  let mut world : Array Hittable := #[]

  -- Ground
  world := world.push <| mkSphere ⟨0, -1000, 0⟩ 1000 (lambertian ⟨0.5, 0.5, 0.5⟩)

  for a' in [0:22] do
    let a := Float.ofNat a' - 11
    for b' in [0:22] do
      let b := Float.ofNat b' - 11
      let center : Vec3 Float := ⟨a + 0.9 * (← IO.randFloat), 0.2, b + 0.9 * (← IO.randFloat)⟩
      if Vec3.length (center - Vec3.mk 4 0.2 0) > 0.9 then
        let chooseMat ← IO.randFloat
        if chooseMat < 0.9 then
          let albedo : Color Float := (← IO.randVec3) * (← IO.randVec3)
          world := world.push <| mkSphere center 0.2 (lambertian albedo)
        else if chooseMat < 0.95 then
          let albedo : Color Float ← IO.randVec3 0.5 1
          let fuzz ← IO.randFloat 0 0.5
          world := world.push <| mkSphere center 0.2 (metal albedo fuzz)
        else
          world := world.push <| mkSphere center 0.2 (dielectric 1.5)

  world := world.push <| mkSphere ⟨0, 1, 0⟩ 1 (dielectric 1.5)
  world := world.push <| mkSphere ⟨-4, 1, 0⟩ 1 (lambertian ⟨0.4, 0.2, 0.1⟩)
  world := world.push <| mkSphere ⟨4, 1, 0⟩ 1 (metal ⟨0.7, 0.6, 0.5⟩)

  return world

def writeTestImage (filename : String) : IO Unit := do
  let width : Nat := 500
  let height : Nat := width * 2 / 3
  let aspectRatio : Float := (Float.ofNat width) / (Float.ofNat height)
  let numThreads := 8
  let samplesPerPixel := 10
  let maxDepth := 30

  let world ← randomScene

  let lookFrom : Vec3 Float := ⟨13, 2, 3⟩
  let lookAt : Vec3 Float := ⟨0, 0, 0⟩
  let vup : Vec3 Float := ⟨0, 1, 0⟩
  let distToFocus := 10
  let aperture := 0.1
  let cam := Camera.default lookFrom lookAt vup 20.0 aspectRatio aperture distToFocus

  let renderTask (showProgress := false) : IO (Array (Color Float)) := do
    let mut pixels : Array (Color Float) := Array.empty
    for j' in [0:height] do
      if showProgress then
        IO.println s!"line {j'+1} of {height}"
      let j := height - j' - 1
      for i in [0:width] do
        let mut pixelColor := Color.black
        for s in [0:samplesPerPixel] do
          let u := (Float.ofNat i + (← IO.randFloat))/ Float.ofNat width
          let v := (Float.ofNat j + (← IO.randFloat))/ Float.ofNat height
          let ray ← cam.getRay u v
          pixelColor := pixelColor + (← rayColor world ray maxDepth)
        pixels := pixels.push pixelColor
    return pixels

  IO.println s!"Starting {numThreads} threads."
  let mut tasks := Array.empty
  for i in [0:numThreads] do
    tasks := tasks.push (← IO.asTask (renderTask (i = 0)))
  let mut pixels : Array (Color Float) := Array.mkArray (height * width) Color.black

  for t in tasks do
    let pixels' ← (IO.ofExcept (← IO.wait t))
    let pixels'' := pixels
    for i in [0:height*width] do
      pixels := pixels.set! i (pixels'[i] + pixels''[i])

  IO.println s!"Writing to {filename}"
 
  IO.FS.withFile filename IO.FS.Mode.write λ handle => do
    handle.putStrLn "P3"
    handle.putStrLn s!"{width} {height} 255"
    for i in [0:height*width] do
      let pixel := pixels[i]
      handle.writeColor (pixel / Float.ofNat (samplesPerPixel * numThreads))

def main : List String → IO Unit
| [] => writeTestImage "out.ppm"
| (x::xs) => writeTestImage x
