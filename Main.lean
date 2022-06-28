import Render.Vec3

@[inline] def Float.max (x y : Float) : Float := if x ≤ y then y else x
@[inline] def Float.min (x y : Float) : Float := if x ≤ y then x else y
@[inline] def Float.abs (x : Float) : Float := if x ≤ 0 then -x else x

def Float.pi : Float := 3.1415926535897932385
@[inline] def Float.infinity : Float := 1e100 -- fix this

/-- Uniform at random in [0, 1)-/
def randomFloat {gen} [RandomGen gen] (g : gen) : Float × gen :=
  let (n, g') := RandomGen.next g
  let (lo, hi) := RandomGen.range g
  (Float.ofNat (n - lo) / Float.ofNat (hi - lo + 1), g')

def IO.randFloat (lo := 0.0) (hi := 1.0) : IO Float := do
  let gen ← IO.stdGenRef.get
  let (r, gen) := randomFloat gen
  IO.stdGenRef.set gen
  return lo + (hi - lo) * r

def IO.randVec3 (lo := 0.0) (hi := 1.0) : IO (Vec3 Float) :=
  return ⟨←IO.randFloat lo hi, ←IO.randFloat lo hi, ←IO.randFloat lo hi⟩

def IO.randVec3InUnitSphere : IO (Vec3 Float) := do
  for _ in [0:100] do -- 7e-33 probability of failure
    let p ← IO.randVec3 (-1.0) (1.0)
    if p.lengthSquared < 1.0 then
      return p
  return ⟨1, 0, 0⟩

def IO.randVec3InUnitDisk : IO (Vec3 Float) := do
  for _ in [0:100] do -- 2e-67 probability of failure
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
  (u v w : Vec3 Float) /- right, up, back -/
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
  return { origin := c.origin + offset
           dir := c.lowerLeftCorner + s*c.horizontal + t*c.vertical - c.origin - offset }

inductive MaterialResponse
| emit (c : Color Float)
| scatter (albedo : Color Float) (scattered : Ray Float)

def MaterialResponse.absorb : MaterialResponse := MaterialResponse.emit Color.black

inductive Material
| lambertian (albedo : Color Float)
| metal (albedo : Color Float) (fuzz : Float := 0.0)
| dielectric (indexOfRefraction : Float)
| sky

structure HitRecord where
  p : Vec3 Float
  t : Float
  material : Material
  normal : Vec3 Float
  frontFace : Bool

@[inline]
def HitRecord.withNormal
      (p : Vec3 Float) (t : Float) (m : Material)
      (dir : Vec3 Float) (outwardNormal : Vec3 Float) : HitRecord :=
  let frontFace : Bool := dir.dot outwardNormal < 0.0
  { p := p
    t := t
    material := m
    normal := if frontFace then outwardNormal else -outwardNormal
    frontFace := frontFace }

@[inline]
def Vec3.refract (uv : Vec3 Float) (n : Vec3 Float) (etai_over_etat : Float) : Vec3 Float :=
  let cosTheta := Float.min (- uv.dot n) 1.0
  let rOutPerp := etai_over_etat * (uv + cosTheta * n)
  let rOutParallel := (-Float.sqrt (1.0 - rOutPerp.lengthSquared).abs) * n
  rOutPerp + rOutParallel

def HitRecord.scatter (hitrec : HitRecord) (r : Ray Float) : IO MaterialResponse :=
  match hitrec.material with
  | .lambertian albedo => do
      let mut scatterDir := hitrec.normal + (←IO.randVec3InUnitSphere).normalized
      if scatterDir.nearZero then
        scatterDir := hitrec.normal
      return .scatter albedo { origin := hitrec.p, dir := scatterDir }
  | .metal albedo fuzz => do
      let reflected := r.dir.normalized.reflect hitrec.normal
      let scattered := { origin := hitrec.p, dir := reflected + fuzz * (← IO.randVec3InUnitSphere) }
      if scattered.dir.dot hitrec.normal > 0.0 then
        return .scatter albedo scattered
      else
        return .absorb
  | .dielectric indexOfRefraction => do
      let refractionRatio := if hitrec.frontFace then 1.0/indexOfRefraction else indexOfRefraction
      let unitDirection := r.dir.normalized
      let cosTheta := Float.min (-unitDirection.dot hitrec.normal) 1.0
      let sinTheta := Float.sqrt (1.0 - cosTheta * cosTheta)
      let cannotRefract : Bool := refractionRatio * sinTheta > 1.0

      -- Schlick's approximation
      let reflectance :=
        let r0' := (1 - refractionRatio) / (1 + refractionRatio)
        let r0 := r0' * r0'
        r0 + (1 - r0) * Float.pow (1 - cosTheta) 5

      let direction : Vec3 Float :=
        if cannotRefract || reflectance > (← IO.randFloat) then
          Vec3.reflect unitDirection hitrec.normal
        else
          Vec3.refract unitDirection hitrec.normal refractionRatio

      let scattered := { origin := hitrec.p, dir := direction }
      return .scatter Color.white scattered
  | .sky => do
    let unit : Vec3 Float := r.dir.normalized
    let t := 0.5 * (unit.y + 1.0)
    return .emit <| (1.0 - t) * Color.white + t * (Color.mk 0.5 0.7 1.0)

inductive Hittable
| sphere (center : Vec3 Float) (radius : Float) (mat : Material)

def Hittable.hit (r : Ray Float) (tmin : Float) (hitrec : HitRecord) : (obj : Hittable) → HitRecord
| sphere center radius mat => Id.run do
  let oc := r.origin - center
  let a := r.dir.lengthSquared
  let halfb := Vec3.dot oc r.dir
  let c := oc.lengthSquared - radius * radius
  let discr := halfb*halfb - a*c
  if discr < 0.0 then
    return hitrec
  let sqrtd := discr.sqrt
  -- Find the nearest root that lies in the acceptable range
  let mut root := (-halfb - sqrtd) / a
  if root < tmin || hitrec.t < root then
    root := (-halfb + sqrtd) / a
    if root < tmin || hitrec.t < root then
      return hitrec
  let t := root
  let p := r.at t
  let outwardNormal := (p - center) / radius
  return HitRecord.withNormal p t mat r.dir outwardNormal

def hitList (hs : Array Hittable) (r : Ray Float) (tmin tmax : Float) : HitRecord := Id.run do
  let mut hitrec : HitRecord :=
    { p := ⟨0, 0, 0⟩
      t := tmax
      material := Material.sky
      normal := ⟨0, 0, 0⟩
      frontFace := true }
  for obj in hs do
    hitrec := obj.hit r tmin hitrec
  return hitrec

def rayColor (hs : Array Hittable) (r : Ray Float) :
  (depth : Nat) → (acc : Color Float) → IO (Color Float)
| 0, _ => return Color.black -- exceeded ray bounce limit, no more light gathered
| depth + 1, acc => do
  match ← (hitList hs r 0.001 Float.infinity).scatter r with
  | .emit c => return acc * c
  | .scatter albedo scattered => rayColor hs scattered depth (albedo * acc)

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
  world := world.push <| .sphere ⟨0, -1000, 0⟩ 1000 (.lambertian ⟨0.5, 0.5, 0.5⟩)

  for a' in [0:22] do
    let a := Float.ofNat a' - 11
    for b' in [0:22] do
      let b := Float.ofNat b' - 11
      let center : Vec3 Float := ⟨a + 0.9 * (← IO.randFloat), 0.2, b + 0.9 * (← IO.randFloat)⟩
      if Vec3.length (center - Vec3.mk 4 0.2 0) > 0.9 then
        let chooseMat ← IO.randFloat
        if chooseMat < 0.9 then
          let albedo : Color Float := (← IO.randVec3) * (← IO.randVec3)
          world := world.push <| .sphere center 0.2 (.lambertian albedo)
        else if chooseMat < 0.95 then
          let albedo : Color Float ← IO.randVec3 0.5 1
          let fuzz ← IO.randFloat 0 0.5
          world := world.push <| .sphere center 0.2 (.metal albedo fuzz)
        else
          world := world.push <| .sphere center 0.2 (.dielectric 1.5)

  world := world.push <| .sphere ⟨0, 1, 0⟩ 1 (.dielectric 1.5)
  world := world.push <| .sphere ⟨-4, 1, 0⟩ 1 (.lambertian ⟨0.4, 0.2, 0.1⟩)
  world := world.push <| .sphere ⟨4, 1, 0⟩ 1 (.metal ⟨0.7, 0.6, 0.5⟩)

  return world

def writeTestImage (filename : String) : IO Unit := do
  let width : Nat := 500
  let height : Nat := width * 2 / 3
  let aspectRatio : Float := (Float.ofNat width) / (Float.ofNat height)
  let numThreads := 8
  let samplesPerPixel := 10
  let maxDepth := 30

  -- Set the seed to something specific for determinism
  IO.stdGenRef.set mkStdGen

  let world ← randomScene

  let lookFrom : Vec3 Float := ⟨13, 2, 3⟩
  let lookAt : Vec3 Float := ⟨0, 0, 0⟩
  let vup : Vec3 Float := ⟨0, 1, 0⟩
  let distToFocus := 10
  let aperture := 0.1
  let cam := Camera.default lookFrom lookAt vup 20.0 aspectRatio aperture distToFocus

  let renderTask (showProgress := false) : IO (Array (Color Float)) := do
    let width' := Float.ofNat width
    let height' := Float.ofNat height
    let mut pixels : Array (Color Float) := Array.empty
    for line in [0:height] do
      if showProgress then
        IO.println s!"line {line+1} of {height}"
      let j := height - line - 1
      let j' := Float.ofNat j
      for i in [0:width] do
        let i' := Float.ofNat i
        let mut pixelColor := Color.black
        for _ in [0:samplesPerPixel] do
          let u := (i' + (← IO.randFloat)) / width'
          let v := (j' + (← IO.randFloat)) / height'
          let ray ← cam.getRay u v
          pixelColor := pixelColor + (← rayColor world ray maxDepth Color.white)
        pixels := pixels.push pixelColor
    return pixels

  IO.println s!"Starting {numThreads} threads."
  let mut tasks := Array.empty
  for i in [0:numThreads] do
    tasks := tasks.push (← IO.asTask (renderTask (i = 0)))
  let mut pixels : Array (Color Float) := Array.mkArray (height * width) Color.black

  for t in tasks do
    let pixels' ← IO.ofExcept (← IO.wait t)
    let pixels'' := pixels
    for i in [0:height*width] do
      pixels := pixels.set! i (pixels'[i] + pixels''[i])

  IO.println s!"Writing to {filename}"
 
  IO.FS.withFile filename IO.FS.Mode.write λ handle => do
    handle.putStrLn "P3"
    handle.putStrLn s!"{width} {height} 255"
    for i in [0:height*width] do
      let pixel := pixels[i]
      handle.writeColor <| pixel / Float.ofNat (samplesPerPixel * numThreads)

def main : List String → IO Unit
| [] => writeTestImage "out.ppm"
| (x::_) => writeTestImage x
