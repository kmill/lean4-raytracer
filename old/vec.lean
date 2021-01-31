import render.ArrayExtra
import render.NatExtra
import render.Algebra

def Function.leftInverse (g : β → α) (f : α → β) : Prop := ∀ x, g (f x) = x
def Function.rightInverse (g : β → α) (f : α → β) : Prop := Function.leftInverse f g

structure Equiv (α : Sort u) (β : Sort v) where
    toFun : α → β
    invFun : β → α
    leftInv : Function.leftInverse invFun toFun
    rightInv : Function.rightInverse invFun toFun

infix:25 " ≃ " => Equiv

def Equiv.symm (f : α ≃ β) : β ≃ α where
    toFun := f.invFun
    invFun := f.toFun
    leftInv := f.rightInv
    rightInv := f.leftInv

/-- An equivalence "is" a function. -/
instance : CoeFun (α ≃ β) (λ _ => α → β) where
    coe := Equiv.toFun

/-- A finite type with a specific enumeration. -/
class Enumerable (α : Type u) where
    card : Nat
    enum : α ≃ Fin card

instance : Enumerable (Fin n) where
    card := n
    enum := { toFun := id
              invFun := id
              leftInv := λ _ => rfl
              rightInv := λ _ => rfl }

section CartesianProduct

theorem cartEncodeProp {i j m n : Nat} (hi : i < m) (hj : j < n) : i * n + j < m * n := by
    cases m with
    | zero => apply False.elim; exact Nat.notLtZero _ hi
    | succ m => {
        rw Nat.succMul;
        exact Nat.ltOfLeOfLt (Nat.addLeAddRight (Nat.mulLeMulRight _ (Nat.leOfLtSucc hi)) _) (Nat.addLtAddLeft hj _)
    }

def cartDecode {n m : Nat} : Fin (n * m) → Fin n × Fin m
| ⟨k, h⟩ =>
    (⟨k / m, Nat.div_lt_of_lt_mul h⟩,
     ⟨k % m, Nat.modLt _ (by { cases m; apply False.elim; rw Nat.mulZero at h; exact Nat.notLtZero _ h; apply Nat.succPos})⟩)

instance [Enumerable α] [Enumerable β] : Enumerable (α × β) where
    card := Enumerable.card α * Enumerable.card β
    enum := {
        toFun := λ (a, b) =>
            let ⟨i, hi⟩ := Enumerable.enum a
            let ⟨j, hj⟩ := Enumerable.enum b
            ⟨i * Enumerable.card β + j, cartEncodeProp hi hj⟩
        invFun := λ n =>
            let (i, j) := cartDecode n
            (Enumerable.enum.symm i, Enumerable.enum.symm j)
        leftInv := sorry
        rightInv := sorry
    }

end CartesianProduct



instance : Enumerable Bool where
    card := 2
    enum := {
        toFun := fun
        | false => 0
        | true => 1
        invFun := fun
        | ⟨0, _⟩ => false
        | ⟨1, _⟩ => true
        | ⟨n+2, h⟩ => False.elim (Nat.notSuccLeZero _ (Nat.leOfSuccLeSucc (Nat.leOfSuccLeSucc h)))
        leftInv := by
            intro
            | true => rfl
            | false => rfl
        rightInv := by
            intro
            | ⟨0, _⟩ => rfl
            | ⟨1, _⟩ => rfl
            | ⟨n+2, h⟩ => exact False.elim (Nat.notSuccLeZero _ (Nat.leOfSuccLeSucc (Nat.leOfSuccLeSucc h)))
    }

instance : Enumerable Empty where
    card := 0
    enum := {
        toFun := fun t => nomatch t
        invFun := fun
        | ⟨n, h⟩ => False.elim (Nat.notSuccLeZero _ h)
        leftInv := fun t => nomatch t
        rightInv := fun t => nomatch t
    }

def Enumerable.listOf.aux (α : Type u) [Enumerable α] : Nat -> Nat -> List α
| lo, 0 => []
| lo, (left+1) =>
    if h : lo < Enumerable.card α then
        Enumerable.enum.symm ⟨lo, h⟩ :: aux α (lo + 1) left
    else [] -- Shouldn't happen, but makes the definition easy.

/-- Create a list of every term in the Enumerable type in order. -/
def Enumerable.listOf (α : Type u) [Enumerable α] : List α :=
    Enumerable.listOf.aux α 0 (Enumerable.card α)

structure Vec (ι : Type u) [Enumerable ι] (α : Type v) where
    array : Array α
    hasSize : array.size = Enumerable.card ι

namespace Vec
variable {ι : Type _} [Enumerable ι]

def fill (a : α) : Vec ι α where
    array := Array.mkArray (Enumerable.card ι) a
    hasSize := Array.sizeMkArrayEq ..

def empty [Inhabited α] : Vec ι α :=
    fill Inhabited.default

@[inline] def translateIdx (v : Vec ι α) (i : ι) : Fin v.array.size :=
    let ⟨n, h⟩ := Enumerable.enum i
    ⟨n, by rw v.hasSize; exact h⟩

/-- Get the value associated to a particular index. -/
@[inline] def get (v : Vec ι α) (i : ι) : α :=
    v.array.get (v.translateIdx i)

/-- support `v[i]` notation. -/
@[inline] def getOp (self : Vec ι α) (idx : ι) : α := self.get idx

/-- Set the value associated to a particular index. -/
@[inline] def set (v : Vec ι α) (i : ι) (a : α) : Vec ι α where
    array := v.array.set (v.translateIdx i) a
    hasSize := by rw [Array.sizeSetEq, v.hasSize]

@[inline] def forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Vec ι α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
    as.array.forIn b f

def pure (x : α) : Vec ι α := fill x

@[inline] def of (f : ι → α) : Vec ι α where
    array := do
        let mut a := Array.empty
        for i in Enumerable.listOf ι do
            a := a.push $ f i
        return a
    hasSize := sorry -- need to define differently to be able to easily prove this

macro "vec" xs:Lean.explicitBinders " => " b:term : term => Lean.expandExplicitBinders `Vec.of xs b

def reindex (v : Vec ι α) (ι' : Type _) [Enumerable ι'] (h : Enumerable.card ι = Enumerable.card ι') : Vec ι' α where
    array := v.array
    hasSize := by rw [←h, v.hasSize]

def bind [Enumerable κ] (f : α → Vec κ β) (v : Vec ι α) : Vec (ι × κ) β where
    array := Id.run <| Array.foldlM (λ w a => w ++ (f a).array) Array.empty v.array
    hasSize := sorry

@[inline]
def map (v : Vec ι α) (f : α → β) : Vec ι β where
    array := v.array.map f
    hasSize := sorry

@[inline]
def map₂ (v : Vec ι α) (w : Vec ι β) (f : α → β → γ) : Vec ι γ where
    array := Array.map₂ f v.array w.array (by { rw [v.hasSize, ← w.hasSize] })
    hasSize := sorry

instance [Enumerable ι] [Add α] : Add (Vec ι α) where
    add v w := Vec.map₂ v w (. + .)
instance [Enumerable ι] [Sub α] : Sub (Vec ι α) where
    sub v w := Vec.map₂ v w (. - .)
instance [Enumerable ι] [Mul α] : Mul (Vec ι α) where
    mul v w := Vec.map₂ v w (. * .)
instance [Enumerable ι] [Div α] : Div (Vec ι α) where
    div v w := Vec.map₂ v w (. / .)
instance [Enumerable ι] [Neg α] : Neg (Vec ι α) where
    neg v := Vec.map v (- .)

-- Scalar multiplication
instance [Enumerable ι] [Mul α] : HMul α (Vec ι α) (Vec ι α) where
    hMul c v := v.map (c * .)
-- Scalar division
instance [Enumerable ι] [Div α] : HDiv (Vec ι α) α (Vec ι α) where
    hDiv v c := v.map (. / c)
-- Zero vector
instance [Enumerable ι] [Zero α] : Zero (Vec ι α) where
    zero := vec i => 0

def lengthSquared [Add α] [Mul α] [Zero α] (v : Vec ι α) : α :=
    Id.run <| v.array.foldlM (λ x a => x + a * a) 0

def length (v : Vec ι Float) : Float := Float.sqrt <| v.lengthSquared

def normalized (v : Vec ι Float) : Vec ι Float := v / v.length

def dot [Add α] [Mul α] [Zero α] (v w : Vec ι α) : α :=
    Id.run <| Array.foldlM₂ (λ x a b => x + a * b) 0 v.array w.array (by { rw [v.hasSize, ← w.hasSize] })

end Vec

theorem List.toArraySizeEq (x : List α) : x.toArray.size = x.length := sorry

def List.toDenseVec (x : List α) : Vec (Fin x.length) α where
    array := x.toArray
    hasSize := List.toArraySizeEq ..

syntax "![" sepBy(term, ", ") "]" : term

macro_rules
  | `(![ $elems,* ]) => `(List.toDenseVec [ $elems,* ])

instance [Repr α] [Enumerable ι] : Repr (Vec ι α) where
    reprPrec v _ :=
        if v.array.size == 0 then
            "![]"
        else
            Std.Format.bracketFill "![" (@Std.Format.joinSep _ ⟨repr⟩ (v.array.toList) ("," ++ Std.Format.line)) "]"

example : Vec (Fin 3) Nat := ![2,22,222]

abbrev Vec3 (α : Type _) := Vec (Fin 3) α

namespace Vec3

def mk (x y z : α) : Vec3 α where
    array := #[x, y, z]
    hasSize := rfl

@[inline] def x (v : Vec3 α) : α := v[⟨0, rfl⟩]
@[inline] def y (v : Vec3 α) : α := v[⟨1, rfl⟩]
@[inline] def z (v : Vec3 α) : α := v[⟨2, rfl⟩]

def cross [Sub α] [Mul α] (v w : Vec3 α) : Vec3 α :=
    ![v.y*w.z - v.z*w.y, v.z*w.x - v.x*w.z, v.x*w.y - v.y*w.x]

end Vec3

inductive ColorChannel
| R | G | B

open ColorChannel

instance : Enumerable ColorChannel where
    card := 3
    enum := {
        toFun := fun
        | R => 0
        | G => 1
        | B => 2
        invFun := fun
        | ⟨0, _⟩ => R
        | ⟨1, _⟩ => G
        | ⟨2, _⟩ => B
        | ⟨n+3, h⟩ => False.elim (Nat.notSuccLeZero _ (Nat.leOfSuccLeSucc (Nat.leOfSuccLeSucc (Nat.leOfSuccLeSucc h))))
        leftInv := by
            intro
            | R => rfl
            | G => rfl
            | B => rfl
        rightInv := by
            intro
            | ⟨0, _⟩ => rfl
            | ⟨1, _⟩ => rfl
            | ⟨2, _⟩ => rfl
            | ⟨n+3, h⟩ => exact False.elim (Nat.notSuccLeZero _ (Nat.leOfSuccLeSucc (Nat.leOfSuccLeSucc (Nat.leOfSuccLeSucc h))))
    }

abbrev Color α := Vec ColorChannel α

def Color.mk (r g b : α) : Color α where
    array := #[r, g, b]
    hasSize := rfl

namespace Color

@[inline] def r (v : Color α) : α := v[R]
@[inline] def g (v : Color α) : α := v[G]
@[inline] def b (v : Color α) : α := v[B]

end Color