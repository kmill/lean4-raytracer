class Zero (α : Type _) where
    zero : α

class One (α : Type _) where
    one : α

instance [OfNat α 0] : Zero α where
    zero := 0

instance [OfNat α 1] : One α where
    one := 1

instance [Zero α] : OfNat α (natLit! 0) where
    ofNat := Zero.zero
instance [One α] : OfNat α (natLit! 1) where
    ofNat := One.one