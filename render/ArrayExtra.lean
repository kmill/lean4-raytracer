namespace Array

-- TODO add unsafe version

def foldlM₂ {m : Type _ → Type _} [Monad m] (f : γ → α → β → m γ) (init : γ) (as : Array α) (bs : Array β) (h' : as.size = bs.size) (start := 0) (stop := as.size) : m γ :=
  let fold (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) (c : γ) : m γ := do
      if hlt : j < stop then
        match i with
        | 0    => pure c
        | i'+1 =>
          loop i' (j+1) (← f c (as.get ⟨j, Nat.ltOfLtOfLe hlt h⟩) (bs.get ⟨j, by { rw ←h'; exact Nat.ltOfLtOfLe hlt h }⟩))
      else
        pure c
    loop (stop - start) start init
  if h : stop ≤ as.size then
    fold stop h
  else
    fold as.size (Nat.leRefl _)

def mapM₂ {m : Type _ → Type _} [Monad m] (f : α → β → m γ) (as : Array α) (bs : Array β) (h : as.size = bs.size) : m (Array γ) :=
  foldlM₂ (fun cs a b => do let c ← f a b; pure (cs.push c)) (mkEmpty as.size) as bs h

@[inline]
def map₂ (f : α → β → γ) (as : Array α) (bs : Array β) (h : as.size = bs.size): Array γ :=
  Id.run <| mapM₂ f as bs h

end Array