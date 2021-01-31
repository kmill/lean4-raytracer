theorem Nat.zeroDiv {n : Nat} : 0 / n = 0 := by
    rw Nat.divDef
    have key : ¬ (0 < n ∧ n ≤ 0) by
        intro h
        have h' := Nat.ltOfLtOfLe h.1 h.2
        exact Nat.notLtZero 0 h'
    rw ifNeg key

theorem Nat.div_le_div_of_mul_aux (k n m : Nat) : n / k ≤ (n + m) / k := by {
    induction m with
    | zero => { exact Nat.leRefl _ }
    | succ m ih => { exact sorry }
}

theorem Nat.div_le_div_of_mul {k n m : Nat} (h : n ≤ m) : n / k ≤ m / k := by {
    have h' := Nat.div_le_div_of_mul_aux k n (m - n);
    exact sorry
}

theorem Nat.div_le_of_le_mul {k n m : Nat} (h : k ≤ n * m) : k / m ≤ n := by {
    induction k with
    | zero => { rw Nat.zeroDiv; exact Nat.zeroLe _ }
    | succ k ih => {
        have hk : k ≤ n * m := Nat.leTrans (Nat.leSucc _) h;
        have ih' := ih (Nat.leTrans (Nat.leSucc _) h);
        exact sorry
    }
}

theorem Nat.div_lt_of_lt_mul {k n m : Nat} (h : k < n * m) : k / m < n := by {
    exact sorry
}