import Mbekworm.Buchholz.order

instance natStrictLinearOrder : strict_linear_order Nat where
  irrefl _ := Nat.lt_irrefl _
  trans _ _ _ := Nat.lt_trans
  total a b := by omega

instance (priority := low) stdStrictLinearOrder (A : Type u)
    [LT A] [LE A] [Std.IsLinearOrder A] [Std.LawfulOrderLT A]
    [DecidableLT A] [DecidableLE A] : strict_linear_order A where
  irrefl a haa := by
    have h := (Std.LawfulOrderLT.lt_iff a a).mp haa
    exact h.2 (Std.IsPreorder.le_refl a)
  trans a b c hab hbc := by
    have hab' := (Std.LawfulOrderLT.lt_iff a b).mp hab
    have hbc' := (Std.LawfulOrderLT.lt_iff b c).mp hbc
    apply (Std.LawfulOrderLT.lt_iff a c).mpr
    constructor
    · exact Std.IsPreorder.le_trans a b c hab'.1 hbc'.1
    · intro hca
      exact hab'.2 (Std.IsPreorder.le_trans b c a hbc'.1 hca)
  total a b := by
    if hab : a < b then
      exact Or.inl hab
    else if hba : b < a then
      exact Or.inr (Or.inl hba)
    else
      apply Or.inr
      apply Or.inr
      rcases Std.IsLinearPreorder.le_total a b with hab' | hba'
      · have hba' : b ≤ a := by
          if h : b ≤ a then
            exact h
          else
            exact (hab ((Std.LawfulOrderLT.lt_iff a b).mpr ⟨hab', h⟩)).elim
        exact Std.IsPartialOrder.le_antisymm a b hab' hba'
      · have hab' : a ≤ b := by
          if h : a ≤ b then
            exact h
          else
            exact (hba ((Std.LawfulOrderLT.lt_iff b a).mpr ⟨hba', h⟩)).elim
        exact Std.IsPartialOrder.le_antisymm a b hab' hba'

theorem List.strictLinearTotal
    {A : Type u} [LT A] [strict_linear_order A] :
    ∀ xs ys : List A, xs < ys ∨ ys < xs ∨ xs = ys
  | [], [] => Or.inr (Or.inr rfl)
  | [], _ :: _ => Or.inl List.Lex.nil
  | _ :: _, [] => Or.inr (Or.inl List.Lex.nil)
  | x :: xs, y :: ys => by
      rcases strict_linear_order.total x y with hxy | hyx | rfl
      · exact Or.inl (List.Lex.rel hxy)
      · exact Or.inr (Or.inl (List.Lex.rel hyx))
      · rcases List.strictLinearTotal xs ys with hxy | hyx | hEq
        · exact Or.inl (List.Lex.cons hxy)
        · exact Or.inr (Or.inl (List.Lex.cons hyx))
        · exact Or.inr (Or.inr (congrArg (List.cons x) hEq))

instance (A : Type u) [LT A] [strict_linear_order A] :
    strict_linear_order (List A) where
  irrefl xs := List.lex_irrefl strict_partial_order.irrefl xs
  trans _ _ _ :=
    List.lex_trans (fun hxy hyz => strict_partial_order.trans _ _ _ hxy hyz)
  total := List.strictLinearTotal
