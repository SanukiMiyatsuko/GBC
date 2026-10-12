import Mbekworm.MbekRank1.Basic

/-!
# `M = 0` の場合

`isOT 0` は単調非増加列全体と一致し、カントール標準形
`cantorSeq` によって `ψ₀(ω) = ω^ω` 未満の rank-one 標準形と順序同型になる。
-/

open T

namespace MbekRank1

/-! ## `expand 0` の計算 -/

theorem max?_append_singleton (xs : List Nat) (a b : Nat)
    (h : xs.max? = some a) : (xs ++ [b]).max? = some (max a b) := by
  cases xs with
  | nil => simp at h
  | cons x xs =>
      simp only [List.max?] at h ⊢
      injection h with h
      change some (List.foldl max x (xs ++ [b])) = some (max a b)
      rw [List.foldl_append]
      simp [h]

theorem max?_range_succ (m : Nat) :
    (List.range (m + 1)).max? = some m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [show m + 1 + 1 = (m + 1) + 1 by omega, List.range_succ]
      rw [max?_append_singleton _ m (m + 1) ih]
      simp

theorem parent_zero_append (l : List Nat) (v : Nat) :
    parent (l ++ [v]) 0 = some l.length := by
  simp [parent, parent_cand, max?_range_succ]

theorem parent_zero_cons (a : Nat) (l : List Nat) :
    parent (a :: l) 0 = some l.length := by
  simp [parent, parent_cand, max?_range_succ]

theorem true_parent_scan_empty_zero (list : List Nat) (pm : Nat)
    (hp : parent list #[].size = some pm) :
    true_parent_scan list pm #[] hp 0 (by simp) = none := by
  rfl

theorem true_parent_go_zero_singleton (k : Nat) :
    true_parent_go 0 [k + 1] (k + 1) #[] (by simp) = none := by
  rw [true_parent_go]
  simp only [Array.size_empty]
  split
  · rename_i hp
    rw [parent_zero_cons] at hp
  · rename_i pm hp
    have hpm : pm = 0 :=
      Option.some.inj (hp.symm.trans (parent_zero_cons (k + 1) []))
    subst pm
    simp [true_parent_scan_empty_zero, relatives]

theorem true_parent_go_zero_cons_append (a : Nat) (l : List Nat) (k : Nat) :
    true_parent_go 0 ((a :: l) ++ [k + 1]) (k + 1) #[] (by simp) =
      some l.length := by
  rw [true_parent_go]
  simp only [Array.size_empty]
  split
  · rename_i hp
    rw [parent_zero_append] at hp
    cases hp
  · rename_i pm hp
    have hpm : pm = (a :: l).length :=
      Option.some.inj (hp.symm.trans (parent_zero_append (a :: l) (k + 1)))
    subst pm
    have hget :
        ((a :: l) ++ [k + 1])[(a :: l).length]'(parent_lt_length _ 0 _ hp) =
          k + 1 := by
      simp
    rw [hget]
    split
    · rename_i hlt
      omega
    · simp only [Nat.zero_sub, Nat.min_self]
      rw [true_parent_scan_empty_zero]
      simp only [Nat.lt_irrefl, dite_false]
      rfl

theorem expand_zero_zero_last (l : List Nat) (n : Nat) :
    expand 0 (l ++ [0]) n = l := by
  simp [expand]

theorem expand_zero_succ_last (l : List Nat) (k n : Nat) :
    expand 0 (l ++ [k + 1]) n = l ++ List.replicate (n + 1) k := by
  cases l with
  | nil =>
      simp [expand, true_parent_go_zero_singleton, List.repeat]
  | cons a l =>
      have hlast : ((a :: l) ++ [k + 1]).getLast? = some (k + 1) :=
        List.getLast?_eq_some_iff.mpr ⟨a :: l, rfl⟩
      rw [expand, hlast]
      simp only [List.dropLast_append]
      rw [true_parent_go_zero_cons_append]
      simp [List.repeat, List.replicate_succ]

/-! ## `isOT 0` は単調非増加列全体 -/

/-- 単調非増加列。 -/
def Desc (xs : List Nat) : Prop := xs.Pairwise (fun a b => b ≤ a)

theorem desc_append_replicate (l : List Nat) (k n : Nat)
    (h : Desc (l ++ [k + 1])) : Desc (l ++ List.replicate (n + 1) k) := by
  have hparts := List.pairwise_append.mp h
  apply List.pairwise_append.mpr
  refine ⟨hparts.1, List.pairwise_replicate.mpr (Or.inr (Nat.le_refl k)), ?_⟩
  intro a ha b hb
  have hak := hparts.2.2 a ha (k + 1) (by simp)
  have hbk : b = k := (List.mem_replicate.mp hb).2
  subst b
  omega

theorem expand_zero_desc (xs : List Nat) (n : Nat) (h : Desc xs) :
    Desc (expand 0 xs n) := by
  cases hx : xs.getLast? with
  | none =>
      have hnil : xs = [] := List.getLast?_eq_none_iff.mp hx
      subst xs
      simp [expand, Desc]
  | some last =>
      obtain ⟨l, rfl⟩ := List.getLast?_eq_some_iff.mp hx
      cases last with
      | zero =>
          rw [expand_zero_zero_last]
          exact (List.pairwise_append.mp h).1
      | succ k =>
          rw [expand_zero_succ_last]
          exact desc_append_replicate l k n h

theorem isOT_zero_desc {xs : List Nat} (h : isOT 0 xs) : Desc xs := by
  induction h with
  | base n => simp [Desc]
  | step s _ n ih => exact expand_zero_desc s n ih

/-- 上界 `d+1` 未満の非増加列は `d` の連続と `d` 未満の非増加列に分かれる。 -/
theorem desc_split (d : Nat) :
    ∀ Q : List Nat, Desc Q → (∀ q ∈ Q, q < d + 1) →
      ∃ j Q', Q = List.replicate j d ++ Q' ∧ Desc Q' ∧ ∀ q ∈ Q', q < d := by
  intro Q
  induction Q with
  | nil => exact fun _ _ => ⟨0, [], rfl, List.Pairwise.nil, fun _ h => by cases h⟩
  | cons q Q ih =>
      intro hd hb
      have hq : q < d + 1 := hb q (by simp)
      have hQ := (List.pairwise_cons.mp hd)
      by_cases hqd : q = d
      · subst q
        obtain ⟨j, Q', hQ', hdesc, hlt⟩ :=
          ih hQ.2 (fun x hx => hb x (by simp [hx]))
        exact ⟨j + 1, Q', by simp [hQ', List.replicate_succ], hdesc, hlt⟩
      · refine ⟨0, q :: Q, rfl, hd, ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · have := hQ.1 x hx
          omega

theorem reach_zero (c : Nat) :
    ∀ P Q : List Nat, Desc Q → (∀ q ∈ Q, q < c) →
      Reach 0 (P ++ [c]) (P ++ Q) := by
  induction c with
  | zero =>
      intro P Q _ hb
      cases Q with
      | nil =>
          refine Reach.step _ 0 _ ?_
          rw [expand_zero_zero_last]
          simpa using Reach.refl P
      | cons q Q => exact absurd (hb q (by simp)) (Nat.not_lt_zero q)
  | succ d ih =>
      intro P Q hd hb
      obtain ⟨j, Q', rfl, hdesc, hlt⟩ := desc_split d Q hd hb
      refine Reach.step _ j _ ?_
      rw [expand_zero_succ_last,
        show P ++ List.replicate (j + 1) d = (P ++ List.replicate j d) ++ [d] by
          simp [List.replicate_succ']]
      simpa [List.append_assoc] using ih (P ++ List.replicate j d) Q' hdesc hlt

theorem desc_isOT_zero (xs : List Nat) (h : Desc xs) : isOT 0 xs := by
  cases xs with
  | nil =>
      have h0 := isOT.step (M := 0) [0] (isOT.base 0) 0
      have he : expand 0 [0] 0 = [] := expand_zero_zero_last [] 0
      rw [he] at h0
      exact h0
  | cons b rest =>
      have hr := reach_zero (b + 1) [] (b :: rest) h (by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · omega
        · have := (List.pairwise_cons.mp h).1 q hq
          omega)
      exact isOT_of_reach (isOT.base (b + 1)) (by simpa [LF] using hr)

/-! ## カントール標準形への写像 -/

/-- `[a₀, a₁, …] ↦ ω^{a₀} + ω^{a₁} + ⋯`（`ψ₀(n) = ω^n`）。 -/
def cantorSeq : List Nat → T
  | [] => Z
  | n :: ns => P 0 (T.ofNat n) (cantorSeq ns)

/-- `T.ofNat` の逆。 -/
def toNatT : T → Nat
  | Z => 0
  | P _ _ r => toNatT r + 1

/-- `cantorSeq` の逆。 -/
def uncantor : T → List Nat
  | Z => []
  | P _ s r => toNatT s :: uncantor r

theorem toNatT_ofNat (n : Nat) : toNatT (T.ofNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [T.ofNat, toNatT, ih]

theorem uncantor_cantorSeq (xs : List Nat) : uncantor (cantorSeq xs) = xs := by
  induction xs with
  | nil => rfl
  | cons n ns ih => simp [cantorSeq, uncantor, toNatT_ofNat, ih]

theorem ofNat_injective {m n : Nat} (h : T.ofNat m = T.ofNat n) : m = n := by
  rw [← toNatT_ofNat m, ← toNatT_ofNat n, h]

theorem cantorSeq_lt_iff (xs ys : List Nat) :
    cantorSeq xs < cantorSeq ys ↔ xs < ys := by
  constructor
  · intro h
    induction xs generalizing ys with
    | nil =>
        cases ys with
        | nil => cases h
        | cons y ys => exact List.Lex.nil
    | cons x xs ih =>
        cases ys with
        | nil => cases h
        | cons y ys =>
            rcases lt_inv 0 (T.ofNat x) (cantorSeq xs)
                0 (T.ofNat y) (cantorSeq ys) h with
              hzero | ⟨_, hmid⟩ | ⟨_, hmid, htail⟩
            · omega
            · exact List.Lex.rel (ofNat_reflect_lt hmid)
            · have hxy : x = y := ofNat_injective hmid
              subst y
              exact List.Lex.cons (ih ys htail)
  · intro h
    induction h with
    | nil => exact T.Lt.Z_lt_P _ _ _
    | rel hxy =>
        exact T.Lt.p_mid 0 (T.ofNat _) (T.ofNat _) _ _ (ofNat_strict_mono hxy)
    | cons _ ih =>
        exact T.Lt.p_tail 0 (T.ofNat _) _ _ ih

theorem G1_ofNat_lt (n : Nat) :
    ∀ x ∈ T.G1 0 (T.ofNat n), x < T.ofNat n := by
  induction n with
  | zero => simp [T.ofNat, T.G1]
  | succ n ih =>
      intro x hx
      simp only [T.ofNat, T.G1, Nat.zero_le, ite_true,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx
      · exact T.Lt.Z_lt_P _ _ _
      · exact lt_trans_thm _ _ _ (ih x hx) (ofNat_one_step n)

theorem cantorSeq_isNF1 : ∀ xs : List Nat, Desc xs → T.isNF1 (cantorSeq xs) := by
  intro xs
  induction xs with
  | nil => intro _; exact T.isNF1.z
  | cons n ns ih =>
      intro hnf
      have hrel := (List.pairwise_cons.mp hnf).1
      have htail := (List.pairwise_cons.mp hnf).2
      refine T.isNF1.p 0 (T.ofNat n) (cantorSeq ns)
        (IsN_isNF1 _ (ofNat_IsN n)) (ih htail) (G1_ofNat_lt n) ?_
      cases ns with
      | nil => exact T.Z_le _
      | cons m ms =>
          change P 0 (T.ofNat m) Z ≤ P 0 (T.ofNat n) Z
          rcases Nat.lt_or_eq_of_le (hrel m (by simp)) with hmn | rfl
          · exact Or.inl (T.Lt.p_mid 0 (T.ofNat m) (T.ofNat n) Z Z (ofNat_strict_mono hmn))
          · exact Or.inr rfl

theorem ofNat_lt_omega (n : Nat) : T.ofNat n < P 0 (P 0 Z Z) Z := by
  cases n with
  | zero => exact T.Lt.Z_lt_P _ _ _
  | succ n => exact T.Lt.p_mid 0 Z (P 0 Z Z) _ Z (T.Lt.Z_lt_P _ _ _)

theorem cantorSeq_lt_bound (xs : List Nat) : cantorSeq xs < bound 0 := by
  cases xs with
  | nil => exact T.Lt.Z_lt_P _ _ _
  | cons n ns =>
      exact T.Lt.p_mid 0 (T.ofNat n) (P 0 (P 0 Z Z) Z) (cantorSeq ns) Z (ofNat_lt_omega n)

/-! ## 逆写像 -/

theorem lt_one_eq_Z {s : T} (h : s < P 0 Z Z) : s = Z := by
  cases h with
  | Z_lt_P => rfl
  | p_head _ _ _ _ _ _ h => omega
  | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h

/-- 先頭が `1` 以下の標準形は自然数。 -/
theorem eq_ofNat_of_head_le_one :
    ∀ s : T, T.isNF1 s → T.head s ≤ P 0 Z Z → s = T.ofNat (toNatT s) := by
  intro s
  induction s with
  | Z => intro _ _; rfl
  | P j a b _ ihb =>
      intro hs hh
      obtain ⟨_, hb, _, hbh⟩ := T.isNF1_P_inv j a b hs
      have hja : j = 0 ∧ a = Z := by
        rcases hh with hh | hh
        · cases hh with
          | p_head _ _ _ _ _ _ h => omega
          | p_mid _ _ _ _ _ h | p_tail _ _ _ _ h => cases h
        · cases hh; exact ⟨rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ := hja
      simp only [toNatT, T.ofNat]
      rw [← ihb hb hbh]

theorem head_le_one_of_lt_omega {s : T} (h : s < P 0 (P 0 Z Z) Z) :
    T.head s ≤ P 0 Z Z := by
  cases h with
  | Z_lt_P => exact Or.inl (T.Lt.Z_lt_P _ _ _)
  | p_head _ _ _ _ _ _ h => omega
  | p_mid _ a _ _ _ h => rw [lt_one_eq_Z h]; exact Or.inr rfl
  | p_tail _ _ _ _ h => cases h

theorem cantorSeq_uncantor :
    ∀ t : T, T.isNF1 t → t < bound 0 → cantorSeq (uncantor t) = t := by
  intro t
  induction t with
  | Z => intro _ _; rfl
  | P i s r _ ihr =>
      intro ht hb
      obtain ⟨hs, hr, _, _⟩ := T.isNF1_P_inv i s r ht
      have hi : i = 0 ∧ s < P 0 (P 0 Z Z) Z := by
        cases hb with
        | p_head _ _ _ _ _ _ h => omega
        | p_mid _ _ _ _ _ h => exact ⟨rfl, h⟩
        | p_tail _ _ _ _ h => cases h
      obtain ⟨rfl, hsω⟩ := hi
      have hrb : r < bound 0 := by
        rcases T.isNF1_tail_le _ ht 0 s r rfl with h | h
        · exact lt_trans_thm _ _ _ h hb
        · rw [h]; exact hb
      simp only [uncantor, cantorSeq]
      rw [← eq_ofNat_of_head_le_one s hs (head_le_one_of_lt_omega hsω), ihr hr hrb]

theorem le_of_P0_ofNat_le {m n : Nat}
    (h : P 0 (T.ofNat m) Z ≤ P 0 (T.ofNat n) Z) : m ≤ n := by
  rcases h with h | h
  · rcases lt_inv 0 (T.ofNat m) Z 0 (T.ofNat n) Z h with h | ⟨_, h⟩ | ⟨_, _, h⟩
    · omega
    · exact Nat.le_of_lt (ofNat_reflect_lt h)
    · cases h
  · exact Nat.le_of_eq (ofNat_injective (T.P.inj h).2.1)

theorem desc_of_cantorSeq_isNF1 :
    ∀ xs : List Nat, T.isNF1 (cantorSeq xs) → Desc xs := by
  intro xs
  induction xs with
  | nil => intro _; exact List.Pairwise.nil
  | cons a rest ih =>
      intro h
      obtain ⟨_, hr, _, hh⟩ := T.isNF1_P_inv 0 (T.ofNat a) (cantorSeq rest) h
      have hd := ih hr
      refine List.pairwise_cons.mpr ⟨?_, hd⟩
      cases rest with
      | nil => intro _ hy; cases hy
      | cons b rest' =>
          have hba : b ≤ a := le_of_P0_ofNat_le hh
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hba
          · exact Nat.le_trans ((List.pairwise_cons.mp hd).1 y hy) hba

theorem uncantor_desc (t : T) (ht : T.isNF1 t) (hb : t < bound 0) :
    Desc (uncantor t) := by
  apply desc_of_cantorSeq_isNF1
  rw [cantorSeq_uncantor t ht hb]
  exact ht

/-! ## 順序同型 -/

/-- `M = 0` の順序同型。 -/
def iso0 : MbekRank1Iso 0 where
  toFun a := ⟨cantorSeq a.1, cantorSeq_isNF1 _ (isOT_zero_desc a.2), cantorSeq_lt_bound _⟩
  invFun b := ⟨uncantor b.1, desc_isOT_zero _ (uncantor_desc b.1 b.2.1 b.2.2)⟩
  left_inv a := Subtype.ext (uncantor_cantorSeq a.1)
  right_inv b := Subtype.ext (cantorSeq_uncantor b.1 b.2.1 b.2.2)
  map_rel_iff a b := cantorSeq_lt_iff a.1 b.1

end MbekRank1
