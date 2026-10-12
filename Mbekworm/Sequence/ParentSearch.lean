import Mbekworm.Sequence.Transfer
import Mbekworm.Sequence.NormalForm

/-!
# The parent search over an arbitrary alphabet

The multi-level parent search `gTP` and the expansion `gExpand` for lists over
any decidable linear order, their agreement with `expand` on `ℕ`, and their
naturality under order embeddings.
-/

set_option linter.unusedSectionVars false

open GenBek

namespace Mbek

/-!
## The parent search over an arbitrary alphabet

`gTP m L q` is the true parent of the last entry of `L` when that entry is
replaced by `q`, computed by the same multi-level search as `true_parent_go`,
but for lists over any decidable linear order.  `gExpand` is the corresponding
expansion.  On `ℕ` they coincide with `true_parent_go` and `expand`.
-/

/-! ### Index searches -/

/-- The largest `i < n` with `p i`. -/
def lastIdx (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 => if p n then some n else lastIdx p n

theorem lastIdx_lt (p : Nat → Bool) : ∀ n i, lastIdx p n = some i → i < n
  | 0, i, h => by simp [lastIdx] at h
  | n + 1, i, h => by
      simp only [lastIdx] at h
      split at h
      · cases h; exact Nat.lt_succ_self n
      · exact Nat.lt_succ_of_lt (lastIdx_lt p n i h)

theorem max?_append_singleton (xs : List Nat) (a b : Nat)
    (h : xs.max? = some a) : (xs ++ [b]).max? = some (max a b) := by
  cases xs with
  | nil => cases h
  | cons x xs =>
      injection h with h
      change some (List.foldl max x (xs ++ [b])) = some (max a b)
      rw [List.foldl_append]
      simp [h]

theorem max?_filter_range (p : Nat → Bool) : ∀ n,
    ((List.range n).filter p).max? = lastIdx p n
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.filter_append]
      simp only [lastIdx]
      by_cases hp : p n = true
      · simp only [List.filter_cons, hp, ite_true, List.filter_nil]
        cases h : ((List.range n).filter p).max? with
        | none =>
            rw [List.max?_eq_none_iff] at h
            rw [h]; rfl
        | some a =>
            rw [max?_append_singleton _ a n h]
            have ha : a < n := by
              rw [max?_filter_range p n] at h
              exact lastIdx_lt p n a h
            congr 1; omega
      · simp only [List.filter_cons, hp, List.filter_nil]
        simp only [Bool.false_eq_true, ite_false, List.append_nil]
        exact max?_filter_range p n

theorem lastIdx_congr {p q : Nat → Bool} : ∀ n, (∀ i, i < n → p i = q i) →
    lastIdx p n = lastIdx q n
  | 0, _ => rfl
  | n + 1, h => by
      simp only [lastIdx, h n (Nat.lt_succ_self n),
        lastIdx_congr n (fun i hi => h i (Nat.lt_succ_of_lt hi))]

theorem lastIdx_add (p : Nat → Bool) (a : Nat) : ∀ b,
    lastIdx p (a + b) =
      match lastIdx (fun j => p (a + j)) b with
      | some j => some (a + j)
      | none => lastIdx p a
  | 0 => rfl
  | b + 1 => by
      rw [show a + (b + 1) = (a + b) + 1 by omega]
      simp only [lastIdx]
      split
      · rfl
      · exact lastIdx_add p a b

theorem relativesFinal_eq (list : List Nat) (M p : Nat) (hM : 0 < M) (hp : parent list M = some p)
    (r : Nat) (h : relatives list p M = some r) : relativesFinal list M p hM hp = r := by
  unfold relativesFinal
  split
  · rename_i r' hr'
    rw [h] at hr'
    exact (Option.some.inj hr').symm
  · rename_i hr'
    rw [h] at hr'
    cases hr'

section
variable {α : Type} [LT α] [DecidableEq α] [DecidableLT α]

mutual
def gParentCand (L : List α) : Nat → List Nat
  | 0 => List.range L.length
  | m + 1 =>
    match gParent L m with
    | none => []
    | some p => (List.range p).filter (fun i => decide (L.drop i < L.drop p))

def gParent (L : List α) (m : Nat) : Option Nat :=
  (gParentCand L m).max?
end

def gUncle (L : List α) (x m : Nat) : Option Nat :=
  (gParentCand L m).filter (fun i => decide (x < i)) |>.min?

def gRelatives (L : List α) (x n : Nat) : Option Nat :=
  match n with
  | 0 =>
    match x with
    | 0 => none
    | x' + 1 => x'
  | 1 => x
  | n' + 1 =>
    match gUncle L x n' with
    | none => none
    | some u => gRelatives L u n'

/-- The segment of `L` between the parents of levels `k` and `k - 1`. -/
def gSeg (L : List α) (k : Nat) : List α :=
  (L.drop ((gParent L k).getD 0)).take ((gParent L (k - 1)).getD 0 - (gParent L k).getD 0)

def gScan (L : List α) (pm limit : Nat) : Option Nat :=
  (((List.range limit).drop 1).find? (fun k => decide (L.drop pm < gSeg L k))).bind
    (fun k => gRelatives L pm (k + 1))

def ltAt (L : List α) (i : Nat) (q : α) : Bool :=
  match L[i]? with
  | some a => decide (a < q)
  | none => false

def gGo (m : Nat) (L : List α) (q : α) : Nat → Nat → Option Nat
  | 0, _ => none
  | f + 1, s =>
    match gParent L s with
    | none => none
    | some pm =>
      if ltAt L pm q then some pm
      else
        match gScan L pm (min (m - 1) s) with
        | some r => some r
        | none => if s = m then gRelatives L pm m else gGo m L q f (s + 1)

def gTP (m : Nat) (L : List α) (q : α) : Option Nat := gGo m L q (m + 1) 0

def gExpand (m : Nat) (L : List α) (q : α) (n : Nat) : List α :=
  match gTP m L q with
  | none => List.repeat (n + 1) (L.dropLast ++ [q])
  | some i => (L.dropLast ++ [q]) ++ List.repeat n ((L.dropLast ++ [q]).drop (i + 1))

end

/-! ### Agreement with the original definitions on `ℕ` -/

theorem gParentCand_nat (list : List Nat) : ∀ m, gParentCand list m = parent_cand list m ∧
    gParent list m = parent list m := by
  intro m
  induction m with
  | zero =>
      have h0 : gParentCand list 0 = parent_cand list 0 := by simp [gParentCand, parent_cand]
      exact ⟨h0, by simp only [gParent, parent, h0]⟩
  | succ m ih =>
      have h1 : gParentCand list (m + 1) = parent_cand list (m + 1) := by
        simp only [gParentCand, parent_cand, ih.2]
        cases parent list m <;> rfl
      exact ⟨h1, by simp only [gParent, parent, h1]⟩

theorem gParent_nat (list : List Nat) (m : Nat) : gParent list m = parent list m :=
  (gParentCand_nat list m).2

theorem gUncle_nat (list : List Nat) (x m : Nat) : gUncle list x m = uncle list x m := by
  simp only [gUncle, uncle, (gParentCand_nat list m).1]

theorem gRelatives_nat (list : List Nat) : ∀ n x, gRelatives list x n = relatives list x n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro x
      match n with
      | 0 => rfl
      | 1 => rfl
      | n' + 2 =>
          simp only [gRelatives, relatives, gUncle_nat]
          cases uncle list x (n' + 1) with
          | none => rfl
          | some u => exact ih (n' + 1) (by omega) u

theorem find?_map {β γ : Type} (f : β → γ) (p : γ → Bool) :
    ∀ l : List β, (l.map f).find? p = (l.find? (p ∘ f)).map f
  | [] => rfl
  | a :: l => by
      simp only [List.map_cons, List.find?_cons, Function.comp]
      cases p (f a) with
      | true => rfl
      | false => exact find?_map f p l

theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

theorem find?_bind_of_map {n : Nat} {ks : List (Fin n)} {ns : List Nat}
    (hks : ks.map Fin.val = ns) (P : Fin n → Bool) (P' : Nat → Bool) (hP : ∀ k ∈ ks, P k = P' k.val)
    (f : Fin n → Nat) (g : Nat → Option Nat) (hg : ∀ k ∈ ks, g k.val = some (f k)) :
    (ks.find? P).map f = (ns.find? P').bind g := by
  induction ks generalizing ns with
  | nil => subst hks; rfl
  | cons k ks ih =>
      subst hks
      simp only [List.map_cons, List.find?_cons]
      rw [hP k List.mem_cons_self]
      cases P' k.val with
      | true => simp only [Option.map_some, Option.bind_some]; exact (hg k List.mem_cons_self).symm
      | false =>
          exact ih rfl (fun j hj => hP j (List.mem_cons_of_mem _ hj))
            (fun j hj => hg j (List.mem_cons_of_mem _ hj))

theorem true_parent_scan_eq (list : List Nat) (pm : Nat) (plist : Array Nat)
    (hp : parent list plist.size = some pm) (limit : Nat) (hlimit : limit ≤ plist.size)
    (hinv : ∀ k (hk : k < plist.size), parent list k = some plist[k]) :
    true_parent_scan list pm plist hp limit hlimit = gScan list pm limit := by
  unfold true_parent_scan gScan
  simp only
  apply find?_bind_of_map
  · rw [List.map_map]
    have : (Fin.val ∘ Fin.castLE hlimit : Fin limit → Nat) = Fin.val := rfl
    rw [this, List.map_drop, finRange_map_val]
  · intro k hk
    have hk1 := hinv k.val k.isLt
    have hk2 := hinv (k.val - 1) (by have := k.isLt; omega)
    simp only [gSeg, gParent_nat, hk1, hk2, Option.getD_some, List.extract_eq_take_drop]
    rfl
  · intro k _
    unfold relativesAt
    rw [gRelatives_nat]
    split
    · rename_i r hr; exact hr
    · rename_i hr
      exact absurd hr (relatives_ne_none_of_parent list plist.size k.val pm k.isLt hp)

theorem ltAt_nat (list : List Nat) (pm : Nat) (h : pm < list.length) (q : Nat) :
    ltAt list pm q = decide (list[pm] < q) := by
  simp [ltAt, List.getElem?_eq_getElem h]

theorem true_parent_go_eq (M : Nat) (list : List Nat) (last : Nat) :
    ∀ (f : Nat) (plist : Array Nat) (hle : plist.size ≤ M), M - plist.size < f →
      (∀ k (hk : k < plist.size), parent list k = some plist[k]) →
      true_parent_go M list last plist hle = gGo M list (last - 1) f plist.size := by
  intro f
  induction f with
  | zero => intro plist hle hf; omega
  | succ f ih =>
      intro plist hle hf hinv
      rw [true_parent_go]
      simp only [gGo, gParent_nat]
      split
      · rename_i hp
        rw [hp]
      · rename_i pm hp
        conv => rhs; rw [hp]
        simp only
        rw [ltAt_nat list pm (parent_lt_length _ _ _ hp)]
        split
        · rename_i h; simp [h]
        · rename_i h
          simp only [h, decide_false, Bool.false_eq_true, if_false]
          rw [true_parent_scan_eq list pm plist hp _ _ hinv]
          split
          · rename_i r hr; rw [hr]
          · rename_i hr
            rw [hr]
            simp only
            split
            · rename_i hfin
              split
              · rename_i hM
                rw [gRelatives_nat]
                have hpM : parent list M = some pm := by rw [← hfin]; exact hp
                cases hr' : relatives list pm M with
                | none => exact absurd hr' (relatives_ne_none_final list M pm hM hpM)
                | some r => rw [relativesFinal_eq list M pm hM _ r hr']
              · rw [gRelatives_nat]
            · rename_i hfin
              rw [ih (plist.push pm) _ (by simp; omega)]
              · simp
              · intro k hk
                simp only [Array.size_push] at hk
                rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | hk
                · rw [Array.getElem_push_lt hk]; exact hinv k hk
                · subst hk; rw [Array.getElem_push_eq]; exact hp

theorem true_parent_go_eq_gTP (M : Nat) (list : List Nat) (last : Nat) :
    true_parent_go M list last #[] (by simp) = gTP M list (last - 1) := by
  unfold gTP
  exact true_parent_go_eq M list last (M + 1) #[] _ (by simp) (fun k hk => by simp at hk)

theorem expand_eq_gExpand (M : Nat) (s : List Nat) (c n : Nat) :
    expand M (s ++ [c + 1]) n = gExpand M (s ++ [c + 1]) c n := by
  have hlast : (s ++ [c + 1]).getLast? = some (c + 1) := by simp
  have hinit : (s ++ [c + 1]).dropLast = s := by simp
  unfold expand gExpand
  simp only [hinit, hlast]
  rw [true_parent_go_eq_gTP, Nat.add_sub_cancel]
  cases gTP M (s ++ [c + 1]) c <;> rfl

/-!
## Index descriptions of the generic parent search
-/

/-! ### Least index -/

/-- The least `i < n` with `p i`. -/
def firstIdx (p : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 =>
    match firstIdx p n with
    | some i => some i
    | none => if p n then some n else none

theorem firstIdx_lt (p : Nat → Bool) : ∀ n i, firstIdx p n = some i → i < n
  | 0, i, h => by simp [firstIdx] at h
  | n + 1, i, h => by
      simp only [firstIdx] at h
      split at h
      · rename_i j hj
        cases h; exact Nat.lt_succ_of_lt (firstIdx_lt p n _ hj)
      · split at h
        · cases h; exact Nat.lt_succ_self n
        · cases h

theorem firstIdx_spec (p : Nat → Bool) : ∀ n i, firstIdx p n = some i →
    p i = true ∧ ∀ j, j < i → p j = false
  | 0, i, h => by simp [firstIdx] at h
  | n + 1, i, h => by
      simp only [firstIdx] at h
      split at h
      · rename_i j hj
        cases h; exact firstIdx_spec p n _ hj
      · rename_i hn
        split at h
        · rename_i hpn
          cases h
          refine ⟨hpn, fun j hj => ?_⟩
          cases hpj : p j with
          | false => rfl
          | true =>
              exfalso
              have : ∀ n, (∃ j, j < n ∧ p j = true) → firstIdx p n ≠ none := by
                intro n
                induction n with
                | zero => intro ⟨j, hj, _⟩; omega
                | succ n ihn =>
                    intro ⟨j, hj, hpj⟩
                    simp only [firstIdx]
                    split
                    · simp
                    · rename_i hnone
                      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
                      · exact absurd hnone (ihn ⟨j, hj, hpj⟩)
                      · simp [hpj]
              exact this n ⟨j, hj, hpj⟩ hn
        · cases h

theorem firstIdx_none_iff (p : Nat → Bool) : ∀ n, firstIdx p n = none ↔ ∀ j, j < n → p j = false
  | 0 => by simp [firstIdx]
  | n + 1 => by
      simp only [firstIdx]
      constructor
      · intro h j hj
        split at h
        · cases h
        · rename_i hn
          split at h
          · cases h
          · rename_i hpn
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
            · exact (firstIdx_none_iff p n).mp hn j hj
            · simpa using hpn
      · intro h
        have hn : firstIdx p n = none :=
          (firstIdx_none_iff p n).mpr (fun j hj => h j (Nat.lt_succ_of_lt hj))
        rw [hn]
        simp [h n (Nat.lt_succ_self n)]

theorem firstIdx_eq_some_of (p : Nat → Bool) (n i : Nat) (hi : i < n) (hp : p i = true)
    (hmin : ∀ j, j < i → p j = false) : firstIdx p n = some i := by
  cases h : firstIdx p n with
  | none => exact absurd ((firstIdx_none_iff p n).mp h i hi) (by simp [hp])
  | some k =>
      have hk := firstIdx_spec p n k h
      have hkn := firstIdx_lt p n k h
      rcases Nat.lt_trichotomy k i with hki | rfl | hik
      · exact absurd (hmin k hki) (by simp [hk.1])
      · rfl
      · exact absurd (hk.2 i hik) (by simp [hp])

theorem firstIdx_congr {p q : Nat → Bool} (n : Nat) (h : ∀ i, i < n → p i = q i) :
    firstIdx p n = firstIdx q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [firstIdx, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

/-- Skipping an initial segment where the predicate fails. -/
theorem firstIdx_shift (p : Nat → Bool) (a : Nat) (ha : ∀ i, i < a → p i = false) :
    ∀ b, firstIdx p (a + b) = (firstIdx (fun j => p (a + j)) b).map (a + ·)
  | 0 => by
      simp only [Nat.add_zero]
      rw [(firstIdx_none_iff p a).mpr ha]
      rfl
  | b + 1 => by
      rw [show a + (b + 1) = (a + b) + 1 by omega]
      simp only [firstIdx]
      rw [firstIdx_shift p a ha b]
      cases firstIdx (fun j => p (a + j)) b with
      | some j => rfl
      | none =>
          simp only [Option.map_none]
          split <;> rfl

/-! ### Minimum and maximum of filtered ranges -/

theorem min_nat_of_lt {a b : Nat} (h : a < b) : min a b = a := by
  simp only [min]
  split <;> omega

theorem min?_append_singleton_lt (xs : List Nat) (a b : Nat) (h : xs.min? = some a)
    (hab : a < b) : (xs ++ [b]).min? = some a := by
  cases xs with
  | nil => simp at h
  | cons x xs =>
      simp only [List.min?] at h ⊢
      injection h with h
      change some (List.foldl min x (xs ++ [b])) = some a
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, h]
      rw [min_nat_of_lt hab]

theorem min?_filter_range (p : Nat → Bool) : ∀ n,
    ((List.range n).filter p).min? = firstIdx p n
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.filter_append]
      simp only [firstIdx]
      rw [← min?_filter_range p n]
      cases h : ((List.range n).filter p).min? with
      | none =>
          rw [List.min?_eq_none_iff] at h
          rw [h]
          cases hp : p n <;> simp [hp]
      | some a =>
          have ha : a < n := by
            rw [min?_filter_range p n] at h
            exact firstIdx_lt p n a h
          cases hp : p n
          · simp [hp, h]
          · simp only [List.filter_cons, hp, ite_true, List.filter_nil]
            exact min?_append_singleton_lt _ a n h ha

theorem filter_true' {β : Type} : ∀ l : List β, l.filter (fun _ => true) = l
  | [] => rfl
  | a :: l => by simp [filter_true' l]

theorem max?_range (n : Nat) : (List.range n).max? = lastIdx (fun _ => true) n := by
  have := max?_filter_range (fun _ => true) n
  rwa [filter_true'] at this

theorem lastIdx_true (n : Nat) : lastIdx (fun _ => true) n = if n = 0 then none else some (n - 1) := by
  cases n with
  | zero => rfl
  | succ n => simp [lastIdx]

theorem lastIdx_spec (p : Nat → Bool) : ∀ n i, lastIdx p n = some i →
    p i = true ∧ ∀ j, i < j → j < n → p j = false
  | 0, i, h => by simp [lastIdx] at h
  | n + 1, i, h => by
      simp only [lastIdx] at h
      split at h
      · rename_i hpn
        cases h
        exact ⟨hpn, fun j hj hjn => by omega⟩
      · rename_i hpn
        have ih := lastIdx_spec p n i h
        refine ⟨ih.1, fun j hj hjn => ?_⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjn) with hjn | rfl
        · exact ih.2 j hj hjn
        · simpa using hpn

theorem lastIdx_none_iff (p : Nat → Bool) : ∀ n, lastIdx p n = none ↔ ∀ j, j < n → p j = false
  | 0 => by simp [lastIdx]
  | n + 1 => by
      simp only [lastIdx]
      constructor
      · intro h j hj
        split at h
        · cases h
        · rename_i hpn
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
          · exact (lastIdx_none_iff p n).mp h j hj
          · simpa using hpn
      · intro h
        rw [if_neg (by simp [h n (Nat.lt_succ_self n)])]
        exact (lastIdx_none_iff p n).mpr (fun j hj => h j (Nat.lt_succ_of_lt hj))

/-! ### The generic search in terms of indices -/

section
variable {α : Type} [LT α] [DecidableEq α] [DecidableLT α]

theorem gParent_zero (L : List α) :
    gParent L 0 = if L.length = 0 then none else some (L.length - 1) := by
  simp only [gParent, gParentCand]
  rw [max?_range, lastIdx_true]

theorem gParent_succ (L : List α) (m : Nat) :
    gParent L (m + 1) =
      match gParent L m with
      | none => none
      | some p => lastIdx (fun i => decide (L.drop i < L.drop p)) p := by
  conv => lhs; rw [gParent, gParentCand]
  cases gParent L m with
  | none => rfl
  | some p => exact max?_filter_range _ p

theorem gUncle_zero (L : List α) (x : Nat) :
    gUncle L x 0 = firstIdx (fun i => decide (x < i)) L.length := by
  simp only [gUncle, gParentCand]
  exact min?_filter_range _ _

theorem gUncle_succ (L : List α) (x m : Nat) :
    gUncle L x (m + 1) =
      match gParent L m with
      | none => none
      | some p => firstIdx (fun i => decide (x < i) && decide (L.drop i < L.drop p)) p := by
  conv => lhs; rw [gUncle, gParentCand]
  cases gParent L m with
  | none => rfl
  | some p =>
      simp only
      rw [List.filter_filter]
      exact min?_filter_range _ p

theorem gParent_succ_lt {L : List α} {m p : Nat} (h : gParent L (m + 1) = some p) :
    ∃ q, gParent L m = some q ∧ p < q ∧ L.drop p < L.drop q := by
  rw [gParent_succ] at h
  cases hq : gParent L m with
  | none => rw [hq] at h; cases h
  | some q =>
      rw [hq] at h
      exact ⟨q, rfl, lastIdx_lt _ q p h, by simpa using (lastIdx_spec _ q p h).1⟩

theorem gParent_lt_of_lt {L : List α} : ∀ {m k p : Nat}, k < m → gParent L m = some p →
    ∃ q, gParent L k = some q ∧ p < q := by
  intro m
  induction m with
  | zero => intro k p hk; omega
  | succ m ih =>
      intro k p hk hp
      obtain ⟨q, hq, hpq, _⟩ := gParent_succ_lt hp
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · obtain ⟨r, hr, hqr⟩ := ih hk hq
        exact ⟨r, hr, by omega⟩
      · exact ⟨q, hq, hpq⟩

theorem gParent_lt_length {L : List α} : ∀ {m p : Nat}, gParent L m = some p → p < L.length := by
  intro m
  induction m with
  | zero =>
      intro p hp
      rw [gParent_zero] at hp
      split at hp
      · cases hp
      · cases hp; omega
  | succ m ih =>
      intro p hp
      obtain ⟨q, hq, hpq, _⟩ := gParent_succ_lt hp
      exact Nat.lt_trans hpq (ih hq)

theorem gRelatives_ne_none_of_lt_parent (L : List α) : ∀ (k x p : Nat), gParent L k = some p →
    x < p → gRelatives L x (k + 1) ≠ none := by
  intro k
  induction k with
  | zero => intro x p _ _; simp [gRelatives]
  | succ k ih =>
      intro x p hp hx
      obtain ⟨q, hq, hpq, hdrop⟩ := gParent_succ_lt hp
      have hu : gUncle L x (k + 1) ≠ none := by
        rw [gUncle_succ, hq]
        simp only
        intro h
        have := (firstIdx_none_iff _ q).mp h p hpq
        simp [hdrop, hx] at this
      cases hu' : gUncle L x (k + 1) with
      | none => exact absurd hu' hu
      | some u =>
          have huq : u < q := by
            rw [gUncle_succ, hq] at hu'
            exact firstIdx_lt _ q u hu'
          have hrec := ih u q hq huq
          show (match gUncle L x (k + 1) with
            | none => (none : Option Nat)
            | some v => gRelatives L v (k + 1)) ≠ none
          rw [hu']
          exact hrec

theorem gRelatives_ne_none (L : List α) (m p : Nat) (hm : 0 < m) (hp : gParent L m = some p) :
    gRelatives L p m ≠ none := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨q, hq, hpq⟩ := gParent_lt_of_lt (Nat.lt_succ_self m') hp
  exact gRelatives_ne_none_of_lt_parent L m' p q hq hpq

end

/-!
## Expansions commute with order embeddings of the alphabet
-/

section
variable {α β : Type} [LT α] [strict_linear_order α] [DecidableEq α] [DecidableLT α]
  [LT β] [strict_linear_order β] [DecidableEq β] [DecidableLT β]

/-- `f` is an order embedding on the entries of `S`. -/
def EmbOn (f : α → β) (S : List α) : Prop := ∀ x ∈ S, ∀ y ∈ S, x < y → f x < f y

theorem EmbOn.lt_iff {f : α → β} {S : List α} (hf : EmbOn f S) {x y : α} (hx : x ∈ S) (hy : y ∈ S) :
    f x < f y ↔ x < y := by
  constructor
  · intro h
    rcases strict_linear_order.total x y with h' | h' | h'
    · exact h'
    · exact absurd (strict_partial_order.trans _ _ _ h (hf y hy x hx h'))
        (strict_partial_order.irrefl _)
    · subst h'; exact absurd h (strict_partial_order.irrefl _)
  · exact hf x hx y hy

theorem EmbOn.inj {f : α → β} {S : List α} (hf : EmbOn f S) {x y : α} (hx : x ∈ S) (hy : y ∈ S)
    (h : f x = f y) : x = y := by
  rcases strict_linear_order.total x y with h' | h' | h'
  · exact absurd h (ne_of_lt' (hf x hx y hy h'))
  · exact absurd h.symm (ne_of_lt' (hf y hy x hx h'))
  · exact h'

theorem EmbOn.list_lt_iff {f : α → β} {S : List α} (hf : EmbOn f S) {p q : List α}
    (hp : ∀ x ∈ p, x ∈ S) (hq : ∀ x ∈ q, x ∈ S) : p.map f < q.map f ↔ p < q := by
  constructor
  · intro h
    rcases List.strictLinearTotal p q with h' | h' | h'
    · exact h'
    · have := map_lt_map (fun x hx y hy hxy => hf x (hq x hx) y (hp y hy) hxy)
        (fun x hx y hy e => hf.inj (hq x hx) (hp y hy) e) h'
      exact absurd (strict_partial_order.trans _ _ _ h this) (strict_partial_order.irrefl _)
    · subst h'; exact absurd h (strict_partial_order.irrefl _)
  · exact map_lt_map (fun x hx y hy hxy => hf x (hp x hx) y (hq y hy) hxy)
      (fun x hx y hy e => hf.inj (hp x hx) (hq y hy) e)

theorem mem_of_mem_drop' {L : List α} {i : Nat} {x : α} (h : x ∈ L.drop i) : x ∈ L :=
  List.mem_of_mem_drop h

variable {f : α → β} {S : List α}

theorem gParentCand_map {L : List α} (hf : EmbOn f S) (hL : ∀ x ∈ L, x ∈ S) :
    ∀ m, gParentCand (L.map f) m = gParentCand L m ∧ gParent (L.map f) m = gParent L m := by
  intro m
  induction m with
  | zero =>
      have h0 : gParentCand (L.map f) 0 = gParentCand L 0 := by simp [gParentCand]
      exact ⟨h0, by simp only [gParent, h0]⟩
  | succ m ih =>
      have h1 : gParentCand (L.map f) (m + 1) = gParentCand L (m + 1) := by
        simp only [gParentCand, ih.2]
        cases gParent L m with
        | none => rfl
        | some p =>
            simp only
            apply List.filter_congr
            intro i _
            rw [← List.map_drop, ← List.map_drop]
            simp only [decide_eq_decide]
            exact hf.list_lt_iff (fun x hx => hL x (mem_of_mem_drop' hx))
              (fun x hx => hL x (mem_of_mem_drop' hx))
      exact ⟨h1, by simp only [gParent, h1]⟩

theorem gUncle_map {L : List α} (hf : EmbOn f S) (hL : ∀ x ∈ L, x ∈ S) (x m : Nat) :
    gUncle (L.map f) x m = gUncle L x m := by
  simp only [gUncle, (gParentCand_map hf hL m).1]

theorem gRelatives_map {L : List α} (hf : EmbOn f S) (hL : ∀ x ∈ L, x ∈ S) :
    ∀ n x, gRelatives (L.map f) x n = gRelatives L x n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro x
      match n with
      | 0 => rfl
      | 1 => rfl
      | n' + 2 =>
          simp only [gRelatives, gUncle_map hf hL]
          cases gUncle L x (n' + 1) with
          | none => rfl
          | some u => exact ih (n' + 1) (by omega) u

theorem gSeg_map {L : List α} (hf : EmbOn f S) (hL : ∀ x ∈ L, x ∈ S) (k : Nat) :
    gSeg (L.map f) k = (gSeg L k).map f := by
  simp only [gSeg, (gParentCand_map hf hL k).2, (gParentCand_map hf hL (k - 1)).2,
    List.map_take, List.map_drop]

theorem gSeg_sub (L : List α) (k : Nat) : ∀ x ∈ gSeg L k, x ∈ L := by
  intro x hx
  exact mem_of_mem_drop' (List.mem_of_mem_take hx)

theorem find?_congr'' {γ : Type} {p p' : γ → Bool} : ∀ {l : List γ}, (∀ x ∈ l, p x = p' x) →
    l.find? p = l.find? p'
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.find?_cons, h a List.mem_cons_self]
      cases p' a with
      | true => rfl
      | false => exact find?_congr'' (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem gScan_map {L : List α} (hf : EmbOn f S) (hL : ∀ x ∈ L, x ∈ S) (pm limit : Nat) :
    gScan (L.map f) pm limit = gScan L pm limit := by
  simp only [gScan, gRelatives_map hf hL]
  congr 1
  apply find?_congr''
  intro k _
  rw [gSeg_map hf hL, ← List.map_drop]
  simp only [decide_eq_decide]
  exact hf.list_lt_iff (fun x hx => hL x (mem_of_mem_drop' hx))
    (fun x hx => hL x (gSeg_sub L k x hx))

theorem ltAt_map {L : List α} {q : α} (hf : EmbOn f S) (hL : ∀ x ∈ L, x ∈ S) (hq : q ∈ S)
    (i : Nat) : ltAt (L.map f) i (f q) = ltAt L i q := by
  simp only [ltAt, List.getElem?_map]
  cases h : L[i]? with
  | none => rfl
  | some a =>
      simp only [Option.map_some]
      have ha : a ∈ L := List.mem_of_getElem? h
      simp only [decide_eq_decide]
      exact hf.lt_iff (hL a ha) hq

theorem gGo_map {L : List α} {q : α} (hf : EmbOn f S) (hL : ∀ x ∈ L, x ∈ S) (hq : q ∈ S) (m : Nat) :
    ∀ fuel s, gGo m (L.map f) (f q) fuel s = gGo m L q fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
      intro s
      simp only [gGo, (gParentCand_map hf hL s).2]
      cases gParent L s with
      | none => rfl
      | some pm =>
          simp only [ltAt_map hf hL hq, gScan_map hf hL, gRelatives_map hf hL, ih]

theorem gTP_map {L : List α} {q : α} (hf : EmbOn f S) (hL : ∀ x ∈ L, x ∈ S) (hq : q ∈ S) (m : Nat) :
    gTP m (L.map f) (f q) = gTP m L q := gGo_map hf hL hq m (m + 1) 0

theorem repeat_map {γ δ : Type} (g : γ → δ) (n : Nat) (l : List γ) :
    (List.repeat n l).map g = List.repeat n (l.map g) := by
  simp [List.repeat, List.map_flatten, List.map_replicate]

/-- **Naturality of expansions.** -/
theorem gExpand_map {L : List α} {q : α} (hf : EmbOn f S) (hL : ∀ x ∈ L, x ∈ S) (hq : q ∈ S)
    (m n : Nat) : gExpand m (L.map f) (f q) n = (gExpand m L q n).map f := by
  simp only [gExpand, gTP_map hf hL hq]
  cases gTP m L q with
  | none => simp [repeat_map, List.map_dropLast]
  | some i => simp [repeat_map, List.map_dropLast, List.map_drop]

end

end Mbek
