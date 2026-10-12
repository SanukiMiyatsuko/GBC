import Mbekworm.Sequence.ParentSearch
import Mbekworm.Sequence.NormalForm

/-!
# Reductions of the expansion

R1: an expansion inside the last piece above the least letter.
R2: an expansion at the least letter runs one level down, on the pieces.
-/

set_option linter.unusedSectionVars false

open GenBek strict_partial_order strict_linear_order

namespace Mbek

/-!
## R1: the search stays inside the last piece

For `L = pre ++ μ :: P` with every entry of `P` above `μ`, and `μ < q`, the
parent search on `L` is the parent search on `P`, shifted, where "no parent"
in `P` becomes the separator `μ`.
-/

section
variable {α : Type} [LT α] [strict_linear_order α] [DecidableEq α] [DecidableLT α]

theorem drop_length_add' (l₁ l₂ : List α) (i : Nat) : (l₁ ++ l₂).drop (l₁.length + i) = l₂.drop i := by
  induction l₁ with
  | nil => simp
  | cons a l ih => rw [List.length_cons, show l.length + 1 + i = (l.length + i) + 1 by omega]; exact ih

theorem option_bind_map {β γ : Type} (o : Option Nat) (g : Nat → Option β) (f : β → γ) :
    (o.bind (fun k => (g k).map f)) = (o.bind g).map f := by
  cases o <;> rfl

theorem find?_congr' {β : Type} (p q : β → Bool) : ∀ l : List β, (∀ x ∈ l, p x = q x) →
    l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.find?_cons, h a List.mem_cons_self]
      cases q a with
      | true => rfl
      | false => exact find?_congr' p q l (fun x hx => h x (List.mem_cons_of_mem a hx))

variable (pre P : List α) (μ : α)

theorem r1_drop_off (j : Nat) : (pre ++ μ :: P).drop (pre.length + 1 + j) = P.drop j := by
  have := drop_length_add' (pre ++ [μ]) P j
  simpa using this

theorem r1_drop_sep : (pre ++ μ :: P).drop pre.length = μ :: P := by
  have := drop_length_add' pre (μ :: P) 0
  simpa using this

theorem r1_get_off (j : Nat) : (pre ++ μ :: P)[pre.length + 1 + j]? = P[j]? := by
  rw [List.getElem?_append_right (by omega)]
  simp only [show pre.length + 1 + j - pre.length = j + 1 by omega, List.getElem?_cons_succ]

theorem r1_get_sep : (pre ++ μ :: P)[pre.length]? = some μ := by
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

variable {pre P μ}

theorem r1_parent (hP : ∀ x ∈ P, μ < x) (hPne : P ≠ []) : ∀ k, (∀ k' < k, gParent P k' ≠ none) →
    gParent (pre ++ μ :: P) k =
      match gParent P k with
      | none => some pre.length
      | some j => some (pre.length + 1 + j) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [gParent_zero, gParent_zero]
      have hlen : P.length ≠ 0 := fun h => hPne (List.eq_nil_of_length_eq_zero h)
      simp only [List.length_append, List.length_cons]
      rw [if_neg (by omega), if_neg hlen]
      congr 1; omega
  | succ k ih =>
      intro hk
      have hPk : gParent P k ≠ none := hk k (Nat.lt_succ_self k)
      obtain ⟨j, hj⟩ : ∃ j, gParent P k = some j := by
        cases h : gParent P k with
        | none => exact absurd h hPk
        | some j => exact ⟨j, rfl⟩
      have hL := ih (fun k' hk' => hk k' (Nat.lt_succ_of_lt hk'))
      rw [hj] at hL
      simp only at hL
      rw [gParent_succ, hL, gParent_succ, hj]
      simp only
      rw [lastIdx_add]
      have hjP : j < P.length := gParent_lt_length hj
      have hcongr : lastIdx (fun j' => decide ((pre ++ μ :: P).drop (pre.length + 1 + j') <
            (pre ++ μ :: P).drop (pre.length + 1 + j))) j =
          lastIdx (fun i => decide (P.drop i < P.drop j)) j := by
        apply lastIdx_congr
        intro i _
        rw [r1_drop_off, r1_drop_off]
      rw [hcongr]
      cases lastIdx (fun i => decide (P.drop i < P.drop j)) j with
      | some j' => rfl
      | none =>
          simp only [lastIdx]
          have hlt : μ :: P < P.drop j := by
            rw [List.drop_eq_getElem_cons hjP]
            exact List.Lex.rel (hP _ (List.getElem_mem hjP))
          have hc : decide ((pre ++ μ :: P).drop pre.length <
              (pre ++ μ :: P).drop (pre.length + 1 + j)) = true := by
            rw [r1_drop_sep, r1_drop_off]; simp [hlt]
          rw [if_pos hc]

theorem r1_uncle (hP : ∀ x ∈ P, μ < x) (hPne : P ≠ []) (x' : Nat) : ∀ k,
    (k = 0 ∨ ∃ j, gParent P (k - 1) = some j ∧
      gParent (pre ++ μ :: P) (k - 1) = some (pre.length + 1 + j)) →
    gUncle (pre ++ μ :: P) (pre.length + 1 + x') k = (gUncle P x' k).map (pre.length + 1 + ·) := by
  intro k hk
  cases k with
  | zero =>
      rw [gUncle_zero, gUncle_zero]
      have hlen : (pre ++ μ :: P).length = pre.length + 1 + P.length := by simp; omega
      rw [hlen, firstIdx_shift _ _ (fun i hi => by simp; omega)]
      congr 1
      apply firstIdx_congr
      intro i _
      simp
  | succ k =>
      rcases hk with hk | ⟨j, hPj, hLj⟩
      · cases hk
      · simp only [Nat.add_sub_cancel] at hPj hLj
        rw [gUncle_succ, gUncle_succ, hPj, hLj]
        simp only
        rw [firstIdx_shift _ _ (fun i hi => by simp; omega)]
        congr 1
        apply firstIdx_congr
        intro i _
        rw [r1_drop_off, r1_drop_off]
        simp

theorem r1_relatives (hP : ∀ x ∈ P, μ < x) (hPne : P ≠ []) : ∀ n x', 1 ≤ n →
    (∀ k < n, gParent P k ≠ none) →
    gRelatives (pre ++ μ :: P) (pre.length + 1 + x') n =
      (gRelatives P x' n).map (pre.length + 1 + ·) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro x' hn hk
      match n, hn with
      | 1, _ => rfl
      | n' + 2, _ =>
          simp only [gRelatives]
          have hPn' : gParent P n' ≠ none := hk n' (by omega)
          obtain ⟨j, hj⟩ : ∃ j, gParent P n' = some j := by
            cases h : gParent P n' with
            | none => exact absurd h hPn'
            | some j => exact ⟨j, rfl⟩
          have hLj := r1_parent (pre := pre) hP hPne n' (fun k' hk' => hk k' (by omega))
          rw [hj] at hLj
          rw [r1_uncle hP hPne x' (n' + 1) (Or.inr ⟨j, by simpa using hj, by simpa using hLj⟩)]
          cases gUncle P x' (n' + 1) with
          | none => rfl
          | some u =>
              simp only [Option.map_some]
              exact ih (n' + 1) (by omega) u (by omega) (fun k' hk' => hk k' (by omega))

theorem r1_relatives_zero (x' : Nat) :
    gRelatives (pre ++ μ :: P) (pre.length + 1 + x') 0 =
      match gRelatives P x' 0 with
      | none => some pre.length
      | some r => some (pre.length + 1 + r) := by
  cases x' with
  | zero => simp [gRelatives]
  | succ x' => rfl

theorem r1_seg (hP : ∀ x ∈ P, μ < x) (hPne : P ≠ []) (k : Nat) (hk1 : 1 ≤ k)
    (hk : ∀ k' ≤ k, gParent P k' ≠ none) :
    gSeg (pre ++ μ :: P) k = gSeg P k := by
  obtain ⟨j, hj⟩ : ∃ j, gParent P k = some j := by
    cases h : gParent P k with
    | none => exact absurd h (hk k (Nat.le_refl _))
    | some j => exact ⟨j, rfl⟩
  obtain ⟨j', hj'⟩ : ∃ j', gParent P (k - 1) = some j' := by
    cases h : gParent P (k - 1) with
    | none => exact absurd h (hk (k - 1) (by omega))
    | some j' => exact ⟨j', rfl⟩
  have hLj := r1_parent (pre := pre) hP hPne k (fun k' hk' => hk k' (by omega))
  have hLj' := r1_parent (pre := pre) hP hPne (k - 1) (fun k' hk' => hk k' (by omega))
  rw [hj] at hLj
  rw [hj'] at hLj'
  simp only at hLj hLj'
  unfold gSeg
  rw [hLj, hLj', hj, hj']
  simp only [Option.getD_some]
  rw [r1_drop_off]
  congr 1
  omega

theorem r1_scan (hP : ∀ x ∈ P, μ < x) (hPne : P ≠ []) (pm' limit s : Nat) (hls : limit ≤ s)
    (hpar : ∀ k' ≤ s, gParent P k' ≠ none) :
    gScan (pre ++ μ :: P) (pre.length + 1 + pm') limit =
      (gScan P pm' limit).map (pre.length + 1 + ·) := by
  unfold gScan
  have hmem : ∀ k ∈ (List.range limit).drop 1, 1 ≤ k ∧ k < limit := by
    intro k hk
    have h1 := List.mem_range.mp (List.mem_of_mem_drop hk)
    refine ⟨?_, h1⟩
    rw [List.mem_iff_getElem] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    simp
  rw [find?_congr' _ (fun k => decide (P.drop pm' < gSeg P k)) _ (fun k hk => by
    rw [r1_drop_off, r1_seg hP hPne k (hmem k hk).1 (fun k' hk' => hpar k' (by
      have := (hmem k hk).2; omega))])]
  cases hfind : List.find? (fun k => decide (P.drop pm' < gSeg P k)) ((List.range limit).drop 1) with
  | none => rfl
  | some k =>
      have hk' := List.mem_of_find?_eq_some hfind
      simp only [Option.bind_some]
      exact r1_relatives hP hPne (k + 1) pm' (by omega)
        (fun k' hk'' => hpar k' (by have := (hmem k hk').2; omega))

theorem r1_go (hP : ∀ x ∈ P, μ < x) (hPne : P ≠ []) (q : α) (hq : μ < q) (m : Nat) :
    ∀ f s, s ≤ m → m - s < f → (∀ k < s, gParent P k ≠ none) →
    gGo m (pre ++ μ :: P) q f s =
      match gGo m P q f s with
      | none => some pre.length
      | some j => some (pre.length + 1 + j) := by
  intro f
  induction f with
  | zero => intro s hs hf; omega
  | succ f ih =>
      intro s hs hf hpar
      have hLs := r1_parent (pre := pre) hP hPne s hpar
      simp only [gGo]
      cases hPs : gParent P s with
      | none =>
          rw [hPs] at hLs
          simp only at hLs
          rw [hLs]
          simp only
          have hlt : ltAt (pre ++ μ :: P) pre.length q = true := by
            unfold ltAt; rw [r1_get_sep]; simp [hq]
          rw [if_pos hlt]
      | some j =>
          rw [hPs] at hLs
          simp only at hLs
          rw [hLs]
          simp only
          have hlt : ltAt (pre ++ μ :: P) (pre.length + 1 + j) q = ltAt P j q := by
            unfold ltAt; rw [r1_get_off]
          rw [hlt]
          have hpar' : ∀ k' ≤ s, gParent P k' ≠ none := by
            intro k' hk'
            rcases Nat.lt_or_eq_of_le hk' with hk' | rfl
            · exact hpar k' hk'
            · rw [hPs]; simp
          split
          · rfl
          · rw [r1_scan hP hPne j (min (m - 1) s) s (Nat.min_le_right _ _) hpar']
            cases hsc : gScan P j (min (m - 1) s) with
            | some r => rfl
            | none =>
                simp only [Option.map_none]
                by_cases hsm : s = m
                · rw [if_pos hsm, if_pos hsm]
                  subst hsm
                  cases s with
                  | zero =>
                      rw [show pre.length + 1 + j = pre.length + 1 + j from rfl, r1_relatives_zero]
                  | succ s' =>
                      rw [r1_relatives hP hPne (s' + 1) j (by omega) hpar]
                      cases hr : gRelatives P j (s' + 1) with
                      | none => exact absurd hr (gRelatives_ne_none P (s' + 1) j (by omega) hPs)
                      | some r => rfl
                · rw [if_neg hsm, if_neg hsm]
                  exact ih (s + 1) (by omega) (by omega) (fun k hk => hpar' k (by omega))

theorem r1_tp (hP : ∀ x ∈ P, μ < x) (hPne : P ≠ []) (q : α) (hq : μ < q) (m : Nat) :
    gTP m (pre ++ μ :: P) q =
      match gTP m P q with
      | none => some pre.length
      | some j => some (pre.length + 1 + j) :=
  r1_go hP hPne q hq m (m + 1) 0 (Nat.zero_le _) (by omega) (fun k hk => by omega)

theorem dropLast_r1 (hPne : P ≠ []) : (pre ++ μ :: P).dropLast = pre ++ μ :: P.dropLast := by
  rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
  cases P with
  | nil => exact absurd rfl hPne
  | cons a P => simp

theorem repeat_succ_gen {β : Type} (n : Nat) (xs : List β) :
    List.repeat (n + 1) xs = xs ++ List.repeat n xs := by
  simp [List.repeat, List.replicate_succ]

/-- R1 for expansions. -/
theorem r1_expand (hP : ∀ x ∈ P, μ < x) (hPne : P ≠ []) (q : α) (hq : μ < q) (m n : Nat) :
    gExpand m (pre ++ μ :: P) q n = pre ++ μ :: gExpand m P q n := by
  unfold gExpand
  rw [r1_tp hP hPne q hq m, dropLast_r1 hPne]
  have hbase : (pre ++ μ :: P.dropLast) ++ [q] = pre ++ μ :: (P.dropLast ++ [q]) := by simp
  rw [hbase]
  cases gTP m P q with
  | none =>
      simp only
      have hd : (pre ++ μ :: (P.dropLast ++ [q])).drop (pre.length + 1) = P.dropLast ++ [q] := by
        have := r1_drop_off pre (P.dropLast ++ [q]) μ 0
        simpa using this
      rw [hd, repeat_succ_gen]
      simp
  | some j =>
      simp only
      have hd : (pre ++ μ :: (P.dropLast ++ [q])).drop (pre.length + 1 + j + 1) =
          (P.dropLast ++ [q]).drop (j + 1) := by
        rw [show pre.length + 1 + j + 1 = pre.length + 1 + (j + 1) by omega, r1_drop_off]
      rw [hd]
      simp

end

/-!
## Separator positions in `joinS μ Ps`
-/

/-! ### Sparse index lemmas -/

theorem lastIdx_eq_some_of (p : Nat → Bool) (n i : Nat) (hi : i < n) (hp : p i = true)
    (hmax : ∀ j, i < j → j < n → p j = false) : lastIdx p n = some i := by
  induction n with
  | zero => exfalso; omega
  | succ n ih =>
      simp only [lastIdx]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi' | rfl
      · rw [if_neg (by simp [hmax n hi' (Nat.lt_succ_self n)])]
        exact ih hi' (fun j hj hjn => hmax j hj (Nat.lt_succ_of_lt hjn))
      · rw [if_pos hp]

/-- Index search along a strictly increasing enumeration. -/
theorem lastIdx_sparse (P Q : Nat → Bool) (f : Nat → Nat) :
    ∀ n, (∀ a b, a < b → b ≤ n → f a < f b) →
      (∀ i, i < f n → (P i = true ↔ ∃ j, j < n ∧ i = f j ∧ Q j = true)) →
      lastIdx P (f n) = (lastIdx Q n).map f := by
  intro n
  induction n with
  | zero =>
      intro _ h
      rw [(lastIdx_none_iff P _).mpr (fun j hj => by
        cases hP : P j with
        | false => rfl
        | true => obtain ⟨j', hj', _⟩ := (h j hj).mp hP; omega)]
      rfl
  | succ n ih =>
      intro hf h
      have hfn := hf n (n + 1) (Nat.lt_succ_self n) (Nat.le_refl _)
      simp only [lastIdx]
      by_cases hQ : Q n = true
      · rw [if_pos hQ]
        apply lastIdx_eq_some_of _ _ _ hfn ((h (f n) hfn).mpr ⟨n, Nat.lt_succ_self n, rfl, hQ⟩)
        intro j hj hjn
        cases hP : P j with
        | false => rfl
        | true =>
            obtain ⟨j', hj', rfl, _⟩ := (h j hjn).mp hP
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj') with hj' | rfl
            · have := hf j' n hj' (by omega); omega
            · omega
      · rw [if_neg hQ]
        have hlow : ∀ i, i < f n → (P i = true ↔ ∃ j, j < n ∧ i = f j ∧ Q j = true) := by
          intro i hi
          rw [h i (Nat.lt_trans hi hfn)]
          constructor
          · rintro ⟨j, hj, rfl, hq⟩
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
            · exact ⟨j, hj, rfl, hq⟩
            · omega
          · rintro ⟨j, hj, rfl, hq⟩
            exact ⟨j, Nat.lt_succ_of_lt hj, rfl, hq⟩
        rw [← ih (fun a b hab hb => hf a b hab (by omega)) hlow]
        have hsplit : f (n + 1) = (f n + 1) + (f (n + 1) - (f n + 1)) := by omega
        rw [hsplit, lastIdx_add]
        rw [(lastIdx_none_iff _ _).mpr (fun j hj => by
          cases hP : P (f n + 1 + j) with
          | false => rfl
          | true =>
              obtain ⟨j', hj', he, _⟩ := (h _ (by omega)).mp hP
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj') with hj' | rfl
              · have := hf j' n hj' (by omega); omega
              · omega)]
        simp only [lastIdx]
        rw [if_neg (by
          cases hP : P (f n) with
          | false => simp
          | true =>
              obtain ⟨j', hj', he, hq⟩ := (h _ hfn).mp hP
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj') with hj' | rfl
              · have := hf j' n hj' (by omega); omega
              · exact absurd hq hQ)]

/-- Index search along a strictly increasing enumeration. -/
theorem firstIdx_sparse (P Q : Nat → Bool) (f : Nat → Nat) :
    ∀ n, (∀ a b, a < b → b ≤ n → f a < f b) →
      (∀ i, i < f n → (P i = true ↔ ∃ j, j < n ∧ i = f j ∧ Q j = true)) →
      firstIdx P (f n) = (firstIdx Q n).map f := by
  intro n hf h
  cases hq : firstIdx Q n with
  | none =>
      rw [(firstIdx_none_iff P _).mpr (fun j hj => by
        cases hP : P j with
        | false => rfl
        | true =>
            obtain ⟨j', hj', rfl, hQ⟩ := (h j hj).mp hP
            have := (firstIdx_none_iff Q n).mp hq j' hj'
            simp [hQ] at this)]
      rfl
  | some j =>
      have hjn := firstIdx_lt Q n j hq
      have hs := firstIdx_spec Q n j hq
      have hfj := hf j n hjn (Nat.le_refl _)
      simp only [Option.map_some]
      apply firstIdx_eq_some_of _ _ _ hfj ((h _ hfj).mpr ⟨j, hjn, rfl, hs.1⟩)
      intro i hi
      cases hP : P i with
      | false => rfl
      | true =>
          obtain ⟨j', hj', rfl, hQ⟩ := (h i (Nat.lt_trans hi hfj)).mp hP
          rcases Nat.lt_trichotomy j' j with hlt | rfl | hgt
          · have := hs.2 j' hlt; simp [hQ] at this
          · omega
          · have := hf j j' hgt (by omega); omega

/-! ### Joining pieces -/

section
variable {α : Type} [LT α] [strict_linear_order α] [DecidableEq α] [DecidableLT α]

theorem take_ne_nil' {β : Type} {l : List β} {j : Nat} (hj1 : 1 ≤ j) (hj : j < l.length) :
    l.take j ≠ [] := by
  intro h; have := congrArg List.length h
  simp only [List.length_take, List.length_nil] at this; omega

theorem drop_ne_nil' {β : Type} {l : List β} {j : Nat} (hj : j < l.length) : l.drop j ≠ [] := by
  intro h; have := congrArg List.length h; simp at this; omega

/-- The position of the separator in front of the piece number `j`. -/
def sepB (μ : α) (Ps : List (List α)) (j : Nat) : Nat := (joinS μ (Ps.take j)).length

theorem joinS_split (μ : α) (Ps : List (List α)) (j : Nat) (hj1 : 1 ≤ j) (hj : j < Ps.length) :
    joinS μ Ps = joinS μ (Ps.take j) ++ μ :: joinS μ (Ps.drop j) := by
  conv => lhs; rw [← List.take_append_drop j Ps]
  exact joinS_append μ _ _ (take_ne_nil' hj1 hj) (drop_ne_nil' hj)

theorem drop_sepB (μ : α) (Ps : List (List α)) (j : Nat) (hj1 : 1 ≤ j) (hj : j < Ps.length) :
    (joinS μ Ps).drop (sepB μ Ps j) = μ :: joinS μ (Ps.drop j) := by
  rw [joinS_split μ Ps j hj1 hj, sepB]
  have := drop_length_add' (joinS μ (Ps.take j)) (μ :: joinS μ (Ps.drop j)) 0
  simpa using this

theorem sepB_zero (μ : α) (Ps : List (List α)) : sepB μ Ps 0 = 0 := by simp [sepB, joinS]

theorem sepB_one (μ : α) (P : List α) (Ps : List (List α)) : sepB μ (P :: Ps) 1 = P.length := by
  simp [sepB, joinS, joinTailS]

theorem sepB_succ (μ : α) (Ps : List (List α)) (j : Nat) (hj1 : 1 ≤ j) (hj : j < Ps.length) :
    sepB μ Ps (j + 1) = sepB μ Ps j + (Ps[j]).length + 1 := by
  unfold sepB
  rw [List.take_succ, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some]
  rw [joinS_append μ _ _ (take_ne_nil' hj1 (by omega)) (by simp)]
  simp [joinS, joinTailS]
  omega

theorem sepB_strictMono (μ : α) (Ps : List (List α)) (h0 : ∀ P, Ps.head? = some P → P ≠ []) :
    ∀ a b, a < b → b < Ps.length → sepB μ Ps a < sepB μ Ps b := by
  intro a b hab hb
  induction b with
  | zero => omega
  | succ b ih =>
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hab) with hab' | rfl
      · have := ih hab' (by omega)
        cases b with
        | zero => omega
        | succ b' => rw [sepB_succ μ Ps (b' + 1) (by omega) (by omega)]; omega
      · cases a with
        | zero =>
            rw [sepB_zero]
            cases Ps with
            | nil => simp at hb
            | cons P Ps =>
                rw [sepB_one]
                have := h0 P rfl
                cases P with
                | nil => exact absurd rfl this
                | cons x P => simp
        | succ a' => rw [sepB_succ μ Ps (a' + 1) (by omega) (by omega)]; omega

theorem length_joinS_last (μ : α) (Ps : List (List α)) (k : Nat) (hk1 : 1 ≤ k)
    (hk : k + 1 = Ps.length) :
    (joinS μ Ps).length = sepB μ Ps k + 1 + (Ps[k]'(by omega)).length := by
  have hdrop : Ps.drop k = [Ps[k]'(by omega)] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
  rw [joinS_split μ Ps k hk1 (by omega), hdrop]
  show (joinS μ (Ps.take k) ++ μ :: (Ps[k] ++ joinTailS μ [])).length =
    (joinS μ (Ps.take k)).length + 1 + _
  simp only [joinTailS, List.append_nil, List.length_append, List.length_cons]
  omega

end

/-!
## R2: a search through separators is a search one level down

Let `L = joinS μ Ps`, where `μ` is the least entry, the pieces `Ps = [P₀, …, Pₖ]`
(`k ≥ 1`) lie above `μ`, the first piece is the largest one and the last piece is
nonempty.  If the last entry of `L` is replaced by `μ`, the parent search of
level `m` on `L` is the parent search of level `m - 1` on the list of pieces,
where the last piece is replaced by its initial part.
-/

section
variable {α : Type} [LT α] [strict_linear_order α] [DecidableEq α] [DecidableLT α]

theorem take_append_take_drop' {β : Type} (l : List β) (a c : Nat) :
    l.take (a + c) = l.take a ++ (l.drop a).take c := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
      cases a with
      | zero => simp
      | succ a => simp [show a + 1 + c = (a + c) + 1 by omega, ih]

theorem joinS_singleton (μ : α) (P : List α) : joinS μ [P] = P := by simp [joinS, joinTailS]

theorem range_drop_one_succ (ll : Nat) (hll : 1 ≤ ll) :
    (List.range (ll + 1)).drop 1 = 1 :: ((List.range ll).drop 1).map (· + 1) := by
  rw [List.range_succ_eq_map]
  simp only [List.drop_succ_cons, List.drop_zero]
  obtain ⟨l', rfl⟩ : ∃ l', ll = l' + 1 := ⟨ll - 1, by omega⟩
  rw [List.range_succ_eq_map]
  simp

/-- The scan of the separator search, for `m ≥ 3`. -/

theorem gScan_small (L : List α) (pm limit : Nat) (h : limit ≤ 1) : gScan L pm limit = none := by
  unfold gScan
  have : (List.range limit).drop 1 = [] := by
    rcases Nat.lt_or_eq_of_le h with h | rfl
    · have : limit = 0 := by omega
      subst this; rfl
    · rfl
  rw [this]; rfl

/-- Hypotheses for R2. -/
structure R2Hyp (μ : α) (Ps : List (List α)) (k : Nat) : Prop where
  hlen : k + 1 = Ps.length
  hk1 : 1 ≤ k
  habove : ∀ P ∈ Ps, AboveL μ P
  hlast : ∀ h : k < Ps.length, Ps[k] ≠ []
  hmax : ∀ h : 0 < Ps.length, ∀ P ∈ Ps, Le P Ps[0]
  hsucc : ∀ i (hi : i + 1 < (joinS μ Ps).length),
    (joinS μ Ps)[i] < (joinS μ Ps)[(joinS μ Ps).length - 1] → (joinS μ Ps)[i] = μ

variable {μ : α} {Ps : List (List α)} {k : Nat}

theorem cons_lt_cons_iff' (a : α) (u v : List α) : (a :: u < a :: v) ↔ u < v := by
  constructor
  · intro h
    cases h with
    | rel h => exact absurd h (irrefl _)
    | cons h => exact h
  · intro h; exact List.Lex.cons h

theorem cons_cons_lt_singleton (a c b : α) (u : List α) : (a :: c :: u < [b]) ↔ a < b := by
  constructor
  · intro h
    cases h with
    | rel h => exact h
    | cons h => exact absurd h List.not_lex_nil
  · intro h; exact List.Lex.rel h

namespace R2Hyp

variable (H : R2Hyp μ Ps k)
include H

theorem k_lt : k < Ps.length := by have := H.hlen; omega

theorem zero_lt : 0 < Ps.length := by have := H.hlen; omega

theorem first_ne : Ps[0]'H.zero_lt ≠ [] := by
  intro h0
  have hle := H.hmax H.zero_lt (Ps[k]'H.k_lt) (List.getElem_mem _)
  rw [h0] at hle
  rcases hle with h | h
  · exact List.not_lex_nil h
  · exact H.hlast H.k_lt h

theorem sepB_mono : ∀ a b, a < b → b ≤ k → sepB μ Ps a < sepB μ Ps b := by
  intro a b hab hb
  apply sepB_strictMono μ Ps _ a b hab (by have := H.hlen; omega)
  intro P hP
  cases Ps with
  | nil => simp at hP
  | cons Q Qs =>
      simp only [List.head?_cons, Option.some.injEq] at hP
      subst hP
      exact H.first_ne

theorem length_L : (joinS μ Ps).length = sepB μ Ps k + 1 + (Ps[k]'H.k_lt).length :=
  length_joinS_last μ Ps k H.hk1 H.hlen

theorem drop_sep (j : Nat) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    (joinS μ Ps).drop (sepB μ Ps j) = μ :: joinS μ (Ps.drop j) :=
  drop_sepB μ Ps j hj1 (by have := H.hlen; omega)

theorem get_sep (j : Nat) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    (joinS μ Ps)[sepB μ Ps j]? = some μ := by
  have h := H.drop_sep j hj1 hjk
  have : ((joinS μ Ps).drop (sepB μ Ps j))[0]? = some μ := by rw [h]; rfl
  rwa [List.getElem?_drop, Nat.add_zero] at this

theorem get_block (j : Nat) (hj1 : 1 ≤ j) (hjk : j ≤ k) (t : Nat)
    (ht : t < (Ps[j]'(by have := H.hlen; omega)).length) :
    (joinS μ Ps)[sepB μ Ps j + 1 + t]? = (Ps[j]'(by have := H.hlen; omega))[t]? := by
  have h := H.drop_sep j hj1 hjk
  have hd : Ps.drop j = Ps[j]'(by have := H.hlen; omega) :: Ps.drop (j + 1) :=
    List.drop_eq_getElem_cons (by have := H.hlen; omega)
  rw [hd] at h
  have : ((joinS μ Ps).drop (sepB μ Ps j))[1 + t]? = (Ps[j]'(by have := H.hlen; omega))[t]? := by
    rw [h, show 1 + t = t + 1 by omega, List.getElem?_cons_succ]
    show (Ps[j]'(by have := H.hlen; omega) ++ joinTailS μ (Ps.drop (j + 1)))[t]? = _
    exact List.getElem?_append_left ht
  rwa [List.getElem?_drop, show sepB μ Ps j + (1 + t) = sepB μ Ps j + 1 + t by omega] at this

theorem get_first (t : Nat) (ht : t < (Ps[0]'H.zero_lt).length) :
    (joinS μ Ps)[t]? = (Ps[0]'H.zero_lt)[t]? := by
  cases Ps with
  | nil => exact absurd H.zero_lt (Nat.lt_irrefl 0)
  | cons P Qs =>
      have ht' : t < P.length := ht
      show (P ++ joinTailS μ Qs)[t]? = P[t]?
      exact List.getElem?_append_left ht'

/-- Every position is a separator position or carries an entry above `μ`. -/
theorem cover (i : Nat) (hi : i < (joinS μ Ps).length) :
    (∃ j, 1 ≤ j ∧ j ≤ k ∧ i = sepB μ Ps j) ∨ (∃ x, (joinS μ Ps)[i]? = some x ∧ μ < x) := by
  have hab : ∀ j (hj : j < Ps.length), ∀ x ∈ Ps[j], μ < x :=
    fun j hj x hx => H.habove _ (List.getElem_mem hj) x hx
  -- by induction over the blocks
  have blocks : ∀ j, 1 ≤ j → j ≤ k → ∀ i, i < sepB μ Ps j →
      (∃ j', 1 ≤ j' ∧ j' ≤ k ∧ i = sepB μ Ps j') ∨ (∃ x, (joinS μ Ps)[i]? = some x ∧ μ < x) := by
    intro j hj1 hjk
    induction j with
    | zero => exfalso; omega
    | succ j ih =>
        intro i hi
        cases j with
        | zero =>
            right
            have hs1 : sepB μ Ps 1 = (Ps[0]'H.zero_lt).length := by
              cases Ps with
              | nil => exact absurd H.zero_lt (Nat.lt_irrefl 0)
              | cons P Qs => exact sepB_one μ P Qs
            rw [hs1] at hi
            refine ⟨_, (H.get_first i hi).trans (List.getElem?_eq_getElem hi), ?_⟩
            exact hab 0 H.zero_lt _ (List.getElem_mem hi)
        | succ j' =>
            have hsucc := sepB_succ μ Ps (j' + 1) (by omega) (by have := H.hlen; omega)
            by_cases hlow : i < sepB μ Ps (j' + 1)
            · exact ih (by omega) (by omega) i hlow
            · by_cases heq : i = sepB μ Ps (j' + 1)
              · exact Or.inl ⟨j' + 1, by omega, by omega, heq⟩
              · right
                have ht : i - sepB μ Ps (j' + 1) - 1 < (Ps[j' + 1]'(by have := H.hlen; omega)).length := by
                  omega
                have hg := H.get_block (j' + 1) (by omega) (by omega) _ ht
                rw [show sepB μ Ps (j' + 1) + 1 + (i - sepB μ Ps (j' + 1) - 1) = i by omega] at hg
                exact ⟨_, hg.trans (List.getElem?_eq_getElem ht), hab _ _ _ (List.getElem_mem ht)⟩
  by_cases hlow : i < sepB μ Ps k
  · exact blocks k H.hk1 (Nat.le_refl _) i hlow
  · by_cases heq : i = sepB μ Ps k
    · exact Or.inl ⟨k, H.hk1, Nat.le_refl _, heq⟩
    · right
      have hlen := H.length_L
      have ht : i - sepB μ Ps k - 1 < (Ps[k]'H.k_lt).length := by omega
      have hg := H.get_block k H.hk1 (Nat.le_refl _) _ ht
      rw [show sepB μ Ps k + 1 + (i - sepB μ Ps k - 1) = i by omega] at hg
      exact ⟨_, hg.trans (List.getElem?_eq_getElem ht), hab _ _ _ (List.getElem_mem ht)⟩

theorem drop_sep_lt_iff (j p : Nat) (hj1 : 1 ≤ j) (hjk : j ≤ k) (hp1 : 1 ≤ p) (hpk : p ≤ k) :
    (joinS μ Ps).drop (sepB μ Ps j) < (joinS μ Ps).drop (sepB μ Ps p) ↔ Ps.drop j < Ps.drop p := by
  rw [H.drop_sep j hj1 hjk, H.drop_sep p hp1 hpk, cons_lt_cons_iff']
  apply joinS_lt_iff (drop_ne_nil' (by have := H.hlen; omega))
    (drop_ne_nil' (by have := H.hlen; omega))
  · intro P hP; exact H.habove P (List.mem_of_mem_drop hP)
  · intro P hP; exact H.habove P (List.mem_of_mem_drop hP)

theorem gParent_L_zero : gParent (joinS μ Ps) 0 = some ((joinS μ Ps).length - 1) := by
  rw [gParent_zero, if_neg (by have := H.length_L; omega)]

theorem drop_last_L : (joinS μ Ps).drop ((joinS μ Ps).length - 1) =
    [(joinS μ Ps)[(joinS μ Ps).length - 1]'(by have := H.length_L; omega)] := by
  rw [List.drop_eq_getElem_cons (by have := H.length_L; omega)]
  rw [List.drop_eq_nil_of_le (by omega)]

theorem drop_lt_last_iff (i : Nat) (hi : i + 1 < (joinS μ Ps).length) :
    (joinS μ Ps).drop i < (joinS μ Ps).drop ((joinS μ Ps).length - 1) ↔
      (joinS μ Ps)[i] < (joinS μ Ps)[(joinS μ Ps).length - 1]'(by omega) := by
  rw [H.drop_last_L, List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
  exact cons_cons_lt_singleton _ _ _ _

/-- The level-one parent of the last entry is the last separator. -/
theorem gParent_L_one : gParent (joinS μ Ps) 1 = some (sepB μ Ps k) := by
  rw [gParent_succ, H.gParent_L_zero]
  simp only
  have hlen := H.length_L
  have hlast_ne := H.hlast H.k_lt
  have hPk : 0 < (Ps[k]'H.k_lt).length := List.length_pos_iff.mpr hlast_ne
  apply lastIdx_eq_some_of _ _ _ (by omega)
  · rw [decide_eq_true_iff, H.drop_lt_last_iff _ (by omega)]
    have hg := H.get_sep k H.hk1 (Nat.le_refl _)
    rw [List.getElem?_eq_getElem (by omega)] at hg
    have hμ : (joinS μ Ps)[sepB μ Ps k]'(by omega) = μ := Option.some.inj hg
    rw [hμ]
    have ht : (Ps[k]'H.k_lt).length - 1 < (Ps[k]'H.k_lt).length := by omega
    have hb := H.get_block k H.hk1 (Nat.le_refl _) _ ht
    rw [show sepB μ Ps k + 1 + ((Ps[k]'H.k_lt).length - 1) = (joinS μ Ps).length - 1 by omega,
      List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem ht] at hb
    rw [Option.some.inj hb]
    exact H.habove _ (List.getElem_mem _) _ (List.getElem_mem _)
  · intro j hj hjn
    rw [decide_eq_false_iff_not, H.drop_lt_last_iff _ (by omega)]
    intro hlt
    have hμ := H.hsucc j (by omega) hlt
    rcases H.cover j (by omega) with ⟨j', hj1', hjk', rfl⟩ | ⟨x, hx, hμx⟩
    · have := H.sepB_mono j' k
      by_cases hjk : j' < k
      · have := this hjk (Nat.le_refl _); omega
      · have : j' = k := by omega
        subst this; omega
    · rw [List.getElem?_eq_getElem (by omega), hμ] at hx
      exact irrefl _ (Option.some.inj hx ▸ hμx)

theorem not_lt_sep_of_above (i : Nat) {x : α} (hx : (joinS μ Ps)[i]? = some x) (hμx : μ < x)
    (r : List α) : ¬ (joinS μ Ps).drop i < μ :: r := by
  have hi : i < (joinS μ Ps).length := by
    rcases Nat.lt_or_ge i (joinS μ Ps).length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hx; cases hx
  rw [List.drop_eq_getElem_cons hi]
  have : (joinS μ Ps)[i] = x := by
    rw [List.getElem?_eq_getElem hi] at hx; exact Option.some.inj hx
  rw [this]
  intro h
  cases h with
  | rel h => exact irrefl _ (strict_partial_order.trans _ _ _ hμx h)
  | cons h => exact irrefl _ hμx

theorem gParent_Ps_zero : gParent Ps 0 = some k := by
  rw [gParent_zero, if_neg (by have := H.hlen; omega)]
  congr 1; have := H.hlen; omega

/-- Invariant of the parents of the letter-level search. -/
def Inv (s p : Nat) : Prop :=
  1 ≤ p ∧ p ≤ k ∧ ((s = 0 ∧ p = k) ∨ (1 ≤ s ∧ p < k ∧ ∃ hp : p < Ps.length, Ps[p] < Ps[0]'H.zero_lt))

end R2Hyp

theorem cons_lt_cons_Le {β : Type} [LT β] {a b : β} {u v : List β} (h : a :: u < b :: v) :
    a < b ∨ a = b := by
  cases h with
  | rel h => exact Or.inl h
  | cons h => exact Or.inr rfl

namespace R2Hyp

variable (H : R2Hyp μ Ps k)
include H

theorem letter_Le (j p : Nat) (hj : j < Ps.length) (hp : p < Ps.length) (h : Ps.drop j < Ps.drop p) :
    Le (Ps[j]'hj) (Ps[p]'hp) := by
  rw [List.drop_eq_getElem_cons hj, List.drop_eq_getElem_cons hp] at h
  exact cons_lt_cons_Le h

theorem letter_lt_last (j : Nat) (hj : j < k) (h : Ps.drop j < Ps.drop k) :
    (Ps[j]'(by have := H.hlen; omega)) < Ps[k]'H.k_lt := by
  have hk' : Ps.drop k = [Ps[k]'H.k_lt] := by
    rw [List.drop_eq_getElem_cons H.k_lt, List.drop_eq_nil_of_le (by have := H.hlen; omega)]
  rw [hk', List.drop_eq_getElem_cons (by have := H.hlen; omega),
    List.drop_eq_getElem_cons (by have := H.hlen; omega)] at h
  exact (cons_cons_lt_singleton _ _ _ _).mp h

theorem letter_zero_false (s p : Nat) (hinv : H.Inv s p) : ¬ Ps.drop 0 < Ps.drop p := by
  intro h
  obtain ⟨hp1, hpk, hcase⟩ := hinv
  have hle := H.letter_Le 0 p H.zero_lt (by have := H.hlen; omega) h
  rcases hcase with ⟨_, rfl⟩ | ⟨_, _, _, hlt⟩
  · have hmk := H.hmax H.zero_lt (Ps[p]'H.k_lt) (List.getElem_mem _)
    have := H.letter_lt_last 0 (by omega) h
    exact not_lt_of_Le hmk this
  · exact not_lt_of_Le hle hlt

theorem parent_step (s p : Nat) (hp : gParent Ps s = some p)
    (hL : gParent (joinS μ Ps) (s + 1) = some (sepB μ Ps p)) (hinv : H.Inv s p) :
    gParent (joinS μ Ps) (s + 2) = (gParent Ps (s + 1)).map (sepB μ Ps) ∧
      ∀ p', gParent Ps (s + 1) = some p' → H.Inv (s + 1) p' := by
  obtain ⟨hp1, hpk, hcase⟩ := hinv
  have hpkL : sepB μ Ps p < (joinS μ Ps).length := by
    have := H.length_L
    rcases Nat.lt_or_eq_of_le hpk with h | rfl
    · have := H.sepB_mono p k h (Nat.le_refl _); omega
    · omega
  have hcorr : ∀ i, i < sepB μ Ps p →
      (decide ((joinS μ Ps).drop i < (joinS μ Ps).drop (sepB μ Ps p)) = true ↔
        ∃ j, j < p ∧ i = sepB μ Ps j ∧ decide (Ps.drop j < Ps.drop p) = true) := by
    intro i hi
    simp only [decide_eq_true_iff]
    constructor
    · intro h
      rcases H.cover i (by omega) with ⟨j, hj1, hjk, rfl⟩ | ⟨x, hx, hμx⟩
      · have hjp : j < p := by
          rcases Nat.lt_or_ge j p with hjp | hjp
          · exact hjp
          · rcases Nat.lt_or_eq_of_le hjp with hjp | rfl
            · have := H.sepB_mono p j hjp hjk; omega
            · omega
        exact ⟨j, hjp, rfl, (H.drop_sep_lt_iff j p hj1 hjk hp1 hpk).mp h⟩
      · rw [H.drop_sep p hp1 hpk] at h
        exact absurd h (H.not_lt_sep_of_above i hx hμx _)
    · rintro ⟨j, hjp, rfl, h⟩
      cases j with
      | zero => exact absurd h (H.letter_zero_false s p ⟨hp1, hpk, hcase⟩)
      | succ j' => exact (H.drop_sep_lt_iff (j' + 1) p (by omega) (by omega) hp1 hpk).mpr h
  refine ⟨?_, ?_⟩
  · rw [gParent_succ (joinS μ Ps) (s + 1), hL, gParent_succ Ps s, hp]
    simp only
    exact lastIdx_sparse _ _ (sepB μ Ps) p (fun a b hab hb => H.sepB_mono a b hab (by omega)) hcorr
  · intro p' hp'
    rw [gParent_succ Ps s, hp] at hp'
    simp only at hp'
    have hlt := lastIdx_lt _ p p' hp'
    have hpred : Ps.drop p' < Ps.drop p := by simpa using (lastIdx_spec _ p p' hp').1
    have hp'1 : 1 ≤ p' := by
      cases p' with
      | zero => exact absurd hpred (H.letter_zero_false s p ⟨hp1, hpk, hcase⟩)
      | succ _ => omega
    refine ⟨hp'1, by omega, Or.inr ⟨by omega, by omega, by have := H.hlen; omega, ?_⟩⟩
    have hle := H.letter_Le p' p (by have := H.hlen; omega) (by have := H.hlen; omega) hpred
    rcases hcase with ⟨_, rfl⟩ | ⟨_, _, _, hpz⟩
    · have hmk := H.hmax H.zero_lt (Ps[p]'H.k_lt) (List.getElem_mem _)
      exact lt_of_lt_of_Le (H.letter_lt_last p' hlt hpred) hmk
    · exact lt_of_Le_of_lt hle hpz

/-- The parents of the two searches correspond. -/
theorem parent_chain : ∀ s, (∀ s' ≤ s, gParent Ps s' ≠ none) →
    ∃ p, gParent Ps s = some p ∧ gParent (joinS μ Ps) (s + 1) = some (sepB μ Ps p) ∧ H.Inv s p := by
  intro s
  induction s with
  | zero =>
      intro _
      exact ⟨k, H.gParent_Ps_zero, H.gParent_L_one, H.hk1, Nat.le_refl _, Or.inl ⟨rfl, rfl⟩⟩
  | succ s ih =>
      intro hs
      obtain ⟨p, hp, hL, hinv⟩ := ih (fun s' hs' => hs s' (by omega))
      have hstep := H.parent_step s p hp hL hinv
      cases hp' : gParent Ps (s + 1) with
      | none => exact absurd hp' (hs (s + 1) (Nat.le_refl _))
      | some p' =>
          rw [hp'] at hstep
          exact ⟨p', rfl, hstep.1, hstep.2 p' rfl⟩

theorem parent_none (s : Nat) (hs : ∀ s' ≤ s, gParent Ps s' ≠ none) (hn : gParent Ps (s + 1) = none) :
    gParent (joinS μ Ps) (s + 2) = none := by
  obtain ⟨p, hp, hL, hinv⟩ := H.parent_chain s hs
  have := (H.parent_step s p hp hL hinv).1
  rw [hn] at this
  exact this

theorem sepB_lt_length (p : Nat) (hpk : p ≤ k) : sepB μ Ps p < (joinS μ Ps).length := by
  have := H.length_L
  rcases Nat.lt_or_eq_of_le hpk with h | rfl
  · have := H.sepB_mono p k h (Nat.le_refl _); omega
  · omega

theorem corr (s p : Nat) (hinv : H.Inv s p) : ∀ i, i < sepB μ Ps p →
    (decide ((joinS μ Ps).drop i < (joinS μ Ps).drop (sepB μ Ps p)) = true ↔
      ∃ j, j < p ∧ i = sepB μ Ps j ∧ decide (Ps.drop j < Ps.drop p) = true) := by
  obtain ⟨hp1, hpk, hcase⟩ := hinv
  have hpkL := H.sepB_lt_length p hpk
  intro i hi
  simp only [decide_eq_true_iff]
  constructor
  · intro h
    rcases H.cover i (by omega) with ⟨j, hj1, hjk, rfl⟩ | ⟨x, hx, hμx⟩
    · have hjp : j < p := by
        rcases Nat.lt_or_ge j p with hjp | hjp
        · exact hjp
        · rcases Nat.lt_or_eq_of_le hjp with hjp | rfl
          · have := H.sepB_mono p j hjp hjk; omega
          · omega
      exact ⟨j, hjp, rfl, (H.drop_sep_lt_iff j p hj1 hjk hp1 hpk).mp h⟩
    · rw [H.drop_sep p hp1 hpk] at h
      exact absurd h (H.not_lt_sep_of_above i hx hμx _)
  · rintro ⟨j, hjp, rfl, h⟩
    cases j with
    | zero => exact absurd h (H.letter_zero_false s p ⟨hp1, hpk, hcase⟩)
    | succ j' => exact (H.drop_sep_lt_iff (j' + 1) p (by omega) (by omega) hp1 hpk).mpr h

theorem get_sep' (j : Nat) (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    (joinS μ Ps)[sepB μ Ps j]'(H.sepB_lt_length j hjk) = μ := by
  have hg := H.get_sep j hj1 hjk
  rw [List.getElem?_eq_getElem (H.sepB_lt_length j hjk)] at hg
  exact Option.some.inj hg

theorem last_above : μ < (joinS μ Ps)[(joinS μ Ps).length - 1]'(by have := H.length_L; omega) := by
  have hlen := H.length_L
  have hPk : 0 < (Ps[k]'H.k_lt).length := List.length_pos_iff.mpr (H.hlast H.k_lt)
  have ht : (Ps[k]'H.k_lt).length - 1 < (Ps[k]'H.k_lt).length := by omega
  have hb := H.get_block k H.hk1 (Nat.le_refl _) _ ht
  rw [show sepB μ Ps k + 1 + ((Ps[k]'H.k_lt).length - 1) = (joinS μ Ps).length - 1 by omega,
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem ht] at hb
  rw [Option.some.inj hb]
  exact H.habove _ (List.getElem_mem _) _ (List.getElem_mem _)

theorem uncle_one (j : Nat) (hj1 : 1 ≤ j) (hjk : j < k) :
    gUncle (joinS μ Ps) (sepB μ Ps j) 1 = some (sepB μ Ps (j + 1)) := by
  rw [gUncle_succ, H.gParent_L_zero]
  simp only
  have hlen := H.length_L
  have hPk : 0 < (Ps[k]'H.k_lt).length := List.length_pos_iff.mpr (H.hlast H.k_lt)
  have hjj := H.sepB_mono j (j + 1) (Nat.lt_succ_self j) (by omega)
  have hj1k : sepB μ Ps (j + 1) ≤ sepB μ Ps k := by
    rcases Nat.lt_or_eq_of_le (show j + 1 ≤ k by omega) with h | h
    · exact Nat.le_of_lt (H.sepB_mono _ _ h (Nat.le_refl _))
    · rw [h]; exact Nat.le_refl _
  apply firstIdx_eq_some_of _ _ _ (by omega)
  · simp only [Bool.and_eq_true, decide_eq_true_iff]
    refine ⟨hjj, ?_⟩
    rw [H.drop_lt_last_iff _ (by omega), H.get_sep' (j + 1) (by omega) (by omega)]
    exact H.last_above
  · intro i hi
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_cases hij : sepB μ Ps j < i
    · right
      rw [H.drop_lt_last_iff _ (by omega)]
      intro hlt
      have hμ := H.hsucc i (by omega) hlt
      rcases H.cover i (by omega) with ⟨j', hj1', hjk', rfl⟩ | ⟨x, hx, hμx⟩
      · rcases Nat.lt_trichotomy j' j with h | rfl | h
        · have := H.sepB_mono j' j h (by omega); omega
        · omega
        · rcases Nat.lt_or_eq_of_le (show j + 1 ≤ j' by omega) with h' | h'
          · have := H.sepB_mono (j + 1) j' h' hjk'; omega
          · subst h'; omega
      · rw [List.getElem?_eq_getElem (by omega), hμ] at hx
        exact irrefl _ (Option.some.inj hx ▸ hμx)
    · left; exact hij

theorem uncle_succ (n p j : Nat) (hp : gParent Ps n = some p)
    (hL : gParent (joinS μ Ps) (n + 1) = some (sepB μ Ps p)) (hinv : H.Inv n p)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    gUncle (joinS μ Ps) (sepB μ Ps j) (n + 2) = (gUncle Ps j (n + 1)).map (sepB μ Ps) := by
  rw [gUncle_succ (joinS μ Ps) _ (n + 1), hL, gUncle_succ Ps j n, hp]
  simp only
  have hinv' := hinv
  obtain ⟨hp1, hpk, _⟩ := hinv'
  apply firstIdx_sparse _ _ (sepB μ Ps) p (fun a b hab hb => H.sepB_mono a b hab (by omega))
  intro i hi
  have hc := H.corr n p hinv i hi
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hc ⊢
  constructor
  · rintro ⟨hji, h⟩
    obtain ⟨j', hj', rfl, h'⟩ := hc.mp h
    refine ⟨j', hj', rfl, ?_, h'⟩
    rcases Nat.lt_or_ge j j' with h'' | h''
    · exact h''
    · rcases Nat.lt_or_eq_of_le h'' with h'' | rfl
      · have := H.sepB_mono j' j h'' hjk; omega
      · omega
  · rintro ⟨j', hj', rfl, hjj', h'⟩
    exact ⟨H.sepB_mono j j' hjj' (by omega), hc.mpr ⟨j', hj', rfl, h'⟩⟩

theorem relatives_zero (j : Nat) (hj1 : 1 ≤ j) :
    gRelatives (joinS μ Ps) (sepB μ Ps j) 1 = (gRelatives Ps j 0).map (fun r => sepB μ Ps (r + 1)) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rfl

theorem relatives_corr : ∀ n j, 1 ≤ n → 1 ≤ j → j < k → (∀ s' < n, gParent Ps s' ≠ none) →
    gRelatives (joinS μ Ps) (sepB μ Ps j) (n + 1) =
      (gRelatives Ps j n).map (fun r => sepB μ Ps (r + 1)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro j hn hj1 hjk hpar
      match n, hn with
      | 1, _ =>
          show (match gUncle (joinS μ Ps) (sepB μ Ps j) 1 with
            | none => none
            | some u => gRelatives (joinS μ Ps) u 1) = _
          rw [H.uncle_one j hj1 hjk]
          rfl
      | n' + 2, _ =>
          show (match gUncle (joinS μ Ps) (sepB μ Ps j) (n' + 2) with
            | none => none
            | some u => gRelatives (joinS μ Ps) u (n' + 2)) =
            (match gUncle Ps j (n' + 1) with
            | none => none
            | some u => gRelatives Ps u (n' + 1)).map _
          obtain ⟨p, hp, hL, hinv⟩ := H.parent_chain n' (fun s' hs' => hpar s' (by omega))
          rw [H.uncle_succ n' p j hp hL hinv hj1 (by omega)]
          cases hu : gUncle Ps j (n' + 1) with
          | none => rfl
          | some u =>
              simp only [Option.map_some]
              have hu' := hu
              rw [gUncle_succ, hp] at hu'
              simp only at hu'
              have hup := firstIdx_lt _ p u hu'
              have hus := (firstIdx_spec _ p u hu').1
              simp only [Bool.and_eq_true, decide_eq_true_iff] at hus
              obtain ⟨_, hpk, _⟩ := hinv
              exact ih (n' + 1) (by omega) u (by omega) (by omega) (by omega)
                (fun s' hs' => hpar s' (by omega))

theorem seg_eq (a b : Nat) (ha1 : 1 ≤ a) (hab : a < b) (hbk : b ≤ k) :
    ((joinS μ Ps).drop (sepB μ Ps a)).take (sepB μ Ps b - sepB μ Ps a) =
      μ :: joinS μ ((Ps.drop a).take (b - a)) := by
  have hlenPs := H.hlen
  rw [H.drop_sep a ha1 (by omega)]
  have hsplit : joinS μ (Ps.drop a) =
      joinS μ ((Ps.drop a).take (b - a)) ++ μ :: joinS μ ((Ps.drop a).drop (b - a)) :=
    joinS_split μ (Ps.drop a) (b - a) (by omega) (by simp; omega)
  have htb : Ps.take b = Ps.take a ++ (Ps.drop a).take (b - a) := by
    rw [← take_append_take_drop', show a + (b - a) = b by omega]
  have hlen : sepB μ Ps b - sepB μ Ps a = 1 + (joinS μ ((Ps.drop a).take (b - a))).length := by
    unfold sepB
    rw [htb, joinS_append μ _ _ (take_ne_nil' ha1 (by omega))
      (take_ne_nil' (by omega) (by simp; omega))]
    simp only [List.length_append, List.length_cons]
    omega
  rw [hsplit, hlen, Nat.add_comm, List.take_succ_cons]
  simp

theorem seg_one :
    ((joinS μ Ps).drop (sepB μ Ps k)).take ((joinS μ Ps).length - 1 - sepB μ Ps k) =
      μ :: (Ps[k]'H.k_lt).dropLast := by
  have hlen := H.length_L
  have hPk : 0 < (Ps[k]'H.k_lt).length := List.length_pos_iff.mpr (H.hlast H.k_lt)
  rw [H.drop_sep k H.hk1 (Nat.le_refl _)]
  have hd : Ps.drop k = [Ps[k]'H.k_lt] := by
    rw [List.drop_eq_getElem_cons H.k_lt, List.drop_eq_nil_of_le (by have := H.hlen; omega)]
  rw [hd, joinS_singleton,
    show (joinS μ Ps).length - 1 - sepB μ Ps k = ((Ps[k]'H.k_lt).length - 1) + 1 by omega,
    List.take_succ_cons, List.dropLast_eq_take]

theorem gSeg_one : gSeg (joinS μ Ps) 1 = μ :: (Ps[k]'H.k_lt).dropLast := by
  unfold gSeg
  rw [H.gParent_L_one, show 1 - 1 = 0 from rfl, H.gParent_L_zero]
  simp only [Option.getD_some]
  exact H.seg_one

theorem gSeg_succ (t : Nat) (hpar : ∀ s' ≤ t + 1, gParent Ps s' ≠ none) :
    gSeg (joinS μ Ps) (t + 2) = μ :: joinS μ (gSeg Ps (t + 1)) ∧ gSeg Ps (t + 1) ≠ [] := by
  obtain ⟨a, ha, haL, hainv⟩ := H.parent_chain (t + 1) hpar
  obtain ⟨b, hb, hbL, hbinv⟩ := H.parent_chain t (fun s' hs' => hpar s' (by omega))
  obtain ⟨b', hb', hab, _⟩ := gParent_succ_lt ha
  rw [hb] at hb'
  cases hb'
  obtain ⟨ha1, hak, _⟩ := hainv
  obtain ⟨hb1, hbk, _⟩ := hbinv
  have hsegPs : gSeg Ps (t + 1) = (Ps.drop a).take (b - a) := by
    unfold gSeg
    rw [ha, show t + 1 - 1 = t by omega, hb]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hsegPs]
    unfold gSeg
    rw [haL, show t + 2 - 1 = t + 1 by omega, hbL]
    simp only [Option.getD_some]
    exact H.seg_eq a b ha1 hab hbk
  · rw [hsegPs]; exact take_ne_nil' (by omega) (by simp; have := H.hlen; omega)

theorem joinS_drop_lt_iff (p : Nat) (hp1 : 1 ≤ p) (hpk : p ≤ k) :
    joinS μ (Ps.drop p) < (Ps[k]'H.k_lt).dropLast ↔ (Ps[p]'(by have := H.hlen; omega)) <
      (Ps[k]'H.k_lt).dropLast := by
  have hlenPs := H.hlen
  rw [List.drop_eq_getElem_cons (by omega)]
  show Ps[p] ++ joinTailS μ (Ps.drop (p + 1)) < _ ↔ _
  have hQ : AboveL μ (Ps[k]'H.k_lt).dropLast := fun x hx =>
    H.habove _ (List.getElem_mem _) x (List.dropLast_subset _ hx)
  have key := above_append_lt_iff (r' := []) (H.habove (Ps[p]'(by omega)) (List.getElem_mem _)) hQ
    (SepStart.joinTailS μ (Ps.drop (p + 1))) (Or.inl rfl)
  rw [List.append_nil] at key
  rw [key]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact h
    · exact absurd h List.not_lex_nil
  · intro h; exact Or.inl h

theorem scan_corr (m s p : Nat) (hm : 3 ≤ m) (hs : 1 ≤ s) (hpar : ∀ s' ≤ s, gParent Ps s' ≠ none)
    (hp : gParent Ps s = some p) (hinv : H.Inv s p) :
    gScan (joinS μ Ps) (sepB μ Ps p) (min (m - 1) (s + 1)) =
      (if ltAt Ps p (Ps[k]'H.k_lt).dropLast then some p
        else gScan Ps p (min (m - 1 - 1) s)).map (fun r => sepB μ Ps (r + 1)) := by
  have hinv' := hinv
  obtain ⟨hp1, hpk, hcase⟩ := hinv'
  have hpk' : p < k := by
    rcases hcase with ⟨h, _⟩ | ⟨_, h, _⟩
    · omega
    · exact h
  unfold gScan
  have hle : min (m - 1) (s + 1) = min (m - 1 - 1) s + 1 := by omega
  rw [hle, range_drop_one_succ (min (m - 1 - 1) s) (by omega), List.find?_cons]
  have hpred1 : decide ((joinS μ Ps).drop (sepB μ Ps p) < gSeg (joinS μ Ps) 1) =
      ltAt Ps p (Ps[k]'H.k_lt).dropLast := by
    rw [H.gSeg_one, H.drop_sep p hp1 hpk]
    unfold ltAt
    rw [List.getElem?_eq_getElem (by have := H.hlen; omega)]
    simp only
    rw [decide_eq_decide, cons_lt_cons_iff', H.joinS_drop_lt_iff p hp1 hpk]
  rw [hpred1]
  cases hlt : ltAt Ps p (Ps[k]'H.k_lt).dropLast with
  | true =>
      simp only [Option.bind_some, ite_true, Option.map_some]
      rw [H.relatives_corr 1 p (Nat.le_refl _) hp1 hpk' (fun s' hs' => hpar s' (by omega))]
      rfl
  | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [find?_map, ← option_bind_map]
      have hfind : List.find? ((fun k' => decide ((joinS μ Ps).drop (sepB μ Ps p) <
            gSeg (joinS μ Ps) k')) ∘ (· + 1)) ((List.range (min (m - 1 - 1) s)).drop 1) =
          List.find? (fun k' => decide (Ps.drop p < gSeg Ps k'))
            ((List.range (min (m - 1 - 1) s)).drop 1) := by
        apply find?_congr'
        intro k'' hk''
        have hk1 : 1 ≤ k'' := by
          rw [List.mem_iff_getElem] at hk''
          obtain ⟨i, hi, rfl⟩ := hk''
          simp
        have hk2 : k'' < min (m - 1 - 1) s := List.mem_range.mp (List.mem_of_mem_drop hk'')
        obtain ⟨t, rfl⟩ : ∃ t, k'' = t + 1 := ⟨k'' - 1, by omega⟩
        have hseg := H.gSeg_succ t (fun s' hs' => hpar s' (by omega))
        simp only [Function.comp]
        rw [hseg.1, H.drop_sep p hp1 hpk, decide_eq_decide, cons_lt_cons_iff']
        exact joinS_lt_iff (drop_ne_nil' (by have := H.hlen; omega)) hseg.2
          (fun P hP => H.habove P (List.mem_of_mem_drop hP))
          (fun P hP => by
            unfold gSeg at hP
            exact H.habove P (List.mem_of_mem_drop (List.mem_of_mem_take hP)))
      rw [hfind]
      cases hf : List.find? (fun k' => decide (Ps.drop p < gSeg Ps k'))
          ((List.range (min (m - 1 - 1) s)).drop 1) with
      | none => rfl
      | some k'' =>
          have hk'' := List.mem_of_find?_eq_some hf
          have hk2 : k'' < min (m - 1 - 1) s := List.mem_range.mp (List.mem_of_mem_drop hk'')
          simp only [Option.bind_some]
          exact H.relatives_corr (k'' + 1) p (by omega) hp1 hpk' (fun s' hs' => hpar s' (by omega))

theorem ltAt_last_false : ltAt Ps k (Ps[k]'H.k_lt).dropLast = false := by
  unfold ltAt
  rw [List.getElem?_eq_getElem H.k_lt]
  simp only [decide_eq_false_iff_not]
  intro h
  have hne := H.hlast H.k_lt
  have hpre : (Ps[k]'H.k_lt).dropLast < Ps[k]'H.k_lt := by
    conv => rhs; rw [← List.dropLast_concat_getLast hne]
    exact list_prefix_lt' _ _ []
  exact list_lt_irrefl' _ (list_lt_trans' h hpre)

theorem ltAt_sep (p : Nat) (hp1 : 1 ≤ p) (hpk : p ≤ k) : ltAt (joinS μ Ps) (sepB μ Ps p) μ = false := by
  unfold ltAt
  rw [H.get_sep p hp1 hpk]
  simp [irrefl]

theorem go_corr (m : Nat) (hm : 1 ≤ m) : ∀ f s, s + 1 ≤ m → m - (s + 1) < f →
    (∀ s' < s, gParent Ps s' ≠ none) →
    gGo m (joinS μ Ps) μ f (s + 1) =
      (gGo (m - 1) Ps (Ps[k]'H.k_lt).dropLast f s).map (fun r => sepB μ Ps (r + 1)) := by
  intro f
  induction f with
  | zero => intro s hs hf; omega
  | succ f ih =>
      intro s hs hf hpar
      simp only [gGo]
      cases hPs : gParent Ps s with
      | none =>
          have hs1 : 1 ≤ s := by
            rcases Nat.eq_zero_or_pos s with rfl | h
            · rw [H.gParent_Ps_zero] at hPs; cases hPs
            · exact h
          obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
          rw [H.parent_none s' (fun t ht => hpar t (by omega)) hPs]
          rfl
      | some p =>
          have hpar' : ∀ s' ≤ s, gParent Ps s' ≠ none := by
            intro s' hs'
            rcases Nat.lt_or_eq_of_le hs' with h | rfl
            · exact hpar s' h
            · rw [hPs]; simp
          obtain ⟨p', hp', hL, hinv⟩ := H.parent_chain s hpar'
          rw [hPs] at hp'
          cases hp'
          rw [hL]
          simp only
          have hinv' := hinv
          obtain ⟨hp1, hpk, hcase⟩ := hinv'
          rw [H.ltAt_sep p hp1 hpk]
          simp only [Bool.false_eq_true, ite_false]
          rcases Nat.eq_zero_or_pos s with rfl | hs1
          · -- level one of the separator search
            have hpk0 : p = k := by
              rcases hcase with ⟨_, h⟩ | ⟨h, _⟩
              · exact h
              · omega
            subst hpk0
            rw [gScan_small _ _ _ (by omega), H.ltAt_last_false]
            simp only [Bool.false_eq_true, ite_false]
            rw [gScan_small _ _ _ (by omega)]
            simp only
            by_cases hm1 : 0 + 1 = m
            · rw [if_pos hm1, if_pos (by omega), ← hm1]
              rw [show 1 - 1 = 0 from rfl, ← H.relatives_zero p hp1]
            · rw [if_neg hm1, if_neg (by omega)]
              exact ih 1 (by omega) (by omega) (fun t ht => by
                have : t = 0 := by omega
                subst this; rw [H.gParent_Ps_zero]; simp)
          · have hpk' : p < k := by
              rcases hcase with ⟨h, _⟩ | ⟨_, h, _⟩
              · omega
              · exact h
            rcases Nat.lt_or_ge m 3 with hm3 | hm3
            · -- `m = 2`, `s = 1`
              have hm2 : m = 2 := by omega
              have hs1' : s = 1 := by omega
              subst hm2 hs1'
              rw [gScan_small _ _ _ (by omega)]
              simp only
              simp only [ite_true]
              rw [H.relatives_corr 1 p (Nat.le_refl _) hp1 hpk' (fun t ht => hpar' t (by omega))]
              cases hlt : ltAt Ps p (Ps[k]'H.k_lt).dropLast with
              | true => rfl
              | false =>
                  simp only [Bool.false_eq_true, ite_false]
                  rw [gScan_small _ _ _ (by omega)]
            · rw [H.scan_corr m s p hm3 hs1 hpar' hPs hinv]
              cases hlt : ltAt Ps p (Ps[k]'H.k_lt).dropLast with
              | true => rfl
              | false =>
                  simp only [Bool.false_eq_true, ite_false]
                  cases hsc : gScan Ps p (min (m - 1 - 1) s) with
                  | some r => rfl
                  | none =>
                      simp only [Option.map_none]
                      by_cases hsm : s + 1 = m
                      · rw [if_pos hsm, if_pos (by omega)]
                        rw [show m = (m - 1) + 1 by omega,
                          H.relatives_corr (m - 1) p (by omega) hp1 hpk'
                            (fun t ht => hpar' t (by omega))]
                        simp
                      · rw [if_neg hsm, if_neg (by omega)]
                        exact ih (s + 1) (by omega) (by omega) (fun t ht => hpar' t (by omega))

/-- R2 for the true parent. -/
theorem tp_corr (m : Nat) (hm : 1 ≤ m) :
    gTP m (joinS μ Ps) μ =
      (gTP (m - 1) Ps (Ps[k]'H.k_lt).dropLast).map (fun r => sepB μ Ps (r + 1)) := by
  unfold gTP
  have hlast : ltAt (joinS μ Ps) ((joinS μ Ps).length - 1) μ = false := by
    unfold ltAt
    rw [List.getElem?_eq_getElem (by have := H.length_L; omega)]
    simp only [decide_eq_false_iff_not]
    exact not_lt_of_Le (Or.inl H.last_above)
  have h0 : gGo m (joinS μ Ps) μ (m + 1) 0 = gGo m (joinS μ Ps) μ m 1 := by
    rw [gGo, H.gParent_L_zero]
    simp only
    rw [hlast]
    simp only [Bool.false_eq_true, ite_false]
    rw [gScan_small _ _ _ (by omega)]
    simp only
    rw [if_neg (by omega)]
  rw [h0, show m - 1 + 1 = m by omega]
  exact H.go_corr m hm m 0 (by omega) (by omega) (fun t ht => by omega)

theorem dropLast_L :
    (joinS μ Ps).dropLast ++ [μ] = joinS μ ((Ps.dropLast ++ [(Ps[k]'H.k_lt).dropLast]) ++ [[]]) := by
  have hlenPs := H.hlen
  have hPs : Ps = Ps.take k ++ [Ps[k]'H.k_lt] := by
    conv => lhs; rw [← List.take_append_drop k Ps]
    rw [List.drop_eq_getElem_cons H.k_lt, List.drop_eq_nil_of_le (by omega)]
  have hdl : Ps.dropLast = Ps.take k := by
    rw [List.dropLast_eq_take, show Ps.length - 1 = k by omega]
  have htk : Ps.take k ≠ [] := take_ne_nil' H.hk1 H.k_lt
  have hne := H.hlast H.k_lt
  rw [hdl]
  conv => lhs; rw [hPs]
  rw [joinS_append μ _ _ htk (by simp), joinS_singleton, List.append_assoc,
    joinS_append μ _ _ htk (by simp)]
  rw [List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _)]
  have hc : (μ :: Ps[k]).dropLast = μ :: (Ps[k]).dropLast := by
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    rw [hx]; simp
  rw [hc]
  simp [joinS, joinTailS]

end R2Hyp

theorem repeat_succ'_gen {β : Type} (n : Nat) (xs : List β) :
    List.repeat (n + 1) xs = List.repeat n xs ++ xs := by
  induction n with
  | zero => simp [List.repeat]
  | succ n ih => rw [repeat_succ_gen, ih, ← List.append_assoc, ← repeat_succ_gen, ih]

theorem repeat_nil_gen {β : Type} : ∀ n, List.repeat n ([] : List β) = []
  | 0 => rfl
  | n + 1 => by rw [repeat_succ_gen, repeat_nil_gen n]; rfl

theorem joinS_snoc_nil (μ : α) (B : List (List α)) (hB : B ≠ []) :
    joinS μ (B ++ [[]]) = joinS μ B ++ [μ] := by
  rw [joinS_append μ _ _ hB (by simp)]
  simp [joinS, joinTailS]

theorem joinS_repeat_nil (μ : α) (B : List (List α)) (hB : B ≠ []) : ∀ n,
    joinS μ (List.repeat (n + 1) B ++ [[]]) = List.repeat (n + 1) (joinS μ B ++ [μ]) := by
  intro n
  induction n with
  | zero =>
      rw [show List.repeat 1 B = B by simp [List.repeat],
        show List.repeat 1 (joinS μ B ++ [μ]) = joinS μ B ++ [μ] by simp [List.repeat]]
      exact joinS_snoc_nil μ B hB
  | succ n ih =>
      rw [repeat_succ_gen (n + 1) B, repeat_succ_gen (n + 1) (joinS μ B ++ [μ]), ← ih,
        List.append_assoc, joinS_append μ _ _ hB (by simp)]
      simp

theorem joinS_append_repeat_nil (μ : α) (A D : List (List α)) (hA : A ≠ []) (hD : D ≠ []) : ∀ n,
    joinS μ (A ++ List.repeat n D ++ [[]]) =
      joinS μ (A ++ [[]]) ++ List.repeat n (joinS μ (D ++ [[]])) := by
  intro n
  induction n with
  | zero => simp [List.repeat]
  | succ n ih =>
      rw [repeat_succ'_gen, repeat_succ'_gen, ← List.append_assoc,
        ← List.append_assoc (joinS μ (A ++ [[]])), ← ih]
      have hAR : A ++ List.repeat n D ≠ [] := by simp [hA]
      rw [List.append_assoc (A ++ List.repeat n D) D [[]],
        joinS_append μ _ _ hAR (by simp), joinS_snoc_nil μ _ hAR]
      simp

namespace R2Hyp

variable (H : R2Hyp μ Ps k)
include H

/-- R2 for expansions. -/
theorem expand_corr (m n : Nat) (hm : 1 ≤ m) :
    gExpand m (joinS μ Ps) μ n =
      joinS μ (gExpand (m - 1) Ps ((Ps[k]'H.k_lt).dropLast) n ++ [[]]) := by
  have hlenPs := H.hlen
  unfold gExpand
  rw [H.tp_corr m hm, H.dropLast_L]
  have hBlen : (Ps.dropLast ++ [(Ps[k]'H.k_lt).dropLast]).length = k + 1 := by simp; omega
  have hBtake : ∀ j, j < k → ((Ps.dropLast ++ [(Ps[k]'H.k_lt).dropLast]) ++ [[]]).take (j + 1) =
      Ps.take (j + 1) := by
    intro j hjk
    rw [List.take_append_of_le_length (by simp; omega),
      List.take_append_of_le_length (by simp; omega), List.dropLast_eq_take, List.take_take]
    congr 1; omega
  have hBL : (joinS μ ((Ps.dropLast ++ [(Ps[k]'H.k_lt).dropLast]) ++ [[]])).length =
      (joinS μ Ps).length := by
    rw [← H.dropLast_L]
    simp only [List.length_append, List.length_dropLast, List.length_singleton]
    have := H.length_L; omega
  generalize Ps.dropLast ++ [(Ps[k]'H.k_lt).dropLast] = B at hBlen hBtake hBL ⊢
  have hBne : B ≠ [] := by
    intro h; rw [h] at hBlen; exact absurd hBlen (by simp only [List.length_nil]; omega)
  cases gTP (m - 1) Ps (Ps[k]'H.k_lt).dropLast with
  | none =>
      simp only [Option.map_none]
      rw [joinS_repeat_nil μ B hBne n, joinS_snoc_nil μ B hBne]
  | some j =>
      simp only [Option.map_some]
      rcases Nat.lt_or_ge j k with hjk | hjk
      · have htake := hBtake j hjk
        have hsep : sepB μ Ps (j + 1) = sepB μ (B ++ [[]]) (j + 1) := by
          unfold sepB; rw [htake]
        have hdrop := drop_sepB μ (B ++ [[]]) (j + 1) (by omega) (by simp; omega)
        rw [hsep, show sepB μ (B ++ [[]]) (j + 1) + 1 = sepB μ (B ++ [[]]) (j + 1) + 1 from rfl,
          ← List.drop_drop, hdrop]
        simp only [List.drop_succ_cons, List.drop_zero]
        rw [List.drop_append_of_le_length (by omega)]
        exact (joinS_append_repeat_nil μ B (B.drop (j + 1)) hBne
          (drop_ne_nil' (by omega)) n).symm
      · have hsep : sepB μ Ps (j + 1) = (joinS μ Ps).length := by
          unfold sepB; rw [List.take_of_length_le (by omega)]
        rw [hsep, List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (as := B) (by omega),
          repeat_nil_gen, repeat_nil_gen, List.append_nil, List.append_nil]

end R2Hyp

end

end Mbek
