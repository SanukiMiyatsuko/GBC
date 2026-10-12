import Mbekworm.Sequence.Reductions

/-!
# Well-foundedness of `OT M`

Expansions preserve the normal forms `NF A m`, hence every element of `OT M` is a
normal form, and the lexicographic order on `OT M` is well-founded.
-/

set_option linter.unusedSectionVars false

open GenBek strict_partial_order strict_linear_order

namespace Mbek

/-!
## Expansions preserve the normal forms

For every level `m` and every alphabet, if the last entry `ℓ` of a normal form is
replaced by `q < ℓ` such that no entry lies strictly between `q` and `ℓ`, then
the expansion is again a normal form of level `m`.  On `ℕ` this shows
`OT M ⊆ {xs | NF Nat M xs}`.
-/

section
variable {α : Type} [LT α] [strict_linear_order α] [DecidableEq α] [DecidableLT α]

theorem mem_repeat {β : Type} {z : β} : ∀ {n : Nat} {xs : List β}, z ∈ List.repeat n xs → z ∈ xs
  | 0, _, h => by simp [List.repeat] at h
  | n + 1, xs, h => by
      rw [repeat_succ_gen] at h
      rcases List.mem_append.mp h with h | h
      · exact h
      · exact mem_repeat h

theorem mem_gExpand (m : Nat) (L : List α) (q : α) (n : Nat) :
    ∀ z ∈ gExpand m L q n, z ∈ L.dropLast ++ [q] := by
  intro z hz
  unfold gExpand at hz
  split at hz
  · exact mem_repeat hz
  · rcases List.mem_append.mp hz with hz | hz
    · exact hz
    · exact List.mem_of_mem_drop (mem_repeat hz)

theorem gExpand_prefix (m : Nat) (L : List α) (q : α) (n : Nat) :
    ∃ r, gExpand m L q n = (L.dropLast ++ [q]) ++ r := by
  unfold gExpand
  split
  · exact ⟨List.repeat n (L.dropLast ++ [q]), repeat_succ_gen n _⟩
  · exact ⟨_, rfl⟩

theorem gExpand_lt (m : Nat) (A : List α) (ℓ q : α) (n : Nat) (hq : q < ℓ) :
    gExpand m (A ++ [ℓ]) q n < A ++ [ℓ] := by
  obtain ⟨r, hr⟩ := gExpand_prefix m (A ++ [ℓ]) q n
  rw [hr, List.dropLast_concat, List.append_assoc, List.singleton_append]
  exact list_append_lt_left A (List.Lex.rel hq)

theorem gExpand_ne_nil (m : Nat) (L : List α) (q : α) (n : Nat) : gExpand m L q n ≠ [] := by
  obtain ⟨r, hr⟩ := gExpand_prefix m L q n
  rw [hr]; simp

/-- "No entry strictly between `q` and `ℓ`". -/
def SuccCond (A : List α) (ℓ q : α) : Prop := ∀ x ∈ A, x < ℓ ↔ Le x q

theorem succ_lift {ℓ : α} {p Q : List α} (hp : ∀ x ∈ p, Le ℓ x) : p < Q ++ [ℓ] ↔ Le p Q := by
  induction p generalizing Q with
  | nil =>
      constructor
      · intro _; exact nil_Le_list Q
      · intro _; cases Q with
        | nil => exact List.Lex.nil
        | cons _ _ => exact List.Lex.nil
  | cons a p ih =>
      have ha := hp a List.mem_cons_self
      have hp' : ∀ x ∈ p, Le ℓ x := fun x hx => hp x (List.mem_cons_of_mem a hx)
      cases Q with
      | nil =>
          constructor
          · intro h
            cases h with
            | rel h => exact absurd h (not_lt_of_Le ha)
            | cons h => exact absurd h List.not_lex_nil
          · intro h
            rcases h with h | h
            · exact absurd h List.not_lex_nil
            · cases h
      | cons b Q =>
          constructor
          · intro h
            cases h with
            | rel h => exact Or.inl (List.Lex.rel h)
            | cons h =>
                rcases (ih hp').mp h with h' | h'
                · exact Or.inl (List.Lex.cons h')
                · exact Or.inr (h' ▸ rfl)
          · intro h
            rcases h with h | h
            · cases h with
              | rel h => exact List.Lex.rel h
              | cons h => exact List.Lex.cons ((ih hp').mpr (Or.inl h))
            · cases h
              exact List.Lex.cons ((ih hp').mpr (Or.inr rfl))

theorem sepPieces_repeat_free (q : α) (A : List α) (hq : q ∉ A) : ∀ n,
    sepPieces q (List.repeat (n + 1) (A ++ [q])) = List.replicate (n + 1) A ++ [[]] := by
  intro n
  induction n with
  | zero =>
      rw [show List.repeat 1 (A ++ [q]) = A ++ [q] by simp [List.repeat], sepPieces_snoc_eq,
        sepPieces_free q A hq]
      rfl
  | succ n ih =>
      rw [repeat_succ_gen, List.append_assoc, List.singleton_append, sepPieces_append_sep q A hq, ih]
      simp [List.replicate_succ]

end

section
variable {α : Type} [LT α] [strict_linear_order α] [DecidableEq α] [DecidableLT α]

theorem cons_lt_single (a b : α) (rest : List α) : a :: rest < [b] ↔ a < b ∨ (a = b ∧ rest < []) := by
  constructor
  · intro h
    cases h with
    | rel h => exact Or.inl h
    | cons h => exact Or.inr ⟨rfl, h⟩
  · rintro (h | ⟨rfl, h⟩)
    · exact List.Lex.rel h
    · exact List.Lex.cons h

theorem drop_lt_last_snoc (A : List α) (ℓ : α) (i : Nat) (hi : i < A.length) :
    (A ++ [ℓ]).drop i < (A ++ [ℓ]).drop A.length ↔ A[i] < ℓ := by
  rw [List.drop_append_of_le_length (Nat.le_of_lt hi), List.drop_eq_getElem_cons hi]
  have hA : (A ++ [ℓ]).drop A.length = [ℓ] := by simp
  rw [hA, List.cons_append, cons_lt_single]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact h
    · exact absurd h List.not_lex_nil
  · intro h; exact Or.inl h

theorem ltAt_last (A : List α) (ℓ q : α) (hq : q < ℓ) : ltAt (A ++ [ℓ]) A.length q = false := by
  unfold ltAt
  simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  simp only [decide_eq_false_iff_not]
  exact not_lt_of_Le (Or.inl hq)

theorem gParent_snoc_zero (A : List α) (ℓ : α) : gParent (A ++ [ℓ]) 0 = some A.length := by
  rw [gParent_zero]; simp

theorem gTP_zero_snoc (A : List α) (ℓ q : α) (hq : q < ℓ) :
    gTP 0 (A ++ [ℓ]) q = (match A.length with
      | 0 => none
      | a + 1 => some a) := by
  unfold gTP
  rw [gGo, gParent_snoc_zero]
  simp only
  rw [ltAt_last A ℓ q hq]
  simp only [Bool.false_eq_true, ite_false]
  rw [gScan_small _ _ _ (by omega)]
  simp only [ite_true]
  rfl

theorem gTP_R3 (m : Nat) (A : List α) (ℓ q : α) (hq : q < ℓ) (hs : SuccCond A ℓ q)
    (hR3 : ∀ x ∈ A, ¬ Le x q) : gTP (m + 1) (A ++ [ℓ]) q = none := by
  unfold gTP
  rw [gGo, gParent_snoc_zero]
  simp only
  rw [ltAt_last A ℓ q hq]
  simp only [Bool.false_eq_true, ite_false]
  rw [gScan_small _ _ _ (by omega)]
  simp only
  rw [if_neg (by omega), gGo, gParent_succ, gParent_snoc_zero]
  simp only
  rw [(lastIdx_none_iff _ _).mpr]
  intro j hj
  rw [decide_eq_false_iff_not, drop_lt_last_snoc A ℓ j hj, hs _ (List.getElem_mem hj)]
  exact hR3 _ (List.getElem_mem hj)

theorem repeat_single {β : Type} (q : β) : ∀ j, List.repeat j [q] = List.replicate j q
  | 0 => rfl
  | j + 1 => by rw [repeat_succ_gen, repeat_single q j]; rfl

theorem mem_joinS' {μ z : α} {Qs : List (List α)} (h : z ∈ joinS μ Qs) :
    z = μ ∨ ∃ Q ∈ Qs, z ∈ Q := by
  by_cases hz : z = μ
  · exact Or.inl hz
  · exact Or.inr (mem_joinS h hz)

theorem mu_mem_joinS (μ : α) (Qs : List (List α)) (h : 2 ≤ Qs.length) : μ ∈ joinS μ Qs := by
  rw [joinS_split μ Qs 1 (Nat.le_refl _) (by omega)]
  simp

theorem NF_joinS {m : Nat} {μ : α} {Qs : List (List α)} (h2 : 2 ≤ Qs.length)
    (habove : ∀ Q ∈ Qs, AboveL μ Q) (h1 : NF (List α) m Qs) (hQ : ∀ Q ∈ Qs, NF α (m + 1) Q) :
    NF α (m + 1) (joinS μ Qs) := by
  have hmin : AllGe μ (joinS μ Qs) := fun z hz => by
    rcases mem_joinS' hz with rfl | ⟨Q, hQ, hzQ⟩
    · exact Le.refl _
    · exact Or.inl (habove Q hQ z hzQ)
  rw [NF_succ_iff, md_of_min (mu_mem_joinS μ _ h2) hmin, sepPieces_joinS μ _
    (fun e => by rw [e, List.length_nil] at h2; omega) (fun Q hQ hm => irrefl _ (habove Q hQ μ hm))]
  exact ⟨h1, hQ⟩

/-- **The shapes of an expansion** at level `m + 1`: R3 (no parent), or the worm is cut at its
least letter `μ ≤ q` and the expansion is R1 (`μ < q`, inside the last piece) or R2 (`μ = q`,
one level down, on the pieces). -/
theorem expand_cases (m : Nat) {A : List α} {ℓ q : α} (h : NF α (m + 1) (A ++ [ℓ])) (hq : q < ℓ)
    (hs : SuccCond A ℓ q) :
    ((∀ x ∈ A, ¬ Le x q) ∧
      ∀ n, gExpand (m + 1) (A ++ [ℓ]) q n = joinS q (List.replicate (n + 1) A ++ [[]])) ∨
    ∃ μ Ps P', μ ∈ A ∧ AllGe μ (A ++ [ℓ]) ∧ Ps ≠ [] ∧ (∀ Q ∈ Ps ++ [P' ++ [ℓ]], AboveL μ Q) ∧
      A ++ [ℓ] = joinS μ (Ps ++ [P' ++ [ℓ]]) ∧ (∀ Q ∈ Ps ++ [P'], ∀ z ∈ Q, z ∈ A) ∧
      P'.length < A.length ∧ NF (List α) m (Ps ++ [P' ++ [ℓ]]) ∧
      (∀ Q ∈ Ps ++ [P' ++ [ℓ]], NF α (m + 1) Q) ∧
      ((μ < q ∧ ∀ n, gExpand (m + 1) (A ++ [ℓ]) q n =
          joinS μ (Ps ++ [gExpand (m + 1) (P' ++ [ℓ]) q n])) ∨
        (μ = q ∧ ∀ n, gExpand (m + 1) (A ++ [ℓ]) q n =
          joinS μ (gExpand m (Ps ++ [P' ++ [ℓ]]) P' n ++ [[]]))) := by
  by_cases hR : ∃ x ∈ A, (x < q ∨ x = q)
  · right
    obtain ⟨x, hxA, hxq⟩ := hR
    obtain ⟨μ, hμ⟩ := min?_isSome (show A ++ [ℓ] ≠ [] by simp)
    have hsL := min?_spec hμ
    have hμq : Le μ q := Le.trans (hsL.2 x (List.mem_append_left _ hxA)) hxq
    have hμℓ : μ < ℓ := lt_of_Le_of_lt hμq hq
    have hμA : μ ∈ A := (List.mem_append.mp hsL.1).resolve_right
      (fun h' => irrefl _ (List.mem_singleton.mp h' ▸ hμℓ))
    have hnf := (NF_succ_iff m (A ++ [ℓ])).mp h
    rw [md_eq hμ] at hnf
    obtain ⟨Ps, P', hA, hL⟩ := sepPieces_snoc_ne μ A ℓ (fun e => irrefl _ (e ▸ hμℓ))
    rw [hL] at hnf
    have hPs : Ps ≠ [] := by
      rintro rfl
      rw [List.nil_append] at hA
      have hAj := joinS_sepPieces μ A
      rw [hA, joinS_singleton] at hAj
      exact (mem_of_mem_sepPieces μ A P' (by rw [hA]; simp) μ (hAj ▸ hμA)).2 rfl
    have habove : ∀ Q ∈ Ps ++ [P' ++ [ℓ]], AboveL μ Q := hL ▸ above_of_mem_sepPieces hsL.2
    have hLeq : A ++ [ℓ] = joinS μ (Ps ++ [P' ++ [ℓ]]) := by rw [← hL, joinS_sepPieces]
    refine ⟨μ, Ps, P', hμA, hsL.2, hPs, habove, hLeq,
      fun Q hQ z hz => (mem_of_mem_sepPieces μ A Q (by rw [hA]; exact hQ) z hz).1,
      length_lt_of_mem_sepPieces μ A hμA P' (by rw [hA]; simp), hnf.1, hnf.2, ?_⟩
    rcases hμq with hμq | rfl
    · refine Or.inl ⟨hμq, fun n => ?_⟩
      rw [hLeq, joinS_append μ _ _ hPs (by simp), joinS_append μ _ _ hPs (by simp), joinS_singleton,
        joinS_singleton, r1_expand (habove _ (by simp)) (by simp) q hμq (m + 1) n]
    · refine Or.inr ⟨rfl, fun n => ?_⟩
      have hH : R2Hyp μ (Ps ++ [P' ++ [ℓ]]) Ps.length := by
        refine ⟨by simp, List.length_pos_iff.mpr hPs, habove, fun _ => by simp, ?_, ?_⟩
        · intro h0 Q hQ
          obtain ⟨Q0, Qs, rfl⟩ := List.exists_cons_of_ne_nil hPs
          exact NF_head_max m Q0 _ hnf.1 Q hQ
        · intro i hi hlt
          have hiA : i < A.length := by rw [← hLeq] at hi; simp at hi; omega
          simp only [← hLeq] at hlt ⊢
          rw [show (A ++ [ℓ])[(A ++ [ℓ]).length - 1] = ℓ by simp, List.getElem_append_left hiA] at hlt
          rw [List.getElem_append_left hiA]
          rcases (hs _ (List.getElem_mem hiA)).mp hlt with h1 | h1
          · exact absurd h1 (not_lt_of_Le (hsL.2 _ (List.mem_append_left _ (List.getElem_mem hiA))))
          · exact h1
      rw [hLeq, hH.expand_corr (m + 1) n (by omega),
        show (Ps ++ [P' ++ [ℓ]])[Ps.length]'hH.k_lt = P' ++ [ℓ] by simp, List.dropLast_concat,
        Nat.add_sub_cancel]
  · left
    have hR3 : ∀ x ∈ A, ¬ Le x q := fun x hx hle => hR ⟨x, hx, hle⟩
    refine ⟨hR3, fun n => ?_⟩
    unfold gExpand
    rw [gTP_R3 m A ℓ q hq hs hR3, List.dropLast_concat]
    simp only
    rw [← sepPieces_repeat_free q A (fun hqA => hR3 q hqA (Le.refl q)) n, joinS_sepPieces]

end

/-- Expansions preserve the normal forms. -/
theorem gExpand_NF (m : Nat) : ∀ {α : Type} [LT α] [strict_linear_order α] [DecidableEq α]
    [DecidableLT α] (A : List α) (ℓ q : α) (n : Nat), NF α m (A ++ [ℓ]) → q < ℓ →
    SuccCond A ℓ q → NF α m (gExpand m (A ++ [ℓ]) q n) := by
  induction m with
  | zero =>
      intro α _ _ _ _ A ℓ q n h hq _
      unfold gExpand
      rw [gTP_zero_snoc A ℓ q hq, List.dropLast_concat]
      have h' : List.Pairwise (fun x y : α => y < x ∨ y = x) (A ++ [ℓ]) := h
      cases hl : A.length with
      | zero =>
          rw [List.eq_nil_of_length_eq_zero hl]
          simp only [List.nil_append]
          rw [repeat_single]
          exact NF_replicate 0 q (n + 1)
      | succ a =>
          simp only
          rw [show (A ++ [q]).drop (a + 1) = [q] by rw [← hl]; simp, repeat_single]
          show List.Pairwise _ (A ++ [q] ++ List.replicate n q)
          rw [List.append_assoc, List.singleton_append, ← List.replicate_succ, List.pairwise_append]
          refine ⟨(List.pairwise_append.mp h').1, List.pairwise_replicate.mpr (Or.inr (Or.inr rfl)),
            fun x hx y hy => ?_⟩
          rw [(List.mem_replicate.mp hy).2]
          exact Or.inl (lt_of_lt_of_Le hq ((List.pairwise_append.mp h').2.2 x hx ℓ (by simp)))
  | succ m ih =>
      intro α _ _ _ _
      suffices H : ∀ (k : Nat) (A : List α) (ℓ q : α) (n : Nat), A.length ≤ k →
          NF α (m + 1) (A ++ [ℓ]) → q < ℓ → SuccCond A ℓ q →
          NF α (m + 1) (gExpand (m + 1) (A ++ [ℓ]) q n) from
        fun A ℓ q n h hq hs => H A.length A ℓ q n (Nat.le_refl _) h hq hs
      intro k
      induction k using Nat.strongRecOn with
      | ind k ihk =>
      intro A ℓ q n hk h hq hs
      have hnil : ∀ Qs, NF α (m + 1) ([] : List α) → ∀ Q ∈ Qs ++ [[]], (Q ∈ Qs → NF α (m + 1) Q) →
          NF α (m + 1) Q := fun Qs h0 Q hQ hQs => by
        rcases List.mem_append.mp hQ with hQ | hQ
        · exact hQs hQ
        · rw [List.mem_singleton.mp hQ]; exact h0
      rcases expand_cases m h hq hs with ⟨hR3, hexp⟩ |
        ⟨μ, Ps, P', _, _, hPs, habove, _, hmemA, hlenP', hnf1, hnf2, (⟨hμq, hexp⟩ | ⟨rfl, hexp⟩)⟩
      · rw [hexp]
        refine NF_joinS (by simp) (fun Q hQ z hz => ?_)
          (NF_appmin m _ [] (NF_replicate m A (n + 1)) (fun z _ => nil_Le_list z))
          (fun Q hQ => hnil _ (NF_nil _) Q hQ (fun hQ => by
            rw [(List.mem_replicate.mp hQ).2]; exact (NF_prefix_dec (m + 1)).1 A ℓ h))
        rcases List.mem_append.mp hQ with hQ | hQ
        · rw [(List.mem_replicate.mp hQ).2] at hz
          exact (Le_of_not_lt (fun h' => hR3 z hz (Or.inl h'))).resolve_right
            (fun e => hR3 z hz (Or.inr e.symm))
        · rw [List.mem_singleton.mp hQ] at hz; cases hz
      · rw [hexp n]
        have hE := ihk P'.length (by omega) P' ℓ q n (Nat.le_refl _) (hnf2 _ (by simp)) hq
          (fun z hz => hs z (hmemA P' (by simp) z hz))
        have hEab : AboveL μ (gExpand (m + 1) (P' ++ [ℓ]) q n) := fun z hz => by
          have := mem_gExpand (m + 1) (P' ++ [ℓ]) q n z hz
          rw [List.dropLast_concat] at this
          rcases List.mem_append.mp this with h' | h'
          · exact habove (P' ++ [ℓ]) (by simp) z (List.mem_append_left _ h')
          · rw [List.mem_singleton.mp h']; exact hμq
        refine NF_joinS (by simp; exact List.length_pos_iff.mpr hPs) (fun Q hQ => ?_)
          ((NF_prefix_dec m).2 Ps (P' ++ [ℓ]) _ hnf1 (gExpand_lt _ _ _ _ _ hq)) (fun Q hQ => ?_)
        · rcases List.mem_append.mp hQ with hQ | hQ
          · exact habove Q (List.mem_append_left _ hQ)
          · rw [List.mem_singleton.mp hQ]; exact hEab
        · rcases List.mem_append.mp hQ with hQ | hQ
          · exact hnf2 Q (List.mem_append_left _ hQ)
          · rw [List.mem_singleton.mp hQ]; exact hE
      · rw [hexp n]
        have hsucc' : SuccCond Ps (P' ++ [ℓ]) P' := fun Q hQ => succ_lift fun z hz =>
          Le_of_not_lt fun hzℓ => by
            have hzA := hmemA Q (List.mem_append_left _ hQ) z hz
            have hμz := habove Q (List.mem_append_left _ hQ) z hz
            rcases (hs z hzA).mp hzℓ with h' | h'
            · exact irrefl _ (strict_partial_order.trans _ _ _ h' hμz)
            · exact irrefl _ (h' ▸ hμz)
        have hgE := ih (α := List α) Ps (P' ++ [ℓ]) P' n hnf1
          (by simpa using list_prefix_lt' P' ℓ []) hsucc'
        have hmemE : ∀ Q ∈ gExpand m (Ps ++ [P' ++ [ℓ]]) P' n, Q ∈ Ps ∨ Q = P' := fun Q hQ => by
          have := mem_gExpand m _ _ n Q hQ
          rw [List.dropLast_concat] at this
          exact (List.mem_append.mp this).imp id List.mem_singleton.mp
        have h2 : 2 ≤ (gExpand m (Ps ++ [P' ++ [ℓ]]) P' n ++ [[]]).length := by
          have := List.length_pos_iff.mpr (gExpand_ne_nil m (Ps ++ [P' ++ [ℓ]]) P' n)
          simp; omega
        refine NF_joinS h2 (fun Q hQ => ?_) (NF_appmin m _ [] hgE (fun z _ => nil_Le_list z))
          (fun Q hQ => hnil _ (NF_nil _) Q hQ (fun hQ => ?_))
        · rcases List.mem_append.mp hQ with hQ | hQ
          · rcases hmemE Q hQ with h' | rfl
            · exact habove Q (List.mem_append_left _ h')
            · exact fun z hz => habove (Q ++ [ℓ]) (by simp) z (List.mem_append_left _ hz)
          · rw [List.mem_singleton.mp hQ]; intro z hz; cases hz
        · rcases hmemE Q hQ with h' | rfl
          · exact hnf2 Q (List.mem_append_left _ h')
          · exact (NF_prefix_dec (m + 1)).1 Q ℓ (hnf2 _ (by simp))

/-!
## The lexicographic order on `OT M` is a well-order, for every `M`

Every element of `OT M` is a normal form `NF Nat M` (expansions preserve normal
forms), and the normal forms are well-founded by `generalizedBeklemishev`.
-/

/-- Every element of `OT M` is a generalized Beklemishev normal form of level `M`. -/
theorem isOT_NF (M : Nat) (s : List Nat) (h : isOT M s) : NF Nat M s := by
  induction h with
  | base k => exact NF_singleton M k
  | step s _ n ih =>
      rcases list_eq_nil_or_append s with rfl | ⟨t, c, rfl⟩
      · have : expand M [] n = [] := by simp [expand]
        rw [this]; exact NF_nil M
      · cases c with
        | zero =>
            rw [expand_append_zero]
            exact (NF_prefix_dec M).1 t 0 ih
        | succ c =>
            rw [expand_eq_gExpand]
            apply gExpand_NF M t (c + 1) c n ih (Nat.lt_succ_self c)
            intro x _
            show x < c + 1 ↔ x < c ∨ x = c
            exact ⟨fun h => Nat.lt_or_eq_of_le (Nat.le_of_lt_succ h),
              fun h => h.elim (fun h => Nat.lt_succ_of_lt h) (fun h => h ▸ Nat.lt_succ_self _)⟩

theorem nat_lt_wf : WellFounded (fun x y : Nat => x < y) := Nat.lt_wfRel.wf

/-- **Well-foundedness**: for every `M`, the lexicographic order on `OT M` is well-founded. -/
theorem OT_wellFounded (M : Nat) : WellFounded (fun a b : MbekRank1.Mbek M => a.val < b.val) := by
  have hNF := generalizedBeklemishev Nat nat_lt_wf M
  exact InvImage.wf (fun a : MbekRank1.Mbek M => (⟨a.val, isOT_NF M a.val a.property⟩ :
    {xs : List Nat // NF Nat M xs})) hNF

end Mbek
