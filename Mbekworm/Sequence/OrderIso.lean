import Mbekworm.Sequence.SemCofinal
import Mbekworm.Sequence.OTWellFounded

/-!
# The order isomorphism `OT M ≅ {NF1 below the bound}` for every `M`

For `M ≥ 1` the translation is `trM M xs = o M (xs.map ofNat)`; it is strictly
monotone and normal-form valued (`Sem.facts`), adds `1` when a `0` is appended
(`succLast`), its expansions are cofinal (`cofW`), and the starting points
`[k]` climb to `φ_{M-1}(0, 0) = T.phi000 (M - 1)` (the fixed-point limit `fl`).
For `M = 0` the translation `translation0` is used.
-/

open T GenBek Mbek

namespace Sem

/-! ### Lists of naturals -/

theorem ofNat_add_one : ∀ c : Nat, T.ofNat (c + 1) = T.add (T.ofNat c) one
  | 0 => rfl
  | c + 1 => by
      show P 0 Z (T.ofNat (c + 1)) = T.add (P 0 Z (T.ofNat c)) one
      rw [add_P, ← ofNat_add_one c]

theorem embOn_ofNat (S : List Nat) : EmbOn T.ofNat S := fun _ _ _ _ h => ofNat_strict_mono h

theorem goodW_ofNat {M : Nat} {s : List Nat} (h : NF Nat M s) : GoodW M (s.map T.ofNat) :=
  ⟨fun y hy => by obtain ⟨x, _, rfl⟩ := List.mem_map.mp hy; exact good_ofNat x,
    NF_map M T.ofNat s h (fun _ _ _ _ hxy => ofNat_strict_mono hxy)⟩

theorem goodW_OT {M : Nat} {s : List Nat} (h : isOT M s) : GoodW M (s.map T.ofNat) :=
  goodW_ofNat (isOT_NF M s h)

theorem map_ofNat_lt {s t : List Nat} (h : s < t) : s.map T.ofNat < t.map T.ofNat :=
  map_lt_map (fun _ _ _ _ hxy => ofNat_strict_mono hxy) (fun _ _ _ _ e => T.ofNat_injective e) h

theorem trM_lt {M : Nat} {s t : List Nat} (hs : isOT M s) (ht : isOT M t) (h : s < t) :
    trM M s < trM M t :=
  o_mono (goodW_OT hs) (goodW_OT ht) (map_ofNat_lt h)

theorem trM_inj {M : Nat} {s t : List Nat} (hs : isOT M s) (ht : isOT M t)
    (h : trM M s = trM M t) : s = t := by
  rcases List.strictLinearTotal s t with h' | h' | h'
  · exact absurd h (ne_of_lt'' (trM_lt hs ht h'))
  · exact absurd h.symm (ne_of_lt'' (trM_lt ht hs h'))
  · exact h'

theorem trM_succ {M : Nat} {s : List Nat} (h : isOT M (s ++ [0])) :
    trM M (s ++ [0]) = T.add (trM M s) one := by
  have hw := goodW_OT h
  rw [List.map_append, List.map_cons, List.map_nil] at hw
  show o M ((s ++ [0]).map T.ofNat) = _
  rw [List.map_append, List.map_cons, List.map_nil]
  exact succLast M hw

theorem expand_map (M : Nat) (s : List Nat) (c n : Nat) :
    (expand M (s ++ [c + 1]) n).map T.ofNat =
      gExpand M (s.map T.ofNat ++ [T.add (T.ofNat c) one]) (T.ofNat c) n := by
  rw [expand_eq_gExpand, ← gExpand_map (embOn_ofNat ((s ++ [c + 1]) ++ [c]))
    (fun x hx => List.mem_append_left _ hx) (List.mem_append_right _ (List.mem_singleton_self c)) M n,
    List.map_append, List.map_cons, List.map_nil, ofNat_add_one]

theorem trM_expand_lt {M : Nat} {s : List Nat} {c : Nat} (h : isOT M (s ++ [c + 1])) (n : Nat) :
    trM M (expand M (s ++ [c + 1]) n) < trM M (s ++ [c + 1]) :=
  trM_lt (isOT_expand h n) h (expand_append_succ_lt M s c n)

theorem trM_expand_le {M : Nat} {s : List Nat} (h : isOT M s) (n : Nat) :
    trM M (expand M s n) ≤ trM M s := by
  rcases list_eq_nil_or_append s with rfl | ⟨t, c, rfl⟩
  · have : expand M [] n = [] := by simp [expand]
    rw [this]; exact le_refl' _
  · cases c with
    | zero =>
        rw [expand_append_zero, trM_succ h]
        exact le_of_lt' (lt_add_of_ne _ nofun)
    | succ c => exact le_of_lt' (trM_expand_lt h n)

/-! ### The bound for `M ≥ 1` -/

theorem copies_T : ∀ j, T.copies 1 Om j = copies Om j
  | 0 => rfl
  | j + 1 => by
      show P 1 Om (T.copies 1 Om j) = P 1 Om (copies Om j)
      rw [copies_T j]

theorem boundM_eq (n : Nat) : boundM (n + 1) = Eom (n + 1) one one := by
  have hone : one ≠ Z := by intro e; cases e
  cases n with
  | zero =>
      rw [Eom_succ_ne 0 hone, if_neg hone, if_pos rfl]
      rfl
  | succ n =>
      show P 0 (P 1 (T.mul (P 1 Om Z) (T.ofNat (n + 1))) Z) Z = _
      rw [T.mul_ofNat_eq_copies, copies_T, Eom_succ_ne (n + 1) hone, if_neg hone,
        if_neg (Nat.succ_ne_zero n)]
      exact (phi_succ_Z_Z n).symm

theorem boundM_zero : boundM 0 = omegaPow (P 0 one Z) := rfl

theorem ofNat_lt_omega : ∀ k, T.ofNat k < P 0 one Z
  | 0 => Z_lt_P' _ _ _
  | _ + 1 => T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)

theorem rep0_Z : ∀ k, rep0 Z k = T.ofNat k
  | 0 => rfl
  | k + 1 => by
      show P 0 Z (rep0 Z k) = P 0 Z (T.ofNat k)
      rw [rep0_Z k]

theorem trM_single_lt : ∀ M k, trM M [k] < boundM M
  | 0, k => by
    show o 0 [T.ofNat k] < _
    rw [o_single_zero, boundM_zero]
    exact omegaPow_lt_omegaPow (good_ofNat k) (good_omegaPow good_one) (ofNat_lt_omega k)
  | n + 1, k => by
      show o (n + 1) [T.ofNat k] < _
      have hb : one < boundM (n + 1) :=
        T.Lt.p_mid _ _ _ _ _ (Z_lt_P' _ _ _)
      rw [o_single, ← rep0_Z, E_rep0, logA_Z]
      rw [boundM_eq] at hb ⊢
      induction k with
      | zero => exact hb
      | succ k ih =>
          show Eom (n + 1) Z (iterT (Eom (n + 1) Z) one k) < _
          have hg : ∀ j, Good (iterT (Eom (n + 1) Z) one j) := by
            intro j
            induction j with
            | zero => exact good_one
            | succ j ihj => exact Eom_good (facts n) good_Z ihj
          have hEg : Good (Eom (n + 1) one one) := Eom_good (facts n) good_one good_one
          have := Eom_lt (facts n) good_Z (hg k) hEg ih
          rwa [Eom_fix (facts n) good_Z good_one good_one (Z_lt_P' _ _ _)] at this

theorem fin_of_lt_omega : ∀ {δ : T}, Good δ → δ < P 0 one Z → ∃ k, δ = T.ofNat k
  | Z, _, _ => ⟨0, rfl⟩
  | P i c r, hδ, hlt => by
      have hi := hδ.idx; subst hi
      have hc : c = Z := by
        rcases lt_inv _ _ _ _ _ _ hlt with h | ⟨_, h⟩ | ⟨_, _, h⟩
        · exact absurd h (Nat.lt_irrefl 0)
        · cases c with
          | Z => rfl
          | P j c' r' =>
              rcases lt_inv _ _ _ _ _ _ h with h' | ⟨_, h'⟩ | ⟨_, _, h'⟩
              · exact absurd h' (Nat.not_lt_zero _)
              · exact absurd h' (not_lt_Z' _)
              · exact absurd h' (not_lt_Z' _)
        · exact absurd h (not_lt_Z' _)
      subst hc
      obtain ⟨k, hk⟩ := fin_of_lt_omega hδ.tail (lt_tr (tail_lt_of_desc hδ.desc) hlt)
      exact ⟨k + 1, by rw [hk]; rfl⟩

theorem top_cofinal_M : ∀ M (b : T), T.isNF1 b → b < boundM M → ∃ k, b ≤ trM M [k]
  | 0, b, hb, hlt => by
    rw [boundM_zero] at hlt
    have hω : Good (P 0 one Z) := good_omegaPow good_one
    obtain ⟨⟨δ, hδ, hδlt⟩, hbδ⟩ := omegaPow_cont hω (lim_P0 nofun)
      (s := fun y : Below (P 0 one Z) => y.1) (fun y => y.2.1) (cof_below hω) b hb hlt
    obtain ⟨k, rfl⟩ := fin_of_lt_omega hδ hδlt
    exact ⟨k, by show b ≤ o 0 [T.ofNat k]; rw [o_single_zero]; exact hbδ⟩
  | n + 1, b, hb, hlt => by
      rw [boundM_eq] at hlt
      have h0 : Eom (n + 1) one Z = Z := Eom_succ_Zarg n one
      obtain ⟨⟨δ, hδ, hδlt⟩, hbδ⟩ := fl n good_one nofun good_Z b hb hlt
      change b ≤ E (n + 1) δ (T.add (Eom (n + 1) one Z) one) at hbδ
      rw [h0] at hbδ
      obtain ⟨k, rfl⟩ := fin_of_lt_omega hδ hδlt
      refine ⟨k, ?_⟩
      show b ≤ o (n + 1) [T.ofNat k]
      rw [o_single]
      exact hbδ

theorem trM_lt_bound (M : Nat) {s : List Nat} (h : isOT M s) : trM M s < boundM M := by
  induction h with
  | base k => exact trM_single_lt M k
  | step s hs m ih => exact lt_of_le_of_lt' (trM_expand_le hs m) ih

/-! ### The translation -/

/-- **The translation of `OT M`** into normal forms below `boundM M`. -/
def translation (M : Nat) : Translation M (boundM M) where
  tr := trM M
  tr_nil := o_nil _
  tr_isNF1 _ hs := (o_good (goodW_OT hs)).nf
  tr_lt_bound _ hs := trM_lt_bound M hs
  tr_inj _ _ hs ht h := trM_inj hs ht h
  tr_succ_lt _ hs := by
    rw [trM_succ hs]; exact lt_add_of_ne _ nofun
  tr_succ_le _ b hs _ hlt := by
    rw [trM_succ hs] at hlt; exact lt_add_one_le _ b hlt
  tr_expand_lt _ _ m hs := trM_expand_lt hs m
  tr_expand_cofinal s c b hs hb hlt := by
    have hw := goodW_OT hs
    have e : (s ++ [c + 1]).map T.ofNat = s.map T.ofNat ++ [T.add (T.ofNat c) one] := by
      rw [List.map_append, List.map_cons, List.map_nil, ofNat_add_one]
    rw [e] at hw
    have hlt' : b < o M (s.map T.ofNat ++ [T.add (T.ofNat c) one]) := by
      rw [← e]; exact hlt
    obtain ⟨k, hk⟩ := cofW M _ _ hw (good_ofNat c) b hb hlt'
    refine ⟨k, ?_⟩
    show b ≤ o M ((expand M (s ++ [c + 1]) k).map T.ofNat)
    rw [expand_map]
    exact hk
  top_cofinal b hb hlt := top_cofinal_M M b hb hlt

end Sem

namespace Mbek

/-- The bound of `OT M`: `ψ₀(ω) = ω^ω` for `M = 0`, and `φ_{M-1}(0, 0)` for `M > 0`. -/
def boundT (M : Nat) : T :=
  if M = 0 then P 0 (P 0 (P 0 Z Z) Z) Z
  else P 0 (P 1 (T.mul (P 1 (P 1 Z Z) Z) (T.ofNat (M - 1))) Z) Z

theorem boundT_eq : ∀ M, boundT M = Sem.boundM M
  | 0 => rfl
  | n + 1 => by
      unfold boundT
      rw [if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel]
      rfl

/-- **The order isomorphism** between `OT M` (ordered lexicographically) and the
rank-one normal forms below `boundT M`. -/
def OT_iso (M : Nat) : StrictOrderIso (OT M) (NF1Below (boundT M)) :=
  boundT_eq M ▸ (Sem.translation M).toIso

/-- For every `M`, `OT M` is order-isomorphic to the normal forms below `boundT M`. -/
theorem OT_order_iso (M : Nat) : Nonempty (StrictOrderIso (OT M) (NF1Below (boundT M))) :=
  ⟨OT_iso M⟩

end Mbek

