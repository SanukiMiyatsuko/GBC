import Mbekworm.Sequence.SemFixpoint
import Mbekworm.Sequence.ParentSearch
import Mbekworm.Sequence.OTWellFounded

/-!
# Cofinality

The worm valuation adds `1` when `0` is appended, has limit values otherwise, is
continuous in its last letter, and the values of the expansions of a worm are
cofinal in its value.
-/

open T GenBek Mbek

namespace Sem

/-!
## Continuity of the worm valuation

* `succLast`: appending the letter `0` adds `1`;
* `limLast`: a worm ending with a positive letter has a limit value;
* `econt`: `E (n+1) μ` is continuous in its argument;
* `contLast`: the value is continuous in the last letter.
-/

/-! ### The facts, unconditionally -/

theorem gb (n L : Nat) : GoodBelow (n + 1) L := fun w hw _ => (facts (n + 1)).good w hw

theorem mb (n L : Nat) : MonoBelow (n + 1) L :=
  fun s t hs ht _ h => (facts (n + 1)).mono s t hs ht h

theorem o_good {n : Nat} {w : List T} (hw : GoodW n w) : Good (o n w) := (facts n).good w hw

theorem o_mono {n : Nat} {s t : List T} (hs : GoodW n s) (ht : GoodW n t) (h : s < t) :
    o n s < o n t := (facts n).mono s t hs ht h

theorem o_vals' {n : Nat} {w : List T} (hw : GoodW (n + 1) w) :
    o (n + 1) w = minus1 (o n (vals n w)) :=
  o_vals (facts n) (gb n w.length) (mb n w.length) hw (Nat.le_refl _)

theorem vals_goodW' {n : Nat} {w : List T} (hw : GoodW (n + 1) w) : GoodW n (vals n w) :=
  vals_goodW (facts n) (gb n (w.length + 1)) (mb n (w.length + 1)) hw (Nat.le_succ _)
    (fun _ => Nat.lt_succ_self _)

theorem o_shift' {n : Nat} {w : List T} {ν : T} (hw : GoodW (n + 1) w) (hν : Good ν)
    (h : ∀ x ∈ w, ν ≤ x) : o (n + 1) w = E (n + 1) ν (o (n + 1) (w.map (leftSub ν))) :=
  o_shift (facts n) (gb n w.length) (mb n w.length) hw hν h (Nat.le_refl _)

theorem goodW_prefix {n : Nat} {V : List T} {x : T} (h : GoodW n (V ++ [x])) : GoodW n V :=
  ⟨fun y hy => h.good (List.mem_append_left _ hy), (Mbek.NF_prefix_dec n).1 V x h.2⟩

theorem goodW_dec {n : Nat} {V : List T} {x y : T} (h : GoodW n (V ++ [x])) (hy : Good y)
    (hyx : y < x) : GoodW n (V ++ [y]) := by
  refine ⟨fun z hz => ?_, (Mbek.NF_prefix_dec n).2 V x y h.2 hyx⟩
  rcases List.mem_append.mp hz with hz | hz
  · exact h.good (List.mem_append_left _ hz)
  · rw [List.mem_singleton.mp hz]; exact hy

theorem goodW_le {n : Nat} {V : List T} {x y : T} (h : GoodW n (V ++ [x])) (hy : Good y)
    (hyx : y ≤ x) : GoodW n (V ++ [y]) := by
  rcases hyx with hyx | rfl
  · exact goodW_dec h hy hyx
  · exact h

theorem list_snoc_lt : ∀ (V : List T) {x y : T}, x < y → V ++ [x] < V ++ [y]
  | [], _, _, h => List.Lex.rel h
  | a :: V, _, _, h => List.Lex.cons (list_snoc_lt V h)

theorem o_last_le {n : Nat} {V : List T} {x y : T} (hx : GoodW n (V ++ [x])) (hy : GoodW n (V ++ [y]))
    (h : x ≤ y) : o n (V ++ [x]) ≤ o n (V ++ [y]) := by
  rcases h with h | rfl
  · exact Or.inl (o_mono hx hy (list_snoc_lt V h))
  · exact le_refl' _

/-! ### Appending `0` -/

theorem oadd_add_one : ∀ (x y : T), oadd x (T.add y one) = T.add (oadd x y) one
  | Z, _ => rfl
  | P i a b, y => by
      by_cases hy : y = Z
      · subst hy
        rw [show T.add Z one = one from rfl, oadd_one, oadd_Z_right]
      · rw [oadd_P, oadd_P, head_add_of_ne hy]
        split
        · rfl
        · rw [add_P, oadd_add_one b y]

theorem cantorT_snoc_Z : ∀ (Q : List T), cantorT (Q ++ [Z]) = T.add (cantorT Q) one
  | [] => by
      show oadd (omegaPow Z) (cantorT []) = T.add Z one
      rw [show cantorT [] = Z from rfl, oadd_Z_right]; rfl
  | b :: Q => by
      show oadd (omegaPow b) (cantorT (Q ++ [Z])) = T.add (oadd (omegaPow b) (cantorT Q)) one
      rw [cantorT_snoc_Z Q, oadd_add_one]

theorem vals_snoc_Z (n : Nat) (Q : List T) : vals n (Q ++ [Z]) = vals n Q ++ [Z] := by
  simp only [vals, Mbek.sepPieces_snoc_eq, List.map_append, List.map_cons, List.map_nil, o_nil]

theorem vals_ne_nil (n : Nat) (Q : List T) : vals n Q ≠ [] := by
  unfold vals; intro h; exact sepPieces_ne_nil Z Q (List.map_eq_nil_iff.mp h)

/-- **Appending `0` adds `1`**. -/
theorem succLast : ∀ (n : Nat) {Q : List T}, GoodW n (Q ++ [Z]) → o n (Q ++ [Z]) = T.add (o n Q) one
  | 0, Q, _ => by rw [o_zero, o_zero, cantorT_snoc_Z]
  | n + 1, Q, hw => by
      have hQ := goodW_prefix hw
      rw [o_vals' hw, o_vals' hQ, vals_snoc_Z]
      have hvg := vals_goodW' hw
      rw [vals_snoc_Z] at hvg
      rw [succLast n hvg]
      apply minus1_add_one
      exact (ne_of_lt'' ((facts n).pos (vals_goodW' hQ) (vals_ne_nil n Q))).symm

/-! ### Limit values -/

theorem lim_of_lastS {x : T} (h0 : x ≠ Z) (h1 : lastS x ≠ one) : Lim x :=
  ⟨h0, fun y hy => h1 (by rw [hy, lastS_add_of_ne y (show one ≠ Z by intro e; cases e)]; rfl)⟩

theorem oadd_suffix : ∀ x y : T, ∃ p, oadd x y = T.add p y
  | Z, _ => ⟨Z, rfl⟩
  | P i a b, y => by
      rw [oadd_P]
      split
      · exact ⟨Z, rfl⟩
      · obtain ⟨p, hp⟩ := oadd_suffix b y
        exact ⟨P i a p, by rw [hp, add_P]⟩

theorem cantorT_snoc_suffix : ∀ (Q : List T) (ℓ : T), ∃ p, cantorT (Q ++ [ℓ]) = T.add p (omegaPow ℓ)
  | [], ℓ => ⟨Z, by
      show oadd (omegaPow ℓ) (cantorT []) = _
      rw [show cantorT [] = Z from rfl, oadd_Z_right]; rfl⟩
  | b :: Q, ℓ => by
      obtain ⟨p, hp⟩ := cantorT_snoc_suffix Q ℓ
      show ∃ p', oadd (omegaPow b) (cantorT (Q ++ [ℓ])) = _
      rw [hp]
      obtain ⟨p', hp'⟩ := oadd_suffix (omegaPow b) (T.add p (omegaPow ℓ))
      exact ⟨T.add p' p, by rw [hp', add_assoc'']⟩

theorem sepPieces_snoc_of {A : List T} {Ps : List (List T)} {μ x : T} {P' : List T} (h1 : sepPieces μ A = Ps ++ [P'])
    (hx : x ≠ μ) : sepPieces μ (A ++ [x]) = Ps ++ [P' ++ [x]] := by
  obtain ⟨Ps', P'', h1', h2'⟩ := Mbek.sepPieces_snoc_ne μ A x hx
  rw [h1] at h1'
  obtain ⟨e1, e2⟩ := List.append_inj' h1' rfl
  injection e2 with e2
  rw [h2', e1, e2]

/-- **A positive last letter gives a limit value**. -/
theorem limLast : ∀ (n : Nat) {Q : List T} {ℓ : T}, GoodW n (Q ++ [ℓ]) → ℓ ≠ Z →
    Lim (o n (Q ++ [ℓ]))
  | 0, Q, ℓ, _, hℓ => by
      rw [o_zero]
      obtain ⟨p, hp⟩ := cantorT_snoc_suffix Q ℓ
      rw [hp]
      apply lim_of_lastS
      · intro e; exact omegaPow_ne_Z ℓ (add_eq_Z_iff.mp e).2
      · rw [lastS_add_of_ne p (omegaPow_ne_Z ℓ), omegaPow_eq]
        intro e; injection e with _ h; exact omegaArg_ne_Z hℓ h
  | n + 1, Q, ℓ, hw, hℓ => by
      rw [o_vals' hw]
      obtain ⟨Ps, P', _, hL⟩ := Mbek.sepPieces_snoc_ne Z Q ℓ hℓ
      have hv : vals n (Q ++ [ℓ]) = Ps.map (fun p => o (n + 1) (p.map minus1)) ++
          [o (n + 1) ((P' ++ [ℓ]).map minus1)] := by
        simp only [vals, hL, List.map_append, List.map_cons, List.map_nil]
      have hvg := vals_goodW' hw
      rw [hv] at hvg ⊢
      have hpos : o (n + 1) ((P' ++ [ℓ]).map minus1) ≠ Z := by
        have hp : (P' ++ [ℓ]) ∈ sepPieces Z (Q ++ [ℓ]) := by rw [hL]; simp
        have hg := goodW_piece hw hp
        exact (ne_of_lt'' ((facts (n + 1)).pos hg (by simp))).symm
      have hl := limLast n hvg hpos
      rw [minus1_lim (o_good hvg) hl]
      exact hl

theorem lim_single (n : Nat) {y : T} (hy : Good y) (h0 : y ≠ Z) : Lim (o n [y]) :=
  limLast n (Q := []) (GoodW.single n hy) h0

/-! ### Continuity -/

/-- `f` is continuous at `ξ`. -/
def ContAt (f : T → T) (ξ : T) : Prop := Cof (f ξ) (fun y : Below ξ => f y.1)

theorem good_of_lt_good {b ξ : T} (hb : T.isNF1 b) (hξ : Good ξ) (h : b < ξ) : Good b :=
  ⟨hb, Cnt_of_lt_Om (isNF1_desc hb) (lt_tr h (Cnt_lt_Om hξ.cnt))⟩

theorem cof_below {ξ : T} (hξ : Good ξ) : Cof ξ (fun y : Below ξ => y.1) :=
  fun b hb hlt => ⟨⟨b, good_of_lt_good hb hξ hlt, hlt⟩, le_refl' _⟩

theorem le_minus1_of_lt {u b : T} (hu : Good u) (h : b < u) : b ≤ minus1 u := by
  cases u with
  | Z => exact absurd h (not_lt_Z' _)
  | P i a r =>
      have hi := hu.idx; subst hi
      cases a with
      | Z =>
          show b ≤ r
          rw [← fin_succ hu] at h
          exact lt_add_one_le r b h
      | P _ _ _ => exact Or.inl h

theorem Eom_le {n : Nat} {α y y' : T} (hα : Good α) (hy : Good y) (hy' : Good y') (h : y ≤ y') :
    Eom (n + 1) α y ≤ Eom (n + 1) α y' := by
  rcases h with h | rfl
  · exact Or.inl (Eom_lt (facts n) hα hy hy' h)
  · exact le_refl' _

theorem Eom_lim (n : Nat) {α y : T} (hα : Good α) (hy : Good y) (hy0 : y ≠ Z) :
    Lim (Eom (n + 1) α y) := by
  by_cases h0 : α = Z
  · subst h0
    rw [Eom_succ_Z]
    have hl := lim_single n hy hy0
    rw [minus1_lim (o_good (GoodW.single n hy)) hl]
    exact hl
  · rw [Eom_succ_ne n h0, if_neg hy0]
    have hα' : Good (if n = 0 then α else minus1 α) := by
      split
      · exact hα
      · exact good_minus1 hα
    obtain ⟨Y, hY, hY0, _⟩ := phi_lvl n (if n = 0 then α else minus1 α) (minus1 y) hα' (good_minus1 hy)
    rw [hY]
    exact lim_P0 hY0

theorem E_lim (n : Nat) : ∀ {μ x : T}, Good μ → Good x → Lim x → Lim (E (n + 1) μ x)
  | Z, x, _, _, hl => by rw [E_Z]; exact hl
  | P i c b, x, hμ, hx, hl => by
      have hi := hμ.idx; subst hi
      rw [E_P]
      exact Eom_lim n (good_logA (isNF1_head hμ.nf)) (E_good (facts n) hμ.tail hx)
        (E_lim n hμ.tail hx hl).1

/-- Continuity of one step of the hyperation, from continuity of `o n` on single letters. -/
theorem Eom_cont (n : Nat) (hS : ∀ z, Good z → Lim z → ContAt (fun y => o n [y]) z)
    {α z : T} (hα : Good α) (hz : Good z) (hl : Lim z) : ContAt (Eom (n + 1) α) z := by
  intro b hb hlt
  by_cases h0 : α = Z
  · subst h0
    rw [Eom_succ_Z] at hlt
    have hlt' := lt_of_lt_of_le' hlt (minus1_le (o_good (GoodW.single n hz)))
    obtain ⟨⟨y, hy, hyz⟩, hby⟩ := hS z hz hl b hb hlt'
    have hy1 := hl.succ_lt hz hy hyz
    refine ⟨⟨T.add y one, good_add_one hy, hy1⟩, ?_⟩
    show b ≤ Eom (n + 1) Z (T.add y one)
    rw [Eom_succ_Z]
    apply le_minus1_of_lt (o_good (GoodW.single n (good_add_one hy)))
    apply lt_of_le_of_lt' hby
    exact o_mono (GoodW.single n hy) (GoodW.single n (good_add_one hy))
      (List.Lex.rel (lt_add_of_ne y nofun))
  · have hα' : Good (if n = 0 then α else minus1 α) := by
      split
      · exact hα
      · exact good_minus1 hα
    have hk : n = 0 → (if n = 0 then α else minus1 α) ≠ Z := by
      intro h; rw [if_pos h]; exact h0
    have hEz : Eom (n + 1) α z = phi n (if n = 0 then α else minus1 α) z := by
      rw [Eom_succ_ne n h0, if_neg hl.1, minus1_lim hz hl]
    rw [hEz] at hlt
    obtain ⟨⟨y, hy, hyz⟩, hby⟩ := phi_cont n hα' hk hz hl (s := fun y : Below z => y.1)
      (fun y => y.2.1) (fun y => y.2.2) (cof_below hz) b hb hlt
    have hy1 := hl.succ_lt hz hy hyz
    refine ⟨⟨T.add y one, good_add_one hy, hy1⟩, ?_⟩
    show b ≤ Eom (n + 1) α (T.add y one)
    rw [Eom_succ_ne n h0, if_neg (add_one_ne_Z y)]
    apply le_tr hby
    rcases le_minus1_succ hy with h | h
    · exact Or.inl (phi_lt_phi n _ hα' hy (good_minus1 (good_add_one hy)) hk h)
    · rw [← h]; exact le_refl' _

/-- **Continuity of `E (n+1) μ` in its argument**. -/
theorem econt (n : Nat) (hS : ∀ z, Good z → Lim z → ContAt (fun y => o n [y]) z) :
    ∀ {μ x : T}, Good μ → Good x → Lim x → ContAt (E (n + 1) μ) x
  | Z, x, _, hx, _ => by
      intro b hb hlt
      rw [E_Z] at hlt
      obtain ⟨y, hy⟩ := cof_below hx b hb hlt
      exact ⟨y, by show b ≤ E (n + 1) Z y.1; rw [E_Z]; exact hy⟩
  | P i c b0, x, hμ, hx, hl => by
      have hi := hμ.idx; subst hi
      intro b hb hlt
      rw [E_P] at hlt
      have hα := good_logA (isNF1_head hμ.nf)
      have hEb := E_good (facts n) hμ.tail hx
      obtain ⟨⟨z, hz, hzE⟩, hbz⟩ := Eom_cont n hS hα hEb (E_lim n hμ.tail hx hl) b hb hlt
      obtain ⟨⟨y, hy, hyx⟩, hzy⟩ := econt n hS hμ.tail hx hl z hz.nf hzE
      refine ⟨⟨y, hy, hyx⟩, ?_⟩
      show b ≤ E (n + 1) (P 0 c b0) y
      rw [E_P]
      exact le_tr hbz (Eom_le hα hz (E_good (facts n) hμ.tail hy) hzy)

/-! ### Left subtraction and ordinal addition -/

theorem leftSub_oadd : ∀ x u : T, leftSub x (oadd x u) = u
  | Z, u => leftSub_Z_left u
  | P i a b, u => by
      rw [oadd_P]
      split
      · rename_i h
        cases u with
        | Z => exact absurd h (not_lt_Z' _)
        | P j c d =>
            rw [leftSub_P_P]
            have hne : ¬ (i = j ∧ a = c) := by
              rintro ⟨rfl, rfl⟩; exact lt_irr _ h
            rw [if_neg hne]
      · rw [leftSub_P_P, if_pos ⟨rfl, rfl⟩, leftSub_oadd b u]

theorem leftSub_add : ∀ C X : T, leftSub C (T.add C X) = X
  | Z, X => leftSub_Z_left X
  | P i a b, X => by rw [add_P, leftSub_P_P, if_pos ⟨rfl, rfl⟩, leftSub_add b X]

theorem leftSub_eq_Z {μ x : T} (hμ : Good μ) (hx : Good x) (h : μ ≤ x) (e : leftSub μ x = Z) :
    x = μ := by
  have := oadd_leftSub hμ hx h
  rw [e, oadd_Z_right] at this
  exact this.symm

theorem oadd_le_right {x y y' : T} (hx : Desc x) (h : y ≤ y') : oadd x y ≤ oadd x y' := by
  rcases h with h | rfl
  · exact Or.inl (oadd_lt_oadd_right hx h)
  · exact le_refl' _

theorem le_oadd_self {x y : T} (hx : Desc x) : x ≤ oadd x y := by
  have := oadd_le_right (y := Z) (y' := y) hx (Z_le' y)
  rwa [oadd_Z_right] at this

theorem cnt_of_add_left : ∀ {C D : T}, Cnt (T.add C D) → Cnt C
  | Z, _, _ => trivial
  | P i a b, D, h => by
      rw [add_P] at h
      exact ⟨h.1, cnt_of_add_left h.2⟩

theorem lim_leftSub {μ x : T} (hμ : Good μ) (hx : Good x) (h : μ < x) (hl : Lim x) :
    Lim (leftSub μ x) := by
  have hx' := oadd_leftSub hμ hx (le_of_lt' h)
  refine ⟨fun e => ?_, fun y hy => ?_⟩
  · rw [e, oadd_Z_right] at hx'
    rw [hx'] at h; exact lt_irr _ h
  · rw [hy, oadd_add_one] at hx'
    exact hl.2 _ hx'.symm

theorem lim_decomp : ∀ {lm : T}, Good lm → Lim lm → ∃ lm' c, lm = T.add lm' (P 0 c Z) ∧ c ≠ Z
  | Z, _, hl => absurd rfl hl.1
  | P i a b, hg, hl => by
      have hi := hg.idx; subst hi
      by_cases hb : b = Z
      · subst hb
        obtain ⟨c, b', he, hc⟩ := lim_head hg hl
        injection he with _ h1 h2
        subst h1
        exact ⟨Z, a, rfl, hc⟩
      · obtain ⟨lm'', c, he, hc⟩ := lim_decomp hg.tail (hl.tail hb)
        exact ⟨P 0 a lm'', c, by rw [he, add_P], hc⟩

/-! ### Shifted letters and piece values -/

/-- `-1 + (-μ + x)`. -/
def fSh (μ x : T) : T := minus1 (leftSub μ x)

/-- The value of a piece above `μ`. -/
def vSh (n : Nat) (μ : T) (p : List T) : T := o (n + 1) (p.map (fSh μ))

theorem leftSub_ne_Z {μ x : T} (hμ : Good μ) (hx : Good x) (h : μ < x) : leftSub μ x ≠ Z :=
  fun e => by rw [leftSub_eq_Z hμ hx (le_of_lt' h) e] at h; exact lt_irr _ h

theorem good_fSh {μ x : T} (hμ : Good μ) (hx : Good x) : Good (fSh μ x) :=
  good_minus1 (good_leftSub hμ hx)

theorem fSh_lt {μ x y : T} (hμ : Good μ) (hx : Good x) (hy : Good y) (hμx : μ < x) (h : x < y) :
    fSh μ x < fSh μ y :=
  minus1_lt_minus1 (good_leftSub hμ hx) (good_leftSub hμ hy) (leftSub_ne_Z hμ hx hμx)
    (leftSub_lt_leftSub hμ hx hy (le_of_lt' hμx) h)

theorem fSh_inj {μ x y : T} (hμ : Good μ) (hx : Good x) (hy : Good y) (hμx : μ < x) (hμy : μ < y)
    (h : fSh μ x = fSh μ y) : x = y := by
  rcases lt_total_thm x y with h' | h' | h'
  · exact absurd h (ne_of_lt'' (fSh_lt hμ hx hy hμx h'))
  · exact absurd h.symm (ne_of_lt'' (fSh_lt hμ hy hx hμy h'))
  · exact h'

theorem leftSub_add_one {μ q : T} (hμ : Good μ) (hq : Good q) (h : μ ≤ q) :
    leftSub μ (T.add q one) = T.add (leftSub μ q) one := by
  have e := oadd_leftSub hμ hq h
  conv => lhs; rw [← e, ← oadd_add_one]
  exact leftSub_oadd _ _

theorem fSh_add_one {μ q : T} (hμ : Good μ) (hq : Good q) (h : μ < q) :
    fSh μ (T.add q one) = T.add (fSh μ q) one := by
  unfold fSh
  rw [leftSub_add_one hμ hq (le_of_lt' h), minus1_add_one (leftSub_ne_Z hμ hq h)]

theorem fSh_succ_self (q : T) : fSh q (T.add q one) = Z := by
  unfold fSh; rw [leftSub_add]; rfl

theorem embOn_fSh {μ : T} {S : List T} (hμ : Good μ) (hS : ∀ x ∈ S, Good x ∧ μ < x) :
    EmbOn (fSh μ) S :=
  fun x hx y hy h => fSh_lt hμ (hS x hx).1 (hS y hy).1 (hS x hx).2 h

theorem map_fSh_lt {μ : T} {p p' : List T} (hμ : Good μ) (hp : ∀ x ∈ p, Good x ∧ μ < x)
    (hp' : ∀ x ∈ p', Good x ∧ μ < x) (h : p < p') : p.map (fSh μ) < p'.map (fSh μ) :=
  map_lt_map (fun x hx y hy hxy => fSh_lt hμ (hp x hx).1 (hp' y hy).1 (hp x hx).2 hxy)
    (fun x hx y hy e => fSh_inj hμ (hp x hx).1 (hp' y hy).1 (hp x hx).2 (hp' y hy).2 e) h

/-- **Value of a worm cut at a lower bound `ν`**. -/
theorem o_joinS {n : Nat} {ν : T} {Qs : List (List T)} (hQs : Qs ≠ [])
    (habove : ∀ Q ∈ Qs, AboveL ν Q) (hν : Good ν) (hw : GoodW (n + 1) (joinS ν Qs)) :
    o (n + 1) (joinS ν Qs) = E (n + 1) ν (minus1 (o n (Qs.map (vSh n ν)))) ∧
    GoodW n (Qs.map (vSh n ν)) ∧ ∀ Q ∈ Qs, GoodW (n + 1) (Q.map (fSh ν)) := by
  have hmin : ∀ x ∈ joinS ν Qs, ν ≤ x := by
    intro x hx
    rcases mem_joinS' hx with rfl | ⟨Q, hQ, hxQ⟩
    · exact le_refl' _
    · exact Or.inl (habove Q hQ x hxQ)
  have hU := goodW_leftSub (facts n) hw hν hmin
  have hsp : sepPieces Z ((joinS ν Qs).map (leftSub ν)) = Qs.map (List.map (leftSub ν)) := by
    have h := sepPieces_map (f := leftSub ν) (μ := ν) (xs := joinS ν Qs)
      (fun x hx e => leftSub_eq_Z hν (hw.good hx) (hmin x hx) (e.trans (leftSub_self ν)))
    rw [leftSub_self] at h
    rw [h, sepPieces_joinS ν Qs hQs (fun Q hQ hm => lt_irr _ (habove Q hQ ν hm))]
  have hv : vals n ((joinS ν Qs).map (leftSub ν)) = Qs.map (vSh n ν) := by
    unfold vals
    rw [hsp, List.map_map]
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_def, vSh, List.map_map]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [o_shift' hw hν hmin, o_vals' hU, hv]
  · have := vals_goodW' hU
    rwa [hv] at this
  · intro Q hQ
    have hp : Q.map (leftSub ν) ∈ sepPieces Z ((joinS ν Qs).map (leftSub ν)) := by
      rw [hsp]; exact List.mem_map_of_mem hQ
    have h1 := goodW_piece hU hp
    rwa [List.map_map] at h1

/-! ### Splitting off the last piece -/

theorem last_split_data {n : Nat} {V : List T} {μ y : T} {Ps : List (List T)} {P' : List T}
    (hw : GoodW (n + 1) (V ++ [y])) (hμ : Good μ) (hmin : ∀ x ∈ V ++ [y], μ ≤ x) (hyμ : y ≠ μ)
    (hsep : sepPieces μ V = Ps ++ [P']) :
    o (n + 1) (V ++ [y]) = E (n + 1) μ (minus1 (o n
      (Ps.map (fun p => o (n + 1) (p.map (fun x => minus1 (leftSub μ x)))) ++
        [o (n + 1) (P'.map (fun x => minus1 (leftSub μ x)) ++ [minus1 (leftSub μ y)])]))) ∧
    GoodW n (Ps.map (fun p => o (n + 1) (p.map (fun x => minus1 (leftSub μ x)))) ++
        [o (n + 1) (P'.map (fun x => minus1 (leftSub μ x)) ++ [minus1 (leftSub μ y)])]) ∧
    GoodW (n + 1) (P'.map (fun x => minus1 (leftSub μ x)) ++ [minus1 (leftSub μ y)]) := by
  have hsep' := sepPieces_snoc_of hsep hyμ
  have hJ : V ++ [y] = joinS μ (Ps ++ [P' ++ [y]]) := by rw [← hsep', joinS_sepPieces]
  obtain ⟨e, g1, g2⟩ := o_joinS (by simp) (hsep' ▸ above_of_mem_sepPieces hmin) hμ (hJ ▸ hw)
  have g3 := g2 _ (by simp : P' ++ [y] ∈ Ps ++ [P' ++ [y]])
  rw [← hJ] at e
  simp only [vSh, List.map_append, List.map_cons, List.map_nil] at e g1 g3
  exact ⟨e, g1, g3⟩

/-! ### Continuity in the last letter -/

/-- The value of a worm is continuous in its last letter. -/
def ContLastStmt (n : Nat) : Prop :=
  ∀ (V : List T) (lm : T), GoodW n (V ++ [lm]) → Lim lm → ContAt (fun y => o n (V ++ [y])) lm

theorem oadd_cont {x u : T} (hx : Good x) (hu : Good u) (hl : Lim u) {b : T} (hb : T.isNF1 b)
    (hlt : b < oadd x u) : ∃ z, Good z ∧ z < u ∧ (b = oadd x z ∨ b < x) := by
  by_cases hbx : b < x
  · exact ⟨Z, good_Z, by cases u with
      | Z => exact absurd rfl hl.1
      | P _ _ _ => exact Z_lt_P' _ _ _, Or.inr hbx⟩
  · have hou := good_oadd hx hu
    have hbg : Good b := good_of_lt_good hb hou hlt
    have hxb : x ≤ b := le_of_not_lt' hbx
    refine ⟨leftSub x b, good_leftSub hx hbg, ?_, Or.inl (oadd_leftSub hx hbg hxb).symm⟩
    have := leftSub_lt_leftSub hx hbg hou hxb hlt
    rwa [leftSub_oadd] at this

theorem contLast_zero : ContLastStmt 0 := by
  intro V
  induction V with
  | nil =>
      intro lm hw hl b hb hlt
      have hlm := hw.good (List.mem_singleton_self lm)
      show ∃ y : Below lm, b ≤ o 0 [y.1]
      change b < o 0 [lm] at hlt
      rw [o_single_zero] at hlt
      obtain ⟨y, hy⟩ := omegaPow_cont hlm hl (s := fun y : Below lm => y.1) (fun y => y.2.1)
        (cof_below hlm) b hb hlt
      exact ⟨y, by rw [o_single_zero]; exact hy⟩
  | cons a V ih =>
      intro lm hw hl b hb hlt
      have hlm := hw.good (List.mem_append_right _ (List.mem_singleton_self lm))
      have ha := hw.good (List.mem_cons_self (a := a) (l := V ++ [lm]))
      have hw' : GoodW 0 (V ++ [lm]) :=
        ⟨fun x hx => hw.good (List.mem_cons_of_mem a hx), (List.pairwise_cons.mp hw.2).2⟩
      have hx := good_omegaPow ha
      have hu := o_good hw'
      have hul := limLast 0 hw' hl.1
      have hcons : ∀ y, o 0 (a :: (V ++ [y])) = oadd (omegaPow a) (o 0 (V ++ [y])) := by
        intro y; rw [o_zero, o_zero]; rfl
      show ∃ y : Below lm, b ≤ o 0 (a :: (V ++ [y.1]))
      change b < o 0 (a :: (V ++ [lm])) at hlt
      rw [hcons] at hlt
      obtain ⟨z, hz, hzu, hbz | hbx⟩ := oadd_cont hx hu hul hb hlt
      · obtain ⟨y, hy⟩ := ih lm hw' hl z hz.nf hzu
        refine ⟨y, ?_⟩
        rw [hcons, hbz]
        exact oadd_le_right hx.desc hy
      · have hZ : Z < lm := by
          cases lm with
          | Z => exact absurd rfl hl.1
          | P _ _ _ => exact Z_lt_P' _ _ _
        refine ⟨⟨Z, good_Z, hZ⟩, ?_⟩
        rw [hcons]
        exact le_tr (Or.inl hbx) (le_oadd_self hx.desc)

theorem Z_lt_of_ne_Z {x : T} (h : x ≠ Z) : Z < x := by
  cases x with
  | Z => exact absurd rfl h
  | P _ _ _ => exact Z_lt_P' _ _ _

theorem head_ge_of_le_single {x : T} {j : Nat} {c : T} (h : P j c Z ≤ x) : P j c Z ≤ T.head x := by
  rcases h with h | h
  · exact head_le_of_lt h
  · rw [← h]; exact le_refl' _

theorem contLast_succ (n : Nat) (hC : ContLastStmt n) : ContLastStmt (n + 1) := by
  have hS : ∀ z, Good z → Lim z → ContAt (fun y => o n [y]) z :=
    fun z hz hl => hC [] z (GoodW.single n hz) hl
  suffices H : ∀ k (V : List T) (lm : T), V.length = k → GoodW (n + 1) (V ++ [lm]) → Lim lm →
      ContAt (fun y => o (n + 1) (V ++ [y])) lm from fun V lm => H V.length V lm rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro V lm hk hw hl b hb hlt
  change b < o (n + 1) (V ++ [lm]) at hlt
  show ∃ y : Below lm, b ≤ o (n + 1) (V ++ [y.1])
  have hlm : Good lm := hw.good (List.mem_append_right _ (List.mem_singleton_self lm))
  have hne : V ++ [lm] ≠ [] := by simp
  have hs := tmin_spec hne
  have hμg : Good (tmin (V ++ [lm])) := hw.good hs.1
  generalize tmin (V ++ [lm]) = μ at hs hμg
  by_cases hμl : μ < lm
  · -- the least letter occurs before the last one
    have hμne : lm ≠ μ := fun e => by rw [e] at hμl; exact lt_irr _ hμl
    have hμV : μ ∈ V := by
      rcases List.mem_append.mp hs.1 with h | h
      · exact h
      · exact absurd (List.mem_singleton.mp h).symm hμne
    obtain ⟨Ps, P', hsep, _⟩ := Mbek.sepPieces_snoc_ne μ V lm hμne
    obtain ⟨e0, gW0, gP0⟩ := last_split_data hw hμg hs.2 hμne hsep
    have hLS := lim_leftSub hμg hlm hμl hl
    have hLSg := good_leftSub hμg hlm
    have hfl : minus1 (leftSub μ lm) = leftSub μ lm := minus1_lim hLSg hLS
    rw [hfl] at e0 gW0 gP0
    have hgpos := (facts (n + 1)).pos gP0 (by simp)
    have hglim := limLast (n + 1) gP0 hLS.1
    have hL1 := limLast n gW0 (ne_of_lt'' hgpos).symm
    rw [minus1_lim (o_good gW0) hL1] at e0
    rw [e0] at hlt
    obtain ⟨⟨z1, hz1, hz1L⟩, hbz1⟩ := econt n hS hμg (o_good gW0) hL1 b hb hlt
    obtain ⟨⟨u, hu, hug⟩, hz1u⟩ := hC _ _ gW0 hglim z1 hz1.nf hz1L
    have hlen : (P'.map (fun x => minus1 (leftSub μ x))).length < k := by
      rw [List.length_map, ← hk]
      have hP'mem : P' ++ [lm] ∈ sepPieces μ (V ++ [lm]) := by
        rw [sepPieces_snoc_of hsep hμne]; simp
      have := length_lt_of_mem_sepPieces μ (V ++ [lm]) hs.1 _ hP'mem
      simp only [List.length_append, List.length_singleton] at this
      omega
    obtain ⟨⟨z2, hz2, hz2l⟩, huz2⟩ := ih _ hlen _ _ rfl gP0 hLS u hu.nf hug
    have hδ1 := hLS.succ_lt hLSg hz2 hz2l
    have hδ2 := hLS.succ_lt hLSg (good_add_one hz2) hδ1
    have hδg : Good (T.add (T.add z2 one) one) := good_add_one (good_add_one hz2)
    generalize hδdef : T.add (T.add z2 one) one = δ at hδ2 hδg
    have hδ0 : δ ≠ Z := by rw [← hδdef]; exact add_one_ne_Z _
    have hy'g : Good (oadd μ δ) := good_oadd hμg hδg
    have hy'lt : oadd μ δ < lm := by
      have := oadd_lt_oadd_right hμg.desc hδ2
      rwa [oadd_leftSub hμg hlm (le_of_lt' hμl)] at this
    have hμy' : μ < oadd μ δ := by
      have := oadd_lt_oadd_right (y := Z) hμg.desc (Z_lt_of_ne_Z hδ0)
      rwa [oadd_Z_right] at this
    have hw' : GoodW (n + 1) (V ++ [oadd μ δ]) := goodW_dec hw hy'g hy'lt
    have hmin' : ∀ x ∈ V ++ [oadd μ δ], μ ≤ x := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hs.2 x (List.mem_append_left _ h)
      · rw [List.mem_singleton.mp h]; exact le_of_lt' hμy'
    obtain ⟨e1, gW1, gP1⟩ := last_split_data hw' hμg hmin'
      (fun e => by rw [e] at hμy'; exact lt_irr _ hμy') hsep
    rw [leftSub_oadd] at e1 gW1 gP1
    have hfy : z2 < minus1 δ := by
      rw [← hδdef, minus1_add_one (add_one_ne_Z z2)]
      exact lt_of_le_of_lt' (le_minus1_succ hz2) (lt_add_of_ne _ nofun)
    have hgP2 := goodW_dec gP0 hz2 hz2l
    have h3 := le_tr huz2 (o_last_le hgP2 gP1 (Or.inl hfy))
    have hgW2 := goodW_dec gW0 hu hug
    have h4 := le_tr hz1u (o_last_le hgW2 gW1 h3)
    have hgpos1 := (facts (n + 1)).pos gP1 (by simp)
    have hL2 := limLast n gW1 (ne_of_lt'' hgpos1).symm
    rw [minus1_lim (o_good gW1) hL2] at e1
    refine ⟨⟨oadd μ δ, hy'g, hy'lt⟩, ?_⟩
    show b ≤ o (n + 1) (V ++ [oadd μ δ])
    rw [e1]
    exact le_tr hbz1 (E_le (facts n) hμg hz1 (o_good gW1) h4)
  · -- the last letter is the least one
    have hlmμ : μ = lm := by
      rcases hs.2 lm (List.mem_append_right _ (List.mem_singleton_self lm)) with h | h
      · exact absurd h hμl
      · exact h
    have hall : ∀ x ∈ V, lm ≤ x := fun x hx => hlmμ ▸ hs.2 x (List.mem_append_left _ hx)
    obtain ⟨lm', c, hdec, hc0⟩ := lim_decomp hlm hl
    have hωn : T.isNF1 (P 0 c Z) := by
      have := hlm.nf; rw [hdec] at this; exact isNF1_of_add_right this
    have hωg : Good (P 0 c Z) := ⟨hωn, rfl, trivial⟩
    have hlm'g : Good lm' := by
      have h1 := hlm.nf; have h2 := hlm.cnt; rw [hdec] at h1 h2
      exact ⟨isNF1_of_add_left h1, cnt_of_add_left h2⟩
    have hlm'le : lm' ≤ lm := by rw [hdec]; exact le_add_right' _ _
    have hlS : leftSub lm' lm = P 0 c Z := by rw [hdec]; exact leftSub_add _ _
    have hoadd : oadd lm' (P 0 c Z) = lm := by rw [← hlS]; exact oadd_leftSub hlm'g hlm hlm'le
    have heg : Good (logA c) := good_logA hωn
    have he0 : logA c ≠ Z := logA_ne_Z hc0
    have hωe : omegaPow (logA c) = P 0 c Z := omegaPow_logA hωn
    have hEω : ∀ y, E (n + 1) (P 0 c Z) y = Eom (n + 1) (logA c) y := by
      intro y; rw [E_P, E_Z]
    have hmin_lm' : ∀ y, lm' ≤ y → ∀ x ∈ V ++ [y], lm' ≤ x := by
      intro y hy x hx
      rcases List.mem_append.mp hx with h | h
      · exact le_tr hlm'le (hall x h)
      · rw [List.mem_singleton.mp h]; exact hy
    have hshift : ∀ y, Good y → lm' ≤ y → y ≤ lm →
        o (n + 1) (V ++ [y]) = E (n + 1) lm' (o (n + 1) (V.map (leftSub lm') ++ [leftSub lm' y])) ∧
        GoodW (n + 1) (V.map (leftSub lm') ++ [leftSub lm' y]) := by
      intro y hy hle hyl
      have hwy := goodW_le hw hy hyl
      have hm := hmin_lm' y hle
      refine ⟨?_, ?_⟩
      · rw [o_shift' hwy hlm'g hm, List.map_append, List.map_cons, List.map_nil]
      · have := goodW_leftSub (facts n) hwy hlm'g hm
        rwa [List.map_append, List.map_cons, List.map_nil] at this
    obtain ⟨eL, gL⟩ := hshift lm hlm hlm'le (le_refl' _)
    rw [hlS] at eL gL
    have hV'big : ∀ x ∈ V.map (leftSub lm'), P 0 c Z ≤ x := by
      intro x hx
      obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
      rw [← hlS]
      exact leftSub_le_leftSub hlm'g hlm (hw.good (List.mem_append_left _ hx0)) hlm'le (hall x0 hx0)
    generalize V.map (leftSub lm') = V' at eL gL hshift hV'big
    have hV'g : GoodW (n + 1) V' := goodW_prefix gL
    have hminω : ∀ x ∈ V' ++ [P 0 c Z], P 0 c Z ≤ x := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hV'big x h
      · rw [List.mem_singleton.mp h]; exact le_refl' _
    have hX : Good (o (n + 1) (V'.map (leftSub (P 0 c Z)))) :=
      o_good (goodW_leftSub (facts n) hV'g hωg hV'big)
    have hinω : o (n + 1) (V' ++ [P 0 c Z]) =
        Eom (n + 1) (logA c) (T.add (o (n + 1) (V'.map (leftSub (P 0 c Z)))) one) := by
      rw [o_shift' gL hωg hminω, hEω, List.map_append, List.map_cons, List.map_nil, leftSub_self]
      have hg := goodW_leftSub (facts n) gL hωg hminω
      rw [List.map_append, List.map_cons, List.map_nil, leftSub_self] at hg
      rw [succLast (n + 1) hg]
    have hV'val : o (n + 1) V' = Eom (n + 1) (logA c) (o (n + 1) (V'.map (leftSub (P 0 c Z)))) := by
      rw [o_shift' hV'g hωg hV'big, hEω]
    have hinδ : ∀ δ, Good δ → δ < P 0 c Z → GoodW (n + 1) (V' ++ [δ]) →
        o (n + 1) (V' ++ [δ]) = E (n + 1) δ (T.add (o (n + 1) V') one) := by
      intro δ hδ hδω hgδ
      have hhead : ∀ x ∈ V', leftSub δ x = x := by
        intro x hx
        apply leftSub_of_head_lt
        cases δ with
        | Z => exact Or.inl rfl
        | P i a b' =>
            right
            exact lt_of_lt_of_le' (head_lt_of_lt_single hδω) (head_ge_of_le_single (hV'big x hx))
      have hmδ : ∀ x ∈ V' ++ [δ], δ ≤ x := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact le_of_lt' (lt_of_lt_of_le' hδω (hV'big x h))
        · rw [List.mem_singleton.mp h]; exact le_refl' _
      have hmap : (V' ++ [δ]).map (leftSub δ) = V' ++ [Z] := by
        rw [List.map_append, List.map_cons, List.map_nil, leftSub_self,
          (List.map_congr_left (f := leftSub δ) (g := id) hhead).trans (List.map_id V')]
      rw [o_shift' hgδ hδ hmδ, hmap]
      have hg := goodW_leftSub (facts n) hgδ hδ hmδ
      rw [hmap] at hg
      rw [succLast (n + 1) hg]
    have hinlim : Lim (o (n + 1) (V' ++ [P 0 c Z])) := limLast (n + 1) gL nofun
    rw [eL] at hlt
    obtain ⟨⟨z, hz, hzlt⟩, hbz⟩ := econt n hS hlm'g (o_good gL) hinlim b hb hlt
    rw [hinω] at hzlt
    obtain ⟨⟨δ, hδ, hδlt⟩, hzδ⟩ := fl n heg he0 hX z hz.nf hzlt
    rw [hωe] at hδlt
    change z ≤ E (n + 1) δ (T.add (Eom (n + 1) (logA c) (o (n + 1) (V'.map (leftSub (P 0 c Z))))) one) at hzδ
    rw [← hV'val] at hzδ
    have hyg : Good (oadd lm' δ) := good_oadd hlm'g hδ
    have hylt : oadd lm' δ < lm := by
      have := oadd_lt_oadd_right hlm'g.desc hδlt
      rwa [hoadd] at this
    have hyle : lm' ≤ oadd lm' δ := le_oadd_self hlm'g.desc
    obtain ⟨ey, gy⟩ := hshift (oadd lm' δ) hyg hyle (le_of_lt' hylt)
    rw [leftSub_oadd] at ey gy
    refine ⟨⟨oadd lm' δ, hyg, hylt⟩, ?_⟩
    show b ≤ o (n + 1) (V ++ [oadd lm' δ])
    rw [ey, hinδ δ hδ hδlt gy]
    exact le_tr hbz (E_le (facts n) hlm'g hz
      (E_good (facts n) hδ (good_add_one (o_good hV'g))) hzδ)

/-- **Continuity in the last letter**, at every level. -/
theorem contLast : ∀ n, ContLastStmt n
  | 0 => contLast_zero
  | n + 1 => contLast_succ n (contLast n)

theorem singleCont (n : Nat) {z : T} (hz : Good z) (hl : Lim z) : ContAt (fun y => o n [y]) z :=
  contLast n [] z (GoodW.single n hz) hl

theorem econt' (n : Nat) {μ x : T} (hμ : Good μ) (hx : Good x) (hl : Lim x) :
    ContAt (E (n + 1) μ) x :=
  econt n (fun _ hz hl => singleCont n hz hl) hμ hx hl

/-!
## Cofinality of the expansions

For a normal worm `A ++ [q + 1]` over countable letters, the values of the
expansions `gExpand m (A ++ [q + 1]) q k` are cofinal in its value.  The proof
follows the reductions R1 (the parent lies in the last piece), R2 (one level
down, on the pieces) and R3 (no parent).
-/

/-! ### The statement and level `0` -/

/-- Cofinality of the expansions at level `m`. -/
def CofWStmt (m : Nat) : Prop :=
  ∀ (A : List T) (q : T), GoodW m (A ++ [T.add q one]) → Good q →
    Cof (o m (A ++ [T.add q one])) (fun k : Nat => o m (gExpand m (A ++ [T.add q one]) q k))

theorem gExpand_zero_eq (A : List T) (ℓ q : T) (hq : q < ℓ) (k : Nat) :
    gExpand 0 (A ++ [ℓ]) q k = A ++ List.replicate (k + 1) q := by
  unfold gExpand
  rw [gTP_zero_snoc A ℓ q hq, List.dropLast_concat]
  cases hl : A.length with
  | zero =>
      rw [List.eq_nil_of_length_eq_zero hl]
      simp only [List.nil_append]
      rw [repeat_single]
  | succ a =>
      simp only
      have hdrop : (A ++ [q]).drop (a + 1) = [q] := by rw [← hl]; simp
      rw [hdrop, repeat_single, List.append_assoc, List.singleton_append, ← List.replicate_succ]

theorem cantorT_replicate (q : T) : ∀ N, cantorT (List.replicate N q) = rep0 (omegaArg q) N
  | 0 => rfl
  | N + 1 => by
      show oadd (omegaPow q) (cantorT (List.replicate N q)) = P 0 (omegaArg q) (rep0 (omegaArg q) N)
      rw [cantorT_replicate q N, omegaPow_eq, oadd_P_of_not_lt, oadd_Z_left]
      cases N with
      | zero => exact not_lt_Z' _
      | succ N => exact lt_irr _

theorem good_cantorT' : ∀ (w : List T), (∀ x ∈ w, Good x) → Good (cantorT w)
  | [], _ => good_Z
  | a :: w, h => by
      show Good (oadd (omegaPow a) (cantorT w))
      exact good_oadd (good_omegaPow (h a List.mem_cons_self))
        (good_cantorT' w (fun x hx => h x (List.mem_cons_of_mem a hx)))

theorem rep0_le_succ (x : T) : ∀ N, rep0 x N ≤ rep0 x (N + 1)
  | 0 => Z_le' _
  | N + 1 => P_le_P_tail (rep0_le_succ x N)

theorem rep0_cof {q : T} (hq : Good q) :
    ∀ b, T.isNF1 b → b < omegaPow (T.add q one) → ∃ N, b ≤ rep0 (omegaArg q) N := by
  intro b
  induction b with
  | Z => exact fun _ _ => ⟨0, le_refl' _⟩
  | P i c r _ ihr =>
      intro hb hlt
      rw [omegaPow_eq] at hlt
      obtain ⟨rfl, hc⟩ := lt_P0 hlt
      have hcn := isNF1_head hb
      have hlg := good_logA hcn
      have hoa := omegaArg_logA hcn
      have hle : logA c ≤ q := by
        apply le_of_not_lt'
        intro hql
        have h1 := succ_le_of_lt hql
        have h2 : omegaArg (T.add q one) ≤ omegaArg (logA c) := by
          rcases h1 with h1 | h1
          · exact Or.inl (omegaArg_lt (good_add_one hq) hlg h1)
          · rw [h1]; exact le_refl' _
        rw [hoa] at h2
        exact not_lt_of_le' h2 hc
      rcases hle with hle | hle
      · refine ⟨1, Or.inl ?_⟩
        show P 0 c r < P 0 (omegaArg q) Z
        apply T.Lt.p_mid
        rw [← hoa]
        exact omegaArg_lt hlg hq hle
      · have hcq : c = omegaArg q := by rw [← hoa, hle]
        subst hcq
        have hrlt : r < P 0 (omegaArg (T.add q one)) Z :=
          lt_tr (tail_lt_of_desc (isNF1_desc hb)) hlt
        rw [← omegaPow_eq] at hrlt
        obtain ⟨N, hN⟩ := ihr (isNF1_tail hb) hrlt
        exact ⟨N + 1, P_le_P_tail hN⟩

theorem cofW_zero : CofWStmt 0 := by
  intro A q hw hq
  have hlt : q < T.add q one := lt_add_of_ne q nofun
  have key : ∀ (A : List T), (∀ x ∈ A, Good x) → ∀ b, T.isNF1 b →
      b < cantorT (A ++ [T.add q one]) → ∃ k, b ≤ cantorT (A ++ List.replicate (k + 1) q) := by
    intro A
    induction A with
    | nil =>
        intro _ b hb hlt'
        rw [List.nil_append, cantorT_single] at hlt'
        obtain ⟨N, hN⟩ := rep0_cof hq b hb hlt'
        refine ⟨N, ?_⟩
        rw [List.nil_append, cantorT_replicate]
        exact le_tr hN (rep0_le_succ _ N)
    | cons a A ih =>
        intro hA b hb hlt'
        have ha := hA a List.mem_cons_self
        have hA' : ∀ x ∈ A, Good x := fun x hx => hA x (List.mem_cons_of_mem a hx)
        have hx := good_omegaPow ha
        have hU := good_cantorT' (A ++ [T.add q one]) (fun x hx' => by
          rcases List.mem_append.mp hx' with h | h
          · exact hA' x h
          · rw [List.mem_singleton.mp h]; exact good_add_one hq)
        change b < oadd (omegaPow a) (cantorT (A ++ [T.add q one])) at hlt'
        show ∃ k, b ≤ oadd (omegaPow a) (cantorT (A ++ List.replicate (k + 1) q))
        by_cases hbx : b < omegaPow a
        · exact ⟨0, le_tr (Or.inl hbx) (le_oadd_self hx.desc)⟩
        · have hou := good_oadd hx hU
          have hbg := good_of_lt_good hb hou hlt'
          have hxb := le_of_not_lt' hbx
          have hz := leftSub_lt_leftSub hx hbg hou hxb hlt'
          rw [leftSub_oadd] at hz
          obtain ⟨k, hk⟩ := ih hA' _ (good_leftSub hx hbg).nf hz
          refine ⟨k, ?_⟩
          rw [← oadd_leftSub hx hbg hxb]
          exact oadd_le_right hx.desc hk
  intro b hb hlt'
  rw [o_zero] at hlt'
  obtain ⟨k, hk⟩ := key A (fun x hx => hw.good (List.mem_append_left _ hx)) b hb hlt'
  refine ⟨k, ?_⟩
  show b ≤ o 0 (gExpand 0 (A ++ [T.add q one]) q k)
  rw [gExpand_zero_eq A _ q hlt k, o_zero]
  exact hk

/-! ### Expansions of a single letter -/

theorem gTP_single (m : Nat) {ℓ q : T} (hq : q < ℓ) : gTP m ([] ++ [ℓ]) q = none := by
  cases m with
  | zero => rw [gTP_zero_snoc [] ℓ q hq]; rfl
  | succ m =>
      exact gTP_R3 m [] ℓ q hq (fun x hx => absurd hx List.not_mem_nil)
        (fun x hx => absurd hx List.not_mem_nil)

theorem gExpand_single (m : Nat) {ℓ q : T} (hq : q < ℓ) (k : Nat) :
    gExpand m [ℓ] q k = List.replicate (k + 1) q := by
  have := gTP_single m hq
  unfold gExpand
  rw [show [ℓ] = [] ++ [ℓ] from rfl, this, List.dropLast_concat]
  exact repeat_single q (k + 1)

/-! ### Level `m + 1` -/

theorem succCond_T (A : List T) (q : T) : SuccCond A (T.add q one) q :=
  fun x _ => ⟨fun h => lt_add_one_le q x h,
    fun h => lt_of_le_of_lt' h (lt_add_of_ne q nofun)⟩

theorem lt_succ_T (q : T) : q < T.add q one := lt_add_of_ne q nofun

theorem expand_goodW (m : Nat) {A : List T} {q : T} (hw : GoodW m (A ++ [T.add q one]))
    (hq : Good q) (k : Nat) : GoodW m (gExpand m (A ++ [T.add q one]) q k) := by
  refine ⟨fun z hz => ?_, gExpand_NF m A (T.add q one) q k hw.2 (lt_succ_T q) (succCond_T A q)⟩
  have := mem_gExpand m _ q k z hz
  rw [List.dropLast_concat] at this
  rcases List.mem_append.mp this with h | h
  · exact hw.good (List.mem_append_left _ h)
  · rw [List.mem_singleton.mp h]; exact hq

/-- **R3**: no earlier letter is `≤ q`. -/
theorem cofW_R3 (m : Nat) (hC : CofWStmt m) {A : List T} {q : T}
    (hw : GoodW (m + 1) (A ++ [T.add q one])) (hq : Good q) (hR3 : ∀ x ∈ A, ¬ Le x q)
    (hexp : ∀ k, gExpand (m + 1) (A ++ [T.add q one]) q k =
      joinS q (List.replicate (k + 1) A ++ [[]])) :
    Cof (o (m + 1) (A ++ [T.add q one]))
      (fun k : Nat => o (m + 1) (gExpand (m + 1) (A ++ [T.add q one]) q k)) := by
  have hR : ∀ x ∈ A, q < x := fun x hx => by
    rcases lt_total_thm q x with h | h | h
    · exact h
    · exact absurd (Or.inl h) (hR3 x hx)
    · exact absurd (Or.inr h.symm) (hR3 x hx)
  have hAb : ∀ Q ∈ [A ++ [T.add q one]], AboveL q Q := fun Q hQ x hx => by
    rw [List.mem_singleton.mp hQ] at hx
    rcases List.mem_append.mp hx with h | h
    · exact hR x h
    · rw [List.mem_singleton.mp h]; exact lt_succ_T q
  obtain ⟨e0, gW0, gP0⟩ := o_joinS (n := m) (by simp) hAb hq (by rwa [joinS_singleton])
  rw [joinS_singleton] at e0
  have hP0 := gP0 _ (List.mem_singleton_self _)
  have hmapA : (A ++ [T.add q one]).map (fSh q) = A.map (fSh q) ++ [Z] := by
    rw [List.map_append, List.map_cons, List.map_nil, fSh_succ_self]
  rw [hmapA] at hP0
  have hY : vSh m q (A ++ [T.add q one]) = T.add (o (m + 1) (A.map (fSh q))) one := by
    unfold vSh; rw [hmapA, succLast (m + 1) hP0]
  have hYg : Good (o (m + 1) (A.map (fSh q))) := o_good (goodW_prefix hP0)
  have hvA : vSh m q A = o (m + 1) (A.map (fSh q)) := rfl
  generalize o (m + 1) (A.map (fSh q)) = Y at hY hYg hvA
  simp only [List.map_cons, List.map_nil, hY] at e0 gW0
  have hlimY := lim_single m (good_add_one hYg) (add_one_ne_Z Y)
  rw [minus1_lim (o_good gW0) hlimY] at e0
  intro b hb hlt'
  rw [e0] at hlt'
  obtain ⟨⟨z, hz, hzlt⟩, hbz⟩ := econt' m hq (o_good gW0) hlimY b hb hlt'
  obtain ⟨k, hk⟩ := hC [] Y gW0 hYg z hz.nf hzlt
  change z ≤ o m (gExpand m [T.add Y one] Y k) at hk
  rw [gExpand_single m (lt_succ_T Y) k] at hk
  refine ⟨k, ?_⟩
  show b ≤ o (m + 1) (gExpand (m + 1) (A ++ [T.add q one]) q k)
  have hwk : GoodW (m + 1) (joinS q (List.replicate (k + 1) A ++ [[]])) := by
    rw [← hexp k]; exact expand_goodW (m + 1) hw hq k
  rw [hexp k]
  have hab : ∀ Q ∈ List.replicate (k + 1) A ++ [[]], AboveL q Q := fun Q hQ x hx => by
    rcases List.mem_append.mp hQ with h | h
    · rw [(List.mem_replicate.mp h).2] at hx; exact hR x hx
    · rw [List.mem_singleton.mp h] at hx; cases hx
  obtain ⟨e1, gW1, _⟩ := o_joinS (by simp) hab hq hwk
  rw [List.map_append, List.map_replicate, hvA, List.map_cons, List.map_nil,
    show vSh m q [] = Z from o_nil _] at e1 gW1
  rw [e1, succLast m gW1]
  have g1 := o_good (goodW_prefix gW1)
  exact le_tr hbz (E_le (facts m) hq hz (good_minus1 (good_add_one g1))
    (le_tr hk (le_minus1_succ g1)))

/-- **R1**: the least letter `μ` is below `q`; the expansion happens in the last piece. -/
theorem cofW_R1 (m : Nat) {A : List T} {q : T}
    (ih : ∀ A' : List T, A'.length < A.length → ∀ q', GoodW (m + 1) (A' ++ [T.add q' one]) →
      Good q' → Cof (o (m + 1) (A' ++ [T.add q' one]))
        (fun k : Nat => o (m + 1) (gExpand (m + 1) (A' ++ [T.add q' one]) q' k)))
    (hw : GoodW (m + 1) (A ++ [T.add q one])) (hq : Good q) {μ : T} {Ps : List (List T)}
    {P' : List T} (hμA : μ ∈ A) (hPs : Ps ≠ [])
    (habove : ∀ Q ∈ Ps ++ [P' ++ [T.add q one]], AboveL μ Q)
    (hLeq : A ++ [T.add q one] = joinS μ (Ps ++ [P' ++ [T.add q one]]))
    (hP'A : ∀ z ∈ P', z ∈ A) (hlenP' : P'.length < A.length) (hμq : μ < q)
    (hexp : ∀ k, gExpand (m + 1) (A ++ [T.add q one]) q k =
      joinS μ (Ps ++ [gExpand (m + 1) (P' ++ [T.add q one]) q k])) :
    Cof (o (m + 1) (A ++ [T.add q one]))
      (fun k : Nat => o (m + 1) (gExpand (m + 1) (A ++ [T.add q one]) q k)) := by
  have hμg := hw.good (List.mem_append_left _ hμA)
  have hPabove : ∀ z ∈ P' ++ [T.add q one], μ < z := habove _ (by simp)
  obtain ⟨e0, gW0, gP0⟩ := o_joinS (by simp) habove hμg (hLeq ▸ hw)
  rw [← hLeq, List.map_append, List.map_cons, List.map_nil] at e0
  rw [List.map_append, List.map_cons, List.map_nil] at gW0
  have hX := gP0 _ (by simp : P' ++ [T.add q one] ∈ Ps ++ [P' ++ [T.add q one]])
  have hmapX : (P' ++ [T.add q one]).map (fSh μ) = P'.map (fSh μ) ++ [T.add (fSh μ q) one] := by
    rw [List.map_append, List.map_cons, List.map_nil, fSh_add_one hμg hq hμq]
  rw [hmapX] at hX
  have hIH := ih (P'.map (fSh μ)) (by rw [List.length_map]; exact hlenP') (fSh μ q) hX
    (good_fSh hμg hq)
  have hS : ∀ x ∈ (P' ++ [T.add q one]) ++ [q], Good x ∧ μ < x := by
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · refine ⟨hw.good ?_, hPabove x h⟩
      rcases List.mem_append.mp h with h' | h'
      · exact List.mem_append_left _ (hP'A x h')
      · exact List.mem_append_right _ h'
    · rw [List.mem_singleton.mp h]; exact ⟨hq, hμq⟩
  have hnat : ∀ k, (gExpand (m + 1) (P' ++ [T.add q one]) q k).map (fSh μ) =
      gExpand (m + 1) (P'.map (fSh μ) ++ [T.add (fSh μ q) one]) (fSh μ q) k := fun k => by
    rw [← hmapX]
    exact (gExpand_map (embOn_fSh hμg hS) (fun x hx => List.mem_append_left _ hx)
      (List.mem_append_right _ (List.mem_singleton_self q)) (m + 1) k).symm
  rw [show vSh m μ (P' ++ [T.add q one]) = o (m + 1) (P'.map (fSh μ) ++ [T.add (fSh μ q) one])
    by unfold vSh; rw [hmapX]] at e0 gW0
  have hglim := limLast (m + 1) hX (add_one_ne_Z _)
  have hL1 := limLast m gW0 (ne_of_lt'' ((facts (m + 1)).pos hX (by simp))).symm
  rw [minus1_lim (o_good gW0) hL1] at e0
  intro b hb hlt'
  rw [e0] at hlt'
  obtain ⟨⟨z1, hz1, hz1L⟩, hbz1⟩ := econt' m hμg (o_good gW0) hL1 b hb hlt'
  obtain ⟨⟨u, hu, hug⟩, hz1u⟩ := contLast m _ _ gW0 hglim z1 hz1.nf hz1L
  obtain ⟨k, hk⟩ := hIH u hu.nf hug
  refine ⟨k, ?_⟩
  show b ≤ o (m + 1) (gExpand (m + 1) (A ++ [T.add q one]) q k)
  have hwk : GoodW (m + 1) (joinS μ (Ps ++ [gExpand (m + 1) (P' ++ [T.add q one]) q k])) := by
    rw [← hexp k]; exact expand_goodW (m + 1) hw hq k
  rw [hexp k]
  have hab : ∀ Q ∈ Ps ++ [gExpand (m + 1) (P' ++ [T.add q one]) q k], AboveL μ Q := by
    intro Q hQ
    rcases List.mem_append.mp hQ with h | h
    · exact habove Q (List.mem_append_left _ h)
    · rw [List.mem_singleton.mp h]
      intro z hz
      have := mem_gExpand (m + 1) (P' ++ [T.add q one]) q k z hz
      rw [List.dropLast_concat] at this
      rcases List.mem_append.mp this with h | h
      · exact hPabove z (List.mem_append_left _ h)
      · rw [List.mem_singleton.mp h]; exact hμq
  obtain ⟨e1, gW1, gP1⟩ := o_joinS (by simp) hab hμg hwk
  have hP1 := gP1 _ (List.mem_append_right _ (List.mem_singleton_self _))
  rw [hnat k] at hP1
  rw [List.map_append, List.map_cons, List.map_nil, show vSh m μ (gExpand (m + 1)
    (P' ++ [T.add q one]) q k) = o (m + 1) (gExpand (m + 1) (P'.map (fSh μ) ++
      [T.add (fSh μ q) one]) (fSh μ q) k) by unfold vSh; rw [hnat k]] at e1 gW1
  rw [e1, minus1_lim (o_good gW1)
    (limLast m gW1 (ne_of_lt'' ((facts (m + 1)).pos hP1 (gExpand_ne_nil _ _ _ _))).symm)]
  exact le_tr hbz1 (E_le (facts m) hμg hz1 (o_good gW1)
    (le_tr hz1u (o_last_le (goodW_dec gW0 hu hug) gW1 hk)))

/-- **R2**: the least letter is `q`; the expansion runs one level down, on the pieces. -/
theorem cofW_R2 (m : Nat) (hC : CofWStmt m) {A : List T} {q : T}
    (hw : GoodW (m + 1) (A ++ [T.add q one])) (hq : Good q) {Ps : List (List T)} {P' : List T}
    (habove : ∀ Q ∈ Ps ++ [P' ++ [T.add q one]], AboveL q Q)
    (hLeq : A ++ [T.add q one] = joinS q (Ps ++ [P' ++ [T.add q one]]))
    (hmemA : ∀ Q ∈ Ps ++ [P'], ∀ z ∈ Q, z ∈ A)
    (hexp : ∀ k, gExpand (m + 1) (A ++ [T.add q one]) q k =
      joinS q (gExpand m (Ps ++ [P' ++ [T.add q one]]) P' k ++ [[]])) :
    Cof (o (m + 1) (A ++ [T.add q one]))
      (fun k : Nat => o (m + 1) (gExpand (m + 1) (A ++ [T.add q one]) q k)) := by
  obtain ⟨e0, gW0, gP0⟩ := o_joinS (by simp) habove hq (hLeq ▸ hw)
  rw [← hLeq] at e0
  have hX := gP0 _ (by simp : P' ++ [T.add q one] ∈ Ps ++ [P' ++ [T.add q one]])
  have hmapX : (P' ++ [T.add q one]).map (fSh q) = P'.map (fSh q) ++ [Z] := by
    rw [List.map_append, List.map_cons, List.map_nil, fSh_succ_self]
  rw [hmapX] at hX
  have hvP'g : Good (vSh m q P') := o_good (goodW_prefix hX)
  have hmapv : (Ps ++ [P' ++ [T.add q one]]).map (vSh m q) =
      Ps.map (vSh m q) ++ [T.add (vSh m q P') one] := by
    rw [List.map_append, List.map_cons, List.map_nil,
      show vSh m q (P' ++ [T.add q one]) = T.add (vSh m q P') one by
        unfold vSh; rw [hmapX, succLast (m + 1) hX]]
  rw [hmapv] at e0 gW0
  have hlimT := limLast m gW0 (add_one_ne_Z _)
  rw [minus1_lim (o_good gW0) hlimT] at e0
  have hSg : ∀ p ∈ (Ps ++ [P' ++ [T.add q one]]) ++ [P'],
      GoodW (m + 1) (p.map (fSh q)) ∧ ∀ x ∈ p, Good x ∧ q < x := by
    have hgA : ∀ x ∈ A, Good x := fun x hx => hw.good (List.mem_append_left _ hx)
    have hP'ab : ∀ x ∈ P', q < x :=
      fun x hx => habove (P' ++ [T.add q one]) (by simp) x (List.mem_append_left _ hx)
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · refine ⟨gP0 p h, fun x hx => ⟨?_, habove p h x hx⟩⟩
      rcases List.mem_append.mp h with h | h
      · exact hgA x (hmemA p (List.mem_append_left _ h) x hx)
      · rw [List.mem_singleton.mp h] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hgA x (hmemA P' (by simp) x hx)
        · rw [List.mem_singleton.mp hx]; exact good_add_one hq
    · rw [List.mem_singleton.mp h]
      exact ⟨goodW_prefix hX, fun x hx => ⟨hgA x (hmemA P' (by simp) x hx), hP'ab x hx⟩⟩
  have hnat : ∀ k, (gExpand m (Ps ++ [P' ++ [T.add q one]]) P' k).map (vSh m q) =
      gExpand m (Ps.map (vSh m q) ++ [T.add (vSh m q P') one]) (vSh m q P') k := fun k => by
    rw [← hmapv]
    exact (gExpand_map (fun p hp p' hp' h => o_mono (hSg p hp).1 (hSg p' hp').1
        (map_fSh_lt hq (hSg p hp).2 (hSg p' hp').2 h)) (fun x hx => List.mem_append_left _ hx)
      (List.mem_append_right _ (List.mem_singleton_self P')) m k).symm
  intro b hb hlt'
  rw [e0] at hlt'
  obtain ⟨⟨z, hz, hzlt⟩, hbz⟩ := econt' m hq (o_good gW0) hlimT b hb hlt'
  obtain ⟨k, hk⟩ := hC (Ps.map (vSh m q)) (vSh m q P') gW0 hvP'g z hz.nf hzlt
  refine ⟨k, ?_⟩
  show b ≤ o (m + 1) (gExpand (m + 1) (A ++ [T.add q one]) q k)
  have hwk : GoodW (m + 1) (joinS q (gExpand m (Ps ++ [P' ++ [T.add q one]]) P' k ++ [[]])) := by
    rw [← hexp k]; exact expand_goodW (m + 1) hw hq k
  rw [hexp k]
  have hab : ∀ Q ∈ gExpand m (Ps ++ [P' ++ [T.add q one]]) P' k ++ [[]], AboveL q Q := by
    intro Q hQ
    rcases List.mem_append.mp hQ with hQ | hQ
    · have := mem_gExpand m _ _ k Q hQ
      rw [List.dropLast_concat] at this
      rcases List.mem_append.mp this with h' | h'
      · exact habove Q (List.mem_append_left _ h')
      · rw [List.mem_singleton.mp h']
        exact fun z hz => habove (P' ++ [T.add q one]) (by simp) z (List.mem_append_left _ hz)
    · rw [List.mem_singleton.mp hQ]; intro z hz; cases hz
  obtain ⟨e1, gW1, _⟩ := o_joinS (by simp) hab hq hwk
  rw [List.map_append, List.map_cons, List.map_nil, show vSh m q [] = Z from o_nil _, hnat k]
    at e1 gW1
  rw [e1, succLast m gW1]
  have g1 := o_good (goodW_prefix gW1)
  exact le_tr hbz (E_le (facts m) hq hz (good_minus1 (good_add_one g1))
    (le_tr hk (le_minus1_succ g1)))

theorem cofW_succ (m : Nat) (hC : CofWStmt m) : CofWStmt (m + 1) := by
  suffices H : ∀ k (A : List T), A.length = k → ∀ q, GoodW (m + 1) (A ++ [T.add q one]) →
      Good q → Cof (o (m + 1) (A ++ [T.add q one]))
        (fun k : Nat => o (m + 1) (gExpand (m + 1) (A ++ [T.add q one]) q k)) from
    fun A q => H A.length A rfl q
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro A hk q hw hq
  rcases expand_cases m hw.2 (lt_succ_T q) (succCond_T A q) with ⟨hR3, hexp⟩ |
    ⟨μ, Ps, P', hμA, _, hPs, habove, hLeq, hmemA, hlenP', _, _, (⟨hμq, hexp⟩ | ⟨rfl, hexp⟩)⟩
  · exact cofW_R3 m hC hw hq hR3 hexp
  · exact cofW_R1 m (fun A' hA' q' hw' hq' => ih A'.length (hk ▸ hA') A' rfl q' hw' hq') hw hq
      hμA hPs habove hLeq (hmemA P' (by simp)) hlenP' hμq hexp
  · exact cofW_R2 m hC hw hq habove hLeq hmemA hexp

/-- **Cofinality of the expansions**, at every level. -/
theorem cofW : ∀ m, CofWStmt m
  | 0 => cofW_zero
  | m + 1 => cofW_succ m (cofW m)

end Sem
