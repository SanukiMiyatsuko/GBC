import Mbekworm.Sequence.SemPhi
import Mbekworm.Sequence.NormalForm

/-!
# The worm valuation is normal-form valued and strictly monotone
-/

open T GenBek

namespace Sem

/-!
## Normal forms and strict monotonicity of the worm valuation, level by level
-/

/-- Worms of level `n` over countable normal forms. -/
def GoodW (n : Nat) (w : List T) : Prop := (∀ x ∈ w, Good x) ∧ NF T n w

theorem GoodW.good {n : Nat} {w : List T} (h : GoodW n w) {x : T} (hx : x ∈ w) : Good x := h.1 x hx

theorem GoodW.single (n : Nat) {y : T} (hy : Good y) : GoodW n [y] :=
  ⟨fun x hx => by rw [List.mem_singleton.mp hx]; exact hy, Mbek.NF_singleton n y⟩

/-! ### The least letter -/

theorem tmin_spec {w : List T} (hw : w ≠ []) : tmin w ∈ w ∧ ∀ x ∈ w, tmin w ≤ x := by
  obtain ⟨μ, hμ⟩ := min?_isSome hw
  have hs := min?_spec hμ
  have : tmin w = μ := by simp [tmin, hμ]
  rw [this]
  exact ⟨hs.1, hs.2⟩

theorem tmin_eq_of {w : List T} {μ : T} (hμ : μ ∈ w) (h : ∀ x ∈ w, μ ≤ x) : tmin w = μ := by
  have hw : w ≠ [] := List.ne_nil_of_mem hμ
  have hs := tmin_spec hw
  exact le_antisymm' (hs.2 μ hμ) (h _ hs.1)

theorem tmin_map {w : List T} {f : T → T} (hw : w ≠ [])
    (hf : ∀ x ∈ w, ∀ y ∈ w, x ≤ y → f x ≤ f y) : tmin (w.map f) = f (tmin w) := by
  have hs := tmin_spec hw
  apply tmin_eq_of (List.mem_map_of_mem hs.1)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  exact hf _ hs.1 _ hx (hs.2 x hx)

theorem tmin_eq_Z_of_mem {w : List T} (h : Z ∈ w) : tmin w = Z :=
  tmin_eq_of h (fun x _ => Z_le' x)

/-! ### Small worms -/

theorem cantorT_single (y : T) : cantorT [y] = omegaPow y := by
  simp only [cantorT, oadd_Z_right]

theorem o_single_zero (y : T) : o 0 [y] = omegaPow y := by
  rw [o_zero, cantorT_single]

theorem leftSub_Z_fun : leftSub Z = id := by funext x; exact leftSub_Z_left x

theorem o_replicate : ∀ (n k : Nat), o n (List.replicate k Z) = T.ofNat k
  | n, 0 => o_nil n
  | 0, k + 1 => by
      rw [o_zero]
      induction k with
      | zero => rfl
      | succ k ih =>
          rw [List.replicate_succ, cantorT, ih, omegaPow_Z]
          show oadd (P 0 Z Z) (P 0 Z (T.ofNat k)) = P 0 Z (P 0 Z (T.ofNat k))
          rw [oadd_P_of_not_lt (lt_irr _), oadd_Z_left]
  | n + 1, k + 1 => by
      have hne : List.replicate (k + 1) Z ≠ [] := by simp
      have hmin : tmin (List.replicate (k + 1) Z) = Z := tmin_eq_Z_of_mem (by simp)
      rw [o_succ n _ hne, hmin, E_Z, leftSub_Z_fun, List.map_id]
      simp only [zs]
      rw [if_pos (by simp), Mbek.sepPieces_replicate]
      simp only [List.map_replicate, List.map_nil, o_nil]
      rw [o_replicate n (k + 2)]
      rfl

theorem o_single (n : Nat) (y : T) : o (n + 1) [y] = E (n + 1) y one := by
  rw [o_succ n _ (by simp)]
  have hmin : tmin [y] = y := tmin_eq_of (List.mem_singleton_self y) (fun x hx => by
    rw [List.mem_singleton.mp hx]; exact le_refl' _)
  rw [hmin]
  congr 1
  simp only [List.map_cons, List.map_nil, leftSub_self, zs]
  rw [if_pos (List.mem_singleton_self Z)]
  have : GenBek.sepPieces Z [Z] = [[], []] := by simp [GenBek.sepPieces]
  rw [this]
  simp only [List.map_cons, List.map_nil, o_nil]
  have h2 := o_replicate n 2
  simp only [List.replicate] at h2
  rw [h2]
  rfl

theorem Eom_succ_Z (n : Nat) (y : T) : Eom (n + 1) Z y = minus1 (o n [y]) := by
  cases n with
  | zero => simp only [Eom, if_pos, o_single_zero]
  | succ m => simp only [Eom, if_pos, o_single]

theorem Eom_succ_ne (n : Nat) {α : T} (hα : α ≠ Z) (y : T) :
    Eom (n + 1) α y = if y = Z then Z else phi n (if n = 0 then α else minus1 α) (minus1 y) := by
  cases n with
  | zero => simp only [Eom, if_neg hα, if_pos]
  | succ m => simp only [Eom, if_neg hα]; simp

theorem Eom_succ_Zarg (n : Nat) (α : T) : Eom (n + 1) α Z = Z := by
  by_cases hα : α = Z
  · subst hα
    rw [Eom_succ_Z, show [Z] = List.replicate 1 Z from rfl, o_replicate]
    rfl
  · rw [Eom_succ_ne n hα, if_pos rfl]

theorem logA_Z : logA Z = Z := rfl

theorem E_one (n : Nat) (y : T) : E n one y = Eom n Z y := by
  rw [show one = P 0 Z Z from rfl, E_P, logA_Z, E_Z]

theorem E_Zarg (n : Nat) : ∀ μ : T, E (n + 1) μ Z = Z
  | Z => E_Z _ _
  | P i c b => by rw [E_P, E_Zarg n b, Eom_succ_Zarg]

theorem o_lvl (n : Nat) {Φ : T} (h : Lvl n Φ) (hg : Good Φ) : o n [Φ] = Φ := by
  cases n with
  | zero => rw [o_single_zero]; exact h.omegaPow
  | succ m =>
      rw [o_single]
      obtain ⟨Y, rfl, hY, hb⟩ := h
      rw [E_P, E_Z, (show Lvl (m + 1) (P 0 Y Z) from ⟨Y, rfl, hY, hb⟩).logA,
        Eom_succ_ne m (by intro e; cases e)]
      rw [if_neg nofun]
      have hl : Lvl (m + 1) (P 0 Y Z) := ⟨Y, rfl, hY, hb⟩
      have hm1 : minus1 one = Z := rfl
      rw [hm1]
      split
      · exact phi_fix_lvl m hl hg
      · rw [hl.minus1]
        exact phi_fix_lvl m hl hg

/-! ### The induction over levels -/

/-- What we prove about the valuation of each level. -/
structure Facts (n : Nat) : Prop where
  good : ∀ w, GoodW n w → Good (o n w)
  mono : ∀ s t, GoodW n s → GoodW n t → s < t → o n s < o n t

theorem facts_zero : Facts 0 where
  good w hw := by rw [o_zero]; exact good_cantorT hw.1 hw.2
  mono s t hs ht h := by rw [o_zero, o_zero]; exact cantorT_lt hs.1 ht.1 hs.2 ht.2 h

theorem Facts.pos {n : Nat} (F : Facts n) {w : List T} (hw : GoodW n w) (hne : w ≠ []) :
    Z < o n w := by
  have := F.mono [] w ⟨fun _ h => absurd h List.not_mem_nil, Mbek.NF_nil n⟩ hw
    (by cases w with | nil => exact absurd rfl hne | cons a w => exact List.Lex.nil)
  rwa [o_nil] at this

theorem isNF1_head' {i : Nat} {c b : T} (h : T.isNF1 (P i c b)) : T.isNF1 (P i c Z) := by
  have h' := T.isNF1_P_inv _ _ _ h
  exact T.isNF1.p i c Z h'.1 T.isNF1.z h'.2.2.1 (T.Z_le _)

section succ
variable {n : Nat} (F : Facts n)
include F

theorem Eom_good {α y : T} (hα : Good α) (hy : Good y) : Good (Eom (n + 1) α y) := by
  by_cases h0 : α = Z
  · subst h0
    rw [Eom_succ_Z]
    exact good_minus1 (F.good _ (GoodW.single n hy))
  · rw [Eom_succ_ne n h0]
    split
    · exact good_Z
    · apply good_phi
      · split
        · exact hα
        · exact good_minus1 hα
      · exact good_minus1 hy
      · intro hn
        rw [if_pos hn]
        exact h0

theorem Eom_lt {α y y' : T} (hα : Good α) (hy : Good y) (hy' : Good y') (h : y < y') :
    Eom (n + 1) α y < Eom (n + 1) α y' := by
  by_cases h0 : α = Z
  · subst h0
    rw [Eom_succ_Z, Eom_succ_Z]
    apply minus1_lt_minus1 (F.good _ (GoodW.single n hy)) (F.good _ (GoodW.single n hy'))
    · exact ne_of_lt'' (F.pos (GoodW.single n hy) (by simp)) |>.symm
    · exact F.mono _ _ (GoodW.single n hy) (GoodW.single n hy') (List.Lex.rel h)
  · have hα' : Good (if n = 0 then α else minus1 α) := by
      split
      · exact hα
      · exact good_minus1 hα
    have hk : n = 0 → (if n = 0 then α else minus1 α) ≠ Z := by
      intro hn; rw [if_pos hn]; exact h0
    have hy'0 : y' ≠ Z := fun e => not_lt_Z' _ (e ▸ h)
    rw [Eom_succ_ne n h0, Eom_succ_ne n h0, if_neg hy'0]
    split
    · exact (phi_lvl _ _ _ hα' (good_minus1 hy')).ne_Z |> fun hne => by
        cases hp : phi n (if n = 0 then α else minus1 α) (minus1 y') with
        | Z => exact absurd hp hne
        | P _ _ _ => exact Z_lt_P' _ _ _
    · rename_i hy0
      apply phi_lt_phi n _ hα' (good_minus1 hy) (good_minus1 hy') hk
      exact minus1_lt_minus1 hy hy' hy0 h

theorem Eom_fix {α β y : T} (hα : Good α) (hβ : Good β) (hy : Good y) (h : α < β) :
    Eom (n + 1) α (Eom (n + 1) β y) = Eom (n + 1) β y := by
  have hβ0 : β ≠ Z := fun e => not_lt_Z' _ (e ▸ h)
  by_cases hy0 : y = Z
  · subst hy0; rw [Eom_succ_Zarg, Eom_succ_Zarg]
  have hβ' : Good (if n = 0 then β else minus1 β) := by
    split
    · exact hβ
    · exact good_minus1 hβ
  rw [Eom_succ_ne n hβ0, if_neg hy0]
  have hlvl := phi_lvl n (if n = 0 then β else minus1 β) (minus1 y) hβ' (good_minus1 hy)
  have hgood : Good (phi n (if n = 0 then β else minus1 β) (minus1 y)) := by
    apply good_phi _ _ _ hβ' (good_minus1 hy)
    intro hn; rw [if_pos hn]; exact hβ0
  by_cases h0 : α = Z
  · subst h0
    rw [Eom_succ_Z, o_lvl n hlvl hgood, hlvl.minus1]
  · rw [Eom_succ_ne n h0, if_neg hlvl.ne_Z, hlvl.minus1]
    have hα' : Good (if n = 0 then α else minus1 α) := by
      split
      · exact hα
      · exact good_minus1 hα
    apply phi_fix n hα' hβ' (good_minus1 hy)
    · intro hn; rw [if_pos hn]; exact h0
    · split
      · exact h
      · exact minus1_lt_minus1 hα hβ h0 h

theorem E_good : ∀ {μ x : T}, Good μ → Good x → Good (E (n + 1) μ x)
  | Z, x, _, hx => by rw [E_Z]; exact hx
  | P i c b, x, hμ, hx => by
      rw [E_P]
      have hi : i = 0 := hμ.cnt.idx
      subst hi
      exact Eom_good F (good_logA (isNF1_head' hμ.nf)) (E_good hμ.tail hx)

theorem E_lt : ∀ {μ x x' : T}, Good μ → Good x → Good x' → x < x' → E (n + 1) μ x < E (n + 1) μ x'
  | Z, x, x', _, _, _, h => by rw [E_Z, E_Z]; exact h
  | P i c b, x, x', hμ, hx, hx', h => by
      rw [E_P, E_P]
      have hi : i = 0 := hμ.cnt.idx
      subst hi
      exact Eom_lt F (good_logA (isNF1_head' hμ.nf)) (E_good F hμ.tail hx) (E_good F hμ.tail hx')
        (E_lt hμ.tail hx hx' h)

theorem E_le {μ x x' : T} (hμ : Good μ) (hx : Good x) (hx' : Good x') (h : x ≤ x') :
    E (n + 1) μ x ≤ E (n + 1) μ x' := by
  rcases h with h | rfl
  · exact Or.inl (E_lt F hμ hx hx' h)
  · exact le_refl' _

theorem E_absorb : ∀ {a b x : T}, Good a → Good b → Good x → (a = Z ∨ T.head a < T.head b) →
    E (n + 1) a (E (n + 1) b x) = E (n + 1) b x
  | Z, b, x, _, _, _, _ => by rw [E_Z]
  | P i c r, b, x, ha, hb, hx, hab => by
      have hlt : P i c Z < T.head b := by
        rcases hab with h | h
        · cases h
        · exact h
      rw [E_P, E_absorb ha.tail hb hx ?_]
      · cases b with
        | Z => exact absurd hlt (not_lt_Z' _)
        | P j d b' =>
            rw [E_P]
            have hi : i = 0 := ha.cnt.idx
            have hj : j = 0 := hb.cnt.idx
            subst hi hj
            have hcd : c < d := (lt_P0 hlt).2
            exact Eom_fix F (good_logA (isNF1_head' ha.nf)) (good_logA (isNF1_head' hb.nf))
              (E_good F hb.tail hx) (logA_lt_logA (isNF1_head' ha.nf) (isNF1_head' hb.nf) hcd)
      · cases r with
        | Z => exact Or.inl rfl
        | P j e f => exact Or.inr (lt_of_le_of_lt' ha.desc.hd hlt)

theorem E_comp : ∀ {a b x : T}, Good a → Good b → Good x →
    E (n + 1) (oadd a b) x = E (n + 1) a (E (n + 1) b x)
  | Z, b, x, _, _, _ => by rw [oadd_Z_left, E_Z]
  | P i c r, b, x, ha, hb, hx => by
      rw [oadd_P]
      split
      · rename_i h
        exact (E_absorb F ha hb hx (Or.inr h)).symm
      · rw [E_P, E_P, E_comp ha.tail hb hx]

end succ

/-! ### Pieces at `0` -/

/-- The values of the decremented pieces at the letter `0`. -/
def vals (n : Nat) (w : List T) : List T :=
  (sepPieces Z w).map (fun p => o (n + 1) (p.map minus1))

theorem zs_eq_vals (n : Nat) {w : List T} (h : Z ∈ w) : zs n w = minus1 (o n (vals n w)) := by
  simp only [zs, vals, if_pos h]

theorem allGe_Z (w : List T) : AllGe Z w := fun x _ => Z_le' x

theorem md_eq_Z {w : List T} (h : Z ∈ w) : List.md T w = sepPieces Z w :=
  Mbek.md_of_min h (allGe_Z w)

theorem two_le_length_sepPieces {μ : T} : ∀ {w : List T}, μ ∈ w → 2 ≤ (sepPieces μ w).length
  | [], h => absurd h List.not_mem_nil
  | x :: xs, h => by
      simp only [sepPieces]
      by_cases hx : x = μ
      · simp only [hx, ite_true, List.length_cons]
        have := (sepPieces_ne_nil μ xs)
        cases hs : sepPieces μ xs with
        | nil => exact absurd hs this
        | cons _ _ => simp
      · simp only [hx, ite_false]
        have hm : μ ∈ xs := by
          rcases List.mem_cons.mp h with h | h
          · exact absurd h.symm hx
          · exact h
        have ih := two_le_length_sepPieces hm
        cases hs : sepPieces μ xs with
        | nil => rw [hs] at ih; simp at ih
        | cons q qs => rw [hs] at ih; simpa [consHd] using ih

/-- Sum of the lengths of the pieces. -/
def lsum : List (List T) → Nat
  | [] => 0
  | p :: ps => p.length + lsum ps

theorem lsum_consHd (x : T) (ps : List (List T)) (h : ps ≠ []) :
    lsum (consHd x ps) = lsum ps + 1 := by
  cases ps with
  | nil => exact absurd rfl h
  | cons p ps => simp only [consHd, lsum, List.length_cons]; omega

theorem lsum_sepPieces (μ : T) : ∀ w : List T, lsum (sepPieces μ w) + w.count μ = w.length
  | [] => rfl
  | x :: xs => by
      have ih := lsum_sepPieces μ xs
      simp only [sepPieces]
      by_cases hx : x = μ
      · subst hx
        simp only [ite_true, lsum, List.length_nil, List.count_cons_self, List.length_cons]
        omega
      · simp only [hx, ite_false, List.length_cons]
        rw [lsum_consHd x _ (sepPieces_ne_nil μ xs)]
        have : List.count μ (x :: xs) = List.count μ xs := by
          simp [List.count_cons, hx]
        rw [this]; omega

theorem length_le_lsum : ∀ {ps : List (List T)} {q : List T}, q ∈ ps → q.length ≤ lsum ps
  | [], _, hq => absurd hq List.not_mem_nil
  | r :: ps, q, hq => by
      simp only [lsum]
      obtain h | h := List.mem_cons.mp hq
      · rw [h]; omega
      · have := length_le_lsum h; omega

theorem length_add_le_lsum : ∀ {ps : List (List T)} {p q : List T}, p ∈ ps → q ∈ ps → p ≠ q →
    p.length + q.length ≤ lsum ps
  | [], _, _, hp, _, _ => absurd hp List.not_mem_nil
  | r :: ps, p, q, hp, hq, hpq => by
      simp only [lsum]
      obtain h1 | h1 := List.mem_cons.mp hp
      · obtain h2 | h2 := List.mem_cons.mp hq
        · exact absurd (h1.trans h2.symm) hpq
        · have := length_le_lsum h2; rw [h1]; omega
      · obtain h2 | h2 := List.mem_cons.mp hq
        · have := length_le_lsum h1; rw [h2]; omega
        · have := length_add_le_lsum h1 h2 hpq; omega

theorem length_add_lt_of_pieces {w p q : List T} (hZ : Z ∈ w) (hp : p ∈ sepPieces Z w)
    (hq : q ∈ sepPieces Z w) (hpq : p ≠ q) : p.length + q.length < w.length := by
  have h1 := length_add_le_lsum hp hq hpq
  have h2 := lsum_sepPieces Z w
  have h3 : 0 < w.count Z := List.count_pos_iff.mpr hZ
  omega

theorem length_le_of_mem_sepPieces' (μ : T) (w : List T) :
    ∀ p ∈ sepPieces μ w, p.length ≤ w.length := by
  intro p hp
  have h1 := length_le_lsum hp
  have h2 := lsum_sepPieces μ w
  omega

theorem minus1_le_minus1 {x y : T} (hx : Good x) (hy : Good y) (hx0 : x ≠ Z) (h : x ≤ y) :
    minus1 x ≤ minus1 y := by
  rcases h with h | rfl
  · exact Or.inl (minus1_lt_minus1 hx hy hx0 h)
  · exact le_refl' _

theorem minus1_inj {x y : T} (hx : Good x) (hy : Good y) (hx0 : x ≠ Z) (hy0 : y ≠ Z)
    (h : minus1 x = minus1 y) : x = y := by
  rcases lt_total_thm x y with h' | h' | h'
  · exact absurd h (ne_of_lt'' (minus1_lt_minus1 hx hy hx0 h'))
  · exact absurd h.symm (ne_of_lt'' (minus1_lt_minus1 hy hx hy0 h'))
  · exact h'

theorem goodW_piece {n : Nat} {w p : List T} (hw : GoodW (n + 1) w) (hp : p ∈ sepPieces Z w) :
    GoodW (n + 1) (p.map minus1) := by
  have hmem : ∀ x ∈ p, x ∈ w ∧ x ≠ Z := fun x hx => mem_of_mem_sepPieces Z w p hp x hx
  have hpnf : NF T (n + 1) p := by
    by_cases hZ : Z ∈ w
    · have := (NF_succ_iff n w).mp hw.2
      rw [md_eq_Z hZ] at this
      exact this.2 p hp
    · rw [sepPieces_free Z w hZ, List.mem_singleton] at hp
      rw [hp]; exact hw.2
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact good_minus1 (hw.good (hmem x hx).1)
  · apply NF_map (n + 1) minus1 p hpnf
    intro x hx y hy hxy
    exact minus1_lt_minus1 (hw.good (hmem x hx).1) (hw.good (hmem y hy).1) (hmem x hx).2 hxy

theorem nf_pieces {n : Nat} {w : List T} (hw : GoodW (n + 1) w) (hZ : Z ∈ w) :
    NF (List T) n (sepPieces Z w) := by
  have := (NF_succ_iff n w).mp hw.2
  rw [md_eq_Z hZ] at this
  exact this.1

theorem minus1_map_lt {p q : List T} (hp : ∀ x ∈ p, Good x ∧ x ≠ Z) (hq : ∀ x ∈ q, Good x ∧ x ≠ Z)
    (h : p < q) : p.map minus1 < q.map minus1 :=
  map_lt_map (fun x hx y hy hxy => minus1_lt_minus1 (hp x hx).1 (hq y hy).1 (hp x hx).2 hxy)
    (fun x hx y hy e => minus1_inj (hp x hx).1 (hq y hy).1 (hp x hx).2 (hq y hy).2 e) h

/-- Goodness below a length. -/
def GoodBelow (n L : Nat) : Prop := ∀ w, GoodW n w → w.length < L → Good (o n w)

/-- Monotonicity below a total length. -/
def MonoBelow (n L : Nat) : Prop :=
  ∀ s t, GoodW n s → GoodW n t → s.length + t.length < L → s < t → o n s < o n t

theorem piece_letters {w p : List T} (hw : ∀ x ∈ w, Good x) (hp : p ∈ sepPieces Z w) :
    ∀ x ∈ p, Good x ∧ x ≠ Z := fun x hx =>
  ⟨hw x (mem_of_mem_sepPieces Z w p hp x hx).1, (mem_of_mem_sepPieces Z w p hp x hx).2⟩

theorem mem_map_leftSub_self {w : List T} {μ : T} (h : μ ∈ w) : Z ∈ w.map (leftSub μ) := by
  have := List.mem_map_of_mem (f := leftSub μ) h
  rwa [leftSub_self] at this

section succ2
variable {n : Nat} (F : Facts n)
include F

theorem vals_goodW {L : Nat} (hG : GoodBelow (n + 1) L) (hM : MonoBelow (n + 1) L) {w : List T}
    (hw : GoodW (n + 1) w) (hL : w.length ≤ L) (hZL : Z ∉ w → w.length < L) :
    GoodW n (vals n w) := by
  by_cases hZ : Z ∈ w
  · refine ⟨?_, ?_⟩
    · intro y hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
      apply hG _ (goodW_piece hw hp)
      rw [List.length_map]
      exact Nat.lt_of_lt_of_le (length_lt_of_mem_sepPieces Z w hZ p hp) hL
    · apply NF_map n _ _ (nf_pieces hw hZ)
      intro p hp q hq hpq
      have hne : p ≠ q := fun e => list_lt_irrefl' p (e ▸ hpq)
      apply hM _ _ (goodW_piece hw hp) (goodW_piece hw hq)
      · simp only [List.length_map]
        exact Nat.lt_of_lt_of_le (length_add_lt_of_pieces hZ hp hq hne) hL
      · exact minus1_map_lt (piece_letters hw.1 hp) (piece_letters hw.1 hq) hpq
  · simp only [vals, sepPieces_free Z w hZ, List.map_cons, List.map_nil]
    apply GoodW.single
    apply hG _ (goodW_piece hw (by rw [sepPieces_free Z w hZ]; exact List.mem_singleton_self w))
    rw [List.length_map]; exact hZL hZ

theorem zs_good {L : Nat} (hG : GoodBelow (n + 1) L) (hM : MonoBelow (n + 1) L) {w : List T}
    (hw : GoodW (n + 1) w) (hZ : Z ∈ w) (hL : w.length ≤ L) : Good (zs n w) := by
  rw [zs_eq_vals n hZ]
  exact good_minus1 (F.good _ (vals_goodW F hG hM hw hL (fun h => absurd hZ h)))

theorem goodW_leftSub {w : List T} {ν : T} (hw : GoodW (n + 1) w) (hν : Good ν)
    (h : ∀ x ∈ w, ν ≤ x) : GoodW (n + 1) (w.map (leftSub ν)) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact good_leftSub hν (hw.good hx)
  · apply NF_map (n + 1) _ _ hw.2
    intro x hx y hy hxy
    exact leftSub_lt_leftSub hν (hw.good hx) (hw.good hy) (h x hx) hxy

theorem o_shift {L : Nat} (hG : GoodBelow (n + 1) L) (hM : MonoBelow (n + 1) L) {w : List T}
    {ν : T} (hw : GoodW (n + 1) w) (hν : Good ν) (h : ∀ x ∈ w, ν ≤ x) (hL : w.length ≤ L) :
    o (n + 1) w = E (n + 1) ν (o (n + 1) (w.map (leftSub ν))) := by
  by_cases hne : w = []
  · subst hne; simp only [List.map_nil, o_nil, E_Zarg]
  have hs := tmin_spec hne
  have hμ : Good (tmin w) := hw.good hs.1
  have hne' : w.map (leftSub ν) ≠ [] := by simpa using hne
  have hmin : tmin (w.map (leftSub ν)) = leftSub ν (tmin w) :=
    tmin_map hne (fun x hx y hy hxy => leftSub_le_leftSub hν (hw.good hx) (hw.good hy) (h x hx) hxy)
  rw [o_succ n w hne, o_succ n _ hne', hmin, List.map_map]
  have hcomp : (w.map (leftSub (leftSub ν (tmin w)) ∘ leftSub ν)) = w.map (leftSub (tmin w)) := by
    apply List.map_congr_left
    intro x hx
    exact leftSub_leftSub hν hμ (hw.good hx) (h _ hs.1) (hs.2 x hx)
  rw [hcomp]
  have hX : Good (zs n (w.map (leftSub (tmin w)))) :=
    zs_good F hG hM (goodW_leftSub F hw hμ hs.2) (mem_map_leftSub_self hs.1) (by simpa using hL)
  rw [← E_comp F hν (good_leftSub hν hμ) hX, oadd_leftSub hν hμ (h _ hs.1)]

theorem o_zsplit {L : Nat} (hG : GoodBelow (n + 1) L) (hM : MonoBelow (n + 1) L) {w : List T}
    (hw : GoodW (n + 1) w) (hZ : Z ∉ w) (hne : w ≠ []) (hL : w.length ≤ L) :
    o (n + 1) w = minus1 (o n [o (n + 1) (w.map minus1)]) := by
  have hs := tmin_spec hne
  have hμ : Good (tmin w) := hw.good hs.1
  have hμ0 : tmin w ≠ Z := fun e => hZ (e ▸ hs.1)
  have hne' : w.map minus1 ≠ [] := by simpa using hne
  have hx0 : ∀ x ∈ w, x ≠ Z := fun x hx e => hZ (e ▸ hx)
  have hmin : tmin (w.map minus1) = minus1 (tmin w) :=
    tmin_map hne (fun x hx y hy hxy => minus1_le_minus1 (hw.good hx) (hw.good hy) (hx0 x hx) hxy)
  rw [o_succ n (w.map minus1) hne', hmin, List.map_map]
  have hcomp : (w.map (leftSub (minus1 (tmin w)) ∘ minus1)) = w.map (leftSub (tmin w)) := by
    apply List.map_congr_left
    intro x hx
    exact leftSub_minus1 hμ (hw.good hx) hμ0 (hs.2 x hx)
  rw [hcomp, ← Eom_succ_Z, ← E_one]
  have hX : Good (zs n (w.map (leftSub (tmin w)))) :=
    zs_good F hG hM (goodW_leftSub F hw hμ hs.2) (mem_map_leftSub_self hs.1) (by simpa using hL)
  rw [← E_comp F good_one (good_minus1 hμ) hX, oadd_one_minus1 hμ hμ0, o_succ n w hne]

theorem o_vals {L : Nat} (hG : GoodBelow (n + 1) L) (hM : MonoBelow (n + 1) L) {w : List T}
    (hw : GoodW (n + 1) w) (hL : w.length ≤ L) : o (n + 1) w = minus1 (o n (vals n w)) := by
  by_cases hZ : Z ∈ w
  · have hne : w ≠ [] := List.ne_nil_of_mem hZ
    rw [o_succ n w hne, tmin_eq_Z_of_mem hZ, E_Z, leftSub_Z_fun, List.map_id, zs_eq_vals n hZ]
  · by_cases hne : w = []
    · subst hne
      simp only [vals, sepPieces, List.map_cons, List.map_nil, o_nil]
      rw [show [Z] = List.replicate 1 Z from rfl, o_replicate]
      rfl
    · rw [o_zsplit F hG hM hw hZ hne hL]
      simp only [vals, sepPieces_free Z w hZ, List.map_cons, List.map_nil]

theorem one_lt_o_vals {L : Nat} (hG : GoodBelow (n + 1) L) (hM : MonoBelow (n + 1) L)
    {w : List T} (hw : GoodW (n + 1) w) (hZ : Z ∈ w) (hL : w.length ≤ L) :
    one < o n (vals n w) := by
  have hv := vals_goodW F hG hM hw hL (fun h => absurd hZ h)
  have h2 := two_le_length_sepPieces hZ
  have hlt : [Z] < vals n w := by
    simp only [vals]
    cases hp : sepPieces Z w with
    | nil => rw [hp] at h2; simp at h2
    | cons p ps =>
        cases ps with
        | nil => rw [hp] at h2; simp at h2
        | cons q qs =>
            simp only [List.map_cons]
            rcases Z_le' (o (n + 1) (p.map minus1)) with h | h
            · exact List.Lex.rel h
            · rw [← h]; exact List.Lex.cons List.Lex.nil
  have := F.mono [Z] _ (GoodW.single n good_Z) hv hlt
  rwa [show [Z] = List.replicate 1 Z from rfl, o_replicate] at this

theorem o_pos {L : Nat} (hG : GoodBelow (n + 1) L) (hM : MonoBelow (n + 1) L) {w : List T}
    (hw : GoodW (n + 1) w) (hne : w ≠ []) (hL : w.length ≤ L) : Z < o (n + 1) w := by
  have hs := tmin_spec hne
  have hμ : Good (tmin w) := hw.good hs.1
  have hw' := goodW_leftSub F hw hμ hs.2
  have hZ := mem_map_leftSub_self hs.1 (w := w)
  have hL' : (w.map (leftSub (tmin w))).length ≤ L := by simpa using hL
  rw [o_succ n w hne, zs_eq_vals n hZ]
  have h1 := one_lt_o_vals F hG hM hw' hZ hL'
  have hv := vals_goodW F hG hM hw' hL' (fun h => absurd hZ h)
  have h2 : Z < minus1 (o n (vals n (w.map (leftSub (tmin w))))) := by
    have := minus1_lt_minus1 good_one (F.good _ hv) nofun h1
    exact this
  have := E_lt F hμ good_Z (good_minus1 (F.good _ hv)) h2
  rwa [E_Zarg] at this

end succ2

section succ3
variable {n : Nat} (F : Facts n)
include F

theorem mono_step {L : Nat} (hG : GoodBelow (n + 1) L) (hM : MonoBelow (n + 1) L) {s t : List T}
    (hs : GoodW (n + 1) s) (ht : GoodW (n + 1) t) (hL : s.length + t.length ≤ L) (h : s < t) :
    o (n + 1) s < o (n + 1) t := by
  have htne : t ≠ [] := by
    intro e; subst e; exact List.not_lex_nil h
  have hpos_t : 0 < t.length := List.length_pos_iff.mpr htne
  by_cases hsne : s = []
  · subst hsne
    rw [o_nil]
    exact o_pos F hG hM ht htne (by simp only [List.length_nil] at hL; omega)
  have hpos_s : 0 < s.length := List.length_pos_iff.mpr hsne
  have hss := tmin_spec hsne
  have hts := tmin_spec htne
  -- the common lower bound
  obtain ⟨κ, hκ, hκs, hκt, hκm⟩ : ∃ κ, Good κ ∧ (∀ x ∈ s, κ ≤ x) ∧ (∀ x ∈ t, κ ≤ x) ∧
      (κ ∈ s ∨ κ ∈ t) := by
    by_cases hle : tmin s ≤ tmin t
    · exact ⟨tmin s, hs.good hss.1, hss.2, fun x hx => le_tr hle (hts.2 x hx), Or.inl hss.1⟩
    · have hle' : tmin t ≤ tmin s := Or.inl (by
        rcases lt_total_thm (tmin s) (tmin t) with h' | h' | h'
        · exact absurd (Or.inl h') hle
        · exact h'
        · exact absurd (Or.inr h') hle)
      exact ⟨tmin t, ht.good hts.1, fun x hx => le_tr hle' (hss.2 x hx), hts.2, Or.inr hts.1⟩
  have hsL : s.length ≤ L := by omega
  have htL : t.length ≤ L := by omega
  rw [o_shift F hG hM hs hκ hκs hsL, o_shift F hG hM ht hκ hκt htL]
  have hs' := goodW_leftSub F hs hκ hκs
  have ht' := goodW_leftSub F ht hκ hκt
  have hs'L : (s.map (leftSub κ)).length ≤ L := by simpa using hsL
  have ht'L : (t.map (leftSub κ)).length ≤ L := by simpa using htL
  rw [o_vals F hG hM hs' hs'L, o_vals F hG hM ht' ht'L]
  have hvs := vals_goodW F hG hM hs' hs'L (fun _ => by simp only [List.length_map]; omega)
  have hvt := vals_goodW F hG hM ht' ht'L (fun _ => by simp only [List.length_map]; omega)
  apply E_lt F hκ (good_minus1 (F.good _ hvs)) (good_minus1 (F.good _ hvt))
  apply minus1_lt_minus1 (F.good _ hvs) (F.good _ hvt)
  · exact (ne_of_lt'' (F.pos hvs (by simp [vals, sepPieces_ne_nil]))).symm
  apply F.mono _ _ hvs hvt
  -- comparing the pieces
  have hlt' : s.map (leftSub κ) < t.map (leftSub κ) := by
    apply map_lt_map
    · intro x hx y hy hxy
      exact leftSub_lt_leftSub hκ (hs.good hx) (ht.good hy) (hκs x hx) hxy
    · intro x hx y hy e
      rcases lt_total_thm x y with h' | h' | h'
      · exact absurd e (ne_of_lt'' (leftSub_lt_leftSub hκ (hs.good hx) (ht.good hy) (hκs x hx) h'))
      · exact absurd e.symm
          (ne_of_lt'' (leftSub_lt_leftSub hκ (ht.good hy) (hs.good hx) (hκt y hy) h'))
      · exact h'
    · exact h
  have hZ' : Z ∈ s.map (leftSub κ) ∨ Z ∈ t.map (leftSub κ) := by
    rcases hκm with h' | h'
    · exact Or.inl (mem_map_leftSub_self h')
    · exact Or.inr (mem_map_leftSub_self h')
  have hlen : ∀ p ∈ sepPieces Z (s.map (leftSub κ)), ∀ q ∈ sepPieces Z (t.map (leftSub κ)),
      (p.map minus1).length + (q.map minus1).length < L := by
    intro p hp q hq
    simp only [List.length_map]
    have h1 := length_le_of_mem_sepPieces' Z _ p hp
    have h2 := length_le_of_mem_sepPieces' Z _ q hq
    simp only [List.length_map] at h1 h2
    rcases hZ' with hZ | hZ
    · have := length_lt_of_mem_sepPieces Z _ hZ p hp
      simp only [List.length_map] at this
      omega
    · have := length_lt_of_mem_sepPieces Z _ hZ q hq
      simp only [List.length_map] at this
      omega
  have hmono : ∀ p ∈ sepPieces Z (s.map (leftSub κ)), ∀ q ∈ sepPieces Z (t.map (leftSub κ)),
      p < q → o (n + 1) (p.map minus1) < o (n + 1) (q.map minus1) := by
    intro p hp q hq hpq
    exact hM _ _ (goodW_piece hs' hp) (goodW_piece ht' hq) (hlen p hp q hq)
      (minus1_map_lt (piece_letters hs'.1 hp) (piece_letters ht'.1 hq) hpq)
  have hmono' : ∀ q ∈ sepPieces Z (t.map (leftSub κ)), ∀ p ∈ sepPieces Z (s.map (leftSub κ)),
      q < p → o (n + 1) (q.map minus1) < o (n + 1) (p.map minus1) := by
    intro q hq p hp hqp
    have := hlen p hp q hq
    exact hM _ _ (goodW_piece ht' hq) (goodW_piece hs' hp) (by omega)
      (minus1_map_lt (piece_letters ht'.1 hq) (piece_letters hs'.1 hp) hqp)
  simp only [vals]
  apply map_lt_map hmono
  · intro p hp q hq e
    rcases List.strictLinearTotal p q with h' | h' | h'
    · exact absurd e (ne_of_lt'' (hmono p hp q hq h'))
    · exact absurd e.symm (ne_of_lt'' (hmono' q hq p hp h'))
    · exact h'
  · exact (sepPieces_lt_iff (allGe_Z _) (allGe_Z _)).mp hlt'

theorem good_step {L : Nat} (hG : GoodBelow (n + 1) L) (hM : MonoBelow (n + 1) L) {w : List T}
    (hw : GoodW (n + 1) w) (hL : w.length ≤ L) : Good (o (n + 1) w) := by
  by_cases hne : w = []
  · subst hne; rw [o_nil]; exact good_Z
  have hs := tmin_spec hne
  have hμ := hw.good hs.1
  rw [o_succ n w hne]
  exact E_good F hμ (zs_good F hG hM (goodW_leftSub F hw hμ hs.2) (mem_map_leftSub_self hs.1)
    (by simpa using hL))

theorem below_all : ∀ L, GoodBelow (n + 1) L ∧ MonoBelow (n + 1) L
  | 0 => ⟨fun _ _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | L + 1 => by
      obtain ⟨hG, hM⟩ := below_all L
      exact ⟨fun w hw hL => good_step F hG hM hw (Nat.le_of_lt_succ hL),
        fun s t hs ht hL h => mono_step F hG hM hs ht (Nat.le_of_lt_succ hL) h⟩

theorem facts_succ : Facts (n + 1) where
  good w hw := (below_all F (w.length + 1)).1 w hw (Nat.lt_succ_self _)
  mono s t hs ht h := (below_all F (s.length + t.length + 1)).2 s t hs ht (Nat.lt_succ_self _) h

end succ3

/-- **The valuation of every level is normal-form valued and strictly monotone.** -/
theorem facts : ∀ n, Facts n
  | 0 => facts_zero
  | n + 1 => facts_succ (facts n)

end Sem
