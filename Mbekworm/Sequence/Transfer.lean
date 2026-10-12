import Mbekworm.MbekRank1.Basic
import Mbekworm.Sequence.NormalForm

/-!
# Transfer of the order type along `expand`

If a translation `tr : List Nat → T` of the `expand M` system into rank-one Buchholz
terms is injective on `OT M`, lands in normal forms below `bound`, sends removal of a
trailing `0` to an immediate predecessor, sends the other expansions to a sequence below
`tr s` and cofinal in it, and sends the starting points `[k]` to a sequence cofinal in
`bound`, then `OT M` is order-isomorphic to the normal forms below `bound`.  The inverse
is found by a search through an enumeration of `OT M`; nothing uses choice.
-/

open T GenBek

namespace Mbek

/-! ### Basic facts about `expand` and `isOT` -/

theorem expand_append_zero (M : Nat) (s : List Nat) (n : Nat) :
    expand M (s ++ [0]) n = s := by
  simp [expand]

/-- The prefix of every expansion of `s ++ [c + 1]`. -/
theorem expand_append_succ_eq (M : Nat) (s : List Nat) (c n : Nat) :
    ∃ r, expand M (s ++ [c + 1]) n = (s ++ [c]) ++ r := by
  have hlast : (s ++ [c + 1]).getLast? = some (c + 1) := by simp
  have hinit : (s ++ [c + 1]).dropLast = s := by simp
  unfold expand
  simp only [hinit, hlast]
  split
  · cases n with
    | zero => exact ⟨[], by simp [List.repeat]⟩
    | succ n => exact ⟨List.repeat (n + 1) (s ++ [c]), by simp [List.repeat, List.replicate_succ]⟩
  · exact ⟨_, rfl⟩

theorem expand_append_succ_lt (M : Nat) (s : List Nat) (c n : Nat) :
    expand M (s ++ [c + 1]) n < s ++ [c + 1] := by
  obtain ⟨r, hr⟩ := expand_append_succ_eq M s c n
  rw [hr, List.append_assoc]
  exact list_append_lt_left s (List.Lex.rel (Nat.lt_succ_self c))

theorem list_eq_nil_or_append (s : List Nat) : s = [] ∨ ∃ t a, s = t ++ [a] := by
  cases h : s.getLast? with
  | none => exact Or.inl (List.getLast?_eq_none_iff.mp h)
  | some a =>
      obtain ⟨t, ht⟩ := List.getLast?_eq_some_iff.mp h
      exact Or.inr ⟨t, a, ht⟩

theorem isOT_expand {M : Nat} {s : List Nat} (h : isOT M s) (n : Nat) : isOT M (expand M s n) :=
  isOT.step s h n

theorem isOT_init {M : Nat} {s : List Nat} (h : isOT M (s ++ [0])) : isOT M s := by
  have := isOT.step _ h 0
  rwa [expand_append_zero] at this

/-! ### Rank-one facts -/

theorem T.not_lt_Z (b : T) : ¬ b < Z := fun h => lt_Z_inv h

/-! ### A choice-free search -/

section find
variable (p : Nat → Prop) [DecidablePred p]

/-- One more step of an unsuccessful search. -/
def Lbp (m n : Nat) : Prop := m = n + 1 ∧ ∀ k, k ≤ n → ¬ p k

theorem lbp_wf (h : ∃ n, p n) : WellFounded (Lbp p) := by
  obtain ⟨n0, hn0⟩ := h
  have key : ∀ d n, n0 ≤ n + d → Acc (Lbp p) n := by
    intro d
    induction d with
    | zero => exact fun n hn => ⟨n, fun m hm => absurd hn0 (hm.2 n0 (by omega))⟩
    | succ d ih => exact fun n hn => ⟨n, fun m hm => hm.1 ▸ ih (n + 1) (by omega)⟩
  exact ⟨fun n => key n0 n (by omega)⟩

/-- A witness of a decidable existential over `ℕ`. -/
def findNat (h : ∃ n, p n) : {n // p n} :=
  (lbp_wf p h).fix (C := fun k => (∀ j, j < k → ¬ p j) → {n // p n})
    (fun k IH hk => if hp : p k then ⟨k, hp⟩ else
      have hk' : ∀ j, j < k + 1 → ¬ p j := fun j hj =>
        (Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj)).elim (hk j) (fun e => e ▸ hp)
      IH (k + 1) ⟨rfl, fun j hj => hk' j (Nat.lt_succ_of_le hj)⟩ hk')
    0 (fun j hj => absurd hj (Nat.not_lt_zero j))

end find

/-- A witness of a decidable existential over a list. -/
def findIn {α : Type} (p : α → Prop) [DecidablePred p] :
    (l : List α) → (∃ x, x ∈ l ∧ p x) → {x // x ∈ l ∧ p x}
  | [], h => absurd h (by rintro ⟨x, hx, _⟩; exact absurd hx List.not_mem_nil)
  | a :: l, h =>
      if ha : p a then ⟨a, List.mem_cons_self, ha⟩
      else
        let r := findIn p l (by
          obtain ⟨x, hx, hpx⟩ := h
          rcases List.mem_cons.mp hx with rfl | hx
          · exact absurd hpx ha
          · exact ⟨x, hx, hpx⟩)
        ⟨r.1, List.mem_cons_of_mem a r.2.1, r.2.2⟩

/-! ### Enumerating `OT M` -/

/-- The lists of length `l` with entries `≤ N`. -/
def allLen (N : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | l + 1 => (allLen N l).flatMap (fun xs => (List.range (N + 1)).map (fun a => a :: xs))

/-- The lists of length `≤ N` with entries `≤ N`. -/
def cand (N : Nat) : List (List Nat) := (List.range (N + 1)).flatMap (allLen N)

theorem mem_allLen (N : Nat) : ∀ c : List Nat, (∀ x ∈ c, x ≤ N) → c ∈ allLen N c.length
  | [], _ => List.mem_singleton_self _
  | a :: c, h => by
      show a :: c ∈ (allLen N c.length).flatMap (fun xs => (List.range (N + 1)).map (fun a => a :: xs))
      rw [List.mem_flatMap]
      refine ⟨c, mem_allLen N c (fun x hx => h x (List.mem_cons_of_mem a hx)), ?_⟩
      rw [List.mem_map]
      exact ⟨a, List.mem_range.mpr (Nat.lt_succ_of_le (h a List.mem_cons_self)), rfl⟩

theorem le_sum_of_mem' : ∀ {c : List Nat} {x : Nat}, x ∈ c → x ≤ c.sum
  | a :: c, x, h => by
      rw [List.sum_cons]
      rcases List.mem_cons.mp h with rfl | h
      · omega
      · have := le_sum_of_mem' h; omega

theorem mem_cand (c : List Nat) : c ∈ cand (c.length + c.sum) := by
  unfold cand
  rw [List.mem_flatMap]
  refine ⟨c.length, List.mem_range.mpr (by omega), ?_⟩
  exact mem_allLen _ c (fun x hx => by have := le_sum_of_mem' hx; omega)

/-- A code `k :: ns` stands for `[k]` expanded successively at `ns`. -/
def decodeOT (M : Nat) (c : List Nat) : List Nat :=
  c.tail.foldl (fun s n => expand M s n) [c.headD 0]

theorem isOT_foldl (M : Nat) : ∀ (ns s : List Nat), isOT M s →
    isOT M (ns.foldl (fun s n => expand M s n) s)
  | [], _, h => h
  | n :: ns, s, h => isOT_foldl M ns _ (isOT.step s h n)

theorem isOT_decodeOT (M : Nat) (c : List Nat) : isOT M (decodeOT M c) :=
  isOT_foldl M _ _ (isOT.base _)

theorem decodeOT_surj (M : Nat) {s : List Nat} (h : isOT M s) : ∃ c, decodeOT M c = s := by
  suffices H : ∃ (k : Nat) (ns : List Nat), ns.foldl (fun s n => expand M s n) [k] = s by
    obtain ⟨k, ns, e⟩ := H
    exact ⟨k :: ns, e⟩
  induction h with
  | base k => exact ⟨k, [], rfl⟩
  | step s _ n ih =>
      obtain ⟨k, ns, e⟩ := ih
      exact ⟨k, ns ++ [n], by rw [List.foldl_append, e]; rfl⟩

/-! ### Translations with an injectivity hypothesis -/

/-- The data of an injective translation of `OT M` into rank-one normal forms below `bound`. -/
structure Translation (M : Nat) (bound : T) where
  tr : List Nat → T
  tr_nil : tr [] = Z
  tr_isNF1 : ∀ s, isOT M s → T.isNF1 (tr s)
  tr_lt_bound : ∀ s, isOT M s → tr s < bound
  tr_inj : ∀ s t, isOT M s → isOT M t → tr s = tr t → s = t
  tr_succ_lt : ∀ s, isOT M (s ++ [0]) → tr s < tr (s ++ [0])
  tr_succ_le : ∀ s b, isOT M (s ++ [0]) → T.isNF1 b → b < tr (s ++ [0]) → b < tr s ∨ b = tr s
  tr_expand_lt : ∀ s c n, isOT M (s ++ [c + 1]) →
    tr (expand M (s ++ [c + 1]) n) < tr (s ++ [c + 1])
  tr_expand_cofinal : ∀ s c b, isOT M (s ++ [c + 1]) → T.isNF1 b → b < tr (s ++ [c + 1]) →
    ∃ n, b < tr (expand M (s ++ [c + 1]) n) ∨ b = tr (expand M (s ++ [c + 1]) n)
  top_cofinal : ∀ b, T.isNF1 b → b < bound → ∃ k, b < tr [k] ∨ b = tr [k]

namespace Translation

variable {M : Nat} {bound : T} (D : Translation M bound)

/-- Everything below a translated element is the translation of a smaller element. -/
theorem below_aux : ∀ a : T.NF1, ∀ t, isOT M t → D.tr t = a.val →
    ∀ b, T.isNF1 b → b < D.tr t → ∃ s, isOT M s ∧ D.tr s = b ∧ s < t := by
  intro a
  induction a using T.well_founded_NF1.induction with
  | h a ih =>
      intro t ht hta b hb hlt
      have step : ∀ t', isOT M t' → D.tr t' < D.tr t → t' < t → (b < D.tr t' ∨ b = D.tr t') →
          ∃ s, isOT M s ∧ D.tr s = b ∧ s < t := fun t' ht' h1 h2 hb' => by
        rcases hb' with hb' | rfl
        · obtain ⟨s, hs, e, hst⟩ := ih ⟨_, D.tr_isNF1 t' ht'⟩ (hta ▸ h1) t' ht' rfl b hb hb'
          exact ⟨s, hs, e, list_lt_trans' hst h2⟩
        · exact ⟨t', ht', rfl, h2⟩
      rcases list_eq_nil_or_append t with rfl | ⟨t', c, rfl⟩
      · rw [D.tr_nil] at hlt; exact absurd hlt (T.not_lt_Z _)
      · cases c with
        | zero =>
            exact step t' (isOT_init ht) (D.tr_succ_lt t' ht) (list_prefix_lt' t' 0 [])
              (D.tr_succ_le t' b ht hb hlt)
        | succ c =>
            obtain ⟨n, hn⟩ := D.tr_expand_cofinal t' c b ht hb hlt
            exact step _ (isOT_expand ht n) (D.tr_expand_lt t' c n ht)
              (expand_append_succ_lt M t' c n) hn

theorem tr_lt_iff {s t : List Nat} (hs : isOT M s) (ht : isOT M t) :
    D.tr s < D.tr t ↔ s < t := by
  have reflect : ∀ {s t}, isOT M s → isOT M t → D.tr s < D.tr t → s < t := fun hs ht h => by
    obtain ⟨s', hs', e, hlt⟩ := D.below_aux ⟨_, D.tr_isNF1 _ ht⟩ _ ht rfl _ (D.tr_isNF1 _ hs) h
    rwa [← D.tr_inj _ _ hs' hs e]
  refine ⟨reflect hs ht, fun h => ?_⟩
  rcases lt_total_thm (D.tr s) (D.tr t) with h' | h' | h'
  · exact h'
  · exact absurd (list_lt_trans' h (reflect ht hs h')) (list_lt_irrefl' s)
  · rw [D.tr_inj s t hs ht h'] at h; exact absurd h (list_lt_irrefl' t)

theorem surj (b : T) (hb : T.isNF1 b) (hbound : b < bound) : ∃ s, isOT M s ∧ D.tr s = b := by
  obtain ⟨k, hk | rfl⟩ := D.top_cofinal b hb hbound
  · obtain ⟨s, hs, e, -⟩ := D.below_aux ⟨_, D.tr_isNF1 _ (isOT.base k)⟩ _ (isOT.base k) rfl b hb hk
    exact ⟨s, hs, e⟩
  · exact ⟨[k], isOT.base k, rfl⟩

/-- The preimage of a normal form below `bound`, found by search. -/
def preimage (b : {t : T // T.isNF1 t ∧ t < bound}) :
    {s : List Nat // isOT M s ∧ D.tr s = b.1} :=
  have hN : ∃ N, ∃ c, c ∈ cand N ∧ D.tr (decodeOT M c) = b.1 := by
    obtain ⟨s, hs, e⟩ := D.surj b.1 b.2.1 b.2.2
    obtain ⟨c, hc⟩ := decodeOT_surj M hs
    exact ⟨_, c, mem_cand c, by rw [hc, e]⟩
  let N := findNat _ hN
  let c := findIn (fun c => D.tr (decodeOT M c) = b.1) (cand N.1) N.2
  ⟨decodeOT M c.1, isOT_decodeOT M c.1, c.2.2⟩

/-- **The order isomorphism** `OT M ≅ {NF1 below bound}`. -/
def toIso : MbekRank1.OrderIso (MbekRank1.Mbek M) {t : T // T.isNF1 t ∧ t < bound}
    (fun a b => a.1 < b.1) (fun a b => a.1 < b.1) where
  toFun s := ⟨D.tr s.1, D.tr_isNF1 s.1 s.2, D.tr_lt_bound s.1 s.2⟩
  invFun b := ⟨(D.preimage b).val, (D.preimage b).property.1⟩
  left_inv s := Subtype.ext
    (D.tr_inj _ _ (D.preimage _).property.1 s.property (D.preimage _).property.2)
  right_inv b := Subtype.ext (D.preimage b).property.2
  map_rel_iff a b := D.tr_lt_iff a.property b.property

end Translation

end Mbek
