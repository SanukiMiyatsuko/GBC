import Mbekworm.Sequence.mbekwormDef
import Mbekworm.Buchholz.Rank1

/-!
# `isOT M` と rank-one Buchholz 項の順序同型：主張

`isOT M` で生成されるリスト（辞書式順序）と、`T.isNF1` を満たし
`bound M` 未満の項（`T.Lt`）との順序同型を述べる。
-/

open T

namespace MbekRank1

/-- `expand M` で生成されるリスト全体。 -/
abbrev Mbek (M : Nat) : Type := {xs : List Nat // isOT M xs}

/-- 予想される順序型の上界。 -/
def bound : Nat → T
  | 0 => P 0 (P 0 (P 0 Z Z) Z) Z
  | M + 1 => P 0 (P 1 (T.mul (P 1 (P 1 Z Z) Z) (T.ofNat M)) Z) Z

/-- `bound M` 未満の rank-one 標準形。 -/
abbrev Rank1 (M : Nat) : Type := {t : T // T.isNF1 t ∧ t < bound M}

/-- `mathlib` に依存しない順序同型（逆写像をデータとして持つ）。 -/
structure OrderIso (A B : Type) (ra : A → A → Prop) (rb : B → B → Prop) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  map_rel_iff : ∀ a b, rb (toFun a) (toFun b) ↔ ra a b

/-- `isOT M`（辞書式順序）と `bound M` 未満の rank-one 標準形の順序同型。 -/
abbrev MbekRank1Iso (M : Nat) : Type :=
  OrderIso (Mbek M) (Rank1 M) (fun a b => a.1 < b.1) (fun a b => a.1 < b.1)

/-- 目標の主張。 -/
def Conjecture : Prop := ∀ M : Nat, Nonempty (MbekRank1Iso M)

/-- `expand M` の反射推移閉包。 -/
inductive Reach (M : Nat) : List Nat → List Nat → Prop where
  | refl (a : List Nat) : Reach M a a
  | step (a : List Nat) (n : Nat) (b : List Nat) :
      Reach M (expand M a n) b → Reach M a b

theorem isOT_of_reach {M : Nat} {a b : List Nat}
    (ha : isOT M a) (hr : Reach M a b) : isOT M b := by
  induction hr with
  | refl => exact ha
  | step a n b _ ih => exact ih (isOT.step a ha n)

end MbekRank1
