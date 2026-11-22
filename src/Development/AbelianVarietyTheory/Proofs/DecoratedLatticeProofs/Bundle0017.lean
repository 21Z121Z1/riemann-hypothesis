import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IndicatorFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndicatorIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricPositionLevelCharacterEqOneSingleRow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceOrder
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalInduct

def psum {N : ℕ} (ν : Fin N → ℤ) (j : ℕ) : ℤ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i

def pot {N : ℕ} (ν : Fin N → ℤ) : ℤ := ∑ j ∈ Finset.range (N + 1), psum ν j

theorem psum_succ {N : ℕ} (ν : Fin N → ℤ) (i : Fin N) : psum ν (i + 1) = psum ν i + ν i := by
  unfold psum
  have : Finset.univ.filter (fun j : Fin N => (j : ℕ) < i + 1) =
      insert i (Finset.univ.filter (fun j : Fin N => (j : ℕ) < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sum_insert (by simp), add_comm]

theorem pot_lt {N : ℕ} {μ ν : Fin N → ℤ} (h : ∀ j, psum μ j ≤ psum ν j) (hne : μ ≠ ν) : pot μ < pot ν := by
  obtain ⟨i, hi⟩ : ∃ i, μ i ≠ ν i := by
    by_contra h'; push_neg at h'; exact hne (funext h')
  have hiN := i.isLt
  have : ∃ j ∈ Finset.range (N + 1), psum μ j < psum ν j := by
    by_contra h'; push_neg at h'
    have e1 : psum μ i = psum ν i := le_antisymm (h _) (h' _ (Finset.mem_range.2 (by omega)))
    have e2 : psum μ (i + 1) = psum ν (i + 1) := le_antisymm (h _) (h' _ (Finset.mem_range.2 (by omega)))
    rw [psum_succ, psum_succ, e1] at e2
    exact hi (by linarith)
  obtain ⟨j, hj, hlt⟩ := this
  exact Finset.sum_lt_sum (fun j _ => h j) ⟨j, hj, hlt⟩

theorem pot_nonneg {N : ℕ} {ν : Fin N → ℤ} (h : ∀ i, 0 ≤ ν i) : 0 ≤ pot ν :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun i _ => h i

theorem pos_iff_lt {N : ℕ} {e : Fin N → ℤ} (ha : Antitone e) (i : Fin N) :
    0 < e i ↔ (i : ℕ) < (Finset.univ.filter fun j => 0 < e j).card := by
  first
  | exact @_root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card
  | exact _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card
  | (apply _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveIffLtCard.pos_iff_lt_card ..)

theorem nonneg_of_dom {N : ℕ} {ν e : Fin N → ℤ} (hν : Antitone ν) (he : ∀ i, 0 ≤ e i)
    (hle : ∀ j, psum ν j ≤ psum e j) (hsum : ∑ i, ν i = ∑ i, e i) (i : Fin N) : 0 ≤ ν i := by
  by_contra hneg
  push_neg at hneg
  have sν := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < i) ν
  have se := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < i) e
  have tν : ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < i), ν j < 0 := by
    refine Finset.sum_neg (fun j hj => ?_) ⟨i, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
    exact lt_of_le_of_lt (hν (Fin.le_def.2 hj)) hneg
  have te : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < i), e j :=
    Finset.sum_nonneg fun j _ => he j
  have := hle i
  unfold psum at this
  linarith

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem torusElt_add' {N : ℕ} (ϖ : kˣ) (a b : Fin N → ℤ) :
    torusElt k (Fin N) ϖ (a + b) = torusElt k (Fin N) ϖ a * torusElt k (Fin N) ϖ b := by
  apply Units.ext
  rw [Units.val_mul, val_torusElt, val_torusElt, val_torusElt, diagonal_mul_diagonal]
  congr 1; funext i; simp [zpow_add₀ (Units.ne_zero ϖ)]

theorem torusElt_zero' {N : ℕ} (ϖ : kˣ) : torusElt k (Fin N) ϖ (fun _ => 0) = 1 := by
  apply Units.ext
  rw [val_torusElt]; simp

theorem torusElt_one_comm {N : ℕ} (ϖ : kˣ) (g : GL (Fin N) k) :
    g * torusElt k (Fin N) ϖ (fun _ => 1) = torusElt k (Fin N) ϖ (fun _ => 1) * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_torusElt]
  ext i j; simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

theorem vanish_of_shift {N : ℕ} {ϖ : kˣ} {c : ℕ → ℂ} (hc : c N ≠ 0) {h : GL (Fin N) k → ℂ}
    (hK : ∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m)
    (hT : ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R →
      ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m)
    (hex : ∀ g : GL (Fin N) k, ∃ R, IsRepsK g R) (j : ℕ) (m : GL (Fin N) k)
    (hm : h (m * torusElt k (Fin N) ϖ (fun _ => (j : ℤ))) = 0) : h m = 0 := by
  induction j generalizing m with
  | zero => simpa [torusElt_zero'] using hm
  | succ j ih =>
    apply ih
    have hz : indic (Finset.univ : Finset (Fin N)) = fun _ => 1 := funext fun i => by simp [indic]
    obtain ⟨R, hR⟩ := hex (torusElt k (Fin N) ϖ (indic Finset.univ))
    set z := torusElt k (Fin N) ϖ (fun _ => 1) with hzdef
    set m' := m * torusElt k (Fin N) ϖ (fun _ => (j : ℤ))
    have hsplit : torusElt k (Fin N) ϖ (fun _ => ((j + 1 : ℕ) : ℤ)) = torusElt k (Fin N) ϖ (fun _ => (j : ℤ)) * z := by
      rw [hzdef, ← torusElt_add']; congr 1
    have hm' : h (m' * z) = 0 := by rw [← hm, hsplit, mul_assoc]
    have key := hT Finset.univ R hR m'
    have hterm : ∀ g ∈ R, h (m' * g) = 0 := by
      intro g hg
      obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hR.1 g hg
      rw [hz] at *
      have e : m' * (κ * z * κ') = (m' * z) * (κ * κ') := by
        rw [torusElt_one_comm]; simp only [mul_assoc]; rfl
      rw [e, (hK _ (mul_mem hκ hκ') _).2, hm']
    rw [Finset.sum_eq_zero hterm, Finset.card_univ, Fintype.card_fin] at key
    exact (mul_eq_zero.1 key.symm).resolve_left hc

theorem vanish_dominant {N : ℕ} {ϖ : kˣ} {c : ℕ → ℂ} {h : GL (Fin N) k → ℂ}
    (hcart : ∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧ ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
      x = κ * torusElt k (Fin N) ϖ ν * κ')
    (hdom : ∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k,
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N),
        g = κ * torusElt k (Fin N) ϖ (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') →
      (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), torusElt k (Fin N) ϖ μ * g = κ * torusElt k (Fin N) ϖ ν * κ') →
      ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j),
          (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i))
    (hex : ∀ g : GL (Fin N) k, ∃ R, IsRepsK g R)
    (hK : ∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m)
    (hT : ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R →
      ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m)
    (h1 : h 1 = 0) :
    ∀ n : ℕ, ∀ e : Fin N → ℤ, Antitone e → (∀ i, 0 ≤ e i) → pot e ≤ n → h (torusElt k (Fin N) ϖ e) = 0 := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih e ha he hpot
  have IH : ∀ ν : Fin N → ℤ, Antitone ν → (∀ i, 0 ≤ ν i) → pot ν < pot e →
      h (torusElt k (Fin N) ϖ ν) = 0 := by
    intro ν hν hν0 hlt
    have h0 := pot_nonneg hν0
    exact ih (pot ν).toNat (by omega) ν hν hν0 (by omega)
  by_cases hzero : ∀ i, e i = 0
  · have : e = fun _ => 0 := funext hzero
    rw [this, torusElt_zero', h1]
  push_neg at hzero
  obtain ⟨i₀, hi₀⟩ := hzero
  have hi₀pos : 0 < e i₀ := lt_of_le_of_ne (he i₀) (Ne.symm hi₀)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = (Finset.univ.filter fun j => 0 < e j).card := ⟨_, rfl⟩
  have key : ∀ i, 0 < e i ↔ (i : ℕ) < n₀ := fun i => hn₀ ▸ pos_iff_lt ha i
  have hn₀N : n₀ ≤ N := by rw [hn₀]; exact (Finset.card_le_univ _).trans (by simp)
  obtain ⟨s, hs⟩ : ∃ s : Finset (Fin N), s = Finset.univ.filter fun i : Fin N => (i : ℕ) < n₀ := ⟨_, rfl⟩
  have hind : ∀ i, indic s i = if 0 < e i then 1 else 0 := by
    intro i; simp only [indic, hs, Finset.mem_filter, Finset.mem_univ, true_and, ← key]
  have hscard : s.card = n₀ := by
    rw [hn₀]; congr 1; rw [hs]; ext i; simp [key]
  set μ : Fin N → ℤ := fun i => e i - indic s i with hμdef
  have hμe : ∀ i, μ i + indic s i = e i := fun i => by simp [hμdef]
  have hμa : Antitone μ := by
    intro i j hij
    have := ha hij; have hi := he i; have hj := he j
    simp only [hμdef, hind]
    split_ifs <;> omega
  have hμ0 : ∀ i, 0 ≤ μ i := by
    intro i; have := he i; simp only [hμdef, hind]; split_ifs <;> omega
  have hμlt : pot μ < pot e := by
    apply pot_lt
    · intro j; unfold psum
      exact Finset.sum_le_sum fun i _ => by simp only [hμdef, hind]; split_ifs <;> omega
    · intro hh; have := congrFun hh i₀; simp only [hμdef, hind, if_pos hi₀pos] at this; omega
  have hμv := IH μ hμa hμ0 hμlt
  have hTe : torusElt k (Fin N) ϖ e = torusElt k (Fin N) ϖ μ * torusElt k (Fin N) ϖ (indic s) := by
    rw [← torusElt_add']; congr 1; funext i; exact (hμe i).symm
  have hsumind : ∑ i, indic s i = (n₀ : ℤ) := by
    rw [← hscard]; simp [indic]
  obtain ⟨R, hR⟩ := hex (torusElt k (Fin N) ϖ (indic s))
  have hsum := hT s R hR (torusElt k (Fin N) ϖ μ)
  rw [hμv, mul_zero] at hsum
  have hterm : ∀ g ∈ R, h (torusElt k (Fin N) ϖ μ * g) = 0 ∨
      h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ e) := by
    intro g hg
    obtain ⟨ν, hν, κ1, hκ1, κ2, hκ2, hx⟩ := hcart (torusElt k (Fin N) ϖ μ * g)
    have hval : h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ ν) := by
      rw [hx, mul_assoc, (hK κ1 hκ1 _).1, (hK κ2 hκ2 _).2]
    obtain ⟨κ, hκ, κ', hκ', hgeq⟩ := hR.1 g hg
    have hd := hdom μ ν hμa hν n₀ hn₀N g ⟨κ, hκ, κ', hκ', by rw [← hs]; exact hgeq⟩ ⟨κ1, hκ1, κ2, hκ2, hx⟩
    simp only [← hs] at hd
    obtain ⟨hd1, hd2⟩ := hd
    have hle : ∀ j, psum ν j ≤ psum e j := by
      intro j; have := hd2 j; simp only [hμe] at this; exact this
    have hsumeq : ∑ i, ν i = ∑ i, e i := by
      rw [hd1, ← hsumind, ← Finset.sum_add_distrib]; simp only [hμe]
    have hν0 := nonneg_of_dom hν he hle hsumeq
    by_cases hνe : ν = e
    · right; rw [hval, hνe]
    · left; rw [hval]; exact IH ν hν hν0 (pot_lt hle hνe)
  obtain ⟨g₁, ⟨hg₁R, hg₁K⟩, -⟩ := hR.2 1 (one_mem _)
  have hg₁ : h (torusElt k (Fin N) ϖ μ * g₁) = h (torusElt k (Fin N) ϖ e) := by
    have e1 : torusElt k (Fin N) ϖ μ * g₁ =
        torusElt k (Fin N) ϖ e * (g₁⁻¹ * (1 * torusElt k (Fin N) ϖ (indic s)))⁻¹ := by
      rw [hTe]; group
    rw [e1, (hK _ (inv_mem hg₁K) _).2]
  by_contra hx
  have hite : ∀ g ∈ R, h (torusElt k (Fin N) ϖ μ * g) =
      if h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ e) then h (torusElt k (Fin N) ϖ e) else 0 := by
    intro g hg
    rcases hterm g hg with h0 | h0
    · rw [h0, if_neg (Ne.symm hx)]
    · rw [if_pos h0]; exact h0
  rw [Finset.sum_congr rfl hite, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul] at hsum
  have hcard : (R.filter fun g => h (torusElt k (Fin N) ϖ μ * g) = h (torusElt k (Fin N) ϖ e)).card ≠ 0 :=
    Finset.card_ne_zero.2 ⟨g₁, Finset.mem_filter.2 ⟨hg₁R, hg₁⟩⟩
  rcases mul_eq_zero.1 hsum with hc0 | hc0
  · exact hcard (by exact_mod_cast hc0)
  · exact hx hc0

theorem zonal_vanish : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (ϖ : kˣ) (c : ℕ → ℂ), c N ≠ 0 → (∀ x : GL (Fin N) k, ∃ ν : Fin N → ℤ, Antitone ν ∧ ∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), x = κ * torusElt k (Fin N) ϖ ν * κ') → (∀ (μ ν : Fin N → ℤ), Antitone μ → Antitone ν → ∀ n : ℕ, n ≤ N → ∀ g : GL (Fin N) k, (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), g = κ * torusElt k (Fin N) ϖ (indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n)) * κ') → (∃ κ ∈ KO k (Fin N), ∃ κ' ∈ KO k (Fin N), torusElt k (Fin N) ϖ μ * g = κ * torusElt k (Fin N) ϖ ν * κ') → ∑ i, ν i = ∑ i, μ i + n ∧ ∀ j : ℕ, ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), ν i ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), (μ i + indic (Finset.univ.filter fun i : Fin N => (i : ℕ) < n) i)) → (∀ g : GL (Fin N) k, ∃ R, IsRepsK g R) → ∀ h : GL (Fin N) k → ℂ, (∀ κ ∈ KO k (Fin N), ∀ m, h (κ * m) = h m ∧ h (m * κ) = h m) → (∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, h (m * g) = c s.card * h m) → h 1 = 0 → ∀ m, h m = 0 := by
  intro k _ _ _ _ N ϖ c hc hcart hdom hex h hK hT h1 m
  obtain ⟨ν, hν, κ, hκ, κ', hκ', rfl⟩ := hcart m
  rw [mul_assoc, (hK κ hκ _).1, (hK κ' hκ' _).2]
  set j : ℕ := (∑ i, |ν i|).toNat with hj
  apply vanish_of_shift hc hK hT hex j
  rw [← torusElt_add']
  refine vanish_dominant hcart hdom hex hK hT h1 (pot (ν + fun _ => (j : ℤ))).toNat (ν + fun _ => (j : ℤ))
    ?_ ?_ (Int.self_le_toNat _)
  · intro a b hab; simp only [Pi.add_apply]; linarith [hν hab]
  · intro i; simp only [Pi.add_apply]
    have h1' : |ν i| ≤ ∑ i, |ν i| :=
      Finset.single_le_sum (f := fun i => |ν i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (ν i)
    have h3 := Int.self_le_toNat (∑ i, |ν i|)
    omega

end GlobalTheory.ZonalInduct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExchangeToPositionOneIsPositionOne
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)

noncomputable section
namespace GlobalTheory.PosOne.ToOnePos

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
  {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem toOne_lin (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ) :
    ∀ m : ℕ, m + 1 ≤ c → ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ (m + 1) σ l →
      ∃ l₁ : A →ₗ[ℂ] ℂ, (∀ v, l₁ v = toOne ν σ (m + 1) l v) ∧ IsNEquiv ψ 1 σ l₁ := by
  intro m
  induction m with
  | zero => intro _ l hl; exact ⟨l, fun v => rfl, hl⟩
  | succ m ih =>
    intro hm l hl
    obtain ⟨l', hl'v, hl'⟩ := (GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) (by omega) ψ hψ hψ1
      ν A σ hσ).2.1 l hl
    obtain ⟨l₁, hl₁v, hl₁⟩ := ih (by omega) l' hl'
    refine ⟨l₁, fun v => ?_, hl₁⟩
    rw [hl₁v, toOne_succ]
    congr 1
    funext w
    exact hl'v w

theorem toOne_bil (ψ : AddChar k Circle) (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure]
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (hσ : IsSmoothRep σ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (π : Representation ℂ (GL n k) P) :
    ∀ m : ℕ, m + 1 ≤ c → ∀ b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, IsPos ψ (m + 1) π σ b →
      ∃ b₁ : P →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ φ v, b₁ φ v = toOne ν σ (m + 1) (b φ) v) ∧ IsPos ψ 1 π σ b₁ := by
  intro m
  induction m with
  | zero => intro _ b hb; exact ⟨b, fun φ v => rfl, hb⟩
  | succ m ih =>
    intro hm b hb
    obtain ⟨b', hb'v, hb'⟩ := ((GlobalTheory.RootEx.Exchange.exchange_isPos k n c (m + 1) (by omega) (by omega) ψ hψ hψ1
      ν A σ hσ).2.2 P π b).2 hb
    obtain ⟨b₁, hb₁v, hb₁⟩ := ih (by omega) b' hb'
    refine ⟨b₁, fun φ v => ?_, hb₁⟩
    rw [hb₁v, toOne_succ]
    congr 1
    funext w
    exact hb'v φ w

variable {n' : Type} [Fintype n'] [DecidableEq n']

def omRep (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) : Representation ℂ (GL n k) (SB (Matrix n n' k)) where
  toFun g :=
    { toFun := fun Ψ => ⟨om μ 1 g Ψ.1,
        (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.2.1 1 g Ψ.1 Ψ.2⟩
      map_add' := fun Ψ Ψ' => by
        apply Subtype.ext
        have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.1 1 g 1 Ψ.1 Ψ'.1
        simpa using this
      map_smul' := fun z Ψ => by
        apply Subtype.ext
        have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.2.1 1 g z Ψ.1 0
        have h0 : om μ 1 g (0 : Matrix n n' k → ℂ) = 0 := by
          funext x
          simp [om]
        simpa [h0] using this }
  map_one' := by
    ext Ψ : 2
    exact (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).1 Ψ.1
  map_mul' g h := by
    ext Ψ : 2
    have := (GlobalTheory.SplitWeil.om_isSmoothRepresentation k n' n μ hμ).2.1 1 1 g h Ψ.1
    simpa using this

theorem bilPos_iff (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (hμ : IsOpen (μ.ker : Set kˣ)) (p : ℕ)
    {A : Type} [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) : BilPos ψ μ p σ B ↔ IsPos ψ p (omRep μ hμ) σ B := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun g Ψ v => h2 g Ψ _ v rfl⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun g Ψ Ψ₁ v hΨ => ?_⟩
    have : Ψ₁ = omRep μ hμ g Ψ := Subtype.ext hΨ
    subst this
    exact h2 g Ψ v

end GlobalTheory.PosOne.ToOnePos

open GlobalTheory.PosOne.ToOnePos in

theorem GlobalTheory.PosOne.toOne_isPosOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c P : ℕ) (_ : 1 ≤ P) (_ : P ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ), (∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ P σ l → ∃ l₁ : A →ₗ[ℂ] ℂ, (∀ v, l₁ v = toOne ν σ P l v) ∧ IsNEquiv ψ 1 σ l₁) ∧ ∀ (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), BilPos ψ μ P σ B → ∃ B₁ : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ, (∀ Ψ v, B₁ Ψ v = toOne ν σ P (B Ψ) v) ∧ BilPos ψ μ 1 σ B₁ := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c P hP hPc ψ hψ hψ1 ν _ A _ _ σ hσ
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 1 := ⟨P - 1, by omega⟩
  refine ⟨toOne_lin ψ hψ hψ1 ν σ hσ m hPc, fun μ hμ B hB => ?_⟩
  obtain ⟨B₁, hB₁v, hB₁⟩ := toOne_bil ψ hψ hψ1 ν σ hσ (omRep μ hμ) m hPc B ((bilPos_iff ψ μ hμ _ σ B).1 hB)
  exact ⟨B₁, hB₁v, (bilPos_iff ψ μ hμ 1 σ B₁).2 hB₁⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelsCommuteTwisted
section
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp

noncomputable section
namespace GlobalTheory.KernelCommTw

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]

def IsTwEquiv (l' l : kˣ →* ℂˣ) (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V)
    (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V) : Prop :=
  ∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)),
    (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) *
      Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)

variable {l' l : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}

theorem unram_val {χ : kˣ →* ℂˣ} (hχ : IsUnram χ) (u z : kˣ) (hz : valuation k ((z * u : kˣ) : k) = 1) :
    (χ z : ℂ) = (χ u : ℂ)⁻¹ := by
  have := congrArg (fun w : ℂˣ => (w : ℂ)) (hχ _ hz)
  simp only [map_mul, Units.val_mul, Units.val_one] at this
  exact eq_inv_of_mul_eq_one_left this

theorem theta_mem (hl : IsUnram l) (hθ : IsTwEquiv l' l π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) (v : V') :
    θ v (phiOneSB P₀ Q₀) ∈ levelVec π Q₀ := fun h hh => by
  have hv := valuation_det_of_fix Q₀.lat (h := h) (by rw [← Pair.smul_lat, hh])
  have := hθ 1 h v (phiOneSB P₀ Q₀) (phiOneSB P₀ Q₀) fun x => by
    have e := phiOne_smul (x := x) (P := P₀) (Q := Q₀) 1 h
    rw [one_smul, hh] at e
    simp only [phiOneSB, map_one, hl _ hv, Units.val_one, one_mul]
    simpa using e
  simpa using this.symm

variable (hl : IsUnram l) (hθ : IsTwEquiv l' l π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)

def KK : Form k n' V' →ₗ[ℂ] Form k n V :=
  (EqForm π).subtype ∘ₗ (evalEquiv π Q₀).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (θ.flip (phiOneSB P₀ Q₀) ∘ₗ LinearMap.proj P₀) fun φ => theta_mem hl hθ P₀ Q₀ (φ P₀)

theorem KK_mem (φ : Form k n' V') : KK hl hθ P₀ Q₀ φ ∈ EqForm π := formOf_mem _ _ _

theorem KK_smul (φ : Form k n' V') (h : GL n k) :
    KK hl hθ P₀ Q₀ φ (h • Q₀) = π h (θ (φ P₀) (phiOneSB P₀ Q₀)) := formOf_smul π Q₀ _ h

theorem KK_move (hl' : IsUnram l') {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (u : kˣ) (g : GL n' k) (h : GL n k)
    (hg : valuation k ((Matrix.GeneralLinearGroup.det g * u : kˣ) : k) = 1)
    (hh : valuation k ((Matrix.GeneralLinearGroup.det h * u : kˣ) : k) = 1) :
    KK hl hθ P₀ Q₀ φ (h • Q₀) = ((l' u : ℂ) * (l u : ℂ))⁻¹ • θ (φ (g • P₀)) (phiOneSB (g • P₀) (h • Q₀)) := by
  rw [KK_smul, hφ g, ← map_smul]
  refine (hθ g h _ _ _ fun x => ?_).symm
  simp only [phiOneSB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, phiOne_smul, unram_val hl' u _ hg,
    unram_val hl u _ hh]
  rw [mul_inv]

theorem KK_same (hl' : IsUnram l') {φ : Form k n' V'} (hφ : φ ∈ EqForm π') {P : Pair k n'} {Q : Pair k n}
    (hP : P.lat = P₀.lat) (hQ : Q.lat = Q₀.lat) : KK hl hθ P₀ Q₀ φ Q = θ (φ P) (phiOneSB P Q) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P₀ P
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [KK_move hl hθ P₀ Q₀ hl' hφ 1 g h (by simpa only [mul_one] using valuation_det_of_fix _ hP)
    (by simpa only [mul_one] using valuation_det_of_fix _ hQ)]
  simp

theorem KK_up (hl' : IsUnram l') (q : Unif k) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') {P : Pair k n'}
    {Q : Pair k n} (hP : P.ker = P₀.lat) (hQ : Q.ker = Q₀.lat) :
    KK hl hθ P₀ Q₀ φ Q = ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ • θ (φ P) (phiOneSB P Q) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P₀ P
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [Pair.smul_ker] at hP hQ
  exact KK_move hl hθ P₀ Q₀ hl' hφ q.unit g h (GlobalTheory.KernelComm.valuation_det q _ hP)
    (GlobalTheory.KernelComm.valuation_det q _ hQ)

theorem U_KK (hl' : IsUnram l') (q : Unif k) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') :
    U q (KK hl hθ P₀ Q₀ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ • KK hl hθ P₀ Q₀ (U q φ) := by
  classical
  refine GlobalTheory.KernelComm.eq_of_base Q₀ (U_mem_EqForm q (KK_mem hl hθ P₀ Q₀ φ))
    (Submodule.smul_mem _ _ (KK_mem hl hθ P₀ Q₀ _)) ?_
  have h1 : ∀ P₁ ∈ withKer P₀.lat, U q (KK hl hθ P₀ Q₀ φ) Q₀ =
      ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ •
        ∑ P ∈ withLat P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P₁ hP => by
    rw [mem_withKer] at hP
    rw [U_apply, Finset.sum_congr rfl fun Q₁ hQ =>
      KK_up hl hθ P₀ Q₀ hl' q hφ hP (mem_withKer.1 (Finset.mem_filter.1 hQ).1), ← Finset.smul_sum,
      ← Finset.sum_filter, ← map_sum, ← map_sum, ← hP]
    congr 2
    refine Subtype.ext (funext fun x => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, phiOneSB]
    exact (GlobalTheory.KernelComm.sum_target q P₁.hasVal_vec Q₀ x).trans (GlobalTheory.KernelComm.sum_source q P₁.hasVal_vec Q₀ x)
  have h2 : ∀ P ∈ withLat P₀.lat, KK hl hθ P₀ Q₀ (U q φ) Q₀ =
      ∑ P₁ ∈ withKer P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P hP => by
    rw [mem_withLat] at hP
    rw [KK_same hl hθ P₀ Q₀ hl' (U_mem_EqForm q hφ) hP rfl, U_apply, map_sum, LinearMap.sum_apply, hP,
      Finset.sum_filter]
  have h3 := Finset.sum_congr rfl h1
  rw [← Finset.smul_sum, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    GlobalTheory.KernelComm.card_withKer q, smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h3
  refine smul_right_injective V ?_ h3
  exact_mod_cast (Finset.card_pos.2 ⟨P₀, mem_withLat.2 rfl⟩).ne'

theorem KK_dia (hl' : IsUnram l') (s : 𝓀[k]ˣ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') :
    KK hl hθ P₀ Q₀ (dia s φ) = dia s (KK hl hθ P₀ Q₀ φ) := by
  refine GlobalTheory.KernelComm.eq_of_base Q₀ (KK_mem hl hθ P₀ Q₀ _) (dia_mem_EqForm s (KK_mem hl hθ P₀ Q₀ φ)) ?_
  rw [dia_apply, KK_same hl hθ P₀ Q₀ hl' hφ (P := s • P₀) (Q := s • Q₀) rfl rfl,
    KK_same hl hθ P₀ Q₀ hl' (dia_mem_EqForm s hφ) rfl rfl, dia_apply]
  congr 1
  exact Subtype.ext (phiOne_dia s).symm

theorem KK_ram (hl' : IsUnram l') {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (h : φ ∈ Mram k n' V') :
    KK hl hθ P₀ Q₀ φ ∈ Mram k n V := by
  have : Nm (KK hl hθ P₀ Q₀ φ) = KK hl hθ P₀ Q₀ (Nm φ) := by
    simp only [Nm, LinearMap.sum_apply, map_sum, KK_dia hl hθ P₀ Q₀ hl' _ hφ]
  rw [show Nm φ = 0 from h, map_zero] at this
  exact this

theorem FFStar_KK (hl' : IsUnram l') (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π')
    (h : φ ∈ Mram k n' V') :
    FFStar q χ (KK hl hθ P₀ Q₀ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ • KK hl hθ P₀ Q₀ (FFStar q χ φ) := by
  have h1 : GsStar χ (KK hl hθ P₀ Q₀ φ) = KK hl hθ P₀ Q₀ (GsStar χ φ) := by
    simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, KK_dia hl hθ P₀ Q₀ hl' _ hφ]
  have h2 : GsStar χ φ ∈ EqForm π' := by
    simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply]
    exact sum_mem fun c _ => Submodule.smul_mem _ _ (dia_mem_EqForm _ hφ)
  rw [FFStar_eq_U_GsStar q χ h, FFStar_eq_U_GsStar q χ (KK_ram hl hθ P₀ Q₀ hl' hφ h), h1,
    U_KK hl hθ P₀ Q₀ hl' q h2]

theorem KK_FFStar (hl' : IsUnram l') (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π')
    (h : φ ∈ Mram k n' V') :
    KK hl hθ P₀ Q₀ (FFStar q χ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ)) • FFStar q χ (KK hl hθ P₀ Q₀ φ) := by
  rw [FFStar_KK hl hθ P₀ Q₀ hl' q χ hφ h, smul_smul, mul_inv_cancel₀ (mul_ne_zero (Units.ne_zero _)
    (Units.ne_zero _)), one_smul]

end GlobalTheory.KernelCommTw

namespace GlobalTheory.KernelCommTw

theorem kernelsCommuteTwisted : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (l' l : kˣ →* ℂˣ), IsUnram l' → IsUnram l → ∀ (P₀ : Pair k n') (Q₀ : Pair k n), ∃ c : ℂ, c ≠ 0 ∧ ∀ (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V) (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V), (∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)), (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)) → ∃ K : EqForm π' →ₗ[ℂ] EqForm π, (∀ φ, (K φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀)) ∧ (∀ (s : 𝓀[k]ˣ) φ, (K ⟨dia s φ.1, dia_mem_EqForm s φ.2⟩).1 = dia s (K φ).1) ∧ ∀ φ : EqForm π', φ.1 ∈ Mram k n' V' → (K φ).1 ∈ Mram k n V ∧ (K ⟨FFStar q (resChar ψ hψ q) φ.1, FFStar_mem_EqForm q _ φ.2⟩).1 = c • FFStar q (resChar ψ hψ q) (K φ).1 := by
  intro k _ _ _ _ n n' _ _ _ _ q ψ hψ l' l hl' hl P₀ Q₀
  refine ⟨(l' q.unit : ℂ) * (l q.unit : ℂ), mul_ne_zero (Units.ne_zero _) (Units.ne_zero _), ?_⟩
  intro V' V _ _ _ _ π' π θ hθ
  refine ⟨LinearMap.codRestrict (EqForm π) (KK hl hθ P₀ Q₀ ∘ₗ (EqForm π').subtype)
    fun φ => KK_mem hl hθ P₀ Q₀ φ.1, fun φ => ?_, fun s φ => KK_dia hl hθ P₀ Q₀ hl' s φ.2, fun φ h =>
      ⟨KK_ram hl hθ P₀ Q₀ hl' φ.2 h, KK_FFStar hl hθ P₀ Q₀ hl' q _ φ.2 h⟩⟩
  show KK hl hθ P₀ Q₀ φ.1 Q₀ = _
  simpa using KK_smul hl hθ P₀ Q₀ φ.1 1

end GlobalTheory.KernelCommTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricPositionLevelCharacterEqOneSingleRowStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricPositionLevel_character_eq_one_single_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin l)), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P → ∀ (i₀ : Fin l) (g : P.J), (∀ a b, a ≠ Sum.inr i₀ → (g : GL (Fin κ ⊕ Fin l) k).val a b = (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) a b) → (∀ i : Fin l, i.val = i₀.val + 1 → (g : GL (Fin κ ⊕ Fin l) k).val (Sum.inr i₀) (Sum.inr i) = 0) → P.lam g = 1 := by
  first | exact @GlobalTheory.lam_purerow | exact GlobalTheory.lam_purerow | (intros; apply GlobalTheory.lam_purerow <;> assumption)
end

