import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0444
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

abbrev FrameIx (r : ℕ) : Type := Option (Fin r ⊕ Fin r)

variable {E : Type} [Field E] {n r : ℕ}

def frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    FrameIx r → Matrix (Fin n) (Fin n) E
  | some (Sum.inl i) => X * single i i (1 : E) * (cT S Y * J)
  | some (Sum.inr i) => Y * single i i (1 : E) * (cT S X * J)
  | none => 1 - X * (cT S Y * J) - Y * (cT S X * J)

def frameWt (t : Fin r → ℝ) : FrameIx r → ℝ
  | some (Sum.inl i) => t i
  | some (Sum.inr i) => (t i)⁻¹
  | none => 1

def frameLev (s : Fin r) : FrameIx r → ℕ
  | some (Sum.inl i) => if i ≤ s then 2 else 1
  | some (Sum.inr i) => if i ≤ s then 0 else 1
  | none => 1

theorem sum_frameIdem (S : E →+* E) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) :
    ∑ α, frameIdem S J X Y α = 1 := by
  have key : ∀ (A : Matrix (Fin n) (Fin r) E) (B : Matrix (Fin r) (Fin n) E),
      ∑ i : Fin r, (A * (Matrix.single i i (1 : E) : Matrix (Fin r) (Fin r) E) * B : Matrix (Fin n) (Fin n) E) = A * B := fun A B => by
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  rw [Fintype.sum_option, Fintype.sum_sum_type]
  simp only [frameIdem]
  rw [key, key]
  abel

theorem frameWt_pos {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) (α : FrameIx r) : 0 < frameWt t α := by
  rcases α with _ | i | i
  · exact one_pos
  · exact ht i
  · exact inv_pos.2 (ht i)

end GlobalTheory.CompanionTheory.RapidDecay

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableHeightPowOfPolynomialCount
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem summable_rpow_neg_of_polynomial_count :
    ∀ (Q : Type) (h : Q → ℝ), (∀ q, 1 ≤ h q) → ∀ (C : ℝ) (c : ℕ),
    (∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C * T ^ c) → ∀ s : ℝ, (c : ℝ) < s →
    Summable fun q => h q ^ (-s) := by
  intro Q h h1 C c hc s hs
  classical
  have hC : 0 ≤ C := by
    have h2 := (hc 1 le_rfl).2
    have h3 : (0:ℝ) ≤ (Set.ncard {q | h q ≤ 1} : ℝ) := Nat.cast_nonneg _
    simp only [one_pow, mul_one] at h2
    linarith
  set r : ℝ := (2:ℝ) ^ ((c:ℝ) - s) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable fun k : ℕ => C * 2 ^ c * r ^ k :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  have hg0 : ∀ k : ℕ, 0 ≤ C * 2 ^ c * r ^ k := fun k => by positivity
  set K : Q → ℕ := fun q => ⌊Real.logb 2 (h q)⌋₊ with hK
  have hlog0 : ∀ q, 0 ≤ Real.logb 2 (h q) := fun q =>
    Real.logb_nonneg (by norm_num) (h1 q)
  have hlow : ∀ q, (2:ℝ) ^ (K q : ℝ) ≤ h q := fun q => by
    have hq : (0:ℝ) < h q := lt_of_lt_of_le one_pos (h1 q)
    have : (K q : ℝ) ≤ Real.logb 2 (h q) := Nat.floor_le (hlog0 q)
    calc (2:ℝ) ^ (K q : ℝ) ≤ (2:ℝ) ^ (Real.logb 2 (h q)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      _ = h q := Real.rpow_logb (by norm_num) (by norm_num) hq
  have hupp : ∀ q, h q ≤ (2:ℝ) ^ (K q + 1) := fun q => by
    have hq : (0:ℝ) < h q := lt_of_lt_of_le one_pos (h1 q)
    have : Real.logb 2 (h q) ≤ ((K q + 1 : ℕ) : ℝ) := by
      push_cast
      exact (Nat.lt_floor_add_one _).le
    calc h q = (2:ℝ) ^ (Real.logb 2 (h q)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hq).symm
      _ ≤ (2:ℝ) ^ (((K q + 1 : ℕ)) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) this
      _ = (2:ℝ) ^ (K q + 1) := Real.rpow_natCast _ _
  have hterm : ∀ q, h q ^ (-s) ≤ ((2:ℝ) ^ (K q : ℝ)) ^ (-s) := fun q =>
    Real.rpow_le_rpow_of_nonpos (by positivity) (hlow q) (by linarith [(Nat.cast_nonneg c : (0:ℝ) ≤ c)])
  have hfib : ∀ (u : Finset Q) (k : ℕ),
      ∑ q ∈ u with K q = k, h q ^ (-s) ≤ C * 2 ^ c * r ^ k := by
    intro u k
    have hT : (1:ℝ) ≤ (2:ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
    obtain ⟨hfin, hcard⟩ := hc _ hT
    have hsub : ((u.filter fun q => K q = k : Finset Q) : Set Q) ⊆ {q | h q ≤ (2:ℝ) ^ (k + 1)} := by
      intro q hq
      have hq' : K q = k := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
      have := hupp q
      rw [hq'] at this
      exact this
    have hcard2 : ((u.filter fun q => K q = k : Finset Q).card : ℝ) ≤ C * ((2:ℝ) ^ (k + 1)) ^ c := by
      refine le_trans ?_ hcard
      have := Set.ncard_le_ncard hsub hfin
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this
    have hb : ∀ q ∈ u.filter (fun q => K q = k), h q ^ (-s) ≤ ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
      intro q hq
      have hq' : K q = k := (Finset.mem_filter.mp hq).2
      have := hterm q
      rw [hq'] at this
      exact this
    have hb0 : (0:ℝ) ≤ ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by positivity
    calc ∑ q ∈ u with K q = k, h q ^ (-s)
        ≤ ((u.filter fun q => K q = k : Finset Q).card : ℝ) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
          simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul _ _ _ hb
      _ ≤ (C * ((2:ℝ) ^ (k + 1)) ^ c) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) :=
          mul_le_mul_of_nonneg_right hcard2 hb0
      _ = C * 2 ^ c * r ^ k := by
          have e1 : ((2:ℝ) ^ (k + 1)) ^ c = 2 ^ c * ((2:ℝ) ^ (k : ℝ)) ^ (c : ℝ) := by
            rw [Real.rpow_natCast, Real.rpow_natCast, pow_succ, mul_pow, mul_comm]
          have e2 : r ^ k = ((2:ℝ) ^ (k : ℝ)) ^ (c : ℝ) * ((2:ℝ) ^ (k : ℝ)) ^ (-s) := by
            rw [← Real.rpow_add (by positivity), hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
              ← Real.rpow_mul (by norm_num)]
            congr 1
            ring
          rw [e1, e2]
          ring
  refine summable_of_sum_le (c := ∑' k : ℕ, C * 2 ^ c * r ^ k) (fun q => Real.rpow_nonneg (by linarith [h1 q]) _) ?_
  intro u
  calc ∑ q ∈ u, h q ^ (-s)
      = ∑ k ∈ u.image K, ∑ q ∈ u with K q = k, h q ^ (-s) :=
        (Finset.sum_fiberwise_of_maps_to (fun q hq => Finset.mem_image_of_mem K hq) _).symm
    _ ≤ ∑ k ∈ u.image K, C * 2 ^ c * r ^ k := Finset.sum_le_sum fun k _ => hfib u k
    _ ≤ ∑' k : ℕ, C * 2 ^ c * r ^ k := hg.sum_le_tsum _ fun k _ => hg0 k

end GlobalTheory.CompanionTheory.GodementH
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SwapTwistedCentralizerDiagonal
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.SwapCent

theorem twCent_swap : ∀ (H : Type) [Group H] (N : H),
    twCent ((MulEquiv.prodComm : H × H ≃* H × H).toMonoidHom) (N, (1 : H)) =
      (twCent (MonoidHom.id H) N).map ((MonoidHom.id H).prod (MonoidHom.id H)) := by
  intro H _ N
  ext ⟨a, b⟩
  constructor
  · intro h
    have h' : (a, b) * (N, (1 : H)) = (N, (1 : H)) * (b, a) := h
    have h1 : a * N = N * b := congrArg Prod.fst h'
    have h2 : b = a := by simpa using congrArg Prod.snd h'
    subst h2
    exact ⟨b, h1, rfl⟩
  · rintro ⟨x, hx, hxe⟩
    have hx' : x * N = N * x := hx
    have e1 : x = a := congrArg Prod.fst hxe
    have e2 : x = b := congrArg Prod.snd hxe
    subst e1
    subst e2
    change (x, x) * (N, (1 : H)) = (N, (1 : H)) * (x, x)
    simp [hx']

end GlobalTheory.CompanionTheory.SwapCent
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCharacterEqResidueLift
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem isUnit_BdRp_of_thB {l : ℕ} [Fact l.Prime] {u : Formalism.Per6.BdRp l} (h : thB l u ≠ 0) :
    IsUnit u := by
  change IsUnit (show BDeRhamPlus (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l from u)
  by_contra hy
  have h2 := (IsLocalRing.mem_maximalIdeal _).2 hy
  rw [GroundTheory.PAdicHodge.IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker] at h2
  exact h h2

theorem eq_of_pow_eq_self_of_thB_eq {l : ℕ} [Fact l.Prime] {q : ℕ} (hq : 2 ≤ q)
    {a b : Formalism.Per6.BdRp l} (ha : a ^ q = a) (hb : b ^ q = b) (hab : thB l a = thB l b) :
    a = b := by
  set S : Formalism.Per6.BdRp l := ∑ i ∈ Finset.range q, a ^ i * b ^ (q - 1 - i) with hS
  have hkey : (a - b) * (S - 1) = 0 := by
    have h1 : (a - b) * S = a ^ q - b ^ q := (Commute.all a b).mul_geom_sum₂ q
    rw [mul_sub, h1, ha, hb, mul_one, sub_self]
  have hθS : thB l S = (q : ℂ_[l]) * thB l a ^ (q - 1) := by
    rw [hS, map_sum, Finset.sum_congr rfl (g := fun _ => thB l a ^ (q - 1))]
    · simp
    · intro i hi
      have hi' : i ≤ q - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.1 hi)
      rw [map_mul, map_pow, map_pow, ← hab, ← pow_add, Nat.add_sub_cancel' hi']
  have hζ : thB l a ^ q = thB l a := by rw [← map_pow, ha]
  have hne : thB l (S - 1) ≠ 0 := by
    rw [map_sub, map_one, hθS]
    by_cases h0 : thB l a = 0
    · rw [h0, zero_pow (by omega)]
      simp
    · have h1 : thB l a ^ (q - 1) = 1 := by
        have e : thB l a ^ (q - 1) * thB l a = 1 * thB l a := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega), hζ, one_mul]
        exact mul_right_cancel₀ h0 e
      rw [h1, mul_one, sub_ne_zero]
      exact_mod_cast (by omega : q ≠ 1)
  have hu := isUnit_BdRp_of_thB hne
  exact sub_eq_zero.1 ((hu.mul_left_eq_zero).1 hkey)

theorem tch_eq_rB_of_sh_eq : ∀ {l : ℕ} [Fact l.Prime] (q : ℕ), 2 ≤ q → l ∣ q → ∀ (x : Tl l) (y : Om l),
    x ^ q = x → y ^ q = y → sh x = omC y → tch l x = rB l y := by
  intro l _ q hq _ x y hx hy hxy
  refine eq_of_pow_eq_self_of_thB_eq hq ?_ ?_ ?_
  · rw [← tch_pow, hx]
  · rw [← map_pow, hy]
  · rw [thB_tch, thB_rB, hxy, omC_apply]

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerCompatibleSequenceApproximation
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

variable {l : ℕ} [Fact l.Prime]

private def vv (a : ℕ → Tl l) (f n m : ℕ) : Tl l := a (n + m) ^ l ^ (f * m)

private theorem vv_step (a : ℕ → Tl l) {f : ℕ} {ρ : ℝ} (h : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ)
    (n m : ℕ) : ‖vv a f n (m + 1) - vv a f n m‖ ≤ ρ ^ l ^ (f * m) := by
  have e : vv a f n (m + 1) = (a (n + m + 1) ^ l ^ f) ^ l ^ (f * m) := by
    rw [vv, ← pow_mul, ← pow_add, ← add_assoc, mul_add, mul_one, add_comm (f * m) f]
  rw [e, vv, norm_sub_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (h _) _

private theorem pow_bound {f : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hf : 0 < f) (m : ℕ) :
    ρ ^ l ^ (f * m) ≤ ρ ^ m := by
  refine pow_le_pow_of_le_one hρ0 hρ1.le ?_
  have h2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h3 : m ≤ f * m := Nat.le_mul_of_pos_left m hf
  exact h3.trans (Nat.lt_pow_self h2).le

private theorem vv_near (a : ℕ → Tl l) {f : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (h : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ) (n m : ℕ) : ‖vv a f n m - a n‖ ≤ ρ := by
  induction m with
  | zero => simpa [vv] using hρ0
  | succ m ih =>
    have e : vv a f n (m + 1) - a n = (vv a f n (m + 1) - vv a f n m) + (vv a f n m - a n) := by
      abel
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
    refine (vv_step a h n m).trans ?_
    exact pow_le_of_le_one hρ0 hρ1.le (pow_pos (Fact.out : l.Prime).pos _).ne'

theorem exists_tilt_lift_compat {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ) (hf : 0 < f)
    (hl : ‖(l : ℂ_[l])‖ ≤ ρ) (hρ1 : ρ < 1) (Z : ℕ → ℂ_[l])
    (hZ : ∀ n, ‖Z n‖ ≤ 1) (hc : ∀ n, ‖Z (n + 1) ^ l ^ f - Z n‖ ≤ ρ) :
    ∃ u : ℕ → Tl l, (∀ n, u (n + 1) ^ l ^ f = u n) ∧ ∀ n, ‖sh (u n) - Z n‖ ≤ ρ := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hl
  choose a ha using fun n => exists_sh_near (l := l) (Z n) (hZ n)
  have ha' : ∀ n, ‖sh (a n) - Z n‖ ≤ ρ := fun n => (ha n).trans hl
  have hd : ∀ n, ‖a (n + 1) ^ l ^ f - a n‖ ≤ ρ := by
    intro n
    refine norm_sub_le_of_near hl ?_
    have h1 := near_pow hl (hZ (n + 1)) (ha' (n + 1)) (l ^ f)
    have e : sh (a (n + 1) ^ l ^ f) - sh (a n) =
        (sh (a (n + 1) ^ l ^ f) - Z (n + 1) ^ l ^ f) +
          ((Z (n + 1) ^ l ^ f - Z n) + -(sh (a n) - Z n)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc n) ?_)
    rw [norm_neg]
    exact ha' n
  have hcau : ∀ n, CauchySeq (vv a f n) := by
    intro n
    refine cauchySeq_of_le_geometric ρ 1 hρ1 fun m => ?_
    rw [dist_comm, dist_eq_norm, one_mul]
    exact (vv_step a hd n m).trans (pow_bound hρ0 hρ1 hf m)
  choose u hu using fun n => cauchySeq_tendsto_of_complete (hcau n)
  refine ⟨u, fun n => ?_, fun n => ?_⟩
  · have h1 : Filter.Tendsto (fun m => vv a f (n + 1) m ^ l ^ f) Filter.atTop
        (nhds (u (n + 1) ^ l ^ f)) := (hu (n + 1)).pow _
    have h2 : Filter.Tendsto (fun m => vv a f n (m + 1)) Filter.atTop (nhds (u n)) :=
      (hu n).comp (Filter.tendsto_add_atTop_nat 1)
    have e : (fun m => vv a f (n + 1) m ^ l ^ f) = fun m => vv a f n (m + 1) := by
      funext m
      rw [vv, vv, ← pow_mul, ← pow_add, mul_add, mul_one, add_comm (f * m) f, add_assoc,
        add_comm 1 m]
    rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  · have h1 : ‖u n - a n‖ ≤ ρ :=
      le_of_tendsto (((hu n).sub_const (a n)).norm)
        (Filter.Eventually.of_forall fun m => vv_near a hρ0 hρ1 hd n m)
    have h2 := near_of_norm_sub_le hl h1
    have e : sh (u n) - Z n = (sh (u n) - sh (a n)) + (sh (a n) - Z n) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h2 (ha' n))

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerFixedPointApproximation
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_fixed_near : ∀ {l : ℕ} [Fact l.Prime] (f : ℕ) (ρ : ℝ), 0 < f → ‖(l : ℂ_[l])‖ ≤ ρ → ρ < 1 → ∀ c : ℂ_[l],
    ‖c‖ ≤ 1 → ‖c ^ l ^ f - c‖ ≤ ρ → ∃ y : Tl l, y ^ l ^ f = y ∧ ‖sh y - c‖ ≤ ρ := by
  intro l _ f ρ hf hρ hρ1 c hc hcf
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hρ
  obtain ⟨a, ha⟩ := exists_sh_near c hc
  have ha' : ‖sh a - c‖ ≤ ρ := ha.trans hρ
  have hq1 : 1 ≤ l ^ f := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
  have hq2 : 2 ≤ l ^ f := Nat.one_lt_pow hf.ne' (Fact.out : l.Prime).one_lt

  have h0 : ‖a ^ l ^ f - a‖ ≤ ρ := by
    refine norm_sub_le_of_near hρ ?_
    have e : sh (a ^ l ^ f) - sh a =
        (sh (a ^ l ^ f) - c ^ l ^ f) + ((c ^ l ^ f - c) + -(sh a - c)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (near_pow hρ hc ha' _) ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hcf ?_)
    rwa [norm_neg]
  let u : ℕ → Tl l := fun n => a ^ l ^ (f * n)
  have hstep : ∀ n, u (n + 1) = u n ^ l ^ f := by
    intro n
    show a ^ l ^ (f * (n + 1)) = (a ^ l ^ (f * n)) ^ l ^ f
    rw [← pow_mul, ← pow_add, Nat.mul_succ]
  have hdiff : ∀ n, ‖u (n + 1) - u n‖ ≤ ρ ^ (l ^ (f * n)) := by
    intro n
    have e : u (n + 1) - u n = (a ^ l ^ f) ^ l ^ (f * n) - a ^ l ^ (f * n) := by
      show a ^ l ^ (f * (n + 1)) - a ^ l ^ (f * n) = _
      rw [← pow_mul, ← pow_add, Nat.mul_succ, Nat.add_comm]
    rw [e, norm_sub_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h0 _
  have hdiff1 : ∀ n, ‖u (n + 1) - u n‖ ≤ ρ := by
    intro n
    refine (hdiff n).trans ?_
    have : 1 ≤ l ^ (f * n) := Nat.one_le_pow _ _ (Fact.out : l.Prime).pos
    simpa using pow_le_pow_of_le_one hρ0 hρ1.le this
  have hgeom : ∀ n, dist (u n) (u (n + 1)) ≤ 1 * ρ ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm, one_mul]
    refine (hdiff n).trans (pow_le_pow_of_le_one hρ0 hρ1.le ?_)
    have h1 : n < l ^ n := Nat.lt_pow_self (Fact.out : l.Prime).one_lt
    have h2 : l ^ n ≤ l ^ (f * n) :=
      Nat.pow_le_pow_right (Fact.out : l.Prime).pos (Nat.le_mul_of_pos_left n hf)
    omega
  have hcau : CauchySeq u := cauchySeq_of_le_geometric ρ 1 hρ1 hgeom
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcau
  have hclose : ∀ n, ‖u n - a‖ ≤ ρ := by
    intro n
    induction n with
    | zero => simpa [u] using hρ0
    | succ n ih =>
      have e : u (n + 1) - a = (u (n + 1) - u n) + (u n - a) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hdiff1 n) ih)
  have hya : ‖y - a‖ ≤ ρ :=
    le_of_tendsto ((hy.sub_const a).norm) (Filter.Eventually.of_forall hclose)
  refine ⟨y, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun n => u n ^ l ^ f) Filter.atTop (nhds (y ^ l ^ f)) := hy.pow _
    have h2 : Filter.Tendsto (fun n => u n ^ l ^ f) Filter.atTop (nhds y) := by
      simpa only [hstep] using (Filter.tendsto_add_atTop_iff_nat 1).2 hy
    exact tendsto_nhds_unique h1 h2
  · have e : sh y - c = (sh y - sh a) + (sh a - c) := by ring
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (near_of_norm_sub_le hρ hya) ha')

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusArchimedeanFrameConjugationStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_archimedean_frame_conjugation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n r m : ℕ) (J : Matrix (Fin n) (Fin n) E) (X Y : Matrix (Fin n) (Fin r) E) (Z : Matrix (Fin n) (Fin m) E), cT (σ : E →+* E) X * J * Z = 0 → cT (σ : E →+* E) Y * J * Z = 0 → ∀ (t : Fin r → ℝ) (a : GAd σ J), IsTorusElt σ J X Y t a → ∀ (w : InfinitePlace F) (τ : EmbOver E w), archMat σ J τ (projArch σ J w a) * (frm X Z Y).map τ.1 = (frm X Z Y).map τ.1 * diagonal (fun u => ((wt m t u : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.CFin.torus_diag_witt | exact GlobalTheory.CompanionTheory.CFin.torus_diag_witt | (intros; apply GlobalTheory.CompanionTheory.CFin.torus_diag_witt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValuesStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_elements_act_by_gelfand_values : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V) (χ : Fin (m + 1) → ℂ) (v : V), Formalism.REAL.GlRel E → (∀ Y : ℂ, Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) v = Formalism.QuantumDeterminants.capP χ Y • v) → ∀ k : ℕ, Formalism.REAL.etr E k v = GlobalTheory.Dec.gelfVal χ k • v := by
  first | exact @GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli | exact GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli | (intros; apply GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistProductDistributes
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

theorem giso_tw_prod (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (A : GRep k r) (B : GRep k t) (s : ℝ) : GIso ((A.prod B).tw s) ((A.tw s).prod (B.tw s)) :=
  ⟨(GlobalTheory.LocGL.multiProdTwistEquiv (two (stdSum rfl)) (twoRep A.ρ B.ρ)
      (GlobalTheory.LocGL.isSmoothChar_absPow (k := k) (s : ℂ))).trans
    (GlobalTheory.LocGL.multiProdEquiv _ fun x => match x with
      | false => Representation.Equiv.refl _
      | true => Representation.Equiv.refl _)⟩

end GlobalTheory.CompanionTheory.LeibOrd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistTwistAdd
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.LeibOrd

theorem dpow_add_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (s s' : ℝ) (x : GL (Fin n) k) : dpow n (s + s') x = dpow n s x * dpow n s' x := by
  simp only [dpow, detChar_apply, Complex.ofReal_add, absPow_add, MonoidHom.mul_apply]

theorem giso_tw_tw : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (A : GRep k n) (s s' : ℝ), GIso ((A.tw s).tw s') (A.tw (s + s')) := by
  intro k _ _ _ _ n A s s'
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ A.V) fun x => ?_⟩
  ext v
  show ((dpow n s' x : ℂˣ) : ℂ) • ((dpow n s x : ℂˣ) : ℂ) • A.ρ x v = ((dpow n (s + s') x : ℂˣ) : ℂ) • A.ρ x v
  rw [dpow_add_apply, smul_smul, Units.val_mul, mul_comm]

end GlobalTheory.CompanionTheory.LeibOrd

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoinvariantLeviActionStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_coinvariant_levi_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (a : Mir k i) (w : GL (Fin (t + 1)) k) (v : τ.V ⊗[ℂ] σ.V),
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a, w) v) =
    (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
      extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a, w) (qO τ σ ψ v) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Coinv.intertwine | exact GlobalTheory.CompanionTheory.BZPhiPG.Coinv.intertwine | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Coinv.intertwine <;> assumption)
end

