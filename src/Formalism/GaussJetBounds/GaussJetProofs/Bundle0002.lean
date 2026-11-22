import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound
import Formalism.GaussJetBounds.Bundle0001
import Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0034

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.AsmRDotAddRight
section
noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem asmR_dot_single {ι : Type v} (i : ι) (k : ℕ) (r : ι → ℝ) :
    dot (Finsupp.single i k) r = (k : ℝ) * r i := by
  unfold dot
  rw [Finsupp.sum_single_index (by simp)]

theorem asmR_dot_pureMon {ι : Type v} [DecidableEq ι] (l : ℕ) (i j : ι) (α β : ℕ) (r : ι → ℝ) :
    dot (pureMon l i j α β) r = (l : ℝ) ^ α * r i + (l : ℝ) ^ β * r j := by
  unfold pureMon dot
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  push_cast
  ring

theorem asmR_dot_add_right {ι : Type v} (n : ι →₀ ℕ) (r s : ι → ℝ) :
    dot n (fun i => r i + s i) = dot n r + dot n s := by
  unfold dot
  simp only [mul_add]
  exact Finsupp.sum_add

theorem asmR_dot_fintype {ι : Type v} [Fintype ι] (n : ι →₀ ℕ) (r : ι → ℝ) :
    dot n r = ∑ i, (n i : ℝ) * r i := by
  unfold dot
  exact Finsupp.sum_fintype _ _ (fun i => by simp)

theorem asmR_dot_nonneg {ι : Type v} (n : ι →₀ ℕ) {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) : 0 ≤ dot n r := by
  unfold dot Finsupp.sum
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hr i)

theorem asmR_monoWtGe_rad {K : Type u} [NormedField K] {ι : Type v} {pi : ℝ} (h0 : 0 < pi)
    (h1 : pi ≤ 1) {r r' : ι → ℝ} (hr : ∀ i, r i ≤ r' i) {w : ℝ} {n : ι →₀ ℕ} {c : K}
    (h : MonoWtGe pi r w n c) : MonoWtGe pi r' w n c := by
  have hd : dot n r ≤ dot n r' := by
    have h := asmR_dot_add_right n r (fun i => r' i - r i)
    have hf : (fun i => r i + (r' i - r i)) = r' := by funext i; ring
    rw [hf] at h
    rw [h]
    linarith [asmR_dot_nonneg n (r := fun i => r' i - r i) (fun i => sub_nonneg.mpr (hr i))]
  unfold MonoWtGe at h ⊢
  exact h.trans (Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith))

private theorem constantCoeff_mvPowerSeries_subst_eq_zero {σ τ R : Type*} [CommRing R] [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    {f : MvPowerSeries σ R} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ : ∃ s, n s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (Finsupp.ext h)
    have hp : MvPowerSeries.constantCoeff (n.prod fun s e => a s ^ e) = 0 := by
      simp only [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      rw [map_pow, ha s, zero_pow hs]
    rw [hp, smul_zero]

theorem lemmaR_of (hS : LemmaS.{u}) (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u})
    (hW1 : SubstWt.{u, 0, v}) (hW0 : SubstWt.{u, 0, 0}) (hRM : RadMono.{u, v})
    (hMW : MulWtLe.{u, v}) (hE : ExpWtLe.{u, v}) (hF : FactVal.{u, v})
    (hP : PureCross.{u, v}) : LemmaR.{u, v} := by
  intro K _ _ _ l d N0 N1 _ hl hlo hd hde hpi K0 hK0 ζ hζ be hBH ι _ _ lt M hM hlt g hg0 hgl U hU
    ε hε sig hsig κ hpure
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne_zero
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr hl0
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hρ : 0 ≤ rho l := by
    unfold rho
    apply div_nonneg zero_le_one
    nlinarith
  have hr : ∀ i, (fun _ : ι => rho l) i ≤ (fun i => rho l + sig i) i := fun i => by
    simp only
    linarith [hsig i]

  obtain ⟨hbw, hbn⟩ := hS K l d hl hlo hd hde hpi K0 hK0 ζ hζ be hBH
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    by_contra hne
    have := (hBH.2.2.1 0 (by rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])).1
    simp [degE] at this
  obtain ⟨hsw, hsn⟩ := hP K l d N0 N1 hl hpi ι M hM be hbe0 hbw hbn

  have hlin0 : ∀ x, MvPowerSeries.constantCoeff (linSub M x) = 0 := fun x => by
    simp [linSub]
  have hlinw : ∀ x, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (linSub M x) := by
    intro x n
    unfold MonoWtGe
    by_cases hn : ∃ i, n = Finsupp.single i 1
    · obtain ⟨i, rfl⟩ := hn
      have hc : MvPowerSeries.coeff (Finsupp.single i 1) (linSub M x) = M x i := by
        simp only [linSub, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
        rw [Finset.sum_eq_single i (fun j _ hji => by
          rw [if_neg (fun h => hji ((Finsupp.single_left_inj one_ne_zero).mp h).symm), mul_zero])
          (by simp), if_pos rfl, mul_one]
      rw [hc, asmR_dot_single, Nat.cast_one, one_mul, sub_self, Real.rpow_zero]
      exact hM x i
    · have hc : MvPowerSeries.coeff n (linSub M x) = 0 := by
        simp only [linSub, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [if_neg (fun h => hn ⟨i, h⟩), mul_zero]
      rw [hc, norm_zero]
      exact (Real.rpow_pos_of_pos hpi0 _).le

  have hgw : ∀ x, WtGe ‖(l : K)‖ (fun _ => rho l) (rho l) (g x) := by
    have hb := (hB K l d N0 N1).2.1
    exact hG K l hl hpi (ZV d N0 N1) (fun y => (y.1 - 2, y.2.1, y.2.2)) g hg0
      (fun x => by rw [← hb x]; exact hgl x)
  have hUw : WtGe ‖(l : K)‖ (fun _ => rho l) 0 U := by
    intro n
    unfold MonoWtGe
    exact (hU n).trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hpi0 hpi.le
      (by linarith [asmR_dot_nonneg n (r := fun _ => rho l) (fun _ => hρ)]))
  have hgU := hW0 K _ hpi0 hpi (ZV d N0 N1) (ZV d N0 N1) g (fun _ => rho l) (fun _ => rho l) 0 U
    hg0 hgw hUw
  have hA := hW1 K _ hpi0 hpi (ZV d N0 N1) ι (linSub M) (fun _ => rho l) (fun _ => rho l) 0 _
    hlin0 hlinw hgU
  have hA' := (hRM K _ hpi0 hpi ι (fun _ => rho l) (fun i => rho l + sig i) 0 hr).1 _ hA
  have hAle : WtGeLe ‖(l : K)‖ (fun i => rho l + sig i) 0 κ
      (MvPowerSeries.subst (linSub M) (MvPowerSeries.subst g U)) := fun n _ => hA' n

  have hbs0 : MvPowerSeries.constantCoeff (bSum M be) = 0 := by
    simp only [bSum, map_sum]
    exact Finset.sum_eq_zero fun ab _ => constantCoeff_mvPowerSeries_subst_eq_zero (fun s => hlin0 _) hbe0
  have hεbs0 : MvPowerSeries.constantCoeff (ε • bSum M be) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_smul,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hbs0, smul_zero]
  have hεn : ‖ε‖ = 1 := by rcases hε with rfl | rfl <;> simp
  have hB1 : WtGeLe ‖(l : K)‖ (fun i => rho l + sig i) (1 / ((l : ℝ) - 1)) κ (ε • bSum M be) := by
    intro n hn
    unfold MonoWtGe
    rw [map_smul, smul_eq_mul, norm_mul, hεn, one_mul]
    have hsplit : dot n (fun i => rho l + sig i) = dot n (fun _ => rho l) + dot n sig :=
      asmR_dot_add_right n _ _
    by_cases hp : ∃ (i j : ι) (α β : ℕ), n = pureMon l i j α β
    · obtain ⟨i, j, α, β, rfl⟩ := hp
      by_cases hm : MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
          (MvPowerSeries.coeff (pureMon l i j α β) (bSum M be))
      · exact asmR_monoWtGe_rad hpi0 hpi.le hr hm
      · have h1 := hpure i j α β hn hm
        have h2 := hsw (pureMon l i j α β)
        unfold MonoWtGe at h2
        rw [hsplit, asmR_dot_pureMon l i j α β sig]
        refine h2.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hpi.le ?_)
        linarith
    · exact asmR_monoWtGe_rad hpi0 hpi.le hr (hsn n hp)
  have hBle := hE K l hl hpi ι (fun i => rho l + sig i) κ _ hεbs0 hB1
  have hprod := hMW K _ hpi0 ι (fun i => rho l + sig i) 0 0 κ _ _ hAle hBle κ le_rfl
  unfold MonoWtGe at hprod
  have hfac := hF K l hl hpi ι κ
  have h1' : (l : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith)
  have h2' : (l : ℝ) ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith)
  have hγ : gam l = 1 / ((l : ℝ) - 1) - rho l := by
    unfold gam rho
    field_simp
    ring
  rw [norm_mul]
  refine (mul_le_mul hfac hprod (norm_nonneg _) (Real.rpow_nonneg hpi0.le _)).trans (le_of_eq ?_)
  rw [← Real.rpow_add hpi0, asmR_dot_fintype]
  congr 1
  have hterm : ∀ i, (κ i : ℝ) * (gam l - sig i) =
      (κ i : ℝ) / ((l : ℝ) - 1) - (κ i : ℝ) * (rho l + sig i) := fun i => by
    rw [hγ]
    ring
  simp only [hterm, Finset.sum_sub_distrib]
  ring

end Formalism.DworkPowerSeriesWeights
end
end

-- bundled from Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
section
noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

section Norms

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem norm_natCast_eq_one_of_not_dvd {l m : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    (hm : ¬ l ∣ m) : ‖(m : K)‖ = 1 := by
  first | exact GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd .. | (apply GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd <;> assumption) | (intros; apply GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd <;> assumption) | (apply @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd <;> assumption) | (intros; apply @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd <;> assumption) | (apply @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd <;> first | assumption | infer_instance) | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› l m hl hlt hm | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› l m hl hlt | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› l m hl | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› l m | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› l | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› ‹_› | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K ‹_› | exact @GlobalTheory.NatCastUnitNorm.norm_natCast_eq_one_of_not_dvd K

theorem norm_natCast_eq_pow_padicValNat {l n : ℕ} (hl : l.Prime) (hlt : ‖(l : K)‖ < 1)
    (hn : n ≠ 0) : ‖(n : K)‖ = ‖(l : K)‖ ^ padicValNat l n := by
  have hfac := Nat.ordProj_mul_ordCompl_eq_self n l
  have hnd := Nat.not_dvd_ordCompl hl hn
  rw [Nat.factorization_def n hl] at hfac hnd
  conv_lhs => rw [← hfac]
  rw [Nat.cast_mul, norm_mul, Nat.cast_pow, norm_pow, norm_natCast_eq_one_of_not_dvd hl hlt hnd,
    mul_one]

end Norms

theorem multiplicative_weight_le : MulWtLe.{u, v} := by
  intro K _ _ pi h0 ι r w1 w2 κ f g hf hg
  classical
  intro n hn
  rw [monoWtGe_iff, MvPowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
    fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have h1 : x.1 ≤ κ := le_trans (hx ▸ le_self_add) hn
  have h2 : x.2 ≤ κ := le_trans (hx ▸ le_add_self) hn
  rw [norm_mul, ← hx, dot_add]
  calc ‖MvPowerSeries.coeff x.1 f‖ * ‖MvPowerSeries.coeff x.2 g‖
      ≤ pi ^ (w1 - dot x.1 r) * pi ^ (w2 - dot x.2 r) :=
        mul_le_mul (hf x.1 h1) (hg x.2 h2) (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = pi ^ (w1 + w2 - (dot x.1 r + dot x.2 r)) := by
        rw [← Real.rpow_add h0]; congr 1; ring

theorem wtGeLe_pow {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v} {pi : ℝ}
    (h0 : 0 < pi) {r : ι → ℝ} {wt : ℝ} {κ : ι →₀ ℕ} {f : MvPowerSeries ι K}
    (hf : WtGeLe pi r wt κ f) (k : ℕ) : WtGeLe pi r (k * wt) κ (f ^ k) := by
  induction k with
  | zero =>
    intro n _
    simpa using wtGe_one (K := K) h0 r n
  | succ k ih =>
    rw [pow_succ]
    have := multiplicative_weight_le K pi h0 ι r _ _ κ _ _ ih hf
    push_cast
    rwa [add_mul, one_mul]

theorem exponential_weight_le : ExpWtLe.{u, v} := by
  intro K _ _ _ l hl hlt ι r κ B hB0 hB
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have hs : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero hB0
  intro n hn
  rw [monoWtGe_iff]
  unfold mvExp
  rw [PowerSeries.coeff_subst hs]
  refine norm_finsum_le_of (Real.rpow_nonneg hpi0.le _) fun k => ?_
  rw [PowerSeries.coeff_exp, smul_eq_mul, norm_mul]
  have hk := wtGeLe_pow hpi0 hB k n hn
  rw [monoWtGe_iff] at hk
  have hfk : (k.factorial : ℕ) ≠ 0 := Nat.factorial_ne_zero k
  have hnorm : ‖(algebraMap ℚ K) (1 / (k.factorial : ℚ))‖ =
      ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ)) := by
    rw [map_div₀, map_one, map_natCast, norm_div, norm_one,
      norm_natCast_eq_pow_padicValNat hl hlt hfk, Real.rpow_neg hpi0.le, Real.rpow_natCast,
      one_div]
  rw [hnorm]

  have hv : (padicValNat l k.factorial : ℝ) ≤ (k : ℝ) * (1 / ((l : ℝ) - 1)) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0; simp
    · have := (Formalism.IncomingBounds.padicValFactorialBounds l hl k hk0).2
      have hl0 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
      calc (padicValNat l k.factorial : ℝ) ≤ ((k : ℝ) - 1) / ((l : ℝ) - 1) := this
        _ ≤ (k : ℝ) / ((l : ℝ) - 1) := by
          apply div_le_div_of_nonneg_right _ hl0.le; linarith
        _ = (k : ℝ) * (1 / ((l : ℝ) - 1)) := by ring
  calc ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ)) * ‖MvPowerSeries.coeff n (B ^ k)‖
      ≤ ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ)) *
          ‖(l : K)‖ ^ ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r) :=
        mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hpi0.le _)
    _ = ‖(l : K)‖ ^ (-(padicValNat l k.factorial : ℝ) +
          ((k : ℝ) * (1 / ((l : ℝ) - 1)) - dot n r)) := by rw [← Real.rpow_add hpi0]
    _ ≤ ‖(l : K)‖ ^ (0 - dot n r) :=
        Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by linarith)

theorem factorial_valuation_bound : FactVal.{u, v} := by
  intro K _ _ _ l hl hlt ι _ κ
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  set L : ℝ := Real.logb l (κ.degree : ℝ) + 1 with hL
  have hL0 : 0 ≤ L := by
    rcases Nat.eq_zero_or_pos κ.degree with h | h
    · rw [hL, h]; simp
    · have : 0 ≤ Real.logb l (κ.degree : ℝ) :=
        Real.logb_nonneg hl1 (by exact_mod_cast h)
      linarith

  have hcoord : ∀ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖ ≤
      ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) := by
    intro i hi
    have hki : 1 ≤ κ i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have hb := (Formalism.IncomingBounds.padicValFactorialBounds l hl (κ i) hki).1
    have hdeg : (κ i : ℝ) ≤ (κ.degree : ℝ) := by
      have : κ i ≤ κ.degree := by
        rw [Finsupp.degree_apply]
        exact Finset.single_le_sum (f := fun j => κ j) (fun j _ => Nat.zero_le _) hi
      exact_mod_cast this
    have hlog : Real.logb l (κ i : ℝ) ≤ Real.logb l (κ.degree : ℝ) :=
      Real.logb_le_logb_of_le hl1 (by exact_mod_cast hki) hdeg
    rw [norm_natCast_eq_pow_padicValNat hl hlt (Nat.factorial_ne_zero _), ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by rw [hL]; linarith)
  have hmf : ((mfact κ : ℕ) : K) = ∏ i ∈ κ.support, (((κ i).factorial : ℕ) : K) := by
    rw [mfact, Finsupp.prod, Nat.cast_prod]
  rw [hmf, norm_prod]
  calc ∏ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖
      ≤ ∏ i ∈ κ.support, ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) :=
        Finset.prod_le_prod (fun i _ => norm_nonneg _) hcoord
    _ = ‖(l : K)‖ ^ (∑ i ∈ κ.support, ((κ i : ℝ) / ((l : ℝ) - 1) - L)) :=
        (Real.rpow_sum_of_pos hpi0 _ _).symm
    _ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - (Fintype.card ι : ℝ) * L) := by
        apply Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        have hsum : ∑ i ∈ κ.support, (κ i : ℝ) / ((l : ℝ) - 1) =
            ∑ i, (κ i : ℝ) / ((l : ℝ) - 1) := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          rw [Finsupp.notMem_support_iff.mp hi]; simp
        have hcard : (κ.support.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast Finset.card_le_univ _
        rw [hsum]
        nlinarith

end Formalism.DworkPowerSeriesWeights
end
end

