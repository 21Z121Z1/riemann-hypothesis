import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDefs
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.BesselMultiplicityOneL2
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.MainNotions.S

def IsL2BoundedBessel {k r : ℕ} (L : LocBessel k r) (B : L.Hs → L.Wp) : Prop :=
  ∃ (μG ν : Measure (Mt k r)) (C : ℝ), Formalism.FourierDecayAlt.B.IsHaarOn (GV k r) μG ∧
    IsQuotMeas μG ((L.μW.prod L.μN).map fun p => fun i j => (Matrix.of p.2 * Matrix.of p.1) i j) ν ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) L.σ,
      ∫⁻ x : Mt k r, ‖B (L.σ (Matrix.of x) v)‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (C * ‖v‖ ^ 2)

def HasDecay {k r : ℕ} (L : LocBessel k r) (a : ℝ) : Prop :=
  ∃ w ∈ smoothVecs (k := k) (r := r) L.σ, ‖w‖ = 1 ∧
    ∃ C : ℝ, ∀ x ∈ GV k r, ‖⟪w, L.σ x w⟫_ℂ‖ ≤ C * gN x ^ (-a)

def BesselMultiplicityOneL2 : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (B₁ B₂ : L.Hs → L.Wp), L.c ≠ 0 → 1 ≤ k → HasDecay L (aM k r) →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₁ →
    IsBesselMapSm (k := k) (r := r) L.z (psi k r L.z L.c) L.σ L.π B₂ →
    IsL2BoundedBessel L B₁ → IsL2BoundedBessel L B₂ →
    ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ v ∈ smoothVecs (k := k) (r := r) L.σ, a • B₁ v + b • B₂ v = 0

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConvA
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

theorem bc_gN_eq_frob (g : Mat k r) :
    gN g = @Norm.norm _ (Matrix.frobeniusSeminormedAddCommGroup).toNorm g := by
  unfold gN
  rw [Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

theorem bc_gN_mul_le (a b : Mat k r) : gN (a * b) ≤ gN a * gN b := by
  rw [bc_gN_eq_frob, bc_gN_eq_frob, bc_gN_eq_frob]
  exact Matrix.frobenius_norm_mul a b

theorem bc_gN_nonneg (g : Mat k r) : 0 ≤ gN g := Real.sqrt_nonneg _

theorem bc_gN_pos_of_ne {g : Mat k r} (hg : g ≠ 0) : 0 < gN g := by
  obtain ⟨i, j, hij⟩ : ∃ i j, g i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (Matrix.ext h)
  unfold gN
  apply Real.sqrt_pos.mpr
  apply lt_of_lt_of_le (Complex.normSq_pos.mpr hij)
  calc Complex.normSq (g i j) ≤ ∑ j', Complex.normSq (g i j') :=
        Finset.single_le_sum (fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', Complex.normSq (g i' j') :=
        Finset.single_le_sum (f := fun i' => ∑ j', Complex.normSq (g i' j'))
          (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem bc_gN_zero : gN (0 : Mat k r) = 0 := by
  simp [gN]

theorem bc_gN_continuous : Continuous (fun g : Mat k r => gN g) := by
  unfold gN
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

theorem bc_measurable_invM : Measurable (invM (k := k) (r := r)) := by
  have h1 : Continuous fun x : Mt k r => (Matrix.of x : Mat k r).det := continuous_id.matrix_det
  have h2 : Continuous fun x : Mt k r => (Matrix.of x : Mat k r).adjugate := continuous_id.matrix_adjugate
  have he : ∀ (x : Mt k r) (i j : Fin (2 * r + k + 1)),
      invM x i j = ((Matrix.of x : Mat k r).det)⁻¹ * (Matrix.of x : Mat k r).adjugate i j := by
    intro x i j
    simp only [invM, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [he]
  exact h1.measurable.inv.mul ((continuous_apply j).comp ((continuous_apply i).comp h2)).measurable

theorem bc_AB_le_of (b : ℝ) (hb : AS k r + 1 ≤ b) : AB k r ≤ b := by
  unfold AB
  unfold AS nR at hb
  push_cast at hb
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  nlinarith [sq_nonneg ((k : ℝ) + r), sq_nonneg ((r : ℝ) + 1),
    mul_nonneg (sq_nonneg (2 * (r : ℝ) + k + 1)) (by positivity : (0 : ℝ) ≤ 2 * r + k)]

theorem bc_gN_cont_mt : Continuous (fun g : Mt k r => gN (Matrix.of g : Mat k r)) := bc_gN_continuous

def bcPow (A : ℝ) (g : Mt k r) : ℝ≥0∞ := ENNReal.ofReal (gN (Matrix.of g : Mat k r) ^ (-A))

theorem bc_measurable_pow (A : ℝ) : Measurable (bcPow (k := k) (r := r) A) := ENNReal.measurable_ofReal.comp (bc_gN_cont_mt.measurable.pow_const (-A))

theorem bc_continuous_mulM : Continuous (mulM (k := k) (r := r)) := by
  unfold mulM
  exact continuous_fst.matrix_mul continuous_snd

theorem bc_isHaarOn_sigmaFinite {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    SigmaFinite μ := by
  have _ : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem bc_isHaarOn_ae_mem {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := by
  rw [ae_iff]
  exact h.conc

theorem bc_ae_prod_and {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {ν : Measure β} [SFinite μ] [SFinite ν] {P : α → Prop} {Q : β → Prop} (hP : ∀ᵐ x ∂μ, P x)
    (hQ : ∀ᵐ y ∂ν, Q y) : ∀ᵐ p ∂(μ.prod ν), P p.1 ∧ Q p.2 := ((Measure.quasiMeasurePreserving_fst.ae hP).and (Measure.quasiMeasurePreserving_snd.ae hQ))

theorem bc_pow_pos_of_mem (hGL : GNLower) {g : Mat k r} (hg : g ∈ GV k r) (A : ℝ) :
    0 < bcPow A (g : Mt k r) := by
  have h1 : 1 ≤ gN (Matrix.of g : Mat k r) := hGL k r g hg
  unfold bcPow
  exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)

theorem bc_lintegral_pow_ne_zero {α : Type*} [MeasurableSpace α] (hGL : GNLower) {μ : Measure α}
    (hμ : μ ≠ 0) (φ : α → Mt k r) (hφ : Measurable φ) (hmem : ∀ᵐ x ∂μ, (Matrix.of (φ x) : Mat k r) ∈ GV k r)
    (A : ℝ) : (∫⁻ x, bcPow A (φ x) ∂μ) ≠ 0 := by
  intro h0
  have h0' := (lintegral_eq_zero_iff ((bc_measurable_pow A).comp hφ)).mp h0
  have hF : ∀ᵐ x ∂μ, False := by
    filter_upwards [h0', hmem] with x hx hxm
    have hx' : bcPow A (φ x) = 0 := by simpa using hx
    exact (bc_pow_pos_of_mem hGL hxm A).ne' hx'
  exact hμ (ae_eq_bot.mp (Filter.eventually_false_iff_eq_bot.mp hF))

theorem bc_pow_zero {A : ℝ} (hA : A ≠ 0) : bcPow A ((0 : Mat k r) : Mt k r) = 0 := by
  show ENNReal.ofReal (gN (0 : Mat k r) ^ (-A)) = 0
  rw [bc_gN_zero, Real.zero_rpow (neg_ne_zero.mpr hA), ENNReal.ofReal_zero]

theorem norm_power_product_lower_bound {a g b : Mat k r} (ha : IsUnit a) (hb : IsUnit b) (hg : g ≠ 0) {A : ℝ} (hA : 0 ≤ A) :
    bcPow A (g : Mt k r) * (bcPow A (a : Mt k r) * bcPow A (b : Mt k r)) ≤ bcPow A ((a * g * b : Mat k r) : Mt k r) := by
  have hagb : a * g * b ≠ 0 := by
    intro h0
    exact hg ((ha.mul_right_eq_zero).mp ((hb.mul_left_eq_zero).mp h0))
  have pa := bc_gN_pos_of_ne ha.ne_zero
  have pb := bc_gN_pos_of_ne hb.ne_zero
  have pg := bc_gN_pos_of_ne hg
  have pagb := bc_gN_pos_of_ne hagb
  have hle : gN (a * g * b) ≤ gN a * gN g * gN b :=
    calc gN (a * g * b) ≤ gN (a * g) * gN b := bc_gN_mul_le _ _
      _ ≤ gN a * gN g * gN b := mul_le_mul_of_nonneg_right (bc_gN_mul_le _ _) pb.le
  show ENNReal.ofReal (gN g ^ (-A)) * (ENNReal.ofReal (gN a ^ (-A)) * ENNReal.ofReal (gN b ^ (-A))) ≤
    ENNReal.ofReal (gN (a * g * b) ^ (-A))
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg pa.le _), ← ENNReal.ofReal_mul (Real.rpow_nonneg pg.le _)]
  apply ENNReal.ofReal_le_ofReal
  calc gN g ^ (-A) * (gN a ^ (-A) * gN b ^ (-A)) = (gN a * gN g * gN b) ^ (-A) := by
        rw [Real.mul_rpow (mul_nonneg pa.le pg.le) pb.le, Real.mul_rpow pa.le pg.le]
        ring
    _ ≤ gN (a * g * b) ^ (-A) := Real.rpow_le_rpow_of_nonpos pagb hle (by linarith)

theorem bc_lintegral_S_pow_AB (hM : UnitaryGroupStructuralFacts) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) (hW : D.μW' = D.μW) :
    (∫⁻ p : Mt k r × Mt k r, bcPow (AB k r) (mulM (p.2, p.1)) ∂(D.μW.prod D.μN)) < ∞ := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hGI, hGL, -, -, -, hCG, -, -, -, -, -, -, -⟩,
    -, -, -, -, -, -, -, -, -, -, -, -, -, hINB, -, -, -⟩ := hM
  obtain ⟨c, ⟨hc, hF⟩, -⟩ := hINB k r Wp Wq D
  set A := AB k r with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    unfold AB
    positivity
  have hA : A ≠ 0 := by
    rw [hAdef]
    unfold AB
    positivity
  have _ := bc_isHaarOn_sigmaFinite D.haarW
  have _ := bc_isHaarOn_sigmaFinite D.haarN
  have _ := bc_isHaarOn_sigmaFinite D.haarW'
  let f : Mt k r → ℝ≥0∞ := bcPow A
  have hfm : Measurable f := bc_measurable_pow A
  let Fa : Mt k r × Mt k r → Mt k r := fun p => mulM (invM p.1, invM p.2)
  let Gb : Mt k r × Mt k r → Mt k r := fun p => mulM (p.2, p.1)
  have hFa : Measurable Fa := bc_continuous_mulM.measurable.comp (bc_measurable_invM.prodMap bc_measurable_invM)
  have hGb : Measurable Gb := bc_continuous_mulM.measurable.comp measurable_swap
  have hae1 : ∀ᵐ p ∂(D.μW.prod D.μN), (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧
      (Matrix.of p.2 : Mat k r) ∈ Nset k r :=
    bc_ae_prod_and (bc_isHaarOn_ae_mem D.haarW) (bc_isHaarOn_ae_mem D.haarN)
  have hae2 : ∀ᵐ p ∂(D.μW'.prod D.μN), (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z' ∧
      (Matrix.of p.2 : Mat k r) ∈ Nset k r :=
    bc_ae_prod_and (bc_isHaarOn_ae_mem D.haarW') (bc_isHaarOn_ae_mem D.haarN)
  have haeSS := bc_ae_prod_and (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN) hae1 hae2
  have hunitG : ∀ x ∈ GV k r, IsUnit x := fun x hx =>
    (Matrix.isUnit_iff_isUnit_det x).mpr ((hCG k r).unit x hx)
  have hL : (∫⁻ p, f (Fa p) ∂(D.μW.prod D.μN)) ≠ 0 := by
    refine bc_lintegral_pow_ne_zero hGL ?_ Fa hFa ?_ A
    · rw [← Measure.measure_univ_ne_zero, ← Set.univ_prod_univ, Measure.prod_prod]
      exact mul_ne_zero (Measure.measure_univ_ne_zero.mpr D.haarW.ne_zero)
        (Measure.measure_univ_ne_zero.mpr D.haarN.ne_zero)
    · filter_upwards [hae1] with p hp
      exact (hCG k r).mul_mem _ ((hCG k r).inv_mem _ hp.1.1) _ ((hCG k r).inv_mem _ hp.2.1)
  have hlow : ∀ g : Mat k r, g ≠ 0 →
      f g * ((∫⁻ p, f (Fa p) ∂(D.μW.prod D.μN)) * ∫⁻ p, f (Gb p) ∂(D.μW'.prod D.μN)) ≤
        ∫⁻ p, f (sgs p g) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) := by
    intro g hg
    have hprod : ∫⁻ z, f (Fa z.1) * f (Gb z.2) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) =
        (∫⁻ p, f (Fa p) ∂(D.μW.prod D.μN)) * ∫⁻ p, f (Gb p) ∂(D.μW'.prod D.μN) :=
      lintegral_prod_mul (hfm.comp hFa).aemeasurable (hfm.comp hGb).aemeasurable
    have hcm : ∫⁻ z, f g * (f (Fa z.1) * f (Gb z.2)) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) =
        f g * ∫⁻ z, f (Fa z.1) * f (Gb z.2) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    refine (congrArg (f g * ·) hprod.symm).trans_le (hcm.symm.trans_le (lintegral_mono_ae ?_))
    filter_upwards [haeSS] with p hp
    have ha : IsUnit ((Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹) :=
      hunitG _ ((hCG k r).mul_mem _ ((hCG k r).inv_mem _ hp.1.1.1) _ ((hCG k r).inv_mem _ hp.1.2.1))
    have hb : IsUnit ((Matrix.of p.2.2 : Mat k r) * (Matrix.of p.2.1 : Mat k r)) :=
      hunitG _ ((hCG k r).mul_mem _ hp.2.2.1 _ hp.2.1.1)
    have hs : sgs p g = (Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * g *
        ((Matrix.of p.2.2 : Mat k r) * Matrix.of p.2.1) := by
      simp only [sgs, Matrix.mul_assoc]
    exact (norm_power_product_lower_bound ha hb hg hA0).trans_eq (congrArg f hs.symm)
  by_contra hK
  rw [not_lt, top_le_iff] at hK
  have hK' : ∫⁻ p, f (Gb p) ∂(D.μW'.prod D.μN) = ⊤ := by
    rw [hW]
    exact hK
  have hGfin : ∫⁻ g, f g ∂D.μG < ⊤ := hGI k r D.μG A D.haarG le_rfl
  have hGne : ∫⁻ g, f g ∂D.μG ≠ 0 :=
    bc_lintegral_pow_ne_zero hGL D.haarG.ne_zero id measurable_id (bc_isHaarOn_ae_mem D.haarG) A
  let h : (Fin r → ℂ) × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) *
      ∫⁻ p, f (sgs p (bigCell k r q.1 (D.μsec q.2))) ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN))
  have hIF : c • ∫⁻ g, f g ∂D.μG = ∫⁻ q, h q := by
    rw [← lintegral_smul_measure]
    exact hF f hfm
  have h2 : ∀ q, h q = 2 * h q := by
    intro q
    by_cases hw : ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q) = 0
    · simp only [h, hw, zero_mul, mul_zero]
    by_cases hb0 : bigCell k r q.1 (D.μsec q.2) = 0
    · have hz : ∀ p, f (sgs p (bigCell k r q.1 (D.μsec q.2))) = 0 := by
        intro p
        rw [hb0]
        simp only [sgs, Matrix.mul_zero, Matrix.zero_mul]
        exact bc_pow_zero hA
      simp only [h, hz, lintegral_zero, mul_zero]
    · have hpos : f (bigCell k r q.1 (D.μsec q.2)) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (bc_gN_pos_of_ne hb0) _)).ne'
      have hinf := hlow _ hb0
      rw [hK', ENNReal.mul_top hL, ENNReal.mul_top hpos, top_le_iff] at hinf
      show ENNReal.ofReal _ * _ = 2 * (ENNReal.ofReal _ * _)
      rw [hinf, ENNReal.mul_top hw, ENNReal.mul_top two_ne_zero]
  have hfin : ∫⁻ q, h q ≠ ⊤ := by
    rw [← hIF, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hGfin.ne
  have hdouble : ∫⁻ q, h q = 2 * ∫⁻ q, h q := by
    rw [← lintegral_const_mul' 2 h (by norm_num)]
    exact lintegral_congr fun q => h2 q
  have hzero : ∫⁻ q, h q = 0 := by
    have ht : (∫⁻ q, h q).toReal = 2 * (∫⁻ q, h q).toReal := by
      conv_lhs => rw [hdouble]
      simp [ENNReal.toReal_mul]
    have h0 : (∫⁻ q, h q).toReal = 0 := by linarith
    rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h0 | h0
    · exact h0
    · exact absurd h0 hfin
  rw [← hIF, ENNReal.smul_def, smul_eq_mul] at hzero
  rcases mul_eq_zero.mp hzero with h0 | h0
  · exact hc.ne' (ENNReal.coe_eq_zero.mp h0)
  · exact hGne h0

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSymBetaA
section
noncomputable section

open MeasureTheory Matrix Filter Topology
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymBetaA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem deriv_smul_const_any {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (h : ℝ → ℂ) (T : E) :
    deriv (fun t => h t • T) 0 = deriv h 0 • T := by
  by_cases hT : T = 0
  · subst hT
    simp
  by_cases hd : DifferentiableAt ℝ h 0
  · exact deriv_smul_const hd T
  · have hnd : ¬ DifferentiableAt ℝ (fun t => h t • T) 0 := by
      intro hd'
      apply hd
      obtain ⟨φ, -, hφ⟩ := exists_dual_vector ℂ T (norm_ne_zero_iff.mpr hT)
      have hφT : φ T ≠ 0 := by
        rw [hφ]
        exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hT)
      have he : h = fun t => (φ T)⁻¹ * φ (h t • T) := by
        funext t
        rw [map_smul, smul_eq_mul]
        field_simp
      rw [he]
      exact DifferentiableAt.const_mul ((φ.restrictScalars ℝ).differentiableAt.comp (0 : ℝ) hd') _
    rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hd, zero_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem LdV_smul (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    LdV X (fun g => φ g • T) = fun g => LdV X φ g • T := by
  funext g
  exact deriv_smul_const_any _ T

theorem RdV_smul (X : Mat k r) (φ : Mat k r → ℂ) (T : E) :
    RdV X (fun g => φ g • T) = fun g => RdV X φ g • T := by
  funext g
  exact deriv_smul_const_any _ T

theorem Rw_smul (v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    Rw v (fun g => φ g • T) = fun g => Rw v φ g • T := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show RdV X (Rw v (fun g => φ g • T)) = fun g => RdV X (Rw v φ) g • T
    rw [ih]
    exact RdV_smul X (Rw v φ) T

theorem dLR_smul (u v : List (Mat k r)) (φ : Mat k r → ℂ) (T : E) :
    dLR u v (fun g => φ g • T) = fun g => dLR u v φ g • T := by
  induction u with
  | nil => exact Rw_smul v φ T
  | cons X u ih =>
    show LdV X (dLR u v (fun g => φ g • T)) = fun g => LdV X (dLR u v φ) g • T
    rw [ih]
    exact LdV_smul X (dLR u v φ) T

theorem ccle_scalF {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {A : ℝ} {m : ℕ}
    {f : Mat k r → ℂ} {c : ℝ} (hf : CCle A m f c) : CCle A m (scalF Wp f) c := by
  obtain ⟨hck, hb⟩ := hf
  refine ⟨?_, fun u v hu hv hl g hg => ?_⟩
  · intro g₀ hg₀
    obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hck g₀ hg₀
    refine ⟨U, fun g => f' g • ContinuousLinearMap.id ℂ Wp, hU, hgU, hcd.smul contDiffOn_const,
      fun g hgU' hgG => ?_⟩
    simp only [scalF, heq g hgU' hgG]
  · have h1 := hb u v hu hv hl g hg
    have hsc : dLR u v (scalF Wp f) g = dLR u v f g • ContinuousLinearMap.id ℂ Wp :=
      congrFun (dLR_smul u v f (ContinuousLinearMap.id ℂ Wp)) g
    rw [hsc, norm_smul]
    have hid : ‖ContinuousLinearMap.id ℂ Wp‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have hg0 : 0 ≤ gN g ^ A := Real.rpow_nonneg (Real.sqrt_nonneg _) A
    calc gN g ^ A * (‖dLR u v f g‖ * ‖ContinuousLinearMap.id ℂ Wp‖) ≤ gN g ^ A * ‖dLR u v f g‖ := by
          apply mul_le_mul_of_nonneg_left _ hg0
          exact mul_le_of_le_one_right (norm_nonneg _) hid
      _ ≤ c := h1

theorem inCC_scalF {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {A : ℝ} {m : ℕ}
    {f : Mat k r → ℂ} (hf : InCC A m f) : InCC A m (scalF Wp f) := by
  obtain ⟨c, hc⟩ := hf
  exact ⟨c, ccle_scalF hc⟩

theorem inCC_five_four' {A : ℝ} {f : Mat k r → E} (h : InCC A 5 f) : InCC A 4 f := by
  obtain ⟨c, hck, hb⟩ := h
  refine ⟨c, ?_, fun u v hu hv hl g hg => hb u v hu hv (by omega) g hg⟩
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := hck g₀ hg₀
  exact ⟨U, f', hU, hgU, hcd.of_le (WithTop.coe_le_coe.mpr (Nat.cast_le.mpr (by norm_num))), heq⟩

theorem continuousOn_of_ckOn {m : ℕ∞} {f : Mat k r → E} (h : CkOn m (GV k r) f) :
    ContinuousOn f (GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hcd, heq⟩ := h g₀ hg₀
  have hc : ContinuousAt f' g₀ := hcd.continuousOn.continuousAt (hU.mem_nhds hgU)
  refine (hc.continuousWithinAt (s := GV k r)).congr_of_eventuallyEq ?_ (heq g₀ hgU hg₀)
  filter_upwards [inter_mem_nhdsWithin (GV k r) (hU.mem_nhds hgU)] with g hg
  exact heq g hg.2 hg.1

theorem integrable_of_inCC (hInt : GNIntSharp) (hLow : GNLower) (hCl : ClosedG) {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (D : RealPlaceData k r Wp Wq) {A : ℝ} (hA : AB k r ≤ A) {f : Mat k r → ℂ} (hf : InCC A 5 f) :
    Integrable (fun g : Mt k r => f (Matrix.of g)) D.μG := by
  obtain ⟨c, hCk, hbd⟩ := hf
  have hb0 : ∀ g ∈ GV k r, ‖f g‖ ≤ c * gN g ^ (-A) := by
    intro g hg
    have h1 := hbd [] [] (by simp) (by simp) (by simp) g hg
    have hgN : 0 < gN g := lt_of_lt_of_le one_pos (hLow k r g hg)
    have hpow : 0 < gN g ^ A := Real.rpow_pos_of_pos hgN A
    rw [Real.rpow_neg hgN.le, ← div_eq_mul_inv, le_div_iff₀ hpow]
    have h2 : gN g ^ A * ‖f g‖ ≤ c := h1
    linarith [mul_comm (gN g ^ A) ‖f g‖]
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := ae_iff.mpr D.haarG.conc
  have hGm : MeasurableSet {g : Mt k r | Matrix.of g ∈ GV k r} :=
    (show IsClosed {g : Mt k r | Matrix.of g ∈ GV k r} from (hCl k r).closed).measurableSet
  have hgNc : Continuous fun g : Mt k r => gN (Matrix.of g) := by
    unfold gN
    exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))
  have hint : Integrable (fun g : Mt k r => gN (Matrix.of g) ^ (-A)) D.μG := by
    refine ⟨(hgNc.measurable.pow_const (-A)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun g => by
      show (0 : ℝ) ≤ gN (Matrix.of g) ^ (-A)
      unfold gN
      exact Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
    exact hInt k r D.μG A D.haarG hA
  have hcont : ContinuousOn (fun g : Mt k r => f (Matrix.of g)) {g : Mt k r | Matrix.of g ∈ GV k r} :=
    continuousOn_of_ckOn hCk
  have hmeas : AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) D.μG := by
    have := hcont.aestronglyMeasurable (μ := D.μG) hGm
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {g : Mt k r | Matrix.of g ∈ GV k r}) hae] at this
  refine (hint.const_mul c).mono' hmeas (hae.mono fun g hg => ?_)
  exact hb0 _ hg

theorem volume_normSq_eq (c : ℝ) :
    volume {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = c} = 0 := by
  have hsub : {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = c} ⊆
      Set.univ ×ˢ Metric.sphere (0 : ℂ) (Real.sqrt c) := by
    rintro ⟨a, z⟩ hz
    simp only [Set.mem_setOf_eq] at hz
    refine ⟨Set.mem_univ _, ?_⟩
    rw [mem_sphere_zero_iff_norm, ← hz, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  refine measure_mono_null hsub ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.addHaar_sphere, mul_zero]

theorem bcWeight_nonneg (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (by linarith) _)
  · exact le_rfl

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymBetaA
end
end

