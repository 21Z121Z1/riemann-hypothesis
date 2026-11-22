import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Formalism.FlagUnipotentLattices.Bundle0006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0092
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0218
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0219
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0221
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeRatioMul
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.MassRatioInvBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma sqrt_pow_eq_pow_sqrt (a : ℝ) (ha : 0 ≤ a) (f : ℕ) : Real.sqrt (a ^ f) = Real.sqrt a ^ f := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg a) f), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt ha]

private lemma one_le_factorial_mul_exp_div_pow (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ ((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk0 : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkpos k
  have hn : (k - 1).factorial * k = k.factorial := by
    rw [mul_comm]; exact Nat.mul_factorial_pred (by omega)
  have hf : ((k - 1).factorial : ℝ) * k = (k.factorial : ℝ) := by exact_mod_cast hn
  rw [hf, le_div_iff₀ hk0, one_mul, Real.exp_one_pow]
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (Nat.cast_nonneg k) k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hfac] at h
  rw [mul_comm]
  exact h

theorem one_le_ratio_mul (f k : ℕ) (v L : ℝ) (hv : 0 < v) (hk : 1 ≤ k) (hL : ((2 : ℝ) ^ f)⁻¹ ≤ L) :
    1 ≤ (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) ^ f / Real.sqrt ((2 * v) ^ f) * L *
      ((Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (2 * (k : ℝ) * (2 * v) ^ ((1 : ℝ) / 2)) ^ f) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpi := Real.pi_pos
  have hs0 : 0 < Real.sqrt (2 * v) := Real.sqrt_pos.mpr (by linarith)
  have hrp : (2 * v) ^ ((1 : ℝ) / 2) = Real.sqrt (2 * v) := by rw [Real.sqrt_eq_rpow]
  rw [hrp, sqrt_pow_eq_pow_sqrt (2 * v) (by linarith) f, pow_mul]

  have hcol : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) ^ f / Real.sqrt (2 * v) ^ f * L *
      (((Real.exp 1 * Real.pi / (k * v)) ^ k) ^ f * (2 * (k : ℝ) * Real.sqrt (2 * v)) ^ f) =
      ((((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) * (Real.exp 1 * Real.pi / (k * v)) ^ k *
        (2 * (k : ℝ) * Real.sqrt (2 * v)) / Real.sqrt (2 * v)) ^ f * L := by
    rw [div_pow, mul_pow, mul_pow]
    ring

  have hbase : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) * (Real.exp 1 * Real.pi / (k * v)) ^ k *
      (2 * (k : ℝ) * Real.sqrt (2 * v)) / Real.sqrt (2 * v) =
      (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) * 2 := by
    have hv0 : v ≠ 0 := hv.ne'
    have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
    have hp0 : Real.pi ≠ 0 := hpi.ne'
    have hs : Real.sqrt (2 * v) ≠ 0 := hs0.ne'
    rw [div_pow, div_pow, mul_pow, mul_pow]
    field_simp
  rw [hcol, hbase, mul_pow]
  have hA := one_le_factorial_mul_exp_div_pow k hk
  have hAf : 1 ≤ (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) ^ f := one_le_pow₀ hA
  have h2 : 1 ≤ (2 : ℝ) ^ f * L := by
    have h := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 2 ^ f)
    rwa [mul_inv_cancel₀ (by positivity)] at h
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) ^ f * ((2 : ℝ) ^ f * L) :=
        mul_le_mul hAf h2 zero_le_one (by linarith)
    _ = _ := by ring

theorem stdH_eq (D : D7) (j : ℕ) : Cnt.stdH D.host.E j = massTelescope_form D.host.E j := rfl

theorem stdLat_eq (D : D7) (j : ℕ) : Cnt.stdLat D.host.E j = massTelescope_lat D.host.E j := by
  unfold Cnt.stdLat massTelescope_lat
  congr 2
  funext i
  simp [Pi.basisFun_apply]

theorem massS_eq (D : D7) (j : ℕ) :
    Cnt.massS D j = mass (massTelescope_form D.host.E j) (massTelescope_lat D.host.E j) := by
  unfold Cnt.massS Cnt.massU
  rw [stdH_eq, stdLat_eq]

theorem mass_pred_le : ∀ D : D7, UnitaryVolumeMass.stMassRatio D → Cnt.massS D (D.R.k - 1) ≤ Cnt.massS D D.R.k * ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) * (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) := by
  intro D hM
  have hk : 5 ≤ D.R.k := D.R.k_ge
  have hrd : D.host.rdE = 2 * D.host.v := by
    unfold Formalism.BasicNotions.Host.v
    ring
  have hv : 0 < D.host.v := by
    unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    have hd : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero D.host.E))
    exact div_pos (Real.rpow_pos_of_pos hd _) two_pos
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hL := (GlobalTheory.EtaValueBound.lValEta_bounds D.host.E hK D.R.k (by omega)).1
  rw [Formalism.MainNotions.StandardLattice.fDeg_host] at hL
  have hrat := hM D.R.k (by omega) (Fin D.R.k → D.host.E) (Fin (D.R.k - 1) → D.host.E)
    (massTelescope_form D.host.E D.R.k) (massTelescope_form D.host.E (D.R.k - 1))
    (massTelescope_lat D.host.E D.R.k) (massTelescope_lat D.host.E (D.R.k - 1))
    (massTelescope_symm D.host.E _) (massTelescope_symm D.host.E _)
    (massTelescope_ortho D.host.E _) (massTelescope_ortho D.host.E _)
  unfold massRatioRightSide at hrat
  rw [Formalism.MainNotions.StandardLattice.fDeg_host, Formalism.MainNotions.StandardLattice.vInv_host] at hrat
  have key := one_le_ratio_mul D.R.f D.R.k D.host.v (lValEta D.host.E D.R.k) hv (by omega) hL
  rw [massS_eq, massS_eq, hrd]
  set a := mass (massTelescope_form D.host.E D.R.k) (massTelescope_lat D.host.E D.R.k) with ha
  set b := mass (massTelescope_form D.host.E (D.R.k - 1)) (massTelescope_lat D.host.E (D.R.k - 1))
    with hb
  set R := (((D.R.k - 1).factorial : ℝ) * (D.host.v / Real.pi) ^ D.R.k) ^ D.R.f /
    Real.sqrt ((2 * D.host.v) ^ D.R.f) * lValEta D.host.E D.R.k with hR

  have hb0 : 0 ≤ b := by
    rw [hb]
    unfold mass
    split_ifs
    · exact Finset.sum_nonneg fun _ _ => by positivity
    · exact le_rfl
  have hRpos : 0 < R := by
    have h2 : (0 : ℝ) < (2 ^ D.R.f)⁻¹ := by positivity
    have hLpos : 0 < lValEta D.host.E D.R.k := lt_of_lt_of_le h2 hL
    have hpi := Real.pi_pos
    rw [hR]
    positivity
  have hbne : b ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hrat
    linarith
  have hab : a = R * b := by rw [← hrat, div_mul_cancel₀ a hbne]
  rw [hab]
  calc b = b * 1 := (mul_one b).symm
    _ ≤ b * (R * ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (2 * (D.R.k : ℝ) * (2 * D.host.v) ^ ((1 : ℝ) / 2)) ^ D.R.f)) :=
        mul_le_mul_of_nonneg_left key hb0
    _ = _ := by ring

end GlobalTheory.MassRatioInvBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOne
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec Filter Topology
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Dec.Local

theorem eventually_eq_zero_of_fixed {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (σ : E → E)
    (hadd : ∀ x y, σ (x + y) = σ x + σ y) (hsmul : ∀ (c : ℂ) x, σ (c • x) = star c • σ x)
    (hinv : ∀ x, σ (σ x) = x) (hcont : Continuous σ) (x₀ : E) (hx₀ : σ x₀ = x₀) (f : E → F)
    (hf : ∀ᶠ x in 𝓝 x₀, DifferentiableAt ℂ f x ∧ (σ x = x → f x = 0)) :
    ∀ᶠ x in 𝓝 x₀, f x = 0 := by
  let u : E → E := fun x => (1 / 2 : ℂ) • (x + σ x)
  let v : E → E := fun x => (-Complex.I / 2 : ℂ) • x + (Complex.I / 2 : ℂ) • σ x
  have hu : ∀ x, σ (u x) = u x := by
    intro x
    simp only [u, hsmul, hadd, hinv]
    rw [add_comm]; simp
  have hv : ∀ x, σ (v x) = v x := by
    intro x
    simp only [v, hsmul, hadd, hinv]
    rw [add_comm]; simp
  have huv : ∀ x, u x + Complex.I • v x = x := by
    intro x
    simp only [u, v]
    match_scalars <;> (ring_nf; try simp) <;> norm_num
  have hG : Continuous fun p : E × ℂ => u p.1 + p.2 • v p.1 := by
    simp only [u, v]; fun_prop
  have h0 : ∀ t : ℂ, u x₀ + t • v x₀ = x₀ := by
    intro t
    simp only [u, v, hx₀]
    match_scalars; ring
  have htube : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Metric.closedBall (0 : ℂ) 2,
      DifferentiableAt ℂ f (u x + t • v x) ∧ (σ (u x + t • v x) = u x + t • v x → f (u x + t • v x) = 0) := by
    apply (isCompact_closedBall (0 : ℂ) 2).eventually_forall_of_forall_eventually
    intro t _
    have := hG.tendsto (x₀, t)
    simp only [h0] at this
    exact this.eventually hf
  filter_upwards [htube] with x hx
  have hd : DifferentiableOn ℂ (fun t : ℂ => f (u x + t • v x)) (Metric.ball 0 2) := by
    intro t ht
    exact ((hx t (Metric.ball_subset_closedBall ht)).1.comp t (by fun_prop)).differentiableWithinAt
  have hfr : ∃ᶠ t in 𝓝[≠] (0 : ℂ), f (u x + t • v x) = 0 := by
    have ht : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simpa using hs
    refine ht.frequently (Eventually.frequently ?_)
    have hb : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ∈ Metric.closedBall (0 : ℝ) 2 :=
      nhdsWithin_le_nhds (Metric.closedBall_mem_nhds 0 two_pos)
    filter_upwards [hb] with s hs
    refine (hx s (by simpa using hs)).2 ?_
    rw [hadd, hu, hsmul, hv]; simp
  have := (hd.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball (0 : ℂ) 2).isPreconnected (Metric.mem_ball_self two_pos) hfr
    (show Complex.I ∈ Metric.ball (0 : ℂ) 2 by simp)
  simpa [huv] using this

theorem differentiableAt_of_coef {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (f : E → (W →L[ℂ] W)) (x : E)
    (hf : ∀ u v : W, DifferentiableAt ℂ (fun y => ⟪u, f y v⟫_ℂ) x) : DifferentiableAt ℂ f x := by
  let b := stdOrthonormalBasis ℂ W
  have e : f = fun y => ∑ i, ∑ j, ⟪b i, f y (b j)⟫_ℂ • (innerSL ℂ (b j)).smulRight (b i) := by
    funext y
    ext v
    conv_lhs => rw [← b.sum_repr' v, ← b.sum_repr' (f y _)]
    simp only [map_sum, map_smul, inner_sum, inner_smul_right, _root_.sum_apply,
      _root_.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      Finset.sum_smul, smul_smul]
    simp only [mul_comm]
  rw [e]
  refine DifferentiableAt.fun_sum fun i _ => DifferentiableAt.fun_sum fun j _ => ?_
  exact (hf _ _).smul_const _

open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

def prJ (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (a + Jm ε * a * Jm ε)

theorem prJ_comm (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : prJ ε a * Jm ε = Jm ε * prJ ε a := by
  simp only [prJ, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
    Jm_mul_self, Matrix.mul_one]
  rw [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul, add_comm]

theorem prJ_of_comm {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (h : a * Jm ε = Jm ε * a) :
    prJ ε a = a := by
  rw [prJ, ← h, Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
  match_scalars; norm_num

theorem prJ_one (ε : Fin n → Bool) : prJ ε 1 = 1 := prJ_of_comm (by simp)

theorem prJ_conjTranspose (ε : Fin n → Bool) (a : Matrix (Fin n) (Fin n) ℂ) : prJ ε aᴴ = (prJ ε a)ᴴ := by
  simp [prJ, Jm_conjTranspose, Matrix.mul_assoc]

theorem differentiable_prJ (ε : Fin n → Bool) : Differentiable ℂ (prJ ε) := by
  unfold prJ; fun_prop

theorem eventually_isUnit : ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), IsUnit a :=
  Units.isOpen.mem_nhds isUnit_one

theorem eventually_prJ_mem (ε : Fin n → Bool) : ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), prJ ε a ∈ KC ε := by
  have := ((differentiable_prJ ε).continuous.tendsto' 1 1 (prJ_one ε)).eventually eventually_isUnit
  filter_upwards [this] with a ha
  exact ⟨ha, prJ_comm ε a⟩

theorem posDef_mul_conjTranspose {c : Matrix (Fin n) (Fin n) ℂ} (hc : IsUnit c) : (c * cᴴ).PosDef := by
  rw [(Matrix.posSemidef_self_mul_conjTranspose c).posDef_iff_isUnit]
  exact hc.mul (by simpa [Matrix.star_eq_conjTranspose] using hc.star)

theorem posDef_exp {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ = X) : (NormedSpace.exp X).PosDef := by
  have hY : ((1 / 2 : ℂ) • X)ᴴ = (1 / 2 : ℂ) • X := by simp [hX]
  have e : X = (1 / 2 : ℂ) • X + (1 / 2 : ℂ) • X := by match_scalars; norm_num
  have := posDef_mul_conjTranspose (Matrix.isUnit_exp ((1 / 2 : ℂ) • X))
  rwa [exp_conjTranspose_of_hermitian hY, ← exp_add_self, ← e] at this

variable {ε : Fin n → Bool} {lam : Fin n → ℝ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

theorem eventually_differentiableAt_tau {abelian₂ : Fin n → ℝ} (hτ : IsTau ε abelian₂ τ w) :
    ∀ᶠ a in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), DifferentiableAt ℂ (fun y => τ (prJ ε y)) a := by
  haveI := hτ.1
  filter_upwards [(eventually_prJ_mem ε).eventually_nhds] with a ha
  refine differentiableAt_of_coef _ _ fun u v => ?_
  have h : DifferentiableOn ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ y v⟫_ℂ) (KC ε) := hτ.2.2.1 u v
  have h2 : DifferentiableOn ℂ (fun y : Matrix (Fin n) (Fin n) ℂ => ⟪u, τ (prJ ε y) v⟫_ℂ)
      {y | prJ ε y ∈ KC ε} :=
    h.comp (differentiable_prJ ε).differentiableOn fun y hy => hy
  exact h2.differentiableAt ha

theorem eventually_ps_mul (hB : PsBasic) (hE : PsEquiv) (hl : IsHCParam lam) (hτ : IsTau ε (lowK ε lam) τ w) :
    ∀ᶠ x : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) in 𝓝 ((1, 1), (1, 1)),
      ps ε lam τ w (prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1) -
        τ (prJ ε x.1.1) * ps ε lam τ w (x.1.2 * x.2.2) * τ (prJ ε x.2.1) = 0 := by
  haveI := hτ.1
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  obtain ⟨hopen, hpos, hdiff, -⟩ := hB n ε lam W τ w hl hτ
  have hopen' : IsOpen (U1 ε) := hopen
  have hdiff' : DifferentiableOn ℂ (ps ε lam τ w) (U1 ε) := hdiff
  have hps : ∀ᶠ z in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), DifferentiableAt ℂ (ps ε lam τ w) z := by
    filter_upwards [hopen'.mem_nhds (hpos 1 Matrix.PosDef.one)] with z hz
    exact hdiff'.differentiableAt (hopen'.mem_nhds hz)
  have hP := differentiable_prJ ε
  refine eventually_eq_zero_of_fixed (fun x => ((x.2.1ᴴ, x.2.2ᴴ), (x.1.1ᴴ, x.1.2ᴴ))) ?_ ?_ ?_ ?_ _ ?_ _ ?_
  · intro x y; simp
  · intro c x; simp
  · intro x; simp
  · fun_prop
  · simp
  · let E := (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
    have d1 : Differentiable ℂ fun x : E => prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1 := by
      fun_prop
    have d2 : Differentiable ℂ fun x : E => x.1.2 * x.2.2 := by fun_prop
    have d3 : Differentiable ℂ fun x : E => x.1.1 := by fun_prop
    have d4 : Differentiable ℂ fun x : E => x.2.1 := by fun_prop
    have d5 : Differentiable ℂ fun x : E => x.1.2 := by fun_prop
    filter_upwards [(d1.continuous.tendsto' ((1, 1), (1, 1)) 1 (by simp [prJ_one])).eventually hps,
      (d2.continuous.tendsto' ((1, 1), (1, 1)) 1 (by simp)).eventually hps,
      (d3.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_differentiableAt_tau hτ),
      (d4.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_differentiableAt_tau hτ),
      (d3.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually (eventually_prJ_mem ε),
      (d5.continuous.tendsto' ((1, 1), (1, 1)) 1 rfl).eventually eventually_isUnit] with x h1 h2 h3 h4 h5 h6
    have k1 := DifferentiableAt.comp (𝕜 := ℂ) (g := ps ε lam τ w) (f := fun x : E => prJ ε x.1.1 * (x.1.2 * x.2.2) * prJ ε x.2.1)
      x h1 (d1 x)
    have k2 := DifferentiableAt.comp (𝕜 := ℂ) (g := ps ε lam τ w) (f := fun x : E => x.1.2 * x.2.2) x h2 (d2 x)
    have k3 := DifferentiableAt.comp (g := fun y => τ (prJ ε y)) (𝕜 := ℂ) (f := fun x : E => x.1.1) x h3 (d3 x)
    have k4 := DifferentiableAt.comp (g := fun y => τ (prJ ε y)) (𝕜 := ℂ) (f := fun x : E => x.2.1) x h4 (d4 x)
    refine ⟨k1.sub ((k3.mul k2).mul k4), ?_⟩
    intro hx
    have e1 : x.2.1 = x.1.1ᴴ := (congrArg (fun y => y.2.1) hx).symm
    have e2 : x.2.2 = x.1.2ᴴ := (congrArg (fun y => y.2.2) hx).symm
    rw [e1, e2, prJ_conjTranspose, hE n ε lam W τ w hl hτ _ _ (posDef_mul_conjTranspose h6) h5, sub_eq_zero]
    rfl

theorem psLocal_of (hB : PsBasic) (hE : PsEquiv) : PsLocal := by
  intro n ε lam W _ _ τ w hl hτ
  obtain ⟨hopen, hpos, -, -⟩ := hB n ε lam W τ w hl hτ
  have hopen' : IsOpen (U1 ε) := hopen
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix n ε).1.continuous
  have hu1 : umat (1 : UJ ε) = 1 := rfl
  obtain ⟨L, hLc, hL⟩ := (polar_decomposition_holds n ε).2.2
  have hdec : ∀ g : Matrix (Fin n) (Fin n) ℂ, g * NormedSpace.exp (-L g) * NormedSpace.exp (L g) = g := by
    intro g
    rw [Matrix.mul_assoc, matrix_exp_neg_mul_exp, Matrix.mul_one]
  have h1U : inUJ ε 1 := by simp [inUJ]
  have hL1 : L 1 = 0 := by
    refine ((polar_decomposition_holds n ε).2.1 _ 1 _ 0 (hL 1 h1U).2 ⟨one_mem _, by simp⟩ (hL 1 h1U).1
      (by simp [inP, inG]) ?_).2
    rw [hdec]; simp
  have hLc' : Continuous fun g : UJ ε => L (umat g) := hLc.comp_continuous hu fun g => g.2
  have hexp : Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) := by
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    exact NormedSpace.exp_continuous
  have hc : Continuous fun g : UJ ε =>
      (((umat g * NormedSpace.exp (-L (umat g)), NormedSpace.exp (L (umat g))), (1, 1)) :
        (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) ×
          (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :=
    ((hu.mul (hexp.comp hLc'.neg)).prodMk (hexp.comp hLc')).prodMk continuous_const
  filter_upwards [(hu.tendsto' 1 1 hu1).eventually (hopen'.mem_nhds (hpos 1 Matrix.PosDef.one)),
    (hc.tendsto' 1 ((1, 1), (1, 1)) (by simp [hu1, hL1])).eventually (eventually_ps_mul hB hE hl hτ)]
    with g hg1 hg2
  refine ⟨hg1, ?_⟩
  obtain ⟨hX, hk⟩ := hL (umat g) g.2
  simp only [prJ_one, prJ_of_comm hk.2, mul_one, hτ.2.1.1, hdec, sub_eq_zero] at hg2
  rw [hg2]
  conv_lhs => rw [← hdec (umat g)]
  exact Psi_unitary_mul ε lam τ w hk.1 (posDef_exp (hermitian_of_mem_hermitian_part hX))

end GlobalTheory.Dec.Local

theorem GlobalTheory.Dec.psLocal : PsLocal := GlobalTheory.Dec.Local.psLocal_of GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one GlobalTheory.T.psi_complexifiedK_equivariance
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallSizeCanonicalFlagPiecesProperties
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.FlagPieces

theorem sizesLe_stepLe (I : AutInst) (x : I.GA) {t : ℝ} (ht : 0 < t)
    (A' : Submodule (𝓞 I.E) (Fin I.n → I.E)) : SizesLe I x (stepLe I x t) A' t := by
  intro N _ hN hne
  have hle : stepLe I x t ≤ lamX I x := GlobalTheory.PointFlag.stepLe_le I x t
  have hne0 : stepLe I x t ≠ ⊥ := by
    intro h0
    apply hne
    rw [h0] at hN ⊢
    exact le_bot_iff.mp hN.1
  exact (GlobalTheory.PointFlag.sizeQ_le I x hle hN hne).trans ((GlobalTheory.T.canonicalLatticeFiltration_size_properties I x t ht).2.2.2.2.1 hne0)

theorem perpIn_bot (I : AutInst) (x : I.GA) : perpIn I x ⊥ = lamX I x := by
  apply le_antisymm
  · exact Submodule.span_le.mpr fun y hy => hy.1
  · intro y hy
    apply Submodule.subset_span
    refine ⟨hy, fun s hs => ?_⟩
    rw [(Submodule.mem_bot _).mp hs]
    simp [Formalism.UG.hform]

theorem flag_pieces : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i, SatX I x (S i) ∧ SatX I x (perpIn I x (S i)) ∧ S i ≤ perpIn I x (S (Fin.last a)) ∧ perpIn I x (S (Fin.last a)) ≤ perpIn I x (S i) ∧ rkK (perpIn I x (S i)) + rkK (S i) = I.n) ∧ perpIn I x (S 0) = lamX I x ∧ SizesLe I x (perpIn I x (S (Fin.last a))) (S (Fin.last a)) 2 ∧ ∀ i : Fin a, SizesGe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (perpIn I x (S i.castSucc)) (perpIn I x (S i.succ)) (τ i)⁻¹ ∧ S i.succ ≠ ⊥ ∧ largestSize (bas I) (frm I x) (S i.succ) ≤ τ i ∧ SizesGe I x (lamX I x) (S i.succ) (if h : (i : ℕ) + 1 < a then τ ⟨i + 1, h⟩ else 1 / 2) := by
  intro I x a S τ hF
  have h35 := GlobalTheory.T.orthogonal_canonicalFiltration_steps_autPoint I x
  have h34 := (GlobalTheory.T.canonicalFlag_exists_unique_semistable I x).2.2 a S τ hF
  have hsat : ∀ m, SatX I x (S m) := fun m => GlobalTheory.PointFlag.flag_sat hF m
  have hperpLast : perpIn I x (S (Fin.last a)) = stepLe I x 2 := by
    rw [hF.2.2.1, (h35.2.2.1 (1 / 2) (by norm_num)).2]
    norm_num
  have hle_last : ∀ i, S i ≤ S (Fin.last a) := fun i => hF.2.1.monotone (Fin.le_last i)
  have hlast_le : S (Fin.last a) ≤ stepLe I x 2 := by
    rw [hF.2.2.1]
    exact (GlobalTheory.PointFlag.stepLt_le_stepLe I x _).trans (GlobalTheory.PointFlag.stepLe_mono I x (by norm_num))
  refine ⟨fun i => ?_, ?_, ?_, fun i => ?_⟩
  · have hp := h35.2.2.2 (S i) (S i) (hsat i) (hsat i) le_rfl
    have hp' := h35.2.2.2 (S i) (S (Fin.last a)) (hsat i) (hsat _) (hle_last i)
    refine ⟨hsat i, hp.1, ?_, hp'.2.2.2.1, hp.2.1⟩
    rw [hperpLast]
    exact (hle_last i).trans hlast_le
  · rw [hF.1]
    exact GlobalTheory.FlagPieces.perpIn_bot I x
  · rw [hperpLast]
    exact GlobalTheory.FlagPieces.sizesLe_stepLe I x (by norm_num) _
  · obtain ⟨hcs, _, hlarge, hge, hlei⟩ := h34.1 i
    obtain ⟨hτpos, _, hsucc, _⟩ := hF.2.2.2.2.1 i
    have hsuccle : S i.succ ≤ lamX I x := by
      rw [hsucc]
      exact GlobalTheory.PointFlag.stepLe_le I x _
    refine ⟨?_, hlei, ?_, ?_, hlarge.le, ?_⟩
    · intro N hlt hle
      exact hge N hlt (hle.trans hsuccle)
    · rw [hcs, hsucc, (h35.2.2.1 _ hτpos).1, (h35.2.2.1 _ hτpos).2]
      exact GlobalTheory.FlagPieces.sizesLe_stepLe I x (inv_pos.mpr hτpos) _
    · intro h
      have hlt : S i.castSucc < S i.succ := hF.2.1 (Fin.castSucc_lt_succ ..)
      rw [h] at hlt
      exact not_lt_bot hlt
    · split_ifs with h
      · have e : (⟨(i : ℕ) + 1, h⟩ : Fin a).castSucc = i.succ := Fin.ext (by simp)
        have hn := (h34.1 ⟨(i : ℕ) + 1, h⟩).2.2.2.1
        rw [e] at hn
        intro N hlt hle
        exact hn N hlt hle
      · have hi := i.isLt
        have e : i.succ = Fin.last a := Fin.ext (by simp; omega)
        rw [e, hF.2.2.1]
        intro N hlt hle
        exact (GlobalTheory.T.canonicalLatticeFiltration_size_properties I x (1 / 2) (by norm_num)).2.2.2.2.2.2.2.1 N hlt hle

end GlobalTheory.FlagPieces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.V0MapIotaEqTopDefinite
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef NumberField

theorem GlobalTheory.V0_map_iota_eq_top_of_definite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → (∃ s, A3.A.fam.Ok s) → Function.Surjective ((A3.side3 Ps ψs Zs).Pq A3.A.μ0).mulVec → Function.Surjective (S1.ι A3.A.μ0).mulVec → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D G _ _ Pl0 I0 Ty T m A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I hD hOk hPq hι
  obtain ⟨s, hs⟩ := hOk

  have key := GlobalTheory.rowSide_iota_maps_fixedColumns_onto_of_matrices D (I.tup A3.A.μ0) _ _ _ _
    (I.jA A3.A.μ0) (rE D A3.A Ps ψs A3.A.μ0) (rV0 D A3.A Ps ψs A3.A.μ0)
    ((A3.side3 Ps ψs Zs).Pq A3.A.μ0) (S1.ι A3.A.μ0) I.eRR
    (fun x => (hD.sharp.forms A3.A.μ0).op_eq x)
    (fun F => Formalism.L2.G.ServJoint.level_operator_fixes_image hs Ps ψs (A3.fam3.toSub2 Zs) A3.A.μ0 F)
    hPq hι (fun F => hD.sharp.iota A3.A.μ0 F)
  rw [hD.tup.mu0] at key
  exact key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrableStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_formula_besselUnitary_integrable : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS ν : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → IsQuotMeas μG μS ν → SigmaFinite ν ∧ ν {x | Matrix.of x ∉ GG k r} = 0 ∧ μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2) p.1) ∧ (∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] (f : Mt k r → B), Integrable f μG → Integrable (fun x => ∫ s, f (lmulM (Matrix.of s) x) ∂μS) ν ∧ ∫ x, f x ∂μG = ∫ x, (∫ s, f (lmulM (Matrix.of s) x) ∂μS) ∂ν) ∧ (∀ F : Mt k r → ENNReal, Measurable F → (∀ s ∈ S, ∀ x, F (lmulM s x) = F x) → ∀ y ∈ GG k r, ∫⁻ x, F (rmulM y x) ∂ν = ∫⁻ x, F x ∂ν) := by
  first | exact @GlobalTheory.SgInf.weil_integrable | exact GlobalTheory.SgInf.weil_integrable | (intros; apply GlobalTheory.SgInf.weil_integrable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.XLamLeSmulSupXLamAdmissibleFlagStatement
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xLam_le_smul_sup_xLam_admissible_flag : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'), IsFixedConv Λ g F → IsFixedConv Λ g F' → IsAdmissible Λ g F F' → XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' := by
  first | exact @GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam | exact GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam | (intros; apply GlobalTheory.AdmFlagSub.xLam_le_smul_sup_xLam <;> assumption)
end

