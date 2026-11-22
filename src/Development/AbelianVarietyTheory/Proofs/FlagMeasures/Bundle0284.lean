import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0057
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0276
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
import Formalism.LocalToGlobal.SiegelLatticeTheory.ResidEvFree
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0241
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCommonStabiliserUnitriangularCoords
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StCoord

theorem zh_eq (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (VS D) D.R.rS T) (F0' : LFlag (VS D) D.R.rS T')
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k)
    (c : GCoord Z F0 F0' FP G) : G.Zh = ZhatL F0 F0' := by
  have hs : ∀ x : D.host.E, D.conjF x = star x := fun x => by
    rw [D.conjF_eq]; exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  funext a b
  have := c.h_eq (frame F0' b) (frame F0 a)
  simp only [GFrames.Zh, Matrix.of_apply, c.f_eq, c.f'_eq]
  simp only [hs]
  exact this

theorem stab_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), (∀ x ∈ G.St, ∃ B : Formalism.L2.SG.PairVal.MatR D, IsUpUni B ∧ (∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) ∧ ∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → B a b = 0) ∧ ∀ B : Formalism.L2.SG.PairVal.MatR D, IsUpUni B → (∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → B a b = 0) → ∃! x, x ∈ G.St ∧ ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a := by
  intro D X Y u u' _ _ w F00 F'0 FP hw _ _ G c
  have hZ : Formalism.MainNotions.S.ZhatOM G.Zh = Formalism.MainNotions.S.ptMat w := by rw [zh_eq D _ F00 F'0 FP G c]; exact hw
  have hinv : ∀ x, (D.conjF : D.host.E →+* D.host.E) ((D.conjF : D.host.E →+* D.host.E) x) = x := by
    intro x
    have hs : ∀ x : D.host.E, D.conjF x = star x := fun x => by
      rw [D.conjF_eq]; exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
    show D.conjF (D.conjF x) = x
    rw [hs, hs, star_star]
  obtain ⟨hb1, hb2⟩ := GlobalTheory.T.unitriangularStabilizer_pointMatrix_blockDiagonal (D.conjF : D.host.E →+* D.host.E) hinv D.R.rS w G.Zh hZ
  have up : ∀ s : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ↔ Formalism.MainNotions.S.IsUpUni s := by
    intro s
    constructor
    · rintro ⟨h1, h2⟩ i j; exact ⟨h1 i j, fun h => h ▸ h2 i⟩
    · intro h; exact ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩
  refine ⟨fun x hx => ?_, fun B hB hBb => ?_⟩
  · obtain ⟨s, s', hs, hs', hf, hf'⟩ := GlobalTheory.T.globalFrameStabilizer_acts_unitriangular _ _ _ G x hx
    have hZs := (GlobalTheory.T.hermitianStabiliser_rational_unitriangular_pairs _ _ _ G s s' hs hs').2 ⟨x, hx, hf, hf'⟩
    exact ⟨s', (up s').1 hs', hf', hb1 s s' ((up s).1 hs) ((up s').1 hs') hZs⟩
  · obtain ⟨s, hs, hZs⟩ := hb2 B hB hBb
    obtain ⟨h, hh, -, hh'⟩ := (GlobalTheory.T.hermitianStabiliser_rational_unitriangular_pairs _ _ _ G s B ((up s).2 hs) ((up B).2 hB)).1 hZs
    refine ⟨h, ⟨hh, hh'⟩, fun y ⟨hy, hy'⟩ => ?_⟩
    have h1 : h⁻¹ * y = 1 := by
      refine GlobalTheory.T.rationalCommonStabiliser_eq_one_of_fixes_second_frame _ _ _ G _ (G.St.mul_mem (G.St.inv_mem hh) hy) fun b => ?_
      show h.symm (y (G.f' b)) = G.f' b
      rw [hy', ← hh' b, LinearEquiv.symm_apply_apply]
    calc y = h * (h⁻¹ * y) := by group
      _ = h := by rw [h1, mul_one]

end GlobalTheory.HL.StCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SimpleRootCoefEqSuperdiagonalSumFrames
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SlocCoef

theorem rationalDualPairing_eq_scaledLocalPairing {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) {r k : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (S : Frames (A.L p) r k) (Hm : Matrix (Fin (k + 2 * r + 1)) (Fin (k + 2 * r + 1)) E)
    (c : ((A.loc p).Fp)ˣ) (hHm : S.Hm = Hm.map (A.loc p).ιE)
    (fv : Fin (r + 1) → Fin (k + 2 * r + 1) → E) (ev : Fin r → Fin (k + 2 * r + 1) → E)
    (Sf : Fin (r + 1) → Fin (k + 2 * r + 1) → (A.loc p).Ep) (Se : Fin r → Fin (k + 2 * r + 1) → (A.loc p).Ep)
    (hfe : ∀ a : Fin (r + 1), algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ))) • Sf a = A.bc p (fv a))
    (hee : ∀ a : Fin r, Se a = algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (ev a))
    (hd : ∀ a j, hf (A.L p) S.Hm (Sf a) (Se j) = if a = j.castSucc then 1 else 0)
    (b : Fin (r + 1)) (a : Fin r) :
    ∑ i, ∑ j, fv b i * Hm i j * sig (ev a j) = if b = a.castSucc then 1 else 0 := by
  haveI := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
  set α : ℕ → (A.loc p).Ep := fun n => algebraMap (A.loc p).Fp (A.loc p).Ep ((c : (A.loc p).Fp) ^ (r - n)) with hα
  have hu : ∀ n, IsUnit (α n) := fun n => ((c.isUnit.pow _)).map _
  have key := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 Hm (fv b) (ev a)
  have h1 : hf (A.L p) S.Hm (A.bc p (fv b)) (Se a) = α b * (if b = a.castSucc then 1 else 0) := by
    rw [← hfe b, ← hd b a]
    simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have h2 : hf (A.L p) S.Hm (A.bc p (fv b)) (Se a) = (A.loc p).ιE (∑ i, ∑ j, fv b i * Hm i j * sig (ev a j)) * α a := by
    rw [hee a, ← key, hHm]
    simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.sum_mul, hα]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h1] at h2
  split_ifs at h2 ⊢ with hb
  · subst hb
    have ha : ((a.castSucc : Fin (r + 1)) : ℕ) = (a : ℕ) := Fin.coe_castSucc a
    rw [ha, mul_one] at h2
    have h3 : (A.loc p).ιE (∑ i, ∑ j, fv a.castSucc i * Hm i j * sig (ev a j)) = (A.loc p).ιE 1 := by
      rw [map_one]
      exact (hu (a : ℕ)).mul_right_cancel (by rw [one_mul]; exact h2.symm)
    exact (A.loc p).ιE.injective h3
  · rw [mul_zero] at h2
    have h3 := ((hu (a : ℕ)).mul_left_eq_zero).mp h2.symm
    exact (A.loc p).ιE.injective (by rw [h3, map_zero])

end GlobalTheory.SlocCoef

namespace GlobalTheory.SlocCoef

theorem pair_f_es {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (b : Fin (r + 1)) (a : Fin r) :
    ∑ i, ∑ j, G.f b i * G.Hm i j * sig (G.es a j) = if b = a.castSucc then 1 else 0 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  exact rationalDualPairing_eq_scaledLocalPairing A p (G.S p) G.Hm (G.c p) (G.Hm_eq p) G.f G.es (G.S p).f (G.S p).es
    (G.f_eq p) (G.es_eq p) (G.S p).dual b a

theorem pair_f'_es' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (b : Fin (r + 1)) (a : Fin r) :
    ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.es' a j) = if b = a.castSucc then 1 else 0 := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  let p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨P, hP.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩
  exact rationalDualPairing_eq_scaledLocalPairing A p (G.S p) G.Hm (G.c p) (G.Hm_eq p) G.f' G.es' (G.S p).f' (G.S p).es'
    (G.f'_eq p) (G.es'_eq p) (G.S p).dual' b a

theorem coef_sum {E : Type} [Field E] [NumberField E] (sig : E → E) {r n : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (fv : Fin (r + 1) → Fin n → E) (ev : Fin r → Fin n → E)
    (hd : ∀ b a, ∑ i, ∑ j, fv b i * Hm i j * sig (ev a j) = if b = a.castSucc then 1 else 0)
    (N : (Fin n → E) ≃ₗ[E] (Fin n → E)) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hN : ∀ b, N (fv b) = ∑ a, B a b • fv a) :
    (∑ a : Fin r, ∑ i, ∑ j, N (fv a.succ) i * Hm i j * sig (ev a j)) = Formalism.L2.SG.PairVal.sgUp B := by
  have h1 : ∀ a : Fin r, ∑ i, ∑ j, N (fv a.succ) i * Hm i j * sig (ev a j) = B a.castSucc a.succ := by
    intro a
    rw [hN]
    have e : ∀ i j, (∑ c, B c a.succ • fv c) i * Hm i j * sig (ev a j) =
        ∑ c, B c a.succ * (fv c i * Hm i j * sig (ev a j)) := by
      intro i j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    simp_rw [e]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hd]
    simp
  rw [Finset.sum_congr rfl fun a _ => h1 a]
  unfold Formalism.L2.SG.PairVal.sgUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, lt_self_iff_false, dif_neg, not_false_eq_true, add_zero,
    add_lt_add_iff_right, Fin.is_lt, dif_pos]
  refine Finset.sum_congr rfl fun a _ => ?_
  rfl

end GlobalTheory.SlocCoef

theorem GlobalTheory.SlocCoef.main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (B : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (N : G.GLV), ((∀ b, N (G.f b) = ∑ a, B a b • G.f a) → (∑ a : Fin r, ∑ i, ∑ j, N (G.f a.succ) i * G.Hm i j * sig (G.es a j)) = Formalism.L2.SG.PairVal.sgUp B) ∧ ((∀ b, N (G.f' b) = ∑ a, B a b • G.f' a) → (∑ a : Fin r, ∑ i, ∑ j, N (G.f' a.succ) i * G.Hm i j * sig (G.es' a j)) = Formalism.L2.SG.PairVal.sgUp B) := by
  intro F E _ _ _ _ _ sig A r k G B N
  exact ⟨GlobalTheory.SlocCoef.coef_sum sig G.Hm G.f G.es (GlobalTheory.SlocCoef.pair_f_es G) N B,
    GlobalTheory.SlocCoef.coef_sum sig G.Hm G.f' G.es' (GlobalTheory.SlocCoef.pair_f'_es' G) N B⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoRescaledIntegralOfDensityOne
section
open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.VagueRescale

theorem integral_le_of_small_balls {d : ℕ} (μ ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] (κ : ℝ) (hκ : 0 ≤ κ)
    (U : Set (EuclideanSpace ℝ (Fin d)))
    (h : ∀ x ∈ U, ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      μ (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r))
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (h0 : ∀ x, 0 ≤ f x) (hU : ∀ x ∉ U, f x = 0) :
    ∫ x, f x ∂μ ≤ κ * ∫ x, f x ∂ν := by
  have hcν : ∀ A, (κ.toNNReal • ν) A = ENNReal.ofReal κ * ν A := fun A => by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]; rfl

  have hsub : ∀ s ⊆ U, μ s ≤ (κ.toNNReal • ν) s := by
    intro s hs
    refine (Besicovitch.vitaliFamily μ).measure_le_of_frequently_le (κ.toNNReal • ν)
      (Measure.AbsolutelyContinuous.refl μ) s fun x hx => ?_
    have hfr := (Besicovitch.tendsto_filterAt μ x).frequently
      (p := fun a => μ a ≤ ENNReal.ofReal κ * ν a) (h x (hs hx)).frequently
    exact hfr.mono fun a ha => ha.trans_eq (hcν a).symm
  have hle : μ.restrict U ≤ κ.toNNReal • ν.restrict U := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs, ← Measure.smul_apply]
    exact hsub _ Set.inter_subset_right
  calc ∫ x, f x ∂μ = ∫ x, f x ∂(μ.restrict U) := (setIntegral_eq_integral_of_forall_compl_eq_zero hU).symm
    _ ≤ ∫ x, f x ∂(κ.toNNReal • ν.restrict U) :=
        integral_mono_measure hle (Filter.Eventually.of_forall h0) (hf.integrable_of_hasCompactSupport hc)
    _ = κ * ∫ x, f x ∂ν := by
        rw [integral_smul_nnreal_measure, setIntegral_eq_integral_of_forall_compl_eq_zero hU,
          NNReal.smul_def, Real.coe_toNNReal _ hκ, smul_eq_mul]

private theorem rescaled_integral_comparable_of_nonneg_compactSupport {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure ν] (κ δ : ℝ) (hκ : 1 < κ)
    (hball : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ →
      ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ν (Metric.closedBall x r) ≤ ENNReal.ofReal κ * volume (Metric.closedBall x r) ∧
        volume (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (h0 : ∀ x, 0 ≤ φ x) (R r : ℝ) (hR : ∀ x : EuclideanSpace ℝ (Fin d), R ≤ ‖x‖ → φ x = 0)
    (hr : 0 < r) (hrR : r * R < δ) :
    (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν ≤ κ * ∫ x, φ x ∧
      ∫ x, φ x ≤ κ * ((r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin d) => r⁻¹ • x) :=
    (continuous_const_smul _).measurable
  have hJ : ∫ x, φ x ∂(ν.map (fun x => r⁻¹ • x)) = ∫ x, φ (r⁻¹ • x) ∂ν :=
    integral_map hmeas.aemeasurable hφ.aestronglyMeasurable
  have hrd : 0 < r ^ d := pow_pos hr d

  have hpre : ∀ (y : EuclideanSpace ℝ (Fin d)) (s : ℝ), 0 ≤ s →
      (ν.map (fun x => r⁻¹ • x)) (Metric.closedBall y s) = ν (Metric.closedBall (r • y) (r * s)) := by
    intro y s hs
    rw [Measure.map_apply hmeas Metric.isClosed_closedBall.measurableSet, Set.preimage_smul_inv₀ hr.ne',
      smul_closedBall _ _ hs, Real.norm_of_nonneg hr.le]
  have hvol : ∀ (y : EuclideanSpace ℝ (Fin d)) (s : ℝ), 0 ≤ s →
      volume (Metric.closedBall (r • y) (r * s)) =
        ENNReal.ofReal (r ^ d) * volume (Metric.closedBall y s) := by
    intro y s hs
    rw [Measure.addHaar_closedBall' _ _ (mul_nonneg hr.le hs), Measure.addHaar_closedBall' _ _ hs,
      finrank_euclideanSpace_fin, mul_pow, ENNReal.ofReal_mul (pow_nonneg hr.le _), mul_assoc]
  have hcv : ∀ A, ((r ^ d).toNNReal • volume : Measure (EuclideanSpace ℝ (Fin d))) A =
      ENNReal.ofReal (r ^ d) * volume A := fun A => by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]; rfl
  have hscale : Filter.Tendsto (fun s : ℝ => r * s) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_const_mul r).tendsto (0 : ℝ))
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hr hs
  set U : Set (EuclideanSpace ℝ (Fin d)) := {y | r * ‖y‖ < δ} with hU
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin d), ‖r • y‖ = r * ‖y‖ := fun y => by
    rw [norm_smul, Real.norm_of_nonneg hr.le]
  have hvan : ∀ y ∉ U, φ y = 0 := by
    intro y hy
    simp only [hU, Set.mem_setOf_eq, not_lt] at hy
    refine hR y ?_
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_lt_mul_of_pos_left hlt hr]
  have hnear : ∀ y ∈ U, ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (ν (Metric.closedBall (r • y) (r * s)) ≤
          ENNReal.ofReal κ * volume (Metric.closedBall (r • y) (r * s)) ∧
        volume (Metric.closedBall (r • y) (r * s)) ≤
          ENNReal.ofReal κ * ν (Metric.closedBall (r • y) (r * s))) ∧ 0 < s := by
    intro y hy
    have hy' : ‖r • y‖ < δ := by rw [hnorm]; exact hy
    filter_upwards [hscale.eventually (hball _ hy'), self_mem_nhdsWithin] with s hs hs0
    exact ⟨hs, hs0⟩
  have A1 := integral_le_of_small_balls (ν.map (fun x => r⁻¹ • x)) ((r ^ d).toNNReal • volume) κ
    (by linarith) U (fun y hy => (hnear y hy).mono fun s hs => by
      rw [hpre y s hs.2.le, hcv, ← hvol y s hs.2.le]; exact hs.1.1) φ hφ hc h0 hvan
  have A2 := integral_le_of_small_balls ((r ^ d).toNNReal • volume) (ν.map (fun x => r⁻¹ • x)) κ
    (by linarith) U (fun y hy => (hnear y hy).mono fun s hs => by
      rw [hpre y s hs.2.le, hcv, ← hvol y s hs.2.le]; exact hs.1.2) φ hφ hc h0 hvan
  have hvolint : ∫ x, φ x ∂((r ^ d).toNNReal • volume) = r ^ d * ∫ x, φ x := by
    rw [integral_smul_nnreal_measure, NNReal.smul_def, Real.coe_toNNReal _ hrd.le, smul_eq_mul]
  rw [hJ, hvolint] at A1 A2
  constructor
  · rw [inv_mul_le_iff₀ hrd]
    linarith
  · rw [show κ * ((r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) = (κ * ∫ x, φ (r⁻¹ • x) ∂ν) / r ^ d by
      field_simp, le_div_iff₀ hrd]
    linarith

theorem tendsto_of_nonneg {d : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ν]
    (h : ∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ →
      ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ν (Metric.closedBall x r) ≤ ENNReal.ofReal κ * volume (Metric.closedBall x r) ∧
        volume (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (h0 : ∀ x, 0 ≤ φ x) :
    Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, φ x)) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x : EuclideanSpace ℝ (Fin d), R ≤ ‖x‖ → φ x = 0 := by
    obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall 0
    refine ⟨R₀ + 1, fun x hx => ?_⟩
    by_contra hne
    have hx' := hR₀ (subset_tsupport φ (Function.mem_support.2 hne))
    rw [Metric.mem_closedBall, dist_zero_right] at hx'
    linarith
  have hL0 : 0 ≤ ∫ x, φ x := integral_nonneg h0
  have key : ∀ κ : ℝ, 1 < κ → ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν ≤ κ * ∫ x, φ x ∧
        ∫ x, φ x ≤ κ * ((r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) := by
    intro κ hκ
    obtain ⟨δ, hδ, hball⟩ := h κ hκ
    have hlin : Filter.Tendsto (fun r : ℝ => r * R) (nhds 0) (nhds 0) := by
      have := ((continuous_mul_const R).tendsto (0 : ℝ))
      rwa [zero_mul] at this
    filter_upwards [(hlin.mono_left nhdsWithin_le_nhds).eventually (eventually_lt_nhds hδ),
      self_mem_nhdsWithin] with r hrR hr
    exact rescaled_integral_comparable_of_nonneg_compactSupport ν κ δ hκ hball φ hφ hc h0 R r hR hr hrR
  rw [Metric.tendsto_nhds]
  intro ε hε
  set L := ∫ x, φ x with hLdef
  set η : ℝ := min 1 (ε / (2 * (L + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hη2 : η * (2 * (L + 1)) ≤ ε := (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  filter_upwards [key (1 + η) (by linarith)] with r hr
  obtain ⟨hu, hl⟩ := hr
  set I := (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν
  have h6 : 0 ≤ η * L := mul_nonneg hη.le hL0
  have h3 : η * I ≤ η * ((1 + η) * L) := mul_le_mul_of_nonneg_left hu hη.le
  have h4 : η * (η * L) ≤ 1 * (η * L) := mul_le_mul_of_nonneg_right hη1 h6
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

end GlobalTheory.VagueRescale

namespace GlobalTheory

theorem tendsto_rescaled_integral_of_density_one :
    ∀ (d : ℕ) (ν : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ν →
    (∀ κ : ℝ, 1 < κ → ∃ δ : ℝ, 0 < δ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < δ →
      ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ν (Metric.closedBall x r) ≤ ENNReal.ofReal κ * volume (Metric.closedBall x r) ∧
        volume (Metric.closedBall x r) ≤ ENNReal.ofReal κ * ν (Metric.closedBall x r)) →
    ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, Continuous φ → HasCompactSupport φ →
    Filter.Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ x, φ x)) := by
  intro d ν hν h φ hφ hc
  have hsplit : ∀ t : ℝ, max t 0 - max (-t) 0 = t := by
    intro t
    rcases le_total 0 t with ht | ht
    · rw [max_eq_left ht, max_eq_right (by linarith)]; ring
    · rw [max_eq_right ht, max_eq_left (by linarith)]; ring
  have hp : Continuous (fun x => max (φ x) 0) := hφ.max continuous_const
  have hm : Continuous (fun x => max (-φ x) 0) := hφ.neg.max continuous_const
  have hpc : HasCompactSupport (fun x => max (φ x) 0) :=
    hc.comp_left (g := fun t : ℝ => max t 0) (by simp)
  have hmc : HasCompactSupport (fun x => max (-φ x) 0) :=
    hc.comp_left (g := fun t : ℝ => max (-t) 0) (by simp)
  have Tp := VagueRescale.tendsto_of_nonneg ν h _ hp hpc (fun x => le_max_right _ _)
  have Tm := VagueRescale.tendsto_of_nonneg ν h _ hm hmc (fun x => le_max_right _ _)
  have hint : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, Continuous g → HasCompactSupport g →
      ∀ r : ℝ, Integrable (fun x => g (r⁻¹ • x)) ν := by
    intro g hg hgc r
    obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
    exact Integrable.of_bound (hg.comp (continuous_const_smul _)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => hC _)
  have heq : (fun r : ℝ => (r ^ d)⁻¹ * ∫ x, φ (r⁻¹ • x) ∂ν) = fun r =>
      (r ^ d)⁻¹ * ∫ x, max (φ (r⁻¹ • x)) 0 ∂ν - (r ^ d)⁻¹ * ∫ x, max (-φ (r⁻¹ • x)) 0 ∂ν := by
    funext r
    rw [← mul_sub, ← integral_sub (hint _ hp hpc r) (hint _ hm hmc r)]
    simp only [hsplit]
  have hvol : ∫ x, φ x = (∫ x, max (φ x) 0) - ∫ x, max (-φ x) 0 := by
    rw [← integral_sub (hp.integrable_of_hasCompactSupport hpc) (hm.integrable_of_hasCompactSupport hmc)]
    simp only [hsplit]
  rw [heq, hvol]
  exact Tp.sub Tm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoLeRootDiscriminantAndSplitArithmeticConditionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_le_rootDiscriminant_and_split_arithmetic_conditions : ∀ D : D7, 2 ≤ D.host.rdE ∧ ArithmeticConditionsOfDatum D := by
  first | exact @GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 | exact GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 | (intros; apply GlobalTheory.two_le_rdE_and_arithmeticConditionsS0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupUJHaarRightInvariantStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_subgroup_UJ_haar_right_invariant : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → (∀ g ∈ S, (Formalism.MainNotions.S.uMat g - 1) ^ m = 0) → ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → ∀ s ∈ S, μ.map (fun x => x * s) = μ := by
  first | exact @GlobalTheory.UJUnimod.unimodular_of_unipotent | exact GlobalTheory.UJUnimod.unimodular_of_unipotent | (intros; apply GlobalTheory.UJUnimod.unimodular_of_unipotent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFactsStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDatum_levelPrime_split_degree_gram_facts : ∀ (D : D7) (u : D.what₂.Word), SplitsIn D.host.E (D.mem u).A.T ∧ (∀ i, SplitsIn D.host.E (D.host.g i)) ∧ (∀ i, (D.mem u).A.T ≠ D.host.g i) ∧ Module.finrank ℚ D.host.E = 2 * D.R.f ∧ D.R.N 0 = D.R.k ∧ IsHerm (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ∧ (gramN D 0 (Nat.zero_le _)).det ≠ 0 := by
  first | exact @GlobalTheory.St.G.record_facts | exact GlobalTheory.St.G.record_facts | (intros; apply GlobalTheory.St.G.record_facts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarySubgroupChartSurjectiveNearOrigin
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open Filter Topology Metric

noncomputable section

namespace GlobalTheory.GaugeSubChartSurj

theorem exists_ball_subset {V M : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup M] [NormedSpace ℝ M] (ι : V →L[ℝ] M) (p : M →L[ℝ] V)
    (hp : ∀ x, p (ι x) = x) {f : M → M} (hf : HasStrictFDerivAt f (ContinuousLinearMap.id ℝ M) 0)
    (h0 : f 0 = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : V, ‖x‖ < ρ → ∃ y : V, ‖f (ι y)‖ < δ ∧ p (f (ι y)) = x := by
  have hf' : HasStrictFDerivAt f (ContinuousLinearMap.id ℝ M) (ι 0) := by rwa [map_zero]
  have h1 := hf'.comp (0 : V) ι.hasStrictFDerivAt
  have h2 := p.hasStrictFDerivAt.comp (0 : V) h1
  have h3 : p.comp ((ContinuousLinearMap.id ℝ M).comp ι) =
      (ContinuousLinearEquiv.refl ℝ V : V →L[ℝ] V) := by
    ext1 x; exact hp x
  rw [h3] at h2
  have h4 := h2.map_nhds_eq_of_equiv
  simp only [map_zero, h0] at h4
  have h5 : Tendsto (fun y => f (ι y)) (𝓝 0) (𝓝 0) := by
    have := h1.continuousAt.tendsto
    simpa only [map_zero, h0] using this
  have h6 : (fun y => f (ι y)) ⁻¹' ball 0 δ ∈ 𝓝 (0 : V) := h5 (ball_mem_nhds 0 hδ)
  have h7 := image_mem_map (m := fun y => p (f (ι y))) h6
  rw [h4] at h7
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.1 h7
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hsub (mem_ball_zero_iff.2 hx)
  exact ⟨y, mem_ball_zero_iff.1 hy, hyx⟩

variable {n d : ℕ}

def comb (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun x := ∑ i, x i • E i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

def coord (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun X := WithLp.toLp 2 (fun i => ((X * (E i)ᴴ).trace).re)
  map_add' X Y := by ext i; simp [Matrix.add_mul]
  map_smul' c X := by ext i; simp

theorem coord_comb (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (x : EuclideanSpace ℝ (Fin d)) :
    coord E (comb E x) = x := by
  ext k
  change (((∑ i, x i • E i) * (E k)ᴴ).trace).re = x k
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum,
    Complex.smul_re, hE]
  simp

open scoped Matrix.Norms.Frobenius in

theorem chart_surj : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A) → (∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E)) → ∀ δ : ℝ, 0 < δ → ∃ ρ : ℝ, 0 < ρ ∧ ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ < ρ → ∃ g : Formalism.REAL.UJ ε, uMat g - 1 ∈ A ∧ Real.sqrt (Formalism.REAL.hs (uMat g - 1)) < δ ∧ (WithLp.toLp 2 (fun i => (((uMat g - 1) * (E i)ᴴ).trace).re) : EuclideanSpace ℝ (Fin d)) = x := by
  intro n ε A d E hA hE hs δ hδ
  obtain ⟨ρ, hρ, h⟩ := exists_ball_subset (LinearMap.toContinuousLinearMap (comb E))
    (LinearMap.toContinuousLinearMap (coord E)) (coord_comb E hE)
    (f := fun Y => NormedSpace.exp Y - 1)
    (HasStrictFDerivAt.sub_const (f := NormedSpace.exp) 1 CompactDualExists.exp_strict)
    (sub_eq_zero.2 (NormedSpace.exp_zero (𝔸 := Matrix (Fin n) (Fin n) ℂ))) hδ
  refine ⟨ρ, hρ, fun x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := h x hx
  have hm : comb E y ∈ A ∧ Formalism.REAL.inG ε (comb E y) :=
    (hs (∑ i, y i • E i)).2 (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
  refine ⟨GaugeConst.expJ ε ⟨comb E y, hm.2⟩, GaugeSubExists.exp_sub_one_mem A hA hm.1, ?_, hyx⟩
  rw [GaugeConst.sqrt_hs]
  exact hy

end GlobalTheory.GaugeSubChartSurj
end
end

