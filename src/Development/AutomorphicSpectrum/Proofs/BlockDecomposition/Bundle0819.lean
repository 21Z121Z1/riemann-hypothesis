import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0812
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0800
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.TChartSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativity
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SphericalSplitting.SphericalEisensteinGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySiegelDomainExists
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreIntegralEq
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

open Set

theorem setLIntegral_eq_of_vanish {V : Type} [MeasurableSpace V] (μ : Measure V) {O : Set V}
    (hO : MeasurableSet O) (f : V → ℝ≥0∞) (hf : ∀ v, v ∉ O → f v = 0) :
    ∫⁻ v in O, f v ∂μ = ∫⁻ v, f v ∂μ := by
  rw [← lintegral_indicator hO]
  refine lintegral_congr fun v => ?_
  by_cases hv : v ∈ O
  · rw [indicator_of_mem hv]
  · rw [indicator_of_notMem hv, hf v hv]

theorem lintegral_chart_of_continuous {V Vx Va VY : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    [MeasurableSpace Vx] [MeasurableSpace Va] [MeasurableSpace VY]
    (c : Vx → Va → VY → V) (hc : Measurable fun p : Vx × VY × Va => c p.1 p.2.2 p.2.1)
    (μ : Measure V) (μx : Measure Vx) (μY : Measure VY) (μa : Measure Va)
    [SFinite μx] [SFinite μY] [SFinite μa]
    (O cell : Set V) (Ox : Set Vx) (hO : MeasurableSet O) (hOx : MeasurableSet Ox)
    (hcell : IsOpen cell) (hcO : cell ⊆ O)
    (h1 : ∀ᵐ v ∂μ, v ∈ O → v ∈ cell)
    (h2 : ∀ᵐ y ∂μY, ∀ x ∈ Ox, ∀ a, c x a y ∈ cell)
    (h3 : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ cell → (∀ v, 0 ≤ φ v) →
      Integrable φ μ ∧ ∫⁻ v, ENNReal.ofReal (φ v) ∂μ =
        ∫⁻ x, ∫⁻ a, ∫⁻ y, ENNReal.ofReal (φ (c x a y)) ∂μY ∂μa ∂μx)
    (h4 : ∀ x a y, x ∉ Ox → c x a y ∉ O)
    (g : V → ℝ≥0∞) (hg : Measurable g) (hgO : ∀ v, v ∉ O → g v = 0) :
    ∫⁻ v, g v ∂μ = ∫⁻ x, ∫⁻ y, ∫⁻ a, g (c x a y) ∂μa ∂μY ∂μx := by
  let f : Vx × VY × Va → V := fun p => c p.1 p.2.2 p.2.1
  let ρ : Measure (Vx × VY × Va) := (μx.restrict Ox).prod (μY.prod μa)
  have hf : Measurable f := hc
  have key : ∀ G : V → ℝ≥0∞, Measurable G → (∀ v, v ∉ O → G v = 0) →
      ∫⁻ v, G v ∂(ρ.map f) = ∫⁻ x, ∫⁻ y, ∫⁻ a, G (c x a y) ∂μa ∂μY ∂μx := by
    intro G hG hG0
    have e : ∀ x, ∫⁻ q, G (f (x, q)) ∂(μY.prod μa) = ∫⁻ y, ∫⁻ a, G (c x a y) ∂μa ∂μY := fun x =>
      lintegral_prod (fun q => G (f (x, q))) ((hG.comp hf).comp measurable_prodMk_left).aemeasurable
    rw [lintegral_map hG hf]
    show ∫⁻ p, G (f p) ∂((μx.restrict Ox).prod (μY.prod μa)) = _
    rw [lintegral_prod (fun p => G (f p)) (hG.comp hf).aemeasurable]
    simp only [e]
    refine setLIntegral_eq_of_vanish μx hOx _ fun x hx => ?_
    have h0 : ∀ y a, G (c x a y) = 0 := fun y a => hG0 _ (h4 x a y hx)
    simp [h0]
  have hmeq : μ.restrict O = ρ.map f := by
    refine GlobalTheory.CompanionTheory.SW.FibreUniq.measure_eq_of_lintegral_eq _ _ cell hcell ?_ ?_ ?_
    · have h : ∀ᵐ v ∂(μ.restrict O), v ∈ cell := (ae_restrict_iff' hO).2 h1
      exact h
    · rw [Measure.map_apply hf hcell.measurableSet.compl]
      have a1 : ∀ᵐ p ∂ρ, p.1 ∈ Ox :=
        Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hOx)
      have a2 : ∀ᵐ q ∂(μY.prod μa), ∀ x ∈ Ox, ∀ a, c x a q.1 ∈ cell :=
        Measure.quasiMeasurePreserving_fst.ae h2
      have a3 : ∀ᵐ p ∂ρ, ∀ x ∈ Ox, ∀ a, c x a p.2.1 ∈ cell :=
        Measure.quasiMeasurePreserving_snd.ae a2
      have h : ∀ᵐ p ∂ρ, f p ∈ cell := by
        filter_upwards [a1, a3] with p h h' using h' _ h _
      exact h
    · intro φ hφ hs hsup h0
      obtain ⟨hi, hl⟩ := h3 φ hφ hs hsup h0
      have hm : Measurable fun v => ENNReal.ofReal (φ v) :=
        ENNReal.measurable_ofReal.comp hφ.measurable
      have hv : ∀ v, v ∉ O → ENNReal.ofReal (φ v) = 0 := fun v hv => by
        rw [image_eq_zero_of_notMem_tsupport fun h => hv (hcO (hsup h)), ENNReal.ofReal_zero]
      refine ⟨hi.restrict, ?_⟩
      rw [key _ hm hv, setLIntegral_eq_of_vanish μ hO _ hv, hl]
      refine lintegral_congr fun x => ?_
      have hH : Measurable fun q : VY × Va => ENNReal.ofReal (φ (c x q.2 q.1)) :=
        (hm.comp hf).comp measurable_prodMk_left
      exact (lintegral_lintegral_swap hH.aemeasurable).symm
  rw [← key g hg hgO, ← hmeq, setLIntegral_eq_of_vanish μ hO g hgO]

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt

open Set

theorem stages_zero_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (hypOne J) (n + 1) (coordW R b lam (n + 1) (M + 2)) (coordHerm R σ b lam (n + 1)) m → IsGramFibFree R σ (hypOne J) 1 (coordW R b lam 1 (M + 2)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable g → (∀ X, ¬ IsUnit (X 0 0) → g X = 0) → ∫⁻ X, g X ∂(m 0) = ∫⁻ x, ∫⁻ Y, ∫⁻ a, g (chartS R σ J x a 0 Y) ∂(coordW R b lam 1 n) ∂(m' 0) ∂(m₁ 0) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n d b lam hlam m m₁ m' hm hm₁ hm' g hg hg0
  obtain ⟨hOpen, hLI, hGr, hCh, hmeas⟩ := GlobalTheory.T.free_cell_open_independent F E σ hCM M J hJ R hR n
  have hOpen0 := (GlobalTheory.T.free_cell_open_independent F E σ hCM M J hJ R hR 0).1
  have hR' := hR
  obtain ⟨r1, r2, r3, r4, -⟩ := hR'
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 (n + 1) (M + 2)
  haveI := t8 1 (M + 2)
  haveI := t8 1 n
  haveI := t8 n M
  haveI : SigmaFinite (m₁ 0) :=
    GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.sigmaFinite_free σ hCM (hypOne J) R hR 1 _ _ m₁ hm₁ 0
  haveI : SigmaFinite (m' 0) :=
    GlobalTheory.CompanionTheory.WeilSiegel.FreeLocal.sigmaFinite_free σ hCM J R hR n _ _ m' hm' 0
  haveI : (coordW R b lam 1 n).IsAddHaarMeasure :=
    (GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam).2.1 1 n
  have hOx : MeasurableSet {x : Fin 1 → Fin (M + 2) → R ⊗[F] E | IsUnit (x 0 0)} := by
    have e : {x : Fin 1 → Fin (M + 2) → R ⊗[F] E | IsUnit (x 0 0)} =
        freeCell (R ⊗[F] E) M 0 := by
      ext x
      exact ⟨fun h => ⟨h, linearIndependent_empty_type⟩, fun h => h.1⟩
    rw [e]
    exact hOpen0.measurableSet
  have hO : MeasurableSet {X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E | IsUnit (X 0 0)} := by
    have hp : Measurable fun (X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) (_ : Fin 1) => X 0 :=
      measurable_pi_lambda _ fun _ => measurable_pi_apply 0
    exact hp hOx
  have hc : Measurable fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) ×
      (Fin 1 → Fin n → R ⊗[F] E) => chartS R σ J p.1 p.2.2 0 p.2.1 :=
    hmeas.comp (measurable_fst.prodMk ((measurable_snd.comp measurable_snd).prodMk
      (measurable_const.prodMk (measurable_fst.comp measurable_snd))))
  have c0 : ∀ᵐ X ∂(m 0), X ∈ (gramR R σ (hypOne J)) ⁻¹' {((0 : HermR R σ (n + 1)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ {X | LinearIndependent (R ⊗[F] E) X} :=
    hm.1 0
  have c1 : ∀ᵐ Y ∂(m' 0), Y ∈ (gramR R σ J) ⁻¹' {((0 : HermR R σ n) :
      Matrix (Fin n) (Fin n) (R ⊗[F] E))} ∩ {X | LinearIndependent (R ⊗[F] E) X} :=
    hm'.1 0
  refine lintegral_chart_of_continuous (fun x a Y => chartS R σ J x a 0 Y) hc (m 0) (m₁ 0) (m' 0)
    (coordW R b lam 1 n) {X | IsUnit (X 0 0)} (freeCell (R ⊗[F] E) M n)
    {x | IsUnit (x 0 0)} hO hOx hOpen (fun X hX => hX.1) ?_ ?_ ?_ ?_ g hg hg0
  · filter_upwards [c0] with X hX hu
    exact hGr X hX.2 hX.1 hu
  · filter_upwards [c1] with Y hY x hx a
    exact hCh x a 0 Y hx hY.2
  · intro φ hφ hs hsup h0
    exact ⟨(hm.2.2 φ hφ hs (hsup.trans fun X hX => hLI X hX)).1 0 (mem_univ _),
      GlobalTheory.T.hyperbolic_fibre_free_extension F E σ hCM M J hJ R hR n d b lam hlam m m₁ m' hm hm₁ hm' φ hφ hs hsup h0⟩
  · intro x a Y hx h
    exact hx (by simpa [chartS] using h)

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage.StageExt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarSectionExists
section
noncomputable section

namespace GlobalTheory.CompanionTheory.ScalWall

open PositivityTheory.RgEis ResidueKilled.Tr GlobalTheory.CompanionTheory.SiegelFrame

theorem pos_eq_norm_cosetSum {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (Γ P : Subgroup G) (Γ' P' : Subgroup G')
    (hΓ : ∀ g, g ∈ Γ ↔ Φ g ∈ Γ') (hP : ∀ g, g ∈ P ↔ Φ g ∈ P') (l : G' → ℝ) (hc : Conv Γ' P' l)
    (hl : ∀ γ ∈ Γ', γ ∈ P' → ∀ y, l (γ * y) = l y) (g : G) :
    pos Γ' P' l (Φ g) = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => (Real.exp (l (Φ x)) : ℂ)) g‖ := by
  have hs : HasSum (fun q : PositivityTheory.RgEis.Cos P' Γ' => Real.exp (l (PositivityTheory.RgEis.rep q * Φ g)))
      (PositivityTheory.RgEis.pos Γ' P' l (Φ g)) := (hc (Φ g)).hasSum
  have h2 := GlobalTheory.CompanionTheory.SiegelFrame.hasSum_cos Φ Γ P Γ' P' hΓ hP (fun y => Real.exp (l y))
    (fun γ hγ hγP y => by simp only [hl γ hγ hγP y]) (Φ g) _ hs
  have h3 : HasSum (fun q : PositivityTheory.RgEis.Cos P Γ => ((Real.exp (l (Φ (PositivityTheory.RgEis.rep q * g))) : ℝ) : ℂ))
      ((PositivityTheory.RgEis.pos Γ' P' l (Φ g) : ℝ) : ℂ) :=
    Complex.hasSum_ofReal.mpr (by simpa only [map_mul] using h2)
  have h4 : GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp (l (Φ x)) : ℝ) : ℂ)) g
      = ((PositivityTheory.RgEis.pos Γ' P' l (Φ g) : ℝ) : ℂ) := h3.tsum_eq
  rw [h4, Complex.norm_real, Real.norm_of_nonneg (hs.nonneg fun _ => (Real.exp_pos _).le)]

theorem fin_along {G G' : Type} [Group G] [Group G'] (Φ : G ≃* G') (K' : Subgroup G') (f : G → ℂ)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun x => f (x * Φ.symm k)))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : G'))))) := by
  have e : (Set.range fun k : K' => fun y => f (Φ.symm (y * (k : G'))))
      = (LinearMap.funLeft ℂ ℂ (⇑Φ.symm)) '' (Set.range fun k : K' => fun x => f (x * Φ.symm k)) := by
    rw [← Set.range_comp]
    congr 1
    funext k y
    simp [LinearMap.funLeft_apply, map_mul]
  rw [e, ← Submodule.map_span]
  exact Module.Finite.map _ _

theorem tScal : TScal := by
  unfold ResidueKilled.Tr.TScal ResidueKilled.Tr.Scal
  intro hSec hWL G G' _ _ _ _ _ _ _ _ Φ Γ P Γ' K' P' c η N hK hPar hHt hΓ hP hW f hf hlaw hfin
  have hcrat : ∀ γ ∈ Γ', γ ∈ P' → c γ = 1 := by
    obtain ⟨_, _, ⟨_, _, h, _⟩⟩ := hPar
    exact h
  have hηl : ∀ p ∈ P', ∀ g, η (p * g) = η p + η g := by
    obtain ⟨h, _, _, _⟩ := hHt
    exact h
  have hηr : ∀ γ ∈ Γ', γ ∈ P' → η γ = 0 := by
    obtain ⟨_, _, h, _⟩ := hHt
    exact h
  have hβ : PositivityTheory.RgEis.IsHt Γ' K' P' (fun g => N * η g) := by
    obtain ⟨h1, h2, h3, h4⟩ := hHt
    exact ⟨fun p hp g => by simp only [h1 p hp g, mul_add], fun g k hk => by simp only [h2 g k hk],
      fun γ hγ hγP => by simp only [h3 γ hγ hγP, mul_zero], continuous_const.mul h4⟩
  have hlaw' : ∀ p ∈ P', ∀ x : G', (fun y => f (Φ.symm y)) (p * x)
      = c p * Complex.exp (0 * ↑(η p)) * (fun y => f (Φ.symm y)) x := by
    intro p hp x
    have hp' : Φ.symm p ∈ P := (hP (Φ.symm p)).mpr (by simpa using hp)
    simp only [map_mul, zero_mul, Complex.exp_zero, mul_one]
    rw [hlaw _ hp']
    simp
  have hfin' := fin_along Φ.toMulEquiv K' f hfin
  obtain ⟨R, D, H, hD, hDz, hHd, hHc, hconv1, hconv2, hbd, hsum⟩ :=
    GlobalTheory.CompanionTheory.SiegelFrame.scalar_wall hSec hWL Γ' K' P' c η (fun g => N * η g) hK hPar hHt hβ hW
      (fun y => f (Φ.symm y)) 0 (hf.comp (map_continuous Φ.symm)) hlaw' hfin'
  refine ⟨D, fun z g => H z (Φ g), R, hD, hDz, fun g => hHd (Φ g), ?_, ?_, ?_⟩
  · exact hHc.comp (continuous_fst.prodMk ((map_continuous Φ).comp continuous_snd))
  · intro z hz g
    show H z (Φ g) = _
    have h2 := GlobalTheory.CompanionTheory.SiegelFrame.hasSum_cos Φ.toMulEquiv Γ P Γ' P' hΓ hP
      (fun y => D z * (Complex.exp ((z - 0) * ↑(η y)) * f (Φ.symm y)))
      (fun γ hγ hγP y => by
        have hγ' : Φ.symm γ ∈ P := (hP (Φ.symm γ)).mpr (by simpa using hγP)
        simp only [hηl γ hγP y, hηr γ hγ hγP, zero_add, map_mul]
        rw [hlaw _ hγ']
        simp [hcrat γ hγ hγP])
      (Φ g) _ (hsum z hz (Φ g))
    have h3 : HasSum (fun q : PositivityTheory.RgEis.Cos P Γ =>
        D z * (Complex.exp (z * ↑(η (Φ (PositivityTheory.RgEis.rep q * g)))) * f (PositivityTheory.RgEis.rep q * g))) (H z (Φ g)) := by
      have e : (fun q : PositivityTheory.RgEis.Cos P Γ =>
          D z * (Complex.exp (z * ↑(η (Φ (PositivityTheory.RgEis.rep q * g)))) * f (PositivityTheory.RgEis.rep q * g)))
          = fun q => (fun y => D z * (Complex.exp ((z - 0) * ↑(η y)) * f (Φ.symm y)))
              (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g) := by
        funext q
        have hm : Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g = Φ (PositivityTheory.RgEis.rep q * g) :=
          (map_mul Φ _ _).symm
        show _ = D z * (Complex.exp ((z - 0) * ↑(η (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g)))
          * f (Φ.symm (Φ.toMulEquiv (PositivityTheory.RgEis.rep q) * Φ g)))
        rw [hm, sub_zero, ContinuousMulEquiv.symm_apply_apply]
      rw [e]
      exact h2
    rw [← h3.tsum_eq, tsum_mul_left]
    rfl
  · intro a b ha hb
    obtain ⟨M, hM⟩ := hbd a b ha hb
    refine ⟨M, fun z hz1 hz2 g => ?_⟩
    have hl2 : (fun x : G' => N * η x - b * η x) = fun x => (N - b) * η x := by
      funext x
      ring
    have hinv : ∀ (t : ℝ), ∀ γ ∈ Γ', γ ∈ P' → ∀ y, t * η (γ * y) = t * η y := by
      intro t γ hγ hγP y
      rw [hηl γ hγP y, hηr γ hγ hγP, zero_add]
    have e1 : PositivityTheory.RgEis.pos Γ' P' (fun x => a * η x) (Φ g)
        = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp (a * η (Φ x)) : ℝ) : ℂ)) g‖ :=
      pos_eq_norm_cosetSum Φ.toMulEquiv Γ P Γ' P' hΓ hP (fun x => a * η x) (hconv1 a ha)
      (fun γ hγ hγP y => hinv a γ hγ hγP y) g
    have hc2 : PositivityTheory.RgEis.Conv Γ' P' (fun x => (N - b) * η x) := by
      rw [← hl2]
      exact hconv2 b hb
    have e2 : PositivityTheory.RgEis.pos Γ' P' (fun x => (N - b) * η x) (Φ g)
        = ‖GlobalTheory.Eis.cosetSum P Γ (fun x => ((Real.exp ((N - b) * η (Φ x)) : ℝ) : ℂ)) g‖ :=
      pos_eq_norm_cosetSum Φ.toMulEquiv Γ P Γ' P' hΓ hP (fun x => (N - b) * η x) hc2
      (fun γ hγ hγP y => hinv (N - b) γ hγ hγP y) g
    have key := hM z hz1 hz2 (Φ g)
    have e3 : PositivityTheory.RgEis.pos Γ' P' (fun x => N * η x - b * η x) (Φ g)
        = PositivityTheory.RgEis.pos Γ' P' (fun x => (N - b) * η x) (Φ g) := by
      rw [hl2]
    calc ‖H z (Φ g)‖ ≤ M * (PositivityTheory.RgEis.pos Γ' P' (fun x => a * η x) (Φ g)
          + PositivityTheory.RgEis.pos Γ' P' (fun x => N * η x - b * η x) (Φ g)) := key
      _ = _ := by
        rw [e3, e1, e2]
        try rfl

end GlobalTheory.CompanionTheory.ScalWall

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerImageNoDualComponent
section
noncomputable section

open scoped NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.RegSW PositivityTheory.RegularEisensteinLemmas
open GlobalTheory.Core.Rk.SWLaw (zeroSp)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

variable {D : D7} {T T₀ T' : HSp D} {r : ℕ}

theorem mul_eq_one_of_gram {R : Type} [CommRing R] {c x G Gi : R} (hg : G * Gi = 1) (h : c * (G * x) = G) : c * x = 1 := by
  linear_combination Gi * h + (1 - c * x) * hg

theorem nnreal_eq_one_of_sq {x : ℝ≥0} (h : x * x = 1) : x = 1 := by
  rw [← sq] at h
  exact (pow_eq_one_iff_of_nonneg zero_le (n := 2) (by norm_num)).1 h

theorem absA_eq_one_of_conj (u : (AE D)ˣ) (h : conjUnit D.sp.cm.sig u * u = 1) : absA D u = 1 := by
  have h3 := congrArg (absE D.host.F D.host.E) h
  rw [map_mul, absE_conjUnit, map_one] at h3
  exact nnreal_eq_one_of_sq h3

theorem absA_det_matHom (g : GA D T₀) : absA D (Matrix.GeneralLinearGroup.det (matHom T₀ g)) = 1 := by
  have hg : (gA T₀).det * (giA T₀).det = 1 := by rw [← Matrix.det_mul, gA_mul_giA, Matrix.det_one]
  have h := congrArg Matrix.det (mt_unitary T₀ g)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hadj : (adj (mt T₀ g)).det = cA D (mt T₀ g).det := by
    rw [adj, Matrix.det_transpose, RingHom.map_det]; rfl
  rw [hadj] at h
  have h2 : conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det (matHom T₀ g)) *
      Matrix.GeneralLinearGroup.det (matHom T₀ g) = 1 := Units.ext (mul_eq_one_of_gram hg h)
  exact absA_eq_one_of_conj _ h2

theorem stabilizer_image_no_dual_component (d : HypDec T T₀ r) (p : stab d) : d.pY ⬝ (mt T p ⬝ d.j0) = 0 := by
  have h := mul_jX d p
  have h1 : adj (onX d p).1 ⬝ (d.pY ⬝ (mt T p ⬝ d.j0)) = 0 := by
    have e : adj (onX d p).1 ⬝ (d.pY ⬝ (mt T p ⬝ d.j0)) = adj (d.jX ⬝ (onX d p).1) ⬝ (gA T ⬝ (mt T p ⬝ d.j0)) := by
      rw [d.pY_eq, adj_mul]; simp only [Matrix.mul_assoc]
    rw [e, ← h, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA T), ← Matrix.mul_assoc (adj (mt T p)), mt_unitary T p]
    exact d.wittDecomp_gram_X_anisotropic
  have h2 : adj ((onX d p)⁻¹).1 ⬝ adj (onX d p).1 = 1 := by
    rw [← adj_mul, Units.mul_inv, adj_one]
  rw [← Matrix.one_mul (d.pY ⬝ (mt T p ⬝ d.j0)), ← h2, Matrix.mul_assoc, h1, Matrix.mul_zero]

theorem stabilizer_image_hyperbolic (d : HypDec T T₀ r) (p : stab d) :
    mt T p ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt T p ⬝ d.j0)) + d.j0 ⬝ (d.p0 ⬝ (mt T p ⬝ d.j0)) := by
  have h : (d.jX ⬝ d.pX + d.j0 ⬝ d.p0 + d.jY ⬝ d.pY) ⬝ (mt T p ⬝ d.j0) = mt T p ⬝ d.j0 := by
    rw [d.sum_eq_one, Matrix.one_mul]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_assoc d.jX, Matrix.mul_assoc d.j0, Matrix.mul_assoc d.jY, stabilizer_image_no_dual_component,
    Matrix.mul_zero, add_zero] at h
  exact h.symm

theorem rat_lag {n a b : ℕ} (M : Matrix (Fin n) (Fin a) D.host.E) (N : Matrix (Fin n) (Fin b) D.host.E) :
    rat ((Matrix.fromCols M N).submatrix id finSumFinEquiv.symm) =
      (Matrix.fromCols (rat M) (rat N)).submatrix id finSumFinEquiv.symm := by
  funext i j
  change incA D (Matrix.fromCols M N i (finSumFinEquiv.symm j)) = Matrix.fromCols (rat M) (rat N) i (finSumFinEquiv.symm j)
  generalize finSumFinEquiv.symm j = s
  cases s <;> rfl

section Blocks

variable {R : Type} [CommRing R] {n a b : ℕ}

theorem fromCols_mul_fromBlocks (P : Matrix (Fin n) (Fin a) R) (Q : Matrix (Fin n) (Fin b) R)
    (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin a) (Fin b) R) (z : Matrix (Fin b) (Fin b) R) :
    Matrix.fromCols P Q * Matrix.fromBlocks x y 0 z = Matrix.fromCols (P * x) (P * y + Q * z) := by
  ext i (j | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem exists_gl_block (x : Matrix.GeneralLinearGroup (Fin a) R) (z : Matrix.GeneralLinearGroup (Fin b) R)
    (y : Matrix (Fin a) (Fin b) R) : ∃ B : Matrix.GeneralLinearGroup (Fin (a + b)) R,
      B.1 = (Matrix.fromBlocks x.1 y 0 z.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm ∧
      Matrix.GeneralLinearGroup.det B = Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det z := by
  have hdet : ((Matrix.fromBlocks x.1 y 0 z.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm :
      Matrix (Fin (a + b)) (Fin (a + b)) R).det = x.1.det * z.1.det := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  have hu : IsUnit ((Matrix.fromBlocks x.1 y 0 z.1).submatrix finSumFinEquiv.symm finSumFinEquiv.symm :
      Matrix (Fin (a + b)) (Fin (a + b)) R).det := by
    rw [hdet]
    exact (Matrix.GeneralLinearGroup.det x * Matrix.GeneralLinearGroup.det z).isUnit
  exact ⟨Matrix.GeneralLinearGroup.mk'' _ hu, rfl, Units.ext hdet⟩

theorem mul_cols_block (X : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin n) (Fin a) R) (Q : Matrix (Fin n) (Fin b) R)
    (x : Matrix (Fin a) (Fin a) R) (y : Matrix (Fin a) (Fin b) R) (z : Matrix (Fin b) (Fin b) R)
    (c1 : X * P = P * x) (c2 : X * Q = P * y + Q * z) :
    X * (Matrix.fromCols P Q).submatrix id finSumFinEquiv.symm = (Matrix.fromCols P Q).submatrix id finSumFinEquiv.symm *
      (Matrix.fromBlocks x y 0 z).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [← Matrix.submatrix_mul _ _ _ _ _ finSumFinEquiv.symm.bijective, fromCols_mul_fromBlocks, ← c1, ← c2,
    ← Matrix.mul_fromCols]
  rfl

theorem mul_sum_eq {t : ℕ} {X : Matrix (Fin n) (Fin n) R} {P : Matrix (Fin n) (Fin t) R} {g : Matrix (Fin t) (Fin t) R}
    {Q : Matrix (Fin n) (Fin b) R} {J : Matrix (Fin t) (Fin a) R} {J₀ : Matrix (Fin t) (Fin b) R}
    {y : Matrix (Fin a) (Fin b) R} {z : Matrix (Fin b) (Fin b) R} (e1 : X * P = P * g) (e2 : X * Q = Q * z)
    (h0 : g * J₀ = J * y + J₀ * z) : X * (P * J₀ + Q) = P * J * y + (P * J₀ + Q) * z := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, e1, Matrix.mul_assoc, h0, e2, Matrix.mul_add, Matrix.add_mul,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, add_assoc]

end Blocks

theorem exists_block (d : HypDec T T₀ r) {jT : Matrix (Fin T'.rank) (Fin T.rank) D.host.E}
    {j₀ : Matrix (Fin T'.rank) (Fin T₀.rank) D.host.E} {d' : HypDec T' (zeroSp D) (r + T₀.rank)}
    {ι : GA D T × GA D T₀ →* GA D T'} {m : stab d →* GA D T₀} (hE : IsEmb jT j₀ ι) (hL : IsLag d jT j₀ d')
    (hM : IsLevi0 d m) (p : stab d) : ∃ B : Matrix.GeneralLinearGroup (Fin (r + T₀.rank)) (AE D),
      mt T' (ι ((p : GA D T), m p)) ⬝ d'.jX = d'.jX ⬝ B.1 ∧
      Matrix.GeneralLinearGroup.det B =
        Matrix.GeneralLinearGroup.det (onX d p) * Matrix.GeneralLinearGroup.det (matHom T₀ (m p)) := by
  obtain ⟨B, hB, hdet⟩ := exists_gl_block (onX d p) (matHom T₀ (m p)) (d.pX ⬝ (mt T p ⬝ d.j0))
  refine ⟨B, ?_, hdet⟩
  have hJ : d'.jX = (Matrix.fromCols (rat jT ⬝ d.jX) (rat jT ⬝ d.j0 + rat j₀)).submatrix id finSumFinEquiv.symm := by
    rw [HypDec.jX, hL, rat_lag, rat_mul, rat_add, rat_mul]; rfl
  have h0 : mt T p ⬝ d.j0 = d.jX ⬝ (d.pX ⬝ (mt T p ⬝ d.j0)) + d.j0 ⬝ mt T₀ (m p) := by
    rw [hM p]; exact stabilizer_image_hyperbolic d p
  obtain ⟨e1, e2⟩ := hE (p : GA D T) (m p)
  rw [hB, hJ]
  refine mul_cols_block _ _ _ _ _ _ ?_ ?_
  · rw [cancel₂ e1, Matrix.mul_assoc, mul_jX d p, Matrix.mul_assoc]
  · exact mul_sum_eq e1 e2 h0

theorem law : Law := by
  intro D T T₀ T' r d jT j₀ d' ι m _ hE hL hM p
  obtain ⟨B, key, hdet⟩ := exists_block d hE hL hM p
  have hmem : ι ((p : GA D T), m p) ∈ stab d' := ⟨B, key⟩
  refine ⟨hmem, ?_⟩
  have hon : onX d' ⟨_, hmem⟩ = B :=
    Units.ext ((eq_of_mul_jX d' (mul_jX d' _)).trans (eq_of_mul_jX d' key).symm)
  change absA D (Matrix.GeneralLinearGroup.det (onX d' ⟨_, hmem⟩)) = absA D (Matrix.GeneralLinearGroup.det (onX d p))
  rw [hon, hdet, map_mul, absA_det_matHom, mul_one]

end GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLocallySummableBoundStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_integral_locally_summable_bound : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ), 2 * r < V.rank → IsCharAF D.host.F ψ → IsInfFam θ → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → φ ∈ schwartzA θ V.rank r → ∀ K : Set (hermA D r), IsCompact K → ∃ u : ratHerm D r → ℝ, Summable u ∧ ∀ c : ratHerm D r, ∀ b ∈ K, ‖Jt ψ V μ φ (b + c.1)‖ ≤ u c := by
  first | exact @GlobalTheory.CompanionTheory.JtUnif.jt_unif | exact GlobalTheory.CompanionTheory.JtUnif.jt_unif | (intros; apply GlobalTheory.CompanionTheory.JtUnif.jt_unif <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySiegelDomainExistsStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_siegel_domain_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ K : Subgroup (GAd σ J), IsCompact (K : Set (GAd σ J)) → (∀ g, ∃ p ∈ minPar σ J X, ∃ k ∈ K, g = p * k) → GoodPosition σ J X Y K → ∃ (Ω : Set (GAd σ J)) (c : ℝ), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ 0 < c ∧ ∀ g, ∃ γ ∈ ratPts σ J, ∃ s ∈ siegelSet σ J X Y Ω c K, g = γ * s := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.cov_main | exact GlobalTheory.CompanionTheory.RedCov.cov_main | (intros; apply GlobalTheory.CompanionTheory.RedCov.cov_main <;> assumption)
end

