import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmStar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0244
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0245
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoModerateGrowthSizeTranslateNearOne
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.Size.NearOne

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem exists_log (V : HSp D) (τ : D.what₂.Tau) :
    ∃ Λ : Matrix (Fin V.rank) (Fin V.rank) ℂ → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ u, Λ u ∈ lieAt V τ) ∧
      Tendsto Λ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ u in 𝓝[Formalism.QuantumDeterminants.UH (gramAt D V τ)] 1, NormedSpace.exp (Λ u) = u := by
  obtain ⟨L, hL, hexp, hlog⟩ := GlobalTheory.ConjMult.hasLogAt (V := V) τ
  have hJ := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have h0 : L 1 = 0 := by
    have h := hlog.self_of_nhds
    simpa using h
  refine ⟨fun u => (L u).1, fun u => (L u).2, ?_, ?_⟩
  · have hc : Filter.Tendsto L (𝓝 1) (𝓝 0) := h0 ▸ hL.continuousAt.tendsto
    exact (continuous_subtype_val.tendsto _).comp hc
  · filter_upwards [nhdsWithin_le_nhds hexp, self_mem_nhdsWithin] with u hu hmem
    exact hu ((GlobalTheory.ConjMult.unit_iffM hJ u).2 hmem)

private theorem continuous_matrix_exp' (n : ℕ) : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp M) := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := .restrictScalars ℚ ℂ _
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact NormedSpace.exp_continuous

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem exists_height_le (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    ∀ᶠ X in 𝓝 (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, height V (oneP θ V τ X t) ≤ 2 := by
  have hl := height_laws (V := V)
  have hexp : Continuous (fun M : Matrix (Fin V.rank) (Fin V.rank) ℂ => NormedSpace.exp M) := continuous_matrix_exp' V.rank
  let F : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ} × ℝ → ℝ :=
    fun p => height V (atTau θ V τ (NormedSpace.exp (p.2 • p.1.1)))
  have hF : Continuous F := by
    have hin : Continuous fun p : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ} × ℝ =>
        NormedSpace.exp (p.2 • p.1.1) :=
      hexp.comp (continuous_snd.smul (continuous_subtype_val.comp continuous_fst))
    exact hl.2.2.2.2.comp ((GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous hin
      fun p => GlobalTheory.Mem.Lift.exp_mem p.1.2 p.2)
  have h0mem : (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ lieAt V τ := by
    show (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ + gramAt D V τ * 0 = 0
    simp
  have hF0 : ∀ t : ℝ, F (⟨0, h0mem⟩, t) = 1 := by
    intro t
    show height V (atTau θ V τ (NormedSpace.exp (t • (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)))) = 1
    rw [smul_zero, NormedSpace.exp_zero, (GlobalTheory.PointAtPlaceHom.atTau_laws D θ hθ V τ).2.1, hl.2.1]
  have hev : ∀ᶠ x in 𝓝 (⟨0, h0mem⟩ : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ}),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, F (x, t) ≤ 2 := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_
    have hlt : F (⟨0, h0mem⟩, t) < 2 := by rw [hF0]; norm_num
    exact (hF.continuousAt.eventually (gt_mem_nhds hlt)).mono fun z hz => hz.le
  rw [nhds_subtype, Filter.eventually_comap] at hev
  filter_upwards [hev] with X hX hXl t ht
  exact hX ⟨X, hXl⟩ rfl t ht

theorem growthSize_sub_le (hθ : IsInfFam θ) {τ : D.what₂.Tau} {N : ℕ} {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V)
    (hf : growthSob θ V 1 N φ ≠ ⊤) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hh : ∀ t ∈ Set.Icc (0 : ℝ) 1, height V (oneP θ V τ X t) ≤ 2) :
    growthSize V N (rTr V (oneP θ V τ X 1) φ - φ) ≤
      ENNReal.ofReal ((∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖) * (growthSob θ V 1 N φ).toReal * 2 ^ N) := by
  set S := (growthSob θ V 1 N φ).toReal with hS
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  set s := ∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖ with hs_def
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hglob : ∀ a : Fin V.rank × Fin V.rank, ∀ h, ‖glDer θ V (τ, a) φ h‖ ≤ S * height V h ^ N := by
    intro a
    have h1 : growthSize V N (glDer θ V (τ, a) φ) ≤ growthSob θ V 1 N φ := by
      have h0 := le_wordSum (A := glDer θ V) (p := growthSize V N) (d := 1) (l := [(τ, a)]) (by simp) φ
      simpa [wordAct, growthSob] using h0
    have h2 : growthSize V N (glDer θ V (τ, a) φ) ≤ ENNReal.ofReal S := by
      rw [hS, ENNReal.ofReal_toReal hf]
      exact h1
    exact (growthSize_le_iff hS0).1 h2
  have hder : ∀ h, ‖Rder θ V τ X φ h‖ ≤ s * S * height V h ^ N := by
    intro h
    rw [Rder_eq_sum_glDer hθ hs hX, Finset.sum_apply]
    calc ‖∑ a : Fin V.rank × Fin V.rank, (X a.1 a.2 • glDer θ V (τ, a) φ) h‖
        ≤ ∑ a : Fin V.rank × Fin V.rank, ‖(X a.1 a.2 • glDer θ V (τ, a) φ) h‖ := norm_sum_le _ _
      _ ≤ ∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖ * (S * height V h ^ N) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [Pi.smul_apply, norm_smul]
          exact mul_le_mul_of_nonneg_left (hglob a h) (norm_nonneg _)
      _ = s * S * height V h ^ N := by rw [← Finset.sum_mul, mul_assoc]
  have hC : 0 ≤ s * S * 2 ^ N := by positivity
  rw [growthSize_le_iff hC]
  intro g
  have hl := height_laws (V := V)
  have hφd : ∀ t, HasDerivAt (fun r : ℝ => φ (g * oneP θ V τ X r)) (Rder θ V τ X φ (g * oneP θ V τ X t)) t :=
    fun t => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hs hX g') g t
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖Rder θ V τ X φ (g * oneP θ V τ X t)‖ ≤ s * S * 2 ^ N * height V g ^ N := by
    intro t ht
    have hk : height V (oneP θ V τ X t) ≤ 2 := hh t (Set.Ico_subset_Icc_self ht)
    have hgk : height V (g * oneP θ V τ X t) ≤ height V g * 2 :=
      (hl.2.2.2.1 g _).trans (mul_le_mul_of_nonneg_left hk (zero_le_one.trans (hl.1 g)))
    have hpow : height V (g * oneP θ V τ X t) ^ N ≤ (height V g * 2) ^ N :=
      pow_le_pow_left₀ (zero_le_one.trans (hl.1 _)) hgk N
    calc ‖Rder θ V τ X φ (g * oneP θ V τ X t)‖ ≤ s * S * height V (g * oneP θ V τ X t) ^ N := hder _
      _ ≤ s * S * (height V g * 2) ^ N := mul_le_mul_of_nonneg_left hpow (mul_nonneg hs0 hS0)
      _ = s * S * 2 ^ N * height V g ^ N := by rw [mul_pow]; ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r : ℝ => φ (g * oneP θ V τ X r))
    (a := 0) (b := 1) (fun t _ => (hφd t).hasDerivWithinAt) hb 1 (by simp)
  simp only [sub_zero, mul_one] at key
  rw [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
  exact key

theorem tendsto_growthSize_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 1 N φ ≠ ⊤ → Filter.Tendsto (fun u : Matrix (Fin V.rank) (Fin V.rank) ℂ => GlobalTheory.Size.growthSize V N (rTr V (atTau θ V τ u) φ - φ)) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (nhds 0) := by
  intro D θ hθ V τ N φ hs hf
  obtain ⟨Λ, hΛmem, hΛ0, hΛexp⟩ := exists_log V τ
  have hH := exists_height_le hθ V τ
  have h1 : Filter.Tendsto Λ (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := hΛ0.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun u => ∑ a : Fin V.rank × Fin V.rank, ‖Λ u a.1 a.2‖)
      (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
    have h3 : ∀ a : Fin V.rank × Fin V.rank, Filter.Tendsto (fun u => ‖Λ u a.1 a.2‖)
        (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
      intro a
      have hce : Continuous fun M : Matrix (Fin V.rank) (Fin V.rank) ℂ => M a.1 a.2 := by
        fun_prop
      have h5 : Filter.Tendsto (fun u => Λ u a.1 a.2) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ)))
          (𝓝 ((0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) a.1 a.2)) :=
        (hce.tendsto _).comp h1
      simpa using h5.norm
    have h4 := tendsto_finsetSum (Finset.univ : Finset (Fin V.rank × Fin V.rank)) fun a _ => h3 a
    simpa using h4
  have hc : Filter.Tendsto (fun u => ENNReal.ofReal ((∑ a : Fin V.rank × Fin V.rank, ‖Λ u a.1 a.2‖) *
      (growthSob θ V 1 N φ).toReal * 2 ^ N)) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
    have h4 := ENNReal.tendsto_ofReal ((h2.mul_const ((growthSob θ V 1 N φ).toReal)).mul_const ((2 : ℝ) ^ N))
    simpa using h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hΛexp, h1.eventually hH] with u hu hhu
  have hk : atTau θ V τ u = oneP θ V τ (Λ u) 1 := by
    show atTau θ V τ u = atTau θ V τ (NormedSpace.exp ((1 : ℝ) • Λ u))
    rw [one_smul, hu]
  rw [hk]
  exact growthSize_sub_le hθ hs hf (hΛmem u) (hhu (hΛmem u))

end GlobalTheory.Size.NearOne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.SquareAgree

variable {D : D7}

theorem kapX_mem (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g : GA D X) :
    (reindex e e (Formalism.L2.Theta.mt X g))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (reindex e e (Formalism.L2.Theta.mt X g)).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := by
  have k : (Formalism.L2.Theta.mt X g)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ * (Formalism.L2.Theta.mt X g).map (cA D) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
    have := congrArg transpose (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram X g)
    rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
    exact this
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) = reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ) := rfl
  rw [hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul, e1]
  simp only [reindex_apply, transpose_submatrix, submatrix_mul_equiv, ← Matrix.submatrix_map]
  rw [k]

end GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

variable {D : D7}

def kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g : GA D X) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J :=
  ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e).toMonoidHom (matHom X g), by
    show (reindex e e (Formalism.L2.Theta.mt X g))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J * (reindex e e (Formalism.L2.Theta.mt X g)).map (cA D) = _
    exact kapX_mem X e hJ g⟩

theorem mat_kapX (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (g : GA D X) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (kapX X e hJ g) = reindex e e (Formalism.L2.Theta.mt X g) := rfl

section Datum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}

def IsDatum (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z) (Φ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ) : Prop :=
  Φ ∈ GlobalTheory.WeilM.schA F _ ∧ ∀ u, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u Φ) = f (crd u)

def algD (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) :
    Submodule ℂ ((Fin n × Fin d → AF F) → ℂ) :=
  Submodule.span ℂ {Φ | ∃ f φ, f ∈ M.Pol ψ emb ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ v = M.vac v) ∧
    Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ}

theorem rho_zero (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (Φ : (Fin n × Fin d → AF F) → ℂ) :
    M.co.rho ψ 0 Φ = Φ := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

end Datum

end GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

variable {D : D7}

structure IsOver (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁))
    (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X) : Prop where

  psi : Bs.ψ = ψ

  alpha : Xc.α = α

  beta : Xc.β = β

  JW : Γ.V.J = (1 : D.host.E) • W.gram

  JW₁ : Γ.V'.J = (-1 : D.host.E) • W₁.gram

  JX : Γ.W.J = D.host.xi0 • reindex e e X.gramᵀ

  measW : Γ.M.μ = ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 JW)

  domW : Γ.M.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 JW '' 𝓕

  measW₁ : Γ.M'.μ = ν₁.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) JW₁)

  domW₁ : Γ.M'.dom = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) JW₁ '' 𝓕₁

  weilA : ∀ Φ f, IsDatum Γ.M ψ cA Φ f → ∀ g h,
    IsDatum Γ.M ψ cA (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 JW g, kapX X e JX h) Φ) (ωA (g, h) f)

  weilB : ∀ Φ f, IsDatum Γ.M' ψ cB Φ f → ∀ g h,
    IsDatum Γ.M' ψ cB (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) JW₁ g, kapX X e JX h) Φ) (ωB (g, h) f)

  algA : ∀ Φ ∈ algF ψ θ true A B, ∃ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, IsDatum Γ.M ψ cA ΦD Φ

  algA' : ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ true A B, IsDatum Γ.M ψ cA ΦD Φ

  algB : ∀ Φ ∈ algF ψ θ false A₁ B, ∃ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, IsDatum Γ.M' ψ cB ΦD Φ

  algB' : ∀ ΦD ∈ algD Γ.M' Bs.ψ Bs.emb, ∃ Φ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB ΦD Φ

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}

theorem IsOver.theta_eq_A (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) {Φ : _} {f : WO W X → ℂ}
    (hD : IsDatum Γ.M ψ cA Φ f) (g : GA D W) (h : GA D X) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om Φ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW g) (kapX X e hO.JX h) = thetaKO ωA g h f := by
  have := (hO.weilA Φ f hD g h).2 0
  rw [rho_zero, map_zero] at this
  exact this

theorem IsOver.theta_eq_B (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) {Φ : _} {f : WO W₁ X → ℂ}
    (hD : IsDatum Γ.M' ψ cB Φ f) (g : GA D W₁) (h : GA D X) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ g) (kapX X e hO.JX h) = thetaKO ωB g h f := by
  have := (hO.weilB Φ f hD g h).2 0
  rw [rho_zero, map_zero] at this
  exact this

end GlobalTheory.SquareAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaModelsAreCoverDiscreteSeriesOfHarishChandra
section
namespace GlobalTheory.CoverModel

theorem modelsAreCoverSeries_all :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules →
      ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D :=
  modelsAreCoverSeries

end GlobalTheory.CoverModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusFieldComplexRootsNormEqOneCompactStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll GlobalTheory.TrEll.RealTorus
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusFieldComplexRoots_norm_eq_one_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (w : InfinitePlace F) (τ : EmbOver E w), Function.Bijective (PsiAll P τ) → CompactSpace (Tor P w.Completion) → ∀ i, ‖cxRoots τ.1 P i‖ = 1 := by
  first | exact @GlobalTheory.TrEll.realTorus_norm_cxRoots | exact GlobalTheory.TrEll.realTorus_norm_cxRoots | (intros; apply GlobalTheory.TrEll.realTorus_norm_cxRoots <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TotallyIsotropicDimBoundsOddRank
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoDim

theorem finrank_perp_add {E : Type} [Field E] [NumberField E] [StarRing E] (V : HSpace E)
    (W : Submodule E V.V) :
    Module.finrank E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) + Module.finrank E W = V.rank := by
  classical
  set a := Module.finrank E W
  let b := Module.finBasis E W
  let ψ : V.V →ₗ[E] (Fin a → E) := LinearMap.pi fun i => V.hT (b i : V.V)
  have hker : LinearMap.ker ψ = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W := by
    ext y
    simp only [LinearMap.mem_ker, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf]
    constructor
    · intro h w hw
      have e := congrArg (fun v : Fin a → E => v) h
      have hw' : (⟨w, hw⟩ : W) = ∑ i, (b.repr ⟨w, hw⟩ i) • b i := (b.sum_repr _).symm
      have : w = ∑ i, (b.repr ⟨w, hw⟩ i) • (b i : V.V) := by
        have := congrArg Subtype.val hw'
        rw [Submodule.coe_sum] at this
        simp only [Submodule.coe_smul] at this
        exact this
      rw [this, map_sum, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply]
      have := congrFun h i
      simp only [ψ, LinearMap.pi_apply, Pi.zero_apply] at this
      rw [this, smul_zero]
    · intro h
      funext i
      simpa [ψ] using h (b i) (b i).2
  have hsurj : LinearMap.range ψ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    let c : Fin a → E := fun i => f (Pi.single i 1)
    have hfc : ∀ v : Fin a → E, f v = ∑ i, v i * c i := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      simp only [smul_eq_mul, c]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    have hy : ∀ y, V.hT (∑ i, (star (c i)) • (b i : V.V)) y = 0 := by
      intro y
      have h1 : f (ψ y) = 0 := by
        have : f (ψ y) ∈ (LinearMap.range ψ).map f := ⟨ψ y, ⟨y, rfl⟩, rfl⟩
        rw [hf] at this
        exact (Submodule.mem_bot E).1 this
      rw [hfc] at h1
      rw [map_sum, LinearMap.sum_apply]
      rw [← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
      simp [ψ, mul_comm]
    have hx := V.nondeg.1 _ hy
    have hli : LinearIndependent E (fun i => (b i : V.V)) :=
      b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
    have hc : ∀ i, star (c i) = 0 := by
      have := (Fintype.linearIndependent_iff.1 hli) (fun i => star (c i)) hx
      exact this
    apply hf0
    apply LinearMap.ext
    intro v
    rw [hfc]
    simp [fun i => star_eq_zero.1 (hc i)]
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hsurj, hker, finrank_top, Module.finrank_fin_fun, V.rank_eq] at hrn
  omega

end GlobalTheory.IsoDim

theorem GlobalTheory.IsoDim.isotropic_dim_bounds : ∀ (D : D7) (V : HSp D), Odd V.rank → ∀ W : Submodule D.host.E V.V, GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W →
    0 < Module.finrank D.host.E W ∧ 2 * Module.finrank D.host.E W + 1 ≤ V.rank := by
  intro D V hodd W hW
  have h := GlobalTheory.IsoDim.finrank_perp_add V W
  have hle : Module.finrank D.host.E W ≤ Module.finrank D.host.E (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W) :=
    Submodule.finrank_mono hW.2
  have hpos : 0 < Module.finrank D.host.E W :=
    Nat.pos_of_ne_zero fun h0 => hW.1 (Submodule.finrank_eq_zero.1 h0)
  obtain ⟨k, hk⟩ := hodd
  refine ⟨hpos, ?_⟩
  omega
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceFormGramPowerBasisHermitianNondegenerateStatement
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceFormGramPowerBasis_hermitian_nondegenerate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r), IsHermND σ (GlobalTheory.TrUnitLat.gramOne P) := by
  first | exact @GlobalTheory.TrUnitLat.gramOne_herm_nd | exact GlobalTheory.TrUnitLat.gramOne_herm_nd | (intros; apply GlobalTheory.TrUnitLat.gramOne_herm_nd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalSumEmbeddingLeMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.SquareComm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_orthogonalSum_embedding_le_mul : ∀ (D : D7) (θ : InfFam D) (V V₁ : HSp D) (g : GA D V) (g₁ : GA D V₁), GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ (hsum V V₁) (blk V V₁ (g, g₁)) ≤ GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g * GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V₁ g₁ := by
  first | exact @GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul | exact GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul | (intros; apply GlobalTheory.Adopt.unitaryAdelicHeight_orthogonalSum_embedding_le_mul <;> assumption)
end

