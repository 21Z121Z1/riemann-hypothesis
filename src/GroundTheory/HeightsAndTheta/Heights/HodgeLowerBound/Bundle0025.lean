import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem StokesLimitPos.proof (hG : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement)
    (hTel : StokesTelescope.Statement) (hNs : NbarSemipos.Statement) (hTp : StokesLimitTp.Statement)
    (hT : StokesLimitT.Statement) (hE : StokesLimitEps.Statement) : StokesLimitPos.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B a hII hpos hB hAr hyp
  have hc0 : (0 : ℝ) ≤ ((D.n + 1 : ℕ) : ℝ) := by positivity

  have step : ∀ m : ℕ, ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
      X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1) ≤ X.topNLim B 1 (m + 1) := by
    intro m
    have hp : 1 ≤ 1 := le_rfl
    have hpq : 1 ≤ m + 1 := by omega
    obtain ⟨t₁, ht₁, hN⟩ := hNs II Ψ K ι Ω E D O Lt X B 1 (m + 1) hp hpq
    obtain ⟨tP, htP, hP⟩ := hpos B 1 (m + 1) hB hp hpq
    obtain ⟨tH, htH, hH⟩ := hyp 1 (m + 1) hp hpq
    obtain ⟨t₂, ht₂, hTp'⟩ := hTp II Ψ K ι Ω E D O Lt X B 1 (m + 1) hp hpq

    have stepT : ∀ t : ℝ, 0 < t → t ≤ min t₁ t₂ →
        ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) * X.degN B 1 (m + 1) t) -
          ((D.n + 1 : ℕ) : ℝ) * X.Vb B 1 (m + 1) t ≤ X.topN B 1 (m + 1) t := by
      intro t ht0 ht1
      have hNt := hN t ht0 (ht1.trans (min_le_left _ _))
      obtain ⟨hlim, hVb⟩ := hTp' t ht0 (ht1.trans (min_le_right _ _)) hNt
      have hev : ∀ᶠ t' in 𝓝[>] (0 : ℝ),
          ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) * X.degN B 1 (m + 1) t) -
            ((D.n + 1 : ℕ) : ℝ) * X.I0 B 1 (m + 1) t t' ≤ X.topN B 1 (m + 1) t := by
        filter_upwards [Ioc_mem_nhdsGT (lt_min htP htH)] with t' ht'
        have hsP := (hP t' ht'.1 (ht'.2.trans (min_le_left _ _))).1
        have htel := hTel II Ψ K ι Ω E D O Lt X B 1 (m + 1) t t' hII hpq hsP hNt
        have hh := hH t' ht'.1 (ht'.2.trans (min_le_right _ _))
        have hdeg : geomDegMUc X.H X.S' B 1 (m + 1) t' = X.degN B 1 (m + 1) t := by
          unfold geomDegMUc ComponentSetting.degN
          congr 1
          rw [hG K ι Ω D.y D.n _ D.arith hsP.1, hG K ι Ω D.y D.n _ D.arith hNt.1]
          congr 1
          simp only [ComponentSetting.MUq, MUc, ComponentSetting.NbarQ, smoothRepConj_a, smoothRep_a]
          rfl
        rw [hdeg] at hh
        have e : ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t) = ((D.n + 1 : ℕ) : ℝ) * (a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t := by ring
        linarith
      have hL : Tendsto (fun t' => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
          X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.I0 B 1 (m + 1) t t') (𝓝[>] 0)
          (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
            X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.Vlim B 1 (m + 1) t)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim)
      have h1 := le_of_tendsto hL hev
      have h2 := mul_le_mul_of_nonneg_left hVb hc0
      linarith
    obtain ⟨hT1, hT2, hT3⟩ := hT II Ψ K ι Ω E D O Lt X B 1 (m + 1) hII hAr hp hpq
    have hL : Tendsto (fun t => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
        X.degN B 1 (m + 1) t) - ((D.n + 1 : ℕ) : ℝ) * X.Vb B 1 (m + 1) t) (𝓝[>] 0)
        (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
          X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1))) :=
      (tendsto_const_nhds.mul (tendsto_const_nhds.mul hT3)).sub (tendsto_const_nhds.mul hT2)
    refine le_of_tendsto_of_tendsto hL hT1 ?_
    filter_upwards [Ioc_mem_nhdsGT (lt_min ht₁ ht₂)] with t ht using stepT t ht.1 ht.2

  obtain ⟨hE1, hE2, hE3⟩ := hE II Ψ K ι Ω E D O Lt X B hII hAr
  have hε : Tendsto (fun m : ℕ => ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Nat.cast_add, Nat.cast_one] using h0
  have hL : Tendsto (fun m : ℕ => ((D.n + 1 : ℕ) : ℝ) * ((a - ((1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) * D.KA) *
      X.degNLim B 1 (m + 1)) - ((D.n + 1 : ℕ) : ℝ) * X.VbLim B 1 (m + 1)) atTop
      (𝓝 (((D.n + 1 : ℕ) : ℝ) * ((a - 0 * D.KA) * degMu X.H) -
        ((D.n + 1 : ℕ) : ℝ) * (meanU X.H X.Cd * degMu X.H / 2))) :=
    (tendsto_const_nhds.mul ((tendsto_const_nhds.sub (hε.mul tendsto_const_nhds)).mul hE3)).sub
      (tendsto_const_nhds.mul hE2)
  have key := le_of_tendsto_of_tendsto' hL hE1 step
  calc ((D.n + 1 : ℕ) : ℝ) * (a - meanU X.H X.Cd / 2) * degMu X.H
      = ((D.n + 1 : ℕ) : ℝ) * ((a - 0 * D.KA) * degMu X.H) -
        ((D.n + 1 : ℕ) : ℝ) * (meanU X.H X.Cd * degMu X.H / 2) := by ring
    _ ≤ arLim X.H X.S B := key

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarChartSemipos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarChartSemipos.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt), ∃ c : ℝ, 0 < c ∧ ∀ (B p q : ℕ) (t δ : ℝ),
      X.M.atlas.Smooth (X.S.regWeight t) →
      (∀ k : Fin X.S.R.N, ∀ x ∈ X.S.R.mid k, ∀ w : Fin D.n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k x) w) →
      (q : ℝ) * δ ≤ p * c →
      IsSemipositiveH (mCoordIdeal D.y) (X.NbarQ B p q t)

section Inhabitants

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

omit [DecidableEq Ψ] in

theorem NbarChartSemipos.hyps_of_setting (X : ComponentSetting D O Lt) {c : ℝ} (hc : 0 < c) :
    ∃ t δ : ℝ, 0 < t ∧ X.M.atlas.Smooth (X.S.regWeight t) ∧
      (∀ k : Fin X.S.R.N, ∀ x ∈ X.S.R.mid k, ∀ w : Fin D.n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k x) w) ∧
      ((1 : ℕ) : ℝ) * δ ≤ ((1 : ℕ) : ℝ) * c := by
  have hlim : Tendsto (fun t => 4 * X.S.Cη * X.S.e1 t) (𝓝[>] 0) (𝓝 0) := by
    simpa using X.S_tied.e1_tendsto_zero.const_mul (4 * X.S.Cη)
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := eventually_mem_nhdsWithin
  have hev := (X.S.eventually_chartLevi X.S_tied).and (h1.and (hlim.eventually (eventually_le_nhds hc)))
  obtain ⟨t, ⟨hs, hl⟩, ht, hδ⟩ := hev.exists
  exact ⟨t, 4 * X.S.Cη * X.S.e1 t, ht, hs, hl, by simpa using hδ⟩

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

theorem NbarChartSemipos.hyps_inhabited {c : ℝ} (hc : 0 < c) :
    ∃ t δ : ℝ, 0 < t ∧ (projLineComponentSetting zeroSystem zero_hII).M.atlas.Smooth
        ((projLineComponentSetting zeroSystem zero_hII).S.regWeight t) ∧
      (∀ k : Fin (projLineComponentSetting zeroSystem zero_hII).S.R.N, ∀ x ∈ (projLineComponentSetting zeroSystem zero_hII).S.R.mid k,
        ∀ w : Fin (lineData zeroSystem zero_hII).n → ℂ,
        -δ * ‖w‖ ^ 2 ≤ levi ((projLineComponentSetting zeroSystem zero_hII).S.R.chartFun
          ((projLineComponentSetting zeroSystem zero_hII).S.regWeight t) k)
          ((projLineComponentSetting zeroSystem zero_hII).S.R.chart k x) w) ∧
      ((1 : ℕ) : ℝ) * δ ≤ ((1 : ℕ) : ℝ) * c :=
  LowerBoundFree.NbarChartSemipos.hyps_of_setting _ hc

end Line

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHermExtend
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def SmoothAlong {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (S : Set V) (f : V → ℝ) : Prop :=
  ∀ z ∈ S, ∃ U ∈ 𝓝 z, ∃ G : V → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G U ∧ ∀ w ∈ U ∩ S, f w = G w

def HermExtend.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (a : K → ℤ)
    (F : ((Σ k, ι k) → ℂ) → ℝ), IsMultiHomogIdeal P → (∀ z ∈ mcPts P, 0 < F z) →
    (∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z) →
    SmoothAlong (mcPts P) F →
    ∃ Z : HermLine ι, Z.a = a ∧ IsSmoothHerm Z ∧ ∀ z ∈ mcPts P, Z.h z = F z

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomMeanMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuHomMeanMass.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt),
    ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) X.Cd.cuspWeight = meanU X.H X.Cd * degMu X.H

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuHomTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuHomTail.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt),
    Tendsto (fun R : ℝ => ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H)
        (fun z => min (X.Cd.cuspWeight z) R))
      atTop (𝓝 (ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H) X.Cd.cuspWeight))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuMeasureLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuMeasureLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      Tendsto (fun t => ptsIntegral (e := D.n) (mCoordIdeal D.y)
          (fun _ z => Real.log ((muReg X.H X.S B t).h z)) (fun z => X.Cd.cuspWeight z / 2))
        (𝓝[>] 0) (𝓝 (meanU X.H X.Cd * degMu X.H / 2)) ∧
      Tendsto (fun t => geomDeg (mCoordIdeal D.y) (muReg X.H X.S B t) D.n) (𝓝[>] 0) (𝓝 (degMu X.H))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuRegMass.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    ∀ᶠ t in 𝓝[>] (0 : ℝ), geomDeg (mCoordIdeal D.y) (muReg X.H X.S B t) D.n = degMu X.H

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegSmooth
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuRegSmooth.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (muReg X.H X.S B t)

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuRegTail.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (δ : ℝ), 0 < δ →
    ∀ᶠ R in atTop, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      |ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ z => Real.log ((muReg X.H X.S B t).h z))
          X.Cd.cuspWeight -
        ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ z => Real.log ((muReg X.H X.S B t).h z))
          (fun z => min (X.Cd.cuspWeight z) R)| ≤ δ

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegTruncLimit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def MuRegTruncLimit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ) (R : ℝ),
    Tendsto (fun t => ptsIntegral (e := D.n) (mCoordIdeal D.y)
        (fun _ z => Real.log ((muReg X.H X.S B t).h z)) (fun z => min (X.Cd.cuspWeight z) R))
      (𝓝[>] 0) (𝓝 (ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu X.H)
        (fun z => min (X.Cd.cuspWeight z) R)))

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsOmNPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

def OmNPoly.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B : ℕ),
    IsIntersectionSystem II → ArLimExists X.H X.S B →
      ∃ v d : ℕ → ℝ → ℝ,
        v 0 = (fun t => ptsIntegral (e := D.n) (mCoordIdeal D.y)
          (fun _ z => Real.log ((muReg X.H X.S B t).h z)) (fun z => X.Cd.cuspWeight z / 2)) ∧
        d 0 = (fun t => geomDeg (mCoordIdeal D.y) (muReg X.H X.S B t) D.n) ∧
        ∀ q : ℕ, 1 ≤ q → ∀ᶠ t in 𝓝[>] (0 : ℝ),
          X.Vb B 1 q t = ∑ i ∈ Finset.range (D.n + 1), v i t * (1 / (q : ℝ)) ^ i ∧
          X.degN B 1 q t = ∑ i ∈ Finset.range (D.n + 1), d i t * (1 / (q : ℝ)) ^ i

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def IsPtsNull (P : Ideal (MRing ι)) (e : ℕ) (N : Set ((Σ k, ι k) → ℂ)) : Prop :=
  ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} = 0

def IsPtsIntegrable (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ∀ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ →
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ φ g y w)

def PtsBddConv.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : HermLine ι) (r : ℝ) (g : ℝ → ((Σ k, ι k) → ℂ) → ℝ) (g₀ : ((Σ k, ι k) → ℂ) → ℝ)
    (N : Set ((Σ k, ι k) → ℂ)) (C s₀ : ℝ),
    IsArithVar P (e + 1) → IsSmoothHerm L → 0 < r → IsPtsNull P e N → 0 < s₀ →
    (∀ s : ℝ, 0 < s → s < s₀ → (∀ z ∈ mcPts P, |g s z| ≤ C) ∧ ContinuousOn (g s) (mcPts P \ N) ∧
      ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, g s (torusSmul c z) = g s z) →
    (∀ z ∈ mcPts P, z ∉ N → Tendsto (fun s => g s z) (𝓝[>] 0) (𝓝 (g₀ z))) →
    IsPtsIntegrable P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀ ∧
      Tendsto (fun s => ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) (g s)) (𝓝[>] 0)
        (𝓝 (ptsIntegral P (fun (_ : Fin e) z => Real.log (L.h z) / r) g₀))

namespace Line

open GroundTheory.Heights₂.Heights.Regular.ProjectiveLine

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

