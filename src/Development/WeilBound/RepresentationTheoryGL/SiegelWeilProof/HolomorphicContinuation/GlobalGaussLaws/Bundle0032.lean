import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0031
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellT
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0030
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0029
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0022
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0009

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousInsT
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.StdUnn
open Formalism.IndefR.Eqv (psiT psiT_sigR psiT_inclR thetaC eq_thetaC glueA splitInv psiT_glueA finPart_glueA ae_ext'
  continuous_glueA continuous_splitInv continuous_psiT)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTP

open Classical

variable {D : D7} {m n : ℕ}

def insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  Matrix.of fun i j => glueA D (splitInv D fun τ' => if τ' = τ then v i j else 0) 0

theorem psiT_insT (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    psiT D τ' (insT τ v i j) = if τ' = τ then v i j else 0 := psiT_glueA D τ' _ 0

theorem finPart_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) :
    finPart D (insT τ v i j) = 0 := finPart_glueA D _ 0

theorem insT_add (τ : D.what₂.Tau) (v w : Matrix (Fin m) (Fin n) ℂ) : insT (D := D) τ (v + w) = insT τ v + insT τ w := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [Matrix.add_apply, RingHom.map_add, psiT_insT, psiT_insT, psiT_insT]
    split_ifs <;> simp
  · rw [Matrix.add_apply, RingHom.map_add, finPart_insT, finPart_insT, finPart_insT, add_zero]

theorem insT_zero (τ : D.what₂.Tau) : insT (D := D) (m := m) (n := n) τ 0 = 0 := by
  ext i j
  apply ae_ext' D
  · intro τ'
    rw [psiT_insT, Matrix.zero_apply, Matrix.zero_apply, RingHom.map_zero]
    split_ifs <;> rfl
  · rw [finPart_insT, Matrix.zero_apply, RingHom.map_zero]

theorem continuous_insT (τ : D.what₂.Tau) : Continuous (insT (D := D) (m := m) (n := n) τ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_glueA D 0).comp ((continuous_splitInv D).comp (continuous_pi fun τ' => ?_))
  split_ifs
  · exact (continuous_apply j).comp (continuous_apply i)
  · exact continuous_const

theorem compAt_insT {θ : InfFam D} (hθ : IsInfFam θ) (τ τ' : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) :
    compAt θ τ' (insT τ v) = if τ' = τ then v else 0 := by
  rw [eq_thetaC D hθ]
  ext i j
  show psiT D τ' (insT τ v i j) = _
  rw [psiT_insT]
  split_ifs <;> rfl

theorem finMap_insT (τ : D.what₂.Tau) (v : Matrix (Fin m) (Fin n) ℂ) : (insT (D := D) τ v).map (finPart D) = 0 := by
  ext i j; exact finPart_insT τ v i j

def sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : (Fin m → Fin n → ℂ) →+ Mx D m n where
  toFun u := insT τ (fr * Matrix.of u)
  map_zero' := by simp [insT_zero]
  map_add' u v := by
    rw [show Matrix.of (u + v) = Matrix.of u + Matrix.of v from rfl, Matrix.mul_add, insT_add]

set_option synthInstance.maxHeartbeats 400000 in

def piF (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) : Mx D m n →+ (Fin m → Fin n → ℂ) where
  toFun y := Matrix.of.symm (fr⁻¹ * compAt θ τ y)
  map_zero' := by
    ext i j
    simp [compAt]
  map_add' y y' := by
    have h : compAt θ τ (y + y') = compAt θ τ y + compAt θ τ y' := by
      ext i j; simp only [compAt, Matrix.map_apply, Matrix.add_apply, RingHom.map_add]
    ext i j
    simp only [h, Matrix.mul_add]
    rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem piF_sIns {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {fr : Matrix (Fin m) (Fin m) ℂ}
    (hfr : IsUnit fr.det) (u : Fin m → Fin n → ℂ) : piF θ τ fr (sIns (D := D) τ fr u) = u := by
  show Matrix.of.symm (fr⁻¹ * compAt θ τ (insT τ (fr * Matrix.of u))) = u
  rw [compAt_insT hθ, if_pos rfl, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr, Matrix.one_mul]
  rfl

theorem continuous_piF {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (piF (n := n) θ τ fr) := by
  have h : Continuous fun y : Mx D m n => (fr⁻¹ * compAt θ τ y : Matrix (Fin m) (Fin n) ℂ) := by
    refine Continuous.matrix_mul continuous_const ?_
    rw [eq_thetaC D hθ]
    exact Continuous.matrix_map continuous_id (Formalism.IndefR.Eqv.continuous_psiT (D := D) τ)
  exact h

theorem continuous_sIns (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) :
    Continuous (sIns (D := D) (n := n) τ fr) := by
  show Continuous fun u : Fin m → Fin n → ℂ => insT τ (fr * Matrix.of u)
  exact (continuous_insT τ).comp (Continuous.matrix_mul continuous_const continuous_id)

end PositivityTheory.Rg.Sw.Glob.FTP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DHol
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct ENNReal Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.SiegelFormula
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

open DHolH

theorem dHol : DHol := by
  intro hP D n V hn hr θ hθ ν hν P _ _ U hU φ h1 h2 h3 h4 h5
  intro F

  have hfacts : ∀ (p₀ : P) (z₀ : ℂ), z₀ ∈ U → ∃ (N : Set (P × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧
      Continuous M ∧ absThetaInt V ν M < ⊤ ∧ ∀ pz ∈ N, pz.2 ∈ U → ∀ x, ‖φ pz.1 pz.2 x‖ ≤ ‖M x‖ := by
    intro p₀ z₀ hz₀
    obtain ⟨N, M, hN, hM, hb⟩ := h5 p₀ z₀ hz₀
    obtain ⟨hMc, hMf⟩ := sch_facts hP V hn hr θ hθ ν hν hM
    exact ⟨N, M, hN, hMc, hMf, hb⟩
  have hcontx : ∀ p, ∀ z ∈ U, Continuous (φ p z) := by
    intro p z hz
    exact (h4 p).comp_continuous (continuous_const.prodMk continuous_id) fun x => ⟨hz, Set.mem_univ _⟩
  have hfin : ∀ p, ∀ z ∈ U, absThetaInt V ν (φ p z) < ⊤ := by
    intro p z hz
    obtain ⟨N, M, hN, -, hMf, hb⟩ := hfacts p z hz
    exact lt_of_le_of_lt (absThetaInt_mono V ν (hb (p, z) (mem_of_mem_nhds hN) hz)) hMf
  have hmeas : ∀ p, ∀ z ∈ U, AEStronglyMeasurable (descend (GQ V) (thS V (φ p z))) (autMeasure V ν) :=
    fun p z hz => aestronglyMeasurable_thS V ν (hcontx p z hz) (hfin p z hz)
  have hfam : ∀ p, Fam V ν U (φ p) := by
    intro p
    refine ⟨h2 p, fun z₀ hz₀ => ?_, hmeas p⟩
    obtain ⟨N, M, hN, hMc, hMf, hb⟩ := hfacts p z₀ hz₀
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hN
    obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.1 hv
    obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hz₀)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, (Metric.ball_subset_ball (min_le_right _ _)).trans hb₂, M, hMc, hMf, ?_⟩
    intro z hz x
    have hzv : z ∈ v := hb₁ (Metric.ball_subset_ball (min_le_left _ _) hz)
    have hzU : z ∈ U := hb₂ (Metric.ball_subset_ball (min_le_right _ _) hz)
    exact hb (p, z) (huv ⟨mem_of_mem_nhds hu, hzv⟩) hzU x
  refine ⟨?_, fun p => ?_, fun p r z hz => ?_⟩
  ·
    rintro ⟨p₀, z₀⟩ ⟨-, hz₀⟩
    obtain ⟨N, M, hN, hMc, hMf, hb⟩ := hfacts p₀ z₀ hz₀
    have hfinq := ae_absTheta_lt V ν hMc hMf
    have hsumM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
        Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E => ‖M (invPt V q.out ξ)‖ := by
      intro q hq
      refine Summable.of_enorm ?_
      simpa [GlobalTheory.AutomorphicL2Unitary.descend, absTheta] using hq.ne
    have htsM : ∀ q : Quot (GQ V), descend (GQ V) (absTheta V M) q < ⊤ →
        ∑' ξ : Matrix (Fin V.rank) (Fin n) D.host.E, ‖M (invPt V q.out ξ)‖ =
          (descend (GQ V) (absTheta V M) q).toReal := by
      intro q hq
      simp only [GlobalTheory.AutomorphicL2Unitary.descend, absTheta]
      rw [ENNReal.tsum_toReal_eq fun ξ => enorm_ne_top]
      simp
    have hs : Set.univ ×ˢ U ∈ 𝓝[Set.univ ×ˢ U] (p₀, z₀) := self_mem_nhdsWithin
    have hNs : N ∩ Set.univ ×ˢ U ∈ 𝓝[Set.univ ×ˢ U] (p₀, z₀) := inter_mem (mem_nhdsWithin_of_mem_nhds hN) hs
    have hint : ContinuousWithinAt (fun pz : P × ℂ => ∫ q, descend (GQ V) (thS V (φ pz.1 pz.2)) q ∂autMeasure V ν)
        (Set.univ ×ˢ U) (p₀, z₀) := by
      refine continuousWithinAt_of_dominated (bound := fun q => (descend (GQ V) (absTheta V M) q).toReal) ?_ ?_
        (integrable_absTheta_toReal V ν hMc hMf) ?_
      · exact Eventually.mono hs fun pz hpz => hmeas pz.1 pz.2 hpz.2
      · refine Eventually.mono hNs fun pz hpz => ?_
        filter_upwards [hfinq] with q hq
        have hs1 := hsumM q hq
        have hs' : Summable fun ξ => ‖φ pz.1 pz.2 (invPt V q.out ξ)‖ :=
          Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hb pz hpz.1 hpz.2.2 _) hs1
        simp only [GlobalTheory.AutomorphicL2Unitary.descend, thS]
        calc ‖∑' ξ, φ pz.1 pz.2 (invPt V q.out ξ)‖ ≤ ∑' ξ, ‖φ pz.1 pz.2 (invPt V q.out ξ)‖ := norm_tsum_le_tsum_norm hs'
          _ ≤ ∑' ξ, ‖M (invPt V q.out ξ)‖ := hs'.tsum_le_tsum (fun ξ => hb pz hpz.1 hpz.2.2 _) hs1
          _ = _ := htsM q hq
      · filter_upwards [hfinq] with q hq
        have hs1 := hsumM q hq
        have hon : ContinuousOn (fun pz : P × ℂ => ∑' ξ, φ pz.1 pz.2 (invPt V q.out ξ)) (N ∩ Set.univ ×ˢ U) :=
          continuousOn_tsum (fun ξ => (h3 _).mono Set.inter_subset_right) hs1
            (fun ξ pz hpz => hb pz hpz.1 hpz.2.2 _)
        exact (hon.continuousWithinAt ⟨mem_of_mem_nhds hN, ⟨Set.mem_univ _, hz₀⟩⟩).mono_of_mem_nhdsWithin hNs
    have : (fun pz : P × ℂ => F pz.1 pz.2) = fun pz => ((autMeasure V ν) Set.univ).toReal⁻¹ •
        ∫ q, descend (GQ V) (thS V (φ pz.1 pz.2)) q ∂autMeasure V ν := by
      funext pz
      simp only [F, average_eq]
      rfl
    rw [this]
    exact hint.const_smul ((autMeasure V ν) Set.univ).toReal⁻¹
  · exact differentiableOn_avg V ν hU (hfam p)
  · exact iteratedDeriv_avg V ν hU (hfam p) r z hz

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerOne
section
namespace PositivityTheory.Rg.Sw.Glob

theorem derivOne (h : GlobalTheory.Published.WeilThetaConvergence) : DerivOne := derivOne_of h curveSt

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Planch
section
noncomputable section

open MeasureTheory FourierTransform

namespace PositivityTheory.Rg.Sw.Glob.PlanchH

open PositivityTheory.Rg.Sw.Glob.FTD

variable {m n : ℕ}

theorem haar_linR (A : (Fin m → Fin n → ℂ) ≃L[ℝ] V m n) : ∃ c : ℝ, 0 < c ∧ ∀ F : V m n → ℝ, Continuous F →
    ∫ y : Fin m → Fin n → ℂ, F (A y) = c * ∫ w, F w := by
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set μ' : Measure (V m n) := (volume : Measure (Fin m → Fin n → ℂ)).map A with hμ'
  have : μ'.IsAddHaarMeasure := A.isAddHaarMeasure_map volume
  have h := Measure.isAddLeftInvariant_eq_smul μ' volume
  refine ⟨Measure.addHaarScalarFactor μ' volume, by
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' volume, fun F hF => ?_⟩
  have h' : ∫ y, F y ∂μ' = ∫ y, F y ∂(Measure.addHaarScalarFactor μ' volume • volume) :=
    congrArg (fun ν => ∫ y, F y ∂ν) h
  rw [← integral_map A.continuous.aemeasurable hF.aestronglyMeasurable, ← hμ', h', integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

end PositivityTheory.Rg.Sw.Glob.PlanchH

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.FTD PositivityTheory.Rg.Sw.Glob.PlanchH

theorem planchLoc : PlanchLoc := by
  intro m n ε t ht
  obtain ⟨c1, hc1, hft⟩ := ftLoc_eq (m := m) (n := n) ε t ht
  obtain ⟨kM, hkM, hM⟩ := haar_linR (Mt (m := m) (n := n) ε t ht)
  obtain ⟨kL, hkL, hL⟩ := haar_linR (Lc (m := m) (n := n))
  refine ⟨c1 ^ 2 * kM / kL, by positivity, fun f hf => ?_⟩
  obtain ⟨S, rfl⟩ := hf
  set g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm S with hg
  have e1 : ∀ u, ‖ftLoc ε t (⇑S) u‖ ^ 2 = c1 ^ 2 * ‖(𝓕 g) (Mt ε t ht u)‖ ^ 2 := by
    intro u
    rw [hft S u, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg hc1.le]
  have e2 : ∀ u, ‖S u‖ ^ 2 = ‖g (Lc u)‖ ^ 2 := by
    intro u
    simp [hg]
  simp_rw [e1, e2]
  have h1 := hM (fun w => ‖(𝓕 g) w‖ ^ 2) ((SchwartzMap.continuous _).norm.pow 2)
  have h2 := hL (fun w => ‖g w‖ ^ 2) ((SchwartzMap.continuous _).norm.pow 2)
  rw [integral_const_mul, h1, h2, SchwartzMap.integral_norm_sq_fourier g]
  field_simp

end PositivityTheory.Rg.Sw.Glob
end
end

