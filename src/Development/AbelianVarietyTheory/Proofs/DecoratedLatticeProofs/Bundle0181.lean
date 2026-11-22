import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemidirectHaarMeasureFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnScalarFormNormBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.ColBound

theorem colForm_bound : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK), ∃ C : ℝ, ∀ (ξ : X.Vpi u) (a : GA D A), ‖B.colForm T.1 ξ a‖ ≤ C * ‖ξ‖ := by
  intro D X h u ψ A B hK T
  have hca := (GlobalTheory.Core.Mi.PhCol.ph_colForm D X h u ψ A B hK T).1
  obtain ⟨K, hKc, hKg⟩ := B.cpt
  have hb : ∀ ξ, ∃ c : ℝ, 0 ≤ c ∧ ∀ a, ‖B.colForm T.1 ξ a‖ ≤ c := by
    intro ξ
    obtain ⟨c, hc⟩ := hKc.exists_bound_of_continuousOn ((hca ξ).2.continuousOn)
    refine ⟨max c 0, le_max_right _ _, fun a => ?_⟩
    obtain ⟨γ, hγ, hγK⟩ := hKg a
    rw [← (hca ξ).1 γ hγ a]
    exact (hc _ hγK).trans (le_max_left _ _)
  let b := Module.finBasis ℂ (X.Vpi u)
  choose c hc0 hc using fun i => hb (b i)
  let L : ∀ i, X.Vpi u →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  refine ⟨∑ i, ‖L i‖ * c i, fun ξ a => ?_⟩
  have hlin : B.colForm T.1 ξ a = ∑ i, L i ξ * B.colForm T.1 (b i) a := by
    have hξ : ξ = ∑ i, b.repr ξ i • b i := (b.sum_repr ξ).symm
    have e1 : B.colForm T.1 ξ a = (T.1 ξ) (B.toH a) := rfl
    rw [e1]
    conv_lhs => rw [hξ]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [hlin, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  calc ‖L i ξ‖ * ‖B.colForm T.1 (b i) a‖ ≤ (‖L i‖ * ‖ξ‖) * c i :=
        mul_le_mul ((L i).le_opNorm ξ) (hc i a) (norm_nonneg _) (by positivity)
    _ = ‖L i‖ * c i * ‖ξ‖ := by ring

end GlobalTheory.Core.Mi.ColBound

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BesselQuot

theorem besGrp_quotient : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ), B.μR.IsHaarMeasure ∧ IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ (∃ Ω : Set (GA D B.V), IsCompact Ω ∧ ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) ∧ ∃ 𝓢 : Set (besGrp B.d B.o), IsFundamentalDomain ((GQ B.V).subgroupOf (besGrp B.d B.o)) 𝓢 B.μR ∧ B.μR 𝓢 < ⊤ ∧ ∀ F : GA D B.V → ℂ, ContinuousOn F (besGrp B.d B.o : Set (GA D B.V)) → (∀ γ ∈ GQ B.V ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o, F (γ * s) = F s) → IntegrableOn (fun s : besGrp B.d B.o => F s) 𝓢 B.μR ∧ ∫ s in 𝓢, F s ∂B.μR = ∫ a in B.vA.𝓕, ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν ∂B.vA.μ := by
  intro D ρ B
  obtain ⟨-, hcl, hHaar⟩ := GlobalTheory.MixPer.jacGrp_besGrp_haar D B.V B.V₀ B.A B.L ρ B.d B.o B.vN.ν B.vN.𝓝 B.vN.unit
  have hμR : B.μR.IsHaarMeasure := hHaar B.vA.μ B.vA.haar
  obtain ⟨hsc, hNcl, hnorm, huniq, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨⟨KN, hKN, hKNcov⟩, -⟩ :=
    GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B.V ρ B.d.e (GlobalTheory.MixPer.isIsoSub_e B.d)
  obtain ⟨KA, hKA, hKAcov⟩ := B.cpt
  have hγA : ∀ γ ∈ GQ B.A, embA B.d B.o γ ∈ GQ B.V := fun γ hγ => by
    have h1 := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
    simpa using h1
  set Ω : Set (GA D B.V) := (fun p : GA D B.V × GA D B.A => p.1 * embA B.d B.o p.2) '' ((Subtype.val '' KN) ×ˢ KA) with hΩ
  have hΩc : IsCompact Ω :=
    ((hKN.image continuous_subtype_val).prod hKA).image (continuous_fst.mul (hsc.comp continuous_snd))
  have hΩsub : Ω ⊆ (besGrp B.d B.o : Set (GA D B.V)) := by
    rintro _ ⟨⟨_, a⟩, ⟨⟨k, hk, rfl⟩, -⟩, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right ⟨a, rfl⟩)
  have hcov : ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω := by
    intro s hs
    obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o s).1 hs
    obtain ⟨γA, hγAQ, hγAK⟩ := hKAcov a
    have hn1 : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ ∈ flagN B.d := hnorm n hn γA
    obtain ⟨γN, hγN, k, hk, he⟩ := hKNcov ⟨_, hn1⟩
    have he' : embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹ = γN.1 * k.1 := congrArg Subtype.val he
    have hk1 : k.1 = γN.1⁻¹ * (embA B.d B.o γA * n * (embA B.d B.o γA)⁻¹) := eq_inv_mul_of_mul_eq he'.symm
    have hQ : γN.1⁻¹ * embA B.d B.o γA ∈ GQ B.V :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hγN)) (hγA γA hγAQ)
    have hR : γN.1⁻¹ * embA B.d B.o γA ∈ besGrp B.d B.o :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left γN.2)) (Subgroup.mem_sup_right ⟨γA, rfl⟩)
    refine ⟨γN.1⁻¹ * embA B.d B.o γA, Subgroup.mem_inf.2 ⟨hQ, hR⟩, ?_⟩
    refine ⟨(k.1, γA * a), ⟨⟨k, hk, rfl⟩, hγAK⟩, ?_⟩
    simp only [hk1, map_mul]
    group
  have hcovA : ∀ g : GA D B.A, ∃ γ ∈ GQ B.A, ∃ k ∈ KA, g = γ * k := fun g => by
    obtain ⟨γ, hγ, hk⟩ := hKAcov g
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, γ * g, hk, by group⟩
  have := B.vA.haar
  have hFfin : B.vA.μ B.vA.𝓕 < ⊤ :=
    GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ B.A) hKA hcovA B.vA.μ B.vA.fund
  have hNfin : B.vN.ν B.vN.𝓝 < ⊤ := by rw [B.vN.unit.2.2]; exact ENNReal.one_lt_top
  obtain ⟨𝓡, hfd, hint⟩ := GlobalTheory.Unf.semiFd_iterated D B.V B.A (flagN B.d) (embA B.d B.o) hsc hNcl hnorm huniq hrat B.vA
    B.vN.ν B.vN.𝓝 B.vN.unit.1 B.vN.unit.2.1 hμR
  have : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.2 hFfin.ne
  have : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hNfin.ne
  refine ⟨hμR, hcl, ⟨Ω, hΩc, hcov⟩, 𝓡, ?_, ?_, ?_⟩
  · rw [← Subgroup.inf_subgroupOf_right]; exact hfd
  · have h1 := (hint (fun _ => (1 : ℂ)) measurable_const).1.2 (integrable_const _)
    exact ((integrableOn_const_iff).1 h1).resolve_left (by simp)
  · intro F hF hinv
    classical
    set F' : GA D B.V → ℂ := (besGrp B.d B.o : Set (GA D B.V)).piecewise F 0 with hF'
    have hF'm : Measurable F' := hF.measurable_piecewise continuousOn_const hcl.measurableSet
    obtain ⟨C, hC⟩ := hΩc.exists_bound_of_continuousOn (hF.mono hΩsub)
    have hb : ∀ x, ‖F' x‖ ≤ max C 0 := by
      intro x
      by_cases hx : x ∈ (besGrp B.d B.o : Set (GA D B.V))
      · obtain ⟨γ, hγ, hγx⟩ := hcov x hx
        rw [hF', Set.piecewise_eq_of_mem _ _ _ hx, ← hinv γ hγ x hx]
        exact (hC _ hγx).trans (le_max_left _ _)
      · rw [hF', Set.piecewise_eq_of_notMem _ _ _ hx]; simp
    have hAC : AbsConv B.vA.μ B.vA.𝓕 B.vN.ν B.vN.𝓝 fun h n => F' (n.1 * embA B.d B.o h) := by
      refine Integrable.of_bound ?_ (max C 0) (Filter.Eventually.of_forall fun p => hb _)
      exact (hF'm.comp ((continuous_subtype_val.comp continuous_snd).mul
        (hsc.comp continuous_fst)).measurable).aestronglyMeasurable
    have hpt : ∀ r : ↥(flagN B.d ⊔ (embA B.d B.o).range), F' r = F r := fun r => Set.piecewise_eq_of_mem _ _ _ r.2
    have hpt2 : ∀ a (n : flagN B.d), F' (n.1 * embA B.d B.o a) = F (n.1 * embA B.d B.o a) := fun a n =>
      Set.piecewise_eq_of_mem _ _ _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨a, rfl⟩))
    obtain ⟨hi1, hi2⟩ := hint F' hF'm
    have e1 : (fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F' r) =
        fun r : ↥(flagN B.d ⊔ (embA B.d B.o).range) => F r := funext hpt
    have e2 : (fun a => ∫ n in B.vN.𝓝, F' (n.1 * embA B.d B.o a) ∂B.vN.ν) =
        fun a => ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν := funext fun a => by simp only [hpt2]
    refine ⟨?_, ?_⟩
    · have h3 := hi1.2 hAC
      rw [e1] at h3
      exact h3
    · have h3 := hi2 hAC
      rw [e1, e2] at h3
      exact h3

end GlobalTheory.BesselQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjDoublingIsotropicUnipotentMemSiegel
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

namespace GlobalTheory.Core.Rk.Dich

theorem exists_leftInv_of_linInd {K : Type} [Field K] {a b : ℕ} (C : Matrix (Fin a) (Fin b) K)
    (hC : LinearIndependent K C.transpose) : ∃ L : Matrix (Fin b) (Fin a) K, L * C = 1 := by
  have hinj : Function.Injective C.mulVec := Matrix.mulVec_injective_iff.2 hC
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' C)
    (LinearMap.ker_eq_bot.2 fun x y h => hinj (by simpa [Matrix.toLin'_apply] using h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  calc LinearMap.toMatrix' g * C = LinearMap.toMatrix' g * LinearMap.toMatrix' (Matrix.toLin' C) := by
        rw [LinearMap.toMatrix'_toLin']
    _ = LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' C) := (LinearMap.toMatrix'_comp _ _).symm
    _ = 1 := by rw [hg, LinearMap.toMatrix'_id]

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem conj_io_gen_mem (V : HSp D) (γ : GA D (dblSp V)) (hγ : γ ∈ GQ (dblSp V))
    (γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E)
    (hγi : (Formalism.L2.Theta.matHom (dblSp V) γ⁻¹).1 = γi.map (incA D)) (r : ℕ)
    (K : Matrix (Fin V.rank) (Fin r) D.host.E) (hK : diagSnd γi * K = 0)
    (hC : IsIsoFrame V (leviMat finSumFinEquiv γi * K)) (g : GA D V)
    (h1 : HMul.hMul ((Formalism.L2.Theta.matHom V g).1 - 1) ((leviMat finSumFinEquiv γi * K).map (incA D)) = 0)
    (h3 : ∀ x : Fin V.rank → D.host.E,
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (leviMat finSumFinEquiv γi * K) * V.gram).mulVec x = 0 →
      ∃ a : Fin r → AE D, ((Formalism.L2.Theta.matHom V g).1 - 1).mulVec (fun i => incA D (x i)) =
        ((leviMat finSumFinEquiv γi * K).map (incA D)).mulVec a) :
    ∃ h : γ * io V (g, 1) * γ⁻¹ ∈ siegel V, aP V ⟨_, h⟩ = 1 := by
  classical
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set J := V.gram with hJ
  have hinjA : Function.Injective (incA D) := by
    haveI : Nontrivial (AF D.host.F) := inferInstanceAs (Nontrivial (Ainf D.host.F × Af D.host.F))
    exact Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective
  obtain ⟨g0, hg0, -, hinv⟩ := exists_rat (dblSp V) hγ
  have hγi' : γi = (g0⁻¹).1 := Matrix.map_injective hinjA (hγi.symm.trans hinv)
  have hu : Formalism.UG.cT σ γi * GlobalTheory.Doubling.dblGram finSumFinEquiv J * γi = GlobalTheory.Doubling.dblGram finSumFinEquiv J := by
    rw [hγi', hJ, ← gram_hdbl V]; exact (Formalism.UG.UJ _ _).inv_mem hg0
  have hiso := isotropic_diag hu
  set P := leviMat finSumFinEquiv γi with hP
  set Q' := diagSnd γi with hQ'
  set C := P * K with hCdef
  have hCJP : Formalism.UG.cT σ C * J * P = 0 := by
    calc Formalism.UG.cT σ C * J * P = Formalism.UG.cT σ K * (Formalism.UG.cT σ P * J * P) := by
          rw [hCdef, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT σ (Q' * K) * J * Q' := by rw [hiso, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hK]; simp [Formalism.UG.cT]
  have hcol : ∀ i, (Formalism.UG.cT σ C * J).mulVec (fun j => P j i) = 0 := fun i => by
    funext k
    have := congrFun (congrFun hCJP k) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  choose a ha using fun i => h3 _ (hcol i)
  set G := (Formalism.L2.Theta.matHom V g).1 with hG
  set m := G - 1 with hm
  let A : Matrix (Fin r) (Fin V.rank) (AE D) := Matrix.of fun k i => a i k
  have hmP : m * P.map (incA D) = HMul.hMul (C.map (incA D)) A := by
    ext j i
    have := congrFun (ha i) j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply, A] using this
  have hCm : C.map (incA D) = HMul.hMul (P.map (incA D)) (K.map (incA D)) := Matrix.map_mul
  obtain ⟨L, hL⟩ := exists_leftInv_of_linInd C hC.2.1
  have hAK : A * K.map (incA D) = 0 := by
    have e1 : C.map (incA D) * (A * K.map (incA D)) = 0 := by
      rw [← Matrix.mul_assoc, ← hmP, Matrix.mul_assoc, ← hCm, h1]
    have e2 : L.map (incA D) * C.map (incA D) = 1 := by
      rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]
    calc A * K.map (incA D) = L.map (incA D) * C.map (incA D) * (A * K.map (incA D)) := by
          rw [e2, Matrix.one_mul]
      _ = 0 := by rw [Matrix.mul_assoc, e1, Matrix.mul_zero]
  set Γ := (Formalism.L2.Theta.matHom (dblSp V) γ).1 with hΓ
  set Γi := (Formalism.L2.Theta.matHom (dblSp V) γ⁻¹).1 with hΓi
  have hΓΓi : Γ * Γi = 1 := by
    rw [hΓ, hΓi, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hMg : (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1 = Γ * blkMat finSumFinEquiv G 1 * Γi := by
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, matHom_io, val_blkGL, map_one, Units.val_one]
  have hdiag : ∀ x : Fin V.rank → AE D, Γi *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (P.map (incA D) *ᵥ x) (Q'.map (incA D) *ᵥ x) := fun x => by
    rw [hγi, mulVec_pairVec_diag, leviMat_map, diagSnd_map]
  have hact : ∀ x : Fin V.rank → AE D, (Γ * blkMat finSumFinEquiv G 1 * Γi) *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (x + (K.map (incA D) * A) *ᵥ x) (x + (K.map (incA D) * A) *ᵥ x) := fun x => by
    have hy : Γi *ᵥ pairVec finSumFinEquiv (x + (K.map (incA D) * A) *ᵥ x) (x + (K.map (incA D) * A) *ᵥ x) =
        blkMat finSumFinEquiv G 1 *ᵥ (Γi *ᵥ pairVec finSumFinEquiv x x) := by
      rw [hdiag, hdiag, blkMat_mulVec, one_mulVec]
      congr 1
      · rw [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, ← hCm, ← hmP, ← mulVec_mulVec,
          show G = m + 1 from (sub_add_cancel G 1).symm, add_mulVec, one_mulVec, add_comm]
      · rw [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.map_mul, hK,
          Matrix.map_zero _ (map_zero _), Matrix.zero_mul, zero_mulVec, add_zero]
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← hy, mulVec_mulVec, hΓΓi, one_mulVec]
  have hKD : KeepsDiag finSumFinEquiv (Γ * blkMat finSumFinEquiv G 1 * Γi) :=
    keepsDiag_of_mulVec fun w hw => by
      obtain ⟨x, rfl⟩ := (mem_diagSub finSumFinEquiv).1 hw
      rw [hact]; exact (pairVec_mem_diagSub finSumFinEquiv).2 rfl
  have hmem : γ * io V (g, 1) * γ⁻¹ ∈ siegel V := mem_siegelOf.2 (by
    change KeepsDiag finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1
    rw [hMg]; exact hKD)
  have hlevi : leviMat finSumFinEquiv (Γ * blkMat finSumFinEquiv G 1 * Γi) = 1 + K.map (incA D) * A := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    have h := (hKD.mulVec_diag (Pi.single j 1)).symm.trans (hact _)
    funext i
    have := congrFun h (finSumFinEquiv (.inl i))
    rw [pairVec_inl, pairVec_inl] at this
    rw [this, add_mulVec, one_mulVec]
  refine ⟨hmem, Units.ext ?_⟩
  rw [Units.val_one]
  change (leviMat finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (g, 1) * γ⁻¹)).1).det = 1
  rw [hMg, hlevi, Matrix.det_one_add_mul_comm, hAK, add_zero, Matrix.det_one]

theorem conj_io_unip_siegel : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ n ∈ NI V (leviMat finSumFinEquiv γi * K), ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1 := by
  intro D V γ hγ γi hγi r K hK hC n hn
  let φ : GA D V →* GA D (dblSp V) := (MulAut.conj γ).toMonoidHom.comp ((io V).comp (MonoidHom.inl _ _))
  let H : Subgroup (GA D (dblSp V)) := (aP V).ker.map (siegel V).subtype
  have hle : NI V (leviMat finSumFinEquiv γi * K) ≤ H.comap φ := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    obtain ⟨h1, -, h3⟩ := hg
    obtain ⟨hmem, ha⟩ := conj_io_gen_mem V γ hγ γi hγi r K hK hC g h1 h3
    exact ⟨⟨_, hmem⟩, ha, rfl⟩
  obtain ⟨p, hp, hpe⟩ := hle hn
  refine ⟨p, ?_, hp⟩
  have : (p : GA D (dblSp V)) = γ * io V (n, 1) * γ⁻¹ := hpe
  rw [this, inv_mul_cancel_right]

end GlobalTheory.Core.Rk.Dich
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffHeisenbergSuperpositionThetaFunctionRealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_heisenbergSuperposition_thetaFunction_real : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → WO S T) (a : Ω → ℂ), Measurable v → Integrable a μ → ContDiff ℝ ∞ (fun z : GlobalTheory.FockCompare.RW T S => ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F (v x) ∂μ) := by
  first | exact @GlobalTheory.SuperposSmooth.main | exact GlobalTheory.SuperposSmooth.main | (intros; apply GlobalTheory.SuperposSmooth.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePow
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EisCont.Shift

open Set Metric

theorem holValueAt_of_continuousAt {h : ℂ → ℂ} (a : GlobalTheory.Cont.Continues h) {t : ℂ}
    (b : ContinuousAt (GlobalTheory.Cont.cont h) t) : GlobalTheory.Cont.HolValueAt h t (GlobalTheory.Cont.cont h t) := by
  obtain ⟨H₀, hH⟩ := a
  have ha := hH.isExtAt (mem_univ t)
  exact ha.holValueAt_iff.2 ((b.tendsto.mono_left nhdsWithin_le_nhds).congr' ha.cont_eventuallyEq)

theorem differentiable_npow_sub {c : ℝ≥0} (hc : 0 < c) (s₁ : ℂ) : Differentiable ℂ fun s => npow c (s₁ - s) :=
  (GlobalTheory.Eis.differentiable_npow hc).comp (differentiable_const _ |>.sub differentiable_id)

theorem contMod_shift (D : D7) (T : HSp D) (e e' : ℂ → GA D T → ℂ) (x : GA D T) (c : ℝ≥0) (s₁ s₂ : ℂ) (hc : 0 < c)
    (he : ∀ s g, e' s g = npow c (s₁ - s) * e (s + s₂) (g * x)) (hm : ContMod T e) : ContMod T e' := by
  have hd := differentiable_npow_sub hc s₁
  have hfun : ∀ g, (fun z => e' z g) = fun z => npow c (s₁ - z) * (fun w => e w (g * x)) (z + s₂) :=
    fun g => funext fun z => he z g
  refine ⟨fun g => ?_, fun s₀ => ?_⟩
  · obtain ⟨H₀, hH⟩ := hm.1 (g * x)
    rw [GlobalTheory.Cont.isMerExt_univ] at hH
    obtain ⟨σ, hσ⟩ := hH.2
    refine ⟨fun z => npow c (s₁ - z) * H₀ (z + s₂), GlobalTheory.Cont.isMerExt_univ.2 ⟨fun z => ?_, σ - s₂.re, fun z hz => ?_⟩⟩
    · exact (hd.analyticAt z).meromorphicAt.fun_mul
        ((hH.1 (z + s₂)).comp_analyticAt (g := (· + s₂)) (by fun_prop))
    · simp only [he]
      congr 1
      exact hσ (by simpa [GlobalTheory.Cont.mem_rightOf] using sub_lt_iff_lt_add.1 hz)
  · obtain ⟨k, r, H, hr, h1, h2, h3, C, N, h4⟩ := hm.2 (s₀ + s₂)
    have hball : ∀ s ∈ ball s₀ r, s + s₂ ∈ ball (s₀ + s₂) r := fun s hs => by
      simpa [mem_ball, dist_eq_norm] using hs

    have hval : ∀ s ∈ ball s₀ r, s ≠ s₀ → ∀ g,
        GlobalTheory.Cont.cont (fun z => e' z g) s = npow c (s₁ - s) * GlobalTheory.Cont.cont (fun z => e z (g * x)) (s + s₂) := by
      intro s hs hne g
      have hne' : s + s₂ ≠ s₀ + s₂ := fun h => hne (add_right_cancel h)
      have hopen : ball (s₀ + s₂) r ∩ {s₀ + s₂}ᶜ ∈ 𝓝 (s + s₂) :=
        (isOpen_ball.inter isOpen_compl_singleton).mem_nhds ⟨hball s hs, hne'⟩
      have hcont : ContinuousAt (GlobalTheory.Cont.cont fun z => e z (g * x)) (s + s₂) := by
        have hq : ContinuousAt (fun t => H t (g * x) / (t - (s₀ + s₂)) ^ k) (s + s₂) :=
          (((h2 (g * x)).continuousOn.continuousAt (isOpen_ball.mem_nhds (hball s hs)))).div
            (by fun_prop) (pow_ne_zero _ (sub_ne_zero.2 hne'))
        refine hq.congr (Filter.eventually_of_mem hopen fun t ht => ?_)
        have := h1 t ht.1 ht.2 (g * x)
        show H t (g * x) / _ = _
        rw [this, mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 ht.2))]
      have hv := holValueAt_of_continuousAt (hm.1 (g * x)) hcont
      have hn : GlobalTheory.Cont.HolValueAt (fun z => npow c (s₁ - z)) s (npow c (s₁ - s)) :=
        GlobalTheory.Cont.IsHolExt.holValueAt ⟨GlobalTheory.Cont.isRightDomain_univ, fun z _ => hd.analyticAt z, .refl _⟩ (mem_univ s)
      have hp := hn.mul hv.comp_add
      rw [hfun g]
      exact hp.valueAt.cont_eq
    obtain ⟨B, hB⟩ := (isCompact_closedBall s₀ r).exists_bound_of_continuousOn hd.continuous.continuousOn
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB s₀ (mem_closedBall_self hr.le))
    refine ⟨k, r, fun s g => npow c (s₁ - s) * H (s + s₂) (g * x), hr, fun s hs hne g => ?_, fun g => ?_, ?_,
      B * |C| * GlobalTheory.Grow.height T x ^ N, N, fun s hs g => ?_⟩
    · show npow c (s₁ - s) * H (s + s₂) (g * x) = _
      rw [hval s hs hne g, h1 _ (hball s hs) (fun h => hne (add_right_cancel h)) (g * x)]
      rw [show s + s₂ - (s₀ + s₂) = s - s₀ by ring]
      ring
    · refine (hd.differentiableOn).mul ((h2 (g * x)).comp (by fun_prop) fun s hs => hball s hs)
    · refine (hd.continuous.comp continuous_fst).continuousOn.mul ?_
      exact h3.comp (f := fun p : ℂ × GA D T => (p.1 + s₂, p.2 * x)) (by fun_prop)
        fun (p : ℂ × GA D T) (hp : p ∈ ball s₀ r ×ˢ univ) => ⟨hball p.1 hp.1, mem_univ _⟩
    · have hH := h4 _ (hball s hs) (g * x)
      have hn := hB s (ball_subset_closedBall hs)
      have hg := GlobalTheory.Grow.height_mul_le T g x
      have hg0 := (GlobalTheory.Grow.height_pos T g).le
      have hx0 := (GlobalTheory.Grow.height_pos T x).le
      have hgx0 := (GlobalTheory.Grow.height_pos T (g * x)).le
      have e1 : ‖H (s + s₂) (g * x)‖ ≤ |C| * (GlobalTheory.Grow.height T g * GlobalTheory.Grow.height T x) ^ N :=
        hH.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hgx0 N)).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hgx0 hg N) (abs_nonneg C)))
      rw [norm_mul]
      calc ‖npow c (s₁ - s)‖ * ‖H (s + s₂) (g * x)‖ ≤ B * (|C| * (GlobalTheory.Grow.height T g * GlobalTheory.Grow.height T x) ^ N) :=
            mul_le_mul hn e1 (norm_nonneg _) hB0
        _ = B * |C| * GlobalTheory.Grow.height T x ^ N * GlobalTheory.Grow.height T g ^ N := by rw [mul_pow]; ring

end GlobalTheory.EisCont.Shift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormMap_values_compact_sobolev_bound : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ T : MMap M, IsMultMap θ M J χ T → ∀ Ω : Set (GA D V), IsCompact Ω → ∀ τ (v : M.Vec), ∃ (L : List (List (Matrix (Fin V.rank) (Fin V.rank) ℂ))) (C : ℝ), (∀ l ∈ L, ∀ Y ∈ l, Y ∈ lieAt V τ) ∧ ∀ w : M.sm τ, ∀ g ∈ Ω, ‖T (Function.update v τ w) g‖ ≤ C * (L.map fun l => ‖l.foldr (dRep (M.rep τ)) (w : M.H τ)‖).sum := by
  first | exact @GlobalTheory.Core.Mi.sobolev_unif_bound | exact GlobalTheory.Core.Mi.sobolev_unif_bound | (intros; apply GlobalTheory.Core.Mi.sobolev_unif_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteRightTranslateFiniteAStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rTr_mem_A0 : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ → ∀ k ∈ GfC A, ∀ u ∈ A0 θ A cA, rTr A k u ∈ A0 θ A cA := by
  first | exact @GlobalTheory.Core.Rk.RTr.cuspFormsArchimedeanKFinite_rightTranslate_finite | exact GlobalTheory.Core.Rk.RTr.cuspFormsArchimedeanKFinite_rightTranslate_finite | (intros; apply GlobalTheory.Core.Rk.RTr.cuspFormsArchimedeanKFinite_rightTranslate_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMemStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormsArchimedeanKFinite_star_comp_mem : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ → ∀ u ∈ A0 θ A cA, (fun g => conj (u g)) ∈ A0 θ A cA := by
  first | exact @GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 | exact GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 | (intros; apply GlobalTheory.Core.Rk.CuspConj.conj_comp_mem_A0 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCartanInvolutionCommuteMaximalCompactStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_cartanInvolution_commute_maximalCompact : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (sA : RealMat A) (a : GL (Fin A.rank) (AE D)), IsInfFam θ → (∀ τ, IsCartanInv (gramAt D A τ) (sA τ)) → (∀ τ, (compAt θ τ a.1)ᴴ * (gramAt D A τ * sA τ) * compAt θ τ a.1 = 1) → (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) ((Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm)) ∧ ∀ k ∈ Khat A a, ∀ τ, compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) * (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = (Matrix.fromBlocks (sA τ) 0 0 (-sA τ)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm * compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k) := by
  first | exact @GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl | exact GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl | (intros; apply GlobalTheory.Core.Rk.IP.Cartan.cartan_dbl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceLeOneStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingHeightAtRealPlace_le_one : ∀ (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ (w : InfinitePlace D.host.F) (y : Gw A w), GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w y ≤ 1 := by
  first | exact @GlobalTheory.Core.Rk.HgtArch.hgtW_le_one | exact GlobalTheory.Core.Rk.HgtArch.hgtW_le_one | (intros; apply GlobalTheory.Core.Rk.HgtArch.hgtW_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalVacuaToDoubledLatticeVacuumStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_sphericalVacua_to_doubled_lattice_vacuum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (LA : Lat A) (LB : Lat B), IsStdChar D ψ (-1) → IsSelfDualC A LA → IsSelfDualC (dblSp A) (sumLat finSumFinEquiv LA LA) ∧ ∀ (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsSphOff ψ A B LA LB Sf Φ₁ → IsSphOff ψ A B LA LB Sf Φ₂ → ∀ v ∉ Sf, IsLatVac (heisO ψ (dblSp A) B) (latO (dblSp A) B (sumLat finSumFinEquiv LA LA : Lat (dblSp A)) LB fun u => u = v) (delta A B Φ₁ Φ₂) := by
  first | exact @GlobalTheory.Core.Rk.VacBox.doubling_isLatVac | exact GlobalTheory.Core.Rk.VacBox.doubling_isLatVac | (intros; apply GlobalTheory.Core.Rk.VacBox.doubling_isLatVac <;> assumption)
end

