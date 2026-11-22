import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeCoefficientsCommonZerosSimple
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0051
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticLineBundleFrameEqAppellHumbert
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBlockProductMemIntegralHarmonic
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0052
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0054
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0005
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeCoefficientsCommonZerosSimpleStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ae_coefficients_common_zeros_simple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) , ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∀ x ∈ X.dom, sf 0 x ≠ 0 → (∀ k : Fin (nd X), sf k.succ x = 0) → (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k => sf k.succ (cpt X x z) / sf 0 (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
  first | exact @GlobalTheory.ParamSard.main | exact GlobalTheory.ParamSard.main | (intros; apply GlobalTheory.ParamSard.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticFrameOfAppellHumbertFramePeriodFamilyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticFrame_of_appellHumbertFramePeriodFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (σ' : KA l →+* ℂ) (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (Pm : (F.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (F.Di i) ty Pm → y.x = F.u i Pm → AHFrame F i Pm Hm χl fr → (∀ ℓ : Lt1 Dw, IsDerivAt0 (fun z => (F.ex i Pm z).left) (Pi.single (el.symm ℓ) 1) (y.u ℓ.1 ℓ.2)) → ∃ Φ : AnPt y g ty el, Φ.OfFam F i Pm ∧ Φ.Hm = Hm ∧ Φ.χ = χl ∧ Φ.fr = fr ∧ (∀ (α : 𝓞 E) a, Pm (F.t i (α • a)) = tyAct ty α (Pm (F.t i a))) ∧ ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), levPt Xo y.x a = Φ.e ((l.M : ℂ)⁻¹ • Pm (F.t i a)) := by
  first | exact @GlobalTheory.AnVal.anPt_of_family | exact GlobalTheory.AnVal.anPt_of_family | (intros; apply GlobalTheory.AnVal.anPt_of_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AnalyticLineBundleFrameEqAppellHumbertStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_line_bundle_frame_eq_appellHumbert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] [StarRing (𝓞 E)] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), Φ.toAnFr.Imm → ∀ (e : ∀ m, FrTy y g Φ.jx m) (wP : PrimTy H Xo), Φ.IsAnE e → IsPrim wP → (∀ (m k : ℕ) (τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 1) (fun _ => (Φ.jx m).left) fun _ => (k : ℤ))), Φ.toAnFr.JetRd (n := 1) m (fun _ : Fin 1 => (Φ.jx m).left) (fun _ => (k : ℤ)) τ (fun _ => LinearMap.proj 0) → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (genPow _ _ (eL y g Φ.jx (anFB ty).A.act e wP m) k)) ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ (eL y g Φ.jx (anFB ty).A.act e wP 0) (homAt y.x (jetAug : Jet ℂ (Fin 1 × Fin g) 0 →ₐ[ℂ] ℂ)).left) (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x ℂ) 1) := by
  first | exact @GlobalTheory.AnValEL.eL_appellHumbert | exact GlobalTheory.AnValEL.eL_appellHumbert | (intros; apply GlobalTheory.AnValEL.eL_appellHumbert <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeepSubMulRecAll
section
open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

theorem deepSubMul_rec_all : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), EtaleWeightGaps.DeepSubMul (recPJ h j hj) ∧ EtaleWeightGaps.DeepSubMul (recPlus h j hj) ∧ ∀ (j' : ℕ) (ka : WeightFamilies.Wt D j') (Nt : NetData (recB h.toLawsCore) j' ka) (hM : NetMax Nt) (hL : NetLeSup Nt), EtaleWeightGaps.DeepSubMul (B := Nt.Bp hM hL) (PJ.tol2NormAlt _ _ _ _ _ _ (recPlus h j hj)) := by
  intro D T h j hj
  have h0 : EtaleWeightGaps.DeepSubMul (recPJ h j hj) := recSubMul D T h j hj
  have h1 : EtaleWeightGaps.DeepSubMul (recPlus h j hj) := h0
  exact ⟨h0, h1, fun j' ka Nt hM hL => h1⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeterminantBlockProductRenameTorusPolynomialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantBlockProduct_rename_torusPolynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (K : Type) [Field K] (σ : K →+* ℂ) (P : MvPolynomial (LtN Dw n) K), IsBlockProd P → ∀ (dim : (E →+* ℂ) → ℕ) (rl : (E →+* ℂ) → (E →+* ℂ)) (hd : ∀ τ, Dw.mult τ ≤ dim (rl τ)), Function.Injective rl → P ≠ 0 ∧ P.IsHomogeneous P.totalDegree ∧ ∃ (nb : ℕ) (bs : Fin nb → I2.Block E n dim), I2.Disj bs ∧ I2.DF bs = P.totalDegree ∧ ∀ (t : ℂ) (F : (Fin n → I2.Vsp dim) → ℂ), Differentiable ℂ F → I2.polyDeriv (MvPolynomial.map σ P) (fun ℓ => t • I2.dir ((ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩) : I2.Letter n dim)) F 0 = t ^ P.totalDegree * I2.polyDeriv (I2.P1 bs) I2.dir F 0 := by
  first | exact @GlobalTheory.BlockRen.blockProd_rename | exact GlobalTheory.BlockRen.blockProd_rename | (intros; apply GlobalTheory.BlockRen.blockProd_rename <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBlockProductMemIntegralHarmonicStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockProduct_mem_integralHarmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ τ i k, i ≤ k → a (τ, k) ≤ a (τ, i)) → I2.PT.f E * (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) ≤ 2 * n → ∃ P : MvPolynomial (LtN Dw n) c.F, P ∈ harmA c a n ∧ IsBlockProd P ∧ P.totalDegree = Formalism.L2.Pj.DF Dw a ∧ ∀ σ : c.F →+* ℂ, ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤ ((Dw.p + Dw.q : ℕ) : ℝ) ^ Formalism.L2.Pj.DF Dw a := by
  first | exact @GlobalTheory.BlockProdEx.exists_blockProd_mem_harmA | exact GlobalTheory.BlockProdEx.exists_blockProd_mem_harmA | (intros; apply GlobalTheory.BlockProdEx.exists_blockProd_mem_harmA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsClearingIntegersPrincipalDatumHost
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.HostClear

theorem absNorm_pos (D : D7) : 0 < Ideal.absNorm D.host.ccK :=
  Nat.pos_of_ne_zero fun h0 => D.host.ccK_ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)

theorem d_pos (D : D7) : 0 < D.host.d := D.host.hyp.2.1.pos

theorem sqrt_ne_zero (D : D7) : D.host.sqrtMinusD ≠ 0 := by
  intro h
  have h1 := D.host.sqrtMinusD_sq
  rw [h] at h1
  have h2 : (D.host.d : D.host.E) = 0 := by linear_combination h1
  exact (d_pos D).ne' (by exact_mod_cast h2)

theorem norm_embedding_hostFormConstant_eq (D : D7) (τ : D.host.E →+* ℂ) :
    ‖τ D.host.xi0‖ = 1 / ((Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d) := by
  have hn : ‖τ D.host.sqrtMinusD‖ ^ 2 = D.host.d := by
    rw [← norm_pow, ← map_pow, D.host.sqrtMinusD_sq, map_neg, map_natCast, norm_neg, Complex.norm_natCast]
  have h1 : ‖τ D.host.sqrtMinusD‖ = Real.sqrt D.host.d := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  unfold Formalism.BasicNotions.Host.xi0
  rw [map_div₀, map_mul, map_natCast, map_neg, map_one, norm_div, norm_neg, norm_one, norm_mul,
    Complex.norm_natCast, h1]

theorem different_le (D : D7) : differentIdeal ℤ (𝓞 D.host.E) ≤ D.host.𝔟 := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 D.host.K) (𝓞 D.host.E)]
  refine (Ideal.mul_le_inf.trans inf_le_left).trans ?_
  rw [D.host.𝔟_spec.1]
  exact Ideal.mul_le_inf.trans inf_le_left

theorem isIntegral_mul_of_mem (D : D7) {z : 𝓞 D.host.E} (hz : z ∈ D.host.𝔟) {a : D.host.E} (ha : a ∈ D.host.AA) :
    IsIntegral ℤ ((z : D.host.E) * a) := by
  obtain ⟨hB, -⟩ := bB_ne D
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0 at ha
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hB] at ha
  obtain ⟨w, -, hw⟩ := (FractionalIdeal.mem_coeIdeal _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  have : (z : D.host.E) * a = (w : D.host.E) := by
    rw [mul_comm]; exact hw.symm
  rw [this]
  exact w.isIntegral_coe

theorem absNorm_mem_AA (D : D7) : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA := by
  obtain ⟨hB, -⟩ := bB_ne D
  unfold Formalism.BasicNotions.Host.AA Formalism.BasicNotions.Host.AA0
  rw [← div_eq_mul_inv, FractionalIdeal.mem_div_iff_of_ne_zero hB]
  intro y hy
  obtain ⟨z, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
  have h1 : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∈ D.host.ccE := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) (Ideal.absNorm_mem D.host.ccK)
    rwa [map_natCast] at this
  refine (FractionalIdeal.mem_coeIdeal _).2 ⟨_, D.host.ccE.mul_mem_right z h1, ?_⟩
  rw [map_mul, map_natCast]

theorem host_clear : ∀ (D : D7) (L : ℝ), 2 ≤ L → lrd D ≤ 2 * L → Real.log D.host.d ≤ 2 * L → Real.log (Ideal.absNorm D.host.ccK) ≤ 2 * L → (∃ NA : ℕ, 0 < NA ∧ (∀ a ∈ D.host.AA, IsIntegral ℤ ((NA : D.host.E) * a)) ∧ Real.log NA ≤ 4 * L) ∧ ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ∈ D.host.AA ∧ 0 < Ideal.absNorm D.host.ccK ∧ (∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : D.host.E) * (2 * D.host.xi0)) ∧ Real.log m ≤ 4 * L) ∧ Real.log (1 / (2 * xiR D)) ≤ 3 * L ∧ fdeg D.host.E = D.R.f ∧ Real.log (dE D.host.E) ≤ 4 * fdeg D.host.E * L ∧ Real.log (rdE D.host.E) ≤ 2 * L ∧ D.R.f ≤ D.R.r ∧ 1 ≤ D.R.f ∧ ReciprocityTheory.ChartRestriction.G.FD.cc D.host.xi0 = -D.host.xi0 ∧ D.host.xi0 ≠ 0 ∧ (∀ τ : D.host.E →+* ℂ, ‖τ D.host.xi0‖ = xiR D) := by
  intro D L hL hrd hd hc
  have hN := absNorm_pos D
  have hd0 := d_pos D
  have hNR : (0 : ℝ) < Ideal.absNorm D.host.ccK := by exact_mod_cast hN
  have hdR : (0 : ℝ) < D.host.d := by exact_mod_cast hd0
  have hNE : ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hN.ne'
  have hs := sqrt_ne_zero D
  have hfin := GlobalTheory.PinNum.finrank_host D
  have hf1 : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
    unfold Ranks.f; omega
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
  have hfd : fdeg D.host.E = D.R.f := by
    unfold fdeg; rw [hfin]; omega
  have hdisc : 0 < |((NumberField.discr D.host.E : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hlog : Real.log |((NumberField.discr D.host.E : ℤ) : ℝ)| ≤ 4 * D.R.f * L := by
    unfold lrd at hrd
    rw [div_le_iff₀ (by positivity)] at hrd
    linarith
  refine ⟨?_, absNorm_mem_AA D, hN, ?_, ?_, hfd, ?_, ?_, ?_, hf1, conj_xi0_alt D, ?_, ?_⟩
  · have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
    obtain ⟨N, hN0, hNm, hNle⟩ := GlobalTheory.T.exists_natCast_mem_differentIdeal_pow_le_discr_sq D.host.E
    refine ⟨N, hN0, fun a ha => ?_, ?_⟩
    · have := isIntegral_mul_of_mem D (different_le D hNm) ha
      simpa using this
    · have hNR' : (0 : ℝ) < N := by exact_mod_cast hN0
      have h1 := Real.log_le_log (by positivity) hNle
      rw [Real.log_pow, Real.log_pow, hfin] at h1
      push_cast at h1
      have h2 : (D.R.f : ℝ) * Real.log N ≤ D.R.f * (4 * L) := by linarith
      exact le_of_mul_le_mul_left h2 (by linarith)
  · refine ⟨Ideal.absNorm D.host.ccK * D.host.d, Nat.mul_pos hN hd0, ?_, ?_⟩
    · have h1 : ((Ideal.absNorm D.host.ccK * D.host.d : ℕ) : D.host.E) * (2 * D.host.xi0) =
          2 * D.host.sqrtMinusD := by
        have h2 : (D.host.d : D.host.E) = -D.host.sqrtMinusD ^ 2 := by
          rw [D.host.sqrtMinusD_sq, neg_neg]
        unfold Formalism.BasicNotions.Host.xi0
        push_cast
        rw [h2]
        field_simp
      rw [h1]
      exact IsIntegral.mul (by exact_mod_cast isIntegral_natCast (R := ℤ) (B := D.host.E) 2) (sqrtMinusD_isIntegral D)
    · push_cast
      rw [Real.log_mul hNR.ne' hdR.ne']
      linarith
  · have hsq : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 hdR
    have h1 : 1 / (2 * xiR D) = (Ideal.absNorm D.host.ccK : ℝ) * Real.sqrt D.host.d / 2 := by
      unfold xiR
      rw [norm_embedding_hostFormConstant_eq]
      field_simp
    rw [h1, Real.log_div (by positivity) two_ne_zero, Real.log_mul hNR.ne' hsq.ne', Real.log_sqrt hdR.le]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    linarith
  · rw [hfd]; exact hlog
  · unfold rdE dE
    rw [Real.log_rpow hdisc, hfin]
    unfold lrd at hrd
    push_cast
    rw [one_div_mul_eq_div]
    exact hrd
  · have h1 := D.R.f_le_k
    have h2 := D.R.two_le_m
    unfold Ranks.f Ranks.n Ranks.r
    omega
  · unfold Formalism.BasicNotions.Host.xi0
    exact div_ne_zero (neg_ne_zero.2 one_ne_zero) (mul_ne_zero hNE hs)
  · intro τ
    unfold xiR
    rw [norm_embedding_hostFormConstant_eq, norm_embedding_hostFormConstant_eq]

end GlobalTheory.HostClear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFaithfullyFlatSplitIsotropicGroupStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_faithfullyFlat_split_isotropicGroup : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.FaithfullyFlat ∧ (∀ i, InZh Xo Λ N (z i)) ∧ GeoInj Xo (spMap φ ≫ x0) z := by
  first | exact @GlobalTheory.exists_faithfullyFlat_split_Zh | exact GlobalTheory.exists_faithfullyFlat_split_Zh | (intros; apply GlobalTheory.exists_faithfullyFlat_split_Zh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsShiftNullValNeZero
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaBase

open GlobalTheory.ThetaCoord GlobalTheory.VVRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem mk_eq_zero_iff (k : ℕ) (m : Dw.La) :
    (Submodule.Quotient.mk m : LatMod Dw k) = 0 ↔ ∃ m' : Dw.La, k • m' = m := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]

theorem exists_shift {R : ℕ} (hR : R ≠ 0) (q : LatMod Dw (R ^ 4)) (hq : R • q = 0) :
    ∃ u : LatMod Dw R, (Submodule.Quotient.mk (R ^ 3 • qRep u) : LatMod Dw (R ^ 4)) = q := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨m', hm⟩ := (mk_eq_zero_iff (R ^ 4) (R • m)).1 hq
  have e : R ^ 3 • m' = m := by
    have h : R • R ^ 3 • m' = R • m := by rw [← hm, ← mul_nsmul', ← pow_succ']
    refine Dw.unimod.1 (LinearMap.ext fun v => nsmul_right_injective hR ?_)
    have := congrArg (fun t => Dw.EF t v) h
    simpa only [map_nsmul, LinearMap.smul_apply] using this
  refine ⟨Submodule.Quotient.mk m', ?_⟩
  have h : (Submodule.Quotient.mk (qRep (Submodule.Quotient.mk m' : LatMod Dw R)) : LatMod Dw R) =
      Submodule.Quotient.mk m' := Classical.choose_spec (Submodule.Quotient.mk_surjective _ _)
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub] at h ⊢
  obtain ⟨d, hd⟩ := (mk_eq_zero_iff R _).1 h
  refine (mk_eq_zero_iff _ _).2 ⟨d, ?_⟩
  rw [← e, ← smul_sub, ← hd, ← mul_nsmul', ← pow_succ]

variable (Xo : Moduli Dw l) (c : Coeff l)

theorem gen_ne_zero {K : Type} [CommRing K] [Nontrivial K] [Algebra c.F K] (y : FrPt Xo c K) :
    (SecM.ofSec Xo.univ.t.G y.s : SecM Xo.univ.t.G Xo.univ.t.PP.L 1 (Over.mk y.x)) ≠ 0 := fun h => by
  have h₀ : ∀ i, y.s.f i = 0 := fun i => congrFun (congrArg Subtype.val h) i
  exact zero_ne_one ((y.gen y.s).unique (y₁ := 0) (y₂ := 1) (fun i => by rw [h₀, MulZeroClass.mul_zero])
    (fun i => by rw [h₀, MulZeroClass.mul_zero]))

theorem exists_nullVal_ne_zero (hL : Laws) {K : Type} [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K)
    (N : ℕ) {n : ℕ} (hn : 2 ≤ n) (a : ptO Xo y.x ⟶ Xo.univ.t.G) :
    ∃ z : ptO Xo y.x ⟶ Xo.univ.t.G, z ^ n = 1 ∧
      ∀ p w, IsNullVal Xo c N y p w → p ^ N = a * z → w ≠ 0 := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨z, hz, hu⟩ := UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange (UnivPol.pol Xo) y.x hn hK y.s
    (gen_ne_zero Xo c y) a
  refine ⟨z, hz, ?_⟩
  rintro p w ⟨F, ⟨t', α₀, α, s₁, U, -, rfl, -, -, -, hs₁, hU, hF⟩, hw⟩ hp h₀
  let o : (Over.mk y.x).left := IsLocalRing.closedPoint K
  choose J hJ using fun χ : (Over.mk y.x).left ⟶ Xo.univ.t.G.left => exists_chart Xo.univ.t.PP.isLB (χ o)
  replace hJ : Good Xo.univ.t.PP.L o J := hJ
  have b₁ := sv_act hU.pt_eq hF (𝟙 _) hJ 1
  have b₂ := sv_mulPull hs₁ (𝟙 _) hJ t'
  have b₃ := sv_of_isValueAt hw (𝟙 _) hJ
  rw [Category.id_comp, _root_.mul_one] at b₁
  rw [Category.id_comp] at b₃
  rw [b₃, b₂, hp, h₀, map_zero, UT.ExactTerm.gs_zero' _ _ ⊤ trivial, MulZeroClass.zero_mul] at b₁
  exact ((Units.isUnit _).mul ((Units.isUnit _).mul (hu o J hJ))).ne_zero b₁.symm

end GlobalTheory.EtaBase

namespace GlobalTheory

open GlobalTheory.EtaBase

theorem exists_shift_nullVal_ne_zero : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : ℕ), Odd R → 1 < R → ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra c.F K] (y : FrPt Xo c K) (ev : LatMod Dw (R ^ 4) → (ptO Xo y.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → K), IsFullLev Xo (R ^ 4) y.x ev → (∀ q, IsNullVal Xo c (R ^ 2) y (ev q) (w q)) → ∀ (n : ℕ) (x₀ : Fin n → Dw.La) (g : LevGrp Dw (R ^ 4)), ∃ u : Fin n → LatMod Dw R, ∀ b, w (g (shiftFam R x₀ u b)) ≠ 0 := by
  intro hL E _ _ _ H Dw l Xo c R _ hR K _ _ _ y ev w hev hw n x₀ g
  have hR₀ : R ≠ 0 := by omega
  have e₀ : ev 0 = 1 := by
    have := hev.1 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have es : ∀ (m : ℕ) q, ev (m • q) = ev q ^ m := fun m q => by
    induction m with
    | zero => rw [zero_smul, e₀, pow_zero]
    | succ m ih => rw [succ_nsmul, hev.1, ih, pow_succ]
  have sur := ((T.fullLinearLevel_cover_baseChange_torsor hL E H Dw l Xo (R ^ 4) (by positivity)).2.2.1 K y.x ev hev).1
  have key : ∀ x : Dw.La, ∃ u : LatMod Dw R,
      w (g (Submodule.Quotient.mk (x + R • qRep u))) ≠ 0 := fun x => by
    obtain ⟨z, hz, h⟩ := exists_nullVal_ne_zero Xo c hL y (R ^ 2) hR (ev (g (Submodule.Quotient.mk x)) ^ R ^ 2)
    obtain ⟨q, rfl⟩ := sur z (by rw [pow_succ', pow_mul, hz, one_pow])
    have hq : R • q = 0 := hev.2.2 K (RingHom.id K) _ _ (by rw [es, hz, e₀])
    obtain ⟨u, hu⟩ := exists_shift hR₀ (g.symm q) (by rw [← map_nsmul, hq, map_zero])
    refine ⟨u, h _ _ (hw _) ?_⟩
    rw [← es, ← es, ← hev.1, ← g.apply_symm_apply q, ← hu, ← map_nsmul, ← map_nsmul, ← map_add]
    congr 2
    show (Submodule.Quotient.mk (R ^ 2 • (x + R • qRep u)) : LatMod Dw (R ^ 4)) =
      Submodule.Quotient.mk (R ^ 2 • x + R ^ 3 • qRep u)
    rw [smul_add, ← mul_nsmul', ← pow_succ]
  choose u hu using key
  exact ⟨fun b => u (x₀ b), fun b => hu (x₀ b)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusWithSignUniformisationFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusWithSign_uniformisationFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x), ∃ A : I2.TorusAt (U.X k) x.1, A.w0 = H.w0 := by
  first | exact @GlobalTheory.TorusSign.exists_torusAt_w0_eq | exact GlobalTheory.TorusSign.exists_torusAt_w0_eq | (intros; apply GlobalTheory.TorusSign.exists_torusAt_w0_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsCore : ∀ (D : D7) (T : Core D), LawsCore T → GamAt T := by
  intro D T h j hj σ hσ k γ h1 h2
  exact GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence D T h j hj σ hσ k γ h1 h2

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicSumIndependentOfChoicesLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicSum_independent_of_choices_local : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ (P : MvPolynomial (LtN Dw n) c.F) (T : Type) [CommRing T] [IsLocalRing T] [Algebra c.F T] (y : FrPt Xo c T) (z1 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp1 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F1 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (z2 : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (tp2 : (Fin n → LevQ Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G)) (F2 : (Fin n → LevQ Dw l) → Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))), (∀ i, InZh Xo Λ N (z1 i)) → GeoInj Xo y.x z1 → (∀ q b, tp1 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp1 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z1 i b) (tp1 q b) (F1 q i b)) → (∀ i, InZh Xo Λ N (z2 i)) → GeoInj Xo y.x z2 → (∀ q b, tp2 q b ^ N = levPt Xo y.x (levRep (q b)) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp2 q b)) → (∀ q i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N y.s (z2 i b) (tp2 q b) (F2 q i b)) → ∀ q, ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F1 q i b) (colOf m b) = ∑ i, ∑ m ∈ P.support, algebraMap c.F T (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F2 q i b) (colOf m b) := by
  first | exact @GlobalTheory.shortSum_indep_local | exact GlobalTheory.shortSum_indep_local | (intros; apply GlobalTheory.shortSum_indep_local <;> assumption)
end

