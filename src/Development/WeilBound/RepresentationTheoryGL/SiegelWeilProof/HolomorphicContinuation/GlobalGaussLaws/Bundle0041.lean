import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0039
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0006
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0030
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0009

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayAB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 100000

namespace PositivityTheory.Rg.Sw.Glob.AW

variable {D : D7} {n : ℕ}

theorem triv_mul {θ : InfFam D} {τ : D.what₂.Tau} {a b : G D n} (ha : IsTrivAt θ τ a) (hb : IsTrivAt θ τ b) :
    IsTrivAt θ τ (a * b) := by
  unfold IsTrivAt at *
  rw [GlobalTheory.StdUnn.LeftInvSect.mat_mul, compAt_mul', ha, hb, Matrix.mul_one]

theorem triv_inv {θ : InfFam D} {τ : D.what₂.Tau} {a : G D n} (ha : IsTrivAt θ τ a) : IsTrivAt θ τ a⁻¹ := by
  unfold IsTrivAt at *
  have h : compAt θ τ (mat a⁻¹) * compAt θ τ (mat a) = 1 := by
    rw [← compAt_mul', ← GlobalTheory.StdUnn.LeftInvSect.mat_mul, inv_mul_cancel, GlobalTheory.StdUnn.LeftInvSect.mat_one, compAt_one']
  rwa [ha, Matrix.mul_one] at h

theorem triv_one {θ : InfFam D} {τ : D.what₂.Tau} : IsTrivAt θ τ (1 : G D n) := by
  unfold IsTrivAt; rw [GlobalTheory.StdUnn.LeftInvSect.mat_one, compAt_one']

theorem eq_one_of_triv_ι {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι) {y : GR n}
    (hy : IsTrivAt θ τ (ι y)) : y = 1 := by
  unfold IsTrivAt at hy
  rw [(hι.2 y).1] at hy
  have h1 : mR y = 1 := by
    have h2 : (mR y).submatrix finSumFinEquiv.symm finSumFinEquiv.symm =
        (1 : M2 n).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
      rw [Matrix.submatrix_one_equiv]; exact hy
    have := congrArg (fun M => Matrix.submatrix M finSumFinEquiv finSumFinEquiv) h2
    simpa using this
  exact Subtype.ext (Units.ext h1)

theorem uniq_dec {θ : InfFam D} {τ : D.what₂.Tau} {ι : GR n →* G D n} (hι : IsPlaceEmb θ τ ι) {a a' : G D n} {y y' : GR n}
    (ha : IsTrivAt θ τ a) (ha' : IsTrivAt θ τ a') (h : a * ι y = a' * ι y') : y = y' := by
  have h2 : ι (y * y'⁻¹) = a⁻¹ * a' := by
    rw [map_mul, map_inv]
    calc ι y * (ι y')⁻¹ = a⁻¹ * (a * ι y) * (ι y')⁻¹ := by group
      _ = a⁻¹ * (a' * ι y') * (ι y')⁻¹ := by rw [h]
      _ = a⁻¹ * a' := by group
  have : y * y'⁻¹ = 1 := eq_one_of_triv_ι hι (by rw [h2]; exact triv_mul (triv_inv ha) ha')
  exact mul_inv_eq_one.mp this

theorem blocks_of_away {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {M : Mx D (n + n) (n + n)}
    (hM : ∀ τ', τ' ≠ τ → compAt θ τ' M = 1) (hMf : M.map (finPart D) = 1) {α β γ δ : Matrix (Fin n) (Fin n) ℂ}
    (hτ : compAt θ τ M = blk4 α β γ δ) :
    ∃ A B C E' : Mx D n n, M = blk4 A B C E' ∧ compAt θ τ A = α ∧ compAt θ τ B = β ∧ compAt θ τ C = γ ∧
      compAt θ τ E' = δ ∧ (∀ τ', τ' ≠ τ → compAt θ τ' A = 1 ∧ compAt θ τ' B = 0 ∧ compAt θ τ' C = 0 ∧ compAt θ τ' E' = 1) ∧
      A.map (finPart D) = 1 ∧ B.map (finPart D) = 0 ∧ C.map (finPart D) = 0 ∧ E'.map (finPart D) = 1 := by
  obtain ⟨B, E', hBE⟩ := GlobalTheory.CompanionTheory.SwUnf.SmallCell.exists_blocks M
  set A := blkA M
  set C := GlobalTheory.CompanionTheory.SwUnf.lowerC M
  refine ⟨A, B, C, E', hBE, ?_⟩
  have h0 := hτ
  rw [hBE, component_block_matrix] at h0
  obtain ⟨e1, e2, e3, e4⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h0
  refine ⟨e1, e2, e3, e4, fun τ' hτ' => ?_, ?_⟩
  · have h1 := hM τ' hτ'
    rw [hBE, component_block_matrix, ← GlobalTheory.StdUnn.Model.block_matrix_one] at h1
    obtain ⟨f1, f2, f3, f4⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h1
    exact ⟨f1, f2, f3, f4⟩
  · have h1 := hMf
    rw [hBE, GlobalTheory.StdUnn.Frame.block_matrix_map, ← GlobalTheory.StdUnn.Model.block_matrix_one] at h1
    obtain ⟨f1, f2, f3, f4⟩ := GlobalTheory.StdUnn.Model.blockMatrixTwoByTwoFin_injective h1
    exact ⟨f1, f2, f3, f4⟩

theorem eq_of_comps {θ : InfFam D} {τ : D.what₂.Tau} (hθ : IsInfFam θ) {X Y : Mx D n n} (hτ : compAt θ τ X = compAt θ τ Y)
    (hτ' : ∀ τ', τ' ≠ τ → compAt θ τ' X = compAt θ τ' Y) (hf : X.map (finPart D) = Y.map (finPart D)) : X = Y := by
  refine mx_ext hθ (fun τ'' => ?_) hf
  by_cases h : τ'' = τ
  · subst h; exact hτ
  · exact hτ' τ'' h

end PositivityTheory.Rg.Sw.Glob.AW
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayFactPf
section
namespace PositivityTheory.Rg.Sw.Glob

theorem awayFact_of (hA : AwayAct) (hD : DecompAway) : AwayFact := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC g
  have hθι : Formalism.L2.Theta.IsInfFam θ ∧ IsPlaceEmb θ τ ι := by
    obtain ⟨-, -, -, hθ, -, -, -, -, -, -, -, -, -, hι, -⟩ := hC
    exact ⟨hθ, hι⟩
  obtain ⟨x, y, hx, hg, -⟩ := hD D n θ τ ι hθι.1 hθι.2 g
  obtain ⟨A, hA'⟩ := hA D n V ψ χ θ μ ω H l s ν τ ε fr ι hC x hx
  exact ⟨x, y, hg, fun Ψ hΨ => ⟨A Ψ, (hA' Ψ hΨ).1, fun S hS => (hA' Ψ hΨ).2 (⇑S) ⟨S, rfl⟩⟩⟩

end PositivityTheory.Rg.Sw.Glob
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.ContinuousKer
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.FTH

open PositivityTheory.Rg.Sw.Glob.FTP
open Classical

variable {D : D7} {n m : ℕ}

theorem norm_ker (ε : Fin m → Bool) (t : ℝ) (v u : Fin m → Fin n → ℂ) : ‖ker ε t v u‖ = 1 := by
  unfold ker
  rw [show Complex.I * ((2 * t : ℝ) : ℂ) * ((((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℝ) : ℂ) =
      ((2 * t * ((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u).trace.re : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_ker (ε : Fin m → Bool) (t : ℝ) (v : Fin m → Fin n → ℂ) : Continuous (ker ε t v) := by
  unfold ker
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp ?_)))
  have h2 : Continuous fun u : Fin m → Fin n → ℂ => Matrix.of u := continuous_id
  have h : Continuous fun u : Fin m → Fin n → ℂ => ((Matrix.of v)ᴴ * Matrix.diagonal (sgn ε) * Matrix.of u) :=
    continuous_const.matrix_mul h2
  exact h.matrix_trace

def Aw (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (θ : InfFam D) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (μ : Measure (Mx D V.rank n)) (Ψ : Mx D V.rank n → ℂ) :
    Mx D V.rank n → ℂ :=
  fun x => kap μ (piF θ τ fr) (Bw ψ V θ τ fr Ψ x)

set_option synthInstance.maxHeartbeats 400000 in

theorem weyl_tens {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {l : D.what₂.Tau → ℝ} (hl : HasRealPar ψ θ l) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsTauFrame V τ s ε fr) {χ : (AE D)ˣ →* Circle}
    (μ : Measure (Mx D V.rank n)) [μ.IsAddHaarMeasure] {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)}
    (hω : IsWeilSch ψ χ θ V μ ω) (w : G D n) (hw : mat w = blk4 0 1 (-1) 0) (Ψ : Mx D V.rank n → ℂ)
    (hΨ : AwayCls θ τ fr Ψ) (f : (Fin V.rank → Fin n → ℂ) → ℂ) (hf : IsSch f) :
    (ω w ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 =
      tens θ τ fr (fun u => 1 * ftLoc ε (tLoc l τ) f u) (Aw ψ V θ τ fr μ Ψ) := by
  funext x
  rw [hω.weyl w hw]
  have e1 : ∀ y, (⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩ : schwartzA θ V.rank n).1 y * ψ (trA (Matrix.trace (inner V x y))) =
      (fun u => f u * ker ε (tLoc l τ) (piF θ τ fr x) u) (piF θ τ fr y) * Bw ψ V θ τ fr Ψ x y :=
    fun y => integrand_eq hθ hl hfr f Ψ x y
  simp_rw [e1]
  obtain ⟨S, hS⟩ := hf
  have hfc : Continuous f := hS ▸ S.continuous
  obtain ⟨C, hC⟩ := sch_decay f ⟨S, hS⟩
  have hk := kap_spec hθ hfr.1 μ hΨ hψ x (fun u => f u * ker ε (tLoc l τ) (piF θ τ fr x) u)
    ((hfc.mul (continuous_ker ε (tLoc l τ) (piF θ τ fr x))).measurable)
    ⟨C, fun u => by rw [norm_mul, norm_ker, mul_one]; exact hC u⟩
  rw [hk]
  simp only [tens, Aw, ftLoc_eq_ker, one_mul]
  rw [mul_comm]
  rfl

end PositivityTheory.Rg.Sw.Glob.FTH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasCLMNbar
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct FourierTransform
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.OpCLMH

variable {D : D7} {n : ℕ}

def HasCLM {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ι : GR n →* G D n) (y : GR n) : Prop :=
  ∃ L : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℝ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ,
    ∀ Ψ (hΨ : AwayCls θ τ fr Ψ) (S : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ),
      (ω (ι y) ⟨tens θ τ fr S Ψ, hΨ.2 S ⟨S, rfl⟩⟩).1 = tens θ τ fr (L S) Ψ

theorem hasCLM_mul {θ : InfFam D} {V : HSp D} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {τ : D.what₂.Tau}
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n} {y₁ y₂ : GR n} (h₁ : HasCLM ω τ fr ι y₁)
    (h₂ : HasCLM ω τ fr ι y₂) : HasCLM ω τ fr ι (y₁ * y₂) := by
  obtain ⟨L₁, hL₁⟩ := h₁
  obtain ⟨L₂, hL₂⟩ := h₂
  refine ⟨L₁.comp L₂, fun Ψ hΨ S => ?_⟩
  have e2 : ω (ι y₂) ⟨tens θ τ fr S Ψ, hΨ.2 S ⟨S, rfl⟩⟩ = ⟨tens θ τ fr (L₂ S) Ψ, hΨ.2 _ ⟨L₂ S, rfl⟩⟩ :=
    Subtype.ext (hL₂ Ψ hΨ S)
  rw [map_mul, map_mul, Module.End.mul_apply, e2, hL₁ Ψ hΨ (L₂ S)]
  rfl

section Gens

variable {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} {H : G D n → ℝ≥0}
    {l : D.what₂.Tau → ℝ} {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ν : Measure (GA D V)}
    {τ : D.what₂.Tau} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ι : GR n →* G D n}

theorem hasCLM_n (hU : UnipTau) (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ)
    (hb : bᴴ = b) (hyb : mR y = nU b) : HasCLM ω τ fr ι y := by
  refine ⟨(SchwartzMap.smulLeftCLM ℂ
    (fun u : Fin V.rank → Fin n → ℂ => Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace))).restrictScalars ℝ,
    fun Ψ hΨ S => ?_⟩
  funext x
  rw [hU D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y b hb hyb]
  have key : ∀ u : Fin V.rank → Fin n → ℂ, (SchwartzMap.smulLeftCLM ℂ
      (fun u : Fin V.rank → Fin n → ℂ => Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace)) S) u =
      Complex.exp (Complex.I * (tLoc l τ : ℂ) * (b * gramX ε u).trace) * S u := fun u => by
    rw [SchwartzMap.smulLeftCLM_apply_apply (OpGenAH.hasTemperateGrowth_phase ε (tLoc l τ) b hb), smul_eq_mul]
  simp only [tens, ContinuousLinearMap.coe_restrictScalars']
  rw [key (fr⁻¹ * compAt θ τ x)]
  ring

theorem hasCLM_m (hLv : LeviTau) (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (y : GR n)
    (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) (hya : mR y = mM a) : HasCLM ω τ fr ι y := by
  obtain ⟨C, Am, hA1, hA2, hA3, hAf⟩ := hLv D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y a ha hya
  refine ⟨(C • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (OpGenAH.rmulEquiv (m := V.rank) a ha)).restrictScalars ℝ,
    fun Ψ hΨ S => ?_⟩
  funext x
  rw [hAf]
  have hx1 : compAt θ τ (HMul.hMul x Am : Mx D V.rank n) = compAt θ τ x * a := by
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA1]
  have hx2 : Ψ (HMul.hMul x Am : Mx D V.rank n) = Ψ x :=
    hΨ.1 _ _ (fun τ' h => by rw [GlobalTheory.AdForm.RatMove.compAt_mul, hA2 τ' h, Matrix.mul_one])
      (by rw [Matrix.map_mul, hA3, Matrix.mul_one])
  simp only [tens]
  rw [hx1, hx2]
  have hm : (fr⁻¹ * (compAt θ τ x * a) : Matrix (Fin V.rank) (Fin n) ℂ) =
      (Matrix.of (fr⁻¹ * compAt θ τ x) : Matrix (Fin V.rank) (Fin n) ℂ) * a := by
    rw [← Matrix.mul_assoc]
    rfl
  have e1 : (⇑S) (fr⁻¹ * (compAt θ τ x * a)) = S (Matrix.of (fr⁻¹ * compAt θ τ x) * a) := congrArg S hm
  rw [e1]
  change C * (S _ * Ψ x) = (C * S (OpGenAH.rmulEquiv (m := V.rank) a ha (fr⁻¹ * compAt θ τ x))) * Ψ x
  rw [mul_assoc]
  rfl

theorem hasCLM_nbar (hU : UnipTau) (hW : WEx) (hS : SchOps) (hF : FTfact) (hl0 : tLoc l τ ≠ 0)
    (hC : Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι) (y : GR n) (c : Matrix (Fin n) (Fin n) ℂ) (hc : cᴴ = c)
    (hyc : mR y = nbar c) : HasCLM ω τ fr ι y := by
  obtain ⟨κ, γ, hκ, -, -, hform⟩ := GenOpsH.gen_nbar hU hW hS hF hC y c hc hyc
  obtain ⟨c1, -, h1⟩ := FTD.ftLoc_eq (n := n) ε (tLoc l τ) hl0
  obtain ⟨c2, -, h2⟩ := FTD.ftLoc_eq (n := n) ε (-tLoc l τ) (neg_ne_zero.2 hl0)
  have hc' : (-c)ᴴ = -c := by rw [Matrix.conjTranspose_neg, hc]
  let FT1 : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℂ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ :=
    (κ * c1) • (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (FTD.Mt ε (tLoc l τ) hl0)).comp
      ((SchwartzMap.fourierTransformCLM ℂ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ FTD.Lc.symm))
  let FT2 : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℂ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ :=
    (κ⁻¹ * c2) • (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (FTD.Mt ε (-tLoc l τ) (neg_ne_zero.2 hl0))).comp
      ((SchwartzMap.fourierTransformCLM ℂ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ FTD.Lc.symm))
  let Em : SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ →L[ℂ] SchwartzMap (Fin V.rank → Fin n → ℂ) ℂ :=
    SchwartzMap.smulLeftCLM ℂ
      (fun u : Fin V.rank → Fin n → ℂ => Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u).trace))
  have hFT1 : ∀ S u, FT1 S u = κ * ftLoc ε (tLoc l τ) S u := by
    intro S u
    rw [h1]
    simp only [FT1, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Function.comp_apply, Pi.smul_apply,
      SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, SchwartzMap.fourierTransformCLM_apply,
      smul_eq_mul]
    push_cast
    ring
  have hFT2 : ∀ S u, FT2 S u = κ⁻¹ * ftLoc ε (-tLoc l τ) S u := by
    intro S u
    rw [h2]
    simp only [FT2, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Function.comp_apply, Pi.smul_apply,
      SchwartzMap.smul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, SchwartzMap.fourierTransformCLM_apply,
      smul_eq_mul]
    push_cast
    ring
  have hEm : ∀ S u, Em S u =
      Complex.exp (Complex.I * (tLoc l τ : ℂ) * ((-c) * gramX ε u).trace) * S u := by
    intro S u
    simp only [Em, SchwartzMap.smulLeftCLM_apply_apply (OpGenAH.hasTemperateGrowth_phase ε _ (-c) hc'), smul_eq_mul]
  refine ⟨(γ⁻¹ • FT1.comp (Em.comp FT2)).restrictScalars ℝ, fun Ψ hΨ S => ?_⟩
  rw [hform Ψ hΨ (⇑S) ⟨S, rfl⟩]
  congr 1
  funext u
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Function.comp_apply, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul, hFT1]
  congr 3
  funext v
  rw [hEm, hFT2]

end Gens

end PositivityTheory.Rg.Sw.Glob.OpCLMH

namespace PositivityTheory.Rg.Sw.Glob

theorem opCLM_of (hU : UnipTau) (hLv : LeviTau) (hW : WEx) (hS : SchOps) (hF : FTfact) (hD : Decomp) (hN : LNe) :
    OpCLM := by
  intro D n V ψ χ θ μ ω H l s ν τ ε fr ι hC y
  have hl0 : tLoc l τ ≠ 0 := by
    unfold tLoc
    exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (hN D ψ θ l hC.hψ hC.hθ hC.hl τ)
  obtain ⟨y₁, y₂, y₃, y₄, rfl, ⟨t, ht⟩, ⟨c, hc, hc'⟩, ⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hD n y
  have h1 : ((t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (t : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  exact OpCLMH.hasCLM_mul (OpCLMH.hasCLM_mul (OpCLMH.hasCLM_mul (OpCLMH.hasCLM_n hU hC y₁ _ h1 ht)
    (OpCLMH.hasCLM_nbar hU hW hS hF hl0 hC y₂ c hc hc')) (OpCLMH.hasCLM_m hLv hC y₃ a ha ha'))
    (OpCLMH.hasCLM_n hU hC y₄ b hb hb')

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocKvacB
section
noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn MvPolynomial
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem const_of_annS {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau}
    {s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {ε : Fin V.rank → Bool} {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hfr : IsTauFrame V τ s ε fr) (hM : ∀ τ, (gramAt D V τ * s τ).IsHermitian) (l : D.what₂.Tau → ℝ)
    (Q : PX V.rank n) (h : ∀ X, annS V l s θ τ X (tens θ τ fr (fP (cLoc l τ) Q) (psi0 θ V n l s τ)) = 0) :
    Q = C (evX Q 0) := by
  have hk : ∀ u W : Matrix (Fin V.rank) (Fin n) ℂ, ∑ k, ptX W k * eval (ptX u) (pderiv k Q) = 0 := by
    intro u W
    have e := congrFun (h (fr * W)) (xL θ τ (fr * u))
    rw [annS_tens hθ hfr hM l] at e
    have hinv : ∀ v : Matrix (Fin V.rank) (Fin n) ℂ, fr⁻¹ * (fr * v) = v := fun v => by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr.1, Matrix.one_mul]
    have hc : compAt θ τ (xL θ τ (fr * u)) = fr * u := by
      have := congrFun (compAt_xL hθ τ (fr * u)) τ
      simpa [dirAt_self] using this
    have hp : psi0 θ V n l s τ (xL θ τ (fr * u)) = 1 := by
      unfold psi0
      rw [compAt_xL hθ, gAway_dirAt, finPart_xL hθ]
      simp only [one_mul]
      exact gaussian_at_zero_eq_one D V.rank n
    rw [hc, hinv, hinv, hp, mul_one] at e
    exact (mul_eq_zero.1 e).resolve_right (gs_ne_zero _ _)
  have hconst : ∀ u : Matrix (Fin V.rank) (Fin n) ℂ, evX Q u = evX Q 0 := by
    intro u
    let F : ℝ → ℂ := fun t => eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u) Q
    have hF : ∀ t, HasDerivAt F 0 t := by
      intro t
      have hd := GlobalTheory.FockAnnKill.hasDerivAt_eval_line Q (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ)) (ptX u) t
      refine hd.congr_deriv ?_
      have e2 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • ptX u = ptX ((0 : Matrix (Fin V.rank) (Fin n) ℂ) + (t : ℂ) • u) :=
        (ptX_add_smul _ _ t).symm
      rw [e2]
      exact hk _ u
    have hdiff : Differentiable ℝ F := fun t => (hF t).differentiableAt
    have hc := is_const_of_deriv_eq_zero hdiff (fun t => (hF t).deriv) 1 0
    have e1 : F 1 = evX Q u := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((1 : ℝ) : ℂ) • ptX u) Q = eval (ptX u) Q
      rw [Complex.ofReal_one, one_smul]
      have e3 : ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ptX u = ptX u := by
        funext k
        obtain ⟨a, i, b⟩ := k
        cases b <;> simp [ptX]
      rw [e3]
    have e0 : F 0 = evX Q 0 := by
      show eval (ptX (0 : Matrix (Fin V.rank) (Fin n) ℂ) + ((0 : ℝ) : ℂ) • ptX u) Q = eval (ptX 0) Q
      rw [Complex.ofReal_zero, zero_smul, add_zero]
    rw [← e1, ← e0, hc]
  apply sub_eq_zero.1
  apply evX_eq_zero
  intro u
  show eval _ (Q - C (evX Q 0)) = 0
  rw [map_sub, eval_C]
  exact sub_eq_zero.2 (hconst u)

end PositivityTheory.Rg.Sw.Glob.RhoH
end
end

