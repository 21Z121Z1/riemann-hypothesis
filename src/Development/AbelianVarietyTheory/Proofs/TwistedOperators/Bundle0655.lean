import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0629
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0630
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0647
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0648
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneLessEqTopBesselLevelPeriod
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {A B : HSp D} {c : ℕ}

theorem coreMat_iA {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iA = frameMat B A d.ι := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin 1) (Fin A.rank) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]

theorem coreMat_iB {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) :
    coreMat d h * (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)).iB = midCol d h := by
  refine (Matrix.submatrix_mul_equiv _ _ _ _ _).trans ?_
  show Matrix.fromCols (frameMat B A d.ι) (midCol d h) *
      Matrix.fromRows (0 : Matrix (Fin A.rank) (Fin 1) D.host.E) (1 : Matrix (Fin 1) (Fin 1) D.host.E) = _
  rw [Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]

theorem besselDecomposition_vector_eq {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1) (a : D.host.E) :
    (besDec d h).i₀ *ᵥ vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) (fun _ => a) =
      a • (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z := by
  show coreMat d h *ᵥ (_ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec, coreMat_iB]
  show midCol d h *ᵥ (fun _ : Fin 1 => a) = _
  funext k
  simp [midCol, Matrix.mulVec, dotProduct, HermitianOrthogonalExtensionData.besDat, mul_comm]

theorem ratV_smul' {n : ℕ} (a : D.host.E) (v : Fin n → D.host.E) : ratV (a • v) = incA D a • ratV v := by
  funext i
  simp [ratV]

section Diag

variable {S S₀ : HSp D} {σ : ℕ} (d1 : HypDec S S₀ σ) (l : Fin σ → D.host.E)

theorem diagI_mul (hl : ∀ a, l a ≠ 0) :
    (diagonal fun a => incA D (l a)) ⬝ (diagonal fun a => incA D (l a)⁻¹) = (1 : Mx D σ σ) := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a
  rw [← map_mul, mul_inv_cancel₀ (hl a), map_one]

theorem diagI_mul' (hl : ∀ a, l a ≠ 0) :
    (diagonal fun a => incA D (l a)⁻¹) ⬝ (diagonal fun a => incA D (l a)) = (1 : Mx D σ σ) := by
  rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a
  rw [← map_mul, inv_mul_cancel₀ (hl a), map_one]

variable (hl : ∀ a, l a ≠ 0)

theorem jX_diag : (diagDec d1 l hl).jX = d1.jX ⬝ diagonal fun a => incA D (l a) := by
  show rat (d1.e * diagonal l) = _
  rw [rat_mul]; congr 1; exact diagonal_map (map_zero _)

theorem pX_diag_jX : (diagDec d1 l hl).pX ⬝ d1.jX = diagonal fun a => incA D (l a)⁻¹ := by
  have e := (diagDec d1 l hl).pX_jX
  rw [jX_diag, ← Matrix.mul_assoc] at e
  calc (diagDec d1 l hl).pX ⬝ d1.jX
        = (diagDec d1 l hl).pX ⬝ d1.jX ⬝ (diagonal fun a => incA D (l a)) ⬝ (diagonal fun a => incA D (l a)⁻¹) := by
          rw [Matrix.mul_assoc ((diagDec d1 l hl).pX ⬝ d1.jX), diagI_mul l hl, Matrix.mul_one]
    _ = _ := by rw [e, Matrix.one_mul]

theorem blockX_diag (n : GA D S) (T : Mx D σ σ) (e1 : mt S n ⬝ d1.jX = d1.jX + d1.jX ⬝ T) :
    blockX (diagDec d1 l hl) n =
      1 + (diagonal fun a => incA D (l a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (l a)) := by
  rw [blockX, jX_diag, ← Matrix.mul_assoc (mt S n), e1, Matrix.add_mul, Matrix.mul_add]
  simp only [← Matrix.mul_assoc]
  rw [pX_diag_jX, diagI_mul' l hl]

theorem coefX_diag (n : GA D S) (z z₀ : Fin S₀.rank → D.host.E) (w : Fin S.rank → D.host.E) (a : D.host.E)
    (b : Fin σ → AE D) (hw : d1.i₀ *ᵥ z₀ = w) (hz : d1.i₀ *ᵥ z = a • w)
    (e2 : mt S n *ᵥ ratV w = ratV w + d1.jX *ᵥ b) :
    coefX (diagDec d1 l hl) z n = incA D a • ((diagonal fun a => incA D (l a)⁻¹) *ᵥ b) := by
  have hzs : (diagDec d1 l hl).j0 *ᵥ ratV z = incA D a • ratV w := by
    rw [HypDec.j0, ← ratV_mulVec]
    show ratV (d1.i₀ *ᵥ z) = _
    rw [hz, ratV_smul']
  have hw' : ratV w = (diagDec d1 l hl).j0 *ᵥ ratV z₀ := by
    rw [HypDec.j0, ← ratV_mulVec]
    show ratV w = ratV (d1.i₀ *ᵥ z₀)
    rw [hw]
  rw [coefX, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzs, Matrix.mulVec_smul, e2, Matrix.mulVec_smul,
    Matrix.mulVec_add, hw', Matrix.mulVec_mulVec, (diagDec d1 l hl).pX_j0, Matrix.zero_mulVec, zero_add,
    Matrix.mulVec_mulVec, pX_diag_jX]

end Diag

theorem incA_inv_mul_pow (i : ℕ) :
    incA D (D.host.xi0 ^ i)⁻¹ * incA D (D.host.xi0 ^ (i + 1)) = incA D D.host.xi0 := by
  rw [← map_mul, pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)), one_mul]

theorem up_sum {σ : ℕ} (T : Mx D σ σ) :
    upSum ((diagonal fun a => incA D (lam σ a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (lam σ a))) =
      ∑ i : Fin σ, ∑ j : Fin σ, if j.1 = i.1 + 1 then incA D D.host.xi0 * T i j else 0 := by
  simp only [upSum, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · have e := incA_inv_mul_pow (D := D) i
    rw [show lam (D := D) σ j = D.host.xi0 ^ ((i : ℕ) + 1) by rw [lam, hij],
      show lam (D := D) σ i = D.host.xi0 ^ (i : ℕ) from rfl]
    linear_combination T i j * e
  · rfl

theorem ell_sum {σ : ℕ} (b : Fin σ → AE D) :
    ell D σ ⬝ᵥ (incA D (D.host.xi0 ^ σ) • ((diagonal fun a => incA D (lam σ a)⁻¹) *ᵥ b)) =
      ∑ i : Fin σ, if i.1 + 1 = σ then incA D D.host.xi0 * b i else 0 := by
  simp only [ell, dotProduct, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have e := incA_inv_mul_pow (D := D) i
    rw [hi] at e
    calc (1 : AE D) * (incA D (D.host.xi0 ^ σ) * (incA D (lam σ i)⁻¹ * b i))
        = (incA D (D.host.xi0 ^ (i : ℕ))⁻¹ * incA D (D.host.xi0 ^ σ)) * b i := by
          rw [one_mul, ← mul_assoc, mul_comm (incA D (D.host.xi0 ^ σ))]; rfl
      _ = incA D D.host.xi0 * b i := by rw [e]
  · exact zero_mul _

theorem simpleSum_lam {σ : ℕ} (T : Mx D σ σ) (b : Fin σ → AE D) :
    upSum (1 + (diagonal fun a => incA D (lam σ a)⁻¹) ⬝ T ⬝ (diagonal fun a => incA D (lam σ a))) +
        ell D σ ⬝ᵥ (incA D (D.host.xi0 ^ σ) • ((diagonal fun a => incA D (lam σ a)⁻¹) *ᵥ b)) =
      GlobalTheory.BesselChar.superSum (fun _ => incA D D.host.xi0) T b := by
  rw [upSum_add, upSum_one, zero_add, up_sum, ell_sum]
  rfl

theorem psiBes_diag (ψ : AddChar (AF D.host.F) ℂ) {σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1)
    (n : GA D B) (hn : n ∈ NFlag B ((besDec d h).e * diagonal (lam σ))) :
    psiBes ψ (diagDec (besDec d h) (lam σ) (lam_ne σ)) 1
      (vecB (GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ) n =
      besChar ψ (d.besDat (neg_ne_zero.2 one_ne_zero) σ h) n := by
  have hn' : n ∈ NFlag B (besDec d h).e := (nFlag_diag _ (lam σ) (lam_ne σ)) ▸ hn
  obtain ⟨T, b, -, h1, h2⟩ : ∃ (T : Mx D σ σ) (b : Fin σ → AE D), GlobalTheory.BesselChar.StrictUp T ∧
      mt B n ⬝ (besDec d h).jX = (besDec d h).jX + (besDec d h).jX ⬝ T ∧
      mt B n *ᵥ ratV (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z =
        ratV (d.besDat (neg_ne_zero.2 one_ne_zero) σ h).z + (besDec d h).jX *ᵥ b :=
    GlobalTheory.BesselChar.exists_coords (d.besDat (neg_ne_zero.2 one_ne_zero) σ h) n hn'
  rw [GlobalTheory.BesselChar.besChar_eq ψ _ n T b h1 h2]
  rw [psiBes, simpleSum, blockX_diag _ _ _ n T h1,
    coefX_diag _ _ _ n _ _ _ _ b (by rw [besselDecomposition_vector_eq d h 1, one_smul]) (besselDecomposition_vector_eq d h _) h2,
    simpleSum_lam, map_one, one_mul, psiE]
  rfl

theorem integral_tr {S : HSp D} {N N' : Subgroup (GA D S)} (hN : N = N') (ν : Measure N) (𝓝 : Set N)
    (f : GA D S → ℂ) : ∫ n in trSet hN 𝓝, f n.1 ∂(trMeas hN ν) = ∫ n in 𝓝, f n.1 ∂ν := by
  subst hN
  rfl

end GlobalTheory.RowChain.TopPer

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem embA_top (G : GridData L sc) (h : GA D (G.V (.top 0))) :
    GlobalTheory.MixPer.embA (besDecAt G 0 ((D.R.m - 2) / 2) top_idx) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) h = embTop G h :=
  (embRel_iff _ h _).1 (GlobalTheory.CharLaws.embRel_embA _ _ _ (coreMat_iA _ _).symm h)

end GlobalTheory.RowChain.TopPer

namespace GlobalTheory.RowChain.TopPer

open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem embA_topLev (G : GridData L sc) {t : T} {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t) (h : GA D (G.V (.top 0))) :
    GlobalTheory.MixPer.embA (topLev G hM).d (topLev G hM).o h = embTop G h :=
  embA_top G h

theorem psiBes_topLev (G : GridData L sc) {t : T} {M : GlobalTheory.FunObj.Vol G} (hM : M.Is t) (ψ : AddChar (AF D.host.F) ℂ)
    (n : GA D (G.V (.grid D.R.m 0))) (hn : n ∈ flagN (topLev G hM).d) :
    psiBes ψ (topLev G hM).d 1 (vecB (topLev G hM).o (topLev G hM).ζ) n = besChar ψ G.besTop n :=
  psiBes_diag ψ (G.rowDec 0 (by have := D.R.two_le_m; omega)) (by have := top_idx (D := D); omega) n hn

theorem bplus_eq_topLev_per : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T)
    (M : GlobalTheory.FunObj.Vol G) (hM : M.Is t) (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)),
    Bplus Wl M φ F = (GlobalTheory.RowChain.topLev G hM).per Wl.ψ φ F := by
  intro D T L sc G Wl t M hM φ F
  have hN : NFlag (G.V (.grid D.R.m 0)) G.besTop.e = flagN (topLev G hM).d :=
    (nFlag_diag (rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2)
      (by have := top_idx (D := D); omega)).e (lam _) (lam_ne _)).symm
  have hper : (topLev G hM).per Wl.ψ φ F = ∫ h in M.fd (.top 0), ∫ n in trSet hN M.fdN,
      GlobalTheory.MixPer.besFun Wl.ψ 1 (topLev G hM).d (topLev G hM).o (topLev G hM).ζ φ F h n ∂(trMeas hN M.νN) ∂M.ν (.top 0) :=
    rfl
  rw [hper]
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  refine (integral_tr hN M.νN M.fdN fun g => φ h * F (g * embTop G h) * star (besChar Wl.ψ G.besTop g)).symm.trans ?_
  refine integral_congr_ae (ae_of_all _ fun n => ?_)
  show φ h * F (n.1 * embTop G h) * star (besChar Wl.ψ G.besTop n.1) =
    φ h * F ((show GA D (topLev G hM).V from n.1) * GlobalTheory.MixPer.embA (topLev G hM).d (topLev G hM).o h) *
      star (psiBes Wl.ψ (topLev G hM).d 1 (vecB (topLev G hM).o (topLev G hM).ζ) n.1)
  rw [embA_topLev G hM h, psiBes_topLev G hM Wl.ψ n.1 n.2]
  rfl

end GlobalTheory.RowChain.TopPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CastRealAll
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowReal
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefBase

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem rank_X (ch : Choice R) : (rowSizes D).nC (0 : Fin ((rowSizes D).m + 1)) = D.sp.X'.rank := by
  have h1 := rank_gridM ch.G (i := 0) (Nat.zero_le _)
  have h2 : (ch.G.V (.grid 0 D.R.m)) = (columnBlock R.toLevCh D.R.m).sp := rfl
  rw [h2, colY_m] at h1
  exact h1.symm

def xPt (ch : Choice R) (g : Gc D.what₂.Tau (rowSizes D)) : GA D D.sp.X' :=
  cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0)

theorem cast_realAll (θ : InfFam D) (n0 : ℕ) (hn : n0 = D.sp.X'.rank) (v : UG D.what₂.Tau n0) :
    ∀ (X : LSp D) (h : X = ⟨D.sp.X', R.toLevCh.ΛX⟩) (O : D.what₂.Tau → Matrix (Fin X.sp.rank) (Fin X.sp.rank) ℂ)
      (hO : HEq O (onb R.MX)) (e1 : n0 = X.sp.rank),
      cast (congrArg (fun X : LSp D => GA D X.sp) h)
        (realAll θ X.sp (fun τ => O τ * ((castU e1 (v τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) * (O τ)⁻¹)) =
      realAll θ D.sp.X' (fun τ => onb R.MX τ * ((castU hn (v τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
        (onb R.MX τ)⁻¹) := by
  intro X h
  subst h
  intro O hO e1
  cases eq_of_heq hO
  rfl

theorem xPt_eq (ch : Choice R) (hO : ch.W.Over R) (h0 : PosOnb ch.W (.grid 0 D.R.m)) (g : Gc D.what₂.Tau (rowSizes D)) :
    xPt ch g = realAll R.θ D.sp.X' (fun τ => GlobalTheory.DefLift.unfr R.MX τ
      ((castU (rank_X ch) (g.2 0 τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ)) := by
  unfold xPt
  have hk : ((kappa ch.W g).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp) =
      realAll ch.W.θ (columnBlock R.toLevCh D.R.m).sp (fun τ => ch.W.onb (.grid 0 D.R.m) τ *
        ((castU (rank_gridM ch.G (i := 0) (Nat.zero_le _)).symm (g.2 0 τ) : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
          (ch.W.onb (.grid 0 D.R.m) τ)⁻¹) := by
    exact vtxPt_eq h0 (colU ch.G 0 g)
  rw [hk]
  have e := cast_realAll (R := R) ch.W.θ _ (rank_X ch) (g.2 0) (columnBlock R.toLevCh D.R.m) (colY_m R.toLevCh)
    (ch.W.onb (.grid 0 D.R.m)) hO.onbX (rank_gridM ch.G (i := 0) (Nat.zero_le _)).symm
  refine e.trans ?_
  rw [hO.θ]
  congr 1
  funext τ
  unfold GlobalTheory.DefLift.unfr onb
  rw [Matrix.nonsing_inv_nonsing_inv _ (GlobalTheory.DefLift.fr_det R.MX τ)]

end GlobalTheory.CoefBase

namespace GlobalTheory.CoefBase

section Core

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} [DecidableEq D.what₂.Tau]

end Core

section Core2

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} [DecidableEq D.what₂.Tau]

theorem core (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ)
    (hθ : IsInfFam θ) (hp : GlobalTheory.DefLift.AllPlus M) (hc : c.Is) (hpr : IsDualPair θ M c pr) (lam : D.what₂.Tau → ℕ → ℤ)
    (hl : ∀ τ (i : Fin V.rank), (lam τ i : ℝ) = -(Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) (Fin.rev i)) :
    ∃ A : c.W ≃ₗ[ℂ] weylSub V.rank lam, ∀ (u : UG D.what₂.Tau V.rank) (w : c.W),
      A (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = weylRep V.rank lam u (A w) := by
  have hε : ∀ τ, M.ε τ = Formalism.MainNotions.S.allPos V.rank := fun τ => funext fun a => hp τ a
  have m := fun τ => GlobalTheory.CompactModel.model_allPos D V S M τ (hε τ)
  haveI : ∀ τ, FiniteDimensional ℂ (M.H τ) := fun τ => (m τ).1
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_perfectPairing_coefficientSpace_tensorModel D V S M θ c pr hθ hp hc hpr
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.weyl_kTypeTensor_eq_contragredient_translatesSpan D.what₂.Tau V.rank M.H M.σ M.lam lam (fun τ => (M.enum τ).1) (fun τ => (m τ).2.2.1) (fun τ => (m τ).2.2.2)
    (fun τ i => by rw [hl τ i, hε τ])
  haveI : FiniteDimensional ℂ (⨂[ℂ] τ, M.H τ) := inferInstance
  haveI : FiniteDimensional ℂ (Module.Dual ℂ (weylSub V.rank lam)) := Module.Finite.equiv Φ.symm
  haveI : FiniteDimensional ℂ (weylSub V.rank lam) := (Module.finite_dual_iff ℂ).1 this
  let ev := Module.evalEquiv ℂ (weylSub V.rank lam)
  refine ⟨(E.trans Φ.dualMap).trans ev.symm, fun u w => ?_⟩
  apply ev.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext φ
  rw [LinearEquiv.dualMap_apply, hE, LinearMap.comp_apply]
  have key : (PiTensorProduct.map fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) :
      M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) (Φ φ) = Φ ((weylRep V.rank lam).dual u⁻¹ φ) := (hΦ u⁻¹ φ).symm
  rw [key]
  obtain ⟨y, hy⟩ := ev.surjective (Φ.dualMap (E w))
  rw [← hy, LinearEquiv.symm_apply_apply]
  have h2 : E w (Φ ((weylRep V.rank lam).dual u⁻¹ φ)) = ev y ((weylRep V.rank lam).dual u⁻¹ φ) := by
    rw [hy]; rfl
  rw [h2]
  show ((weylRep V.rank lam).dual u⁻¹ φ) y = φ (weylRep V.rank lam u y)
  rw [Representation.dual_apply, inv_inv]
  rfl

end Core2

theorem weyl_cast {ι : Type} [Fintype ι] [DecidableEq ι] (n n' : ℕ) (h : n = n') (lam : ι → ℕ → ℤ) :
    ∃ e : weylSub (ι := ι) n lam ≃ₗ[ℂ] weylSub n' lam, ∀ u F,
      e (weylRep n lam u F) = weylRep n' lam (fun τ => castU h (u τ)) (e F) := by
  subst h
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem cast_inv : ∀ (X Y : LSp D) (h : X = Y) (a : GA D X.sp),
    cast (congrArg (fun X : LSp D => GA D X.sp) h) a⁻¹ = (cast (congrArg (fun X : LSp D => GA D X.sp) h) a)⁻¹ := by
  intro X Y h a
  subst h
  rfl

theorem xPt_inv (ch : Choice R) (g : Gc D.what₂.Tau (rowSizes D)) : xPt ch g⁻¹ = (xPt ch g)⁻¹ := by
  have hk : ((kappa ch.W g⁻¹).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp) =
      ((kappa ch.W g).2 0 : GA D (columnBlock R.toLevCh D.R.m).sp)⁻¹ :=
    congrArg (fun x => x.2 0) (map_inv (kappa ch.W) g)
  exact (congrArg (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh))) hk).trans
    (cast_inv (columnBlock R.toLevCh D.R.m) _ (colY_m R.toLevCh) ((kappa ch.W g).2 0))

theorem coefBase [DecidableEq D.what₂.Tau] (ch : Choice R) (hθ : R.models_inf) (hc : R.models_cX) (hpr : R.models_prX)
    (hO : ch.W.Over R) (h0 : PosOnb ch.W (.grid 0 D.R.m)) :
    ∃ B : Module.Dual ℂ (weylSub ((rowSizes D).nC (0 : Fin ((rowSizes D).m + 1))) (baseWt (rowEntries D ch.sc.cGap))) ≃ₗ[ℂ]
        Module.Dual ℂ R.cX.W,
      ∀ g φ, B ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) =
        B φ ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0))⁻¹ := by
  obtain ⟨A0, hA0⟩ := core R.MX R.θ R.cX R.prX hθ (GlobalTheory.DefiniteMult.allPlus_parB _ (Nat.sub_le _ _) _) hc hpr
    (baseWt (rowEntries D ch.sc.cGap)) (fun τ i => GlobalTheory.T.highestWeight_basePar_eq_neg_lowestKType D ch.sc.cGap R.MX τ i)
  obtain ⟨e, he⟩ := weyl_cast (ι := D.what₂.Tau) _ _ (rank_X ch) (baseWt (rowEntries D ch.sc.cGap))
  refine ⟨(A0.trans e.symm).dualMap, fun g φ => ?_⟩
  ext w
  show ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) (e.symm (A0 w)) = φ (e.symm (A0 (R.cX.ρ (xPt ch g)⁻¹ w)))
  rw [← xPt_inv, xPt_eq ch hO h0, hA0, Representation.dual_apply]
  have h1 := he (g⁻¹.2 0) (e.symm (A0 w))
  rw [LinearEquiv.apply_symm_apply] at h1
  rw [← h1, LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory.CoefBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainDownEqLiftAlongPath
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChainDown

open GlobalTheory.FunObj GlobalTheory.RowChain

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (M : GlobalTheory.FunObj.Vol G)

theorem pathLift_comp_split {X Y : Node} (p : Path T X Y) (F : Fn G X) : ∀ {Z : Node} (q : Path T Y Z) (d : PureT G (p.comp q)),
    liftP Wl M (p.comp q) d F = liftP Wl M q (splitFam q d).2 (liftP Wl M p (splitFam q d).1 F)
  | _, .nil, _ => rfl
  | _, .snoc a q, d => congrArg (liftA Wl M a d.2) (pathLift_comp_split p F q d.1)

variable {G} (t : T) (i : ℕ)

noncomputable def lowLift {N : ℕ} (g : ∀ j, j < N → Sch G (.down t i j)) :
    ∀ n, n ≤ N → Fn G (.grid i n) → Fn G (.grid i 0)
  | 0, _, F => F
  | n + 1, h, F => lowLift g n (Nat.le_of_succ_le h) (liftA Wl M (.down t i n) (g n h) F)

theorem lowLift_congr {N N' : ℕ} (g : ∀ j, j < N → Sch G (.down t i j)) (g' : ∀ j, j < N' → Sch G (.down t i j)) :
    ∀ n (h : n ≤ N) (h' : n ≤ N'), (∀ j (hj : j < n), g j (by omega) = g' j (by omega)) →
      ∀ F, lowLift Wl M t i g n h F = lowLift Wl M t i g' n h' F
  | 0, _, _, _, _ => rfl
  | n + 1, h, h', hg, F => by
    show lowLift Wl M t i g n _ (liftA Wl M (.down t i n) (g n h) F) = lowLift Wl M t i g' n _ (liftA Wl M (.down t i n) (g' n h') F)
    rw [hg n (Nat.lt_succ_self n)]
    exact lowLift_congr g g' n _ _ (fun j hj => hg j (by omega)) _

theorem pathLift_downPath : ∀ n (d : PureT G (downPath t i n)) (F : Fn G (.grid i n)),
    liftP Wl M (downPath t i n) d F = lowLift Wl M t i (getD t i n d) n le_rfl F
  | 0, _, _ => rfl
  | n + 1, d, F => by
    have e := pathLift_comp_split G Wl M (Path.one (.down t i n)) F (downPath t i n) d
    refine e.trans ?_
    rw [pathLift_downPath n]
    show _ = lowLift Wl M t i (getD t i (n + 1) d) n _ (liftA Wl M (.down t i n) (getD t i (n + 1) d n (Nat.lt_succ_self n)) F)
    have hx : getD t i (n + 1) d n (Nat.lt_succ_self n) =
        (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).1.2 := by
      rw [getD, dif_neg (lt_irrefl n)]
    rw [hx]
    refine lowLift_congr Wl M t i _ _ n _ _ (fun j hj => ?_) _
    show _ = getD t i (n + 1) d j _
    rw [getD, dif_pos hj]

def castFn {n n' : ℕ} (e : n = n') (F : Fn G (.grid i n)) : Fn G (.grid i n') :=
  Eq.rec (motive := fun k _ => Fn G (.grid i k)) F e

theorem lowLift_two {N : ℕ} (g : ∀ j, j < N → Sch G (.down t i j)) (j n : ℕ) (hn : n ≤ N) (e : j + 1 + 1 = n)
    (F : Fn G (.grid i n)) :
    lowLift Wl M t i g n hn F = lowLift Wl M t i g j (by omega)
      (liftA Wl M (.down t i j) (g j (by omega)) (liftA Wl M (.down t i (j + 1)) (g (j + 1) (by omega)) (castFn i e.symm F))) := by
  subst e
  rfl

theorem castLift (j n : ℕ) (e : j + 1 + 1 = n) (f : Sch G (.down t D.R.m (j + 1))) (F : Fn G (.grid D.R.m n)) :
    GlobalTheory.MixPer.liftS (castOm G e (Wl.om (.mu t D.R.m (j + 1)))) (M.ν (.grid D.R.m n)) (M.fd (.grid D.R.m n)) F (castSch G e f) =
      liftA Wl M (.down t D.R.m (j + 1)) f (castFn D.R.m e.symm F) := by
  subst e
  rfl

variable {t M}

theorem chainFrom_down (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (F : Fn G (.grid D.R.m D.R.m)) :
    ∀ σ j (hj : j + 2 * σ + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j σ hj)),
      lowLift Wl M t D.R.m (getD t D.R.m D.R.m d) D.R.m le_rfl F = lowLift Wl M t D.R.m (getD t D.R.m D.R.m d) j (by omega)
        ((chainFrom G Wl t hM σ j hj vN).down (dataFrom G Wl t hM d σ j hj vN) F)
  | 0, j, hj, vN => by
    rw [lowLift_two Wl M t _ _ j D.R.m le_rfl (by omega) F,
      ← castLift Wl M t j D.R.m (by omega) (getD t D.R.m D.R.m d (j + 1) (by omega)) F]
    rfl
  | σ + 1, j, hj, vN =>
    (chainFrom_down hM d F σ (j + 1 + 1) (by omega) _).trans
      ((lowLift_two Wl M t D.R.m (getD t D.R.m D.R.m d) j (j + 1 + 1) (by omega) rfl _).trans rfl)

end GlobalTheory.RowChainDown

namespace GlobalTheory.RowChainDown

open GlobalTheory.FunObj GlobalTheory.RowChain

theorem chain_down_eq_liftP : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : GlobalTheory.FunObj.Vol G)
    (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (F : Fn G (.grid D.R.m D.R.m)),
    (GlobalTheory.RowChain.chain G Wl t hM).down (GlobalTheory.RowChain.chainData G Wl t hM d) F = liftP Wl M (downPath t D.R.m D.R.m) d F := fun G Wl t M hM d F => by
  show (chainFrom G Wl t hM _ 0 top_idx (topVN hM)).down (dataFrom G Wl t hM d _ 0 top_idx (topVN hM)) F = _
  rw [pathLift_downPath]
  exact (chainFrom_down Wl hM d F _ 0 top_idx (topVN hM)).symm

end GlobalTheory.RowChainDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClosedParabolicSubgroupsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closed_parabolic_subgroups : GlobalTheory.Published.DiscreteSeriesCoefficientsCuspidal → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v a : ∀ τ, M.H τ), (∀ τ, v τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → (∀ τ, a τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → ∀ (τ : D.what₂.Tau) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → ∃ P Q : Subgroup (NI V C), IsClosed (P : Set (NI V C)) ∧ IsClosed (Q : Set (NI V C)) ∧ (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) ∧ (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) ∧ (∀ h, h ∈ P → h ∈ Q → h = 1) ∧ ∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∀ x y : GA D V, ∫ p, coef θ M K v a (x * (((p : NI V C) * q : NI V C) : GA D V) * y) ∂ν = 0 := by
  first | exact @GlobalTheory.FibreAtTau.fibre_integral_eq_zero | exact GlobalTheory.FibreAtTau.fibre_integral_eq_zero | (intros; apply GlobalTheory.FibreAtTau.fibre_integral_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestGridArrowsVacuaIntertwinersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_testGrid_arrows_vacua_intertwiners : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∃ X ωT vacT ItT ωC vacC ItC dn ItU vC, (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsArrows ∧ (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsData ∧ ArrAgree (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) W := by
  first | exact @GlobalTheory.GridJoin.exists_arrows | exact GlobalTheory.GridJoin.exists_arrows | (intros; apply GlobalTheory.GridJoin.exists_arrows <;> assumption)
end

