import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0058
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0711
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisPhiFixedAddFinrankMonLe
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory

theorem finrank_dcris_phi_fixed_add_finrank_mon_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (V' : Type) [AddCommGroup V'] [Module ℚ_[l] V'] [FiniteDimensional ℚ_[l] V'] (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V') (m : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l]), IsDual1 (P.PD K) ρ ρ' m → IsSst P ρ → finrank ℚ_[l] ↥(Dcris (P.PD K) ρ' ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V') - LinearMap.id)) + finrank ℚ_[l] ↥((Dst P ρ).map (monV P ℚ_[l] V)) ≤ finrank ℚ_[l] ↥(Dst P ρ ⊓ ((Dst P ρ).map (monV P ℚ_[l] V)).comap ((l : ℚ_[l]) • phiV P ℚ_[l] V - LinearMap.id)) := by
  intro l _ P AI T K V _ _ _ V' _ _ _ ρ ρ' m hD hS
  obtain ⟨B, h1, h2, h3⟩ := GlobalTheory.T.exists_pairing_Dst_Dcris_frobenius_fixed l P AI T K V V' ρ ρ' m hD hS
  haveI := GlobalTheory.T.finiteDimensional_Dst_of_isSst' l P K V ρ hS
  refine GlobalTheory.T.finrank_add_finrank_le_finrank_inf_comap_sub_id' ℚ_[l] _ _ (Dst P ρ) ((Dst P ρ).map (monV P ℚ_[l] V))
    ((l : ℚ_[l]) • phiV P ℚ_[l] V) B ?_ ?_ ?_ ?_ h3
  · rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_Dst] at hx
    rw [mem_Dst]
    intro g
    rw [← Module.End.mul_apply, ← monV_stRep, Module.End.mul_apply, hx g]
  · intro x hx
    rw [mem_Dst] at hx ⊢
    intro g
    rw [LinearMap.smul_apply, map_smul, ← Module.End.mul_apply, ← phiV_stRep, Module.End.mul_apply,
      hx g]
  · rintro _ ⟨x, hx, rfl⟩ w
    exact h1 x hx w
  · intro x hx w
    exact h2 x hx w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockActionBasePolynomial
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters

theorem rename_fockGL_eq_C_mul_colAct : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ), WtIs Dw w a → ∀ (u : GLR D n) (P : PolF D m n), ∃ (s : ℂ) (g : {τ : D.host.E →+* ℂ // InPsi H τ} → GL (Fin n) ℂ), MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) (fockGL m w 1 u P) = MvPolynomial.C s * GlobalTheory.Harm.colAct ℂ _ Dw.p Dw.q (Fin n) g (MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) P) := by
  intro D H Dw m n hΨ hm w a hw u P
  subst hm
  refine ⟨(((detFam w.c u)⁻¹ : ℂˣ) : ℂ), fun t => u ((tauPsi hΨ).symm t), ?_⟩
  have key : (MvPolynomial.rename (fockVarEquiv Dw hΨ rfl)).comp (GlobalTheory.ExportSeries.fockSubst (m := Dw.p + Dw.q) w.p u) =
      (GlobalTheory.Harm.colSubst (p := Dw.p) (q := Dw.q) (fun t => (((u ((tauPsi hΨ).symm t))⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
        (fun t => ((u ((tauPsi hΨ).symm t) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))).comp
        (MvPolynomial.rename (fockVarEquiv Dw hΨ rfl)) := by
    refine MvPolynomial.algHom_ext fun v => ?_
    obtain ⟨ρ, i, b⟩ := v
    have hp := (hw ρ).1
    induction i using Fin.addCases with
    | left i =>
      have hi : ((Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q)) : ℕ) < w.p ρ := by simp [hp]
      simp only [AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, MvPolynomial.aeval_X, if_pos hi, map_sum, map_mul,
        MvPolynomial.rename_C, MvPolynomial.rename_X, ]
      simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, finCongr_refl, Equiv.refl_trans, Equiv.refl_apply,
        finSumFinEquiv_symm_apply_castAdd]
      erw [GlobalTheory.Harm.colSubst_X_xVar]
      simp [GlobalTheory.Harm.xForm_apply]
    | right j =>
      have hj : ¬ ((Fin.natAdd Dw.p j : Fin (Dw.p + Dw.q)) : ℕ) < w.p ρ := by simp [hp]
      simp only [AlgHom.comp_apply, GlobalTheory.ExportSeries.fockSubst, MvPolynomial.aeval_X, if_neg hj, map_sum, map_mul,
        MvPolynomial.rename_C, MvPolynomial.rename_X, ]
      simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, finCongr_refl, Equiv.refl_trans, Equiv.refl_apply,
        finSumFinEquiv_symm_apply_natAdd]
      erw [GlobalTheory.Harm.colSubst_X_yVar]
      simp [GlobalTheory.Harm.yForm_apply]
  have hB : GlobalTheory.ExportSeries.inBasis (1 : GLR D n) u = u := by simp [GlobalTheory.ExportSeries.inBasis]
  rw [GlobalTheory.ExportSeries.fockGL_apply, hB, map_smul, MvPolynomial.smul_eq_C_mul]
  congr 1
  exact DFunLike.congr_fun key P

end GlobalTheory.FockLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockDeltaBasePolynomial
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters

theorem fockVarEquiv_lt {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (ρ : D.what₂.Tau)
    (k : ℕ) (h : k < m) (hk : k < Dw.p) (c : Fin n) :
    fockVarEquiv Dw hΨ hm (ρ, ⟨k, h⟩, c) = (tauPsi hΨ ρ, Sum.inl ⟨k, hk⟩, c) := by
  simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, Equiv.trans_apply, Equiv.refl_apply]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  simp only
  rw [Equiv.symm_apply_eq]
  ext
  simp

theorem fockVarEquiv_ge {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (ρ : D.what₂.Tau)
    (k : ℕ) (h : Dw.p + k < m) (hk : k < Dw.q) (c : Fin n) :
    fockVarEquiv Dw hΨ hm (ρ, ⟨Dw.p + k, h⟩, c) = (tauPsi hΨ ρ, Sum.inr ⟨k, hk⟩, c) := by
  simp only [fockVarEquiv, Equiv.prodCongr_apply, Prod.map, Equiv.trans_apply, Equiv.refl_apply]
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  simp only
  rw [Equiv.symm_apply_eq]
  ext
  simp

end GlobalTheory.FockLetters

namespace GlobalTheory.FockLetters

theorem rename_minorPlus {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (hn : Dw.p + Dw.q ≤ n)
    (ρ : D.what₂.Tau) (i : Fin Dw.p) :
    MvPolynomial.rename (fockVarEquiv Dw hΨ hm) (minorPlus ρ (i.val + 1) : MvPolynomial (FVar D m n) ℂ) =
      GlobalTheory.Harm.xMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseCovec ℂ hn) := by
  rw [minorPlus, GlobalTheory.Harm.xMinor, AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext1 a b
  have ha := a.isLt; have hb := b.isLt; have hi := i.isLt
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
    GlobalTheory.Harm.baseCovec, GlobalTheory.Harm.xForm_single, varF]
  rw [dif_pos ⟨by omega, by omega⟩, MvPolynomial.rename_X, fockVarEquiv_lt Dw hΨ hm ρ _ _ (by omega)]
  rfl

theorem rename_minorMinus {D : D7} {H : Geo.Tor.Host D.host.E} (Dw : Datum H) {m n : ℕ}
    (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (hn : Dw.p + Dw.q ≤ n)
    (ρ : D.what₂.Tau) (i : Fin Dw.q) :
    MvPolynomial.rename (fockVarEquiv Dw hΨ hm) (minorMinus ρ Dw.p (i.val + 1) : MvPolynomial (FVar D m n) ℂ) =
      ((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : GlobalTheory.Harm.Poly ℂ _ Dw.p Dw.q (Fin n)) *
        GlobalTheory.Harm.yMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseVec ℂ hn) := by
  rw [minorMinus, GlobalTheory.Harm.yMinor, AlgHom.map_det, ← Matrix.det_permute']
  conv_lhs => rw [← Matrix.det_transpose]
  congr 1
  ext1 a b
  have ha := a.isLt; have hb := b.isLt; have hi := i.isLt
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.transpose_apply,
    Matrix.submatrix_apply, id, GlobalTheory.Harm.baseVec, GlobalTheory.Harm.yForm_single, varF]
  rw [dif_pos ⟨by omega, by omega⟩, MvPolynomial.rename_X, fockVarEquiv_ge Dw hΨ hm ρ _ _ (by omega)]
  refine congrArg MvPolynomial.X (Prod.ext rfl (Prod.ext rfl (Fin.ext ?_)))
  simp only [Fin.val_rev, Fin.val_castLE, Fin.revPerm_apply]
  omega

end GlobalTheory.FockLetters

namespace GlobalTheory.FockLetters

theorem rename_delta_eq_smul_basePoly : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ), WtIs Dw w a → ∀ (hn : Dw.p + Dw.q ≤ n), ∃ c : ℂ, MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) (w.delta m) = MvPolynomial.C c * GlobalTheory.Harm.basePoly ℂ hn (GlobalTheory.FockLetters.stepsX Dw a) (GlobalTheory.FockLetters.stepsY Dw a) := by
  intro D H Dw m n hΨ hm w a hw hn
  have hp : ∀ ρ, w.p ρ = Dw.p := fun ρ => (hw ρ).1
  have hq : ∀ ρ, w.q ρ = Dw.q := fun ρ => (hw ρ).2.1
  refine ⟨∏ ρ : D.what₂.Tau, ∏ i : Fin Dw.q,
    (((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : ℂ)) ^ stepsY Dw a (tauPsi hΨ ρ) i, ?_⟩
  rw [GlobalTheory.ExportSeries.Weight.delta, Datum.delta, map_prod, GlobalTheory.Harm.basePoly, GlobalTheory.Harm.minorProd, map_prod,
    ← (tauPsi hΨ).prod_comp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [deltaAt, hp ρ, hq ρ, map_mul, map_prod, map_prod, Finset.prod_range, Finset.prod_range]
  have hx : ∀ i : Fin Dw.p, MvPolynomial.rename (fockVarEquiv Dw hΨ hm)
      ((minorPlus ρ (i.val + 1) : MvPolynomial (FVar D m n) ℂ) ^
        (w.ap ρ i - if i.val + 1 < Dw.p then w.ap ρ (i.val + 1) else 0)) =
      GlobalTheory.Harm.xMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseCovec ℂ hn) ^ stepsX Dw a (tauPsi hΨ ρ) i := by
    intro i
    rw [map_pow, rename_minorPlus Dw hΨ hm hn ρ i]
    congr 1
    simp only [stepsX, GlobalTheory.Harm.diffOf, tauPsi_apply]
    rw [(hw ρ).2.2.1 i i.isLt]
    split_ifs with h1
    · rw [(hw ρ).2.2.1 _ h1]
    · rfl
  have hy : ∀ i : Fin Dw.q, MvPolynomial.rename (fockVarEquiv Dw hΨ hm)
      ((minorMinus ρ Dw.p (i.val + 1) : MvPolynomial (FVar D m n) ℂ) ^
        (w.am ρ i - if i.val + 1 < Dw.q then w.am ρ (i.val + 1) else 0)) =
      MvPolynomial.C ((((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : ℂ)) ^ stepsY Dw a (tauPsi hΨ ρ) i) *
        GlobalTheory.Harm.yMinor (tauPsi hΨ ρ) i (GlobalTheory.Harm.baseVec ℂ hn) ^ stepsY Dw a (tauPsi hΨ ρ) i := by
    intro i
    have he : (w.am ρ i - if i.val + 1 < Dw.q then w.am ρ (i.val + 1) else 0) = stepsY Dw a (tauPsi hΨ ρ) i := by
      simp only [stepsY, GlobalTheory.Harm.diffOf, tauPsi_apply]
      have e0 : ∀ j < Dw.q, a (ComplexEmbedding.conjugate (tauE D ρ), j) = w.am ρ j := (hw ρ).2.2.2
      rw [e0 i i.isLt]
      split_ifs with h1
      · rw [e0 _ h1]
      · rfl
    rw [map_pow, rename_minorMinus Dw hΨ hm hn ρ i, he, mul_pow, map_pow, map_intCast]
  simp only [hx, hy, Finset.prod_mul_distrib, map_prod]
  ring

end GlobalTheory.FockLetters
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicValueSpaceMapEqDualWeylModuleFunctio
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open MvPolynomial

namespace GlobalTheory.ExportSeries.Onto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {n : ℕ}

def coefLin (lam : D.what₂.Tau → DomWeight n) : Pol ℂ D.what₂.Tau n →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam F
  map_add' F G := by
    funext x
    simp only [coefFn, map_add, mul_add, Pi.add_apply]
  map_smul' c F := by
    funext x
    simp only [coefFn, smul_eq_C_mul, map_mul, eval₂Hom_C, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem coefFn_actP (lam : D.what₂.Tau → DomWeight n) (u : GLR D n) (F : Pol ℂ D.what₂.Tau n) (x : GLR D n) :
    coefFn (RingHom.id ℂ) lam (actP lam (invTrK u) F) x = coefFn (RingHom.id ℂ) lam F (u⁻¹ * x) := by
  have e1 : actP lam (invTrK u) F = detTwK lam (invTrK u) • trAct (invTrK u) F := rfl
  have e2 : (eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (x v.1).val v.2.1 v.2.2)).comp
        (trAct (invTrK u) : Pol ℂ D.what₂.Tau n →+* Pol ℂ D.what₂.Tau n) =
      eval₂Hom (RingHom.id ℂ) (fun v => ((u⁻¹ * x) v.1).val v.2.1 v.2.2) := by
    refine MvPolynomial.ringHom_ext (fun a => by simp [trAct, Formalism.GradedWeylDivisibility.blockAct]) fun v => ?_
    simp only [RingHom.comp_apply, RingHom.coe_coe, trAct, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, eval₂Hom_C,
      eval₂Hom_X', Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => rfl
  have e3 : (RingHom.id ℂ) (detTwK lam (invTrK u)) =
      ((detFam (fun τ => (lam τ).detShift) u⁻¹ : ℂˣ) : ℂ) := by
    simp only [detTwK, detPow, detFam, map_prod, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      map_zpow₀, GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    change (((u τ)⁻¹).valᵀ).det = _
    rw [det_transpose]
    rfl
  rw [coefFn, coefFn, e1, smul_eq_C_mul, map_mul, eval₂Hom_C, e3, ← e2, map_mul, Units.val_mul]
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  ring

theorem invTrK_invTrK (g : GLR D n) : invTrK (invTrK g) = g := by
  funext τ
  exact Units.ext rfl

theorem map_harm_eq (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (hw : w.Good) (hm : ∀ τ, w.p τ + w.q τ ≤ m) :
    (harm m w B).map (harmFn m w B) =
      Submodule.span ℂ {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} := by
  obtain ⟨s, hs⟩ := GlobalTheory.T.fockMinorProduct_eq_sign_dualWeylExtremalVector D m n w B hw hm
  have hs0 : ((s : ℤ) : ℂ) ≠ 0 := by exact_mod_cast s.ne_zero
  have h1 : {φ | ∃ F : VV ℂ w.lam, φ = coefFn (RingHom.id ℂ) w.lam (F : Pol ℂ D.what₂.Tau n)} =
      ((VV ℂ w.lam).map (coefLin w.lam) : Set (GLR D n → ℂ)) := by
    ext φ
    constructor
    · rintro ⟨F, rfl⟩
      exact ⟨F, F.2, rfl⟩
    · rintro ⟨F, hF, rfl⟩
      exact ⟨⟨F, hF⟩, rfl⟩
  have key : ∀ u : GLR D n, harmFn m w B (fockGL m w B u (w.delta m)) =
      ((s : ℤ) : ℂ) • coefLin w.lam (actP w.lam (invTrK (u * B)) (ten fun τ => extremal ℂ n (w.lam τ))) := fun u => by
    funext x
    rw [harmFn_fockGL, hs, Pi.smul_apply, smul_eq_mul]
    congr 1
    change _ = coefFn _ _ _ _
    rw [coefFn_actP, _root_.mul_inv_rev, mul_assoc]
  rw [h1, Submodule.span_eq, GlobalTheory.OrbitSpan.VV_eq_span_orbit, harm, Submodule.map_span, Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have h2 := key (invTrK g * B⁻¹)
    rw [inv_mul_cancel_right, invTrK_invTrK] at h2
    refine (Submodule.smul_mem_iff _ hs0).1 ?_
    beta_reduce
    rw [← h2]
    exact Submodule.subset_span ⟨_, ⟨_, rfl⟩, rfl⟩

end GlobalTheory.ExportSeries.Onto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAdjointChartBijectiveConjugateHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.ReadAdj

open GlobalTheory.AdelicLatMove

variable {D : D7}

theorem toEAf_onto : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem cF_cF (z : Formalism.IndefR.Datum.EAf D) : cF D (cF D z) = z := by
  obtain ⟨a, rfl⟩ := toEAf_onto z
  exact GlobalTheory.PlaceVec.cF_cF_toEAf a

theorem frMapAdj_smul_eq (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (a : AE D)
    (x : WO S T) : frMapAdj S T βS βT (a • x) = toEAf D (cA D a) • frMapAdj S T βS βT x := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq]
  have : (((a • x : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D (cA D a) • ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul, toEAf_cA]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_half (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) {e : AE D}
    {x : WO S T} (hx : IsHalf (cA D e) x) : toEAf D e • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
  conv_rhs => rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx]
  rw [frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA]

theorem frMapAdj_sub (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T) :
    frMapAdj S T βS βT (x - y) = frMapAdj S T βS βT x - frMapAdj S T βS βT y := by
  have h := GlobalTheory.PlaceVec.frMapAdj_add S T βS βT (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem frMapAdj_eq_zero (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) {x : WO S T}
    (h : frMapAdj S T βS βT x = 0) : x.map (toEAf D) = 0 := by
  have h1 := congrArg (fun N => (S.gram.map (eToEAf D) * βS.val) * N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))) h
  simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ βS.mul_inv
    (GlobalTheory.PlaceVec.gram_map_mul_inv S) βT.mul_inv (GlobalTheory.PlaceVec.gram_map_mul_inv T)] at h1
  ext i j
  have h2 := congrFun (congrFun h1 j) i
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply] at h2
  have h3 := congrArg (cF D) h2
  rw [cF_cF, map_zero] at h3
  simpa using h3

theorem phi_toEAf_idem {e : AE D} (he : e * e = e) {F : Type} [CommRing F] (φ : Formalism.IndefR.Datum.EAf D →+* F)
    (hker : ∀ z, φ z = 0 ↔ toEAf D e * z = 0) : φ (toEAf D e) = 1 := by
  have h : toEAf D e * (toEAf D e - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, he, sub_self]
  have := (hker _).2 h
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this

theorem finPart_eq_zero_of_toEAf {a : AE D} (h : toEAf D a = 0) : finPart D a = 0 :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective (by rw [map_zero]; exact h)

theorem gram_inv_map_mul (S : HSp D) : (S.gram⁻¹).map (eToEAf D) * S.gram.map (eToEAf D) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.PlaceVec.gram_map_mul_inv S)

theorem rdAdj_read : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D))
    (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)),
    Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι →
    (∀ m, ∃ x : WO S T, IsHalf (cA D e) x ∧ rdAdj S T βS βT φ x = m) ∧
    (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → rdAdj S T βS βT φ x = rdAdj S T βS βT φ x' → x = x') ∧
    (∀ x : WO S T, IsHalf (cA D e) x → (IsIntM (frMapAdj S T βS βT x) ↔
      ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v),
        rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))) ∧
    ∀ (x : WO S T) (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)), IsIntM (frMapAdj S T βS βT x) →
      rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) →
      (redM PP (frMapAdj S T βS βT x)).map ι = z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) := by
  intro D S T βS βT e PP v φ ι hI hL
  obtain ⟨hsurj, hker, hint, hred⟩ := hL
  have hs : IsSplitIdem D e := hI.1
  have hc : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  have h1 : φ (toEAf D e) = 1 := phi_toEAf_idem hs.1 φ hker
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    choose N hN using fun i j => hsurj (m i j)
    set Q : Matrix (Fin S.rank) (Fin T.rank) (Formalism.IndefR.Datum.EAf D) :=
      (S.gram.map (eToEAf D) * βS.val) * Matrix.of N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D)) with hQ
    choose w hw using fun (i : Fin T.rank) (j : Fin S.rank) => toEAf_onto (Q j i)
    set x' : WO S T := Matrix.of fun i j => cA D (w i j) with hx'
    have hfx : frMapAdj S T βS βT x' = Matrix.of N := by
      rw [GlobalTheory.PlaceVec.frMapAdj_eq]
      have hX : ((x'.map (toEAf D)).map (cF D))ᵀ = Q := by
        ext i j
        simp only [Matrix.transpose_apply, Matrix.map_apply, hx', Matrix.of_apply, toEAf_cA, cF_cF, hw]
      rw [hX, hQ]
      exact GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ (gram_inv_map_mul S) βS.inv_mul (gram_inv_map_mul T)
        βT.inv_mul
    refine ⟨cA D e • x', fun i j => ?_, ?_⟩
    · show cA D e * (cA D e * x' i j) = cA D e * x' i j
      rw [← mul_assoc, hc.1]
    · ext i j
      simp only [rdAdj, Matrix.map_apply, frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA, hfx, Matrix.smul_apply,
        smul_eq_mul, map_mul, Matrix.of_apply, hN]
      rw [show φ (toEAf D e) = 1 from h1, one_mul]
  · intro x x' hx hx' h
    have hd : IsHalf (cA D e) (x - x') := fun i j => by
      show cA D e * (x i j - x' i j) = x i j - x' i j
      rw [mul_sub, hx i j, hx' i j]
    have h0 : frMapAdj S T βS βT (x - x') = 0 := by
      ext i j
      have e1 := congrFun (congrFun h i) j
      simp only [rdAdj, Matrix.map_apply] at e1
      have e2 : φ (frMapAdj S T βS βT (x - x') i j) = 0 := by
        rw [frMapAdj_sub, Matrix.sub_apply, map_sub, e1, sub_self]
      have e3 := (hker _).1 e2
      have e4 := congrFun (congrFun (frMapAdj_half S T βS βT hd) i) j
      rw [Matrix.smul_apply, smul_eq_mul, e3] at e4
      rw [← e4, Matrix.zero_apply]
    have hf := frMapAdj_eq_zero S T βS βT h0
    have hinf := GlobalTheory.SplitScalar.half_fin hc hd
    ext i j
    refine sub_eq_zero.1 (GlobalTheory.SplitScalar.adele_ext ?_ ?_)
    · have := congrFun (congrFun hinf i) j
      rw [map_zero]; exact this
    · rw [map_zero]
      exact finPart_eq_zero_of_toEAf (congrFun (congrFun hf i) j)
  · intro x hx
    have hh := fun i j => congrFun (congrFun (frMapAdj_half S T βS βT hx) i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hh
    constructor
    · intro hI'
      refine ⟨Matrix.of fun i j => ⟨φ (frMapAdj S T βS βT x i j), (hint _).1 (by rw [hh i j]; exact hI' i j)⟩, ?_⟩
      ext i j
      rfl
    · rintro ⟨z, hz⟩ i j
      have e1 := congrFun (congrFun hz i) j
      simp only [rdAdj, Matrix.map_apply] at e1
      have e2 : φ (frMapAdj S T βS βT x i j) ∈ v.adicCompletionIntegers D.host.F := by
        rw [e1]; exact (z i j).2
      rw [← hh i j]
      exact (hint _).2 e2
  · intro x z hI' hz
    ext i j
    have e1 := congrFun (congrFun hz i) j
    simp only [rdAdj, Matrix.map_apply] at e1
    simp only [Matrix.map_apply, redM, dif_pos (hI' i j)]
    exact hred ⟨_, hI' i j⟩ (z i j) e1.symm

end GlobalTheory.DownLift.ReadAdj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubsetStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameMatrixReduction_eq_of_halfIdempotent_subset : ∀ {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {Pg Qa Qb : Finset (Pl D.host.E)}, PlacesOK Pg Qa → Qb ⊆ Qa → ∀ {x : WO S T}, IsHalf (halfIdem Pg Qa) x → IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapO S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT x) = redM PP (frMapAdj S T βS βT (halfIdem Pg Qb • x))) ∧ (∀ PP ∈ Qb, redM PP (frMapO S T βS βT x) = redM PP (frMapO S T βS βT (halfIdem Pg Qb • x))) := by
  first | exact @GlobalTheory.RedHalfDrop.redM_drop | exact GlobalTheory.RedHalfDrop.redM_drop | (intros; apply GlobalTheory.RedHalfDrop.redM_drop <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumLocalEulerFactorHeckeOperatorsStatement
section
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_localEulerFactor_heckeOperators : ∀ (Γ : Type) [Group Γ] (K : Subgroup Γ) (c : Γ →* Γ) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : Γ → ℂ) (B : Γ → (H →L[ℂ] H)) (S : ℝ), (∀ g, c (c g) = c g) → (∀ g k k', k ∈ K → k' ∈ K → a (k * g * k') = a g) → (∀ g k, k ∈ K → B (g * k) = B g) → (∀ g, ‖B g‖ ≤ 1) → (∀ C : Finset Γ, (∀ g ∈ C, c g = g ∧ g ∉ K) → (∀ g ∈ C, ∀ g' ∈ C, g⁻¹ * g' ∈ K → g = g') → ∑ g ∈ C, ‖a g‖ ≤ S) → (∀ α, c α = α → ∃ C, GlobalTheory.UpInj.DCRep c K α C) → (∀ α C, c α = α → GlobalTheory.UpInj.DCRep c K α C → ∀ γ, ∑ δ ∈ C, B (γ * δ) = B γ * ∑ δ ∈ C, B δ) → ∀ γ, HasSum (fun x : Γ ⧸ K.comap c => a (c (Quotient.out x)) • B (γ * c (Quotient.out x))) (B γ * ∑' x : Γ ⧸ K.comap c, a (c (Quotient.out x)) • B (c (Quotient.out x))) := by
  first | exact @GlobalTheory.UpInj.localSum_hasSum | exact GlobalTheory.UpInj.localSum_hasSum | (intros; apply GlobalTheory.UpInj.localSum_hasSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEpsilonTransportStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_epsilon_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle) (χ : kˣ →* ℂˣ) (χ' : k'ˣ →* ℂˣ) (e : ℂ), (∀ x, ψ' (i x) = ψ x) → (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → IsTateEps ψ χ e → IsTateEps ψ' χ' e := by
  first | exact @GlobalTheory.LocalFieldIso.isTateEps_transport | exact GlobalTheory.LocalFieldIso.isTateEps_transport | (intros; apply GlobalTheory.LocalFieldIso.isTateEps_transport <;> assumption)
end

