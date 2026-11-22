import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0530
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0529
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0405
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationOperatorReading
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem fmR_coordX_self {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank) :
    fmR A B (Formalism.L2.Ker.coordX l) l.1 = unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  rw [Finset.sum_eq_single l.2.1, Finset.sum_eq_single l.2.2]
  · simp; rfl
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; simp [hi]
  · simp

theorem fmR_coordX_ne {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (τ' : D.what₂.Tau) (h : τ' ≠ l.1) : fmR A B (Formalism.L2.Ker.coordX l) τ' = 0 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp [h]; rfl

theorem fmR_I_coordX_self {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank) :
    fmR A B (I • Formalism.L2.Ker.coordX l) l.1 =
      cplxO (A.cart l.1) (B.cart l.1) (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2) := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  rw [Finset.sum_eq_single l.2.1, Finset.sum_eq_single l.2.2]
  · simp; rfl
  · intro j _ hj; simp [hj]
  · simp
  · intro i _ hi; refine Finset.sum_eq_zero fun j _ => ?_; simp [hi]
  · simp

theorem fmR_I_coordX_ne {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (τ' : D.what₂.Tau) (h : τ' ≠ l.1) : fmR A B (I • Formalism.L2.Ker.coordX l) τ' = 0 := by
  unfold fmR fockMat Formalism.L2.Ker.coordX
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  simp [h]; rfl

theorem gq_add_smul {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) (z e : VCx ι a b) (t : ℝ) :
    gq c (z + t • e) = gq c z + t * gD c z e + t ^ 2 * gq c e := by
  have key : ∀ (k : ℝ) (p q : ℂ), k * ‖p + t • q‖ ^ 2 =
      k * ‖p‖ ^ 2 + t * (2 * (k * (p * conj q).re)) + t ^ 2 * (k * ‖q‖ ^ 2) := by
    intro k p q
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  unfold gq gD
  simp only [Pi.add_apply, Pi.smul_apply, key, Finset.sum_add_distrib, Finset.mul_sum]

theorem heisO_eq_exp_rd (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) {S T : HSp D}
    (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (w : VCx D.what₂.Tau S.rank T.rank) :
    heisO ψ S T (fockPt σ A B w) h x = Complex.exp (-((gq (fw D) w : ℂ) / 2)) * rd ψ σ A B h x w := by
  unfold rd
  rw [Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf
  simp

theorem heis_dRho_fock_eval (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D)
    (hψ : IsStdChar D ψ (-1)) (hC : GlobalTheory.FockCompare.Chart θ σ) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S)
    (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (z e : VCx D.what₂.Tau S.rank T.rank) (τ : D.what₂.Tau)
    (v : Matrix (Fin T.rank) (Fin S.rank) ℂ) (hv : fmR A B e τ = v) (h0 : ∀ τ', τ' ≠ τ → fmR A B e τ' = 0)
    (hd : DifferentiableAt ℝ (rd ψ σ A B h x) z) :
    heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ v h) x =
      Complex.exp (-((gq (fw D) z : ℂ) / 2)) *
        ((-((Real.pi : ℂ) * I) * (omF A B z e : ℂ) - (gD (fw D) z e : ℂ) / 2) * rd ψ σ A B h x z +
          fderiv ℝ (rd ψ σ A B h x) z e) := by
  rw [heis_dRho_fock D ψ θ σ hψ hC S T A B h x z e τ v hv h0]
  have hfun : (fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * I) * ((t * omF A B z e : ℝ) : ℂ)) *
      heisO ψ S T (fockPt σ A B (z + t • e)) h x) = fun t : ℝ =>
      Complex.exp (-((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) - ((gq (fw D) z : ℂ) +
        (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2) * rd ψ σ A B h x (z + t • e) := by
    funext t
    rw [heisO_eq_exp_rd, gq_add_smul, ← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hfun]
  have hline : HasDerivAt (fun t : ℝ => z + t • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
  have hRd : HasDerivAt (fun t : ℝ => rd ψ σ A B h x (z + t • e)) (fderiv ℝ (rd ψ σ A B h x) z e) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    exact this
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hP : HasDerivAt (fun t : ℝ => -((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) - ((gq (fw D) z : ℂ) +
        (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2)
      (-((Real.pi : ℂ) * I) * (omF A B z e : ℂ) - (gD (fw D) z e : ℂ) / 2) 0 := by
    have h1 := (hid.mul_const (omF A B z e : ℂ)).const_mul (-((Real.pi : ℂ) * I))
    have h2 := ((hid.mul_const (gD (fw D) z e : ℂ)).const_add (gq (fw D) z : ℂ)).add
      ((hid.pow 2).mul_const (gq (fw D) e : ℂ))
    have h3 := h1.sub (h2.div_const 2)
    convert h3 using 1
    all_goals first | rfl | (funext t; rfl) | simp
  have hD : HasDerivAt (fun t : ℝ => Complex.exp (-((Real.pi : ℂ) * I) * ((t : ℂ) * (omF A B z e : ℂ)) -
      ((gq (fw D) z : ℂ) + (t : ℂ) * (gD (fw D) z e : ℂ) + (t : ℂ) ^ 2 * (gq (fw D) e : ℂ)) / 2) *
        rd ψ σ A B h x (z + t • e)) _ 0 := hP.cexp.mul hRd
  rw [hD.deriv]
  simp
  ring

theorem rd_aPlusAll : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), IsStdChar D ψ (-1) → GlobalTheory.FockCompare.Chart θ σ → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (h : WO S T → ℂ) (x : WO S T) (l : FVar D T.rank S.rank) (z : VCx D.what₂.Tau S.rank T.rank), DifferentiableAt ℝ (rd ψ σ A B h x) z → rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z = (2 / (fockScale D l.1 : ℂ)) * GlobalTheory.FockTransl.Jet.crOp A B l (rd ψ σ A B h x) z := by
  intro D ψ θ σ hψ hC S T A B h x l z hd
  have h1 := heis_dRho_fock_eval D ψ θ σ hψ hC S T A B h x z (Formalism.L2.Ker.coordX l) l.1 _
    (fmR_coordX_self A B l) (fmR_coordX_ne A B l) hd
  have h2 := heis_dRho_fock_eval D ψ θ σ hψ hC S T A B h x z (I • Formalism.L2.Ker.coordX l) l.1 _
    (fmR_I_coordX_self A B l) (fmR_I_coordX_ne A B l) hd
  have hlin : heisO ψ S T (fockPt σ A B z)
      (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x =
      (fockScale D l.1 : ℂ)⁻¹ *
        (heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ l.1
            (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2) h) x -
          I * heisO ψ S T (fockPt σ A B z) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ l.1
            (cplxO (A.cart l.1) (B.cart l.1) (unitMap (A.onb l.1) (B.onb l.1) l.2.1 l.2.2)) h) x) := by
    simp only [aPlusAll, aPlus, crea, heisO, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hexp : (Real.exp (gq (fw D) z / 2) : ℂ) * Complex.exp (-((gq (fw D) z : ℂ) / 2)) = 1 := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    push_cast
    simp
  have hrd : rd ψ σ A B (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x z =
      (Real.exp (gq (fw D) z / 2) : ℂ) * heisO ψ S T (fockPt σ A B z)
        (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb l h) x := rfl
  rw [hrd, hlin, h1, h2]
  unfold crOp lamF
  linear_combination (↑(fockScale D l.1))⁻¹ *
    ((-((Real.pi : ℂ) * I) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ) - (gD (fw D) z (Formalism.L2.Ker.coordX l) : ℂ) / 2) *
        rd ψ σ A B h x z + fderiv ℝ (rd ψ σ A B h x) z (Formalism.L2.Ker.coordX l) -
      I * ((-((Real.pi : ℂ) * I) * (omF A B z (I • Formalism.L2.Ker.coordX l) : ℂ) -
        (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ) / 2) * rd ψ σ A B h x z +
        fderiv ℝ (rd ψ σ A B h x) z (I • Formalism.L2.Ker.coordX l))) * hexp +
    (↑(fockScale D l.1))⁻¹ * (Real.pi : ℂ) * (omF A B z (I • Formalism.L2.Ker.coordX l) : ℂ) * rd ψ σ A B h x z * I_sq

end GlobalTheory.FockTransl.Jet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuumEquationsTransferSchroedingerDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.VacTransfer

set_option maxHeartbeats 800000 in

theorem exists_darboux_cS : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∃ (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) (Fin S.rank × Fin d)),
        ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹) ∧
        (∀ x : Matrix (Fin X.rank) (Fin S.rank) D.host.E, ∃ y z : Fin S.rank × Fin d → D.host.F,
          co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
            (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) ∧
        ∀ u, co.e (cS u) = M.co.e u := by
  intro D ψ θ _ ε S X A B d e Bs _ _ Vs Ws r s r' s' hJ hJW hV _ _ M hM cS hc
  obtain ⟨G, hGdef⟩ : ∃ G : Matrix (Fin S.rank) (Fin S.rank) D.host.E,
    (if ε then -1 else 1 : D.host.E) • S.gram = G := ⟨_, rfl⟩
  rw [hGdef] at hc
  have hs : (sgn ε S).gram = G := by
    rw [← hGdef]
    cases ε
    · simp [sgn]
    · ext i j; simp [HSpace.gram]
  have hVJ : Vs.J = -G := by
    rw [hJ, ← hGdef]; cases ε <;> simp
  have hdet : IsUnit G.det := by rw [← hs]; exact (Formalism.L2.Theta.gram_det_ne (sgn ε S)).isUnit
  have hHG : (G⁻¹).map (incA D) * G.map (incA D) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG : (G.map (incA D)).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = (G.map (incA D))ᵀ := by
    ext i j
    have h := hV.herm j i
    rw [hVJ, Matrix.neg_apply, Matrix.neg_apply, map_neg, neg_inj] at h
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig (incA D (G i j)) = incA D (G j i)
    rw [← h]
    rfl
  obtain ⟨co, hco⟩ := exists_darboux_transpose_mul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) e (X.gram.map (incA D))
    (incA D D.host.xi0) hHG hG (JV := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Vs.J) (JW := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Ws.J)
    (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F X.gramᵀ)
    (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • (sgn ε S).gram⁻¹))
    (by rw [hVJ]; exact Matrix.map_neg _ (map_neg (incA D)) _) (by rw [hJW]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) rfl
    (by rw [hs]; exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul _ _) M.co cS hc
  refine ⟨1, D.host.xi0 • (sgn ε S).gram⁻¹, co, one_smul _ _, fun x => ?_, hco⟩
  obtain ⟨y, z, h⟩ := hM.rat ((x * G⁻¹)ᵀ.submatrix id e.symm)
  refine ⟨y, z, Eq.trans ?_ h⟩
  rw [← hco, hc]
  congr 1
  exact (map_transpose_inv_mul (incA D) e x hdet).symm

theorem vacDatum_transfer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (ε : Bool) (S X : HSp D) (A : Fr S) (B : Fr X) {d : ℕ} (e : Fin X.rank ≃ Fin d)
      (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig → Bs.ψ = ψ →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E S.rank) (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (r s r' s' : ℕ)
      (hJ : Vs.J = (if ε then 1 else -1 : D.host.E) • S.gram) (hJW : Ws.J = D.host.xi0 • reindex e e X.gramᵀ),
      Vs.IsHerm D.sp.cm.sig Bs r s → Ws.IsSkew D.sp.cm.sig Bs r' s' →
      (∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ Vs.θ w = (if ε then 1 else -1 : ℂ) • A.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ)) →
    ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Vs Ws, M.IsGood Bs.ψ →
    ∀ cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X,
      (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((if ε then -1 else 1 : D.host.E) • S.gram)) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
      ∀ (f : WO S X → ℂ) (Φ : (Fin S.rank × Fin d → AF D.host.F) → ℂ), IsFinF ψ θ ε A B f → IsDatum M ψ cS Φ f →
        GlobalTheory.VacDatum.IsGaussEq M Bs.ψ Bs.emb Φ := by
  intro D ψ θ hθ ε S X A B d e Bs hBs hψ Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS f Φ hf hD
  subst hψ
  have hstd : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hBs.std
  obtain ⟨ξ, JB, co, hJB, hrat, hco⟩ :=
    exists_darboux_cS D Bs.ψ θ hθ ε S X A B e Bs hBs rfl Vs Ws r s r' s' hJ hJW hV hW hcart M hM cS hcS
  have hΦf : GlobalTheory.WeilSchrodinger.thetaTr D.host.F co Bs.ψ Φ = f := by
    funext w
    obtain ⟨u, rfl⟩ := cS.surjective w
    refine Eq.trans ?_ (hD.2 u)
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, hco]
  have hvac : ∀ τ z, dRho (heisO Bs.ψ (sgn ε S) X) θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) f =
      Complex.I • dRho (heisO Bs.ψ (sgn ε S) X) θ τ z f := by
    intro τ z
    funext w
    have h0 := congrFun (hf.2 τ z) w
    simp only [annih, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination (-Complex.I) * h0 +
      dRho (heisO Bs.ψ (sgn ε S) X) θ τ (cplxO ((frSgn ε A).cart τ) (B.cart τ) z) f w * Complex.I_sq
  refine ⟨fun _ => 1, fun u u' _ _ hrel x => ?_⟩
  have hrel' : ∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
      Complex.I • (Vs.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Ws.θ w)ᵀ) := fun w => by
    simpa using hrel w
  obtain ⟨hc, hc0⟩ := GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero D S X e _ cS hcS u
  obtain ⟨hc', hc0'⟩ := GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero D S X e _ cS hcS u'
  have key : (fun w => deriv (fun t : ℝ => heisO Bs.ψ (sgn ε S) X (archLine cS u' t) f w) 0) =
      Complex.I • (fun w => deriv (fun t : ℝ => heisO Bs.ψ (sgn ε S) X (archLine cS u t) f w) 0) := by
    refine (GlobalTheory.T.heisenbergDeriv_realLine_eq_sum_realPlaces D Bs.ψ hstd θ hθ (sgn ε S) X f hf.1 (archLine cS u') hc' hc0').trans
      (Eq.trans ?_ (congrArg (Complex.I • ·) (GlobalTheory.T.heisenbergDeriv_realLine_eq_sum_realPlaces D Bs.ψ hstd θ hθ (sgn ε S) X f hf.1 (archLine cS u) hc hc0).symm))
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    exact (congrArg (fun z => dRho (heisO Bs.ψ (sgn ε S) X) θ τ z f)
      (GlobalTheory.T.realPlaceComponent_archLine_complexStructure D θ hθ ε S X A B e Bs Vs Ws hcart cS hcS u u' hrel' τ)).trans (hvac τ _)
  rw [← hΦf] at key
  have h1 := GlobalTheory.T.schrodingerDeriv_relation_of_heisenbergDeriv D Bs.ψ hstd (sgn ε S) X JB ξ hJB (Fin S.rank × Fin d) co hrat Φ hD.1 (archLine cS u) (archLine cS u')
    hc hc0 hc' hc0' Complex.I key x
  simpa only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model.heisLine, GlobalTheory.WeilM.Darboux.rho, archLine_apply, hco] using h1

end GlobalTheory.VacTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionDivConjModulusOffBadPla
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ModBarOff

theorem idV_mul_inv_iff {D : D7} {v : GlobalTheory.FinPl.Pl D} (I : Ideal (𝓞 D.host.E)) (t : 𝓞 D.host.F) (ht : t ∉ v.asIdeal)
    (hI : algebraMap D.host.F D.host.E (t : D.host.F) ∈ (I : GlobalTheory.SeeSaw.FI D))
    (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D) :
    s ∈ GlobalTheory.SeeSaw.idV (𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  have ht0 : t ≠ 0 := fun h => ht (h ▸ v.asIdeal.zero_mem)
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  have hI0 : (I : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hI
    exact hF ((map_eq_zero _).1 hI)
  have e : 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * (I : GlobalTheory.SeeSaw.FI D) = 𝔞 := by
    rw [mul_assoc, inv_mul_cancel₀ hI0, mul_one]
  constructor
  · revert s
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, h1, h2, a, ha, rfl⟩
    obtain ⟨g1, g2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht h1 h2
    refine AddSubgroup.subset_closure ⟨_, g1, g2, _, ?_, GlobalTheory.IdVGen.tmul_eq ht α a⟩
    rw [← e, mul_comm (algebraMap D.host.F D.host.E (t : D.host.F)) a]
    exact FractionalIdeal.mul_mem_mul ha hI
  · refine fun h => GlobalTheory.SeeSaw.idV_mono ?_ v h
    calc 𝔞 = 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * (I : GlobalTheory.SeeSaw.FI D) := e.symm
      _ ≤ 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * 1 := by
        gcongr
        exact FractionalIdeal.coeIdeal_le_one
      _ = _ := mul_one _

theorem exists_mem_modul {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}
    (hv : v ∉ P.S0) : ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
  have h : ∀ u : HeightOneSpectrum (𝓞 D.host.F), ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ (u ∈ P.S0 → t ∈ u.asIdeal) := by
    intro u
    by_cases hu : u ∈ P.S0
    · have hne : ¬ u.asIdeal ≤ v.asIdeal := fun hle =>
        hv ((HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top hle)) ▸ hu)
      obtain ⟨t, h1, h2⟩ := SetLike.not_le_iff_exists.1 hne
      exact ⟨t, h2, fun _ => h1⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun h => absurd h hu⟩
  choose t ht1 ht2 using h
  refine ⟨∏ u ∈ P.S0, t u ^ P.depth sc u, ?_, ?_⟩
  · have := v.isPrime
    exact prod_mem (S := v.asIdeal.primeCompl) fun u _ => pow_mem (show t u ∈ v.asIdeal.primeCompl from ht1 u) _
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun u hu => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h1 := ht2 u hu
    have h2 : t u ∈ ((P.w u).under (𝓞 D.host.F)).asIdeal := by rw [P.under_w hu]; exact h1
    exact h2

theorem idV_mul_modulBar_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}, v ∉ P.S0 → ∀ (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D), s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  intro D T L P sc v hv 𝔞 s
  obtain ⟨t, ht, hm⟩ := exists_mem_modul P sc hv
  refine idV_mul_inv_iff _ t ht ?_ 𝔞 s
  have h1 : algebraMap D.host.F D.host.E (t : D.host.F) ∈ ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, hm, rfl⟩
  have h2 := (GlobalTheory.ChiGrid.StairConj.mem_coe_iff D _ _).1 h1
  have h3 : D.host.conj (algebraMap D.host.F D.host.E (t : D.host.F)) = algebraMap D.host.F D.host.E (t : D.host.F) :=
    (D.host.conjE_mem_hostF_iff _).1 (t : D.host.F).2
  rw [h3] at h2
  exact h2

end GlobalTheory.ModBarOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GWEqChiSmul
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FormEigenW

theorem gW_eq_chi_smul : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) (w : (R.HW i σ).H), (R.HW i σ).e w ∈ Mult R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P)) → ∀ g0 : P.H, R.gW i σ (R.eG.symm g0.1) w = ((P.chi g0 : ℂˣ) : ℂ) • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hLev hMod i σ P w hX g0
  apply (hMod.HW i σ).1
  have hg : (R.HW i σ).e (R.gW i σ (R.eG.symm g0.1) w) =
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG (R.eG.symm g0.1))) ((R.HW i σ).e w) :=
    hMod.gW i σ (R.eG.symm g0.1) w
  rw [hg, R.eG.apply_symm_apply, LinearMap.map_smul]
  have hM : IsMultMap R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (levChi _ (R.βW i) (R.datWp i P))
      ((R.HW i σ).e w) := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hX
  obtain ⟨κ', hκ'⟩ := (GlobalTheory.StepLifts.lifts_exist R hLev i).2 g0.1

  have hmem : κ' ∈ levG (Wc D i) (R.βW i) (R.datWp i P) := ⟨hκ'.1, hκ'.2.1, by
    show rTup (R.βW i) (R.datWp i R.triv) (finE (Wc D i) κ') ∈ P.H
    rw [hκ'.2.2]; exact g0.2⟩
  have hchi : levChi (Wc D i) (R.βW i) (R.datWp i P) κ' = ((P.chi g0 : ℂˣ) : ℂ) := by
    have hr : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ') = g0.1 := hκ'.2.2
    have h2 : ext1 (R.datWp i P).P.H (R.datWp i P).P.chi
        (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ')) = P.chi g0 := by
      have hp : rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ') ∈ P.H := by rw [hr]; exact g0.2
      have h3 : ext1 (R.datWp i P).P.H (R.datWp i P).P.chi
          (rTup (R.βW i) (R.datWp i P) (finE (Wc D i) κ')) = P.chi ⟨_, hp⟩ := extendOne_of_mem _ hp
      rw [h3]
      exact congrArg _ (Subtype.ext hr)
    unfold levChi levFn
    rw [h2]
    have hs : (R.datWp i P).s = 0 := rfl
    have hQ : (R.datWp i P).Q = ∅ := rfl
    rw [hs, hQ]
    simp
  ext v h
  show actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) g0.1 ((R.HW i σ).e w v) h =
    ((P.chi g0 : ℂˣ) : ℂ) * (R.HW i σ).e w v h
  have hT : HasType (Wc D i) (R.βW i) (flag1L (R.datWp i R.triv)) ((R.HW i σ).e w v) := by
    intro κ hκ h'
    have hle := GlobalTheory.GoodProjLevel.mem_levi_flag_of_mem_parabolic (L := R.datWp i R.triv) P hκ
    have h1 : (R.HW i σ).e w v (h' * κ) = levChi (Wc D i) (R.βW i) (R.datWp i P) κ * (R.HW i σ).e w v h' :=
      hM.lev v κ hle.1 h'
    rw [h1]
    exact congrArg (· * (R.HW i σ).e w v h') hle.2
  have hA := level_action_spec hT ⟨κ', hκ'⟩ κ' hκ' h
  rw [hA, GlobalTheory.ThetaShiftSmooth.levChi_flag_eq_one R i κ', inv_one, one_mul,
    hM.lev v κ' hmem h, hchi]

end GlobalTheory.FormEigenW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodParameterDiagonalNodes
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LeftVertexPar

theorem goodPar_P : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ τ, GoodPar (G.P i).V.rank ((G.P i).V.sig (tauE D τ)).1 ((G.P i).V.sig (tauE D τ)).2 ((G.P i).S τ) := by
  intro _ D _ G₀ _ _ Pl0 T A Ks _ _ _ R G _ hG i hi τ
  exact GlobalTheory.NodePar.goodPar_of_sigOK (G.P i) (hG.spaces.P i hi.le).sigOK τ

end GlobalTheory.LeftVertexPar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridPathCutAtSquareSwapRouteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridPath_cut_at_square_swap_route : ∀ {T : Type} (m : ℕ) (t : T) (i j : ℕ), i < m → j < m → ∀ {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid m t p → GlobalTheory.SplitFlip.PassesThrough i j (GlobalTheory.FlipRun.edges p) → ∃ (A : Path T X (.grid i (j + 1))) (Bp : Path T (.grid (i + 1) j) Y), p = (A.comp (routeSmall t i j)).comp Bp ∧ GlobalTheory.FlipRun.OnGrid m t A ∧ GlobalTheory.FlipRun.OnGrid m t Bp ∧ GlobalTheory.FlipRun.OnGrid m t ((A.comp (routeBig t i j)).comp Bp) ∧ GlobalTheory.FlipRun.edges ((A.comp (routeBig t i j)).comp Bp) = GlobalTheory.SplitFlip.flipPath i j (GlobalTheory.FlipRun.edges p) := by
  first | exact @GlobalTheory.PathCut.cut_at_square | exact GlobalTheory.PathCut.cut_at_square | (intros; apply GlobalTheory.PathCut.cut_at_square <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfLatticeCharSumDetectsNsmulMultipleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfLattice_charSum_detects_nsmul_multiple : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D) (k : ℕ) (R : Finset (WO S T)), 0 < k → (∀ u ∈ Λ, IsHalf e u → ∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T u y) = 1) → (∀ x : WO S T, IsHalf e x → (∀ y ∈ Λ, IsHalf (cA D e) y → ψ (symplO S T x y) = 1) → x ∈ Λ) → (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ Λ) → (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ Λ → ∃! r, r ∈ R ∧ y - r ∈ Λ) → ∀ t ∈ Λ, IsHalf e t → ((∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = R.card) ∧ ((¬ ∃ u ∈ Λ, IsHalf e u ∧ t = k • u) → ∑ r ∈ R, ψ (symplO S T t r) = 0) := by
  first | exact @GlobalTheory.CharSumHalf.charSum_detects_multiple | exact GlobalTheory.CharSumHalf.charSum_detects_multiple | (intros; apply GlobalTheory.CharSumHalf.charSum_detects_multiple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFirstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontal_theta_level_first : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.th t i j).ω h g Φ * φ g) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν) := by
  first | exact @GlobalTheory.ThetaArrowConv.thetaIntegral_integrableOn | exact GlobalTheory.ThetaArrowConv.thetaIntegral_integrableOn | (intros; apply GlobalTheory.ThetaArrowConv.thetaIntegral_integrableOn <;> assumption)
end

