import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormProdSignMulDetSubmatrixSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LeviFinsetSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1509
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorAndDensityNearOneInFlagChart
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal

namespace GlobalTheory.ChartNearOne

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem sum_succ_sub_castSucc {n : ℕ} (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  rw [Finset.sum_sub_distrib]
  have h1 := Fin.sum_univ_succ f
  have h2 := Fin.sum_univ_castSucc f
  linarith

theorem nmat_entry_le (X : Data E r) (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    ‖nmat X z τ a b - (if a = b then 1 else 0)‖ ≤ ‖z‖ := by
  unfold nmat
  by_cases h : b < a
  · have hab : a ≠ b := fun e => lt_irrefl b (e ▸ h)
    rw [dif_pos h, if_neg hab, sub_zero]
    exact PiLp.norm_apply_le z _
  · rw [dif_neg h]
    split_ifs <;> simp

theorem det_nmat (X : Data E r) (z : V (nd X)) (τ : X.Ψ) : (mat (nmat X z) τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp [mat, nmat]
  · intro a b hab
    have h1 : ¬ b < a := fun h => lt_asymm h hab
    have h2 : a ≠ b := ne_of_lt hab
    simp [mat, nmat, h1, h2]

theorem norm_dmin_zero (X : Data E r) (y : Frame X.Ψ r) (τ : X.Ψ) : ‖dmin X.Gm y τ 0‖ = 1 := by
  haveI : IsEmpty (Fin ((0 : Fin (r + 1)) : ℕ)) := ⟨fun i => absurd i.2 (by simp)⟩
  rw [dmin, lminor, Matrix.det_isEmpty, norm_one]

theorem norm_dmin_last (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (z : V (nd X)) (τ : X.Ψ) :
    ‖dmin X.Gm (cpt X x z) τ (Fin.last r)‖ = 1 := by
  rw [PoinPf.dmin_cpt_orth X hx]
  have e : lminor (PoinPf.Gw X z τ) (Fin.last r) = (PoinPf.Gw X z τ).det := rfl
  rw [e, PoinPf.Gw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_nmat,
    show (mat (nmat X z) τ).map (starRingEnd ℂ) = (starRingEnd ℂ).mapMatrix (mat (nmat X z) τ) from rfl,
    ← RingHom.map_det, det_nmat, PoinPf.Jd, Matrix.det_diagonal]
  simp only [one_mul, map_one, mul_one, norm_prod, Complex.norm_real, Real.norm_eq_abs, PoinPf.abs_sgn]
  simp

theorem abs_sub_mid_le (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) (i : Fin r) :
    |(la τ i : ℝ) - ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2| ≤ X.spread la τ / 2 := by
  have h1 := le_ciSup (Finite.bddAbove_range fun k => (la τ k : ℝ)) i
  have h2 := ciInf_le (Finite.bddBelow_range fun k => (la τ k : ℝ)) i
  unfold Data.spread
  rw [abs_le]
  constructor <;> linarith

theorem weighted_diff_le (X : Data E r) (la : Wt X.Ψ r) (τ : X.Ψ) (L : Fin (r + 1) → ℝ) {t : ℝ}
    (hL : ∀ i, |L i| ≤ t) (h0 : L 0 = 0) (hr : L (Fin.last r) = 0) :
    ∑ i : Fin r, (la τ i : ℝ) * (L i.succ - L i.castSucc) ≤ r * t * X.spread la τ := by
  set c := ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2
  have hs : 0 ≤ X.spread la τ := by
    rcases Nat.eq_zero_or_pos r with rfl | hr0
    · simp [Data.spread]
    · have := abs_sub_mid_le X la τ ⟨0, hr0⟩
      linarith [abs_nonneg ((la τ ⟨0, hr0⟩ : ℝ) - c)]
  have e : ∑ i : Fin r, (la τ i : ℝ) * (L i.succ - L i.castSucc) =
      ∑ i : Fin r, ((la τ i : ℝ) - c) * (L i.succ - L i.castSucc) +
        c * ∑ i : Fin r, (L i.succ - L i.castSucc) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, sum_succ_sub_castSucc, h0, hr, sub_zero, mul_zero, add_zero]
  calc ∑ i : Fin r, ((la τ i : ℝ) - c) * (L i.succ - L i.castSucc)
      ≤ ∑ i : Fin r, X.spread la τ / 2 * (2 * t) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (le_abs_self _).trans ?_
        rw [abs_mul]
        have h1 := abs_sub (L i.succ) (L i.castSucc)
        have h2 : |L i.succ - L i.castSucc| ≤ 2 * t := by linarith [hL i.succ, hL i.castSucc]
        exact mul_le_mul (abs_sub_mid_le X la τ i) h2 (abs_nonneg _) (by linarith)
    _ = r * t * X.spread la τ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end

theorem chart_near_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (la : Wt X.Ψ r) (w : ℝ) (x : Frame X.Ψ r), 0 < r → IsOrth X x → (∑ τ, X.spread la τ) ≤ w →
    ∀ z : V (nd X), ‖z‖ ≤ chartRad E r w → cpt X x z ∈ X.dom ∧
      Real.exp (-(1/20)) ≤ X.nfac la (cpt X x z) ^ 2 ∧ Real.exp (-(1/10)) ≤ densF X x z := by
  intro E _ _ _ r X la w x hr hx hw z hz
  have hf : (1 : ℝ) ≤ fdeg E := one_le_field_half_degree
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsp : ∀ τ, 0 ≤ X.spread la τ := fun τ => by
    have := abs_sub_mid_le X la τ ⟨0, hr⟩
    linarith [abs_nonneg ((la τ ⟨0, hr⟩ : ℝ) - ((⨆ k, (la τ k : ℝ)) + ⨅ k, (la τ k : ℝ)) / 2)]
  have hw0 : 0 ≤ w := le_trans (Finset.sum_nonneg fun τ _ => hsp τ) hw
  set δ := chartRad E r w with hδdef
  have hwf : 0 < w + fdeg E := by linarith
  have hδ0 : 0 < δ := by rw [hδdef, chartRad]; positivity
  have key : (r : ℝ) ^ 3 * δ * (w + fdeg E) * 200 = 1 := by
    rw [hδdef, chartRad]
    have : (r : ℝ) ≠ 0 := by positivity
    field_simp
  have hA0 : 0 ≤ (r : ℝ) ^ 3 * δ := by positivity
  have hA : (r : ℝ) ^ 3 * δ ≤ 1 / 200 := by
    nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ w + fdeg E by linarith) hA0]
  have hr2 : (r : ℝ) ^ 2 * δ ≤ (r : ℝ) ^ 3 * δ := by
    have : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 3 := pow_le_pow_right₀ hr1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this hδ0.le
  obtain ⟨hdom, hd⟩ := GlobalTheory.dmin_rmul_near_one X x hx (nmat X z) hδ0.le (by linarith)
    (fun τ a b => (nmat_entry_le X z τ a b).trans hz)
  change cpt X x z ∈ X.dom at hdom
  change ∀ τ i, dmin X.Gm (cpt X x z) τ i ≠ 0 ∧ |Real.log ‖dmin X.Gm (cpt X x z) τ i‖| ≤ 9 * ((r : ℝ) ^ 2 * δ) at hd
  set t := 9 * ((r : ℝ) ^ 2 * δ) with ht
  have ht0 : 0 ≤ t := by positivity
  refine ⟨hdom, ?_, ?_⟩
  ·
    have hne : ∀ τ i, dmin X.Gm (cpt X x z) τ i ≠ 0 := fun τ i => (hd τ i).1
    have hN := CurvPf.neg2log_nfac X la (cpt X x z) hne
    have hbound : -2 * Real.log (X.nfac la (cpt X x z)) ≤ r * t * w := by
      rw [hN]
      calc ∑ τ, ∑ i : Fin r, (la τ i : ℝ) * (Real.log ‖dmin X.Gm (cpt X x z) τ i.succ‖ -
            Real.log ‖dmin X.Gm (cpt X x z) τ i.castSucc‖)
          ≤ ∑ τ, (r : ℝ) * t * X.spread la τ :=
            Finset.sum_le_sum fun τ _ => weighted_diff_le X la τ
              (fun i => Real.log ‖dmin X.Gm (cpt X x z) τ i‖) (fun i => (hd τ i).2)
              (by simp only [norm_dmin_zero, Real.log_one])
              (by simp only [norm_dmin_last X hx, Real.log_one])
        _ = (r : ℝ) * t * ∑ τ, X.spread la τ := (Finset.mul_sum _ _ _).symm
        _ ≤ (r : ℝ) * t * w := mul_le_mul_of_nonneg_left hw (by positivity)
    have hsmall : (r : ℝ) * t * w ≤ 1 / 20 := by
      have e1 : (r : ℝ) * t * w = 9 * ((r : ℝ) ^ 3 * δ * w) := by rw [ht]; ring
      have e2 : 0 ≤ (r : ℝ) ^ 3 * δ * fdeg E := by positivity
      rw [e1]
      nlinarith
    have hpos : 0 < X.nfac la (cpt X x z) := by
      unfold Data.nfac
      exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
        Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hne _ _) (hne _ _))) _
    have e : X.nfac la (cpt X x z) ^ 2 = Real.exp (-(-2 * Real.log (X.nfac la (cpt X x z)))) := by
      rw [show -(-2 * Real.log (X.nfac la (cpt X x z))) =
        Real.log (X.nfac la (cpt X x z)) + Real.log (X.nfac la (cpt X x z)) by ring,
        Real.exp_add, Real.exp_log hpos, sq]
    rw [e]
    exact Real.exp_le_exp.2 (by linarith)
  ·
    have hfac : ∀ τ (i : Fin r), Real.exp (-(2 * t)) ≤ ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ ^ (-2 : ℤ) := by
      intro τ i
      obtain ⟨h0, h1⟩ := hd τ i.castSucc
      have hu : 0 < ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ := norm_pos_iff.2 h0
      have hu' : ‖dmin X.Gm (cpt X x z) τ i.castSucc‖ ≤ Real.exp t := by
        calc ‖dmin X.Gm (cpt X x z) τ i.castSucc‖
            = Real.exp (Real.log ‖dmin X.Gm (cpt X x z) τ i.castSucc‖) := (Real.exp_log hu).symm
          _ ≤ Real.exp t := Real.exp_le_exp.2 (abs_le.1 h1).2
      rw [zpow_neg, zpow_two, Real.exp_neg, two_mul, Real.exp_add]
      exact inv_anti₀ (by positivity) (mul_le_mul hu' hu' hu.le (Real.exp_pos _).le)
    have hprod : Real.exp (-(2 * t)) ^ (Fintype.card X.Ψ * r) ≤ densF X x z := by
      unfold densF
      calc Real.exp (-(2 * t)) ^ (Fintype.card X.Ψ * r)
          = ∏ τ : X.Ψ, ∏ i : Fin r, Real.exp (-(2 * t)) := by
            rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.card_univ,
              Fintype.card_fin, ← pow_mul, Nat.mul_comm (Fintype.card X.Ψ)]
        _ ≤ _ := Finset.prod_le_prod (fun τ _ => by positivity) (fun τ _ =>
            Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => hfac τ i))
    refine le_trans ?_ hprod
    rw [← Real.exp_nat_mul, QuadraticCoefficientForms.card_Psi X]
    refine Real.exp_le_exp.2 ?_
    push_cast
    have e1 : (fdeg E : ℝ) * r * -(2 * t) = -(18 * ((r : ℝ) ^ 3 * δ * fdeg E)) := by rw [ht]; ring
    have e2 : 0 ≤ (r : ℝ) ^ 3 * δ * w := by positivity
    rw [e1]
    nlinarith

end GlobalTheory.ChartNearOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitStabilizerDeterminantCharacter
section
noncomputable section

open Matrix

namespace GlobalTheory.StabPair

theorem det_one_add_vecMulVec {m : Type} [Fintype m] [DecidableEq m] {k : Type} [Field k] (a b : m → k) :
    (1 + vecMulVec a b).det = 1 + b ⬝ᵥ a := by
  rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow]

theorem stab (k : Type) [Field k] (n x x' : ℕ) (hx : x < n) (t : kˣ) (X : Matrix (Fin n) (Fin (x + x')) k) :
    ∃ (g : GL (Fin n) k) (p : GlobalTheory.SmGL.parab k (GlobalTheory.ThK.MidJac.e2 x x')),
      (g : Matrix (Fin n) (Fin n) k) * X *
        Matrix.transpose ((p : GL (Fin (x + x')) k) : Matrix (Fin (x + x')) (Fin (x + x')) k) = X ∧
      Matrix.GeneralLinearGroup.det g *
        Matrix.GeneralLinearGroup.det (GlobalTheory.SmGL.leviProj k (GlobalTheory.ThK.MidJac.e2 x x') p 0) = t := by
  set e := GlobalTheory.ThK.MidJac.e2 x x' with he
  by_cases h : ∃ i j, X i (e ⟨1, j⟩) ≠ 0
  · obtain ⟨I, j, hIj⟩ := h
    set J : Fin (x + x') := e ⟨1, j⟩ with hJ
    set c : k := ((t⁻¹ : kˣ) : k) - 1 with hc
    set u : Fin (x + x') → k := Pi.single J 1 with hu
    set ψ : Fin n → k := Pi.single I (X I J)⁻¹ with hψ
    have hψu : ψ ⬝ᵥ (X *ᵥ u) = 1 := by
      rw [hψ, single_dotProduct, hu]
      simp [mulVec, dotProduct_single, inv_mul_cancel₀ hIj]
    set G0 : Matrix (Fin n) (Fin n) k := 1 + vecMulVec (c • (X *ᵥ u)) ψ with hG0
    set P : Matrix (Fin (x + x')) (Fin (x + x')) k := 1 + vecMulVec (ψ ᵥ* X) (c • u) with hP
    have hdetG0 : G0.det = ((t⁻¹ : kˣ) : k) := by
      rw [hG0, det_one_add_vecMulVec, dotProduct_smul, hψu, hc]; simp
    have hdetP : P.det = ((t⁻¹ : kˣ) : k) := by
      rw [hP, det_one_add_vecMulVec, smul_dotProduct, hc]
      have : u ⬝ᵥ (ψ ᵥ* X) = ψ ⬝ᵥ (X *ᵥ u) := by
        rw [dotProduct_comm, dotProduct_mulVec]
      rw [this, hψu]; simp
    have hne : ((t⁻¹ : kˣ) : k) ≠ 0 := Units.ne_zero _
    set g0 : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero G0 (hdetG0 ▸ hne)
    set pG : GL (Fin (x + x')) k := Matrix.GeneralLinearGroup.mkOfDetNeZero P (hdetP ▸ hne)
    have hpG : (pG : Matrix _ _ k) = P := rfl
    have hg0 : (g0 : Matrix _ _ k) = G0 := rfl
    have hmem : pG ∈ GlobalTheory.SmGL.parab k e := by
      rw [GlobalTheory.SmGL.mem_parab]
      intro a b hab
      have hb : b ≠ J := by
        rintro rfl
        rw [hJ, GlobalTheory.SmGL.blk_apply] at hab
        have := (GlobalTheory.SmGL.blk e a).isLt
        rw [Fin.lt_def] at hab
        simp at hab
        omega
      have hab' : a ≠ b := by rintro rfl; exact lt_irrefl _ hab
      rw [hpG, hP]
      simp [vecMulVec_apply, hu, Pi.single_apply, hb, one_apply, hab']
    refine ⟨g0⁻¹, ⟨pG, hmem⟩, ?_, ?_⟩
    · have hT : (P)ᵀ = 1 + vecMulVec (c • u) (ψ ᵥ* X) := by
        rw [hP, transpose_add, transpose_one, transpose_vecMulVec]
      have hXQ : X * (1 + vecMulVec (c • u) (ψ ᵥ* X)) = G0 * X := by
        rw [hG0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, mul_vecMulVec, vecMulVec_mul, mulVec_smul]
      change ((g0⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * X *
        Matrix.transpose (pG : Matrix (Fin (x + x')) (Fin (x + x')) k) = X
      rw [hpG, hT, Matrix.mul_assoc, hXQ, ← Matrix.mul_assoc, ← hg0, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul]
    · have hblk : GlobalTheory.SmGL.leviProj k e ⟨pG, hmem⟩ 0 = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i i'
        rw [GlobalTheory.SmGL.leviProj_apply]
        have hne' : e ⟨0, i'⟩ ≠ J := by
          rw [hJ]; intro hh
          have := congrArg Sigma.fst (e.injective hh)
          simp at this
        simp only [hpG, hP, Matrix.add_apply, vecMulVec_apply, Pi.smul_apply, hu, Pi.single_apply, hne',
          if_false, smul_eq_mul, mul_zero, add_zero, Units.val_one]
        by_cases hii : i = i'
        · subst hii; simp
        · have : e ⟨0, i⟩ ≠ e ⟨0, i'⟩ := fun hh => hii (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective hh)).2)
          rw [one_apply_ne this, one_apply_ne hii]
      rw [hblk, map_one, mul_one, map_inv]
      have : Matrix.GeneralLinearGroup.det g0 = t⁻¹ := by
        ext; rw [Matrix.GeneralLinearGroup.val_det_apply, hg0, hdetG0]
      rw [this, inv_inv]
  · push_neg at h

    let Y : Matrix (Fin n) (Fin x) k := fun a i => X a (e ⟨0, i⟩)
    have hker : LinearMap.ker (Yᵀ).mulVecLin ≠ ⊥ :=
      LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hx)
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
    have hwX : w ᵥ* X = 0 := by
      funext b
      obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective b
      match a, i with
      | 0, i =>
        have hi : ∑ r, X r (e ⟨0, i⟩) * w r = 0 := congrFun hw i
        simp only [vecMul, dotProduct, Pi.zero_apply]
        rw [← hi]
        exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)
      | 1, i => simp [vecMul, dotProduct, h]
    obtain ⟨r, hr⟩ : ∃ r, w r ≠ 0 := by
      by_contra hcon; push_neg at hcon; exact hw0 (funext hcon)
    set v : Fin n → k := Pi.single r (w r)⁻¹ with hv
    have hwv : w ⬝ᵥ v = 1 := by rw [hv, dotProduct_single, mul_inv_cancel₀ hr]
    set G : Matrix (Fin n) (Fin n) k := 1 + vecMulVec (((t : k) - 1) • v) w with hG
    have hdetG : G.det = (t : k) := by
      rw [hG, det_one_add_vecMulVec, dotProduct_smul, hwv]; simp
    set gG : GL (Fin n) k := Matrix.GeneralLinearGroup.mkOfDetNeZero G (hdetG ▸ Units.ne_zero t)
    have hgG : (gG : Matrix (Fin n) (Fin n) k) = G := rfl
    refine ⟨gG, 1, ?_, ?_⟩
    · rw [OneMemClass.coe_one, Units.val_one, transpose_one, Matrix.mul_one, hgG, hG, Matrix.add_mul,
        Matrix.one_mul, vecMulVec_mul, hwX]
      ext a b; simp [vecMulVec_apply]
    · rw [map_one, Pi.one_apply, map_one, mul_one]
      ext; rw [Matrix.GeneralLinearGroup.val_det_apply, hgG]; exact hdetG

end GlobalTheory.StabPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsCompatible
section
noncomputable section

namespace GlobalTheory.PhRatCommon

section Lemmas

open NumberField
open scoped TensorProduct

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AdTh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}

theorem rdU_of_isBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) {m : ℕ} {f' : Rul Xo c'} {as : Fin m → c'.F}
    {fs : Fin m → Rul Xo c} (h : IsBC hle f' as fs) (k : (U (σ'.comp (incF c c' hle))).Comp)
    (x : Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) :
    rdU (unfBC hle U σ') f' k x = ∑ j, σ' (as j) * rdU (U (σ'.comp (incF c c' hle))) (fs j) k x := by
  by_cases hx : x ∈ ((U (σ'.comp (incF c c' hle))).X k).dom
  · letI : Algebra c.F (CAt σ') := (σ'.comp (incF c c' hle)).toAlgebra
    have e := h (CAt σ') (fun _ => rfl) ((unfBC hle U σ').un k ⟨x, hx⟩)
    have e1 : rdU (unfBC hle U σ') f' k x = toC (evR Xo c' f' ((unfBC hle U σ').un k ⟨x, hx⟩)) := dif_pos hx
    rw [e1, e]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x =
      toC (evR Xo c (fs j) ((U (σ'.comp (incF c c' hle))).un k ⟨x, hx⟩)) := dif_pos hx
    rw [e2]
    rfl
  · have e1 : rdU (unfBC hle U σ') f' k x = 0 := dif_neg hx
    rw [e1]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have e2 : rdU (U (σ'.comp (incF c c' hle))) (fs j) k x = 0 := dif_neg hx
    rw [e2, mul_zero]

theorem exists_rdU_eq_sum (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (f' : Rul Xo c') (hf : f' ∈ cusp Xo c' (unfBC hle U) a n) :
    ∃ (m : ℕ) (b : Fin m → c'.F) (fs : Fin m → cusp Xo c U a n), ∀ k x,
      rdU (unfBC hle U σ') f' k x = ∑ j, σ' (b j) * rdU (U (σ'.comp (incF c c' hle))) (fs j : Rul Xo c) k x := by
  obtain ⟨m, b, fs, hfs, hbc⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC E H Dw l Xo c c' hle).2 r U a n f' hf
  exact ⟨m, b, fun j => ⟨fs j, hfs j⟩, rdU_of_isBC hle U σ' hbc⟩

end Gen

theorem sum_shape {m : ℕ} {c l u x : ℂ} {a a' y p : Fin m → ℂ} (h : x = ∑ j, a j * y j) (ha : ∀ j, a' j = a j)
    (hp : ∀ j, p j = c * u * y j) : c * l * u * x = ∑ j, a' j * (l * p j) := by
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ha, hp]
  ring

end Lemmas

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.PhRatCommon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrame
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt

namespace GlobalTheory.PetAdd

theorem cnorm_add_le {ι : Type} [Fintype ι] (u w : ι → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (u + w) ≤ Formalism.HermitianLatticesTheory.cnorm u + Formalism.HermitianLatticesTheory.cnorm w := by
  have key : ∀ t : ι → ℂ, Formalism.HermitianLatticesTheory.cnorm t = ‖(WithLp.equiv 2 (ι → ℂ)).symm t‖ := fun t => by
    rw [EuclideanSpace.norm_eq]; rfl
  rw [key, key, key]
  have e : (WithLp.equiv 2 (ι → ℂ)).symm (u + w) = (WithLp.equiv 2 (ι → ℂ)).symm u + (WithLp.equiv 2 (ι → ℂ)).symm w := by
    first | exact WithLp.equiv_symm_add 2 u w | rfl | simp
  rw [e]
  exact norm_add_le _ _

theorem IsGram.add_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    {ι : Type} [Fintype ι] [DecidableEq ι] {b : Module.Basis ι K V} {X : InfinitePlace K → Matrix ι ι ℂ}
    {N : (K →+* ℂ) → V → ℝ} (h : IsGram b X N) (v : InfinitePlace K) (f g : V) :
    N v.embedding (f + g) ≤ N v.embedding f + N v.embedding g := by
  rw [← (h v).2, ← (h v).2, ← (h v).2]
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
  have : Formalism.HermitianLatticesTheory.vecAt b v (f + g) = Formalism.HermitianLatticesTheory.vecAt b v f + Formalism.HermitianLatticesTheory.vecAt b v g := by
    funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  rw [this, Matrix.mulVec_add]
  exact cnorm_add_le _ _

end GlobalTheory.PetAdd

namespace GlobalTheory.PetAdd

theorem normOn_add_le : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (G : WTZ E), GoodOn U x V dict Z G → ∀ σ (f g : cuspOn U Z G), normOn U x V dict Z G σ (f + g) ≤ normOn U x V dict Z G σ f + normOn U x V dict Z G σ g := by
  intro E _ _ _ H Dw l Xo c r U x D V dict Z G h σ f g
  obtain ⟨n, ⟨p, hp⟩⟩ := h.1
  have hconj : ∀ y, normOn U x V dict Z G ((starRingEnd ℂ).comp σ) y = normOn U x V dict Z G σ y :=
    fun y => GlobalTheory.CompHt.petOn_conj U x V dict Z G σ y
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · have := IsGram.add_le hp (InfinitePlace.mk σ) f g
    rwa [e] at this
  · have := IsGram.add_le hp (InfinitePlace.mk σ) f g
    have e' : (InfinitePlace.mk σ).embedding = (starRingEnd ℂ).comp σ := by
      rw [e]; ext a; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [e', hconj, hconj, hconj] at this
    exact this

end GlobalTheory.PetAdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointLeSpanGoodBlock
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.AdjBlockSpan

open GlobalTheory.AdjBlock

theorem range_adjoint_le_span_good_block : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → R.PGEquiv F → (∀ t, LinearMap.range (LinearMap.adjoint (R.Th t)) ≤ Submodule.span ℂ (R.jX t '' ((A3.A.fam.R t).ZHg A3.A.X : Set (A3.A.fam.R t).S.Forms))) ∧ ∀ i t, LinearMap.range (LinearMap.adjoint (R.thG i t)) ≤ Submodule.span ℂ (R.jV i t '' ((A3.A.fam.L i t).ZHg A3.A.X : Set (A3.A.fam.L i t).S.Forms)) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hW hE hS hPG
  have hC := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  have hG := GlobalTheory.T.lifts_equivariant_twisted_and_plain_models R F hW.phase hPG
  have hOk2 := hOk.ok2
  refine ⟨fun t => ?_, fun i t => ?_⟩
  · have h1 := GlobalTheory.T.range_adjoint_compositeLift_le_span_blockEigenspaces R.toRealDat F.lv2 hLI hOk2 hC hS t
    have h2 := GlobalTheory.AdjGood.range_adjoint_Th_le_span_good R.toRealDat F.lv2 hOk2 hC hG.1 t
    have hli := (model_form (R.B.R t).pres (R.HX t) (hC.models.HX t) (hC.models.jX t)).1
    have h3 := GlobalTheory.span_image_inf_of_linearIndependent _ (R.jX t) _ hli ((A3.A.fam.R t).ZH) ((A3.A.fam.R t).goodF A3.A.X)
    exact (le_inf h1 h2).trans h3.le
  · have h1 := GlobalTheory.T.range_adjoint_thetaLift_le_blockEigenspaceSpan R.toRealDat F.lv2 hLI hOk2 hC hS i t
    have h2 := GlobalTheory.AdjSpanLift.range_adjoint_lift_le R.toRealDat F.lv2 hOk2 hC hG.2 i t
    have hli := (model_form (R.B.L i t).pres (R.HV i t) (hC.models.HV i t) (hC.models.jV i t)).1
    have h3 := GlobalTheory.span_image_inf_of_linearIndependent _ (R.jV i t) _ hli ((A3.A.fam.L i t).ZH) ((A3.A.fam.L i t).goodF A3.A.X)
    exact (le_inf h1 h2).trans h3.le

end GlobalTheory.AdjBlockSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankDeficientSchwartzAverageStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_deficient_schwartz_average : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ (n d : ℕ) (c : Fin n → Fv F v), c ≠ 0 → ∀ f ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
    (∀ Y : Matrix (Fin n) (Fin d) (Fv F v), Y.rank ≠ n → f Y = 0) →
    ∃ (N : ℕ) (a : Fin N → ℂ) (w : Fin N → Fin d → Fv F v), ∑ m, a m = 1 ∧
      ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), (∑ m, a m * ψ₀ (∑ k, ∑ l, Y k l * c k * w m l)) * f Y = 0 := by
  first | exact @GlobalTheory.TorusSupportAvg.exists_charAvg_mul_eq_zero | exact GlobalTheory.TorusSupportAvg.exists_charAvg_mul_eq_zero | (intros; apply GlobalTheory.TorusSupportAvg.exists_charAvg_mul_eq_zero <;> assumption)
end

