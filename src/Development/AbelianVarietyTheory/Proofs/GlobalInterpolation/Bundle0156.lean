import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0155
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.SharpRestriction.DesignExistsOfChoices
import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0003
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0123
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0128
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FourthTensorThetaEqKernel
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.Bundle0001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0033
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicIsogenyConstantOfIsogenyFormula
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ObjCOfRecExObjO

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AutFormDefiniteUnitaryEqSumPolynomialMulAutFormStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autFormDefiniteUnitary_eq_sum_polynomial_mul_autForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (φ : UA E n → ℂ), IsAutFormU φ → ∃ (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → UA E n → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j} ∧ IsAutFormU (e i)) ∧ ∀ (k : infU E n) (g : UA E n), φ (g * k) = ∑ i, p i k * e i g := by
  first | exact @GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm | exact GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm | (intros; apply GlobalTheory.UnitaryDecomp.exists_poly_mul_autForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DutySevenLibrary
section
namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk GlobalTheory.EX GlobalTheory.Fc

theorem duty_seven_library : ∀ (eps : ℝ) (Fm : FamP eps), DQ.Duty7 Fm → Formalism.MainNotions.PageFix Fm ∧ Formalism.MainNotions.PageWin Fm ∧
    Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.ChosenWall Fm ∧ DQ.TupUsedF Fm ∧ DQ.TwAllF Fm := by
  intro eps Fm h
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  refine ⟨a, b, fun x hx i => (c x hx i).2.2.2.2.1, ?_, ⟨Fm.x1 + 1, fun x hx i => ?_⟩, f, g⟩
  · unfold DC.TameDistinctF at d
    unfold Formalism.MainNotions.TameDistinctF
    simpa only [tameDistinct_iff] using d
  · exact weightAdmissible_smallShares_at_point _ _ (e x (by linarith) i)

end GlobalTheory.EX.DQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EvenThetaIteratedDerivZeroAlgebraic
section
noncomputable section

namespace GlobalTheory.ThetaZeroAlg

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker
open GlobalTheory.IsogConst

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem omegaK_eq (d : ℕ) : Formalism.L2.Th1.CM.omegaK d = Formalism.L2.Th1.F.cmTheta 1 d := by
  unfold Formalism.L2.Th1.CM.omegaK Formalism.L2.Th1.F.cmTheta; push_cast; ring

theorem hasCMBy (B : Base D cc δ) : Formalism.L2.Th1.CM.HasCMBy D.host.d B.L := by
  intro ω hω
  rw [omegaK_eq]
  exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B ω hω

theorem disc_one (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.g₂ ^ 3 - 27 * B.L.g₃ ^ 2 = 1 := by
  have hL' : (B.L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← B.lat]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ B.L hL'
  have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  rw [← e2, ← e3]
  exact h

theorem d_sq (D : D7) : Squarefree D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).squarefree

theorem host_imagQuadratic_discriminant_mod_four (D : D7) : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega

theorem g₂_g₃_mem_Qbar (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.g₂ ∈ TaylorLogMetric.Qbar ∧ B.L.g₃ ∈ TaylorLogMetric.Qbar := by
  have hdisc := disc_one B hcc hδ
  have hj : IsIntegral ℤ (Formalism.L2.Th1.CM.jInv B.L) := GlobalTheory.ThLoc.cm1 D.host.d B.L (d_sq D) (host_imagQuadratic_discriminant_mod_four D) (hasCMBy B)
  have hjQ : Formalism.L2.Th1.CM.jInv B.L ∈ TaylorLogMetric.Qbar :=
    (qbar_iff _).2 (hj.tower_top (A := ℚ)).isAlgebraic
  have hg2c : B.L.g₂ ^ 3 = Formalism.L2.Th1.CM.jInv B.L / 1728 := by
    unfold Formalism.L2.Th1.CM.jInv; rw [hdisc]; ring
  have h2 : B.L.g₂ ∈ TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 3) (by norm_num) ?_
    rw [hg2c]; exact div_mem hjQ (nat_mem 1728)
  have h3sq : B.L.g₃ ^ 2 = (B.L.g₂ ^ 3 - 1) / 27 := by rw [← hdisc]; ring
  have h3 : B.L.g₃ ∈ TaylorLogMetric.Qbar := by
    refine qbar_of_pow (n := 2) (by norm_num) ?_
    rw [h3sq]
    exact div_mem (sub_mem (pow_mem h2 3) (one_mem _)) (nat_mem 27)
  exact ⟨h2, h3⟩

theorem kernelBase_periodLattice_sigmaTwo_algebraic (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    Formalism.L2.Th1.F.s2 B.L ∈ TaylorLogMetric.Qbar := by
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  have hd0 : 0 < D.host.d := (D.host.hyp.2.1 : D.host.d.Prime).pos
  obtain ⟨S, -, -, hIso, -⟩ := Formalism.L2.Th1.F.hasCMByIsogeny D.host.d B.L (hasCMBy B) (-1) 2 (by simp) hd0
  have hαsq := alpha_sq D.host.d
  have hα : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ∈ TaylorLogMetric.Qbar :=
    qbar_of_pow (n := 2) (by norm_num) (by rw [hαsq]; exact neg_mem (natCast_mem _ _))
  have hα0 : ((-1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d ≠ 0 := by
    intro h0
    rw [h0] at hαsq
    have : (D.host.d : ℂ) = 0 := by linear_combination hαsq
    have : D.host.d = 0 := by exact_mod_cast this
    omega
  have he : InQ (Formalism.L2.Th1.F.pSeries B.L) := by
    intro k
    rw [Formalism.L2.KerInert.AlgP.pSeries_eq_map TaylorLogMetric.Qbar B.L h2 h3, PowerSeries.coeff_map]
    exact SetLike.coe_mem _
  have hc := algebraic_isogenyConstant_of_isogenyFormula _ he _ _ hα hα0 _ hIso
  rw [hαsq] at hc
  have hN : (((Fintype.card S + 1 : ℕ) : ℂ) - -(D.host.d : ℂ)) = ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) := by
    push_cast; ring
  rw [hN] at hc
  have hN0 : ((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card S + 1 + D.host.d ≠ 0)
  have e : Formalism.L2.Th1.F.s2 B.L = (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ))⁻¹ *
      (((Fintype.card S + 1 + D.host.d : ℕ) : ℂ) * Formalism.L2.Th1.F.s2 B.L) := by
    rw [← mul_assoc, inv_mul_cancel₀ hN0, one_mul]
  rw [e]
  exact mul_mem (inv_mem (natCast_mem _ _)) hc

theorem weierstrassP_halfPeriod_algebraic (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    B.L.weierstrassP (B.ω₀ / 2) ∈ TaylorLogMetric.Qbar := by
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  haveI : Algebra.IsAlgebraic ℚ TaylorLogMetric.Qbar :=
    ⟨fun x => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 x.2)⟩
  have hN : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) ∈ B.L.lattice := by
    have e : ((2 : ℕ) : ℂ) * (B.ω₀ / 2) = B.ω₀ := by push_cast; ring
    rw [e]; exact B.omega_mem
  have hx : IsAlgebraic ℚ (B.L.weierstrassP (B.ω₀ / 2)) :=
    (PI.GalTorsConj.W.wp_isAlgebraic B.L TaylorLogMetric.Qbar h2 h3 2 (B.ω₀ / 2) (by norm_num) hN
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B)).restrictScalars ℚ
  exact mem_algebraicClosure_iff.2 hx

theorem evenTheta_iteratedDeriv_zero_algebraic : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ k : ℕ, iteratedDeriv k B.th0 0 ∈ TaylorLogMetric.Qbar := by
  intro D cc δ B hcc hδ k
  obtain ⟨h2, h3⟩ := g₂_g₃_mem_Qbar B hcc hδ
  have hc := Formalism.L2.KerInert.AlgP.theta_null_coefficients B.L B.ω₀ B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B) TaylorLogMetric.Qbar h2 h3
    (kernelBase_periodLattice_sigmaTwo_algebraic B hcc hδ) (weierstrassP_halfPeriod_algebraic B hcc hδ) k
  unfold Formalism.L2.Th1.F.taylor0 at hc
  rw [PowerSeries.coeff_mk] at hc
  have hf : ((k.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have e : iteratedDeriv k B.th0 0 = ((k.factorial : ℕ) : ℂ) *
      (iteratedDeriv k (Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2)) 0 / ((k.factorial : ℕ) : ℂ)) := by
    rw [mul_div_cancel₀ _ hf]; rfl
  rw [e]
  exact mul_mem (natCast_mem _ _) hc

end GlobalTheory.ThetaZeroAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDefiniteUnitaryFunctionPolynomialMulSmoothStatement
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_definiteUnitary_function_polynomial_mul_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → finU E n → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) → (∀ i, ∃ V : Subgroup (finU E n), IsOpen (V : Set (finU E n)) ∧ ∀ u ∈ V, ∀ g, e i (g * u) = e i g) → ∃ φ : UA E n → ℂ, Continuous φ ∧ IsOpen {k : finU E n | RU E n k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) ∧ ∀ (g : finU E n) (k : infU E n), φ (g.1 * k.1) = ∑ i, p i k * e i g := by
  first | exact @GlobalTheory.UnitaryBC.exists_fun_of_poly_smooth | exact GlobalTheory.UnitaryBC.exists_fun_of_poly_smooth | (intros; apply GlobalTheory.UnitaryBC.exists_fun_of_poly_smooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.Fc

theorem ObjCP.imp {Q Q' : Par → PtProp} (h : ObjCP Q) (hi : ∀ (κ : Par) (p : Pt κ.C), p.Has (Q κ) → p.Has (Q' κ)) : ObjCP Q' :=
  ParEv.mono (fun κ ⟨x0, H⟩ => ⟨x0, fun s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 =>
    let ⟨p, e1, e2, e3, e4, e5, e6⟩ := H s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9
    ⟨p, e1, e2, e3, e4, e5, hi κ p e6⟩⟩) h

open GlobalTheory.EX.DC in

theorem ObjCP.and_q0Pt {Q : Par → PtProp} (h : ObjCP Q) : ObjCP (fun κ => (Q κ).and twistingGlobalPointProp) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  obtain ⟨c1', hP⟩ := explicitConstants_parameterConditions_large eps a1 a3 C b1
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hP⟩ := hP cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch ((le_max_left _ _).trans hch)
  obtain ⟨x1, hP⟩ := hP ch ((le_max_right _ _).trans hch)
  obtain ⟨x2, hq⟩ := small_prime_lt eps C8 a1 a4
  obtain ⟨x3, hJ⟩ := GlobalTheory.ClassDuty.windowsAt_of eps a1 a3 C b1
  refine ⟨max (max x0 x1) (max x2 x3), fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  dsimp only at d1 d4 d5 d6 d7
  rw [b2] at d5
  simp only [max_le_iff] at d2
  obtain ⟨p, e1, e2, e3, e4, e5, e6⟩ := h s R H q0 a b M c u0 d1 d2.1.1 d3 d4 (b2 ▸ d5) d0 d6 d7 d8 d9
  refine ⟨p, e1, e2, e3, e4, e5, e6, ?_⟩
  dsimp only at e2 p
  subst e1
  show GlobalTwistingFacts p.L
  obtain ⟨hv, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hle, -⟩, hlev⟩ := d5
  have eq0 : q0Av p.D = q0 := (eq_of_from p e4 e2.host.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.1).trans d0.symm
  have hX : (q0Av p.D : ℝ) < p.L.sc.X' := by
    rw [eq0]
    exact hq _ _ q0 d1 d2.2.1 (by exact_mod_cast cond_pos H) hv.log_cond_le hle
  obtain ⟨P, -⟩ := hP _ _ d1 d2.1.2 e2 e3
  have hXb := X'_le_b p.L.sc
  have hs := globalTwisting_spec_fact p.D.host
  have hg : ∀ j, q0Av p.D < p.D.host.g j := by
    intro j
    have hg := (e2.host.2.2.2.2.1 j).1
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast (show (q0Av p.D : ℝ) < p.D.host.g j by linarith)
  refine ⟨?_, hs.1, hs.2.1, ?_, hX, hX.le.trans (hJ cD ch _ _ d1 d2.2.2 e2 P).2, (q0H_ne_pde_and_ne_pde' _).1, (q0H_ne_pde_and_ne_pde' _).2,
    fun j => (hg j).ne, fun u => ((hg 0).trans (firstTypePrime_lt_rowPrime _ u)).ne⟩
  · rw [eq0]
    exact e4.2.2.2.2.2.2.2.2.1 (by rw [hlev]; simp)
  · rw [Real.log_le_iff_le_exp (by exact_mod_cast hs.1.pos)]
    exact hX.le.trans hXb

open GlobalTheory.EX.DC GlobalTheory.EX.OB.Bridge in

theorem objCP_and_of_recExP (QO : Par → ∀ D : D7, Obj D → Prop) (hLP : LevelPrime) (hRec : RecExP QO) :
    ObjCP (fun κ => (ptO (QO κ)).and (TamePt.and (MinkPt.and TwPt))) := by
  obtain ⟨ε0, h0, hRec⟩ := hRec
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb e1 e2 e3 e4 => ?_⟩
  obtain ⟨K0, hRec⟩ := hRec eps C8 C5 c6 Cb e1 e2 e3 e4
  refine ⟨⟨K0.pre, K0.t, fun l => max (K0.mid l) 10, K0.last⟩, fun C hS hC8 hL => ?_⟩
  have hL0 : C.Large K0 C.P.CF :=
    ⟨hL.1, trivial, fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), hL.2.2.2⟩
  have hg : 10 ≤ C.cX.err.g := (le_max_right _ _).trans (hL.2.2.1 _ (by simp [FC.cMid]))
  obtain ⟨c1, hRec⟩ := hRec C hS hC8 hL0
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  have hcD0 : 0 ≤ cD := (le_max_right _ _).trans hcD
  obtain ⟨c2, hRec⟩ := hRec cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  have hch0 : 402 ≤ ch := (le_max_right _ _).trans hch
  obtain ⟨cs, x1, hcs, hRec⟩ := hRec ch ((le_max_left _ _).trans hch)
  obtain ⟨x2, h2⟩ := chGood_of_host eps C5 c6 Cb cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP eps cs C e1 e3 hcs hS
  obtain ⟨x4, h4⟩ := exists_sizeData_over eps cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x5, h5⟩ := scale_X'_le_of_log eps cs e1 hcs
  obtain ⟨x6, h6⟩ := scale_one_le_w'' eps e1
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max x5 x6), ?_⟩
  intro s R H q0 a b M c u0 hs hx hR hCT hH hq0 hW hM hc hu
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨y1, y2⟩, y3, y4⟩, y5, y6⟩ := hx
  dsimp only at hs hCT hH hW hM
  rw [hq0] at hH
  obtain ⟨hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh⟩ := h2 s R H a b M c u0 hs y2 hR hCT hH hW hM hc
  obtain ⟨du, Ds, hdu, hDs, hlog, hRec⟩ := hRec s _ _ _ _ hs y1 hCh
  obtain ⟨Lv, l1, l2, l3⟩ := h3 cD ch s _ _ _ _ _ du Ds hs y3 hCh.ok hdu hDs hlog
  obtain ⟨D, Y, hO, hRO, hLO, hTW, hQ⟩ := hRec Lv l1 l2 l3
  obtain ⟨hA, ⟨L0, m1, m2, m3⟩, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, eW, g11⟩ :=
    h4 s _ _ _ _ _ Lv D hs y4 hCh.ok l3 hO hRO
  have hDR : D.R = R := g0
  have hT : ∀ u, s.X' ≤ ((D.mem u).A.T : ℝ) := by
    intro u
    obtain ⟨u', hu'⟩ := exists_T_of_over hO u
    have w := (Lv.T_win u').1
    rw [l1, l2, l3] at w
    rw [hu']
    refine le_trans (h5 s R _ hs y5 hR ?_ (hlog u')) w
    have : (0 : ℝ) < du u' := by exact_mod_cast hdu u'
    have : 0 < GamS C s R := Real.exp_pos _
    positivity
  obtain ⟨p, n1, n2, n3, n4⟩ := Led.exists_ledPart C cD ch s D Y R.toFrame a b L0 hS hg (by rw [hDR]) m1 m2 m3 hA
    (by rw [hDR]; exact h6 s R hs y6 hR) hT hRO hLO
  exact ⟨p.pt, n1, p.pt_val n3, hA,
    ⟨hDR, g1, g2, g3, g4, g5, g6, g7, g8, g9.trans (R.toFrame.val_ofNat_of_lt hu), g10, p.pt_wtEq n2, ⟨eW, g11⟩,
      hO.field⟩, p.pt_canon n4,
    hQ p n1 n2 n3 n4, hRO.tame, hRO.mink, twAt_tr (nPrime p.L) p.ht hTW⟩

theorem objCP_of_recExP : ∀ QO : Par → ∀ D : D7, Obj D → Prop,
    LevelPrime → RecExP QO → ObjCP (fun κ => DC.withObj (ptO (QO κ))) :=
  fun QO hL hR => (objCP_and_of_recExP QO hL hR).and_q0Pt.imp fun _ _ hp => ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩

end GlobalTheory.Fc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RealTiedSetDiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField

namespace GlobalTheory.Fc

theorem realTied_setDiv {D : D7} (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ)
    (H : Formalism.L2.Theta.RealTied D) : Formalism.L2.Theta.RealTied (setDiv D N h) :=
  ⟨H.cdScale, H.dsig, H.dsig_all, H.vol⟩

theorem built_val (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd) (κ : Par) (D : D7) (O : Obj D) (c : ℝ) (b : Bd D O c)
    (hb : Built Q Lk κ D O c b) :
    Val κ.C κ.cD κ.ch O.L ∧ CanonInst O.Gx ∧ O.K = κ.C.GK ∧ O.cX = κ.C.cX ∧ O.L.sc.eps = κ.eps ∧
      (∀ u, D.div.h u = DV.hExpl6 D O.L O.X κ.C.Csz u) ∧ Nonempty (Formalism.L2.Theta.RealTied D) ∧
      Nonempty {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)} := by
  refine Built.ind (R := fun D O _ _ => Val κ.C κ.cD κ.ch O.L ∧ CanonInst O.Gx ∧ O.K = κ.C.GK ∧ O.cX = κ.C.cX ∧
      O.L.sc.eps = κ.eps ∧ (∀ u, D.div.h u = DV.hExpl6 D O.L O.X κ.C.Csz u) ∧ Nonempty (Formalism.L2.Theta.RealTied D) ∧
      Nonempty {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)}) ?_ hb
  intro K β _ _ h0 _ _
  obtain ⟨h1, h2, h3, h4, -⟩ := h0
  rw [← h1, ← h2, ← h3, ← h4]
  have hv : Val K.C K.cD K.ch β.O.L := β.p.pt_val β.val
  exact ⟨hv, β.p.pt_canon β.canon, rfl, rfl, congrArg Scale.eps β.sc, β.p.pt.xa.h_eq,
    ⟨realTied_setDiv _ _ β.c.real⟩, ⟨⟨(_, _), hv.Del_eq, hv.eta_eq⟩⟩⟩

end GlobalTheory.Fc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingClassesFrozen
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk GlobalTheory.EX GlobalTheory.Fc

namespace GlobalTheory.Fc

theorem tameDistinctF_iff {eps : ℝ} (Fm : FamP eps) : DC.TameDistinctF Fm ↔ Formalism.MainNotions.TameDistinctF Fm := by
  unfold DC.TameDistinctF Formalism.MainNotions.TameDistinctF
  simp only [DQ.tameDistinct_iff]

theorem dGamDvdF_iff {eps : ℝ} (Fm : FamP eps) : DC.DGamDvdF Fm ↔ Formalism.MainNotions.DGamDvdF Fm := Iff.rfl

theorem codeUpF_iff {eps : ℝ} (Fm : FamP eps) (C0 CH : ℝ) : DC.CodeUpF Fm C0 CH ↔ Formalism.MainNotions.CodeUpF Fm C0 CH := Iff.rfl

theorem working_classes_frozen : (∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), (Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧ Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9)) Fm ↔ W1 𝒜 Fm) ∧ (Formalism.MainNotions.Des (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧ Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9) 3 Fm ↔ W3 𝒜 Fm)) ∧ (∀ (𝒜 : FamClass) (cT : ℝ → ℝ → ℝ), (DC.MinkDiv → DC.DesignChoices (DC.WithTw 𝒜) 3 cT) → Formalism.MainNotions.MinkDiv → Formalism.MainNotions.DesignChoices (Formalism.MainNotions.WithTw 𝒜) 3 cT) := by
  refine ⟨fun 𝒜 eps Fm => ?_, fun 𝒜 cT h hM => ?_⟩
  · have e1 : Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (fun Fm => 𝒜 Fm ∧ Formalism.MainNotions.DGamDvdF Fm ∧ Formalism.MainNotions.TameDistinctF Fm ∧ Formalism.MainNotions.BoxesF Fm ∧
        Formalism.MainNotions.QDRowsF Fm ∧ Fm.CYL ≤ 9)) Fm ↔ W1 𝒜 Fm := by
      simp only [Formalism.MainNotions.WithTw, Formalism.MainNotions.WithSm, W1, tameDistinctF_iff, dGamDvdF_iff]
    refine ⟨e1, ?_⟩
    simp only [Formalism.MainNotions.Des, W3, ← e1]
  · obtain ⟨ε0, h0, h⟩ := h hM
    refine ⟨ε0, h0, fun eps he hle K => ?_⟩
    obtain ⟨Fm, CH, C5, Cb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h eps he hle K
    exact ⟨Fm, CH, C5, Cb, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, (tameDistinctF_iff Fm).1 h15, h16,
      (codeUpF_iff Fm 3 CH).1 h17, h18⟩

end GlobalTheory.Fc
end

