import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0312
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0314
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslatePowerSeriesPowBoundedCoeffsOfTorsi
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarAdditionFormulaPadicModelParameter
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.SigmaAdd

open PowerSeries

def gap {R τ : Type} [CommRing R] (s T : PowerSeries R) (x y : MvPowerSeries τ R) : MvPowerSeries τ R :=
  subst (x + y) s * subst (x - y) s - (subst x s * subst x s * subst y T - subst y s * subst y s * subst x T)

theorem mv_subst_subst {R σ τ : Type} [CommRing R] {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b)
    {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries R) :
    MvPowerSeries.subst b (subst a f : MvPowerSeries σ R) = subst (MvPowerSeries.subst b a) f := by
  have has : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => ha
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply has hb]
  rfl

theorem subst_gap {R τ : Type} [CommRing R] (s T : PowerSeries R) {b : Fin 3 → MvPowerSeries τ R}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (gap s T (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) R) =
      gap s T (b 0) (b 1) := by
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have hp : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) = 0 := by simp
  have hm : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R) = 0 := by simp
  simp only [gap, MvPowerSeries.subst_sub hb, MvPowerSeries.subst_mul hb, mv_subst_subst hb h0,
    mv_subst_subst hb h1, mv_subst_subst hb hp, mv_subst_subst hb hm, MvPowerSeries.subst_add hb,
    MvPowerSeries.subst_X hb]

theorem map_gap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (s T : PowerSeries R) :
    MvPowerSeries.map φ (gap s T (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) R) =
      gap (PowerSeries.map φ s) (PowerSeries.map φ T) (MvPowerSeries.X 0) (MvPowerSeries.X 1) := by
  have e : ∀ (a : MvPowerSeries (Fin 3) R), MvPowerSeries.constantCoeff a = 0 → ∀ f : PowerSeries R,
      MvPowerSeries.map φ (subst a f) = subst (MvPowerSeries.map φ a) (PowerSeries.map φ f) :=
    fun a ha f => PowerSeries.map_subst (HasSubst.of_constantCoeff_zero ha) f
  simp only [gap, map_sub, map_mul]
  rw [e _ (by simp), e _ (by simp), e _ (by simp), e _ (by simp), e _ (by simp), e _ (by simp)]
  simp only [map_add, map_sub, MvPowerSeries.map_X]

theorem add_entire {Λ : AddSubgroup ℂ} (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (z w : ℂ) :
    sgStar Λ (z + w) * sgStar Λ (z - w) =
      sgStar Λ z * sgStar Λ z * sqTh Λ v w - sgStar Λ w * sgStar Λ w * sqTh Λ v z := by
  have h1 := (h.differentiable_sqTh v).continuous
  have h3 := h.differentiable.continuous
  refine congrFun (Continuous.ext_on h.dense_compl
    (f := fun z => sgStar Λ (z + w) * sgStar Λ (z - w))
    (g := fun z => sgStar Λ z * sgStar Λ z * sqTh Λ v w - sgStar Λ w * sgStar Λ w * sqTh Λ v z)
    (by fun_prop) (by fun_prop) fun z hz => ?_) z
  beta_reduce
  have h0 := (h.sg_eq_zero z).not.2 hz
  have e : sgStar Λ (z + w) * sgStar Λ (z - w) = sgStar Λ z ^ 2 * sqTh Λ z w := by
    rw [sqTh]; field_simp
  rw [e, h.sqTh_sub hz hv w, h.sqTh_eq hv hz]
  ring

theorem tay_mul {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) :
    PowerSeries.mk (coef1 fun z => F z * G z) = PowerSeries.mk (coef1 F) * PowerSeries.mk (coef1 G) := by
  ext n
  simp only [coeff_mul, coeff_mk, GlobalTheory.SerTransport.taylorCoeff_mul_entire hF hG]

theorem tay_add {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G) :
    PowerSeries.mk (coef1 fun z => F z + G z) = PowerSeries.mk (coef1 F) + PowerSeries.mk (coef1 G) := by
  ext n
  simp only [map_add, coeff_mk, GlobalTheory.SerTransport.taylorCoeff_add_entire hF hG]

theorem tay_scale {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℂ) :
    (subst (C c * X : PowerSeries ℂ) (PowerSeries.mk (coef1 F)) : PowerSeries ℂ) =
      PowerSeries.mk (coef1 fun z => F (c * z)) := by
  rw [← smul_eq_C_mul, ← rescale_eq_subst]
  ext n
  simp only [coeff_rescale, coeff_mk, GlobalTheory.SerTransport.taylorCoeff_scale_entire hF]

theorem gap_taylor {Λ : AddSubgroup ℂ} (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) :
    (gap (PowerSeries.mk (coef1 (sgStar Λ))) (PowerSeries.mk (coef1 (sqTh Λ v)))
      (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) ℂ) = 0 := by
  refine GlobalTheory.mvPowerSeries_three_eq_zero_of_subst_lines ℂ _ fun t => ?_
  have hb : MvPowerSeries.HasSubst (fun i => (C (t i) * X : PowerSeries ℂ)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      rw [map_mul]; exact mul_eq_zero_of_right _ (PowerSeries.constantCoeff_X (R := ℂ))
  have hs := h.differentiable
  have hT := h.differentiable_sqTh v
  refine (subst_gap _ _ hb).trans ?_
  have key : (subst (C (t 0 + t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) : PowerSeries ℂ) *
      subst (C (t 0 - t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) +
      subst (C (t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 0) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sqTh Λ v))) =
      subst (C (t 0) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 0) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sgStar Λ))) *
        subst (C (t 1) * X : PowerSeries ℂ) (PowerSeries.mk (coef1 (sqTh Λ v))) := by
    simp only [tay_scale hs, tay_scale hT]
    rw [← tay_mul (by fun_prop) (by fun_prop), ← tay_mul (by fun_prop) (by fun_prop),
      ← tay_mul (by fun_prop) (by fun_prop), ← tay_mul (by fun_prop) (by fun_prop),
      ← tay_mul (by fun_prop) (by fun_prop), ← tay_add (by fun_prop) (by fun_prop)]
    congr 2
    funext z
    rw [add_mul, sub_mul, add_entire h hv]
    ring
  rw [map_add, map_sub, add_mul, sub_mul] at key
  unfold gap
  linear_combination key

variable {p : ℕ} [Fact p.Prime]

theorem sigmaAdditionFormula_padicTransfer_of_algebraicTaylor (lam : Qbar →+* ℂ_[p]) {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G)
    (h : (gap (PowerSeries.mk (coef1 F)) (PowerSeries.mk (coef1 G))
      (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) ℂ) = 0) :
    (gap (GL3Theta.ser1 lam F) (GL3Theta.ser1 lam G)
      (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
  have e : ∀ {H : ℂ → ℂ}, AlgEnt H → ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 H) = PowerSeries.map (algebraMap Qbar ℂ) S := fun {H} hH =>
    ⟨PowerSeries.mk fun n => ⟨coef1 H n, hH.2 n⟩, by
      ext n; rw [coeff_map, coeff_mk, coeff_mk]; rfl⟩
  obtain ⟨s, hs⟩ := e hF
  obtain ⟨T, hT⟩ := e hG
  rw [hs, hT, ← map_gap] at h
  have h' : (gap s T (MvPowerSeries.X 0) (MvPowerSeries.X 1) : MvPowerSeries (Fin 3) Qbar) = 0 := by
    ext d
    have := congrArg (MvPowerSeries.coeff d) h
    rw [MvPowerSeries.coeff_map, map_zero] at this
    simpa using this
  rw [Param.theta_series_map_coefficients lam _ _ hs, Param.theta_series_map_coefficients lam _ _ hT, ← map_gap, h', map_zero]

theorem const_subst {τ : Type} {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries ℂ_[p]} (hf : constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (subst a f : MvPowerSeries τ ℂ_[p]) = 0 := by
  obtain ⟨f', rfl⟩ := X_dvd_iff.2 hf
  have hs := HasSubst.of_constantCoeff_zero ha
  rw [subst_mul hs, subst_X hs, map_mul, ha, zero_mul]

theorem subst_inv {τ : Type} {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {f : PowerSeries ℂ_[p]} (hf : constantCoeff f ≠ 0) :
    (subst a f⁻¹ : MvPowerSeries τ ℂ_[p]) = (subst a f : MvPowerSeries τ ℂ_[p])⁻¹ := by
  have hs := HasSubst.of_constantCoeff_zero ha
  have e : (subst a f⁻¹ : MvPowerSeries τ ℂ_[p]) * subst a f = 1 := by
    rw [← subst_mul hs, PowerSeries.inv_mul_cancel _ hf, ← coe_substAlgHom hs, map_one]
  refine (MvPowerSeries.eq_inv_iff_mul_eq_one fun h0 => ?_).2 e
  have := congrArg MvPowerSeries.constantCoeff e
  rw [map_mul, h0, mul_zero, map_one] at this
  exact zero_ne_one this

theorem subst_atU (g : GL3Theta.G1 p) {τ : Type} {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (F : ℂ → ℂ) : (subst a (g.atU F) : MvPowerSeries τ ℂ_[p]) =
      subst (MvPowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.lg a) (GL3Theta.ser1 g.lam F) := by
  have hs := HasSubst.of_constantCoeff_zero ha
  rw [GlobalTheory.SerTransport.atU_eq, subst_comp_subst_apply
    (HasSubst.of_constantCoeff_zero' (GlobalTheory.SerTransport.const_Cl g _)) hs, subst_mul hs, subst_C]
  rfl

theorem lg_pt (g : GL3Theta.G1 p) (hg : g.Ok) {τ : Type} {x : MvPowerSeries τ ℂ_[p]}
    (hx : MvPowerSeries.constantCoeff x = 0) : g.lg (g.pt x) = x := by
  have hs := HasSubst.of_constantCoeff_zero hx
  rw [GL3Theta.G1.lg, GL3Theta.G1.pt, ← subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hg.2.2.1) hs,
    hg.2.2.2, subst_X hs]

theorem sigma_add_param : ∀ D : D7, Formalism.MainNotions.Ext.CutA.PAdicSigmaAdditionFormula D := by
  intro D p _ cc δ g hA
  obtain ⟨hq, hL, h2, h3, hσ, v, hv, hw⟩ := GlobalTheory.FrobStick.AtData.atData D p cc δ g hA
  have hok : g.Ok := hA.2.2.2.2
  obtain ⟨aT, eT⟩ := Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  have eS := GlobalTheory.FrobStick.sgStar_atU g hL hσ
  have hgap := sigmaAdditionFormula_padicTransfer_of_algebraicTaylor g.lam hσ aT (gap_taylor hL hv)
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (GL3Theta.Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  have hl : ∀ i : Fin 2, MvPowerSeries.constantCoeff (g.lg (GL3Theta.Xv i) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    fun i => const_subst (hX i) (GlobalTheory.SerTransport.const_l g)
  have hb : MvPowerSeries.HasSubst (![MvPowerSeries.C ε * g.lg (GL3Theta.Xv 0), MvPowerSeries.C ε * g.lg (GL3Theta.Xv 1), 0] :
      Fin 3 → MvPowerSeries (Fin 2) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by
      fin_cases i <;> simp [hl]
  have k := subst_gap (GL3Theta.ser1 g.lam (sgStar g.abelian₂)) (GL3Theta.ser1 g.lam (sqTh g.abelian₂ v)) hb
  rw [hgap, ← MvPowerSeries.coe_substAlgHom hb, map_zero] at k
  have hp0 : MvPowerSeries.constantCoeff
      (g.lg (GL3Theta.Xv 0) + g.lg (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by simp [hl]
  have hm0 : MvPowerSeries.constantCoeff
      (g.lg (GL3Theta.Xv 0) - g.lg (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by simp [hl]
  have hp : MvPowerSeries.constantCoeff (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    const_subst hp0 hok.2.2.1
  have hm : MvPowerSeries.constantCoeff (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    const_subst hm0 hok.2.2.1
  have kp := subst_atU g hp (sgStar g.abelian₂)
  have km := subst_atU g hm (sgStar g.abelian₂)
  rw [show g.lg (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = _ from lg_pt g hok hp0] at kp
  rw [show g.lg (g.sub (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = _ from lg_pt g hok hm0] at km
  simp only [gap, Matrix.cons_val_zero, Matrix.cons_val_one, ← mul_add, ← mul_sub] at k
  rw [← kp, ← km, ← subst_atU g (hX 0), ← subst_atU g (hX 0), ← subst_atU g (hX 1), ← subst_atU g (hX 1),
    eS, eT] at k
  have sS : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      (subst a (C ε * X * ePhi1 g.lam g.abelian₂ g.C g.wq) : MvPowerSeries (Fin 2) ℂ_[p]) =
        MvPowerSeries.C ε * a * subst a (ePhi1 g.lam g.abelian₂ g.C g.wq) := fun a ha => by
    have hs := HasSubst.of_constantCoeff_zero ha
    rw [subst_mul hs, subst_mul hs, subst_X hs, subst_C]
  have hwq : constantCoeff g.wq ≠ 0 := by
    have e := congrArg constantCoeff (show g.wq = _ from hq)
    simp only [map_add, map_mul, map_pow, map_one, constantCoeff_X] at e
    rw [e]
    simp
  have sT : ∀ a : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      (subst a (ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v)) : MvPowerSeries (Fin 2) ℂ_[p]) =
        subst a (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 2 *
          ((subst a g.wq : MvPowerSeries (Fin 2) ℂ_[p])⁻¹ - MvPowerSeries.C (xAt g v) * a ^ 2) := fun a ha => by
    have hs := HasSubst.of_constantCoeff_zero ha
    rw [lineSer, subst_mul hs, subst_pow hs, subst_sub hs, subst_mul hs, subst_pow hs, subst_X hs, subst_C,
      subst_inv ha hwq]
  rw [sS _ hp, sS _ hm, sS _ (hX 0), sS _ (hX 1), sT _ (hX 0), sT _ (hX 1)] at k
  have hne : (MvPowerSeries.C ε : MvPowerSeries (Fin 2) ℂ_[p]) ^ 2 ≠ 0 := by
    refine pow_ne_zero 2 fun h => Units.ne_zero g.C.u⁻¹ ?_
    have e := congrArg MvPowerSeries.constantCoeff h
    rwa [MvPowerSeries.constantCoeff_C, map_zero] at e
  apply mul_left_cancel₀ hne
  linear_combination -k

end GlobalTheory.SigmaAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameHeckeCharTrivialOnFiniteUnitsCongOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem valued_natCast_le_of_mem_asIdeal {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (m : ℕ)
    (hm : (m : 𝓞 L) ∈ P.asIdeal) : Valued.v ((m : P.adicCompletion L)) ≤ WithZero.exp (-1 : ℤ) := by
  have h1 : ((m : P.adicCompletion L)) = ((algebraMap (𝓞 L) L (m : 𝓞 L) : L) : P.adicCompletion L) := by
    rw [map_natCast]
    exact (map_natCast (algebraMap L (P.adicCompletion L)) m).symm
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have := (P.intValuation_le_pow_iff_mem (m : 𝓞 L) 1).2 (by simpa using hm)
  simpa using this

theorem finiteAdele_apply_sub_one_of_eq {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (m : ℕ)
    (a b : FiniteAdeleRing (𝓞 L) L) (e : a - 1 = (m : FiniteAdeleRing (𝓞 L) L) * b) :
    a P - 1 = (m : P.adicCompletion L) * b P := by
  let ev : FiniteAdeleRing (𝓞 L) L →+* P.adicCompletion L :=
    RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L) P
  have e3 : ev (a - 1) = ev ((m : FiniteAdeleRing (𝓞 L) L) * b) := congrArg ev e
  rw [ev.map_sub, ev.map_mul, ev.map_one, map_natCast ev m] at e3
  exact e3

theorem tame_heckeChar_eq_one_of_finUnit : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E), ChrEq c χ → (∀ P, χ.TameAt P) → ∀ m : ℕ, (∀ P : HeightOneSpectrum (𝓞 D.host.E), (m : 𝓞 D.host.E) ∉ P.asIdeal → χ.UnrAt P) → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = m • y) → c x = 1 := by
  intro D c χ hc ht m hu x hx ⟨y, hy, hxy⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.T.exists_baseChangeFiniteAdele_ringEquiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.T.heckeChar_eq_prod_localComponents_approximating D ι h1 h2 (GlobalTheory.T.exists_finitePlaceIdempotent_baseChangeAdeles D ι h1 h2 h3) c χ hc
  obtain ⟨S, k, hS, hS'⟩ := GlobalTheory.T.finiteIdele_exists_local_approx' D.host.E N hN
    (Units.map ((ι : _ →+* _).comp (finPart D)).toMonoidHom x)
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (x : AE D)) P) = 1 := by
    intro P
    have a := (h2 _).1 hx2 P
    have b := (h2 _).1 hx3 P
    have e : ι (finPart D (x : AE D)) * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have e' : Valued.v (ι (finPart D (x : AE D)) P) * Valued.v (ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P) = 1 := by
      rw [← map_mul]
      have : ι (finPart D (x : AE D)) P * ι (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)) P = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z P) e
      rw [this, map_one]
    refine le_antisymm a ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := e'.symm
      _ ≤ Valued.v (ι (finPart D (x : AE D)) P) * 1 := mul_le_mul_right b _
      _ = _ := mul_one _
  have key := hprod x hx1 S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS'
  apply Subtype.ext
  refine key.trans (Finset.prod_eq_one fun P hP => ?_)
  obtain ⟨a, -, b⟩ := hS P hP
  have a' : Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k P : D.host.E) := a
  have b' : Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) ≤
      WithZero.exp (-1 : ℤ) * P.valuation D.host.E (k P : D.host.E) := b
  rw [hv P] at a'
  rw [← a', mul_one] at b'
  have hun : IsUnitAt P (atFin P (k P)) := by
    show Valued.v (((k P : D.host.E)) : P.adicCompletion D.host.E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← a']
  have : χ.loc P (atFin P (k P)) = 1 := by
    by_cases hm : (m : 𝓞 D.host.E) ∈ P.asIdeal
    · refine ht P _ hun ?_
      have e : ι (finPart D (x : AE D)) - 1 = (m : FiniteAdeleRing (𝓞 D.host.E) D.host.E) * ι y := by
        rw [← map_one ι, ← map_sub, hxy, map_nsmul, nsmul_eq_mul]
      have e2 : ι (finPart D (x : AE D)) P - 1 = (m : P.adicCompletion D.host.E) * ι y P :=
        finiteAdele_apply_sub_one_of_eq P m _ _ e
      have c1 : Valued.v (ι (finPart D (x : AE D)) P - 1) ≤ WithZero.exp (-1 : ℤ) := by
        rw [e2, map_mul]
        calc _ ≤ WithZero.exp (-1 : ℤ) * 1 :=
              mul_le_mul' (valued_natCast_le_of_mem_asIdeal P m hm) ((h2 _).1 hy P)
          _ = _ := mul_one _
      have e4 : ((atFin P (k P) : (P.adicCompletion D.host.E)ˣ) : P.adicCompletion D.host.E) - 1 =
          (ι (finPart D (x : AE D)) P - 1) - (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k P : D.host.E)) := by
        show algebraMap D.host.E _ (k P : D.host.E) - 1 = _
        ring
      rw [e4]
      exact Valuation.map_sub_le _ c1 b'
    · exact hu P hm _ hun
  show ((χ.loc P (atFin P (k P)) : ℂˣ) : ℂ) = 1
  rw [this, Units.val_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOrderParameterSeriesBounded
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter
open scoped Topology

noncomputable section

namespace GlobalTheory.ThetaOrderBdd
open GlobalTheory.ThetaTransl GlobalTheory.ThetaTranslDecomp

variable {Λ : AddSubgroup ℂ}

theorem ratio_add (hΛ : IsLat Λ) {G : ℂ → ℂ} {k : ℕ}
    (hlaw : ∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ k = G z * sgStar Λ (z + ω) ^ k)
    (z : ℂ) {l : ℂ} (hl : l ∈ Λ) :
    G (z + l) / sgStar Λ (z + l) ^ k = G z / sgStar Λ z ^ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hlaw l hl z
  by_cases hz : z ∈ Λ
  · rw [(hΛ.sg_eq_zero z).2 hz, (hΛ.sg_eq_zero _).2 (add_mem hz hl), zero_pow hk.ne']
    simp
  have h0 := (hΛ.sg_eq_zero z).not.2 hz
  have h1 : sgStar Λ (z + l) ≠ 0 := (hΛ.sg_eq_zero _).not.2 (fun h => hz (by simpa using sub_mem h hl))
  rw [div_eq_div_iff (pow_ne_zero _ h1) (pow_ne_zero _ h0)]
  exact hlaw l hl z

theorem exists_decomp_gen : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (k : ℕ) (G : ℂ → ℂ), Differentiable ℂ G →
    (∀ ω ∈ Λ, ∀ z, G (z + ω) * sgStar Λ z ^ k = G z * sgStar Λ (z + ω) ^ k) →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), k ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - k) * G z =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  intro Λ hΛ k G hG hlaw v hv
  obtain ⟨L, h⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hσ := hΛ.differentiable
  have hS := hΛ.differentiable_sqTh v
  have hT : Continuous (sqThD Λ v) := by
    have h1 := hσ.deriv.continuous
    have h2 := hS.deriv.continuous
    have h3 := hσ.continuous
    have h4 := hS.continuous
    unfold sqThD
    fun_prop
  have hc : ∀ z, z ∉ L.lattice →
      ContinuousAt (fun z => G z / sgStar Λ z ^ k) z := fun z hz =>
    (hG z).continuousAt.div ((hσ z).continuousAt.pow k)
      (pow_ne_zero _ ((hΛ.sg_eq_zero z).not.2 ((h z).not.2 hz)))
  obtain ⟨A, B, hAB⟩ := GlobalTheory.EllipticPoles.no_pole_case L
    (g := fun z => G z / sgStar Λ z ^ k)
    (fun a => (hG.analyticAt a).meromorphicAt.div ((hσ.analyticAt a).meromorphicAt.pow k))
    (fun a ha => ⟨_, (hc a ha).tendsto.mono_left nhdsWithin_le_nhds⟩)
    (fun z l hl => ratio_add hΛ hlaw z ((h l).2 hl))
  have hAB' : ∀ z, z ∉ L.lattice → G z / sgStar Λ z ^ k =
      A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
    intro z hz
    have h1 := (L.analyticOnNhd_weierstrassP z hz).continuousAt
    have h2 := (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt
    have h3 : ContinuousAt (fun z => A.eval (L.weierstrassP z) +
        B.eval (L.weierstrassP z) * L.derivWeierstrassP z) z :=
      (A.continuous.continuousAt.comp h1).add ((B.continuous.continuousAt.comp h1).mul h2)
    exact tendsto_nhds_unique_of_eventuallyEq ((hc z hz).tendsto.mono_left nhdsWithin_le_nhds)
      (h3.tendsto.mono_left nhdsWithin_le_nhds) (hAB z)
  set A' := Polynomial.taylor (wpF Λ v) A with hA'
  set B' := Polynomial.taylor (wpF Λ v) B with hB'
  obtain ⟨I, hI⟩ : ∃ I, I = A'.natDegree + B'.natDegree + k := ⟨_, rfl⟩
  refine ⟨I, A'.coeff, B'.coeff, by omega, fun z => ?_⟩
  have h3 := hσ.continuous
  have h4 := hS.continuous
  have h5 := hG.continuous
  refine congrFun (Continuous.ext_on hΛ.dense_compl
    (f := fun z => sgStar Λ z ^ (2 * I + 3 - k) * G z)
    (g := fun z => ∑ i ∈ Finset.range (I + 1),
      A'.coeff i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
      ∑ j ∈ Finset.range (I + 1),
        B'.coeff j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z))
    (by fun_prop) (by fun_prop) fun z hz => ?_) z
  have hz' : z ∉ L.lattice := (h z).not.1 hz
  have h0 := (hΛ.sg_eq_zero z).not.2 hz
  have e := hAB' z hz'
  rw [← Polynomial.taylor_eval_sub (wpF Λ v) A, ← Polynomial.taylor_eval_sub (wpF Λ v) B,
    ← hA', ← hB', Polynomial.eval_eq_sum_range' (n := I + 1) (p := A') (by omega),
    Polynomial.eval_eq_sum_range' (n := I + 1) (p := B') (by omega),
    div_eq_iff (pow_ne_zero _ h0)] at e
  beta_reduce
  rw [e, mul_left_comm, ← pow_add, Nat.sub_add_cancel (by omega), sqThD_eq hΛ L h hv hz,
    hΛ.sqTh_eq hv hz, GlobalTheory.OddTheta.wpF_eq L Λ h z, add_mul, Finset.sum_mul, Finset.sum_mul,
    Finset.sum_mul]
  congr 1 <;> refine Finset.sum_congr rfl fun i hi => ?_
  all_goals
    obtain ⟨m, rfl⟩ : ∃ m, I = i + m := Nat.exists_eq_add_of_le (by simpa [Nat.lt_succ_iff] using hi)
    rw [Nat.add_sub_cancel_left, mul_pow]
    ring

set_option maxHeartbeats 800000 in

theorem order_bdd : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar →
    g3 g.abelian₂ ∈ Qbar → TaylorLogMetric.discr g.abelian₂ = 1 → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar →
    ∀ (k : ℕ) (G : ℂ → ℂ), AlgEnt G →
      (∀ ω ∈ g.abelian₂, ∀ z, G (z + ω) * sgStar g.abelian₂ z ^ k = G z * sgStar g.abelian₂ (z + ω) ^ k) →
      ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU G = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B := by
  intro p _ g hok hlat' h2 h3 hdisc hsg v hv hwv k G hG hlaw
  obtain ⟨hu1, hwq1, -, he0, hsgU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he_def
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε_def
  have he : e ≠ 0 := fun h => by rw [h, map_zero] at he0; exact zero_ne_one he0
  have gσ : GoodAt g 1 (sgStar g.abelian₂) :=
    ⟨hsg, PowerSeries.C ε * PowerSeries.X, bdd_mul (bdd_C ε) bdd_X, by rw [hsgU]; ring⟩
  obtain ⟨hSa, hSe⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg v hv hwv
  have gS : GoodAt g 2 (sqTh g.abelian₂ v) := ⟨hSa, lineSer g.wq⁻¹ (xAt g v),
    bdd_sub ⟨1, hwq1⟩ (bdd_mul (bdd_C _) (by rw [sq]; exact bdd_mul (bdd_X (p := p)) (bdd_X (p := p)))), hSe⟩
  obtain ⟨hTa, w, hw, hTe⟩ := GlobalTheory.ThetaTransl.CubeSer.sqThD_atU p g hok hlat' h2 h3 hdisc hsg v hv hwv
  have gT : GoodAt g 3 (sqThD g.abelian₂ v) := ⟨hTa, w, hw, hTe⟩
  obtain ⟨I, a, b, hle, hid⟩ := exists_decomp_gen g.abelian₂ hlat' k G hG.1 hlaw v hv
  let φ : Fin (I + 1) ⊕ Fin (I + 1) → ℂ → ℂ := Sum.elim
    (fun i z => sgStar g.abelian₂ z ^ (2 * (I - (i : ℕ)) + 3) * sqTh g.abelian₂ v z ^ (i : ℕ))
    (fun j z => sgStar g.abelian₂ z ^ (2 * (I - (j : ℕ))) * sqTh g.abelian₂ v z ^ (j : ℕ) * sqThD g.abelian₂ v z)
  let c : Fin (I + 1) ⊕ Fin (I + 1) → ℂ := Sum.elim (fun i => a i) (fun j => b j)
  have gφ : ∀ k, GoodAt g (2 * I + 3) (φ k) := by
    rintro (i | j)
    · have hi := i.isLt
      exact good_congr (good_mul (good_pow gσ (2 * (I - (i : ℕ)) + 3)) (good_pow gS (i : ℕ))) (by omega)
    · have hj := j.isLt
      exact good_congr (good_mul (good_mul (good_pow gσ (2 * (I - (j : ℕ)))) (good_pow gS (j : ℕ))) gT)
        (by omega)
  obtain ⟨hEa, hEe⟩ := atU_mul_pow (g := g) hsg hG (2 * I + 3 - k) 1
  have hEq : ∀ z, sgStar g.abelian₂ z ^ (2 * I + 3 - k) * G z ^ 1 = ∑ j, c j * φ j z := by
    intro z
    rw [pow_one, hid z, Fintype.sum_sum_type]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
  obtain ⟨a', -, hlin⟩ := GlobalTheory.TranslLin.transl_lin p g _ φ c _ hEa (fun j => (gφ j).1) hEq
  choose B hB hBe using fun j => (gφ j).2
  have hS : BddSer (∑ j, PowerSeries.C (lamC g.lam (a' j)) * B j) :=
    bdd_sum _ _ fun j _ => bdd_mul (bdd_C _) (hB j)
  rw [hEe, hsgU, pow_one] at hlin
  simp only [hBe] at hlin
  set Bk : PowerSeries ℂ_[p] := (e ^ k)⁻¹ * g.atU G with hBk
  have hGe : g.atU G = e ^ k * Bk := by
    rw [hBk, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [map_pow, he0, one_pow]; exact one_ne_zero),
      one_mul]
  rw [hGe] at hlin
  set K := 2 * I + 3 - k with hKd
  have hK : K + k = 2 * I + 3 := Nat.sub_add_cancel hle
  have hsum : ∑ j, PowerSeries.C (lamC g.lam (a' j)) * (e ^ (2 * I + 3) * B j) =
      e ^ (2 * I + 3) * ∑ j, PowerSeries.C (lamC g.lam (a' j)) * B j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  have hleft : (PowerSeries.C ε * PowerSeries.X * e) ^ K * (e ^ k * Bk) =
      e ^ (2 * I + 3) * (PowerSeries.C (ε ^ K) * (PowerSeries.X ^ K * Bk)) := by
    rw [← hK, pow_add, map_pow]; ring
  have key := hleft.symm.trans (hlin.trans hsum)
  have key2 := mul_left_cancel₀ (pow_ne_zero _ he) key
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨Bk, ⟨C0, fun n => ?_⟩, hGe⟩
  have h1 := congrArg (PowerSeries.coeff (n + K)) key2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h1
  have h2 := hC0 (n + K)
  rw [← h1, norm_mul, norm_pow, hu1, one_pow, one_mul] at h2
  exact h2

end GlobalTheory.ThetaOrderBdd
end
end

