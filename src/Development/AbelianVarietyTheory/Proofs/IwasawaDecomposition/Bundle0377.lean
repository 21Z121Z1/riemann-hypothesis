import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0992
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0362
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbedding
import Formalism.GradedWeylDivisibility.FinalB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0340
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0367
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0234
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceTransvectionActsPositivelyInvariantFor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightActionMatrixCoeffPolynomialInEntries

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeSmoothModelsOnThetaTargets
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowSmooth

open GlobalTheory.ConjDS GlobalTheory.ConjExt Formalism.MainNotions.S

variable {D : D7} {V : HSp D}

def glue {S : D.what₂.Tau → D.what₂.Tau → SPar} (N : ∀ τ, DSModel V (S τ)) : DSModel V fun τ => S τ τ where
  H τ := (N τ).H τ
  σ τ := (N τ).σ τ
  lam τ := (N τ).lam τ
  ε τ := (N τ).ε τ
  fr τ := (N τ).fr τ
  enum τ := (N τ).enum τ
  ds τ := (N τ).ds τ
  fr_unit τ := (N τ).fr_unit τ
  fr_gram τ := (N τ).fr_gram τ

theorem dualPar_dualPar (S : SPar) : dualPar (dualPar S) = S := by
  unfold dualPar
  ext x
  simp only [Finset.mem_image]
  exact ⟨fun ⟨_, ⟨y, hy, e⟩, e'⟩ => by subst e e'; simpa using hy,
    fun hx => ⟨(-x.1, x.2), ⟨x, hx, rfl⟩, by simp⟩⟩

theorem low_of_conj {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (h : lowKSub ((conjModel M).ε τ) ((conjModel M).lam τ) ((conjModel M).σ τ) ≤ (conjModel M).sm τ) :
    lowKSub (M.ε τ) (M.lam τ) (M.σ τ) ≤ M.sm τ := by
  intro w hw
  let c : (conjModel M).H τ ≃ₗᵢ⋆[ℂ] M.H τ := cj (M.H τ)
  have h1 := h (lowKSub_transfer (ε := M.ε τ) (ε' := (conjModel M).ε τ) (σ' := (conjModel M).σ τ) (fun _ => rfl) c
    (fun _ _ => rfl) hw)
  have h2 : ∀ y ∈ (conjModel M).sm τ, c y ∈ M.sm τ := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span (smoothVec_map c (conj_rep M τ) hy)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearIsometryEquiv.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have h3 := h2 _ h1
  simpa using h3

theorem shape_at {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (h : HCParam D.R) {p q : ℕ}
    (hn : V.rank = D.R.r) (hpq : p + q = V.rank)
    (hS : S τ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) :
    Formalism.QuantumDeterminants.IsHCParam (M.lam τ) ∧ ∃ p ≤ V.rank, ∀ a, M.ε τ a = decide ((a : ℕ) < p) := by
  have key := GlobalTheory.HolDict.isEnum_holPar_kapW h hn hpq (hS ▸ M.enum τ)
  refine ⟨⟨(M.enum τ).1, fun a => ?_⟩, p, by omega, fun a => (key a).2⟩
  obtain ⟨z, hz⟩ := Formalism.L2.NTheta.lamAt_int h a
  obtain ⟨s, hs⟩ := Formalism.L2.NTheta.odd_r D.R
  refine ⟨z - s, ?_⟩
  have hr : ((V.rank : ℕ) : ℝ) = 2 * s + 1 := by rw [hn, hs]; push_cast; rfl
  rw [(key a).1, hz, hr]
  push_cast
  ring

theorem lowSm_MW : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i σ, LowSm (R.MW i σ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i σ
  have key : ∀ τ, ∃ (S : D.what₂.Tau → SPar) (N : DSModel (Wc D i) S),
      (Formalism.QuantumDeterminants.IsHCParam (N.lam τ) ∧ ∃ p ≤ (Wc D i).rank, ∀ a, N.ε τ a = decide ((a : ℕ) < p)) ∧
      (lowKSub (N.ε τ) (N.lam τ) (N.σ τ) ≤ N.sm τ →
        lowKSub ((R.MW i σ).ε τ) ((R.MW i σ).lam τ) ((R.MW i σ).σ τ) ≤ (R.MW i σ).sm τ) := fun τ => by
    have hpq := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW (D := D) i τ
    by_cases hb : labE σ (lab σ τ) = tauE D τ
    · exact ⟨_, R.MW i σ, shape_at _ τ (D.hc (lab σ τ)) (rank_Wc i) hpq (if_pos hb), id⟩
    · refine ⟨_, conjModel (R.MW i σ), shape_at _ τ (D.hc (lab σ τ)) (rank_Wc i) hpq ?_, low_of_conj _ τ⟩
      unfold Links.parAt
      rw [if_neg hb, dualPar_dualPar]
      rfl
  choose S N hN hL using key
  exact fun τ => hL τ ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ (glue N) hN).1 τ)

end GlobalTheory.LowSmooth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MapSingleAtEmb
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.OneRep

noncomputable section

namespace GlobalTheory.OneRep

variable {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ}

omit [NumberField E] [NumberField.IsTotallyComplex E] in

theorem atEmb_zero (τ : E →+* ℂ) : atEmb τ 0 = 0 := by
  classical
  unfold atEmb; split_ifs <;> simp

omit [NumberField E] [NumberField.IsTotallyComplex E] in

theorem map_single_atEmb (τ : E →+* ℂ) (i k : Fin a) (z : ℂ) :
    (Matrix.single i k z).map (atEmb τ) = Matrix.single i k (atEmb τ z) := by
  ext p q
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [atEmb_zero]

end GlobalTheory.OneRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NablaSqUpperEigenvectorWeightEqHighest
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

open scoped Matrix

namespace GlobalTheory.HwEigen

theorem rowAct_transvection_eq_eval (K : Type) [Field K] (n : ℕ) (a b : Fin n) (hab : a ≠ b) (s : K)
    (f : MvPolynomial (Fin n × Fin n) K) :
    Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ f =
      (Formalism.GradedWeylDivisibility.rowGen K a b f).eval (MvPolynomial.C s) := by
  have h : (Polynomial.evalRingHom (MvPolynomial.C s)).comp (Formalism.GradedWeylDivisibility.rowGen K (n := n) a b).toRingHom =
      (Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Formalism.GradedWeylDivisibility.rowGen, Formalism.GradedWeylDivisibility.rowAct]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Formalism.GradedWeylDivisibility.rowGen,
        Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X, Polynomial.coe_evalRingHom]
      simp [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply, add_mul, Finset.sum_add_distrib]
      split_ifs with hv
      · rw [Finset.sum_eq_single a]
        · simp only [hv, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, and_self, if_true]
          exact mul_comm _ _
        · intro c _ hc
          simp [Ne.symm hc]
        · simp
      · simp [Ne.symm hv]
  exact (congrArg (fun φ => φ f) h).symm

end GlobalTheory.HwEigen

namespace GlobalTheory.HwEigen

theorem sqAct_smul' (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (B : GL (Fin n) K) (c : K)
    (f : MvPolynomial (Fin n × Fin n) K) : sqAct K n lam B (c • f) = c • sqAct K n lam B f := by
  unfold sqAct
  rw [map_smul, smul_comm]

theorem rowDiv_eq_zero_of_fixed (K : Type) [Field K] [Infinite K] (n : ℕ) (a b : Fin n) (hab : a ≠ b)
    (f : MvPolynomial (Fin n × Fin n) K)
    (hfix : ∀ s : K, Formalism.GradedWeylDivisibility.rowAct K (n := n) (Matrix.transvection a b s)ᵀ f = f)
    (k : ℕ) (hk : 1 ≤ k) : Formalism.GradedWeylDivisibility.rowDiv K a b k f = 0 := by
  have hP : Formalism.GradedWeylDivisibility.rowGen K a b f - Polynomial.C f = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun s : K => (MvPolynomial.C s : MvPolynomial (Fin n × Fin n) K))
      (MvPolynomial.C_injective _ _)
    intro s
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C]
    rw [← rowAct_transvection_eq_eval K n a b hab s, hfix s, sub_self]
  have h := congrArg (fun p => Polynomial.coeff p k) hP
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_zero] at h
  rw [if_neg (by omega), sub_zero] at h
  exact h

theorem mu_eq_of_upper_eigen : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam0 : DomWeight n) (mu : Fin n → ℤ)
    (f : MvPolynomial (Fin n × Fin n) K), f ∈ nablaSq K n lam0 → f ≠ 0 →
    (∀ B : GL (Fin n) K, (B : Matrix (Fin n) (Fin n) K).BlockTriangular id →
      sqAct K n lam0 B f = (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ mu a) • f) → mu = lam0.w := by
  intro K _ _ n lam0 mu f hf hf0 hB
  haveI : Infinite K := inferInstance

  have hkill : ∀ a b : Fin n, a < b → ∀ k : ℕ, 1 ≤ k → Formalism.GradedWeylDivisibility.rowDiv K a b k f = 0 := by
    intro a b hab k hk
    have hne : a ≠ b := ne_of_lt hab
    apply rowDiv_eq_zero_of_fixed K n a b hne f _ k hk
    intro s
    have hdet : (Matrix.transvection a b s).det = 1 := Matrix.det_transvection_of_ne a b hne s
    let B : GL (Fin n) K := Matrix.nonsingInvUnit _ (by rw [hdet]; exact isUnit_one)
    have hBv : (B : Matrix (Fin n) (Fin n) K) = Matrix.transvection a b s := rfl
    have hent : ∀ i j, (B : Matrix (Fin n) (Fin n) K) i j = (if i = j then 1 else 0) + (if a = i ∧ b = j then s else 0) := by
      intro i j
      rw [hBv]
      simp [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    have htri : (B : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
      intro i j hij
      rw [hent]
      have h1 : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
      have h2 : ¬ (a = i ∧ b = j) := by
        rintro ⟨rfl, rfl⟩
        exact lt_asymm hab hij
      simp [h1, h2]
    have hdiag : ∀ i, (B : Matrix (Fin n) (Fin n) K) i i = 1 := by
      intro i
      rw [hent]
      have h2 : ¬ (a = i ∧ b = i) := by
        rintro ⟨rfl, h⟩
        exact hne h.symm
      simp [h2]
    have h := hB B htri
    simp only [hdiag, one_zpow, Finset.prod_const_one, one_smul] at h
    have hdp : detPow K n B lam0.detShift = 1 := by
      unfold detPow
      have : Matrix.GeneralLinearGroup.det B = 1 := by
        ext
        simp [Matrix.GeneralLinearGroup.val_det_apply, hBv, hdet]
      rw [this, one_zpow, Units.val_one]
    unfold sqAct at h
    rw [hdp, one_smul, hBv] at h
    exact h

  obtain ⟨c, hc⟩ := Formalism.GradedWeylDivisibility.hwLine K n n le_rfl lam0.natW (PI.WGB.natW_anti_A lam0) f hf hkill
  have he : extremal K n lam0 ≠ 0 := Formalism.GradedWeylDivisibility.hwNe K n n le_rfl lam0.natW
  have hce : f = c • extremal K n lam0 := hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf0 (by rw [hce, zero_smul])

  funext i
  let d : Fin n → K := Function.update (fun _ => 1) i 2
  have hdd : (Matrix.diagonal d).det = 2 := by
    rw [Matrix.det_diagonal, Finset.prod_eq_single i]
    · simp [d]
    · intro j _ hj
      simp [d, hj]
    · simp
  let B : GL (Fin n) K := Matrix.nonsingInvUnit _ (by rw [hdd]; exact isUnit_iff_ne_zero.mpr two_ne_zero)
  have hBv : (B : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d := rfl
  have htri : (B : Matrix (Fin n) (Fin n) K).BlockTriangular id := by
    rw [hBv]; exact Matrix.blockTriangular_diagonal d
  have h := hB B htri
  rw [hce, sqAct_smul', GlobalTheory.AlgWtF.DDHw.sqAct_upper K n lam0 B htri, smul_smul, smul_smul] at h
  have h2 := smul_left_injective K he h
  have hprod : ∀ m : Fin n → ℤ, (∏ a, (B : Matrix (Fin n) (Fin n) K) a a ^ m a) = (2 : K) ^ m i := by
    intro m
    rw [Finset.prod_eq_single i]
    · simp [hBv, d]
    · intro j _ hj
      simp [hBv, d, hj]
    · simp
  simp only [hprod] at h2
  have h3 : ((2 : K) ^ lam0.w i) = (2 : K) ^ mu i := by
    have := h2
    rw [mul_comm] at this
    exact (mul_right_cancel₀ hc0 this)
  have h4 : (((2 : ℚ) ^ lam0.w i : ℚ) : K) = (((2 : ℚ) ^ mu i : ℚ) : K) := by
    rw [Rat.cast_zpow, Rat.cast_zpow, Rat.cast_ofNat]
    exact h3
  have h5 := Rat.cast_injective h4
  exact (zpow_right_injective₀ (by norm_num : (0 : ℚ) < 2) (by norm_num) h5).symm

end GlobalTheory.HwEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelFormsSpanDefiniteMultiplicitySpaceStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLevelForms_span_definiteMultiplicitySpace : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → TopMultH R → ∀ (b : Bool) (t : T), Submodule.span ℂ (Set.range fun x => R.cX.toMap R.prX ((R.HX t).e (R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)))) = Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  first | exact @GlobalTheory.TopSpan.topSpan | exact GlobalTheory.TopSpan.topSpan | (intros; apply GlobalTheory.TopSpan.topSpan <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SatakeParametersInertPlaceIndependentOfModel
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

namespace GlobalTheory.SatInd

theorem satAt_indep : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n), π.Iso π' → ∀ v w, NG.OverPl w v → ∀ (Dv Dv' : InertDatum L n v w) α, NG.SatAt π Dv α → NG.SatAt π' Dv' α := by
  intro L _ _ _ n π π' hiso v w _ Dv Dv' α hsat
  have h1 : NG.SatAt π Dv' α := by
    obtain ⟨f, hfS, hf0, U, hU, hUv, hH⟩ := hsat
    refine ⟨f, hfS, hf0, U, hU, hUv, fun h' hh' => ?_⟩
    have hm : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    rw [GlobalTheory.T.inertHeckeOperator_indep_of_inertDatum L n v w Dv Dv' U _ h' hh'.1 f,
      hH _ (GlobalTheory.T.heckeAlgebra_comp_unitaryGroupAntidiagTransport_mem (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') n h' hh'),
      GlobalTheory.T.unitarySatake_invariant_antidiagTransport (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ n (n / 2) h' hh'.1
        (GlobalTheory.T.unitaryTorus_unipotent_coset_transport_iff (gEquiv Dv Dv') (gEquiv_comm Dv Dv') (gEquiv_intL Dv Dv') Dv.ϖ Dv'.ϖ _ _ n (n / 2)
          Dv.unram Dv'.unram hm)]
  exact GlobalTheory.T.inertSatakeParameters_eq_of_iso L n π π' hiso v w Dv' α
    (GlobalTheory.T.finite_inertHecke_support_cosets L n v w Dv' (GlobalTheory.T.unitary_doubleCoset_finite_left_cosets Dv'.ϖ Dv'.σw _ n Dv'.unram) (GlobalTheory.T.mem_maxCompact_of_trivOutside_local_integral L n v w Dv')) h1

end GlobalTheory.SatInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaEquivariantPairBoundedFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.SmVec MeasureTheory Matrix Filter
open scoped TensorProduct ContDiff InnerProductSpace Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVec

theorem exists_l2_lift {H : Type} [AddCommGroup H] [Module ℂ H] (D : Submodule ℂ H) {X : Type} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (a : H →ₗ[ℂ] (X → ℂ))
    (ha : ∀ w ∈ D, Continuous (a w) ∧ ∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) :
    ∃ A : H →ₗ[ℂ] Lp ℂ 2 ν, ∀ w ∈ D, (A w : X → ℂ) =ᵐ[ν] a w := by
  classical
  have hm : ∀ w : D, MemLp (a w) 2 ν := fun w => by
    obtain ⟨hc, C, hC⟩ := ha w w.2
    exact MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  let f : D →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun w => (hm w).toLp (a w)
      map_add' := fun w w' => by
        refine Lp.ext ?_
        filter_upwards [(hm (w + w')).coeFn_toLp, (hm w).coeFn_toLp, (hm w').coeFn_toLp,
          Lp.coeFn_add ((hm w).toLp (a w)) ((hm w').toLp (a w'))] with x h1 h2 h3 h4
        rw [h4, Pi.add_apply, h1, h2, h3, Submodule.coe_add, map_add, Pi.add_apply]
      map_smul' := fun c w => by
        refine Lp.ext ?_
        filter_upwards [(hm (c • w)).coeFn_toLp, (hm w).coeFn_toLp,
          Lp.coeFn_smul c ((hm w).toLp (a w))] with x h1 h2 h3
        rw [RingHom.id_apply, h3, Pi.smul_apply, h1, h2, Submodule.coe_smul, map_smul, Pi.smul_apply] }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨g, fun w hw => ?_⟩
  have hgw : g w = f ⟨w, hw⟩ := by rw [← hg]; rfl
  rw [hgw]
  exact (hm ⟨w, hw⟩).coeFn_toLp

theorem l2_inner_of_ae {X : Type} [MeasurableSpace X] {ν : Measure X} {f g : Lp ℂ 2 ν} {u v : X → ℂ}
    (hf : (f : X → ℂ) =ᵐ[ν] u) (hg : (g : X → ℂ) =ᵐ[ν] v) : ⟪f, g⟫_ℂ = ∫ x, star (u x) * v x ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf, hg] with x hx hy
  rw [hx, hy, RCLike.inner_apply, mul_comm, starRingEnd_apply]

private lemma jm_sq_lemma {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> norm_num

private lemma jm_herm_lemma_2 {n : ℕ} (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : ε i <;> simp [h]

private lemma jm_conjTranspose_jm_mem_and_inverse {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε ∈ UJset ε ∧ (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 ∧
      g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have jj : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, jm_sq_lemma, Matrix.one_mul]
  have hl : (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = 1 := by
    calc (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) * g = Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, jm_sq_lemma]
  have hr : g * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = 1 := mul_eq_one_comm.mp hl
  refine ⟨?_, hl, hr⟩
  have hr' : g * (Formalism.REAL.Jm ε * (gᴴ * Formalism.REAL.Jm ε)) = 1 := by simpa only [Matrix.mul_assoc] using hr
  show (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε
  simp only [Matrix.conjTranspose_mul, jm_herm_lemma_2, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, jj]
  rw [hr', Matrix.mul_one]

theorem schurLemma_equivariant_pair_boundedFunctions : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (P G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = G → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (X : Type) [TopologicalSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν] (act : Formalism.REAL.UJ ε → X → X), Continuous (Function.uncurry act) → ∀ (a a' : H →ₗ[ℂ] (X → ℂ)), (∀ w ∈ smSub G (trRep σ P), Continuous (a w) ∧ (∃ C : ℝ, ∀ x, ‖a w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a (σ (umat g) w) x = a w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a)) → (∀ w ∈ smSub G (trRep σ P), Continuous (a' w) ∧ (∃ C : ℝ, ∀ x, ‖a' w x‖ ≤ C) ∧ ∀ (g : Formalism.REAL.UJ ε) x, a' (σ (umat g) w) x = a' w (act g x)) → (∀ x, Sobolev₂ (lieG G) (trRep σ P) ((LinearMap.proj x).comp a')) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a (σ g w) x ∂ν = ∫ x, star (a u x) * a w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a' (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a' u x) * a' w x ∂ν) → (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P), ∫ x, star (a (σ g u) x) * a' (σ g w) x ∂ν = ∫ x, star (a u x) * a' w x ∂ν) → ∃ c : ℂ, ∀ w ∈ smSub G (trRep σ P), ∀ w' ∈ smSub G (trRep σ P), ∫ x, star (a w x) * a' w' x ∂ν = c * ⟪w, w'⟫_ℂ := by
  intro n ε H _ _ _ σ P G hP hG hσ hirr X _ _ _ _ ν _ act hact a a' ha hsa ha' hsa' hI hI' hIx
  obtain ⟨A, hA⟩ := exists_l2_lift (smSub G (trRep σ P)) ν a (fun w hw => ⟨(ha w hw).1, (ha w hw).2.1⟩)
  obtain ⟨A', hA'⟩ := exists_l2_lift (smSub G (trRep σ P)) ν a' (fun w hw => ⟨(ha' w hw).1, (ha' w hw).2.1⟩)
  have hmem : ∀ g ∈ UJset ε, ∀ w ∈ smSub G (trRep σ P), σ g w ∈ smSub G (trRep σ P) :=
    fun g hg w hw => sigma_mem hP hG hσ hw hg
  have hAinv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A (σ g u), A (σ g w)⟫_ℂ = ⟪A u, A w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA _ (hmem g hg u hu)) (hA _ (hmem g hg w hw)), l2_inner_of_ae (hA u hu) (hA w hw)]
    exact hI g hg u hu w hw
  have hA'inv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A' (σ g u), A' (σ g w)⟫_ℂ = ⟪A' u, A' w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA' _ (hmem g hg u hu)) (hA' _ (hmem g hg w hw)), l2_inner_of_ae (hA' u hu) (hA' w hw)]
    exact hI' g hg u hu w hw
  have hxinv : ∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪A (σ g u), A' (σ g w)⟫_ℂ = ⟪A u, A' w⟫_ℂ := by
    intro g hg u hu w hw
    rw [l2_inner_of_ae (hA _ (hmem g hg u hu)) (hA' _ (hmem g hg w hw)), l2_inner_of_ae (hA u hu) (hA' w hw)]
    exact hIx g hg u hu w hw
  have hcl := closable_of_smoothing n ε H σ P G hP hG hσ (Lp ℂ 2 ν) A hAinv
    (continuous_inner_l2_translate n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
    (GlobalTheory.T.smooth_vectors_continuous_l2 n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
    (GlobalTheory.T.smooth_vectors_inner_product n ε H σ P G hP hG hσ X ν act hact a A ha hsa hA)
  have hcl' := closable_of_smoothing n ε H σ P G hP hG hσ (Lp ℂ 2 ν) A' hA'inv
    (continuous_inner_l2_translate n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
    (GlobalTheory.T.smooth_vectors_continuous_l2 n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
    (GlobalTheory.T.smooth_vectors_inner_product n ε H σ P G hP hG hσ X ν act hact a' A' ha' hsa' hA')
  have hnorm : ∀ B : H →ₗ[ℂ] Lp ℂ 2 ν, (∀ g ∈ UJset ε, ∀ u ∈ smSub G (trRep σ P), ∀ w ∈ smSub G (trRep σ P),
      ⟪B (σ g u), B (σ g w)⟫_ℂ = ⟪B u, B w⟫_ℂ) →
      ∀ i : UJset ε, ∀ w ∈ smSub G (trRep σ P), ‖B (σ i.1 w)‖ = ‖B w‖ := by
    intro B hB i w hw
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) (B w), hB i.1 i.2 w hw w hw]
  have hrep := hσ.1
  obtain ⟨c, hc⟩ := GlobalTheory.T.schur_inner_eq_pair_closable_normInvariant (UJset ε) H (Lp ℂ 2 ν) (fun i => σ i.1) (smSub G (trRep σ P))
    (fun i v => hσ.2.1 i.1 i.2 v)
    (fun i => by
      obtain ⟨hj, hl, hr⟩ := jm_conjTranspose_jm_mem_and_inverse i.2
      refine ⟨⟨_, hj⟩, fun v => ?_, fun v => ?_⟩
      · show σ _ (σ i.1 v) = v
        rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ hj _ i.2, hl, hrep.1,
          ContinuousLinearMap.one_apply]
      · show σ i.1 (σ _ v) = v
        rw [← ContinuousLinearMap.comp_apply, ← hrep.2 _ i.2 _ hj, hr, hrep.1,
          ContinuousLinearMap.one_apply])
    (fun S hS hS' => hirr S hS (fun g hg v hv => hS' ⟨g, hg⟩ v hv))
    (fun i v hv => hmem i.1 i.2 v hv)
    A A' (hnorm A hAinv) (hnorm A' hA'inv) (fun i w hw => hxinv i.1 i.2 w hw w hw) hcl hcl'
  exact ⟨c, fun w hw w' hw' => by rw [← l2_inner_of_ae (hA w hw) (hA' w' hw')]; exact hc w hw w' hw'⟩

end GlobalTheory.SmVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceTransvectionActsPositivelyInvariantForStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceTransvection_acts_positively_invariant_forms : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ ξ, IsoVec T ξ → ∀ e, IsSplitIdem D e → ∀ z ∈ ZI T ξ, Formalism.L2.Theta.SuppAt e T z → ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ a f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T (along S T ξ a) f) = ℓ f) → ∀ f, IsThetaFunO ψ S T f → ℓ (om (1, z) f) = (r : ℂ) * ℓ f := by
  first | exact @GlobalTheory.SplitTransvection.transvection_pos | exact GlobalTheory.SplitTransvection.transvection_pos | (intros; apply GlobalTheory.SplitTransvection.transvection_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRationalPointMatrixHomSurjectiveOntoStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRationalPointMatrixHom_surjective_onto : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γ₀ : GL (Fin n) L), γ₀ ∈ GQ0 L n →
    ∃ γ : GQ L n, GlobalTheory.AlgWtF.ratHom γ = γ₀ := by
  first | exact @GlobalTheory.AlgWtF.ratHom_surjective | exact GlobalTheory.AlgWtF.ratHom_surjective | (intros; apply GlobalTheory.AlgWtF.ratHom_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightActionMatrixCoeffPolynomialInEntriesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightAction_matrixCoeff_polynomial_in_entries : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (F : Formalism.L2.DIV.Pol K ι n)
    (ψ : Formalism.L2.DIV.Pol K ι n →ₗ[K] K), ∃ P : MvPolynomial ((ι ⊕ ι) × Fin n × Fin n) K, ∀ g : ι → GL (Fin n) K,
    ψ (Formalism.L2.DIV.actP lam g F) = MvPolynomial.eval (fun v : (ι ⊕ ι) × Fin n × Fin n =>
      Sum.elim (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2)
        (fun τ => (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) v.2.2 v.2.1) v.1) P := by
  first | exact @GlobalTheory.ActPolyCoeff.polyAction_coeff_poly | exact GlobalTheory.ActPolyCoeff.polyAction_coeff_poly | (intros; apply GlobalTheory.ActPolyCoeff.polyAction_coeff_poly <;> assumption)
end

