import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpDoubledGramDoublingThetaTensor
section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.DblHeis
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_fin_add_add {M : Type} [AddCommMonoid M] {n : ℕ} (f : Fin (n + n) → M) :
    ∑ d, f d = ∑ d, f (finSumFinEquiv (Sum.inl d)) + ∑ d, f (finSumFinEquiv (Sum.inr d)) := by
  rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]

theorem hOF_dblG (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS (nT + nT)) :
    hOF σ JS (dblG JT) x y = hOF σ JS JT (topR x) (topR y) - hOF σ JS JT (botR x) (botR y) := by
  simp only [hOF, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [sum_fin_add_add (n := nT), dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, dbl,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, map_zero, map_neg, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add,
    mul_neg, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, topR, botR, Function.comp_apply, id, Finset.sum_sub_distrib]
  ring

theorem hOF_neg_neg (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS nT) : hOF σ JS JT (-x) (-y) = hOF σ JS JT x y := by
  simp only [hOF, Matrix.neg_apply, map_neg, mul_neg, neg_mul, neg_neg]

theorem symplOHF_dblG (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (x y : WOF F E nS (nT + nT)) :
    symplOHF σ JS (dblG JT) ξ₀ x y =
      symplOHF σ JS JT ξ₀ (topR x) (topR y) - symplOHF σ JS JT ξ₀ (-botR x) (-botR y) := by
  simp only [symplOHF, symplOF, hOF_dblG, hOF_neg_neg, mul_sub, map_sub]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (h : ∀ x, ‖ψ x‖ = 1) (s : AF F) : conj (ψ s) = ψ (-s) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h s]
  simp

theorem heisOF_dblG_deltaT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (w : Formalism.IndefR.DatumF.WOF F E nS (nT + nT)) (f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ w (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) =
          GlobalTheory.DblTargetDelta.deltaT (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (GlobalTheory.DblTargetDelta.topR w) f₁)
            (Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (-GlobalTheory.DblTargetDelta.botR w) f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ w f₁ f₂
  have hn : ∀ x, ‖B.ψ x‖ = 1 := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1.2.1
  funext x
  have ht : topR (x + w) = topR x + topR w := rfl
  have hb : -botR (x + w) = -botR x + -botR w := by
    rw [← neg_add]; rfl
  simp only [heisOF, deltaT_apply, ht, hb, symplOHF_dblG, map_mul, conj_psi hn, sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

end GlobalTheory.DblHeis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelOperatorAtSumSmulLeibniz
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.DelForm

theorem coefwise_del_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {v : V n} (g : ι → V n → ℂ) (Q : ι → V n → Alt n)
    (hg : ∀ k, DifferentiableAt ℝ (g k) v) (hQ : ∀ k S, DifferentiableAt ℝ (fun w => (bas n).repr (Q k w) S) v)
    (ξ : V n) :
    coefwise (fun f => del f v ξ) (fun w => ∑ k, g k w • Q k w) =
      ∑ k, (del (g k) v ξ • Q k v + g k v • coefwise (fun f => del f v ξ) (Q k)) := by
  refine (bas n).ext_elem fun S => ?_
  have e : (fun x => (bas n).repr (∑ k, g k x • Q k x) S) = fun x => ∑ k, g k x * (bas n).repr (Q k x) S :=
    funext fun x => by simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [FormMul.repr_coefwise, e,
    del_sum (A := fun k x => g k x * (bas n).repr (Q k x) S) (fun k _ => (hg k).mul (hQ k S)),
    ContinuousLinearMap.sum_apply, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [del_mul (hg k) (hQ k S), map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    FormMul.repr_coefwise, smul_eq_mul, smul_eq_mul, add_comm]

theorem delAt_sum_smul : ∀ {n : ℕ} {ι : Type} [Fintype ι] {v : ReciprocityTheory.L2DbarEstimates.V n} (g : ι → ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (Q : ι → ReciprocityTheory.L2DbarEstimates.V n → GlobalTheory.CxForm.Alt n), (∀ k, DifferentiableAt ℝ (g k) v) →
    (∀ k S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (Q k w) S) v) →
    GlobalTheory.CxForm.delAt (fun w => ∑ k, g k w • Q k w) v =
      ∑ k, (GlobalTheory.CxForm.DelForm.dOne (g k) v * Q k v + g k v • GlobalTheory.CxForm.delAt (Q k) v) := by
  intro n ι _ v g Q hg hQ
  simp only [delAt, dOne, coefwise_del_sum_smul g Q hg hQ, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, mul_add,
    mul_smul_comm, smul_mul_assoc, ← Finset.sum_add_distrib]
  exact Finset.sum_comm

end GlobalTheory.CxForm.DelForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDifferentialOneFormCompHolomorphic
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

theorem sum_coord_smul_coordVec {n : ℕ} (w : V n) : ∑ b, w b • coordVec b = w := by
  ext i
  simp [coordVec, EuclideanSpace.single_apply, Pi.single_apply]

theorem dOne_comp_holo {n : ℕ} {φ : V n → V n} {c : V n → ℂ} {v : V n}
    (hc : DifferentiableAt ℝ c (φ v)) (hφ : DifferentiableAt ℂ φ v) :
    dOne (fun w => c (φ w)) v = pull (fderiv ℂ φ v) (dOne c (φ v)) := by
  have key (a : Fin n) : del (fun w => c (φ w)) v (coordVec a) =
      ∑ b, fderiv ℂ φ v (coordVec a) b * del c (φ v) (coordVec b) := by
    rw [del_comp_holo hc hφ]
    conv_lhs => rw [← sum_coord_smul_coordVec (fderiv ℂ φ v (coordVec a))]
    simp [map_sum, map_smul, smul_eq_mul]
  simp only [dOne, map_sum, map_smul, (pull_dz _ _).1, Finset.smul_sum, smul_smul, key, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

end GlobalTheory.CxForm.DelForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTorsionUnramifiedOfTateModuleUnramified
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbVarRed

theorem natCast_ne_zero_of_residue {R K : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {m : ℕ} (h : (m : ResidueField R) ≠ 0) : (m : K) ≠ 0 := by
  intro h0
  apply h
  have h1 : (m : R) = 0 := IsFractionRing.injective R K (by rw [map_natCast, map_zero, h0])
  rw [← map_natCast (residue R), h1, map_zero]

theorem torsionUnramified_pow_of_tateUnramified {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
    {V : ValuationSubring Ω} {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {l : ℕ} [Fact l.Prime] (hl : (l : K) ≠ 0) (h : TateUnramified A V l) (n : ℕ) :
    TorsionUnramified A V (l ^ n) := by
  intro σ hσ x hx
  obtain ⟨t, rfl⟩ := GlobalTheory.T.tateModule_level_surjective_of_divisible l (ptOver K Ω ⟶ A) (GlobalTheory.T.abelianVariety_sepClosed_point_divisible K Ω A hA l hl) n x hx
  rw [← lev_galTate, h σ hσ]
  rfl

theorem infinite_torsionUnramified_of_tateUnramified :
    ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
      [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
      (V : ValuationSubring Ω), IsAbove R K V.toSubring →
      ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
      ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 → TateUnramified A V l →
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite := by
  intro R K Ω _ _ _ _ _ _ _ _ _ _ V _ A _ _ hA l hp hl h
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => l ^ n)
    (Nat.pow_right_injective hp.out.two_le) fun n => ⟨?_, ?_⟩
  · rw [Nat.cast_pow]
    exact pow_ne_zero _ hl
  · exact torsionUnramified_pow_of_tateUnramified hA (natCast_ne_zero_of_residue hl) h n

end GlobalTheory.AbVarRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDegreeOfNormBound
section
set_option autoImplicit false

namespace GlobalTheory.DegCmp

open Polynomial

theorem le_sqrt_mul_pow_of_sq_le {n : ℕ} (τ : ℕ) (x y C : ℝ) (u : Fin n → ℝ) (hx : 0 ≤ x) (hu : ∀ i, 0 ≤ u i)
    (h : y ^ 2 ≤ C * (∑ i, u i ^ 2) ^ τ) :
    x ^ τ * y ≤ Real.sqrt (max C 0) * (1 + ∑ i, x * u i) ^ τ := by
  have hS : 0 ≤ ∑ i, u i := Finset.sum_nonneg fun i _ => hu i
  have h1 : ∑ i, u i ^ 2 ≤ (∑ i, u i) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => hu i
  have h0 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : y ^ 2 ≤ (Real.sqrt (max C 0) * (∑ i, u i) ^ τ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_max_right _ _), ← pow_mul, mul_comm τ 2, pow_mul]
    exact h.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ h0 h1 τ) (pow_nonneg h0 τ) (le_max_right _ _))
  have h3 : y ≤ Real.sqrt (max C 0) * (∑ i, u i) ^ τ :=
    (abs_le_of_sq_le_sq' h2 (by positivity)).2
  calc x ^ τ * y ≤ x ^ τ * (Real.sqrt (max C 0) * (∑ i, u i) ^ τ) := by gcongr
    _ = Real.sqrt (max C 0) * (∑ i, x * u i) ^ τ := by rw [← Finset.mul_sum, mul_pow]; ring
    _ ≤ Real.sqrt (max C 0) * (1 + ∑ i, x * u i) ^ τ := by
      have : 0 ≤ ∑ i, x * u i := Finset.sum_nonneg fun i _ => mul_nonneg hx (hu i)
      gcongr
      linarith

theorem isIntDeg_of_bounded_of_algHom (K V Ω R : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] (ι : R →ₐ[K] Ω) (σ : K →+* ℂ) (a : Ωˣ) (n τ : ℕ) (w : Fin n → V)
    (w' : Fin n → R) (t : Ω) (t' : R) (C : ℝ) (hw : ∀ i, ι (w' i) = (a : Ω) * ev (w i))
    (ht : ι t' = (a : Ω) ^ τ * t)
    (hb : ∀ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ → ‖φ t'‖ ^ 2 ≤ C * (∑ i, ‖φ (w' i)‖ ^ 2) ^ τ) :
    IsIntDeg ev τ t := by
  have hint : IsIntegral (Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R)))
      (X ^ τ * Polynomial.C t' : Polynomial R) := by
    refine GlobalTheory.T.cone_degree_growth_chowForm_integrality.2.2.2 K (Polynomial R) σ n τ _ _ (Real.sqrt (max C 0)) fun φ hφ => ?_
    have h := hb (φ.comp Polynomial.C) hφ
    simp only [map_mul, map_pow, norm_mul, norm_pow]
    exact le_sqrt_mul_pow_of_sq_le τ _ _ C (fun i => ‖φ (Polynomial.C (w' i))‖) (norm_nonneg _)
      (fun _ => norm_nonneg _) h
  let f : Polynomial R →ₐ[K] Polynomial Ω :=
    Polynomial.eval₂AlgHom ((Polynomial.CAlgHom : Ω →ₐ[K] Polynomial Ω).comp ι) (X * Polynomial.C ((a⁻¹ : Ωˣ) : Ω))
      fun _ => Commute.all _ _
  have hfX : f X = X * Polynomial.C ((a⁻¹ : Ωˣ) : Ω) := by simp [f]
  have hfC : ∀ b : R, f (Polynomial.C b) = Polynomial.C (ι b) := fun b => by simp [f]
  have hfw : ∀ i, f (X * Polynomial.C (w' i)) = X * Polynomial.C (ev (w i)) := fun i => by
    rw [map_mul, hfX, hfC, hw, mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul]
  have hft : f (X ^ τ * Polynomial.C t') = X ^ τ * Polynomial.C t := by
    rw [map_mul, map_pow, hfX, hfC, ht, mul_pow, mul_assoc, ← map_pow, ← map_mul, ← mul_assoc, ← mul_pow,
      Units.inv_mul, one_pow, one_mul]
  have hmem : ∀ x ∈ Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R)), f x ∈ coneAlg ev := by
    intro x hx
    have : Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R)) ≤ (coneAlg ev).comap f := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨i, rfl⟩
      change f _ ∈ coneAlg ev
      rw [hfw]
      exact Algebra.subset_adjoin ⟨w i, rfl⟩
    exact this hx
  rw [IsIntDeg, ← hft]
  exact hint.map_of_comp_eq
    ((f.toRingHom.comp (Algebra.adjoin K (Set.range fun i => (X * Polynomial.C (w' i) : Polynomial R))).val.toRingHom).codRestrict
      (coneAlg ev) fun x => hmem x.1 x.2) f.toRingHom (RingHom.ext fun _ => rfl)

theorem isIntDeg_of_bounded (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (R : Subalgebra K Ω) [Algebra.FiniteType K R] (σ : K →+* ℂ) (a : Ωˣ) (n τ : ℕ) (w : Fin n → V)
    (w' : Fin n → R) (t : Ω) (t' : R) (C : ℝ) (hw : ∀ i, (w' i : Ω) = (a : Ω) * ev (w i))
    (ht : (t' : Ω) = (a : Ω) ^ τ * t)
    (hb : ∀ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ → ‖φ t'‖ ^ 2 ≤ C * (∑ i, ‖φ (w' i)‖ ^ 2) ^ τ) :
    IsIntDeg ev τ t :=
  isIntDeg_of_bounded_of_algHom K V Ω R ev R.val σ a n τ w w' t t' C hw ht hb

end GlobalTheory.DegCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelFnMulEqZeroOfIsForm
section
set_option autoImplicit false

noncomputable section

open Set Filter Topology Matrix MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem dens_zero : dens (0 : Alt n) = 0 := by simp [dens]

theorem delAt_eq_zero_of_eventually {F : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] fun _ => 0) : delAt F v = 0 := by
  have hS : ∀ S, GlobalTheory.del (fun x => (bas n).repr (F x) S) v = 0 := fun S => by
    have e : (fun x => (bas n).repr (F x) S) =ᶠ[𝓝 v] fun _ => 0 := h.mono fun x hx => by simp [hx]
    rw [GlobalTheory.del_congr e]
    exact GlobalTheory.del_const _ _
  simp [delAt, coefwise, hS]

theorem del_integral {f : V n → ℂ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (u : V n) :
    Integrable (fun v => GlobalTheory.del f v u) ∧ ∫ v, GlobalTheory.del f v u = 0 := by
  have hint : ∀ w : V n, Integrable (fun y => fderiv ℝ f y w) := fun w =>
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply (𝕜 := ℝ) w)
  have hD : Integrable (fun v => GlobalTheory.del f v u) := by
    simp only [GlobalTheory.del_apply, smul_eq_mul]
    exact ((hint _).sub ((hint _).const_mul _)).const_mul _
  refine ⟨hD, ?_⟩
  simp only [GlobalTheory.del_apply, smul_eq_mul]
  rw [integral_const_mul, integral_sub (hint _) ((hint _).const_mul _), integral_const_mul,
    ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n f hf hc, ReciprocityTheory.L2DbarEstimates.integral_fderiv_apply_eq_zero n f hf hc]
  simp

theorem dens_delAt (F : V n → Alt n) (v : V n) : dens (delAt F v) =
    ∑ a, ∑ S, GlobalTheory.del (fun x => (bas n).repr (F x) S) v (coordVec a) *
      ((bas n).repr (dz a * bas n S) Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ) := by
  simp only [dens, delAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Finset.sum_div, mul_div_assoc]

theorem integral_dens_delAt {F : V n → Alt n} (hF : ∀ S, ContDiff ℝ 1 fun v => (bas n).repr (F v) S)
    (hc : ∀ S, HasCompactSupport fun v => (bas n).repr (F v) S) :
    Integrable (fun v => dens (delAt F v)) ∧ ∫ v, dens (delAt F v) = 0 := by
  have hi : ∀ a S, Integrable fun v => GlobalTheory.del (fun x => (bas n).repr (F x) S) v (coordVec a) *
      ((bas n).repr (dz a * bas n S) Finset.univ / (bas n).repr (vol n : Alt n) Finset.univ) :=
    fun a S => (del_integral (hF S) (hc S) _).1.mul_const _
  simp only [dens_delAt]
  refine ⟨integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun S _ => hi a S, ?_⟩
  rw [integral_finset_sum _ fun a _ => integrable_finset_sum _ fun S _ => hi a S]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finset_sum _ fun S _ => hi a S]
  refine Finset.sum_eq_zero fun S _ => ?_
  rw [integral_mul_const, (del_integral (hF S) (hc S) _).2, zero_mul]

end GlobalTheory.CxForm.LocStokes

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem integral_eq_of_vanish {M : Type} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
    [BorelSpace M] (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α) (i : A.ι) {K : Set M} (hKm : MeasurableSet K)
    (hKs : K ⊆ (A.e i).source) (h0 : ∀ x : A.Pt, x.pt ∉ K → α x = 0)
    (hI : Integrable fun v => (dens (A.loc α i v)).re) :
    A.integral α = ∫ v, (dens (A.loc α i v)).re := by
  have hl : ∀ j y (hy : y ∈ (A.e j).source), A.loc α j (A.e j y) = α ⟨(j, y), hy⟩ := fun j y hy =>
    A.loc_crd α ⟨(j, y), hy⟩
  have hρ : ∀ (ε : ℤˣ) j k y, y ∈ (A.e j).source → y ∈ (A.e k).source →
      ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re) =
      ENNReal.ofReal (‖ChartGlue.transDet (A.e j) (A.e k) y‖ ^ 2) *
        ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α k (A.e k y))).re) := by
    intro ε j k y hj hk
    rw [hl j y hj, hl k y hk, hα.compat ⟨(j, y), hj⟩ ⟨(k, y), hk⟩ rfl, dens_pull,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    simp only [ChartGlue.transDet, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hz : ∀ (ε : ℤˣ) j y, y ∈ (A.e j).source → y ∉ K →
      ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re) = 0 := by
    intro ε j y hy hyK
    rw [hl j y hy, h0 ⟨(j, y), hy⟩ hyK, dens_zero]
    simp
  have hc : ∀ ε : ℤˣ, A.part α ε Kᶜ = 0 := fun ε => by
    have key : A.part α ε ≤ (A.part α ε).restrict K := iSup_le fun j => by
      have e : ChartGlue.chartMeas (A.e j)
          (fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re)) Kᶜ = 0 := by
        rw [ChartGlue.chartMeas_apply _ _ hKm.compl]
        refine setLIntegral_eq_zero (ChartGlue.measurableSet_image _
          ((A.e j).open_source.measurableSet.inter hKm.compl) Set.inter_subset_left) ?_
        rintro _ ⟨y, hy, rfl⟩
        simp only [(A.e j).left_inv hy.1]
        exact hz ε j y hy.1 hy.2
      rw [← Measure.restrict_eq_self_of_ae_mem (s := K) (mem_ae_iff.2 e)]
      exact Measure.restrict_mono le_rfl (le_iSup (fun j => ChartGlue.chartMeas (A.e j)
        fun y => ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α j (A.e j y))).re)) j)
    refine le_antisymm ((key Kᶜ).trans_eq ?_) bot_le
    rw [Measure.restrict_apply hKm.compl, Set.compl_inter_self, measure_empty]
  have hv : ∀ v, v ∉ (A.e i) '' K → (dens (A.loc α i v)).re = 0 := fun v hv => by
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dif_pos ht, h0 ⟨(i, (A.e i).symm v), (A.e i).map_target ht⟩
        fun h => hv ⟨_, h, (A.e i).right_inv ht⟩, dens_zero, Complex.zero_re]
    · rw [HolAtlas.loc, dif_neg ht, dens_zero, Complex.zero_re]
  have hp : ∀ ε : ℤˣ, A.part α ε univ = ∫⁻ v, ENNReal.ofReal ((ε : ℤ) * (dens (A.loc α i v)).re) := fun ε => by
    rw [← measure_add_measure_compl hKm, hc ε, add_zero, HolAtlas.part,
      ChartGlue.glueMeas_apply A.e _ (fun j k => A.holo j k) (hρ ε) i hKm hKs,
      ChartGlue.chartMeas_apply_of_subset _ _ hKm hKs,
      ← lintegral_indicator (ChartGlue.measurableSet_image _ hKm hKs)]
    refine lintegral_congr fun v => ?_
    by_cases hvK : v ∈ (A.e i) '' K
    · obtain ⟨y, hy, rfl⟩ := hvK
      rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hy), (A.e i).left_inv (hKs hy)]
    · rw [Set.indicator_of_notMem hvK, hv v hvK, mul_zero, ENNReal.ofReal_zero]
  rw [HolAtlas.integral, measureReal_def, measureReal_def, hp, hp,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI]
  simp

end GlobalTheory.CxForm.LocStokes

namespace GlobalTheory.CxForm.LocStokes

open GlobalTheory.CxForm

variable {n : ℕ}

theorem integral_del_fn_mul_eq_zero_of_isForm {M : Type} [TopologicalSpace M] [CompactSpace M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (A : HolAtlas M n) (γ : A.Fld) (χ : M → ℝ)
    (i : A.ι) (hγ : A.IsForm γ) (hχ : A.SmoothOn univ (fun y => (χ y : ℂ))) (hs : tsupport χ ⊆ (A.e i).source)
    (hd : A.IsForm (A.del (A.fn χ * γ))) : A.integral (A.del (A.fn χ * γ)) = 0 := by
  set β : A.Fld := A.fn χ * γ with hβdef
  set K : Set M := tsupport χ with hKdef
  have hKc : IsCompact K := (isClosed_tsupport χ).isCompact
  have hKm : MeasurableSet K := (isClosed_tsupport χ).measurableSet
  have hβ : A.IsForm β := FormMul.isForm_mul A _ _ (A.isForm_fn hχ) hγ
  have hβ0 : ∀ x : A.Pt, x.pt ∉ K → β x = 0 := fun x hx => by
    simp [hβdef, HolAtlas.fn, image_eq_zero_of_notMem_tsupport hx]

  have hβn : ∀ j, ∀ y ∈ (A.e j).source, y ∉ K → A.loc β j =ᶠ[𝓝 (A.e j y)] fun _ => 0 := fun j y hy hyK => by
    filter_upwards [(ChartGlue.isOpen_over (A.e j) (isClosed_tsupport χ).isOpen_compl).mem_nhds
      (ChartGlue.mem_over (A.e j) (S := Kᶜ) hy hyK)] with w hw
    rw [HolAtlas.loc, dif_pos hw.1]
    exact hβ0 _ hw.2
  have hd0 : ∀ x : A.Pt, x.pt ∉ K → A.del β x = 0 := fun x hx =>
    delAt_eq_zero_of_eventually (hβn x.1.1 x.pt x.2 hx)

  set F : V n → Alt n := A.loc β i with hFdef
  set AK : Set (V n) := (A.e i) '' K with hAKdef
  have hAK : IsCompact AK := hKc.image_of_continuousOn ((A.e i).continuousOn.mono hs)
  have hAKt : AK ⊆ (A.e i).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e i).map_source (hs hy)
  have hF0 : ∀ v ∉ AK, F v = 0 := fun v hv => by
    by_cases ht : v ∈ (A.e i).target
    · rw [hFdef, HolAtlas.loc, dif_pos ht]
      exact hβ0 _ fun h => hv ⟨_, h, (A.e i).right_inv ht⟩
    · rw [hFdef, HolAtlas.loc, dif_neg ht]
  have hFA : ∀ v ∉ AK, F =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hAK.isClosed.isOpen_compl.mem_nhds hv] with w hw
    exact hF0 w hw
  have hFS : ∀ S, ContDiff ℝ 1 fun v => (bas n).repr (F v) S := fun S => contDiff_iff_contDiffAt.2 fun v => by
    by_cases ht : v ∈ (A.e i).target
    · exact ((hβ.smooth i S).contDiffAt ((A.e i).open_target.mem_nhds ht)).of_le (by simp)
    · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ((hFA v fun h => ht (hAKt h)).mono fun w hw => ?_)
      simp [hw]
  have hFc : ∀ S, HasCompactSupport fun v => (bas n).repr (F v) S := fun S =>
    HasCompactSupport.intro hAK fun v hv => by simp [hF0 v hv]
  have hloc : ∀ v, A.loc (A.del β) i v = delAt F v := fun v => by
    by_cases ht : v ∈ (A.e i).target
    · rw [HolAtlas.loc, dif_pos ht]
      show delAt (A.loc β i) ((A.e i) ((A.e i).symm v)) = _
      rw [(A.e i).right_inv ht]
    · rw [HolAtlas.loc, dif_neg ht]
      exact (delAt_eq_zero_of_eventually (hFA v fun h => ht (hAKt h))).symm
  obtain ⟨hI, h0⟩ := integral_dens_delAt hFS hFc
  have hIre : Integrable fun v => (dens (A.loc (A.del β) i v)).re := by
    simp only [hloc]
    exact Complex.reCLM.integrable_comp hI
  rw [integral_eq_of_vanish A hd i hKm hs hd0 hIre]
  simp only [hloc]
  have := Complex.reCLM.integral_comp_comm hI
  simp only [Complex.reCLM_apply] at this
  rw [this, h0, Complex.zero_re]

end GlobalTheory.CxForm.LocStokes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqEuclideanIntegralOfSupportInChartStatement
section
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_eq_euclidean_integral_of_support_in_chart : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld) (i : A.ι) (K : Set M), A.IsForm α → IsCompact K → K ⊆ (A.e i).source → (∀ x : A.Pt, x.pt ∉ K → α x = 0) → A.integral α = ∫ v, (GlobalTheory.CxForm.dens (A.loc α i v)).re := by
  first | exact @GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support | exact GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support | (intros; apply GlobalTheory.CxForm.HolAtlas.integral_eq_integral_chart_of_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralTwistedComparisonAtFixedSectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_twisted_comparison_at_fixed_section : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) (σ : K' ≃+* K') (τ : W →+* W), (∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l) → ∀ (φ : G.left ⟶ G.left) (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → e₀ ≫ φ = spMap τ ≫ e₀ → ∀ (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))) (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ ρ = spMap (σ : K' →+* K') ≫ x → ∀ (M : LB G.left) (N : LB (pullback G.hom (spMap (algebraMap W K')))), M.IsLB → N.IsLB → ∀ (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) N) (w₁ : LB.Iso ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))) N), (∀ (n : N.ι) (i : ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).ι) (h : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ ((M.pull φ).pull (pullback.fst G.hom (spMap (algebraMap W K')))).U i)) (h' : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))).U (fun _ => i PUnit.unit PUnit.unit))), (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h).hom (w₁.s (n, i)).val) = σ ((Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h').hom (w.s (n, fun _ => i PUnit.unit PUnit.unit)).val))) → GlobalTheory.SectionLattice.IntegralAtSection G.hom w w₁ := by
  first | exact @GlobalTheory.SectionLattice.integralAtSection_of_conj | exact GlobalTheory.SectionLattice.integralAtSection_of_conj | (intros; apply GlobalTheory.SectionLattice.integralAtSection_of_conj <;> assumption)
end

