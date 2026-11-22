import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0033
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0043
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1910
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0302
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0011
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0372
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0365

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearModelFourierTransformExchange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.LinearModelFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def flat (n r : ℕ) : Matrix (Fin n) (Fin r) k ≃ₜ (Fin n × Fin r → k) where
  toFun z p := z p.1 p.2
  invFun y := Matrix.of (Function.curry y)
  left_inv z := rfl
  right_inv y := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

def flatT (n r : ℕ) : Matrix (Fin r) (Fin n) k ≃ₜ (Fin n × Fin r → k) where
  toFun x p := x p.2 p.1
  invFun y := Matrix.of fun j i => y (i, j)
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.1).comp (continuous_apply p.2)
  continuous_invFun := continuous_pi fun j => continuous_pi fun i => continuous_apply (i, j)

theorem trace_mul_eq_dotProduct {n r : ℕ} (x : Matrix (Fin r) (Fin n) k) (y : Matrix (Fin n) (Fin r) k) :
    trace (x * y) = flat n r y ⬝ᵥ flatT n r x := by
  simp only [trace, diag, mul_apply, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show x j i * y i j = y i j * x j i
  ring

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : Y ≃ₜ X) {f : X → ℂ}
    (hf : f ∈ GlobalTheory.SplitWeil.SB X) : (f ∘ e) ∈ GlobalTheory.SplitWeil.SB Y :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

variable [MeasurableSpace k]

def fou (ψ : AddChar k Circle) (ν : Measure k) (n r : ℕ) (Φ : Matrix (Fin n) (Fin r) k → ℂ)
    (x : Matrix (Fin r) (Fin n) k) : ℂ :=
  ∫ y, Φ y * (ψ (trace (x * y)) : ℂ) ∂(volM ν (Fin n) (Fin r))

variable [BorelSpace k] {ψ : AddChar k Circle} (ν : Measure k) [ν.IsAddHaarMeasure] {n r : ℕ}

theorem fou_eq_pi (Φ : Matrix (Fin n) (Fin r) k → ℂ) (x : Matrix (Fin r) (Fin n) k) :
    fou ψ ν n r Φ x = ∫ z, (Φ ∘ (flat n r).symm) z * (ψ (z ⬝ᵥ flatT n r x) : ℂ) ∂(Measure.pi fun _ => ν) := by
  rw [fou, integral_volM_eq_pi]
  congr 1
  funext z
  rw [trace_mul_eq_dotProduct]
  rfl

theorem integrable_fou (hψ : Continuous ψ) {f : Matrix (Fin n) (Fin r) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin n) (Fin r) k)) (x : Matrix (Fin r) (Fin n) k) :
    Integrable (fun y => f y * (ψ (trace (x * y)) : ℂ)) (volM ν (Fin n) (Fin r)) := by
  haveI := secondCountable k
  letI : MeasurableSpace (Matrix (Fin n) (Fin r) k) := GlobalTheory.SplitWeil.matrixMeasurableSpace
  haveI : BorelSpace (Matrix (Fin n) (Fin r) k) := inferInstanceAs (BorelSpace (Fin n → Fin r → k))
  haveI : (volM ν (Fin n) (Fin r)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : IsFiniteMeasureOnCompacts (volM ν (Fin n) (Fin r)) := inferInstance
  have hc : Continuous fun y : Matrix (Fin n) (Fin r) k => f y * (ψ (trace (x * y)) : ℂ) :=
    hf.1.continuous.mul (continuous_subtype_val.comp
      (hψ.comp ((continuous_const.matrix_mul continuous_id).matrix_trace)))
  exact hc.integrable_of_hasCompactSupport (μ := volM ν (Fin n) (Fin r)) hf.2.mul_right

theorem fou_mem (hψ : Continuous ψ) (h1 : ψ ≠ 1) {f : Matrix (Fin n) (Fin r) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin n) (Fin r) k)) : fou ψ ν n r f ∈ SB (Matrix (Fin r) (Fin n) k) := by
  haveI := secondCountable k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ h1
  have h2 := FourierPi.fourier_mem_SB (Measure.pi fun _ : Fin n × Fin r => ν) hc
    (comp_mem_SB (flat n r).symm hf)
  have h3 : fou ψ ν n r f = (fun y => ∫ z, (f ∘ (flat n r).symm) z * (ψ (z ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => ν)) ∘ flatT n r := funext fun x => fou_eq_pi ν f x
  rw [h3]
  exact comp_mem_SB _ h2

theorem nabs_det_inv {m : ℕ} (g : GL (Fin m) k) :
    nabs k (Matrix.GeneralLinearGroup.det g⁻¹) = (nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ := by
  simp [nabs, map_inv]

theorem fou_om (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ : Matrix (Fin n) (Fin r) k → ℂ) :
    fou ψ ν n r (om μ hk gk Φ) = om μ⁻¹ gk hk (fou ψ ν n r Φ) := by
  funext x
  set F : Matrix (Fin n) (Fin r) k → ℂ :=
    fun z => Φ z * (ψ (trace (((hk⁻¹ : GL (Fin r) k).val * x * gk.val) * z)) : ℂ) with hF
  have key := integral_comp_mul_mul_volM ν hk gk⁻¹ F
  have htr : ∀ y : Matrix (Fin n) (Fin r) k,
      trace ((hk⁻¹ : GL (Fin r) k).val * x * gk.val * ((gk⁻¹ : GL (Fin n) k).val * y * hk.val)) =
        trace (x * y) := by
    intro y
    have e : (hk⁻¹ : GL (Fin r) k).val * x * gk.val * ((gk⁻¹ : GL (Fin n) k).val * y * hk.val) =
        (hk⁻¹ : GL (Fin r) k).val * (x * y * hk.val) := by
      calc _ = (hk⁻¹ : GL (Fin r) k).val * (x * (gk.val * (gk⁻¹ : GL (Fin n) k).val) * y * hk.val) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Units.mul_inv, Matrix.mul_one]
    rw [e, trace_mul_comm]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  set A : ℂ := (μ (Matrix.GeneralLinearGroup.det hk) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) *
    ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ (-(Fintype.card (Fin r) : ℝ) / 2) : ℝ) : ℂ) with hA
  have lhs : fou ψ ν n r (om μ hk gk Φ) x =
      A * ∫ y, F ((gk⁻¹ : GL (Fin n) k).val * y * hk.val) ∂(volM ν (Fin n) (Fin r)) := by
    rw [fou, ← integral_const_mul]
    congr 1
    funext y
    simp only [om, hF, htr, hA]
    ring
  have hFint : ∫ z, F z ∂(volM ν (Fin n) (Fin r)) =
      fou ψ ν n r Φ ((hk⁻¹ : GL (Fin r) k).val * x * gk.val) := rfl
  rw [lhs, key, hFint, nabs_det_inv]
  simp only [om, hA, MonoidHom.inv_apply, inv_inv, Complex.real_smul, Fintype.card_fin]
  set a := nabs k (Matrix.GeneralLinearGroup.det gk) with ha
  set b := nabs k (Matrix.GeneralLinearGroup.det hk) with hb
  have ha0 : 0 < a := nabs_pos' _
  have hb0 : 0 < b := nabs_pos' _
  have h1 : ((b ^ ((n : ℝ) / 2) : ℝ) : ℂ) * ((b ^ (-(n : ℝ)) : ℝ) : ℂ) = ((b ^ (-(n : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hb0]
    ring_nf
  have h2 : ((a ^ (-(r : ℝ) / 2) : ℝ) : ℂ) * ((a⁻¹ ^ (-(r : ℝ)) : ℝ) : ℂ) = ((a ^ ((r : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Real.inv_rpow ha0.le, ← Real.rpow_neg ha0.le, neg_neg, ← Complex.ofReal_mul, ← Real.rpow_add ha0]
    ring_nf
  rw [Complex.ofReal_mul]
  linear_combination
    ((μ (Matrix.GeneralLinearGroup.det hk) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) *
      fou ψ ν n r Φ ((hk⁻¹ : GL (Fin r) k).val * x * gk.val)) *
    (((a ^ (-(r : ℝ) / 2) : ℝ) : ℂ) * ((a⁻¹ ^ (-(r : ℝ)) : ℝ) : ℂ) * h1 + ((b ^ (-(n : ℝ) / 2) : ℝ) : ℂ) * h2)

def fouL (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] SB (Matrix (Fin r) (Fin n) k) where
  toFun Φ := ⟨fou ψ ν n r Φ.1, fou_mem ν hψ h1 Φ.2⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    funext x
    show fou ψ ν n r (Φ.1 + Ψ.1) x = fou ψ ν n r Φ.1 x + fou ψ ν n r Ψ.1 x
    simp only [fou, Pi.add_apply, add_mul]
    exact integral_add (integrable_fou ν hψ Φ.2 x) (integrable_fou ν hψ Ψ.2 x)
  map_smul' c Φ := by
    apply Subtype.ext
    funext x
    show fou ψ ν n r (c • Φ.1) x = c * fou ψ ν n r Φ.1 x
    simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _

theorem fouL_surjective (hψ : Continuous ψ) (h1 : ψ ≠ 1) (hν : IsSelfDual ψ ν) :
    Function.Surjective (fouL (n := n) (r := r) ν hψ h1) := by
  intro G
  obtain ⟨Φ₀, hΦ₀⟩ := (FourierSurj.hat_surjective k (Fin n × Fin r) ψ hψ h1 ν hν).2
    ⟨_, comp_mem_SB (flatT n r).symm G.2⟩
  refine ⟨⟨Φ₀.1 ∘ flat n r, comp_mem_SB _ Φ₀.2⟩, Subtype.ext (funext fun x => ?_)⟩
  show fou ψ ν n r (Φ₀.1 ∘ flat n r) x = G.1 x
  have h2 := congrFun hΦ₀ (flatT n r x)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, Function.comp_apply, Homeomorph.symm_apply_apply] at h2
  rw [fou_eq_pi, ← h2]
  congr 1
  funext z
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply, dotProduct_comm z]

end GlobalTheory.LinearModelFourier

theorem GlobalTheory.linearModel_fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r : ℕ), ∃ τ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) k), Function.Surjective τ ∧ ∀ (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k)), Φ'.1 = GlobalTheory.SplitWeil.om μ hk gk Φ.1 → (τ Φ').1 = GlobalTheory.SplitWeil.om μ⁻¹ gk hk (τ Φ).1 := by
  intro k _ _ _ _ n r
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ψ, hψ, h1, -⟩ := (conductor_exists k).2.1
  obtain ⟨ν, hν⟩ := (selfDual_measure k ψ hψ h1).1
  haveI := hν.1
  refine ⟨GlobalTheory.LinearModelFourier.fouL ν hψ h1, GlobalTheory.LinearModelFourier.fouL_surjective ν hψ h1 hν,
    fun μ gk hk Φ Φ' hΦ => ?_⟩
  show GlobalTheory.LinearModelFourier.fou ψ ν n r Φ'.1 = om μ⁻¹ gk hk (GlobalTheory.LinearModelFourier.fou ψ ν n r Φ.1)
  rw [hΦ]
  exact GlobalTheory.LinearModelFourier.fou_om ν μ gk hk Φ.1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentUnitarisableTwist
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

section Trace

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem zc_eq_sum_Eop : zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := GlobalTheory.T.splitCentreDerivative_eq_sum_diagonalMatrixUnits E a

theorem sum_Eop_apply {π : CuspSub E a} {τ : E →+* ℂ} {m : Multiset ℂ} (h : π.HasInfChar τ m) {φ : Sm E a}
    (hφ : φ ∈ π.V) : (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := GlobalTheory.T.cuspidal_traceMatrixUnits_acts_by_sum_infinitesimalCharacter E a π τ m h φ hφ

theorem cex_eq (π : CuspSub E a) : cex (⟨a, π⟩ : Letter E) = ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum := by
  refine (letter_centralExponent E ⟨a, π⟩).2.2.2.2 _ ?_
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine ⟨φ, hφ, h0, ?_⟩
  change zc E a φ = _
  rw [zc_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun τ _ => sum_Eop_apply (ParLaws.hasInfChar_infChar (CG.mk π) τ) hφ

end Trace

end GlobalTheory.UnitLocWeight

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem sum_infChar_of_isWeight {π : CuspSub E a} {wt : ℤ} (h : IsWeight π wt) :
    ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum =
      (Module.finrank ℚ E : ℂ) * ((a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ))) / 2 := by
  set c : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hc : Function.Bijective fun τ : E →+* ℂ => τ.comp c := by
    refine Finite.injective_iff_bijective.1 fun τ τ' e => RingHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (IsCMField.complexConj E).surjective x
    exact RingHom.congr_fun e y
  have h1 : ∑ τ : E →+* ℂ, ((CG.mk π).infChar (τ.comp c)).sum = ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum :=
    Function.Bijective.sum_comp hc (fun τ => ((CG.mk π).infChar τ).sum)
  have h2 : ∀ τ : E →+* ℂ, ((CG.mk π).infChar (τ.comp c)).sum =
      (a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ)) - ((CG.mk π).infChar τ).sum := fun τ => by
    rw [h τ, Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, CG.card_infChar, Multiset.map_id',
      nsmul_eq_mul]
  have h3 := Embeddings.card E ℂ
  simp only [h2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, h3, nsmul_eq_mul] at h1
  linear_combination -h1 / 2

end GlobalTheory.UnitLocWeight

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

theorem rexp_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} {wt : ℤ}
    (h : IsWeight π wt) : rexp (⟨a, π⟩ : Letter E) = ((a : ℝ) - 1 - wt) / 2 := by
  have e := (cex_eq π).trans (sum_infChar_of_isWeight h)
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have e2 : (cex (⟨a, π⟩ : Letter E)).re = (Module.finrank ℚ E : ℝ) * ((a : ℝ) * ((a : ℝ) - 1 - wt)) / 2 := by
    rw [e]
    have : (Module.finrank ℚ E : ℂ) * ((a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ))) / 2 =
        (((Module.finrank ℚ E : ℝ) * ((a : ℝ) * ((a : ℝ) - 1 - wt)) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  unfold rexp
  change (cex (⟨a, π⟩ : Letter E)).re / ((a : ℝ) * Module.finrank ℚ E) = _
  rw [e2]
  field_simp

theorem main : AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (wt : ℤ), IsWeight π wt → ∀ (w : HeightOneSpectrum (𝓞 E)) σ, π.IsLocComp w σ →
      GlobalTheory.SmGL.IsUnitarisable ((algNorm σ).nu (((wt : ℝ) / 2 : ℝ) : ℂ)).rep := by
  intro _ E _ _ _ a ha π wt hw w σ hσ
  set t : ℝ := ((a : ℝ) - 1 - wt) / 2 with ht
  have hr := rexp_eq ha hw
  have hu : (π.twist (nu E (-t))).IsUnitary := by
    have e := (letter_centralExponent E ⟨a, π⟩).2.2.1 ha (-t)
    refine ((rexp_eq_zero_iff_isUnitary E (tw ⟨a, π⟩ (-t)) ha).1.1 ?_)
    rw [e, hr]; ring
  have hU := isUnitarisable_of_isLocComp_cusp E a _ ha hu w _ (hσ.twist (nu E (-t)))
  have hloc : (nu E (-t)).loc w = GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ) :=
    GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (-t)) w
  set σ' := σ.twist (CuspSub.locDet a (nu E (-t)) w) (CuspSub.isOpen_ker_locDet (nu E (-t)) w) with hσ'
  have key : (algNorm σ).nu (((wt : ℝ) / 2 : ℝ) : ℂ) = IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
    have e1 : (((1 - (a : ℝ)) / 2 : ℝ) : ℂ) + (((wt : ℝ) / 2 : ℝ) : ℂ) = ((-t : ℝ) : ℂ) := by
      rw [ht]; push_cast; ring
    unfold algNorm
    rw [IrrGL.nu_nu, e1]
    unfold IrrGL.nu
    rw [IrrGL.tw_of]
    refine IrrGL.of_eq_of.2 ⟨?_⟩
    have e2 : GlobalTheory.SmGL.twist σ.ρ (GlobalTheory.SmGL.detChar (Fin a) (GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ))) =
        σ'.ρ := by
      ext g v
      change ((GlobalTheory.SmGL.detChar (Fin a) (GlobalTheory.SmGL.absPow (w.adicCompletion E) ((-t : ℝ) : ℂ)) g : ℂˣ) : ℂ) • σ.ρ g v =
        ((CuspSub.locDet a (nu E (-t)) w g : ℂˣ) : ℂ) • σ.ρ g v
      congr 2
      simp [CuspSub.locDet, hloc, GlobalTheory.SmGL.detChar]
    rw [e2]
    exact .refl _
  rw [key]
  exact GlobalTheory.GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred) hU

end GlobalTheory.UnitLocWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHeckeSplitPlaceSetIffDoubleCoset
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TSetDoubleCoset

theorem trivOutside_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  have e : ((x * y : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [e, Matrix.map_mul, hx v hv, hy v hv, Matrix.mul_one]

theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem loc_mem_GLint {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    {k : GA L n} (hk : k ∈ Umax L n) :
    s.loc n k ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
  apply mem_GLint_of_entries
  · intro a b
    exact GlobalTheory.splitPlace_proj_mem_integers_of_integral s (hk a b)
  · intro a b
    rw [← map_inv]
    exact GlobalTheory.splitPlace_proj_mem_integers_of_integral s ((Umax L n).inv_mem hk a b)

theorem mem_tSet_iff : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (sp : SplitPlace L) (ϖ : (sp.v).adicCompletion (maximalRealSubfield L)) (k : ℕ), ∀ x₀ ∈ Formalism.AUTREP.tSet L n sp ϖ k, ∀ κ, κ ∈ Formalism.AUTREP.tSet L n sp ϖ k ↔ ∃ k₁, (k₁ ∈ Umax L n ∧ TrivOutside {sp.v} k₁) ∧ ∃ k₂, (k₂ ∈ Umax L n ∧ TrivOutside {sp.v} k₂) ∧ κ = k₁ * x₀ * k₂ := by
  intro L _ _ _ n sp ϖ k x₀ hx₀ κ
  obtain ⟨hx₀t, a₀, ha₀, b₀, hb₀, hx₀e⟩ := hx₀
  constructor
  · rintro ⟨hκt, a, ha, b, hb, hκe⟩
    obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n sp
    have hg : a * a₀⁻¹ ∈ Formalism.UG.GLint (Fin n) (sp.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :=
      mul_mem ha (inv_mem ha₀)
    have hg' : b₀⁻¹ * b ∈ Formalism.UG.GLint (Fin n) (sp.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :=
      mul_mem (inv_mem hb₀) hb
    refine ⟨e (a * a₀⁻¹), ⟨GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp _ (he1 _) (by rw [he2]; exact hg), he1 _⟩,
      e (b₀⁻¹ * b), ⟨GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp _ (he1 _) (by rw [he2]; exact hg'), he1 _⟩, ?_⟩
    apply GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n sp
    · exact hκt
    · exact trivOutside_mul (trivOutside_mul (he1 _) hx₀t) (he1 _)
    · rw [map_mul, map_mul, he2, he2]
      apply Units.ext
      simp only [Units.val_mul]
      rw [hκe, hx₀e]
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]
  · rintro ⟨k₁, ⟨hk₁, hk₁t⟩, k₂, ⟨hk₂, hk₂t⟩, rfl⟩
    refine ⟨trivOutside_mul (trivOutside_mul hk₁t hx₀t) hk₂t, sp.loc n k₁ * a₀,
      mul_mem (loc_mem_GLint sp hk₁) ha₀, b₀ * sp.loc n k₂, mul_mem hb₀ (loc_mem_GLint sp hk₂), ?_⟩
    rw [map_mul, map_mul]
    simp only [Units.val_mul]
    rw [hx₀e]
    simp only [Matrix.mul_assoc]

end GlobalTheory.TSetDoubleCoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemISupIsLinAtBilin
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaLoc

open GlobalTheory.SplitWeil

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ}

theorem isLinAt_comp {Θ Ω : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup Ω] [Module ℂ Ω]
    (ω₁ : GAf E n × GAf E r →* Module.End ℂ Θ) (ω₂ : GAf E n × GAf E r →* Module.End ℂ Ω)
    (P : Θ → Prop) (T : Θ →ₗ[ℂ] Ω) (hT : ∀ p f, P f → T (ω₁ p f) = ω₂ p (T f))
    (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ)
    (ι : SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ) (hP : ∀ Φ, P (ι Φ))
    (h : IsLinAt ω₁ s μ η ι) : IsLinAt ω₂ s μ η (T ∘ₗ ι) := by
  obtain ⟨c, hc, hc', hι⟩ := h
  refine ⟨c, hc, hc', fun h g hh hg Φ Φ' hΦ => ?_⟩
  simp only [LinearMap.comp_apply]
  rw [← hT _ _ (hP Φ), hι h g hh hg Φ Φ' hΦ, map_smul]

def valAct {G Θ A B : Type} [Monoid G] [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (ω : G →* Module.End ℂ Θ) : G →* Module.End ℂ (A →ₗ[ℂ] B →ₗ[ℂ] Θ) where
  toFun p :=
    { toFun := fun φ => φ.compr₂ (ω p)
      map_add' := fun φ φ' => by ext; simp
      map_smul' := fun c φ => by ext; simp }
  map_one' := by ext; simp
  map_mul' p q := by ext; simp

def single {Θ A B : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (α : A →ₗ[ℂ] ℂ) (β : B →ₗ[ℂ] ℂ) : Θ →ₗ[ℂ] (A →ₗ[ℂ] B →ₗ[ℂ] Θ) where
  toFun f := α.smulRight (β.smulRight f)
  map_add' f f' := by ext; simp
  map_smul' c f := by ext; simp [smul_comm c]

end GlobalTheory.ThetaLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSpanTranslatesOfFixedLatticeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.LocMod GlobalTheory.PlaceModel ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_translates_of_fixed_lattice : ∀ {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V] (χ : G → G → ℂ), GlobalTheory.PlaceModel.IsBichar χ → ∀ (ρ : G → V →ₗ[ℂ] V) (X Yh L L' K : AddSubgroup G), L ≤ L' → L' ≤ X → K ≤ Yh → (∀ v, ρ 0 v = v) → (∀ x ∈ X, ∀ x' ∈ X, ∀ v, ρ x (ρ x' v) = ρ (x + x') v) → (∀ y ∈ Yh, ∀ y' ∈ Yh, ∀ v, ρ y (ρ y' v) = ρ (y + y') v) → (∀ x ∈ X, ∀ y ∈ Yh, ∀ v, ρ x (ρ y v) = χ x y • ρ y (ρ x v)) → (∃ R : Finset G, ∀ t ∈ L', ∃ r ∈ R, t - r ∈ L) → (∀ x ∈ L', ∀ y ∈ K, χ x y = 1) → (∀ y ∈ Yh, (∀ x ∈ L', χ x y = 1) → y ∈ K) → ∀ (W : Submodule ℂ V), (∀ v ∈ W, ∀ x ∈ X, ρ x v ∈ W) → (∀ v ∈ W, ∀ y ∈ Yh, ρ y v ∈ W) → ∀ f ∈ W, (∀ x ∈ L, ρ x f = f) → (∀ y ∈ K, ρ y f = f) → f ∈ Submodule.span ℂ {v | ∃ r ∈ X, ∃ g ∈ W, (∀ x ∈ L, ρ x g = g) ∧ (∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y g = g) ∧ v = ρ r g} := by
  first | exact @GlobalTheory.FourierSpan.mem_span_translates_of_fixed | exact GlobalTheory.FourierSpan.mem_span_translates_of_fixed | (intros; apply GlobalTheory.FourierSpan.mem_span_translates_of_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsSplitPlaceOfInertOverRealSubfield
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem not_isSplitPl_of_isInertAt (D : D7) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (h : Formalism.UG.IsInertAt (↥D.host.F) D.host.E (HeightOneSpectrum.under (𝓞 ↥D.host.F) Pp) Pp) : ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := by
  rintro ⟨x, hx, hy⟩
  have hc : (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)).comp
      (algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E)) = algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) := by
    refine RingHom.ext fun a => RingOfIntegers.ext ?_
    have key : ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) = ((a : ↥D.host.F) : D.host.E) := rfl
    have h0 := (D.host.conjE_mem_hostF_iff _).1 (a : ↥D.host.F).2
    show (D.host.conj ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E)) = _
    rw [key]; exact h0
  have hmem : NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x ∈ Pp.asIdeal := by
    unfold Formalism.UG.IsInertAt at h
    rw [← h] at hx ⊢
    have := Ideal.mem_map_of_mem (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)) hx
    rwa [Ideal.map_map, hc] at this
  exact hy _ rfl hmem

end GlobalTheory
end

