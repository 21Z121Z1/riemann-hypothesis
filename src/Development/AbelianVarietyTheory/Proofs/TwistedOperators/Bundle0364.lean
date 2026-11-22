import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0282
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzDatumEqOfThetaFunctionEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

def evIHom (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

theorem evI_eq (a : AF F) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = evIHom F a := rfl

def embI (F : Type) [Field F] [NumberField F] : F →+* mixedEmbedding.mixedSpace F :=
  (evIHom F).comp (algebraMap F (AF F))

theorem countable_F : Countable F :=
  (Module.finBasis ℚ F).equivFun.injective.countable

def infAd (m : mixedEmbedding.mixedSpace F) : AF F :=
  (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

theorem evIHom_infAd (m : mixedEmbedding.mixedSpace F) : evIHom F (infAd m) = m := by
  show (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m) = m
  exact RingEquiv.apply_symm_apply _ m

theorem mul_infAd {u : AF F} (hu : evIHom F u = 0) (m : mixedEmbedding.mixedSpace F) : u * infAd m = 0 := by
  have h1 : u.1 = 0 := by
    have : (InfiniteAdeleRing.ringEquiv_mixedSpace F) u.1 = 0 := hu
    exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
  show (u.1 * _, u.2 * 0) = ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
  rw [h1, zero_mul, mul_zero]

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

def bI (F : Type) [Field F] [NumberField F] :
    Module.Basis (Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F))) ℝ (mixedEmbedding.mixedSpace F) :=
  Module.finBasis ℝ (mixedEmbedding.mixedSpace F)

def pI {κ : Type} (ξ : κ → F) : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ :=
  fun ij => Algebra.trace ℝ _ (embI F (ξ ij.1) * bI F ij.2)

def mI {κ : Type} (t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) (i : κ) :
    mixedEmbedding.mixedSpace F :=
  (-(1 / (2 * Real.pi))) • ∑ j, t (i, j) • bI F j

theorem psi_dot {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {κ : Type} [Fintype κ]
    (t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) (ξ : κ → F) :
    ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) =
      Complex.exp (((∑ ij, pI ξ ij * t ij : ℝ) : ℂ) * Complex.I) := by
  set a := (fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i) with ha
  have hAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) a := by
    intro u hu
    rw [evI_eq] at hu
    show u * a = 0
    simp only [ha, dotProduct, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mul_left_comm, mul_infAd hu, mul_zero]
  rw [hψ.2.2 a hAt, evI_eq]
  have hev : evIHom F a = ∑ i, embI F (ξ i) * mI t i := by
    simp only [ha, dotProduct, map_sum, map_mul, evIHom_infAd, embI, RingHom.comp_apply]
  have htr : Algebra.trace ℝ _ (evIHom F a) = -(1 / (2 * Real.pi)) * ∑ ij, pI ξ ij * t ij := by
    rw [hev, map_sum, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mI, mul_smul_comm, Finset.mul_sum, map_smul, map_sum, smul_eq_mul, pI]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [htr]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj
variable {F : Type} [Field F] [NumberField F]

theorem pI_eq_zero {κ : Type} {ξ : κ → F} (h : pI ξ = 0) : ξ = 0 := by
  funext i
  by_contra hne
  have hz : ∀ z, Algebra.trace ℝ _ (embI F (ξ i) * z) = 0 := by
    intro z
    rw [← (bI F).sum_repr z, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [mul_smul_comm, map_smul, show Algebra.trace ℝ _ (embI F (ξ i) * bI F j) = 0 from congrFun h (i, j),
      smul_zero]
  have h1 := hz (embI F (ξ i)⁻¹)
  rw [← map_mul, mul_inv_cancel₀ hne, map_one, ← map_one (algebraMap ℝ (mixedEmbedding.mixedSpace F)),
    Algebra.trace_algebraMap, mixedEmbedding.finrank, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at h1
  exact (Module.finrank_pos (R := ℚ) (M := F)).ne' h1

theorem pI_zero {κ : Type} : pI (0 : κ → F) = 0 := by
  funext ij
  simp [pI]

theorem coeff_zero {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ)
    (c : (κ → F) → ℂ) (hc : Summable fun ξ => ‖c ξ‖)
    (h : ∀ t : κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ,
      ∑' ξ : κ → F, ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) * c ξ = 0) :
    c 0 = 0 := by
  classical
  letI : MeasurableSpace (κ → F) := ⊤
  haveI : MeasurableSingletonClass (κ → F) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  haveI : Countable F := countable_F
  have hint : Integrable c Measure.count := integrable_count_iff.mpr hc
  have hp : Measurable (pI (F := F) (κ := κ)) := fun _ _ => MeasurableSpace.measurableSet_top
  have key := GlobalTheory.FourierPush.setIntegral_preimage_eq_zero (κ → F) Measure.count c hint
    (κ × Fin (Module.finrank ℝ (mixedEmbedding.mixedSpace F)) → ℝ) pI hp ?_ {0} (measurableSet_singleton 0)
  · have hpre : pI ⁻¹' {0} = ({0} : Set (κ → F)) := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨pI_eq_zero, fun h => h ▸ pI_zero⟩
    rw [hpre, integral_singleton] at key
    simpa using key
  · intro l
    have hI : Integrable (fun ξ => Complex.exp ((l (pI ξ) : ℂ) * Complex.I) * c ξ) Measure.count := by
      refine integrable_count_iff.mpr (hc.congr fun ξ => ?_)
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    rw [integral_countable hI]
    have hl : ∀ ξ : κ → F, l (pI ξ) = ∑ ij, pI ξ ij * l (fun k => if ij = k then 1 else 0) := by
      intro ξ
      rw [show l (pI ξ) = l.toLinearMap (pI ξ) from rfl, LinearMap.pi_apply_eq_sum_univ]
      simp [smul_eq_mul]
    have := h (fun ij => l (fun k => if ij = k then 1 else 0))
    rw [← this]
    refine tsum_congr fun ξ => ?_
    rw [psi_dot hψ, ← hl]
    simp

end GlobalTheory.ThetaInj

namespace GlobalTheory.ThetaInj

theorem theta_inj : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type}
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z), ∀ (Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ) (f : Z → ℂ),
    IsDatum M ψ crd Φ₁ f → IsDatum M ψ crd Φ₂ f → Φ₁ = Φ₂ := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z crd Φ₁ Φ₂ f h₁ h₂
  funext x
  have hs : ∀ Φ, Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) →
      Summable fun ξ : Fin n × Fin d → F => ‖Φ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ := by
    intro Φ hΦ
    have := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    exact this
  have hsum : Summable fun ξ : Fin n × Fin d → F =>
      ‖Φ₁ ((fun i => algebraMap F (AF F) (ξ i)) + x) - Φ₂ ((fun i => algebraMap F (AF F) (ξ i)) + x)‖ := by
    refine ((hs Φ₁ h₁.1).add (hs Φ₂ h₂.1)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _)
  have key := coeff_zero hψ
    (fun ξ => Φ₁ ((fun i => algebraMap F (AF F) (ξ i)) + x) - Φ₂ ((fun i => algebraMap F (AF F) (ξ i)) + x))
    hsum ?_
  · have h0 : (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)) + x = x := by
      funext i; simp
    simp only [h0, sub_eq_zero] at key
    exact key
  · intro t
    have hn : ∀ ξ : Fin n × Fin d → F,
        ‖ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i))‖ = 1 := fun ξ => by
      rw [psi_dot hψ]; exact Complex.norm_exp_ofReal_mul_I _
    have hS : ∀ Φ, Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) → Summable fun ξ : Fin n × Fin d → F =>
        ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) *
          Φ ((fun i => algebraMap F (AF F) (ξ i)) + x) := fun Φ hΦ =>
      Summable.of_norm ((hs Φ hΦ).congr fun ξ => by rw [norm_mul, hn, one_mul])
    have hT : ∀ Φ, IsDatum M ψ crd Φ f →
        ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))) * ∑' ξ : Fin n × Fin d → F,
          ψ ((fun i => algebraMap F (AF F) (ξ i)) ⬝ᵥ fun i => infAd (mI t i)) *
            Φ ((fun i => algebraMap F (AF F) (ξ i)) + x) =
          f (crd (M.co.e.symm (x, fun i => infAd (mI t i)))) := by
      intro Φ hΦ
      rw [← hΦ.2 (M.co.e.symm (x, fun i => infAd (mI t i))), ← tsum_mul_left]
      simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, LinearEquiv.apply_symm_apply,
        AddChar.map_add_eq_mul]
      refine tsum_congr fun ξ => ?_
      ring
    have hne : ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))) ≠ 0 := by
      intro h0
      have := AddChar.map_add_eq_mul ψ (⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i)))
        (-(⅟(2 : AF F) * (x ⬝ᵥ fun i => infAd (mI t i))))
      rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
      exact one_ne_zero this
    have e2 := mul_left_cancel₀ hne ((hT Φ₁ h₁).trans (hT Φ₂ h₂).symm)
    simp only [mul_sub]
    rw [(hS Φ₁ h₁.1).tsum_sub (hS Φ₂ h₂.1), e2, sub_self]

end GlobalTheory.ThetaInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzUnitaryIntertwinerScalar
section
open scoped Matrix

noncomputable section

open MeasureTheory Complex
open scoped Real RealInnerProductSpace ComplexConjugate FourierTransform SchwartzMap

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

def modPt (q : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim 0 fun i => q i

def trPt (p : EuclideanSpace ℝ l) : l ⊕ l → ℝ := Sum.elim (fun i => p i) 0

theorem pPart_modPt (q : EuclideanSpace ℝ l) : pPart (modPt q) = 0 := by
  ext i; simp [pPart, modPt]

theorem qPart_modPt (q : EuclideanSpace ℝ l) : qPart (modPt q) = q := by
  ext i; simp [qPart, modPt]

theorem pPart_trPt (p : EuclideanSpace ℝ l) : pPart (trPt p) = p := by
  ext i; simp [pPart, trPt]

theorem qPart_trPt (p : EuclideanSpace ℝ l) : qPart (trPt p) = 0 := by
  ext i; simp [qPart, trPt]

theorem rhoFun_modPt (q : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (modPt q) f x = cexp (((2 * π * ⟪q, x⟫ : ℝ) : ℂ) * I) * f x := by
  simp [rhoFun, phase, pPart_modPt, qPart_modPt]

theorem rhoFun_trPt (p : EuclideanSpace ℝ l) (f : EuclideanSpace ℝ l → ℂ) (x : EuclideanSpace ℝ l) :
    rhoFun (trPt p) f x = f (x + p) := by
  simp [rhoFun, phase, pPart_trPt, qPart_trPt]

def modS (q : EuclideanSpace ℝ l) (g : Sch l) : Sch l :=
  SchwartzMap.smulLeftCLM ℂ (fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫) g

theorem coe_modS (q : EuclideanSpace ℝ l) (g : Sch l) : ⇑(modS q g) = rhoFun (modPt q) ⇑g := by
  have ht : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => GlobalTheory.Published.Metaplectic.eChar ⟪q, x⟫ :=
    GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (innerSL ℝ q).hasTemperateGrowth
  funext x
  rw [modS, SchwartzMap.smulLeftCLM_apply_apply ht, GlobalTheory.Published.Metaplectic.eChar_apply, rhoFun_modPt, smul_eq_mul]
  congr 2
  push_cast
  ring

def trS (p : EuclideanSpace ℝ l) (g : Sch l) : Sch l := SchwartzMap.compSubConstCLM ℂ (-p) g

theorem coe_trS (p : EuclideanSpace ℝ l) (g : Sch l) : ⇑(trS p g) = rhoFun (trPt p) ⇑g := by
  funext x
  rw [trS, SchwartzMap.compSubConstCLM_apply, rhoFun_trPt, sub_neg_eq_add]

theorem integrable_conj_mul (a b : Sch l) : Integrable (fun x => conj (a x) * b x) := by
  refine b.integrable.bdd_mul (c := SchwartzMap.seminorm ℝ 0 0 a)
    (Complex.continuous_conj.comp a.continuous).aestronglyMeasurable (.of_forall fun x => ?_)
  rw [Complex.norm_conj]
  exact SchwartzMap.norm_le_seminorm ℝ a x

theorem integral_conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) :
    ∫ x, conj (U f x) * U g x = ∫ x, conj (f x) * g x := by
  have hn : ∀ h : Sch l, ‖(U h).toLp 2‖ = ‖h.toLp 2‖ := fun h => by
    rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp,
      eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hU]
  have hlin : ∀ (b : ℂ) (u v : Sch l), u.toLp 2 volume + b • v.toLp 2 volume = (u + b • v).toLp 2 volume := fun b u v => by
    have := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_add u (b • v)
    rw [(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclideanSpace ℝ l))).map_smul] at this
    exact this.symm
  have key : ∀ b : ℂ, ‖(U f).toLp 2 + b • (U g).toLp 2‖ = ‖f.toLp 2 + b • g.toLp 2‖ := fun b => by
    rw [hlin, hlin, ← map_smul, ← map_add, hn]
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key (-(RCLike.I : ℂ))
  have k4 := key (RCLike.I : ℂ)
  simp only [one_smul, neg_one_smul, neg_smul, ← sub_eq_add_neg] at k1 k2 k3 k4
  have e1 := SchwartzMap.inner_toL2_toL2_eq (U f) (U g) volume
  have e2 := SchwartzMap.inner_toL2_toL2_eq f g volume
  simp only [RCLike.inner_apply] at e1 e2
  simp only [mul_comm (starRingEnd ℂ _)]
  rw [← e1, ← e2, inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, k1, k2, k3, k4]

end GlobalTheory.RealWeil.SchurSchwartz

namespace GlobalTheory.RealWeil.SchurSchwartz

variable {l : Type} [Fintype l]

theorem conj_mul_eq (U : Sch l →ₗ[ℂ] Sch l)
    (hc : ∀ (w : l ⊕ l → ℝ) (h h₁ : Sch l), ⇑h₁ = rhoFun w ⇑h → ⇑(U h₁) = rhoFun w ⇑(U h))
    (hU : ∀ h : Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) (f g : Sch l) (x : EuclideanSpace ℝ l) :
    conj (U f x) * U g x = conj (f x) * g x := by
  set D : EuclideanSpace ℝ l → ℂ := fun y => conj (U f y) * U g y - conj (f y) * g y with hD
  have hDi : Integrable D := (integrable_conj_mul (U f) (U g)).sub (integrable_conj_mul f g)
  have hDc : Continuous D :=
    ((Complex.continuous_conj.comp (U f).continuous).mul (U g).continuous).sub
      ((Complex.continuous_conj.comp f.continuous).mul g.continuous)
  have hF : 𝓕 D = 0 := by
    funext w
    rw [Real.fourier_eq', Pi.zero_apply]
    have h1 := hc (modPt (-w)) g (modS (-w) g) (coe_modS _ _)
    have h2 := integral_conj_mul_eq U hU f (modS (-w) g)
    rw [← sub_eq_zero, ← integral_sub (integrable_conj_mul _ _) (integrable_conj_mul _ _)] at h2
    rw [← h2]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [h1, coe_modS, rhoFun_modPt, hD, smul_eq_mul]
    rw [inner_neg_left, real_inner_comm]
    push_cast
    ring_nf
  have hinv := hDc.fourierInv_fourier_eq hDi (by rw [hF]; exact integrable_zero _ _ _)
  have hz : 𝓕⁻ (0 : EuclideanSpace ℝ l → ℂ) = 0 := by
    first
      | exact FourierTransform.fourierInv_zero
      | (funext w; simp [Real.fourierInv_eq])
  rw [hF, hz] at hinv
  have hx := congrFun hinv x
  simp only [hD, Pi.zero_apply] at hx
  exact sub_eq_zero.1 hx.symm

theorem schur_schwartz : GlobalTheory.FunPr.Hypotheses₂ → ∀ (l : Type) [Fintype l] (U : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
    (∀ (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(U h₁) = GlobalTheory.RealWeil.rhoFun w ⇑(U h)) →
    (∀ h : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, U h = a • h := by
  intro _ l _ U hc hU
  by_cases h0 : ∃ (g : Sch l) (y : EuclideanSpace ℝ l), g y ≠ 0
  · obtain ⟨g, y0, hg⟩ := h0
    have hb := conj_mul_eq U hc hU g g y0
    rw [Complex.conj_mul', Complex.conj_mul'] at hb
    have h2 : ‖U g y0‖ ^ 2 = ‖g y0‖ ^ 2 := by exact_mod_cast hb
    have hnb : ‖U g y0‖ = ‖g y0‖ := by
      first
        | exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
        | exact pow_left_injective₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero h2
        | nlinarith [norm_nonneg (U g y0), norm_nonneg (g y0)]
    have hb0 : U g y0 ≠ 0 := by
      intro h
      apply hg
      rw [← norm_eq_zero, ← hnb, h, norm_zero]
    have hcb : conj (U g y0) ≠ 0 := (map_ne_zero _).2 hb0
    refine ⟨conj (g y0 / U g y0), ?_, fun f => ?_⟩
    · rw [Complex.norm_conj, norm_div, hnb, div_self (norm_ne_zero_iff.2 hg)]
    · ext x
      have e1 := conj_mul_eq U hc hU f (trS (y0 - x) g) x
      have hxy : x + (y0 - x) = y0 := by abel
      rw [hc (trPt (y0 - x)) g (trS (y0 - x) g) (coe_trS _ _), coe_trS, rhoFun_trPt, rhoFun_trPt, hxy] at e1
      have e2 := congrArg conj e1
      simp only [map_mul, Complex.conj_conj] at e2
      rw [SchwartzMap.smul_apply, smul_eq_mul, map_div₀, div_mul_eq_mul_div, eq_div_iff hcb, e2, mul_comm]
  · push_neg at h0
    refine ⟨1, by simp, fun h => ?_⟩
    ext x
    rw [h0 (U h) x, one_smul, h0 h x]

end GlobalTheory.RealWeil.SchurSchwartz

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SpanValuesDenseFinitePartSubrepStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_values_dense_finitePartSubrep : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ hU : IsSubrep π ⊤, ∀ N : Subrepresentation (finPartDSSm M hU), N ≠ ⊥ → (Submodule.span ℂ {z | ∃ Φ ∈ N.toSubmodule, ∃ y, z = ((Φ : homDS M π ⊤) : ContinuousMultilinearMap ℂ M.H H) y}).topologicalClosure = ⊤ := by
  first | exact @GlobalTheory.TrFinDense.span_values_dense | exact GlobalTheory.TrFinDense.span_values_dense | (intros; apply GlobalTheory.TrFinDense.span_values_dense <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFramesTransportLocalLatticeIsometryStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitFrames_transport_localLatticeIsometry : ∀ (D : D7) (V V' : HSp D) (hr : V'.rank = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (j : GLoc D.sp.cm.sig V.gram v ≃ₜ* GLoc D.sp.cm.sig V'.gram v), IsLatticeConj (frameLat V) (frameLat V') j → (∀ g, j g ∈ Kv V' v ↔ g ∈ Kv V v) ∧ ∀ s : SplitAt D.sp.cm.sig V.gram (frameLat V) v, ∃ s' : SplitAt D.sp.cm.sig V'.gram (frameLat V') v, (∀ g a b, (s'.equiv (j g)).1 a b = (s.equiv g).1 (a.cast hr) (b.cast hr)) ∧ ∀ (k : Kv V v) (k' : Kv V' v), (k' : GLoc D.sp.cm.sig V'.gram v) = j k → ∀ a b, (s'.red k').1 a b = (s.red k).1 (a.cast hr) (b.cast hr) := by
  first | exact @GlobalTheory.LatConjSplit.splitAt_of_isLatticeConj | exact GlobalTheory.LatConjSplit.splitAt_of_isLatticeConj | (intros; apply GlobalTheory.LatConjSplit.splitAt_of_isLatticeConj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceEigenvalueIsSqrtNormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_eigenvalue_is_sqrt_norm : ∀ (D : D7) (lam : ℕ →* ℂ), (∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ)) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → IsSplit (E := D.host.E) v → ∀ m : ℕ, lam (qV D.host.E w ^ m) = (Real.sqrt ((qV D.host.E w ^ m : ℕ) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.FinZeta.SplitNorm.lam_qV_pow | exact GlobalTheory.FinZeta.SplitNorm.lam_qV_pow | (intros; apply GlobalTheory.FinZeta.SplitNorm.lam_qV_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardCharTraceSingleRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

theorem GlobalTheory.PhaseReal.psi_trace_single : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ → ∀ (τ : D.what₂.Tau) (t : AE D),
  finPart D t = 0 → (∀ ρ, ρ ≠ τ → θ ρ (infPart D t) = 0) →
  ψ (Algebra.trace (AF D.host.F) (AE D) t) = Complex.exp (Complex.I * (((-(4 * Real.pi : ℂ)) * θ τ (infPart D t)).re : ℂ)) := by
  intro D ψ hψ θ hθ τ t hfin hsupp
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  set T := Algebra.trace (AF D.host.F) (AE D) t with hTdef
  have h1 : ψ T = psiInf D.host.F ψ (fstA D.host.F T) := by
    unfold psiInf
    congr 1
  have h2 := hψ.2.2 θ hθ (fstA D.host.F T)
  have h3 : ∀ ρ, θ ρ (fstA D.host.F T ⊗ₜ[D.host.F] (1 : D.host.E)) = ((2 * (θ ρ (infPart D t)).re : ℝ) : ℂ) :=
    fun ρ => GlobalTheory.PhaseReal.theta_trace θ hθ ρ t
  have h4 : ∑ ρ, θ ρ (fstA D.host.F T ⊗ₜ[D.host.F] (1 : D.host.E)) = ((2 * (θ τ (infPart D t)).re : ℝ) : ℂ) := by
    simp only [h3]
    refine Finset.sum_eq_single τ (fun ρ _ hρ => ?_) (fun h => absurd (Finset.mem_univ τ) h)
    rw [hsupp ρ hρ]
    simp
  rw [h1, h2, h4]
  congr 1
  have h5 : ((-(4 * Real.pi : ℂ)) * θ τ (infPart D t)).re = -(4 * Real.pi) * (θ τ (infPart D t)).re := by
    have : (-(4 * Real.pi : ℂ)) = ((-(4 * Real.pi) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  rw [h5]
  push_cast
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFormEigenMemSinglePartStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaForm_eigen_mem_single_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (b : Pl D.host.E → List ℤ → ℂ), ∃ ev, ∀ w : (R.HW i σ).H, (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d → postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) → w ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  first | exact @GlobalTheory.ConjScalar.OnePart.mem_one_part | exact GlobalTheory.ConjScalar.OnePart.mem_one_part | (intros; apply GlobalTheory.ConjScalar.OnePart.mem_one_part <;> assumption)
end

