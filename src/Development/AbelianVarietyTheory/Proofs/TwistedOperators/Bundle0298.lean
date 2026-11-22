import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0266
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0101
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0214
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0271
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittTargetProjections
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumTaylorSeriesDerivAtOriginCoordinateSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.FockTaylor

def curryL (ι : Type) (a b : ℕ) : (DVar ι a b → ℂ) →ₗ[ℂ] VCx ι a b where
  toFun w := fun τ i j => w (τ, i, j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem curryL_single {ι : Type} [DecidableEq ι] {a b : ℕ} (k : DVar ι a b) :
    curryL ι a b (Pi.single k 1) = Formalism.L2.Ker.coordX k := by
  funext τ i j
  obtain ⟨x, y, z⟩ := k
  simp [curryL, Formalism.L2.Ker.coordX, Pi.single_apply, Prod.ext_iff]

theorem derivAt0_eq_pderivIter {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ}
    (G : VCx ι a b → ℂ) (hG : Differentiable ℂ G) (m : DVar ι a b →₀ ℕ) :
    derivAt0 G m = GlobalTheory.pderivIter m (fun w => G (curryL ι a b w)) 0 := by
  have han : AnalyticAt ℂ G 0 := SCV.analyticOnNhd_of_differentiable hG Set.univ 0 (Set.mem_univ _)
  rw [derivAt0, GlobalTheory.pderivIter, GlobalTheory.pderivList, GlobalTheory.lineDerivList_comp_linearMap,
    ← GlobalTheory.lineDerivList_ofFn han]
  simp only [map_zero, List.map_map]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [curryL_single]

theorem coeff_taylor_eq_pderivIter {σ : Type} [Fintype σ] [DecidableEq σ] {f : (σ → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (GlobalTheory.taylor f) = GlobalTheory.pderivIter α f 0 / ∏ j, ((α j).factorial : ℂ) := by
  rw [GlobalTheory.coeff_taylor, GlobalTheory.dirPolyDeriv_monomial_eq_lineDerivList (l := α.toMultiset.toList)
    (by simp) _ hf, Nat.cast_prod, div_eq_inv_mul]
  rfl

end GlobalTheory.FockTaylor

open GlobalTheory.FockTaylor in

theorem GlobalTheory.FockTaylor.hasSum_derivAt0 : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (G : VCx ι a b → ℂ), Differentiable ℂ G → ∀ z₀ : VCx ι a b, HasSum (fun m : DVar ι a b →₀ ℕ => (m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m) (G z₀) := by
  intro ι _ a b G hG z₀
  classical
  let L := LinearMap.toContinuousLinearMap (curryL ι a b)
  have hf : Differentiable ℂ (fun w => G (L w)) := hG.comp L.differentiable
  have hfa : AnalyticAt ℂ (fun w => G (L w)) 0 :=
    SCV.analyticOnNhd_of_differentiable hf Set.univ 0 (Set.mem_univ _)
  let c : (DVar ι a b →₀ ℕ) → ℂ := fun m => derivAt0 G m / ∏ j, ((m j).factorial : ℂ)
  have hne : ∀ m : DVar ι a b →₀ ℕ, (∏ j, ((m j).factorial : ℂ)) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.mpr fun k _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc : ∀ m, (∏ j, ((m j).factorial : ℂ)) * c m = GlobalTheory.pderivIter m (fun w => G (L w)) 0 :=
    fun m => by
      rw [mul_div_cancel₀ _ (hne m), derivAt0_eq_pderivIter G hG m]
      rfl
  have hc' : ∀ m, c m = MvPowerSeries.coeff m (GlobalTheory.taylor fun w => G (L w)) := fun m => by
    rw [coeff_taylor_eq_pderivIter hfa]
    show derivAt0 G m / _ = _
    rw [derivAt0_eq_pderivIter G hG m]
    rfl
  let w : DVar ι a b → ℂ := fun k => z₀ k.1 k.2.1 k.2.2
  have hs := GlobalTheory.EntireTaylor.summable_of_entire hf c hc w
  have ht := GlobalTheory.ProdThetaConj.tsum_of_entire hf c hc hc' w
  have hterm : ∀ m : DVar ι a b →₀ ℕ,
      (m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m
        = c m * ∏ j, w j ^ m j := fun m => by
    rw [Finsupp.prod_fintype _ _ (by simp), Finset.prod_div_distrib]
    simp only [c, w]
    ring
  have hGz : G z₀ = G (L w) := rfl
  rw [hGz, ← ht]
  exact (hs.hasSum).congr_fun hterm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumUnramifiedZetaSumUnitaryInert
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ZetaSumU

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem cartan_complete : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ g : GU σ n, ∃ (d : Fin n → ℤ) (t : GU σ n),
      t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) ∧ ∃ k₁ ∈ KU σ n, ∃ k₂ ∈ KU σ n, g = k₁ * t * k₂ := by
  intro L _ _ _ ϖ σ q n hU g
  obtain ⟨d, hd, a, ha, b, hb, e⟩ := GlobalTheory.LFun.UnitaryDiv.exists_good_div L ϖ σ q n hU g
  obtain ⟨t, ht⟩ := GlobalTheory.InertThetaCompare.exists_diag hU hd
  obtain ⟨k₁, h₁, k₂, h₂, e'⟩ := GlobalTheory.T.unitaryDoubleCoset_of_GLintDoubleCoset L ϖ σ q n hU t g a b ha hb (Units.ext (by rw [e, ← ht]; rfl))
  exact ⟨fun i => d.getD i.1 0, t, ht, k₁, h₁, k₂, h₂, e'⟩

section
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] {σ : L →+* L} {q n : ℕ}

theorem kerU_biInv {ϖ : L} (hU : IsUnramInv ϖ σ q) {N : ℕ} {z : ℂˣ} {φ : GU σ n → ℂ} (hφ : KerU ϖ q N z φ)
    (g : GU σ n) {k₁ k₂ : GU σ n} (h₁ : k₁ ∈ KU σ n) (h₂ : k₂ ∈ KU σ n) : φ (k₁ * g * k₂) = φ g := by
  obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := cartan_complete L ϖ σ q n hU g
  rw [show k₁ * (a * t * b) * k₂ = (k₁ * a) * t * (b * k₂) by group, hφ d t ht _ (mul_mem h₁ ha) _ (mul_mem hb h₂),
    hφ d t ht a ha b hb]

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem sph_eq (ϖ : Lˣ) (hU : IsUnramInv (ϖ : L) σ q) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) {s : ℂ} {Φ : GD σ n → ℂ}
    (hΦ : IsSphSec σ q n χ s Φ) {N : ℕ} {z : ℂˣ} {φ : GU σ n → ℂ} (hφ : KerU (ϖ : L) q N z φ)
    (hX : varX q n (χ ϖ) s = (z : ℂ) * ((q : ℂ) ^ N)⁻¹) (g : GU σ n) : Φ (io1 σ n g) = φ g := by
  obtain ⟨d, t, ht, a, ha, b, hb, rfl⟩ := cartan_complete L (ϖ : L) σ q n hU g
  rw [GlobalTheory.T.sphericalDoublingSection_graph_diagonal_eq L ϖ σ q n hU χ hχ s Φ hΦ d t ht a ha b hb, hφ d t ht a ha b hb, hX]

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem exists_unr_char (ϖ : Lˣ) (hU : IsUnramInv (ϖ : L) σ q) (z : ℂˣ) : ∃ χ : Lˣ →* ℂˣ, IsUnr χ ∧ χ ϖ = z := by
  refine ⟨{ toFun := fun u => z ^ Formalism.UG.ordL (u : L), map_one' := ?_, map_mul' := fun a b => ?_ }, fun u hu => ?_, ?_⟩
  · have : Formalism.UG.ordL (1 : L) = 0 := by simp [Formalism.UG.ordL]; rfl
    simp [this]
  · simp [Formalism.UG.P.fIwasawa_ordL_mul _ _ a.ne_zero b.ne_zero, _root_.zpow_add]
  · have : Formalism.UG.ordL (u : L) = 0 := by
      have h0 : Valued.v (u : L) ≠ 0 := by rw [hu]; exact one_ne_zero
      have h1 : WithZero.unzero h0 = 1 := WithZero.coe_injective (by rw [WithZero.coe_unzero, hu]; rfl)
      simp [Formalism.UG.ordL, h0, h1]
    simp [this]
  · have h := Formalism.UG.P.fSatake_ord_zpow hU.2.2.2.1 (1 : ℤ)
    rw [zpow_one] at h
    simp [h]

theorem exists_haar (ϖ : L) (hU : IsUnramInv ϖ σ q) (n : ℕ) [MeasurableSpace (GU σ n)] [BorelSpace (GU σ n)] :
    ∃ μ : Measure (GU σ n), μ.IsHaarMeasure ∧ μ (KU σ n) = 1 := by
  haveI := GlobalTheory.LGrp.locallyCompact_GU_of_unram hU n
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU
  let K₀ : TopologicalSpace.PositiveCompacts (GU σ n) :=
    ⟨⟨_, hc⟩, by rw [ho.interior_eq]; exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K₀, inferInstance, Measure.haarMeasure_self⟩

end

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem closedForm_eq' (q r : ℕ) (X y : ℂ) (α : Fin (r / 2) → ℂˣ) :
    closedForm q r X y α = eulerFac (bcParam r α) y * ∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * X) := by
  rw [closedForm, GlobalTheory.LGrp.bcParam, GlobalTheory.LFun.eulerFac_add, GlobalTheory.LFun.eulerFac_add,
    GlobalTheory.LFun.eulerFac_map, GlobalTheory.LFun.eulerFac_map, Finset.prod_mul_distrib]
  simp only [Units.val_inv_eq_inv_val, div_eq_mul_inv, mul_comm y]
  rcases Nat.even_or_odd r with h | h
  · rw [if_neg (Nat.not_odd_iff_even.2 h), Nat.even_iff.1 h]
    simp only [Multiset.replicate_zero, GlobalTheory.LFun.eulerFac_zero]
    ring
  · rw [if_pos h, Nat.odd_iff.1 h]
    simp only [Multiset.replicate_one, GlobalTheory.LFun.eulerFac_singleton, Units.val_one, one_mul]
    ring

open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in
theorem varXY_eq (q r t : ℕ) (hq : 2 ≤ q) (z : ℂ) :
    varX q r z ((t : ℂ) / 2) = z * ((q : ℂ) ^ (r + t))⁻¹ ∧ varY q z ((t : ℂ) / 2) = z * ((q : ℂ) ^ (t + 1))⁻¹ := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  constructor
  · rw [varX, show -(2 * ((t : ℂ) / 2) + r) = -(((r + t : ℕ) : ℂ)) by push_cast; ring, Complex.cpow_neg,
      Complex.cpow_natCast]
  · rw [varY, show -(2 * ((t : ℂ) / 2) + 1) = -(((t + 1 : ℕ) : ℂ)) by push_cast; ring, Complex.cpow_neg,
      Complex.cpow_natCast]

theorem tb_triv : ∀ (q r : ℕ), 2 ≤ q → ∀ α : Fin (r / 2) → ℂˣ, (∀ i, (α i : ℂ) = (q : ℂ) ^ ((r : ℤ) - 1 - 2 * (i.val : ℤ))) → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α := by
  intro q r hq α hα i
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hn : ‖(α i : ℂ)‖ = (q:ℝ) ^ ((((r:ℤ) - 1 - 2 * (i.val:ℤ) : ℤ)) : ℝ) := by
    rw [hα, norm_zpow, Complex.norm_natCast, Real.rpow_intCast]
  have hi : 2 * i.val + 1 ≤ r := by have := i.2; omega
  have hi' : 2 * (i.val : ℝ) + 1 ≤ r := by exact_mod_cast hi
  have hi0 : (0:ℝ) ≤ i.val := Nat.cast_nonneg _
  rw [Real.rpow_neg (by positivity), GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, hn, ← Real.rpow_neg (by positivity)]
  constructor <;> apply Real.rpow_le_rpow_of_exponent_le hq1 <;> push_cast <;> linarith

theorem dom_of_tb : ∀ (q r t : ℕ), 2 ≤ q → r ≤ t → ∀ (z : ℂ), ‖z‖ = 1 → ∀ α : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.varY q z ((t : ℂ) / 2)) α := by
  intro q r t hq hrt z hz α hα
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hq1' : (1:ℝ) < q := by exact_mod_cast (by omega : 1 < q)
  have hq0 : (0:ℝ) < q := by linarith
  rw [(varXY_eq q r t hq z).2]
  have hy : ‖z * ((q:ℂ)^(t+1))⁻¹‖ = ((q:ℝ)^(t+1))⁻¹ := by
    rw [norm_mul, hz, one_mul, norm_inv, norm_pow, Complex.norm_natCast]
  have hB : ((q:ℝ)^2)^(((r:ℝ)-1)/2) ≤ (q:ℝ)^t := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.bound_eq, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq1 (by have : (r:ℝ) ≤ t := (by exact_mod_cast hrt); linarith)
  have hBp : 0 < ((q:ℝ)^2)^(((r:ℝ)-1)/2) := by positivity
  have e : ((q:ℝ)^(t+1))⁻¹ * (q:ℝ)^t = (q:ℝ)⁻¹ := by rw [pow_succ]; field_simp
  have key : ∀ a : ℝ, a ≤ (q:ℝ)^t → ((q:ℝ)^(t+1))⁻¹ * a < 1 := fun a ha =>
    calc ((q:ℝ)^(t+1))⁻¹ * a ≤ ((q:ℝ)^(t+1))⁻¹ * (q:ℝ)^t := mul_le_mul_of_nonneg_left ha (by positivity)
      _ = (q:ℝ)⁻¹ := e
      _ < 1 := inv_lt_one_of_one_lt₀ hq1'
  rw [GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.Domain, hy]
  refine ⟨by simpa using key 1 (one_le_pow₀ hq1), fun i => ⟨key _ ((hα i).2.trans hB), key _ ?_⟩⟩
  have h1 := (hα i).1
  rw [Real.rpow_neg (by positivity)] at h1
  have hαp : 0 < ‖(α i : ℂ)‖ := norm_pos_iff.2 (α i).ne_zero
  exact (inv_le_of_inv_le₀ hBp h1).trans hB

set_option maxHeartbeats 1000000 in
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables in

theorem hasSum_zetaSum_inert : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q r t : ℕ), IsUnramInv ϖ σ q → r ≤ t → ∀ (z : ℂˣ) (φ : GU σ r → ℂ), ‖(z : ℂ)‖ = 1 → KerU ϖ q (r + t) z φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ r) V) (x : V) (α : Fin (r / 2) → ℂˣ), IsSatVecU ϖ q ρ x α → GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r α → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * ℓ (ρ a.out x)) (eulerFac (bcParam r α) ((z : ℂ) * ((q : ℂ) ^ (t + 1))⁻¹) * (∏ j ∈ Finset.range r, (1 - (-(q : ℂ)) ^ j * ((z : ℂ) * ((q : ℂ) ^ (r + t))⁻¹))) * ℓ x) := by
  intro L _ _ _ ϖ σ q r t hU hrt z φ hz hφ V _ _ ρ x α hx hα ℓ hℓ
  obtain ⟨C, hC⟩ := hℓ
  have hq2 : 2 ≤ q := hU.2.2.2.2.2.1
  have hq : q ≠ 0 := by omega
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    have h' := hU.2.2.2.1
    rw [h, map_zero] at h'
    exact WithZero.zero_ne_coe h'
  let ϖu : Lˣ := Units.mk0 ϖ hϖ0
  have hUu : IsUnramInv (ϖu : L) σ q := hU
  obtain ⟨χ, hχ, hχϖ⟩ := exists_unr_char ϖu hUu z
  obtain ⟨Φ, hΦ⟩ := exists_isSphSec σ hq r hχ ((t : ℂ) / 2)
  obtain ⟨hXe, hYe⟩ := varXY_eq q r t hq2 (z : ℂ)
  have hX : varX q r (χ ϖu) ((t : ℂ) / 2) = (z : ℂ) * ((q : ℂ) ^ (r + t))⁻¹ := by rw [hχϖ, hXe]
  have hΦφ : ∀ g, Φ (io1 σ r g) = φ g := sph_eq ϖu hUu hχ hΦ hφ hX
  letI : MeasurableSpace (GU σ r) := borel _
  haveI : BorelSpace (GU σ r) := ⟨rfl⟩
  obtain ⟨μ, hμH, hμK⟩ := exists_haar ϖ hU r
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU r
  have hKo := (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q r hU).1
  have hright : ∀ g, ∀ k ∈ KU σ r, φ (g * k) = φ g := fun g k hk => by
    simpa using kerU_biInv hU hφ g (one_mem _) hk
  have hdouble := GlobalTheory.T.unramifiedDoublingIntegral_inert_place L ϖu σ q r hUu μ hμK χ hχ _ Φ hΦ
  have hzχ : ((χ ϖu : ℂˣ) : ℂ) = z := by rw [hχϖ]
  have hdom : ∀ β : Fin (r / 2) → ℂˣ, GlobalTheory.IndefiniteRowSideFullHecke.TrivialParameterBound.TrivialBound q r β →
      Domain (varY q (χ ϖu) ((t : ℂ) / 2)) β := fun β hβ => by
    rw [hzχ]; exact dom_of_tb q r t hq2 hrt z hz β hβ

  obtain ⟨α0, hα0, hw0⟩ := isZonal_one hU r
  have hint1 := ((hdouble α0 _ hw0).1 (hdom α0 (tb_triv q r hq2 α0 hα0))).1
  have hintφ : Integrable φ μ := by simpa [hΦφ] using hint1

  obtain ⟨w, hw⟩ := GlobalTheory.T.exists_zonalSphericalFunction_unramifiedUnitary L ϖ σ q r hU α
  obtain ⟨hintw, hval, -⟩ := (hdouble α w hw).1 (hdom α hα)
  simp only [hΦφ] at hintw hval
  have hFw : ∀ g, ∀ k ∈ KU σ r, φ (g * k) * w (g * k) = φ g * w g := fun g k hk => by
    have h1 := hw.1 1 ⟨k, hk⟩ g
    simp only [OneMemClass.coe_one, one_mul] at h1
    rw [hright g k hk, h1]
  have hsw := (GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ r) hKo hμK _ hFw hintw).of_norm
  have hci := (GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ r) hKo hμK (fun g => φ g * w g) _ hFw hsw.hasSum).2
  have hS1 : HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * w a.out)
      (closedForm q r (varX q r (χ ϖu) ((t : ℂ) / 2)) (varY q (χ ϖu) ((t : ℂ) / 2)) α) := by
    rw [← hval, hci]; exact hsw.hasSum

  have hsφ := GlobalTheory.T.summable_norm_coset_out' _ μ (KU σ r) hKo hμK φ hright hintφ
  have hsψ : Summable (fun a : GU σ r ⧸ KU σ r => φ a.out * ℓ (ρ a.out x)) := by
    refine Summable.of_norm_bounded (hsφ.mul_left C) fun a => ?_
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

  have hm : ∀ g : GU σ r, dosetInd ℂ (KU σ r) g ∈ Formalism.UG.Hecke ℂ (KU σ r) := fun g => Formalism.UG.Final.DosetIndMem _ _ ℂ g
  have hcond : ∀ g : GU σ r, Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ x * w g) 1 =
      Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ (ρ g x)) 1 := fun g => by
    have h1 := hw.2.2 _ (hm g)
    have h2 := congrArg ℓ (hx.2.2 _ (hm g))
    rw [map_smul, smul_eq_mul] at h2
    have e1 : Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ x * w g) 1 =
        ℓ x * Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) w 1 := by
      unfold Formalism.UG.hAct
      rw [mul_finsum]
      exact finsum_congr fun c => by simp only [smul_eq_mul]; ring
    have e2 : Formalism.UG.hAct (KU σ r) (dosetInd ℂ (KU σ r) g) (fun g => ℓ (ρ g x)) 1 =
        ℓ (GlobalTheory.LFun.heckeVec ρ (KU σ r) (dosetInd ℂ (KU σ r) g) x) := by
      refine Eq.trans (finsum_congr fun c => ?_)
        (ℓ.toAddMonoidHom.map_finsum (GlobalTheory.LFun.finite_heckeVec hK (hm g) ρ x)).symm
      simp
    rw [e1, e2, h1, h2, mul_comm]
  have hswap := GlobalTheory.T.biInvariant_replace_same_double_coset_sums _ (KU σ r) hK φ (fun g => ℓ x * w g) (fun g => ℓ (ρ g x)) _
    (fun a b g => kerU_biInv hU hφ g a.2 b.2)
    (fun a b g => by simp only [hw.1 a b g]) hcond hsψ.hasSum
  have h2 : HasSum (fun a : GU σ r ⧸ KU σ r => φ a.out * (ℓ x * w a.out))
      (closedForm q r (varX q r (χ ϖu) ((t : ℂ) / 2)) (varY q (χ ϖu) ((t : ℂ) / 2)) α * ℓ x) := by
    have h3 : (fun a : GU σ r ⧸ KU σ r => φ a.out * (ℓ x * w a.out)) = fun a => φ a.out * w a.out * ℓ x :=
      funext fun a => by ring
    rw [h3]; exact hS1.mul_right (ℓ x)
  have e := hswap.unique h2
  rw [hX, hzχ, hYe, closedForm_eq'] at e
  rw [← e]
  exact hsψ.hasSum

end GlobalTheory.ZetaSumU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorEigenOfThetaVectorAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.ThetaEigen

variable {D : D7}

def heisLin (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by funext x; simp only [heisO, Pi.add_apply, mul_add]
  map_smul' a f := by funext x; simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem heisLin_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    heisLin ψ S T w f = heisO ψ S T w f := rfl

theorem heisO_smul_comm (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (k : ℂ) (f : WO S T → ℂ) :
    heisO ψ S T w (k • f) = k • heisO ψ S T w f := (heisLin ψ S T w).map_smul k f

theorem addChar_ne_zero (ψ : AddChar (AF D.host.F) ℂ) (a : AF D.host.F) : ψ a ≠ 0 := by
  intro h
  have h1 := AddChar.map_zero_eq_one ψ
  rw [← add_neg_cancel a, AddChar.map_add_eq_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem eq_zero_of_heisO_eq_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (g : WO S T → ℂ)
    (h : heisO ψ S T w g = 0) : g = 0 := by
  funext x
  have h1 := congrFun h (x - w)
  simp only [heisO, sub_add_cancel, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_left (addChar_ne_zero ψ _)

theorem heisO_eigen_of_isThetaAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (w : WO S T) (c : ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ x : WO S T, IsHalf e x → symplO S T w x = 0) → (∀ y : WO S T, IsHalf (cA D e) y → symplO S T w y = 0) → heisO ψ S T w f₀ = c • f₀ → ∃ c' : ℂ, heisO ψ S T w f = c' • f := by
  intro D ψ S T e Λ f₀ Φ f w c hθ hx hy hc
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hθ
  have hψ0 : ψ 0 = 1 := AddChar.map_zero_eq_one ψ
  have key : ∀ k : ℂ, k • heisO ψ S T w f₀ = f₀ → f = k • heisO ψ S T w f := by
    intro k hk
    have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ (k • (heisLin ψ S T w ∘ₗ T₀)) := by
      refine ⟨fun Φ' hΦ' x hxe => ?_, fun Φ' hΦ' y hye => ?_, ?_⟩
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.trans Φ' hΦ' x hxe, GlobalTheory.Asc.heisO_comm, hx x hxe, hψ0, one_smul, heisO_smul_comm]
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.modul Φ' hΦ' y hye, GlobalTheory.Asc.heisO_comm, hy y hye, hψ0, one_smul, heisO_smul_comm]
      · simp only [LinearMap.smul_apply, LinearMap.comp_apply, heisLin_apply]
        rw [hT₀.vac, hk]
    have h2 : f = (k • (heisLin ψ S T w ∘ₗ T₀)) Φ := hall _ hT'
    have h3 : f = T₀ Φ := hall T₀ hT₀
    rw [show (k • (heisLin ψ S T w ∘ₗ T₀)) Φ = k • heisO ψ S T w (T₀ Φ) from rfl, ← h3] at h2
    exact h2
  by_cases hc0 : c = 0
  · subst hc0
    rw [zero_smul] at hc
    have hf₀ := eq_zero_of_heisO_eq_zero ψ S T w f₀ hc
    have h1 := key 1 (by rw [one_smul, hc, hf₀])
    exact ⟨1, by rw [one_smul]; rw [one_smul] at h1; exact h1.symm⟩
  · refine ⟨c, ?_⟩
    have h1 := key c⁻¹ (by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
    calc heisO ψ S T w f = c • (c⁻¹ • heisO ψ S T w f) := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      _ = c • f := by rw [← h1]

end GlobalTheory.ThetaEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingFourierJacobiStepBasePointColumn
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB

variable {D : D7}

theorem hA_smul_left (T : HSp D) (c : AE D) (y z : Fin T.rank → AE D) : hA T (c • y) z = c * hA T y z := by
  simp only [hA, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem hA_smul_right (T : HSp D) (c : AE D) (y z : Fin T.rank → AE D) : hA T y (c • z) = cA D c * hA T y z := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ratV_smul' {n : ℕ} (c : D.host.E) (v : Fin n → D.host.E) : ratV (c • v) = incA D c • ratV v := by
  funext i; simp [ratV, map_mul]

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem xFB_col (F : Frames G) (hF : Std F) (σ : ℕ) (h' : 2 * σ + 2 ≤ D.R.m) (p : Fin (σ + 1)) :
    (fun k => xFB F σ h' k p) = incA D ((-D.host.xi0) ^ (p.1 + 1)) •
      ratV (fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) := by
  obtain ⟨h2, he, -⟩ := hF.hB σ h'
  induction p using Fin.lastCases with
  | last =>
    have hc : (Fin.castLE (by omega) (Fin.last σ) : Fin (2 * σ + 2 - 1)) = ⟨σ, by omega⟩ := Fin.ext (by simp)
    funext k
    simp only [xFB, xLast, Matrix.of_apply, Fin.snoc_last, vecB, HypDec.j0, ← ratV_mulVec, Matrix.mulVec_mulVec,
      hF.ζ (σ + 1), Matrix.mulVec_smul, hF.zB' σ h', ratV_smul', Fin.val_last, hc]
  | cast i =>
    funext k
    simp only [xFB, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, rat, Matrix.map_apply, he, colsOf,
      Pi.smul_apply, smul_eq_mul, ratV, map_mul, Fin.coe_castSucc]
    rfl

theorem extY_col (F : Frames G) (hF : Std F) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)) :
    (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ
        ratV (fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
          (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) =
      incA D (star ((-D.host.xi0) ^ (p.1 + 1))) • fun k => a' k p := by
  obtain ⟨h2, he, -⟩ := hF.hJ (σ + 1) h
  have hq := ProjTgt.qY_mul_a (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)) (F.dJ (σ + 1) h) (by omega) h2 he

  rw [HypDec.extY_apply, ← Matrix.mulVec_mulVec, HypDec.pY, ← ratV_mulVec]
  have hv : ∀ (M : Matrix (Fin (σ + 1)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) D.host.E)
      (N : Matrix (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) (Fin (2 * (σ + 1) + 1 - 1)) D.host.E) (q : Fin (2 * (σ + 1) + 1 - 1)),
      M *ᵥ (fun k => N k q) = fun r => (M * N) r q := fun M N q => by
    funext r; simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  rw [hv, hq]
  funext k
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ratV, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single p]
  · simp only [if_true, mul_one]; ring
  · intro r _ hr
    have : ¬ ((Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev = (Fin.castLE (by omega) r).rev) := by
      intro e; apply hr; rw [Fin.rev_inj] at e; exact Fin.ext (by simpa [Fin.ext_iff] using e.symm)
    simp only [this, if_false, mul_zero, map_zero]
  · intro hp; exact absurd (Finset.mem_univ p) hp

theorem hA_xFB_col : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)) (p : Fin (σ + 1)),
    hA _ (fun k => xFB F σ h' k p) (fun k => a' k p) =
      hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p))
        ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' *ᵥ
          ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
            (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) := by
  intro D _ T L _ _ sc G _ _ _ F hF σ h h' a' p
  rw [xFB_col F hF σ h' p, extY_col F hF σ h a' p, hA_smul_left, hA_smul_right, GlobalTheory.DualPairCheck.cA_incA, star_star]

example (T : HSp D) (c : AE D) : hA T (c • 0) 0 = c * hA T 0 0 := hA_smul_left T c 0 0

end GlobalTheory.CharXFB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianPairingSelfDualCompletionIntegralAtPlacStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianPairing_selfDual_completion_integral_at_place : ∀ (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ (v : GlobalTheory.FinPl.Pl D) (z w : Fin S.rank → AE D), z ∈ latV S L (· = v) → w ∈ latV S L (· = v) → (∑ k, ∑ l, cA D (w k) * incA D (S.gram k l) * z l) ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.LatPairInt.pairing_mem_at | exact GlobalTheory.LatPairInt.pairing_mem_at | (intros; apply GlobalTheory.LatPairInt.pairing_mem_at <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexMovedHomLatticeSplitPlaceChartStatement
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
theorem _root_.GlobalTheory.T.index_movedHomLattice_splitPlaceChart : ∀ (D : D7) (S T : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsSplit (E := D.host.E) v → ∀ e, IsSplitChart D.sp.cm.sig T.gram (frameLat T) h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin T.rank → ℤ) (t : GL (Fin T.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w T.rank, ∀ k₂ ∈ KGL w T.rank, GlobalTheory.FinWeil.idx (GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)) ((GlobalTheory.FinWeilO.latF S T (frameLat S) (frameLat T)).map (GlobalTheory.FinWeilO.rhoF S T (1, embV T v (e.symm (k₁ * t * k₂))))) = qV D.host.E w ^ (S.rank * (∑ i, |d i|).toNat) := by
  first | exact @GlobalTheory.SplitIdx.index_moved_split | exact GlobalTheory.SplitIdx.index_moved_split | (intros; apply GlobalTheory.SplitIdx.index_moved_split <;> assumption)
end

