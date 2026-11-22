import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0340
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0655
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFockSSelf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0581
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0596
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenPerMultilinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0654
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0631
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulMemIdVOfLines
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem pX_xLast_castSucc {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (k l : Fin σ) :
    (dW.pX ⬝ xLast dW z) k l.castSucc = (1 : Mx D σ σ) k l := by
  rw [← dW.pX_jX]
  simp only [Matrix.mul_apply, SuppShift.xLast_castSucc]

theorem pX_xLast_last {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (k : Fin σ) :
    (dW.pX ⬝ xLast dW z) k (Fin.last σ) = 0 := by
  have h : (dW.pX ⬝ xLast dW z) k (Fin.last σ) = ((dW.pX ⬝ dW.j0) *ᵥ ratV z) k := by
    rw [← Matrix.mulVec_mulVec]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, SuppShift.xLast_last]
  rw [h, dW.pX_j0, Matrix.zero_mulVec, Pi.zero_apply]

theorem pX_xLast_mul_apply {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E)
    (N : Mx D (σ + 1) (σ + 1)) (k : Fin σ) (j : Fin (σ + 1)) :
    (dW.pX ⬝ (xLast dW z ⬝ N)) k j = N k.castSucc j := by
  rw [← Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_castSucc, pX_xLast_last, zero_mul, add_zero]
  simp only [pX_xLast_castSucc, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem psiE_idem_entry {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {σ : ℕ}
    (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (LV : Lat V) (LW : Lat W) (LW₀ : Lat W₀)
    {v : Pl D} (hm : MonoAt dW LW LW₀ v) (hp : PrimAt ψ dV LV v) (hc : ColsAt dV (xLast dW z) LV LW v)
    (N : Mx D (σ + 1) (σ + 1))
    (hY : ∀ y ∈ latV V LV (· = v), (xLast dW z ⬝ N ⬝ dV.pX) *ᵥ y ∈ latA W LW (· = v))
    (i j : Fin (σ + 1)) (hij : j.1 = i.1 + 1) : psiE ψ (idem D (· = v) * N i j) = 1 := by
  obtain ⟨-, -, -, -, -, -, f7⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hiσ : i.1 < σ := by have := j.2; omega
  set i' : Fin σ := ⟨i.1, hiσ⟩ with hi'
  have hii : i'.castSucc = i := Fin.ext rfl
  set s := idem D (· = v) * N i j with hsdef
  have hs : s ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (idem_mem_idAt _)
  have key : ∀ a : AE D, colMul dV.jX j a ∈ latV V LV (· = v) → colMul dV.jX i (s * a) ∈ latV V LV (· = v) := by
    intro a ha
    have haA : a ∈ idAt D (· = v) := GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul dV ha
    have h1 := hY _ ha
    rw [PsiUnit.mulVec_colMul, Matrix.mul_assoc, dV.pX_jX, Matrix.mul_one] at h1
    have hb : N i j * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ haA
    have h2 : colMul (xLast dW z) i (N i j * a) ∈ latA W LW (· = v) := by
      refine (f7 W LW _).2 ⟨fun k => Ideal.mul_mem_right _ _ hb, fun t ht => ?_⟩
      have h3 := ((f7 W LW _).1 h1).2 t ht
      have h4 := ((hm _).1 h3).1 i'
      have e1 : (dW.pX *ᵥ (t • colMul (xLast dW z ⬝ N) j a)) i' = t * (a * N i j) := by
        rw [Matrix.mulVec_smul, PsiUnit.mulVec_colMul, Pi.smul_apply, smul_eq_mul, colMul,
          pX_xLast_mul_apply dW z N, hii]
      rw [e1] at h4
      convert h4 using 1
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, colMul, ← hii, SuppShift.xLast_castSucc]
      ring
    have h5 := (hc i (N i j * a) hb).2 h2
    have e2 : s * a = N i j * a := by
      rw [hsdef, mul_comm (idem D (· = v)), mul_assoc, (mem_idAt_iff _ a).1 haA]
    rwa [e2]
  have h6 := (hp i j hij s hs).1 key (idem D (· = v)) (idem_mem_intAt _)
  rwa [hsdef, mul_assoc, mul_comm (N i j), ← mul_assoc, idem_mul_self] at h6

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem mul_mem_idV_of_lines {V V₀ W W₀ : HSp D} {σ : ℕ} (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ)
    (z : Fin W₀.rank → D.host.E) (LV : Lat V) (A : AddSubgroup (Fin W.rank → AE D)) (𝔟V 𝔟W : GlobalTheory.SeeSaw.FI D) {v : Pl D}
    (k : Fin σ) (j : Fin (σ + 1)) (hV : ∀ a ∈ GlobalTheory.SeeSaw.idV 𝔟V v, colMul dV.jX j a ∈ latV V LV (· = v))
    (hW : ∀ y ∈ A, (dW.pX *ᵥ y) k ∈ GlobalTheory.SeeSaw.idV 𝔟W v) (N : Mx D (σ + 1) (σ + 1))
    (hY : ∀ y ∈ latV V LV (· = v), (xLast dW z ⬝ N ⬝ dV.pX) *ᵥ y ∈ A) :
    ∀ a ∈ GlobalTheory.SeeSaw.idV 𝔟V v, N k.castSucc j * a ∈ GlobalTheory.SeeSaw.idV 𝔟W v := by
  intro a ha
  have h1 := hY _ (hV a ha)
  rw [PsiUnit.mulVec_colMul, Matrix.mul_assoc, dV.pX_jX, Matrix.mul_one] at h1
  have h2 := hW _ h1
  rwa [PsiUnit.mulVec_colMul, colMul, pX_xLast_mul_apply dW z N k j, mul_comm] at h2

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem span_neg (x : D.host.E) : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-x) = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x :=
  (FractionalIdeal.spanSingleton_eq_spanSingleton).2 ⟨-1, by simp⟩

theorem line_ratio (I 𝔞 𝔞' : GlobalTheory.SeeSaw.FI D) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) (x : D.host.E) (hx : x ≠ 0) (n k : ℕ) :
    I * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1)))⁻¹ * (𝔞 ^ n * (𝔞' ^ (k + 1))⁻¹) *
      ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1 + 1)))⁻¹ * (𝔞 ^ n * (𝔞' ^ (k + 1 + 1))⁻¹))⁻¹ =
      I * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x * 𝔞' := by
  have hs : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  rw [pow_succ x (k + 1), ← FractionalIdeal.spanSingleton_mul_spanSingleton, pow_succ 𝔞' (k + 1)]
  have h1 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1)) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact pow_ne_zero _ hx
  have h2 : 𝔞' ^ (k + 1) ≠ 0 := pow_ne_zero _ h𝔞'
  have h3 : 𝔞 ^ n ≠ 0 := pow_ne_zero _ h𝔞
  field_simp

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

variable {D : D7}

theorem line_ratio' (I 𝔞 𝔞' : GlobalTheory.SeeSaw.FI D) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) (x : D.host.E) (hx : x ≠ 0) (n k : ℕ) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x ^ (k + 1))⁻¹) * (𝔞 ^ n * (𝔞' ^ (k + 1))⁻¹) * I *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x ^ (k + 1 + 1))⁻¹) * (𝔞 ^ n * (𝔞' ^ (k + 1 + 1))⁻¹))⁻¹ =
      I * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x * 𝔞' := by
  rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_inv]
  rw [← line_ratio I 𝔞 𝔞' h𝔞 h𝔞' x hx n k]
  ring

end GlobalTheory.UniStepFB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesCuspidal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PoinCusp

theorem poin_isCuspFun : GlobalTheory.Published.DiscreteSeriesCoefficientsCuspidal → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, IsCuspFun V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro hP D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hT a
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  intro r C hC μ 𝓕 hμ h𝓕 g
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5; haveI := i7
  haveI : LocallyCompactSpace (NI V C) := (GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace
  haveI : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := hμ
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK
  have hm : Measurable (coef θ M K v fun τ => (a τ : M.H τ)) := GlobalTheory.T.measurable_level_indicator_coefficient_test_function D θ hθ V S M Λ 𝔪 hΛ h𝔪 v _
  set f : GA D V → ℂ := fun y => coef θ M K v (fun τ => (a τ : M.H τ)) (c * y * g) with hf
  have hfm : ∀ γ : GA D V, Measurable fun h : NI V C => f (γ * (NI V C).subtype h) := fun γ =>
    hm.comp ((continuous_const.mul (continuous_const.mul continuous_subtype_val)).mul continuous_const).measurable
  obtain ⟨-, Kc, hKc, hcov⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩
  have hcov' : ∀ h : NI V C, ∃ δ ∈ (GQ V).comap (NI V C).subtype, δ * h ∈ Kc := fun h => by
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, by simpa using hk⟩
  obtain ⟨B, hB⟩ := GlobalTheory.T.poincareSeries_partialSums_bounded_compact D θ hθ V S M Λ 𝔪 hΛ v hv hT c a ((fun h : NI V C => (h : GA D V) * g) '' Kc)
    (hKc.image (continuous_subtype_val.mul continuous_const))
  have hpt : ∀ h ∈ Kc, ∑' γ : GQ V, ‖f (γ * (NI V C).subtype h) * 1‖ₑ ≤ ENNReal.ofReal B := by
    intro h hh
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have e : ∀ γ : GQ V, f (↑γ * (NI V C).subtype h) * 1 =
        coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * ((h : GA D V) * g)) := fun γ => by
      simp only [hf, mul_one, Subgroup.coe_subtype, mul_assoc]
    simp only [e, ← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hB _ ⟨h, hh, rfl⟩ s)
  have hfin : (∑' q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫⁻ h, ‖f ((q.out : GQ V) * (NI V C).subtype h) * 1‖ₑ ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (GlobalTheory.T.lintegral_unfolding_le_of_translate_cover (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) Kc hcov'
      (fun y => ‖f y * 1‖ₑ) (fun γ => ((hfm γ).mul_const 1).enorm))
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B)) (hKc.measure_lt_top (μ := μ)).ne) ?_
    calc _ ≤ ∫⁻ _ in Kc, ENNReal.ofReal B ∂μ := setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal B * μ Kc := setLIntegral_const _ _
  have hunf := GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) 𝓕 h𝓕 f (fun _ => 1)
    hfm measurable_const (fun _ _ _ => rfl) hfin
  have hzero : ∀ q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ = 0 := by
    intro q
    obtain ⟨τ⟩ := hT
    obtain ⟨P, Q, hPc, hQc, hcomm, hgen, htriv, hvan⟩ := GlobalTheory.T.exists_closed_parabolic_subgroups hP D θ hθ V S M K v (fun τ => (a τ : M.H τ))
      (fun τ => (hv τ).1) (fun τ => (a τ).2) τ r C hC
    have := GlobalTheory.T.integral_haar_eq_zero_of_fibre_integrals_eq_zero_alt (NI V C) μ hμ P Q hPc hQc hcomm hgen htriv
      (fun n => coef θ M K v (fun τ => (a τ : M.H τ)) ((c * (q.out : GQ V)) * (n : GA D V) * g))
      (fun ν hν q' hq' => hvan ν hν q' hq' _ g)
    simpa [hf, mul_assoc] using this
  have hsum0 : HasSum (fun q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) =>
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ) 0 := by
    simpa only [hzero] using (hasSum_zero : HasSum (fun _ : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) => (0:ℂ)) 0)
  have h0 := hunf.2.unique hsum0
  rw [← h0]
  refine integral_congr_ae (.of_forall fun n => ?_)
  simp only [poin, hf, mul_one, Subgroup.coe_subtype, mul_assoc]

end GlobalTheory.PoinCusp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowChainLastStepVectorEqThetaOfDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipTopChain

open Classical in

theorem transport {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (k : ℕ)
    (P : Finset (Pl D.host.E)) (ψ : AddChar (AF D.host.F) ℂ) (e : AE D)
    {S S' : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)}
    {X Y : LSp D} (hX : X = ⟨S, ΛS⟩) (hY : Y = ⟨S', ΛS'⟩)
    {βS : GL (Fin X.sp.rank) (EAf D)} {βT : GL (Fin Y.sp.rank) (EAf D)} {βS₀ : GL (Fin S.rank) (EAf D)}
    {βT₀ : GL (Fin S'.rank) (EAf D)} (h1 : HEq βS βS₀) (h2 : HEq βT βT₀)
    {f₀ g : WO X.sp Y.sp → ℂ} {f₀' g' : WO S S' → ℂ} (h3 : HEq f₀ f₀') (h4 : HEq g g')
    (ha : X.sp.rank = D.R.r + k * D.R.t) (hb : Y.sp.rank = D.R.r + (k + 1) * D.R.t)
    (ha' : S.rank = D.R.r + k * D.R.t) (hb' : S'.rank = D.R.r + (k + 1) * D.R.t)
    (Ω : Matrix (Fin S'.rank) (Fin S.rank) (EAf D) → ℂ)
    (hN : ∀ N, IsIntM N → Ω N = ∏ w ∈ P, stepFn L t w k
      ((N.map (cpt (D := D) w)).submatrix (Comparison₂.ixOf G t w hb') (Comparison₂.ixOf G t w ha')))
    (hθ : IsThetaAt ψ (symplO S S') (heisO ψ S S') e (latO S S' (ΛS : Set _) (ΛS' : Set _) fun _ => True) 1 f₀'
      (fun x => if IsHalf e x ∧ IsIntM (frMapO S S' βS₀ βT₀ x) then Ω (frMapO S S' βS₀ βT₀ x) else 0) g') :
    IsThetaAt ψ (symplO X.sp Y.sp) (heisO ψ X.sp Y.sp) e (latO X.sp Y.sp (X.lat : Set _) (Y.lat : Set _) fun _ => True) 1 f₀
      (fun x => if IsHalf e x ∧ IsIntM (Comparison₂.fr βT βS (x.map (toEAf D))) then
        ∏ w ∈ P, stepFn L t w k (((Comparison₂.fr βT βS (x.map (toEAf D))).map (cpt (D := D) w)).submatrix
          (Comparison₂.ixOf G t w hb) (Comparison₂.ixOf G t w ha)) else 0) g := by
  subst hX hY
  obtain rfl := eq_of_heq h1
  obtain rfl := eq_of_heq h2
  obtain rfl := eq_of_heq h3
  obtain rfl := eq_of_heq h4
  convert hθ using 2
  rename_i x
  by_cases h : IsHalf e x ∧ IsIntM (Comparison₂.fr βT βS (x.map (toEAf D)))
  · have h' : IsHalf e x ∧ IsIntM (frMapO S S' βS βT x) := h
    rw [if_pos h, if_pos h']
    exact (hN _ h.2).symm
  · have h' : ¬ (IsHalf e x ∧ IsIntM (frMapO S S' βS βT x)) := h
    rw [if_neg h, if_neg h']

end GlobalTheory.FlipTopChain

namespace GlobalTheory.FlipTopChain

theorem colY_eq_m {D : D7} {T : Type} (L : LevCh D T) : ∀ n, n = D.R.m → columnBlock L n = ⟨D.sp.X', L.ΛX⟩ := by
  rintro _ rfl; exact colY_m L

theorem colFrame_eq_m {D : D7} {T : Type} (L : LevCh D T) : ∀ n, n = D.R.m → HEq (colFrame L n) L.βX := by
  rintro _ rfl; exact colFrame_m L

set_option maxHeartbeats 1600000 in

theorem last_step_theta : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {large₂ : SizeData₂ D},
    HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ∀ (t : T) (j : Fin D.R.m) (g : Sch ch.G (.down t 0 j)) (hj : (j : ℕ) + 1 = D.R.m),
    HEq g (R.vX t) → ∃ e' : AE D, IsIdemSum e' (GlobalTheory.FlipTop.topPl R.toLevCh t) ∧
      IsThetaAt ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e' (latO (ch.G.pS (.mu t 0 j)) (ch.G.pT (.mu t 0 j)) (ch.G.latS (.mu t 0 j) : Set _) (ch.G.latT (.mu t 0 j) : Set _) fun _ => True) 1 (ch.rm.vT 0 j)
        (GlobalTheory.FlipTop.topFn ch.S.B t e' j (GlobalTheory.FlipTop.rank_col ch.G (by omega)) (GlobalTheory.FlipTop.rank_col ch.G (by omega))) g := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R F large₂ hS ch hch t j g hj hg
  obtain ⟨k, hk⟩ := j
  simp only at hj
  obtain rfl : k = D.R.m - 1 := by omega
  obtain ⟨-, e', he', hθ⟩ := hS.core.chain.vX t
  refine ⟨e', he', ?_⟩
  have hm : D.R.m - 1 < D.R.m := hk
  have hb' : D.sp.X'.rank = D.R.r + (D.R.m - 1 + 1) * D.R.t := by
    rw [hj]; exact D.sp.X'_rank
  have hN := (Comparison₂.local_factors ch.S.B t hS.core.lev).2.2 (D.R.m - 1) hm _ hb'
  have hchi : R.toLevCh.chi (D.R.m - 1 + 1) = R.toLevCh.chi D.R.m := by rw [hj]
  rw [hchi] at hN
  unfold GlobalTheory.FlipTop.topFn
  exact transport ch.G t (D.R.m - 1) _ ch.W.ψ e' (X := ch.G.node (.grid 0 (D.R.m - 1)))
    (Y := ch.G.node (.grid 0 (D.R.m - 1 + 1))) (colY_lt R.toLevCh hm) (colY_eq_m R.toLevCh _ hj)
    (colFrame_lt R.toLevCh hm) (colFrame_eq_m R.toLevCh _ hj) (hch.vac.2 _ hj) hg _ _ (Comparison₂.rank_Yc hm.le) hb' _ hN
    (hch.weil.ψ ▸ hθ)

end GlobalTheory.FlipTopChain

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodsInvariantFunctional
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def pullBil {V₁ V₂ W₁ W₂ : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₁]
    [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (a : V₁ →ₗ[ℂ] W₁) (b : V₂ →ₗ[ℂ] W₂) :
    (W₁ →ₗ[ℂ] W₂ →ₗ[ℂ] ℂ) →ₗ[ℂ] (V₁ →ₗ[ℂ] V₂ →ₗ[ℂ] ℂ) where
  toFun f := f.compl₁₂ a b
  map_add' f f' := by ext; simp
  map_smul' c f := by ext; simp

theorem invLine_of_iso [DecidableEq D.what₂.Tau] (ch : Choice R) {μ0 : T} (hL : R.toLevCh.Is μ0)
    (hlf : (∀ a ξ, ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g,
      pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) (γ * g) =
        pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ) ξ (ch.col a) g) ∧
      ∀ t y η, ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formGen ch t y η (γ * g) = formGen ch t y η g)
    (hc : ∀ t a, ch.S.SumOK t (ch.Phi a) → ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M : Vol ch.G,
      IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ → ∀ d ∈ τ.support,
        ∀ y Q ξ η, GenConv ch t a M d y Q ξ η)
    (Aψ : weylSub ((rowSizes D).nR (0 : Fin ((rowSizes D).m + 1))) (psiWt (rowEntries D ch.sc.cGap)) ≃ₗ[ℂ]
      Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).W)
    (hA : ∀ g F, Aψ (psiRep (rowEntries D ch.sc.cGap) g F) =
      Aψ F ∘ₗ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus ch.G ch.W.θ).ρ ((kappa ch.W g).1 ⟨0, (rowSizes D).m_pos⟩)⁻¹)
    (Bf : Module.Dual ℂ (weylSub ((rowSizes D).nC (0 : Fin ((rowSizes D).m + 1))) (baseWt (rowEntries D ch.sc.cGap))) ≃ₗ[ℂ]
      Module.Dual ℂ R.cX.W)
    (hB : ∀ g φ, Bf ((baseRep (rowEntries D ch.sc.cGap)).dual g φ) =
      Bf φ ∘ₗ R.cX.ρ (cast (congrArg (fun X : LSp D => GA D X.sp) (colY_m R.toLevCh)) ((kappa ch.W g).2 0))⁻¹) :
    InvLine ch := by
  classical
  obtain ⟨tc, tr, htr⟩ := GlobalTheory.RowReal.exists_fock_transport hL ch.W
  refine ⟨D.what₂.Tau, inferInstance, inferInstance, rowSizes D, rowEntries D ch.sc.cGap,
    fun τ => rowEntries_good D _ τ, fun Q => PiTensorProduct.tprod ℂ (fun j => tc j (Q.1 j)) ⊗ₜ[ℂ]
      (PiTensorProduct.tprod ℂ (fun i => tr i (Q.2 i)) ⊗ₜ[ℂ] (Aψ.symm ch.ξ ⊗ₜ[ℂ] Bf.symm (R.prX.flip ch.cv.v))), ?_⟩
  intro t a hS β hβ M hM τ hτ d hd y
  obtain ⟨Φ0, hΦ0⟩ := GlobalTheory.RowReal.genPer_multilinear ch t a M d y (hc t a hS β hβ M hM τ hτ d hd y)
  let Irow := (LinearMap.compMultilinearMapₗ ℂ (pullBil Aψ.toLinearMap Bf.toLinearMap)) ∘ₗ
    (MultilinearMap.compLinearMapₗ (fun i : Fin D.R.m => (tr i).symm.toLinearMap))
  let Φ := (Irow.compMultilinearMap Φ0).compLinearMap (fun j : Fin D.R.m => (tc j).symm.toLinearMap)
  have hΦ : ∀ x₁ y₁ v₁ φ₁, Φ x₁ y₁ v₁ φ₁ =
      genPer ch t a M d y (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i)) (Aψ v₁) (Bf φ₁) :=
    fun x₁ y₁ v₁ φ₁ => hΦ0 (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i)) (Aψ v₁) (Bf φ₁)
  have hv := hS.vec β τ hτ d hd
  have hinv : ∀ g x₁ y₁ v₁ φ₁, Φ (fun j => rowFock (rowEntries D ch.sc.cGap) j g (x₁ j))
      (fun i => colFock (rowEntries D ch.sc.cGap) i g (y₁ i)) (psiRep (rowEntries D ch.sc.cGap) g v₁)
      ((baseRep (rowEntries D ch.sc.cGap)).dual g φ₁) = Φ x₁ y₁ v₁ φ₁ := by
    intro g x₁ y₁ v₁ φ₁
    rw [hΦ, hΦ, hA, hB]
    obtain ⟨h1, h2⟩ := htr ch.S.toGridChoice g t
    have e1 : ptTop ch.W g 0 = (kappa ch.W g).1 ⟨0, (rowSizes D).m_pos⟩ := ptTop_lt ch.W g _
    have e2 : ptGrid ch.W g 0 = (kappa ch.W g).2 0 := ptGrid_le ch.W g (Nat.succ_pos _)
    have key := GlobalTheory.RowReal.genPer_move ch hL t a M d y (fun j => ⟨_, hM.1 j j.2⟩) (fun i => ⟨_, hM.2 i (Nat.le_of_lt_succ i.2)⟩)
      hv.1 hv.2 (hlf.1 a) (hlf.2 t y) g (fun j => (tc j).symm (x₁ j), fun i => (tr i).symm (y₁ i))
      (fun j => (tc j).symm (rowFock (rowEntries D ch.sc.cGap) j g (x₁ j)),
        fun i => (tr i).symm (colFock (rowEntries D ch.sc.cGap) i g (y₁ i)))
      (fun j => by simpa using h1 j (d.1 j) (hv.1 j) ((tc j).symm (x₁ j)))
      (fun i => by simpa using h2 i (d.2 i) (hv.2 i) ((tr i).symm (y₁ i))) (Aψ v₁) (Bf φ₁)
    rw [e1, e2] at key
    exact key
  obtain ⟨l, hl, hle⟩ := GlobalTheory.RowReal.invFun_of_multilinear (rowEntries D ch.sc.cGap) Φ hinv
  refine ⟨l, hl, fun Q => ?_⟩
  rw [hle]
  refine Eq.trans ?_ (hΦ _ _ _ _).symm
  simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem invLine_big : Big fun ch => InvLine ch := by
  obtain ⟨C1, h1⟩ := GlobalTheory.RowReal.gen_left
  obtain ⟨C2, h2⟩ := GlobalTheory.GenConvProof.genPer_conv
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, h1'⟩ := h1 ε CF (le_of_max_le_left hCF)
  obtain ⟨x2, h2'⟩ := h2 ε CF (le_of_max_le_right hCF)
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc => ?_⟩
  classical
  have hlf := h1' D large₂ he (le_of_max_le_left hx) Γ Pl0 T A Ks R F hS ch hch hsc
  have hc := h2' D large₂ he (le_of_max_le_right hx) Γ Pl0 T A Ks R F hS ch hch hsc
  have hL := hS.core.lev
  obtain ⟨Aψ, hA⟩ := GlobalTheory.CoefPsi.coefPsi ch.W (posOnb_of_defNode ch.W A.μ0 hL (X := .top 0) (Nat.zero_le _))
  obtain ⟨Bf, hB⟩ := GlobalTheory.CoefBase.coefBase ch hS.core.models.inf hS.core.models.cX hS.core.models.prX hch.weil
    (posOnb_of_defNode ch.W A.μ0 hL (X := .grid 0 D.R.m) ⟨Nat.zero_le _, rfl⟩)
  exact invLine_of_iso ch hL hlf hc Aψ hA Bf hB

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingDoubling
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section

namespace GlobalTheory.SquareAgree.DatA

theorem datum_lieDer : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ) (γ : Multiplicative ℝ →* UA D.sp.cm.sig Γ.W.J),
    (∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hO.JX (oneP θ X τ Y t)) → γ ∈ Lines D.sp.cm.sig Γ.W →
    ∀ (Φ Φ' : WO W X → ℂ), IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ' →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F)) (m : ℕ) (f f₁ : Fin m → SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
      (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
    (∀ i, f i ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ v ∉ T, φ i v = Γ.M.vac v) →
    (∀ i, ActsD (evI D.host.F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (f i) (f₁ i)) →
    IsDatum Γ.M ψ cA (∑ i, pure (f i) (φ i)) Φ →
    ∀ Φ'D, IsDatum Γ.M ψ cA Φ'D Φ' → Φ'D = ∑ i, pure (f₁ i) (φ i) := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ hγ hL Φ Φ' hD T m f f₁ φ hf hA hΦ Φ'D hΦ'
  have hM := hT.geo.hM
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 := by
    intro i
    filter_upwards [hM.std, T.finite_toSet.compl_mem_cofinite] with v hv hvT
    rw [(hf i).2.2 v hvT, hv]
  have hrest : ∀ i, Rest (evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun i =>
    ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by
      rw [← GlobalTheory.EvZeroInf.pure_eq_tens]; exact GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstd i)⟩
  have hsum : ∀ g : Fin m → SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)),
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (g i) (φ i) = ∑ i, tens (evI D.host.F) (⇑(g i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun g =>
    Finset.sum_congr rfl fun i _ => GlobalTheory.EvZeroInf.pure_eq_tens _ _
  have hone : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW 1 = 1 := by
    apply Subtype.ext; simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU]
  have hstdψ : IsStd ψ := hO.psi ▸ hT.base.std
  have hmem : ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i) ∈ GlobalTheory.WeilM.schA D.host.F _ :=
    Submodule.sum_mem _ fun i _ => GlobalTheory.TensUniq.pure_mem_schA _ _ (hf i).2.1 (hstd i)
  have hDat : IsDatum Γ.M ψ cA (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f₁ i) (φ i)) Φ' := by
    refine ⟨hmem, fun u => ?_⟩
    have h1 : HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho ψ u
        (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))))) (Φ' (cA u)) 0 := by
      have h2 := hD (cA u)
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      have h3 := (hO.weilA _ _ hΦ 1 (oneP θ X τ Y t)).2 u
      rw [hone, ← hγ t] at h3
      exact h3
    have h4 := GlobalTheory.T.restriction_line_operator_sum hP Bs Γ Xc om om' hT γ hL m f f₁ (fun i => GlobalTheory.EvZeroInf.finPart (φ i)) hrest hA u
    rw [← hsum, ← hsum, hO.psi] at h4
    exact h4.unique h1
  exact GlobalTheory.ThetaInj.theta_inj Γ.M ψ hstdψ cA Φ'D _ Φ' hΦ' hDat

end GlobalTheory.SquareAgree.DatA
end
end

