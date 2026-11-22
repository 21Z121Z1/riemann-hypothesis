import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0264
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0188
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionTargetFlagUnipotentHomEquivariant
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtDiagSumProdPairing
section
open MeasureTheory

namespace GlobalTheory

theorem hasDerivAt_diag_sum_prod_pairing
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hβ : ∀ q, (∀ x, β x q = 0) → q = 0)
    (M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (hM : ∀ x y, DifferentiableAt ℝ (fun t => M t x y) 0) :
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
      HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  classical
  set d := Module.finrank ℝ V
  let e : Module.Basis (Fin d) ℝ V := Module.finBasis ℝ V

  have hinj : Function.Injective β.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    exact hβ q (fun x => by simpa using LinearMap.congr_fun hq x)
  have hsurj : Function.Surjective β.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ℝ) (V := V)).symm).1 hinj
  choose q hq using fun i : Fin d => hsurj (e.coord i)
  have hqx : ∀ x i, β x (q i) = e.repr x i := by
    intro x i
    have := LinearMap.congr_fun (hq i) x
    simpa using this

  have hexp : ∀ x t, M t x x =
      ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j) := by
    intro x t
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.mul_sum,
      Complex.real_smul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  let c : Fin d × Fin d → ℂ := fun p => deriv (fun t => M t (e p.1) (e p.2)) 0
  refine ⟨d * d, fun k => q (finProdFinEquiv.symm k).1, fun k => q (finProdFinEquiv.symm k).2,
    fun k => c (finProdFinEquiv.symm k), fun x => ?_⟩
  have hfun : (fun t => M t x x) = fun t =>
      ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j) := funext (hexp x)
  rw [hfun]
  have hd : HasDerivAt (fun t => ∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * M t (e i) (e j))
      (∑ i, ∑ j, ((e.repr x i : ℂ) * (e.repr x j : ℂ)) * c (i, j)) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact ((hM (e i) (e j)).hasDerivAt).const_mul _
  convert hd using 1
  simp only [hqx]
  rw [← Fintype.sum_prod_type']
  rw [← (finProdFinEquiv (m := d) (n := d)).symm.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasProdLocalTwistedLFactorDivUnitaryLocalFactor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

theorem abs_quadTerm_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) {i : ℕ} (hi : 2 ≤ i) :
    ‖-quadTerm D v i‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
  have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by exact_mod_cast one_lt_absNorm v
  have hs : |quadSign D v| = 1 := by unfold quadSign; split_ifs <;> simp
  rw [norm_neg, Real.norm_eq_abs, quadTerm, abs_div, abs_pow, abs_pow, hs, one_pow,
    abs_of_pos (by positivity : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)), Real.rpow_neg (by positivity),
    Real.rpow_two]
  have h2 : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i :=
    pow_le_pow_right₀ hN.le hi
  rw [one_div]
  exact inv_anti₀ (by positivity) (by exact_mod_cast h2)

theorem hasProd_dLoc (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => dLoc D v.1) (dOff D Sb) ∧ dOff D Sb ≠ 0 := by
  have ht := D.R.rank_add_five_le
  set f : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV → ℝ :=
    fun p => -quadTerm D p.1.1 p.2.1 with hf
  have hsum0 := summable_rpow (K := D.host.F) (Sb : Set _) (σ := 2) (by norm_num)
  have hsum1 : Summable fun p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV =>
      ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) * (1 : ℝ) := by
    refine summable_mul_of_summable_norm (f := fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ))) (g := fun _ : Finset.Ioc D.R.t D.R.nV => (1 : ℝ)) ?_ ?_
    · refine hsum0.congr fun v => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · exact Summable.of_finite
  have hsum : Summable fun p => ‖f p‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hsum1
    rw [mul_one]
    have := (Finset.mem_Ioc.1 p.2.2).1
    exact abs_quadTerm_le D p.1.1 (by omega)
  have hne : ∀ p, 1 + f p ≠ 0 := fun p => by
    have h1 := abs_quadTerm_le D p.1.1 (i := p.2.1) (by have := (Finset.mem_Ioc.1 p.2.2).1; omega)
    have hN : (1 : ℝ) < (Ideal.absNorm p.1.1.asIdeal : ℕ) := by exact_mod_cast one_lt_absNorm p.1.1
    have h2 : ((Ideal.absNorm p.1.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hN (by norm_num)
    intro h0
    have : f p = -1 := by linarith
    rw [hf] at this
    simp only at this
    rw [this, norm_neg, norm_one] at h1
    linarith
  have hm := multipliable_one_add_of_summable hsum
  have hz := tprod_one_add_ne_zero_of_summable hne hsum
  have hinv : HasProd (fun p => (1 + f p)⁻¹) (∏' p, (1 + f p))⁻¹ := hm.hasProd.inv₀ hz
  have e1 : (fun p : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} × Finset.Ioc D.R.t D.R.nV => (1 + f p)⁻¹) =
      fun p => (1 - quadTerm D p.1.1 p.2.1)⁻¹ := by
    funext p; rw [hf]; ring_nf
  rw [e1] at hinv
  have hd : dOff D Sb = (∏' p, (1 + f p))⁻¹ := hinv.tprod_eq
  refine ⟨?_, hd ▸ inv_ne_zero hz⟩
  rw [hd]
  refine hinv.prod_fiberwise fun v => ?_
  have := hasProd_fintype (fun c : Finset.Ioc D.R.t D.R.nV => (1 - quadTerm D v.1 c.1)⁻¹)
  rw [Finset.prod_coe_sort (Finset.Ioc D.R.t D.R.nV) (fun i => (1 - quadTerm D v.1 i)⁻¹)] at this
  exact this

theorem hasProd_LvTw_div_dLoc : ∀ (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : Fam D.host.E) (χ : (AE D)ˣ →* Circle), Converges (above D.host.E (Sb : Set (HeightOneSpectrum (𝓞 D.host.F)))) (twist B (val χ)⁻¹) ((1 + (D.R.t : ℂ)) / 2) → HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} => LvTw B (val χ) v.1 ((1 + (D.R.t : ℂ)) / 2) / (dLoc D v.1 : ℂ)) (LSD D Sb B χ ((1 + (D.R.t : ℂ)) / 2) / (dOff D Sb : ℂ)) := by
  intro D Sb B χ h
  have h1 : HasProd (fun v : {v : HeightOneSpectrum (𝓞 D.host.F) // v ∉ Sb} =>
      LvTw B (val χ) v.1 ((1 + (D.R.t : ℂ)) / 2)) (LSD D Sb B χ ((1 + (D.R.t : ℂ)) / 2)) :=
    hasProd_Lv h
  obtain ⟨h2, h3⟩ := hasProd_dLoc D Sb
  have h4 := (h2.map Complex.ofRealHom Complex.continuous_ofReal).inv₀
    (by simpa using h3 : Complex.ofRealHom (dOff D Sb) ≠ 0)
  have h5 := h1.mul h4
  simpa [div_eq_mul_inv, Function.comp_def] using h5

end GlobalTheory.FinZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemConjSum

theorem idemSum_add_conj_idem : ∀ {D : D7} (Z : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Z →
    (e + cA D e) * (e + cA D e) = e + cA D e ∧ cA D (e + cA D e) = e + cA D e := by
  intro D Z e he
  have h1 : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have h2 : e * cA D e = 0 := he.2
  have h3 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  refine ⟨?_, ?_⟩
  · have h4 : cA D e * e = 0 := by rw [mul_comm]; exact h2
    calc (e + cA D e) * (e + cA D e) = e * e + e * cA D e + cA D e * e + cA D e * cA D e := by ring
      _ = e + cA D e := by rw [h1, h2, h4, h3]; ring
  · rw [map_add, cA_cA, add_comm]

end GlobalTheory.IdemConjSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IndexNormalizationInertNormEqNeg
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LamInert

theorem lam_qV_inert : ∀ (D : D7) (lam : ℕ →* ℂ), GlobalTheory.FinWeil.GoodNorm (GlobalTheory.FinWeil.sgO D) lam → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), IsInertAt D.host.F D.host.E v w → lam (qV D.host.E w) = -((qV D.host.F v : ℕ) : ℂ) := by
  intro D lam hl v w hw
  have hmap : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal = w.asIdeal := hw
  have hfix : ∀ x : 𝓞 D.host.F, GlobalTheory.FinWeil.sgO D (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) =
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x := fun x => by
    apply RingOfIntegers.coe_injective
    refine (GlobalTheory.FinWeil.coe_sgO D _).trans ?_
    exact (D.host.conjE_mem_hostF_iff _).1 (by
      change ((x : D.host.F) : D.host.E) ∈ _
      exact (x : D.host.F).2)
  have hstab : ∀ r ∈ w.asIdeal, GlobalTheory.FinWeil.sgO D r ∈ w.asIdeal := by
    rw [← hmap]
    have : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal ≤
        (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) v.asIdeal).comap (GlobalTheory.FinWeil.sgO D) := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_comap, hfix]
      exact Ideal.mem_map_of_mem _ hx
    exact fun r hr => this hr
  have hfin : Finite (𝓞 D.host.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have h1 := ((hl.2 w.asIdeal w.isMaximal hfin).2 hstab).1
  have hcard : Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = qV D.host.E w := by
    change _ = Ideal.absNorm w.asIdeal
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : qV D.host.E w = qV D.host.F v ^ 2 :=
    GlobalTheory.LFun.InertChart.absNorm_eq (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hw
  rw [hcard, hsq] at h1
  rw [hsq, h1]
  congr 1
  push_cast
  rw [Real.sqrt_sq (Nat.cast_nonneg _)]
  push_cast
  rfl

end GlobalTheory.LamInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InducedFunctionL2Positive
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.RealInd

theorem integral_norm_sq_pos_of_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε) (f : UJ ε → D.V), f ∈ D.fns →
    ∀ g, f g ≠ 0 → 0 < ∫ k : KG ε, ‖f k‖ ^ 2 ∂muK ε := by
  intro n ε D f hf g hg
  obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact D.flag g
  obtain ⟨u, hu, m, hm, x, t, ht, hpe⟩ := exists_langlands_decomp D.flag D.pos hp
  have hkK : k ∈ KG ε := by
    have : k ∈ (KG ε : Set (UJ ε)) := (KG_eq ε).symm ▸ hk
    exact this
  have hfk : f k ≠ 0 := by
    intro h0
    apply hg
    have e := (mem_indFun_top.1 hf).2 u hu m hm x t ht k
    rw [← hpe, inv_mul_cancel_right, h0, map_zero, smul_zero] at e
    exact e
  have hcont : Continuous fun k : KG ε => ‖f k‖ ^ 2 :=
    ((mem_indFun_top.1 hf).1.comp continuous_subtype_val).norm.pow 2
  haveI : (muK ε).IsOpenPosMeasure := by unfold muK; infer_instance
  exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := ⟨k, hkK⟩)
    (HasCompactSupport.of_compactSpace _) (fun _ => by positivity) (by simpa using hfk)

end GlobalTheory.RealInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacuumAtReframeFunctionOnHomsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFockVacuumAt_reframeFunctionOnHoms : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), IsInfFam θ → (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ (τ : D.what₂.Tau) (sT : Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 sT) f → IsFockVacAt (heisO ψ (reS S b) T) θ τ (cplxO 1 sT) (reF S T b f) := by
  first | exact @GlobalTheory.AdSpan.ReVec.FockVac.isFockVacAt_reF | exact GlobalTheory.AdSpan.ReVec.FockVac.isFockVacAt_reF | (intros; apply GlobalTheory.AdSpan.ReVec.FockVac.isFockVacAt_reF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFrameFrameChangeInverseGLMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrame_frameChangeInverseGL_mul : ∀ (D : D7) (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (βS : GL (Fin S.rank) (Lev.EAf D)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)), StdFrame.OrthFrame (reS S b) → (ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame (frPinvGL S b * βS) (stdL D.host.E (reS S b).rank) := by
  first | exact @GlobalTheory.AdSpan.ReVec.isFrame_frPinvGL_mul | exact GlobalTheory.AdSpan.ReVec.isFrame_frPinvGL_mul | (intros; apply GlobalTheory.AdSpan.ReVec.isFrame_frPinvGL_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSmoothThetaFunctionReframeFunctionOnHomsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothThetaFunction_reframeFunctionOnHoms : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ (reS S b) T (reF S T b f) := by
  first | exact @GlobalTheory.AdSpan.ReVec.ThetaCarry.isThetaFunO_reF | exact GlobalTheory.AdSpan.ReVec.ThetaCarry.isThetaFunO_reF | (intros; apply GlobalTheory.AdSpan.ReVec.ThetaCarry.isThetaFunO_reF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaAtSplitPlaceReframeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open GlobalTheory.AdSpan.ReVec
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaAtSplitPlace_reframe : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (e : AE D) (Λ : AddSubgroup (WO S T)) (Λ' : AddSubgroup (WO (reS S b) T)) (c : ℂ) (f₀ Φ f : WO S T → ℂ), (∀ x y : WO (reS S b) T, symplO (reS S b) T x y = symplO S T (reW S T b x) (reW S T b y)) → (∀ u, u ∈ Λ' ↔ reW S T b u ∈ Λ) → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → IsThetaAt ψ (symplO (reS S b) T) (heisO ψ (reS S b) T) e Λ' c (reF S T b f₀) (fun x => Φ (reW S T b x)) (reF S T b f) := by
  first | exact @GlobalTheory.ThetaAtReframe.isThetaAt_reframe | exact GlobalTheory.ThetaAtReframe.isThetaAt_reframe | (intros; apply GlobalTheory.ThetaAtReframe.isThetaAt_reframe <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacobiActionTargetFlagUnipotentHomEquivariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_action_target_flag_unipotent_hom_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T T₀ S : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (y : Mx D S.rank ρ), (∀ u ∈ UX D ρ, y ⬝ u.1 = y) → (∀ b c, cenT d S y (d.nB b * d.nC c) = d.qT S c y) ∧ (∀ n ∈ flagN d, ∀ n' ∈ flagN d, ptT d S y (n * n') = ptT d S y n + ptT d S y n' ∧ cenT d S y (n * n') = cenT d S y n + cenT d S y n' + symplOH S T₀ (ptT d S y n) (ptT d S y n') ∧ ∀ f, jacT ψ d S y (n * n') f = jacT ψ d S y n (jacT ψ d S y n' f)) ∧ (∀ n ∈ flagN d, ∀ u ∈ UX D ρ, jacT ψ d S y (n * d.levi u) = jacT ψ d S y n) ∧ ∀ n g, ptT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = actO S T₀ 1 g (ptT d S y n) ∧ cenT d S y (d.emb0 g * n * (d.emb0 g)⁻¹) = cenT d S y n := by
  first | exact @GlobalTheory.MixPer.jacT_hom | exact GlobalTheory.MixPer.jacT_hom | (intros; apply GlobalTheory.MixPer.jacT_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetWordMultiplicityAdditiveJordanHolder
section
noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.SmGL.Exponents.Additive

section General

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem exists_mem_twKer {ρ : Representation F G V} {σ : Representation F G W}
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p) (N : Subgroup G) {w : W}
    (hw : w ∈ twKer σ N 1) : ∃ v ∈ twKer ρ N 1, p v = w := by
  have : twKer σ N 1 ≤ (twKer ρ N 1).map p.toLinearMap := Submodule.span_le.2 (by
    rintro _ ⟨n, w, rfl⟩
    obtain ⟨v, rfl⟩ := hp w
    refine ⟨_, Submodule.subset_span ⟨n, v, rfl⟩, ?_⟩
    simp [p.isIntertwining])
  exact this hw

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem wordMult_exact {π : Representation ℂ (GL (Fin n) k) V}
    {π₁ : Representation ℂ (GL (Fin n) k) W} {π₂ : Representation ℂ (GL (Fin n) k) U}
    (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂) (hπ : IsSmooth π)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (he : Function.Exact ι p)
    (w : List ℂˣ) : wordMult π w = wordMult π₁ w + wordMult π₂ w := by
  unfold wordMult
  split_ifs
  swap
  · simp
  refine jhMult_exact (compMap (jacMap (points _) ι) _) (compMap (jacMap (points _) p) _)
    (isIrreducible_ofChar _) (GlobalTheory.T.jacquetModule_map_injective_of_injective k _ _ _ (points _) W V π₁ π ι hπ hι) (fun x => ?_)
    (fun x => ?_) (fun x hx => ?_)
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp u
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (p (ι u)) = 0
    rw [he.apply_apply_eq_zero]
    rfl
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer π₂ (unipRad k (points (Fin n))) 1 :=
      (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := (he (v - v')).1 (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')

theorem wordMult_of_subsingleton [Subsingleton V] (π : Representation ℂ (GL (Fin n) k) V)
    (w : List ℂˣ) : wordMult π w = 0 := by
  unfold wordMult
  split_ifs
  · have : Subsingleton (Jacquet π (unipB k (Fin n))) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact jhMult_of_subsingleton (isIrreducible_ofChar _) _
  · rfl

theorem sum_add {I : Type 1} (f : I → ℕ∞) (x y : I →₀ ℤ) (hx : ∀ c, 0 ≤ x c) (hy : ∀ c, 0 ≤ y c) :
    ((x + y).sum fun c a => (a.toNat : ℕ∞) * f c) =
      (x.sum fun c a => (a.toNat : ℕ∞) * f c) + y.sum fun c a => (a.toNat : ℕ∞) * f c := by
  classical
  rw [Finsupp.sum_of_support_subset (x + y) Finsupp.support_add _ (by simp),
    Finsupp.sum_of_support_subset x Finset.subset_union_left _ (by simp),
    Finsupp.sum_of_support_subset y Finset.subset_union_right _ (by simp),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finsupp.add_apply, Int.toNat_add (hx c) (hy c), Nat.cast_add, add_mul]

theorem wordMult_eq_sum (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π)
    (hπ : IsSmooth π) (w : List ℂˣ) :
    wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  have hfl : ∀ S : Subrepresentation π, HasFiniteLength S.toRepresentation := fun S =>
    IsFiniteLength.of_injective h
      (f := Representation.IntertwiningMap.equivLinearMapAsModule S.toRepresentation π
        ⟨S.toSubmodule.subtype, fun _ => rfl⟩) Subtype.val_injective
  have hsm : ∀ S : Subrepresentation π, IsSmooth S.toRepresentation := fun S =>
    (IsSubquotient.of_injective (σ := S.toRepresentation) (ρ := π)
      ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective).isSmooth hπ
  have key : ∀ S : Subrepresentation π, wordMult S.toRepresentation w =
      (cls S.toRepresentation (hfl S)).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases eq_or_ne S ⊥ with rfl | hS
    · have : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      have h0 : cls (⊥ : Subrepresentation π).toRepresentation (hfl ⊥) = 0 := by
        ext c
        simp [cls_apply, jhMult_of_subsingleton (IrrRep.irr _)]
      rw [h0, wordMult_of_subsingleton, Finsupp.sum_zero_index]
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hS)
    let ι : T.toRepresentation.IntertwiningMap S.toRepresentation :=
      ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hι : Function.Injective ι := Submodule.inclusion_injective hT.le
    have hps : Function.Surjective p := Submodule.Quotient.mk_surjective _
    have he : Function.Exact ι p := fun v =>
      ⟨fun hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩, by
        rintro ⟨u, rfl⟩
        exact (hp _).2 u.2⟩
    let σ : IrrRep (GL (Fin n) k) :=
      ⟨_, subQuot S T, (IsSubquotient.of_surjective p hps).isSmooth (hsm S),
        isIrreducible_subQuot hT⟩
    have hσ : cls (subQuot S T) σ.hasFiniteLength = Finsupp.single σ.cl 1 := cls_irr σ _
    obtain ⟨ψ⟩ := σ.nonempty_equiv_rep
    rw [wordMult_exact ι p (hsm S) hι hps he, cls_exact ι p hι hps he _ (hfl T) σ.hasFiniteLength,
      sum_add _ _ _ (fun c => by simp [cls_apply]) (fun c => by simp [cls_apply]), ih T hT.lt, hσ,
      Finsupp.sum_single_index (by simp), wordMult_congr ψ]
    simp [σ]
  rw [← wordMult_congr (topEquiv π), key ⊤, cls_congr (topEquiv π) _ h]

theorem wordMult_additive : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π), IsSmooth π → ∀ w : List ℂˣ, wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w :=
  fun _ _ _ _ _ _ _ _ _ π h hπ w => wordMult_eq_sum π h hπ w

end GlobalTheory.SmGL.Exponents.Additive
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeTransportCongruenceOfFrameVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeTransport_congruence_of_frameVectors : ∀ (D : D7) {r : ℕ} (Λ : Lt D.host.E r) (β : Fin r → Fin r → D.host.E) (𝔪 I : Ideal (𝓞 D.host.E)), (∀ i, β i ∈ Λ) → Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ 𝔪 • Λ → 𝔪 ≤ I → ∀ (m : Matrix (Fin r) (Fin r) (AfE D)) (κ' : Matrix (Fin r) (Fin r) (𝓞 D.host.E)), (∀ i j, κ' i j - (1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) i j ∈ I) → IsMov m Λ Λ → (∀ i, m *ᵥ toAf (β i) - toAf (∑ j, κ' j i • β j) ∈ hatV (𝔪 • Λ)) → ∀ x ∈ Λ, m *ᵥ toAf x - toAf x ∈ hatV (I • Λ) := by
  first | exact @GlobalTheory.LevCong.cong_of_frame | exact GlobalTheory.LevCong.cong_of_frame | (intros; apply GlobalTheory.LevCong.cong_of_frame <;> assumption)
end

