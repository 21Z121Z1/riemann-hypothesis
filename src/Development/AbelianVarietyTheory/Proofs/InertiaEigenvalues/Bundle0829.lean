import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightDominantIsoExists
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0657
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightDominantIsoExistsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_weight_dominant_iso_exists : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (emb : ι → L →+* ℂ), Function.Injective (emb) → (∀ t t', (emb) t ≠ ComplexEmbedding.conjugate ((emb) t')) → (∀ σ : L →+* ℂ, ∃ t, σ = (emb) t ∨ σ = ComplexEmbedding.conjugate ((emb) t)) → ∀ a : NG.AlgWt L n, ∃ (lam : ι → DomWeight n) (T : a.W ≃ₗ[ℂ] VV ℂ lam), ∀ (γ : ReciprocityTheory.Aut.GQ L n) (γ₀ : GL (Fin n) L), (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → ∀ x, T (a.ρ γ x) = rhoVr emb lam γ₀ (T x) := by
  first | exact @GlobalTheory.WtClass.exists_equiv_VV | exact GlobalTheory.WtClass.exists_equiv_VV | (intros; apply GlobalTheory.WtClass.exists_equiv_VV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipScalarMemCoefficientField
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipScalField

open Formalism.L2.Host

def sqN {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) : ℝ :=
  Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)

theorem absNorm_pos {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

theorem sqN_pos {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) : 0 < sqN v :=
  Real.sqrt_pos.2 (absNorm_pos v)

theorem sqN_sq {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    sqN v ^ 2 = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
  Real.sq_sqrt (absNorm_pos v).le

theorem cpow_neg_half (n : ℕ) :
    ((n : ℕ) : ℂ) ^ (-(((-1 / 2 : ℝ)) : ℂ)) = ((Real.sqrt n : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  congr 1
  ring

theorem ordF_natCast {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (u : Eˣ) (M₀ : ℕ)
    (hu : (u : E) = ((M₀ : ℕ) : E)) :
    ordF v u = ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {((M₀ : ℕ) : 𝓞 E)})).factors : ℤ) := by
  have h0 : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by
    intro h
    have : ((M₀ : ℕ) : E) = 0 := by
      have := congrArg (algebraMap (𝓞 E) E) h
      simpa using this
    exact u.ne_zero (hu.trans this)
  have e : (u : E) = algebraMap (𝓞 E) E ((M₀ : ℕ) : 𝓞 E) := by rw [hu, map_natCast]
  rw [ordF, e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v h0,
    WithZero.log_exp, neg_neg]

end GlobalTheory.FlipScalField

namespace GlobalTheory.FlipScalField
open Formalism.L2.Host

set_option maxHeartbeats 800000 in

theorem mem_fieldRange : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ r w : ℕ) (u a : Eˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (k : Type) [Field k] (σ : k →+* ℂ), Odd w → (u : E) = ((M₀ : ℕ) : E) → IsIntegral ℤ (a : E) → (∀ v ∈ T, ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∉ v.asIdeal → χ.UnrAt v) → χ.ValuesIn (-1 / 2) σ → (∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| ^ (-(w : ℝ) / 2) : ℝ) : ℂ)) → (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1) → (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ r) * ((Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * w) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ ∈ σ.fieldRange := by
  intro E _ _ χ M₀ r w u a T k _ σ hw hu ha hT hunr hval hinf hTa hST
  classical
  have hM0 : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by
    intro h
    have : ((M₀ : ℕ) : E) = 0 := by
      have := congrArg (algebraMap (𝓞 E) E) h
      simpa using this
    exact u.ne_zero (hu.trans this)
  have hSfin : {v : HeightOneSpectrum (𝓞 E) | ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((M₀ : ℕ) : 𝓞 E)}) ?_).subset fun v hv => ?_
    · rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  set S := hSfin.toFinset with hSdef
  have hmemS : ∀ v, v ∈ S ↔ ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal := fun v => Set.Finite.mem_toFinset _
  set R := (GlobalTheory.HeckeProduct.finite_ordF a).toFinset with hRdef
  have hR : ∀ v, v ∉ R → ordF v a = 0 := fun v hv => by
    by_contra h; exact hv ((Set.Finite.mem_toFinset _).2 h)
  have hTS : T ⊆ S := fun v hv => (hmemS v).2 (hT v hv)
  have hoST : ∀ v ∈ S, v ∉ T → ordF v a = 0 := fun v hv hvT => by
    rw [ordF, (hST v ((hmemS v).1 hv) hvT).2, WithZero.log_one, neg_zero]
  have hoT : ∀ v ∈ T, ordF v a = ordF v u := fun v hv => by
    rw [ordF, ordF, (hTa v hv).2, hu]
  have hPR := Formalism.L2.Host.HChar.productRule χ S (fun v hv => hunr v (fun h => hv ((hmemS v).2 h))) a
  have hloc : ∏ v ∈ S, χ.locK v a = ∏ v ∈ T, χ.locK v u := by
    rw [← Finset.prod_subset hTS (fun v hv hvT => (hST v ((hmemS v).1 hv) hvT).1)]
    exact Finset.prod_congr rfl fun v hv => (hTa v hv).1
  have hfin : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), χ.val v ^ ordF v a) =
      ∏ v ∈ R \ S, χ.val v ^ ordF v a := by
    apply finprod_mem_eq_prod_of_subset (s := {v | v ∉ S})
    · rintro v ⟨hv1, hv2⟩
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe]
      refine ⟨?_, hv1⟩
      by_contra h
      exact hv2 (by simp [hR v h])
    · intro v hv
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hv
      exact hv.2
  rw [hloc, hfin] at hPR
  choose! y hy using hval
  have hvalv : ∀ v, v ∉ S → ((χ.val v : ℂˣ) : ℂ) = σ (y v) / ((sqN v : ℝ) : ℂ) := fun v hv => by
    have h1 := hy v (hunr v fun h => hv ((hmemS v).2 h))
    have h2 : ((sqN v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sqN_pos v).ne'
    rw [h1, HChar.valTw, cpow_neg_half, ← sqN, mul_div_assoc, div_self h2, mul_one]
  obtain ⟨y0, hy0⟩ := hinf
  set Q : ℝ := ∏ v ∈ R, sqN v ^ ordF v a with hQ
  have hQpos : 0 < Q := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hNa : |((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| = Q ^ 2 := by
    rw [← PI.AlgValsFin.W.prod_norm_emb, PI.AlgValsFin.W.prodNorm a R hR, hQ, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← sqN_sq v, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  have hinfv : ((χ.inf a : ℂˣ) : ℂ) = σ y0 * (((Q ^ w)⁻¹ : ℝ) : ℂ) := by
    rw [hy0, hNa]
    congr 2
    rw [← Real.rpow_natCast Q 2, ← Real.rpow_mul hQpos.le, ← Real.rpow_natCast, ← Real.rpow_neg hQpos.le]
    congr 1
    push_cast
    ring
  set A : ℝ := ∏ v ∈ T, sqN v ^ ordF v a with hA
  set B : ℝ := ∏ v ∈ R \ S, sqN v ^ ordF v a with hB
  have hApos : 0 < A := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hBpos : 0 < B := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hQAB : Q = A * B := by
    rw [hQ, ← Finset.prod_inter_mul_prod_diff R S]
    congr 1
    have e1 : ∏ v ∈ R ∩ S, sqN v ^ ordF v a = ∏ v ∈ S, sqN v ^ ordF v a :=
      Finset.prod_subset Finset.inter_subset_right fun v hv hv' => by
        rw [hR v (fun h => hv' (Finset.mem_inter.2 ⟨h, hv⟩)), zpow_zero]
    have e2 : ∏ v ∈ T, sqN v ^ ordF v a = ∏ v ∈ S, sqN v ^ ordF v a :=
      Finset.prod_subset hTS fun v hv hvT => by rw [hoST v hv hvT, zpow_zero]
    rw [e1, ← e2]
  have hprodval : ∏ v ∈ R \ S, ((χ.val v : ℂˣ) : ℂ) ^ ordF v a =
      σ (∏ v ∈ R \ S, y v ^ ordF v a) / ((B : ℝ) : ℂ) := by
    rw [map_prod, hB, Complex.ofReal_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hvalv v (Finset.mem_sdiff.1 hv).2, map_zpow₀, Complex.ofReal_zpow, div_zpow]
  have key := congrArg (fun z : ℂˣ => (z : ℂ)) hPR
  simp only [Units.val_mul, Units.val_one, Units.coe_prod, Units.val_zpow_eq_zpow_val] at key
  rw [hinfv, hprodval, hQAB] at key
  set P : ℂ := ∏ v ∈ T, ((χ.locK v u : ℂˣ) : ℂ) with hPdef
  set Y : k := ∏ v ∈ R \ S, y v ^ ordF v a with hY
  have h1 : σ y0 ≠ 0 := fun h => by rw [h] at key; simp at key
  have h2 : σ Y ≠ 0 := fun h => by rw [h] at key; simp at key
  have hA0 : ((A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
  have hB0 : ((B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have hP : P = ((A : ℝ) : ℂ) ^ w * ((B : ℝ) : ℂ) ^ (w + 1) / (σ y0 * σ Y) := by
    rw [eq_div_iff (mul_ne_zero h1 h2)]
    push_cast at key
    field_simp at key
    linear_combination key

  have hsqrt : Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * w) : ℕ) : ℝ) =
      A ^ (r * w) := by
    rw [← Real.sqrt_sq (pow_nonneg hApos.le _)]
    congr 1
    push_cast
    rw [hA, ← Finset.prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hoT v hv, ordF_natCast v u M₀ hu, HeightOneSpectrum.maxPowDividing, map_pow, zpow_natCast]
    push_cast
    rw [← sqN_sq v]
    ring
  set q : ℚ := ∏ v ∈ R \ S, ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ ordF v a with hq
  have hqB : ((q : ℚ) : ℂ) = ((B : ℝ) : ℂ) ^ 2 := by
    have : ((q : ℚ) : ℝ) = B ^ 2 := by
      rw [hq, hB, ← Finset.prod_pow]
      push_cast
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [← sqN_sq v, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
    rw [← Complex.ofReal_ratCast, this, Complex.ofReal_pow]
  obtain ⟨m, rfl⟩ := hw
  have heq : (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ r) *
      ((Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * (2 * m + 1)) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ =
      (((q : ℚ) : ℂ) ^ (m + 1)) ^ r * ((σ y0 * σ Y)⁻¹) ^ r := by
    rw [hsqrt, Finset.prod_pow, ← hPdef, hP, hqB]
    push_cast
    field_simp
    ring
  rw [heq]
  refine mul_mem (pow_mem (pow_mem (SubfieldClass.ratCast_mem _ q) _) _) (pow_mem (inv_mem (mul_mem ?_ ?_)) _)
  · exact ⟨y0, rfl⟩
  · exact ⟨Y, rfl⟩

end GlobalTheory.FlipScalField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInvCentralFlipIdeleEqProdLocalComponents
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.FlipCharFormula

variable {D : D7}

theorem fa_mul (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a * b) Q = a Q * b Q := rfl
theorem fa_add (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a + b) Q = a Q + b Q := rfl
theorem fa_sub (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a - b) Q = a Q - b Q := rfl
theorem fa_one (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (1 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q = 1 := rfl
theorem fa_natCast (n : ℕ) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (n : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, fa_add, ih, fa_one, Nat.cast_succ]
theorem fa_sum {α : Type*} (s : Finset α) (g : α → FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) : (∑ a ∈ s, g a) Q = ∑ a ∈ s, g a Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, fa_add, ih, Finset.sum_insert ha]

theorem finPart_incA (k : D.host.E) : finPart D (incA D k) = 1 ⊗ₜ k := rfl

theorem comp_of_isIdemAt (ι : Af ↥D.host.F ⊗[↥D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ (x : D.host.E), ι (1 ⊗ₜ[↥D.host.F] x) = (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) x)
    (h2 : ∀ (y : Af ↥D.host.F ⊗[↥D.host.F] D.host.E),
      y ∈ intAE D ↔ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)), Valued.v ((ι y) P) ≤ 1)
    {e : AE D} {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ι (finPart D e) P = if P = PP then 1 else 0 := by
  obtain ⟨⟨hee, -, -⟩, hP⟩ := he
  have hidem : ∀ Q, ι (finPart D e) Q = 0 ∨ ι (finPart D e) Q = 1 := by
    intro Q
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    show ι (finPart D e) Q * ι (finPart D e) Q = ι (finPart D e) Q
    rw [← fa_mul, ← map_mul, ← map_mul, hee]
  have key : ∀ x : 𝓞 D.host.E, x ≠ 0 →
      (x ∈ PP.asIdeal ↔ ∃ Q, ι (finPart D e) Q = 1 ∧ x ∈ Q.asIdeal) := by
    intro x hx
    rw [hP x hx, h2, map_mul, finPart_incA, map_mul, h1]
    have hQ : ∀ Q, (Valued.v ((ι (finPart D e) * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
        ((x : D.host.E))⁻¹) Q) ≤ 1 ↔ ¬ (ι (finPart D e) Q = 1 ∧ x ∈ Q.asIdeal)) := by
      intro Q
      rw [fa_mul]
      rcases hidem Q with h | h
      · rw [h, zero_mul]; simp
      · rw [h, one_mul]
        have hv : Valued.v ((algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((x : D.host.E))⁻¹) Q)
            = HeightOneSpectrum.valuation D.host.E Q ((x : D.host.E))⁻¹ :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q _
        have hx0 : HeightOneSpectrum.valuation D.host.E Q (x : D.host.E) ≠ 0 := by
          simpa using hx
        rw [hv, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hx0), ← not_lt,
          HeightOneSpectrum.valuation_lt_one_iff_mem]
        simp
    simp only [hQ, not_forall, not_not]
  have hne : ∀ Q, Q ≠ PP → ι (finPart D e) Q = 0 := by
    intro Q hQ
    rcases hidem Q with h | h
    · exact h
    · exfalso
      have hnle : ¬ Q.asIdeal ≤ PP.asIdeal := by
        intro hle
        apply hQ
        exact HeightOneSpectrum.ext (Q.isMaximal.eq_of_le PP.isPrime.ne_top hle)
      obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp hnle
      have hx0 : x ≠ 0 := by rintro rfl; exact hxP PP.asIdeal.zero_mem
      exact hxP ((key x hx0).mpr ⟨Q, h, hxQ⟩)
  have hPP : ι (finPart D e) PP = 1 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
    obtain ⟨Q, hQ1, -⟩ := (key x hx0).mp hx
    by_cases hQ : Q = PP
    · rwa [hQ] at hQ1
    · rw [hne Q hQ] at hQ1; exact absurd hQ1 zero_ne_one
  split_ifs with h
  · rw [h, hPP]
  · exact hne P h

theorem infPart_of_isIdemAt {e : AE D} {PP : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) : infPart D e = 0 := by
  obtain ⟨⟨hee, hec, v, ε, ⟨α, rfl, -, -⟩, hsum⟩, -⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id (↥D.host.F) D.host.E)) ((pairA D.host.F 0 α : AF D.host.F) ⊗ₜ[↥D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    have : (fstA D.host.F) (pairA D.host.F 0 α) = 0 := rfl
    rw [this]
    exact TensorProduct.zero_tmul _ _
  have hs := congrArg (infPart D) hsum
  have hm := congrArg (infPart D) hec
  have hi := congrArg (infPart D) hee
  rw [map_add, h0] at hs
  rw [map_mul, map_zero] at hm
  rw [map_mul] at hi
  have hc : infPart D (cA D e) = - infPart D e :=
    eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hs)
  rw [hc, mul_neg, hi, neg_eq_zero] at hm
  exact hm

set_option maxHeartbeats 800000 in

theorem char_inv_eq_prod_locK_of_flip : ∀ (D : D7) (V : HSp D) (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (M₀ : ℕ) (u : D.host.Eˣ) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), ChrEq χW χ → (u : D.host.E) = ((M₀ : ℕ) : D.host.E) → IsIdemSum eT T → IsFlipDet V eT M₀ x → ((χW x : Circle) : ℂ)⁻¹ = ∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank := by
  intro D V χW χ M₀ u T eT x hχ hu hT hx
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) χW χ hχ
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hT
  unfold IsFlipDet at hx
  have heT : ∀ P, ι (finPart D (∑ PP ∈ T, es PP)) P = if P ∈ T then 1 else 0 := by
    intro P
    rw [map_sum, map_sum, fa_sum,
      Finset.sum_congr rfl (fun PP hPP => comp_of_isIdemAt ι h1 h2 (hes PP hPP) P)]
    exact Finset.sum_ite_eq T P (fun _ => (1 : HeightOneSpectrum.adicCompletion D.host.E P))
  have hinfT : infPart D (∑ PP ∈ T, es PP) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero (fun PP hPP => infPart_of_isIdemAt (hes PP hPP))
  have hinf : infPart D (x : AE D) = 1 := by
    have := congrArg (infPart D) hx
    rw [map_mul, map_add, map_mul, map_sub, hinfT, map_one, zero_mul, zero_add, sub_zero, mul_one] at this
    exact this
  have hcomp : ∀ P, ι (finPart D (x : AE D)) P *
      ((if P ∈ T then 1 else 0) * (((M₀ ^ V.rank : ℕ) : HeightOneSpectrum.adicCompletion D.host.E P))
        + (1 - if P ∈ T then 1 else 0)) = 1 := by
    intro P
    have h0 : ι (finPart D ((x : AE D) * ((∑ PP ∈ T, es PP) * ((M₀ ^ V.rank : ℕ) : AE D)
        + (1 - ∑ PP ∈ T, es PP)))) P = ι (finPart D 1) P := by
      rw [Nat.cast_pow, hx]
    simp only [map_mul, map_add, map_sub, map_one, map_natCast] at h0
    rw [fa_mul, fa_add, fa_mul, fa_sub, fa_one, fa_natCast, heT] at h0
    exact h0
  let k : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ := fun P => if P ∈ T then (u⁻¹) ^ V.rank else 1
  have hxk : ∀ P, ι (finPart D (x : AE D)) P =
      algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P) (k P : D.host.E) := by
    intro P
    have hc := hcomp P
    by_cases hP : P ∈ T
    · rw [if_pos hP, one_mul, sub_self, add_zero] at hc
      rw [show k P = (u⁻¹) ^ V.rank from if_pos hP, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hu,
        map_pow, map_inv₀, map_natCast, eq_inv_of_mul_eq_one_left hc, Nat.cast_pow, inv_pow]
    · rw [if_neg hP, zero_mul, sub_zero, zero_add, mul_one] at hc
      rw [show k P = 1 from if_neg hP, Units.val_one, map_one]
      exact hc
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have key := hprod x hinf (T ∪ (Ideal.finite_factors hI).toFinset) k
    (fun P _ => by
      rw [hxk P, sub_self, map_zero]
      exact ⟨HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _, zero_le'⟩)
    (fun P hP => by
      have hPT : P ∉ T := fun h => hP (Finset.mem_union_left _ h)
      refine ⟨?_, ?_⟩
      · rw [hxk P, show k P = 1 from if_neg hPT, Units.val_one, map_one, map_one]
      · intro hNP
        apply hP
        apply Finset.mem_union_right
        rw [Set.Finite.mem_toFinset]
        exact Ideal.dvd_span_singleton.mpr hNP)
  rw [key, ← Finset.prod_subset (Finset.subset_union_left)
    (fun P _ hPT => by rw [show k P = 1 from if_neg hPT, map_one, Units.val_one])]
  rw [Finset.prod_congr rfl (fun P hP => by
    rw [show k P = (u⁻¹) ^ V.rank from if_pos hP, map_pow, map_inv, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, inv_pow])]
  rw [Finset.prod_inv_distrib, inv_inv]

end GlobalTheory.FlipCharFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthTwistedPlacesOfHeckeIntegrality
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory

set_option maxHeartbeats 1000000 in

theorem etaJ_join_closed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → ∀ (Q : D.what₂.places.Pl → Finset (PlE D.host)), (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) → HeckeTied D M → HeckeRational D M → AVTied D M → (∀ i : D.nd.Loc, ClassSum (M.loc i)) → ∀ (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)), m = D.R.m → (∀ (i : Fin m), ∀ y ∈ S0.Tw, ∀ x, D.what₂.thetaP (tup (S0.μ y)) ((i : ℕ) + 1) (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1) (eMt i (S0.μ y) x)) = jW i ((S0.θ i (S0.μ y)).mulVec ((lPrj D A P ψ Zs i (S0.μ y)).mulVec x))) → D.nd.EigSpan → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hStd Q hQ hLatInt hHT hHR hAV hCS jW hmR hθ
    hEig hIsot h42 hZ hGood
  have hLat : ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → LatStable Tn.B j w :=
    fun j w h1 h2 hne => GlobalTheory.T.heckeStableLocalLattice_of_rationalIntegrality D M Tn Q hQ hLatInt j w h1 h2 hne
  have hTC : ∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i) := by
    intro i
    have hne := D.nd.w_tw i
    have hy : D.plEq (D.nd.w i) ∈ S0.Tw := by
      refine (hTw _).2 fun e => hne ?_
      rw [hTup.muAt, ← hTup.mu0, e]
    have htw : D.what₂.muTw (D.nd.w i) = tup (S0.μ (D.plEq (D.nd.w i))) :=
      ((D.what₂.muAt_or _).resolve_left hne).symm.trans (hTup.muAt _)
    obtain ⟨hj1, hj2⟩ := D.nd.j_range i
    let i' : Fin m := ⟨D.nd.j i - 1, by omega⟩
    have hj : D.nd.j i = (i' : ℕ) + 1 := by simp only [i']; omega
    rw [D.nd.mu_w i, htw, hj]
    exact GlobalTheory.EtaJoin.thetaCut_of_tie D G Pl0 T m A P ψ Zs tup eMt s hOk S0 jW i' _
      (hMt i' _ hy).1 (hθ i' _ hy)
  have hSpec : ∀ i, SpecPr D i :=
    GlobalTheory.T.good_part_projector_spectral_at_every_localisation D M hHT hHR hAV Tn hStd hCS hTC hEig hIsot h42 hZ hGood
  exact GlobalTheory.etaJ_join D G Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hStd hLat hSpec

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjLMemWeil
section
open NumberField IsDedekindDomain ValuativeRel
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.FunExt

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FunExt.ConjLift

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field Ω] [Algebra K Ω] [Algebra L Ω]

theorem mem_Dec_of_iff {F : Type} [Field F] [NumberField F] [Algebra F Ω] {A : ValuationSubring Ω} {σ : G F Ω}
    (hσ : ∀ x, σ x ∈ A ↔ x ∈ A) : σ ∈ Dec (F := F) A := by
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hσ]
  show (σ * σ⁻¹) x ∈ A ↔ x ∈ A
  rw [mul_inv_cancel]; rfl

variable (s : L ≃ₐ[K] L) (g : G K Ω) (hgs : ∀ x : L, g (algebraMap L Ω x) = algebraMap L Ω (s x))
include hgs

def conjL (τ : G L Ω) : G L Ω :=
  AlgEquiv.ofRingEquiv (f := g.toRingEquiv.trans (τ.toRingEquiv.trans g.symm.toRingEquiv)) fun x => by
    show g.symm (τ (g (algebraMap L Ω x))) = algebraMap L Ω x
    rw [hgs, AlgEquiv.commutes, AlgEquiv.symm_apply_eq, hgs]

omit [NumberField K] [NumberField L] in
@[simp] theorem conjL_apply (τ : G L Ω) (z : Ω) : conjL s g hgs τ z = g⁻¹ (τ (g z)) := rfl

variable {A : ValuationSubring Ω}

theorem conjL_mem_Weil (hgA : g ∈ Dec (F := K) A) {u : HeightOneSpectrum (𝓞 L)} (h' : IsPlaceOver A u)
    {τ : G L Ω} (hτ : τ ∈ Weil h') : conjL s g hgs τ ∈ Weil h' := by
  obtain ⟨a, b, hD, hab⟩ := hτ
  have hgi : g⁻¹ ∈ Dec (F := K) A := (Dec (F := K) A).inv_mem hgA
  refine ⟨a, b, mem_Dec_of_iff fun x => ?_, fun x hx => ?_⟩
  · rw [conjL_apply, apply_mem_iff_of_mem_Dec hgi, apply_mem_iff_of_mem_Dec hD, apply_mem_iff_of_mem_Dec hgA]
  · have hy : A.valuation (g x) ≤ 1 := val_apply_le_one hgA hx
    have h1 := hab (g x) hy
    rw [← valuation_apply_lt_one_iff hgi] at h1
    have e : (g⁻¹ : G K Ω) ((τ (g x)) ^ (normV u ^ b) - (g x) ^ (normV u ^ a)) =
        (conjL s g hgs τ x) ^ (normV u ^ b) - x ^ (normV u ^ a) := by
      rw [map_sub, map_pow, map_pow, conjL_apply]
      congr 2
      show (g⁻¹ * g) x = x
      rw [inv_mul_cancel]; rfl
    rwa [e] at h1

def conjW (hgA : g ∈ Dec (F := K) A) {u : HeightOneSpectrum (𝓞 L)} (h' : IsPlaceOver A u) (τ : Weil h') : Weil h' :=
  ⟨conjL s g hgs τ, conjL_mem_Weil s g hgs hgA h' τ.2⟩

@[simp] theorem coe_conjW (hgA : g ∈ Dec (F := K) A) {u : HeightOneSpectrum (𝓞 L)} (h' : IsPlaceOver A u) (τ : Weil h')
    (z : Ω) : (conjW s g hgs hgA h' τ : G L Ω) z = g⁻¹ ((τ : G L Ω) (g z)) := rfl

omit hgs

end GlobalTheory.FunExt.ConjLift
end
end

