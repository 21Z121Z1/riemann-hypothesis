import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0638
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0544
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0631
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Formalism.PieriBlockIdeals.LemmaWFromLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffsInIdealOfPowerSeriesIffImage
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem series_in_ideal_iff_image :
    ∀ (B Q σ : Type) [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B) (f : MvPowerSeries σ Q),
      (In N f ↔ ∃ s : MvPowerSeries σ B, (∀ α, coeff α s ∈ N) ∧ map (algebraMap B Q) s = f) ∧
      ∀ g : MvPowerSeries σ Q, In N f → In N g → ∀ a : B,
        In N (f + algebraMap B Q a • g) ∧ In N (f - g) := by
  intro B Q σ _ _ _ N f
  refine ⟨⟨fun h => ?_, fun ⟨s, hs, hsf⟩ α => ?_⟩, fun g hf hg a => ⟨fun α => ?_, fun α => ?_⟩⟩
  · choose b hbN hb using h
    obtain ⟨s, hs⟩ : ∃ s : MvPowerSeries σ B, ∀ α, coeff α s = b α := ⟨b, fun _ => rfl⟩
    refine ⟨s, fun α => (hs α).symm ▸ hbN α, ?_⟩
    ext α
    rw [coeff_map, hs]
    exact (hb α).symm
  · exact ⟨coeff α s, hs α, by rw [← hsf, coeff_map]⟩
  · obtain ⟨b₁, hb₁N, hb₁⟩ := hf α
    obtain ⟨b₂, hb₂N, hb₂⟩ := hg α
    refine ⟨b₁ + a * b₂, N.add_mem hb₁N (N.mul_mem_left a hb₂N), ?_⟩
    rw [map_add, map_smul, smul_eq_mul, hb₁, hb₂, map_add, map_mul]
  · obtain ⟨b₁, hb₁N, hb₁⟩ := hf α
    obtain ⟨b₂, hb₂N, hb₂⟩ := hg α
    exact ⟨b₁ - b₂, N.sub_mem hb₁N hb₂N, by rw [map_sub, hb₁, hb₂, map_sub]⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffsInIdealSolutionOfUnipotentSeriesMatrix
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.InvSolve

theorem in_iff_mem {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (f : MvPowerSeries σ Q) :
    In N f ↔ ∀ α, coeff α f ∈ N.toAddSubmonoid.map (algebraMap B Q).toAddMonoidHom := by
  simp only [In, AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe]
  constructor
  · intro h α; obtain ⟨b, hb, e⟩ := h α; exact ⟨b, hb, e.symm⟩
  · intro h α; obtain ⟨b, hb, e⟩ := h α; exact ⟨b, hb, e.symm⟩

theorem in_mul_map {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (f : MvPowerSeries σ Q) (h : MvPowerSeries σ B) (hf : In N f) :
    In N (f * map (algebraMap B Q) h) := by
  classical
  rw [in_iff_mem] at hf ⊢
  intro α
  rw [coeff_mul]
  refine AddSubmonoid.sum_mem _ fun x _ => ?_
  obtain ⟨b, hb, e⟩ := AddSubmonoid.mem_map.1 (hf x.1)
  refine AddSubmonoid.mem_map.2 ⟨b * coeff x.2 h, N.mul_mem_right _ hb, ?_⟩
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at e ⊢
  rw [map_mul, e, coeff_map]

theorem in_sum {B Q σ ι : Type} [CommRing B] [CommRing Q] [Algebra B Q] (N : Ideal B)
    (s : Finset ι) (f : ι → MvPowerSeries σ Q) (hf : ∀ i ∈ s, In N (f i)) :
    In N (∑ i ∈ s, f i) := by
  rw [in_iff_mem] at *
  intro α
  rw [map_sum]
  exact AddSubmonoid.sum_mem _ fun i hi => (in_iff_mem N (f i)).1 (hf i hi) α

theorem solve : ∀ {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ} (N : Ideal B) (M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B)), (∀ i j, constantCoeff (M i j) = if i = j then 1 else 0) → ∀ (v g : Fin d → MvPowerSeries (Fin d) Q), (∀ i, ∑ j, v j * map (algebraMap B Q) (M j i) = g i) → (∀ i, In N (g i)) → ∀ j, In N (v j) := by
  intro B Q _ _ _ d N M hM v g hv hg j
  classical
  have hc : (constantCoeff : MvPowerSeries (Fin d) B →+* B).mapMatrix M = 1 := by
    ext i k; simp [hM, Matrix.one_apply]
  have hdet : IsUnit M.det := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, hc, Matrix.det_one]
    exact isUnit_one
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdet
  let φ : MvPowerSeries (Fin d) B →+* MvPowerSeries (Fin d) Q := map (algebraMap B Q)
  have h2 : φ.mapMatrix M * φ.mapMatrix M⁻¹ = 1 := by rw [← map_mul, h1, map_one]
  have hvg : Matrix.vecMul v (φ.mapMatrix M) = g := funext fun i => by
    simpa [Matrix.vecMul, dotProduct, φ] using hv i
  have hv' : v = Matrix.vecMul g (φ.mapMatrix M⁻¹) := by
    rw [← hvg, Matrix.vecMul_vecMul, h2, Matrix.vecMul_one]
  rw [hv']
  simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, φ]
  exact in_sum N _ _ fun i _ => in_mul_map N _ _ (hg i)

end GlobalTheory.InvSolve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleGlobalOneFormsFiniteProjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem compatibleGlobalOneForms_finite_projective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → Module.Finite R (Glob1 F) ∧ Module.Projective R (Glob1 F) := by
  intro R _ C _ F hF h0
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨l, -, hl⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ
  let L : Glob1 F →ₗ[R] (Fin n → R) := LinearMap.pi l
  let S : (Fin n → R) →ₗ[R] Glob1 F := Fintype.linearCombination R Φ.w
  have hSL : S.comp L = LinearMap.id := by
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, S, L, Fintype.linearCombination_apply, LinearMap.pi_apply]
    exact (hl w).symm
  have hsurj : Function.Surjective S := fun w ↦ ⟨L w, by
    simpa using LinearMap.congr_fun hSL w⟩
  exact ⟨Module.Finite.of_surjective S hsurj, Module.Projective.of_split L S hSL⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHeckePartialLSeriesEntireBoundedStrips
section
noncomputable section
open NumberField MeasureTheory

namespace GlobalTheory.HeckeStrip

theorem completed_pSeries_entire_bounded : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (M : Ideal (𝓞 K)) (F : 𝓞 K → ℂ), M ≠ ⊥ → (∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) → (∀ (u : (𝓞 K)ˣ) (α : 𝓞 K), F ((u : 𝓞 K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : 𝓞 K) * α : 𝓞 K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips Λ ∧ ∀ s : ℂ, 1 < s.re → Λ s = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s := by
  intro K _ _ _ I _ φ hφ n hn M F hM hper hinv
  haveI : Nonempty I := ⟨hn.choose⟩
  obtain ⟨p, hpm, hp0, hpsum, R, hpR⟩ := GlobalTheory.T.exists_measurable_partitionOfUnity_unitLogTranslates K I φ hφ
  obtain ⟨⟨C, hC⟩, hsumm, hge⟩ := GlobalTheory.T.periodic_bounded_gaussian_summable_cmType K I φ hφ M F hM hper
  obtain ⟨a, κ, hasumm, ⟨δ, hδ, hδa⟩, hfe⟩ := GlobalTheory.T.heckeThetaKernel_poisson_summation K I φ hφ n M F hM hper
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hpsum y) 1 (fun u _ => hp0 _)
    have h0 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by
      funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h0] using h
  have hpB : ∀ y, |p y| ≤ 1 := fun y => abs_le.2 ⟨by linarith [hp0 y], hp1 y⟩
  set S : Set (I → ℝ) := {y | 0 ≤ ∑ i, y i} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hℓ : Measurable (fun y : I → ℝ => ∑ i, y i) := by fun_prop
  have hS0 : ∀ᵐ y ∂(volume.restrict S), 0 ≤ ∑ i, y i := ae_restrict_of_forall_mem hSm fun y hy => hy
  obtain ⟨D1m, D1i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n p 1 R hn hsumm
    ⟨1, one_pos, fun α _ h => hge α h⟩ hpm hpB hpR
  obtain ⟨D2m, D2i⟩ := GlobalTheory.T.integrable_weighted_heckeThetaKernel_halfSpace I (fun v : I → ℂ => v) a n (fun y => p (-y)) 1 R hn hasumm ⟨δ, hδ, hδa⟩
    (hpm.comp measurable_neg) (fun y => hpB _) (fun y hy i j => by
      have := hpR (-y) hy j i
      simp only [Pi.neg_apply] at this
      linarith)
  have A1 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D1m.restrict hS0 D1i
  have A2 := GlobalTheory.T.laplace_integral_entire_boundedInVerticalStrips (volume.restrict S) (fun y : I → ℝ => ∑ i, y i) _ hℓ D2m.restrict hS0 D2i
  have hint : ∀ (g : (I → ℝ) → ℂ) (t : ℂ), AEStronglyMeasurable g volume →
      (∀ σ : ℝ, Integrable (fun y => ‖g y‖ * Real.exp (σ * ∑ i, y i)) (volume.restrict S)) →
      Integrable (fun y => g y * Complex.exp (t * ((∑ i, y i : ℝ) : ℂ))) (volume.restrict S) := by
    intro g t hg hgi
    refine (hgi t.re).mono' (hg.restrict.mul (Continuous.aestronglyMeasurable (by fun_prop))) (ae_of_all _ fun y => ?_)
    rw [norm_mul, Complex.norm_exp]
    apply le_of_eq
    congr 2
    simp [Complex.mul_re]
  set f1 : ℂ → ℂ := fun s => ∫ y in S, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : 𝓞 K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf1
  set f2 : ℂ → ℂ := fun s => ∫ y in S, (p (-y) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) with hf2
  have hd1 : Differentiable ℂ f1 := A1.1
  have hd2 : Differentiable ℂ f2 := A2.1
  have hb1 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f1 := A1.2
  have hb2 : GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.BoundedInStrips f2 := A2.2
  refine ⟨fun s => 2 ^ Fintype.card I * (f1 s + κ * f2 (1 - s)), ?_, ?_, ?_⟩
  · exact (hd1.add ((hd2.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).const_mul κ)).const_mul _
  · intro a' b' hab
    obtain ⟨C1, hC1⟩ := hb1 a' b' hab
    obtain ⟨C2, hC2⟩ := hb2 (1 - b') (1 - a') (by linarith)
    refine ⟨‖(2 : ℂ) ^ Fintype.card I‖ * (C1 + ‖κ‖ * C2), fun s h1 h2 => ?_⟩
    rw [norm_mul]
    gcongr
    refine (norm_add_le _ _).trans (add_le_add (hC1 s h1 h2) ?_)
    rw [norm_mul]
    gcongr
    exact hC2 (1 - s) (by simp; linarith) (by simp; linarith)
  · intro s hs
    rw [GlobalTheory.T.archFactor_mul_pSeries_eq_integral_alt K I φ hφ n hn F C hC hinv p hpm hp0 hpsum s hs,
      GlobalTheory.T.mellin_integral_split_functional_equation I p _ _ κ s hfe (hint _ s D1m D1i) (hint _ (1 - s) D2m D2i)]

end GlobalTheory.HeckeStrip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffExpSub
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

namespace GlobalTheory.WachExp

open PowerSeries

theorem ringHom_gam_X {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L]
    [Algebra ℤ_[l] O] [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] (φ : O⟦X⟧ →+* L⟦X⟧)
    (hφ : ∀ a : O, φ (C a) = C (algebraMap O L a)) (z : L) (hX : φ X = C z * exp L - 1) (hz : z ^ l = 1)
    (c : ℤ_[l]) (hc : (l : ℤ_[l]) ∣ c - 1) :
    φ (GlobalTheory.Fon.gam O c X) = C z * rescale (algebraMap ℤ_[l] L c) (exp L) - 1 := by
  let f : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
    { toRingHom := φ
      commutes' := fun a => (congrArg φ (PowerSeries.algebraMap_apply (R := O) (A := O))).trans
        ((hφ a).trans (PowerSeries.algebraMap_apply (R := O) (A := L)).symm) }
  have h := GlobalTheory.HWL.Ser.map_gam_X f z hX 1 1 (by rw [pow_one]; exact hz) c (by simpa using hc)
  rw [pow_one] at h
  exact h

end GlobalTheory.WachExp

namespace GlobalTheory.WachExp

open PowerSeries

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

theorem norm_root_sub_one_lt {z : ↥LL.1} (hz : z ^ l = 1) : ‖(((z - 1 : ↥LL.1)) : Om l)‖ < 1 := by
  have h : ((z : Om l)) ^ l ^ 1 = 1 := by
    rw [pow_one]; exact_mod_cast congrArg (fun y : ↥LL.1 => (y : Om l)) hz
  have := GlobalTheory.HWL.Ser.norm_sub_one_lt h
  push_cast
  exact this

theorem constantCoeff_exp_sub (z a : ↥LL.1) :
    constantCoeff (C z * rescale a (exp ↥LL.1) - 1) = z - 1 := by
  rw [map_sub, map_mul, GlobalTheory.HWL.Ser.constantCoeff_rescale_exp, constantCoeff_C, mul_one, map_one]

theorem ev_unique (x : PowerSeries ↥LL.1) (hx : ‖((constantCoeff x : ↥LL.1) : Om l)‖ < 1)
    (φ ψ : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1)
    (hφ : ∀ a : ↥(OL LL), φ (C a) = C (a : ↥LL.1)) (hψ : ∀ a : ↥(OL LL), ψ (C a) = C (a : ↥LL.1))
    (hφX : φ X = x) (hψX : ψ X = x) : φ = ψ := by
  let φ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1 :=
    { toRingHom := φ, commutes' := fun a => by change φ (C a) = C (a : ↥LL.1); exact hφ a }
  let ψ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1 :=
    { toRingHom := ψ, commutes' := fun a => by change ψ (C a) = C (a : ↥LL.1); exact hψ a }
  have h := (GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL x hx).1.unique (y₁ := φ') (y₂ := ψ') hφX hψX
  exact RingHom.ext fun f => AlgHom.congr_fun h f

theorem exists_ev (z : ↥LL.1) (hz : z ^ l = 1) :
    ∃ φ : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1,
      (∀ a : ↥(OL LL), φ (C a) = C (a : ↥LL.1)) ∧ φ X = C z * exp ↥LL.1 - 1 := by
  have h := GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL (C z * rescale 1 (exp ↥LL.1) - 1)
    (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL hz)
  obtain ⟨ev, hev, -⟩ := h.1
  refine ⟨ev.toRingHom, fun a => ?_, by
    change ev X = _
    rw [hev, rescale_one, RingHom.id_apply]⟩
  have := ev.commutes a
  exact this

theorem rescale_C' (r z : ↥LL.1) : rescale r (C z) = C z := by
  ext n
  by_cases h : n = 0 <;> simp [coeff_rescale, coeff_C, h]

end GlobalTheory.WachExp

namespace GlobalTheory.WachExp

open PowerSeries

theorem exists_locExp : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), l ≠ 2 → (∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l) →
    ∃ (u : ℤ_[l]ˣ) (c : ℤ_[l]) (ζ : ↥(OL LL)) (jj : ℕ → PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1),
      (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c ∧ IsUnit c ∧ IsPrimitiveRoot ζ l ∧ ζ - 1 ∈ maximalIdeal ↥(OL LL) ∧
      ∀ b ∈ Finset.Ioo 0 l, Formalism.CohomologicalDescent.FrobeniusPeriodChange.IsLocExp l ↥(OL LL) ↥LL.1 (OL LL).val.toRingHom (ζ ^ b - 1)
        (u : ℤ_[l]) (jj b) := by
  intro l _ LL _ hex
  obtain ⟨ζL, hζL⟩ := hex
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hfin := LL.2
  have hint : IsIntegral ℤ_[l] ζL := IsIntegral.of_pow hl (by rw [hζL.pow_eq_one]; exact isIntegral_one)
  let ζ : ↥(OL LL) := ⟨ζL, hint⟩
  have hζ : IsPrimitiveRoot ζ l :=
    IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζL Subtype.val_injective

  have hu : IsUnit (1 + (l : ℤ_[l]) * 1) := by
    have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))
    rcases h with h | h
    · exact absurd ((IsUnit.neg_iff _).1 h) PadicInt.prime_p.not_isUnit
    · simpa [sub_eq_add_neg] using h
  let u : ℤ_[l]ˣ := hu.unit
  have hu1 : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * 1 := hu.unit_spec

  have hmax : ζ - 1 ∈ maximalIdeal ↥(OL LL) := by
    refine (GlobalTheory.DiscEval.mem_maximalIdeal_iff_norm (p := l) LL.1 _).2 ?_
    refine lt_of_eq_of_lt (b := ‖((((ζL - 1 : ↥LL.1)) : PadicAlgCl l) : ℂ_[l])‖) rfl ?_
    rw [PadicComplex.norm_extends]
    exact norm_root_sub_one_lt LL hζL.pow_eq_one
  have hpow : ∀ b : ℕ, (ζL ^ b) ^ l = 1 := fun b => by
    rw [← pow_mul, mul_comm, pow_mul, hζL.pow_eq_one, one_pow]
  choose ev hC hev using fun b : ℕ => exists_ev LL (ζL ^ b) (hpow b)
  refine ⟨u, 1, ζ, ev, hu1, isUnit_one, hζ, hmax, fun b _ => ⟨fun a => hC b a, ?_, fun f => ?_⟩⟩
  · obtain ⟨g, hg⟩ : X ∣ exp ↥LL.1 - 1 := X_dvd_iff.2 (by simp)
    have hg0 : constantCoeff g = 1 := by
      have h := congrArg (coeff 1) hg
      rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply] at h
      rw [← h]; simp [coeff_exp]
    have hzb : ζL ^ b ≠ 0 := pow_ne_zero _ (hζL.ne_zero (by omega))
    have hunit : IsUnit (C (ζL ^ b) * g) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hg0, hzb]
    have hcalc : ev b (X - C (ζ ^ b - 1)) = X * (C (ζL ^ b) * g) := by
      rw [map_sub, hev, hC]
      have hco : ((ζ ^ b - 1 : ↥(OL LL)) : ↥LL.1) = ζL ^ b - 1 := rfl
      rw [hco, map_sub (C : ↥LL.1 →+* _), map_one]
      linear_combination (C (ζL ^ b)) * hg
    rw [hcalc]
    exact associated_mul_unit_left X _ hunit
  · set r : ↥LL.1 := algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l]) with hr_def
    have hact : Formalism.CohomologicalDescent.HeightDescentMinors.act l ↥(OL LL) (u : ℤ_[l]) f = GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) f := by
      simp only [Formalism.CohomologicalDescent.HeightDescentMinors.act, Formalism.CohomologicalDescent.HeightDescentMinors.br, GlobalTheory.Fon.gam]
      exact (congrFun (coe_substAlgHom _) f).symm
    have hxz := ringHom_gam_X (O := ↥(OL LL)) (L := ↥LL.1) (ev b) (hC b) (ζL ^ b) (hev b) (hpow b)
      (u : ℤ_[l]) ⟨1, by rw [hu1]; ring⟩
    have huniq := ev_unique LL (C (ζL ^ b) * rescale r (exp ↥LL.1) - 1)
      (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL (hpow b))
      ((ev b).comp (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) : PowerSeries ↥(OL LL) →+* PowerSeries ↥(OL LL)))
      ((rescale r).comp (ev b))
      (fun a => by
        change ev b (GlobalTheory.Fon.gam ↥(OL LL) (u : ℤ_[l]) (C a)) = _
        rw [GlobalTheory.Fon.gam_C, hC])
      (fun a => by
        change rescale r (ev b (C a)) = _
        rw [hC, rescale_C'])
      hxz
      (by
        change rescale r (ev b X) = _
        rw [hev, map_sub, map_mul, map_one, rescale_C'])
    rw [hact]
    exact RingHom.congr_fun huniq f

end GlobalTheory.WachExp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffNmul
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDefect

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem in_zero {σ : Type} (N : Ideal B) : In N (0 : MvPowerSeries σ Q) :=
  fun α => ⟨0, N.zero_mem, by simp⟩

theorem in_sub {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f - g) := fun α => by
  obtain ⟨a, ha, hfa⟩ := hf α
  obtain ⟨b, hb, hgb⟩ := hg α
  exact ⟨a - b, N.sub_mem ha hb, by rw [map_sub, hfa, hgb, map_sub]⟩

theorem in_subst {σ τ : Type} [Finite σ] {N : Ideal B} {g : MvPowerSeries σ Q}
    (u : σ → MvPowerSeries τ B) (hu : ∀ i, constantCoeff (u i) = 0) (hg : In N g) :
    In N (subst (up Q u) g) := by
  choose c hcN hc using hg
  set G : MvPowerSeries σ B := fun α => c α with hG
  have hgG : g = map (algebraMap B Q) G := by
    ext α; rw [coeff_map, hc α]; rfl
  have hsu : HasSubst u := hasSubst_of_constantCoeff_zero hu
  have key : subst (up Q u) g = map (algebraMap B Q) (subst u G) := by
    rw [map_subst hsu, hgG]; rfl
  intro e
  refine ⟨coeff e (subst u G), ?_, by rw [key, coeff_map]⟩
  rw [coeff_subst hsu]
  refine finsum_induction (fun x => x ∈ N) N.zero_mem (fun x y hx hy => N.add_mem hx hy) ?_
  intro d
  rw [smul_eq_mul]
  exact N.mul_mem_right _ (hcN d)

variable {d : ℕ}

theorem nmul_succ {R : Type} [CommRing R] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) fun i => X i := by
  unfold nmul; rw [Function.iterate_succ_apply']

theorem constantCoeff_nmul {R : Type} [CommRing R] {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    rw [nmul_succ]
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)

theorem up_nmul_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up Q (nmul μ (n + 1)) = op (up Q μ) (up Q (nmul μ n)) fun i => X i := by
  funext i
  have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
    rintro (j | j)
    · exact constantCoeff_nmul hμ n j
    · simp
  rw [nmul_succ]
  simp only [up, op, at2]
  rw [map_subst (hasSubst_of_constantCoeff_zero h0)]
  congr 1
  funext j
  rcases j with j | j
  · rfl
  · simp

theorem defect_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (f : MvPowerSeries (Fin d) Q) :
    defect μ (n + 1) f = defect μ n f -
      subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (cob1 (up Q μ) f) := by
  have hU : ∀ j, constantCoeff (up Q (nmul μ n) j) = 0 := by
    intro j
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_nmul hμ n j, map_zero]
  have hE : ∀ j, constantCoeff (Sum.elim (up Q (nmul μ n)) (fun i => (X i : MvPowerSeries (Fin d) Q)) j) = 0 := by
    rintro (j | j)
    · exact hU j
    · simp
  have hM : ∀ j, constantCoeff (up Q μ j) = 0 := by
    intro j
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ j, map_zero]
  have hsE := hasSubst_of_constantCoeff_zero hE
  have hsM := hasSubst_of_constantCoeff_zero hM
  have hsL : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hsR : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have e1 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (subst (up Q μ) f)
      = subst (up Q (nmul μ (n + 1))) f := by
    rw [subst_comp_subst_apply hsM hsE, up_nmul_succ μ hμ n]; rfl
  have e2 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (inL f)
      = subst (up Q (nmul μ n)) f := by
    unfold inL
    rw [subst_comp_subst_apply hsL hsE]
    congr 1; funext j; rw [subst_X hsE]; rfl
  have e3 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (inR f) = f := by
    unfold inR
    rw [subst_comp_subst_apply hsR hsE]
    have : (fun j => subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q))
        (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) Q)) = fun j => X j := by
      funext j; rw [subst_X hsE]; rfl
    rw [this, subst_self]; rfl
  have hc : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (cob1 (up Q μ) f)
      = subst (up Q (nmul μ (n + 1))) f - subst (up Q (nmul μ n)) f - f := by
    unfold cob1
    rw [← coe_substAlgHom hsE, map_sub, map_sub, coe_substAlgHom, e1, e2, e3]
  rw [hc]
  unfold defect
  push_cast
  rw [add_smul, one_smul]
  abel

theorem main : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), QL μ N f → ∀ n, In N (defect μ n f) ∧ ∀ i, constantCoeff (nmul μ n i) = 0 := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ N f hf n
  refine ⟨?_, constantCoeff_nmul hμ.const n⟩
  induction n with
  | zero =>
    have h0 : up Q (nmul μ 0) = 0 := by funext i; simp [up, nmul]
    simp only [defect, h0, Nat.cast_zero, zero_smul, zero_sub]
    rw [subst_zero_of_constantCoeff_zero hf.1, neg_zero]
    exact in_zero N
  | succ n ih =>
    rw [defect_succ μ hμ.const n f]
    refine in_sub ih ?_
    have hv : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul hμ.const n j
      · simp
    have : (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) =
        up Q (Sum.elim (nmul μ n) fun i => (X i : MvPowerSeries (Fin d) B)) := by
      funext j; rcases j with j | j
      · rfl
      · simp [up]
    rw [this]
    exact in_subst _ hv hf.2.2

end GlobalTheory.QLogDefect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductGradedCommRingAxiomsHoldStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold : GlobalTheory.EtC.DivisorRingCompatibility := by
  first | (exact @GlobalTheory.EtC.a6ring_holds) | (exact GlobalTheory.EtC.a6ring_holds) | (intros; apply GlobalTheory.EtC.a6ring_holds  <;> assumption)
end

