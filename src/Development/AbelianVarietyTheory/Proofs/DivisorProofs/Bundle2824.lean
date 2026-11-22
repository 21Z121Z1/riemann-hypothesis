import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2209
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicValueTranslateAny
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0175
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSigFramesOfIsotropic
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2598
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormChartChangeCoeffIdealPow
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg

theorem eval₂_eq_of_sub_mem_of_coeff_mem_pow {R B σ : Type} [CommRing R] [CommRing B] (φ : R →+* B)
    (I : Ideal R) (e : ℕ) (hbot : (I ^ (e + 1)).map φ = ⊥) (F : MvPolynomial σ R)
    (hF : ∀ m, MvPolynomial.coeff m F ∈ I ^ e) (a b : σ → B) (hab : ∀ l, a l - b l ∈ I.map φ) :
    MvPolynomial.eval₂ φ a F = MvPolynomial.eval₂ φ b F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 : (∏ l ∈ m.support, a l ^ m l) - ∏ l ∈ m.support, b l ^ m l ∈ I.map φ := by
    rw [← Ideal.Quotient.eq]
    simp only [map_prod, map_pow]
    exact Finset.prod_congr rfl fun l _ => by rw [Ideal.Quotient.eq.2 (hab l)]
  have h2 : φ (MvPolynomial.coeff m F) * ((∏ l ∈ m.support, a l ^ m l) - ∏ l ∈ m.support, b l ^ m l) ∈
      (I ^ (e + 1)).map φ := by
    rw [pow_succ, Ideal.map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hF m)) h1
  rw [hbot, Ideal.mem_bot, mul_sub, sub_eq_zero] at h2
  exact h2

theorem eval₂_mem_map_of_coeff_mem {R B σ : Type} [CommRing R] [CommRing B] (φ : R →+* B)
    (J : Ideal R) (F : MvPolynomial σ R) (hF : ∀ m, MvPolynomial.coeff m F ∈ J) (a : σ → B) :
    MvPolynomial.eval₂ φ a F ∈ J.map φ := by
  rw [MvPolynomial.eval₂_eq]
  exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hF m))

theorem Charts.ev_change (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hpb : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (n : ℕ) (C : Charts I Y β n)
    (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d)
    (hc : ∀ m, MvPolynomial.coeff m F ∈ I ^ e) (i j : Fin (n + 1)) :
    C.ev e i F ∈ towerIdeal Y e (I ^ e) (C.D e i) ∧ C.ρ e i i * C.ev e i F = C.ev e i F ∧
      rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) =
        rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ d *
          rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ev e j F) := by
  obtain ⟨hbot, -⟩ := GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective R I Y β hpb n C
  obtain ⟨-, hself, hcoc⟩ := GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hpb n C
  have h1 : C.ev e i F ∈ towerIdeal Y e (I ^ e) (C.D e i) :=
    eval₂_mem_map_of_coeff_mem _ _ F hc _
  refine ⟨h1, ?_, ?_⟩
  · have h := Ideal.mul_mem_mul (hself e i) h1
    have h' : (C.ρ e i i - 1) * C.ev e i F ∈ towerIdeal Y e (I ^ (e + 1)) (C.D e i) := by
      have hm : towerIdeal Y e (I ^ (e + 1)) (C.D e i) =
          towerIdeal Y e I (C.D e i) * towerIdeal Y e (I ^ e) (C.D e i) := by
        unfold towerIdeal
        rw [← Ideal.map_mul, ← pow_succ']
      rw [hm]
      exact h
    rw [hbot, Ideal.mem_bot, sub_mul, one_mul, sub_eq_zero] at h'
    exact h'
  · have hi : (rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i)).comp
        (GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e i)) =
        GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e i ⊓ C.D e j) :=
      RingHom.ext fun r => rs_cst _ _ r
    have hj : (rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j)).comp
        (GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e j)) =
        GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e i ⊓ C.D e j) :=
      RingHom.ext fun r => rs_cst _ _ r
    simp only [Charts.ev, MvPolynomial.coe_eval₂Hom]
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, hi, hj, ← eval₂_scale _ _ _ hF]
    exact eval₂_eq_of_sub_mem_of_coeff_mem_pow _ I e (hbot e _) F hc _ _ fun l => hcoc e i j l

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousLineBaseDifference
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.CovTest.SwapLine

private theorem isHomogeneous_cast {φ : MvPolynomial (Fin 5) ℝ} {m k : ℕ} (h : φ.IsHomogeneous m) (e : m = k) :
    φ.IsHomogeneous k := e ▸ h

theorem powSum_sub_factor (t p q : MvPolynomial (Fin 5) ℝ)
    (ht : t.IsHomogeneous 1) (hp : p.IsHomogeneous 1) (hq : q.IsHomogeneous 1) (n : ℕ) :
    (∃ R : MvPolynomial (Fin 5) ℝ, R.IsHomogeneous n ∧
        t ^ (n + 2) + (p + q - t) ^ (n + 2) - p ^ (n + 2) - q ^ (n + 2) = (t - p) * (t - q) * R) ∧
      (∃ R : MvPolynomial (Fin 5) ℝ, R.IsHomogeneous (n + 1) ∧
        t ^ (n + 3) + (p + q - t) ^ (n + 3) - p ^ (n + 3) - q ^ (n + 3) = (t - p) * (t - q) * R) := by
  have hσ : (p + q).IsHomogeneous 1 := hp.add hq
  have hs : (p + q - t).IsHomogeneous 1 := hσ.sub ht
  induction n with
  | zero =>
    refine ⟨⟨1 + 1, (isHomogeneous_one (Fin 5) ℝ).add (isHomogeneous_one (Fin 5) ℝ), by ring⟩,
      ⟨(p + q) + (p + q) + (p + q), (hσ.add hσ).add hσ, by ring⟩⟩
  | succ n ih =>
    obtain ⟨⟨R₁, h₁, e₁⟩, ⟨R₂, h₂, e₂⟩⟩ := ih
    refine ⟨⟨R₂, h₂, e₂⟩, ⟨(p + q) * R₂ - t * (p + q - t) * R₁ + (p ^ (n + 2) + q ^ (n + 2)), ?_, ?_⟩⟩
    · have a₁ : ((p + q) * R₂).IsHomogeneous (n + 1 + 1) := isHomogeneous_cast (hσ.mul h₂) (by omega)
      have a₂ : (t * (p + q - t) * R₁).IsHomogeneous (n + 1 + 1) :=
        isHomogeneous_cast ((ht.mul hs).mul h₁) (by omega)
      have a₃ : (p ^ (n + 2) + q ^ (n + 2)).IsHomogeneous (n + 1 + 1) :=
        isHomogeneous_cast ((hp.pow (n + 2)).add (hq.pow (n + 2))) (by omega)
      exact (a₁.sub a₂).add a₃
    · linear_combination (p + q) * e₂ - t * (p + q - t) * e₁

theorem onLine_sub_onBase_factor (d : ℕ) (a b : ℤ) : ∃ K : MvPolynomial (Fin 5) ℝ, K.IsHomogeneous d ∧
    onLine d a b - onBase d a b = (X 0 - X 4) * (X 0 - X 3) * K := by
  have hX : ∀ i : Fin 5, (X i : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 := fun i => isHomogeneous_X ℝ i
  have hCX : ∀ (r : ℝ) (i : Fin 5), (C r * X i : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    fun r i => isHomogeneous_C_mul_X r i
  have ht : (C (a : ℝ) * X 0 + C (b : ℝ) * (X 3 + X 4 - X 0) + X 2 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    ((hCX _ 0).add (isHomogeneous_cast ((isHomogeneous_C (Fin 5) (b : ℝ)).mul (((hX 3).add (hX 4)).sub (hX 0)))
      (by omega))).add (hX 2)
  have hp : (C (a : ℝ) * X 4 + C (b : ℝ) * X 3 + X 2 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    ((hCX _ 4).add (hCX _ 3)).add (hX 2)
  have hq : (C (b : ℝ) * X 4 + C (a : ℝ) * X 3 + X 2 : MvPolynomial (Fin 5) ℝ).IsHomogeneous 1 :=
    ((hCX _ 4).add (hCX _ 3)).add (hX 2)
  obtain ⟨R, hR, e⟩ := (powSum_sub_factor _ _ _ ht hp hq d).1
  refine ⟨(C (a : ℝ) - C (b : ℝ)) ^ 2 * R, isHomogeneous_cast
    ((((isHomogeneous_C (Fin 5) (a : ℝ)).sub (isHomogeneous_C (Fin 5) (b : ℝ))).pow 2).mul hR) (by omega), ?_⟩
  have hL : onLine d a b = (C (a : ℝ) * X 0 + C (b : ℝ) * (X 3 + X 4 - X 0) + X 2) ^ (d + 2) +
      (C (b : ℝ) * X 0 + C (a : ℝ) * (X 3 + X 4 - X 0) + X 2) ^ (d + 2) := by
    simp only [onLine, swapSum, lin, map_add, map_pow, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, map_one, one_mul]
  have hB : onBase d a b = (C (a : ℝ) * X 4 + C (b : ℝ) * X 3 + X 2) ^ (d + 2) +
      (C (b : ℝ) * X 4 + C (a : ℝ) * X 3 + X 2) ^ (d + 2) := by
    simp only [onBase, swapSum, lin, map_add, map_pow, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, map_one, one_mul]
  have hs : (C (b : ℝ) * X 0 + C (a : ℝ) * (X 3 + X 4 - X 0) + X 2 : MvPolynomial (Fin 5) ℝ) =
      (C (a : ℝ) * X 4 + C (b : ℝ) * X 3 + X 2) + (C (b : ℝ) * X 4 + C (a : ℝ) * X 3 + X 2) -
        (C (a : ℝ) * X 0 + C (b : ℝ) * (X 3 + X 4 - X 0) + X 2) := by ring
  rw [hL, hB, hs]
  linear_combination e

end GlobalTheory.CovTest.SwapLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostFieldDegreeDivisibilityStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.host_field_degree_divisibility : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => letI := p.T.Q.H.starRing; ∃ α : 𝓞 (Fm.D x ι).host.E, α * star α = ((((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℕ) : 𝓞 (Fm.D x ι).host.E) ∧ ((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1) ∣ Y.d.l₂.M ∧ Y.d.l₂.Mb ≤ Ideal.span {star α} ∧ Module.finrank ℚ (Fm.D x ι).host.E * (dat p i).q ≤ 2 * (Fm.D x ι).R.f * (Fm.D x ι).R.m := by
  first | exact @GlobalTheory.HalfCover.half_gen_on_cover | exact GlobalTheory.HalfCover.half_gen_on_cover | (intros; apply GlobalTheory.HalfCover.half_gen_on_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealFromPlaceShift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.PointMap GlobalTheory.FlatCM GlobalTheory.IndexIdeal GlobalTheory.HTIndex GlobalTheory.PointSig
open GlobalTheory.LieIndex GlobalTheory.HTLat.OmegaRank

namespace GlobalTheory.CMIdeal

theorem ideal_eq_of_map_eq {K : Type} [Field K] [NumberField K] {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (i : K →+* ℂ_[ℓ]), ∃ d : 𝓞_ℂ_[ℓ],
      I.map (embO (PadicComplexInt.integers ℓ) i) = Ideal.span {d} ∧
      J.map (embO (PadicComplexInt.integers ℓ) i) = Ideal.span {d}) : I = J := by
  have key : ∀ P : Ideal (𝓞 K), Prime P → emultiplicity P I = emultiplicity P J := fun P hP => by
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
    obtain ⟨ℓ, hℓ, hm⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ P := by
      have h0 : Ideal.absNorm P ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hP.ne_zero
      have h1 := Ideal.absNorm_mem P
      rw [← Nat.prod_primeFactorsList h0, Nat.cast_list_prod, ← Ideal.Quotient.eq_zero_iff_mem, map_list_prod] at h1
      haveI := 𝔭.isPrime
      haveI : IsDomain (𝓞 K ⧸ P) := Ideal.Quotient.isDomain 𝔭.asIdeal
      obtain ⟨_, h2, h3⟩ := List.mem_map.1 (List.prod_eq_zero_iff.1 h1)
      obtain ⟨ℓ, h4, rfl⟩ := List.mem_map.1 h2
      exact ⟨ℓ, Nat.prime_of_mem_primeFactorsList h4, Ideal.Quotient.eq_zero_iff_mem.1 h3⟩
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨i, he, hi⟩ := GlobalTheory.PrimeEmbedding.exists_embedding_norm_eq K 𝔭 ℓ hm
    obtain ⟨d, h1, h2⟩ := h ℓ i
    have e := (norm_of_map_eq_span he hi (algebraMap_embO _ i) hI h1).symm.trans
      (norm_of_map_eq_span he hi (algebraMap_embO _ i) hJ h2)
    have hℓ' : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
    have he' : (Formalism.BasicNotions.vAdd 𝔭 (ℓ : K) : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have e' := (Real.strictMono_rpow_of_base_gt_one hℓ').injective e
    rw [neg_inj, div_left_inj' he', Nat.cast_inj] at e'
    rw [(FiniteMultiplicity.of_prime_left hP hI).emultiplicity_eq_multiplicity,
      (FiniteMultiplicity.of_prime_left hP hJ).emultiplicity_eq_multiplicity]
    exact congrArg _ e'
  exact le_antisymm
    (Ideal.le_of_dvd ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hJ).2 fun P hP => (key P hP).ge))
    (Ideal.le_of_dvd ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hI).2 fun P hP => (key P hP).le))

theorem cancel_shift {p q : ℕ} {κ₁ κ₂ : ℝ} {g g' c c' a b : ℝ≥0} (hg : g ≠ 0) (hg' : g' ≠ 0) (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h₀ : Real.log g - Real.log g' = p * κ₁ + q * κ₂) (h₁ : Real.log c = κ₁) (h₂ : -Real.log c' = κ₂)
    (h : c ^ p * g' * a = c' ^ q * g * b) : a = b := by
  have e : c ^ p * g' = c' ^ q * g := by
    refine NNReal.coe_injective (Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_)
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow]
    subst h₁ h₂
    linarith
  rw [e] at h
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hc') hg) h

theorem exists_matrix_of_mem {O C U : Type} [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U]
    [Module O U] [IsScalarTower O C U] {n : ℕ} {x u : Fin n → U} (h : ∀ a, u a ∈ Submodule.span O (Set.range x)) :
    ∃ m : Matrix (Fin n) (Fin n) C, ∀ a, u a = ∑ k, m a k • x k := by
  choose m hm using fun a => (Submodule.mem_span_range_iff_exists_fun C).1 (Submodule.span_le_restrictScalars O C _ (h a))
  exact ⟨m, fun a => (hm a).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} {X : CMObj H K ρ σ₁ p q} {FP : GenFib (X.A true).pol}
  {FQ : GenFib (X.A false).pol} {FB : GenFib X.B.pol}
  {MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))} {MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))}
  {τ : 𝓞 E →+* 𝓞 K}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

open Classical in

theorem map_eq_at (hD : IsDiffs FP FQ FB MP MQ) (hτ : τ H.rt = ρ) {φ : E →+* C} (hφ : embO hv φ = (embO hv i).comp τ)
    {n δ : O} (hR : IsIndexRel hv ε i X φ (Ideal.span {n}) δ) {κ₁ κ₂ : ℝ} : letI := H.starRing
    HasSigFrames (pointB hv ε i X) H.rt φ p q → HasSigFrames (pointA hv ε i X true) H.rt φ 1 0 →
    HasSigFrames (pointA hv ε i X false) H.rt φ 0 1 →
    (∀ (P : Point ℓ v O (𝓞 E)) (p q : ℕ),
      (∀ ψ : E →+* C, Module.finrank C (P.eigW (embO P.integers ψ)) = if ψ (H.rt : E) = φ (H.rt : E) then p else q) →
      ∀ (x : Fin p → LieG P.Gt) (x' : Fin q → LieG P.Gt) (g : Matrix (Fin p) (Fin p) C) (g' : Matrix (Fin q) (Fin q) C),
        Submodule.span O (Set.range fun i => P.bLie (x i)) = P.wRec (embO P.integers φ) →
        Submodule.span O (Set.range fun i => P.bLie (x' i)) = P.wRec ((embO P.integers φ).comp (starRingEnd (𝓞 E))) →
        IsLatBasis C (P.latTQuot (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) φ)
          (fun i => ∑ j, g i j • P.bLie (x j)) →
        IsLatBasis C (P.latTSub ((embO P.integers φ).comp (starRingEnd (𝓞 E)))) (fun i => ∑ j, g' i j • P.bLie (x' j)) →
        Real.log (v g.det) - Real.log (v g'.det) = p * κ₁ + q * κ₂) →
    ∃ d : O, (idx K p (FB.eigLat X.B.t.act τ) (subP FP FB MP τ)).map (embO hv i) * Ideal.span {δ} = Ideal.span {d} ∧
      Ideal.span {n} * (idx K q (FB.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))
        (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))).map (embO hv i) = Ideal.span {d} := by
  letI := H.starRing
  rintro ⟨b0, x, x', g, g', b1, b2, b3, b4, b5, b6, -, -, b7, b8, b9, b10⟩
    ⟨p0, y, y₀, c, c₀, p1, p2, p3, p4, p5, -, -, -, -, -, p9, -⟩
    ⟨q0, z₀, z, e₀, e, q1, q2, q3, q4, -, q6, -, -, -, -, -, q10⟩ hS
  have sB := hS _ p q b0 x x' g g' b1 b2 b3 b4
  have sP := hS _ 1 0 p0 y y₀ c c₀ p1 p2 p3 p4
  have sQ := hS _ 0 1 q0 z₀ z e₀ e q1 q2 q3 q4
  simp only [Matrix.det_isEmpty, map_one, NNReal.coe_one, Real.log_one, sub_zero, zero_sub, Nat.cast_one, Nat.cast_zero,
    one_mul, zero_mul, add_zero, zero_add] at sP sQ
  obtain ⟨m, hm⟩ := exists_matrix_of_mem (C := C) fun a => b1.ge (patV_mem_wRec (T := X.A true) hv ε i (X.lin (.inl a)) _ _
    (p1.le (Submodule.subset_span ⟨0, rfl⟩)))
  obtain ⟨m', hm'⟩ := exists_matrix_of_mem (C := C) fun a => b2.ge (patV_mem_wRec (T := X.A false) hv ε i
    (X.lin (.inr a)) _ _ (q2.le (Submodule.subset_span ⟨0, rfl⟩)))
  have e₁ := hR.val_det x x' y z g m g' m' c e b5 b6 p5 q6 b9 b10 p9 q10 b3 b4 p3 q4 hm hm'
  obtain ⟨-, hP, hQ⟩ := lie_index hv ε i hD hτ
  rw [Set.range_unique] at p1 q2
  obtain ⟨d₁, hd₁, f₁⟩ := hP _ hφ x (fun _ => y 0) m b7 b1 (fun _ => p1) hm
  obtain ⟨d₂, hd₂, f₂⟩ := hQ ((embO hv φ).comp (starRingEnd (𝓞 E))) (by rw [hφ]; rfl) x' (fun _ => z 0) m' b8 b2
    (fun _ => q2) hm'
  have e₂ : v (algebraMap O C (d₁ * δ)) = v (algebraMap O C (n * d₂)) := by
    refine cancel_shift ((map_ne_zero v).2 b5) ((map_ne_zero v).2 b6) ((map_ne_zero v).2 p5) ((map_ne_zero v).2 q6)
      sB sP sQ ?_
    rw [map_mul, map_mul, map_mul, map_mul, hd₁, hd₂]
    calc _ = _ := by ring
      _ = _ := e₁
      _ = _ := by ring
  refine ⟨d₁ * δ, by rw [f₁, Ideal.span_singleton_mul_span_singleton], ?_⟩
  rw [f₂, Ideal.span_singleton_mul_span_singleton]
  exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 (hv.le_iff_dvd.1 e₂.ge))
    (Ideal.span_singleton_le_span_singleton.2 (hv.le_iff_dvd.1 e₂.le))

end At

theorem ideal_of_frames (hS : PlaceShiftSt) (hH : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H) (X : CMObj H K ρ σ₁ p q)
    {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ)
    (hF : ∀ (ℓ : ℕ) [Fact ℓ.Prime] [IsAdicComplete (Ideal.span {(ℓ : 𝓞_ℂ_[ℓ])}) 𝓞_ℂ_[ℓ]] (ε : Eps ℓ ℂ_[ℓ])
      (i : K →+* ℂ_[ℓ]) (τ : E →+* ℂ_[ℓ]), τ (H.rt : E) = i (ρ : K) →
      letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
      HasSigFrames (pointB (PadicComplexInt.integers ℓ) ε i X) H.rt τ p q ∧
        HasSigFrames (pointA (PadicComplexInt.integers ℓ) ε i X true) H.rt τ 1 0 ∧
        HasSigFrames (pointA (PadicComplexInt.integers ℓ) ε i X false) H.rt τ 0 1) :
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det * gQ.det} ∧
      ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))
        (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
          idx K p (FB.eigLat X.B.t.act τ) (subP FP FB MP τ) * Ideal.span {τ gQ.det} =
            𝔫.map τ * idx K q (FB.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))
              (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
  obtain ⟨𝔫, h1, h2⟩ := index_ideal X h
  refine ⟨𝔫, h1, fun FP FQ FB MP MQ hD τ hτ => ?_⟩
  obtain ⟨n1, n2⟩ := idx_sub_ne_bot hD hτ
  obtain ⟨g1, g2, -⟩ := GlobalTheory.GramAt.gram_det X h
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h0
    have h := Ideal.absNorm_mem (RingHom.ker τ)
    rw [RingHom.mem_ker, map_natCast, Nat.cast_eq_zero] at h
    exact h0 (Ideal.absNorm_eq_zero_iff.1 h)
  have h𝔫 : 𝔫 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
    exact mul_ne_zero g1 g2 h1
  refine ideal_eq_of_map_eq (mul_ne_zero n1 (Ideal.span_singleton_eq_bot.not.2 ((map_ne_zero_iff τ hinj).2 g2)))
    (mul_ne_zero ((Ideal.map_eq_bot_iff_of_injective hinj).not.2 h𝔫) n2) fun ℓ _ i => ?_
  letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
  haveI := PadicComplexHost.isAdicComplete ℓ
  obtain ⟨ε⟩ : Nonempty (Eps ℓ ℂ_[ℓ]) := inferInstance
  obtain ⟨φ, hφ, hI⟩ := h2 ℓ ε i τ
  have hrt : φ (H.rt : E) = i (ρ : K) := by
    rw [← algebraMap_embO (PadicComplexInt.integers ℓ) φ, hφ, RingHom.comp_apply, hτ, algebraMap_embO]
  obtain ⟨fB, fP, fQ⟩ := hF ℓ ε i φ hrt
  have hR := isIndexRel_of_hasSigFrames (PadicComplexInt.integers ℓ) ε i X h φ fB fP fQ _ hI
  obtain ⟨-, n, -, -, -, -, hn⟩ := hI
  obtain ⟨κ₁, κ₂, hκ⟩ := PlaceShiftModel.pointShiftSt_of_placeShiftSt hS E H hH ℓ φ
  rw [← hn] at hR
  have hn' : ∀ x : ℂ_[ℓ], ‖x‖ = ((Valued.v x : ℝ≥0) : ℝ) := fun x => by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  obtain ⟨d, e₁, e₂⟩ := map_eq_at (PadicComplexInt.integers ℓ) ε i hD hτ hφ hR fB fP fQ
    fun P p q a x x' g g' b c d e => by rw [← hn', ← hn']; exact hκ P p q a x x' g g' b c d e
  refine ⟨d, ?_, ?_⟩
  · rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, ← e₁, hφ]
    rfl
  · rw [Ideal.map_mul, Ideal.map_map, ← hn, e₂]

theorem idealSt_of_placeShiftSt : PlaceShiftSt → IdealSt := fun hS _ _ _ _ H hH _ _ _ _ _ _ _ X _ _ h =>
  ideal_of_frames hS hH X h fun ℓ _ _ ε i τ hτ => by
    letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
    exact CMKernel.hasSigFrames_of_isGram _ ε i X h τ hτ

end GlobalTheory.CMIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageDegreePositive
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo

namespace GlobalTheory.ImageModel

theorem exists_isModelOf : Hypotheses2 → ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ), (∀ σ : K →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → HasGram Nm → (∀ σ x, Nm ((starRingEnd ℂ).comp σ) x = Nm σ x) → W.FG → Submodule.span K (W : Set V) = ⊤ → GlobalTheory.DegVal.GenRatios ev → 0 < imageDeg ev D → ∃ (X : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral X) (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s := by
  intro _ K V Ω _ _ _ _ _ _ _ _ Nm W ev D hK hG hcj hW hs hR hD
  classical
  obtain ⟨N, n, b, w, A, hF⟩ := GlobalTheory.CompHt.exists_isFrame hK hcj hG hW hs
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso
      have hW0 : W = ⊥ := by rw [← hF.span]; simp
      have htop : (⊤ : Submodule K V) = ⊥ := by rw [← hs, hW0]; simp
      refine hR.1 (LinearMap.ext fun x => ?_)
      have hx : x ∈ (⊥ : Submodule K V) := htop ▸ Submodule.mem_top
      rw [Submodule.mem_bot] at hx
      simp [hx]
    · exact ⟨m, rfl⟩
  set u : Fin (m + 1) → V := fun k => ∑ j, w j k • b j with hu_def
  have huW : ∀ k, u k ∈ W := fun k => hF.span ▸ Submodule.subset_span ⟨k, rfl⟩
  let gw : Fin (m + 1) → W := fun k => ⟨u k, huW k⟩
  have hspan : Submodule.span K (Set.range u) = ⊤ := by
    rw [← hs, ← hF.span, Submodule.span_span_of_tower]
  choose cc hcc using fun j => (Submodule.mem_span_range_iff_exists_fun K).1
    (hspan ▸ Submodule.mem_top : b j ∈ Submodule.span K (Set.range u))
  let c : Matrix (Fin (m + 1)) (Fin N) K := Matrix.of fun k j => cc j k
  set y : Fin (m + 1) → Ω := fun k => ev (u k) with hy_def
  have hy0 : y ≠ 0 := fun h0 => hR.1 (LinearMap.ext_on_range hspan fun k => by
    simpa using congrFun h0 k)
  obtain ⟨Y, _, q, B₀, hB₀, t, ψ₀, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_integral_projective_closure_of_linearSystem_point K V Ω ev D m u hspan hR hD
  obtain ⟨X₀, _, p₀, g₀, ψ₁, e⟩ := GlobalTheory.T.exists_flat_projective_model_over_ringOfIntegers K Ω D m y Y q B₀ hB₀ t ψ₀ h1 h2 h3 h4 h5 h6
  obtain ⟨X, _, p, g, ψ, hgp, har, hnorm, hbij, hbase, hrat⟩ := GlobalTheory.T.exists_normal_arithmeticVariety_model_projectiveSpace K Ω D m y X₀ p₀ g₀ ψ₁ e
  let B := (ProjSpace.O1 (𝓞 K) m).pull g
  have hB : B.IsLB := LB.isLB_pull (ProjSpace.O1_isLB _ m) g
  let sk : Fin (m + 1) → B.Sec := fun k => secPull (ProjSpace.coord (𝓞 K) m k) g
  obtain ⟨hlin, hrel⟩ := GlobalTheory.T.pulledBack_coordinate_combination_ratio_and_vanish K Ω m y X p g ψ hbase hrat
  have hev : ∀ lam : Fin (m + 1) → 𝓞 K, ev (∑ k, lam k • u k) = ∑ k, algebraMap K Ω (lam k : K) * y k := by
    intro lam
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← algebraMap_smul K (lam k) (u k), LinearMap.map_smul, Algebra.smul_def]
  have hrelV : ∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • sk k = 0 :=
    fun lam h0 => hrel hy0 lam (by rw [← hev, h0, map_zero])
  choose coef hcoef using fun x : W => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1
    (hF.span.symm ▸ x.2 : (x : V) ∈ Submodule.span (𝓞 K) (Set.range u))
  let s : W → B.Sec := fun x => ∑ k, algX p ⊤ (coef x k) • sk k
  have sg : ∀ k, s (gw k) = sk k := by
    intro k
    have e1 : ∑ l, (Pi.single k (1 : 𝓞 K) : Fin (m + 1) → 𝓞 K) l • u l = u k := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl, zero_smul]) (by simp)]
      rw [Pi.single_eq_same, one_smul]
    have e3 : ∑ l, algX p ⊤ ((Pi.single k (1 : 𝓞 K) : Fin (m + 1) → 𝓞 K) l) • sk l = sk k := by
      rw [Finset.sum_eq_single k (fun l _ hl => by rw [Pi.single_eq_of_ne hl, map_zero, zero_smul]) (by simp)]
      rw [Pi.single_eq_same, map_one, one_smul]
    have h0 := hrelV (coef (gw k) - Pi.single k 1) (by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hcoef, e1]
      exact sub_eq_zero.2 (hcoef (gw k)))
    simp only [Pi.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib, e3, sub_eq_zero] at h0
    exact h0
  have hbpf : ⨆ k, nonzeroLocus (sk k) = ⊤ :=
    ProjSpace.iSup_nonzeroLocus_secPull (ProjSpace.iSup_nonzeroLocus_coord (𝓞 K) m) g
  let A' : (𝓞 K →+* ℂ) → Matrix (Fin (m + 1)) (Fin N) ℂ := fun τ =>
    c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)
  have hnz := GlobalTheory.T.fubiniStudy_coordinate_combinations_noCommonZero K V m N X p g u b c A hgp hrelV (fun j => (hcc j).symm) hF.herm
  have hcU : ∀ τ : 𝓞 K →+* ℂ, ∃ U ∈ Matrix.unitaryGroup (Fin N) ℂ,
      A' ((starRingEnd ℂ).comp τ) = (A' τ).map (starRingEnd ℂ) * U := by
    intro τ
    obtain ⟨U, hU, eU⟩ := GlobalTheory.T.frame_conjugate_embedding_eq_conj_mul_unitary K N A hF.conj hF.herm (OfLattice.extEmb τ)
    have he : OfLattice.extEmb ((starRingEnd ℂ).comp τ) = (starRingEnd ℂ).comp (OfLattice.extEmb τ) :=
      OfLattice.extEmb_eq (by rw [RingHom.comp_assoc, OfLattice.extEmb_comp])
    refine ⟨U, hU, ?_⟩
    simp only [A', he, eU, Matrix.map_mul, Matrix.map_map, Matrix.mul_assoc]
    rfl
  let L : HermLB p := OfLattice.combHerm hB sk A' hnz hcU
  refine ⟨X, inferInstance, p, L, ψ, s, har, hnorm, hbij, hbase, ?_, ?_, ?_⟩
  · obtain ⟨k₀, hk₀⟩ : ∃ k, y k ≠ 0 := by
      by_contra! h; exact hy0 (funext h)
    intro x x' i h
    have hψ : ψ (y k₀) ≠ 0 := (map_ne_zero ψ).2 hk₀
    have ha : ψ (y k₀) * fnOf _ h ((s x).f i) = ψ (ev x) * fnOf _ h ((sk k₀).f i) := by
      have := hlin (coef x) k₀ i h
      rwa [← hev, hcoef] at this
    have hb : ψ (y k₀) * fnOf _ h ((s x').f i) = ψ (ev x') * fnOf _ h ((sk k₀).f i) := by
      have := hlin (coef x') k₀ i h
      rwa [← hev, hcoef] at this
    refine mul_left_cancel₀ hψ ?_
    linear_combination (ψ (ev x)) * hb - (ψ (ev x')) * ha
  · refine top_le_iff.1 ?_
    rw [← hbpf]
    exact iSup_le fun k => by
      rw [← sg k]
      exact le_iSup (fun x => nonzeroLocus (s x)) (gw k)
  · refine ⟨N, m + 1, b, w, A, c, gw, hF, fun k => rfl, fun j => (hcc j).symm, fun σ i z => ?_⟩
    have he : OfLattice.extEmb (σ.comp (algebraMap (𝓞 K) K)) = σ := OfLattice.extEmb_eq rfl
    refine (OfLattice.combWeight_φ hB sk _ (hnz _) i z).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sg k]
    simp only [A', he, Matrix.mul_apply, Matrix.map_apply, c, Matrix.of_apply]
    rfl

end GlobalTheory.ImageModel
end

