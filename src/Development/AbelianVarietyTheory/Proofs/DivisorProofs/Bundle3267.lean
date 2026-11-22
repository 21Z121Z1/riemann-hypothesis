import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2591
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0511
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2527
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1614
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIsAlgebraicOfEllipticCMTheorems
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open GlobalTheory.HilbFam GlobalTheory.QFam GlobalTheory.WpFam
open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.RoadELatAlg

theorem isAlgebraic_of_sq_eq_ratCast {x : ℂ} (q : ℚ) (h : x ^ 2 = (q : ℂ)) : IsAlgebraic ℚ x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C q, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (by norm_num) q
  · simp [h]

theorem exists_theta {K : Type} [Field K] [NumberField K] (ι : K →+* ℂ) (Λ : PeriodPair)
    (hΛ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ) (c : ℂ) (τ : ℍ) (hτ : IsTauOf Λ c τ) :
    ∃ θ : K, ι θ = (τ : ℂ) ∧ IsAlgebraic ℚ c := by
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice → ∃ a : K, ι a = z := by
    intro z hz
    have : z ∈ (Λ.lattice : Set ℂ) := hz
    rw [hΛ] at this
    obtain ⟨a, -, ha⟩ := this
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hmem c ((hτ.2 c).2 ⟨0, 1, by simp⟩)
  obtain ⟨b, hb⟩ := hmem (c * τ) ((hτ.2 _).2 ⟨1, 0, by simp⟩)
  have hc : c ≠ 0 := hτ.1
  refine ⟨b / a, ?_, ?_⟩
  · rw [map_div₀, ha, hb]; field_simp
  · rw [← ha]; exact (Algebra.IsAlgebraic.isAlgebraic a).algHom ι.toRatAlgHom

theorem term_div_eq (r Y H ω : ℂ) (a w W : ℕ) (h : W = 2 * a + w) :
    r * Y ^ a * H / ω ^ W = r * ((Y / ω ^ 2) ^ a * (H / ω ^ w)) := by
  subst h
  rw [pow_add, pow_mul, div_pow]
  ring

theorem coord_id (c0 S0 D Ω c cW P pi im r p sg : ℂ) (W K : ℕ) (hsg : sg ≠ 0) (hD : D = cW * (sg * P) * S0)
    (hc0 : c0 = cW * P * (2 * pi / r) ^ K) (hΩ : Ω ≠ 0) (hc : c ≠ 0) (hp : p ≠ 0) (him : im ≠ 0) (hr : r ≠ 0) :
    c0 * S0 / Ω ^ W = sg⁻¹ * (2 * im / r) ^ K * c ^ W * (D * (pi / im) ^ K / p ^ W / (Ω * c / p) ^ W) := by
  have h2 : (2 * im / r) ^ K * (pi / im) ^ K = (2 * pi / r) ^ K := by
    rw [← mul_pow]; congr 1; field_simp
  have h3 : c ^ W / p ^ W / (Ω * c / p) ^ W = 1 / Ω ^ W := by
    rw [div_pow, mul_pow]; field_simp
  calc c0 * S0 / Ω ^ W = (sg⁻¹ * sg) * (cW * P * S0) * ((2 * im / r) ^ K * (pi / im) ^ K) *
        (c ^ W / p ^ W / (Ω * c / p) ^ W) := by
          rw [inv_mul_cancel₀ hsg, h2, h3, hc0]; ring
    _ = _ := by rw [hD]; ring

theorem latAlg_of_siegelKlingen : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation →
    GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatAlg := by
  intro hSKDR hPZ _ _
  intro K _ _ d δ ι hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ s 𝔣 Q hDat κ y S hS
  classical
  obtain ⟨hUn, hCM, hφι, hs, h𝔣, hQ⟩ := hDat
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := GlobalTheory.LatAlgebraic.two_le_finrank hUn
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hΩ0 : Ω₀ ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ₀ (by rw [← hΩ]; simp)
  have hW2 := GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ
  have hSt := GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke hW2
  have hEis := GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta GlobalTheory.T.lipschitz_formula_totally_real_poisson hW2 hPZ
  obtain ⟨⟨z, hz⟩, -⟩ := GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet hSKDR E s hs
  obtain ⟨⟨g, hg⟩, hD⟩ := (((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1
  obtain ⟨u, hu⟩ := GlobalTheory.LatAlgebraic.exists_list_count κ
  have hDg := ((hD g hg).2 κ u hu).1 S hS
  obtain ⟨c, τ, hτ⟩ := latTau Λ₀
  obtain ⟨θ, hθτ, hcalg⟩ := exists_theta ι Λ₀ hΛ c τ hτ
  have hc : c ≠ 0 := hτ.1
  have hφθ : ∀ i, φ i (algebraMap K E θ) = (τ : ℂ) := by
    intro i; rw [← RingHom.comp_apply, hφι i, hθτ]
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeEmb.exists_equiv E I φ hCM
  have hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := GlobalTheory.LatAlgebraic.card_eq_finrank hCM
  have hI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hI
  have hθF : algebraMap K E θ ∉ Set.range (fun x : maximalRealSubfield E => (x : E)) := by
    rintro ⟨x, hx⟩
    have h1 := he i₀ x
    change (x : E) = _ at hx
    rw [hx, hφθ i₀] at h1
    have h2 := congrArg Complex.im h1
    simp only [Complex.ofReal_im] at h2
    exact τ.im_pos.ne' h2
  obtain ⟨n, N, L, hn, hN, hN2, hL, hLΛ⟩ := GlobalTheory.RoadE.exists_level E (algebraMap K E θ) (condQ 𝔣 Q) y 2 hc0 hθF (by norm_num)
  have hN2' : 2 ≤ N := Nat.le_of_dvd hN hN2
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨by omega⟩
  let y₁ : Fin 2 → ZMod N := ![1, 0]
  have hy₁ : y₁ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [y₁] at this
  have hval := GlobalTheory.HilbFam.eValue_derivs hEis E I φ e (algebraMap K E θ) τ (lattice (condQ 𝔣 Q) y) L n s N g κ u
    (wB N y₁) hf2 hs hN hL he hφθ hn hLΛ hg hu
  obtain ⟨hωDD, hj, hG2, hwp⟩ := GlobalTheory.AlgTau.main K d δ ι 1 Λ₀ c Ω₀ τ hd hδ hΛ hτ hΩ

  set ω : ℂ := Ω₀ * c / (2 * Real.pi * Complex.I) with hω
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  have hω0 : ω ≠ 0 := div_ne_zero (mul_ne_zero hΩ0 hc) h2piI
  have hH : ∀ μ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb (maximalRealSubfield E) → ℕ,
      IsAlgebraic ℚ (GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ / ω ^ GlobalTheory.HilbFam.wt (2 * s) μ) := by
    intro μ
    have h := GlobalTheory.QFam.fam_value_isAlgebraic (GL (Fin 2) (ZMod N)) (GlobalTheory.WpFam.gact N 1) (GlobalTheory.HilbFam.wt (2 * s) μ) N
      (fun α ↦ GlobalTheory.HilbFam.hfun (2 * s) (GlobalTheory.HilbFam.twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) μ (wB N (GlobalTheory.WpFam.vmul y₁ α)))
      τ ω (by omega) (((GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).2.1 1).actBij)
      (GlobalTheory.HilbFam.isFam_hfun_GL hEis (maximalRealSubfield E) hf2 s N L hs hL y₁ μ)
      (fun α ↦ GlobalTheory.HilbFam.qAll_isAlgebraic_hfun_twist hEis (maximalRealSubfield E) hf2 s N L hs hL z hz μ y₁ hy₁ α)
      hj hωDD 1
    simpa only [Units.val_one, GlobalTheory.HilbFam.twist_one_of_hasLevel _ N L hL, (GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).2.2.2.1] using h
  have hX : IsAlgebraic ℚ ((((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y₁ τ) / ω ^ 2) := by
    rw [GlobalTheory.wB_nonhol_correction, neg_div, add_div]
    exact ((hG2.add (hwp N y₁))).neg
  set f := Module.finrank ℚ (maximalRealSubfield E) with hf
  set k := ∑ i, κ i with hk
  set P : ℂ := 2 * Real.pi * Complex.I with hP
  set Y : ℂ := ((Real.pi / τ.im : ℝ) : ℂ) / P ^ 2 - wB N y₁ τ with hY
  set κ' : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb (maximalRealSubfield E) → ℕ := fun j ↦ κ (e.symm j) with hκ'
  have hsum' : ∑ j, κ' j = k := Equiv.sum_comp e.symm κ
  have hA : ∀ x : ℂ, IsAlgebraic ℚ x → x ∈ algebraicClosure ℚ ℂ := fun x h ↦ mem_algebraicClosure_iff.2 h

  have hRalg : IsAlgebraic ℚ (((n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ',
      ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) * Y ^ (∑ j, (κ' j - μ j)) *
        GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ) / ω ^ (2 * s * f + 2 * k)) := by
    have key : ((n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ',
        ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) * Y ^ (∑ j, (κ' j - μ j)) *
          GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ) / ω ^ (2 * s * f + 2 * k) =
        (n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ', ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) *
          ((Y / ω ^ 2) ^ (∑ j, (κ' j - μ j)) * (GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ / ω ^ GlobalTheory.HilbFam.wt (2 * s) μ)) := by
      rw [mul_div_assoc, Finset.sum_div]
      refine congrArg _ (Finset.sum_congr rfl fun μ hμ ↦ ?_)
      have hle : μ ≤ κ' := Finset.mem_Iic.1 hμ
      have hexp : 2 * s * f + 2 * k = 2 * (∑ j, (κ' j - μ j)) + GlobalTheory.HilbFam.wt (2 * s) μ := by
        have h1 : ∑ j, (κ' j - μ j) + ∑ j, μ j = ∑ j, κ' j := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ ↦ Nat.sub_add_cancel (hle j)
        change 2 * s * f + 2 * k = 2 * (∑ j, (κ' j - μ j)) + (2 * s * f + 2 * ∑ j, μ j)
        omega
      exact term_div_eq _ _ _ _ _ _ _ hexp
    rw [key, ← mem_algebraicClosure_iff]
    refine mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun μ _ ↦ mul_mem (intCast_mem _ _)
      (mul_mem (pow_mem (hA _ hX) _) (hA _ (hH μ))))
  have hRalg' : IsAlgebraic ℚ (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 * ((Real.pi / τ.im : ℝ) : ℂ) ^ k / P ^ (2 * s * f + 2 * k) /
      ω ^ (2 * s * f + 2 * k)) := by
    rw [hval]; exact hRalg
  rw [Complex.ofReal_div] at hRalg'
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have him : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
  have hcW : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt
      have h1 : (0 : ℝ) < |(discr (maximalRealSubfield E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
      exact mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos h1 _)
    exact_mod_cast this.ne'
  have hP' : (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j) :=
      Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => by positivity
    exact_mod_cast this.ne'
  have hsgn : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hC0 : ((C0 E d (2 * s) κ : ℝ) : ℂ) = (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) *
      (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ k := by
    rw [GlobalTheory.LatAlgebraic.cmPeriodConstant_eq_of_card_cmType hcard d s hs κ]; push_cast; ring
  rw [GlobalTheory.LatAlgebraic.risingFactor_eq] at hDg
  have key2 : GlobalTheory.ToricTransport.coordIn E d s κ Ω₀ (S 0) = ((-1 : ℂ) ^ k)⁻¹ *
      (2 * ((τ.im : ℝ) : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ k * c ^ (2 * s * f + 2 * k) *
      (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 * ((Real.pi : ℂ) / ((τ.im : ℝ) : ℂ)) ^ k / P ^ (2 * s * f + 2 * k) /
        ω ^ (2 * s * f + 2 * k)) := by
    rw [GlobalTheory.ToricTransport.coordIn, hcard]
    exact coord_id _ (S 0) (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0) Ω₀ c _ _ (Real.pi : ℂ) ((τ.im : ℝ) : ℂ)
      ((Real.sqrt d : ℝ) : ℂ) P ((-1 : ℂ) ^ k) (2 * s * f + 2 * k) k hsgn hDg hC0 hΩ0 hc h2piI him hsd
  have hτalg : IsAlgebraic ℚ (τ : ℂ) := by
    rw [← hθτ]; exact (Algebra.IsAlgebraic.isAlgebraic θ).algHom ι.toRatAlgHom
  have hτc : IsAlgebraic ℚ (starRingEnd ℂ (τ : ℂ)) := by
    rw [← hθτ]; exact (Algebra.IsAlgebraic.isAlgebraic θ).algHom ((starRingEnd ℂ).comp ι).toRatAlgHom
  have hIalg : IsAlgebraic ℚ Complex.I := isAlgebraic_of_sq_eq_ratCast (-1) (by simp [Complex.I_sq])
  have himalg : IsAlgebraic ℚ ((τ.im : ℝ) : ℂ) := by
    rw [← UpperHalfPlane.coe_im, Complex.im_eq_sub_conj, ← mem_algebraicClosure_iff]
    exact div_mem (sub_mem (hA _ hτalg) (hA _ hτc)) (mul_mem (ofNat_mem _ 2) (hA _ hIalg))
  have hsdalg : IsAlgebraic ℚ ((Real.sqrt d : ℝ) : ℂ) := by
    refine isAlgebraic_of_sq_eq_ratCast (d : ℚ) ?_
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  rw [key2, ← mem_algebraicClosure_iff]
  exact mul_mem (mul_mem (mul_mem (inv_mem (pow_mem (neg_mem (one_mem _)) _))
    (pow_mem (div_mem (mul_mem (ofNat_mem _ 2) (hA _ himalg)) (hA _ hsdalg)) _)) (pow_mem (hA _ hcalg) _)) (hA _ hRalg')

end GlobalTheory.RoadELatAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchIntegralAdditiveAndDiagonal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixAdd

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem archInt_congr {A B : HermLB q} (h : A.Isometric B) (M : HermLB q) (e : ℕ) {r : M.B.ι → Y.functionFieldˣ}
    (hr : IsRatSec M.B r) : A.archInt M e hr = B.archInt M e hr := by
  simp only [HermLB.archInt, h.chernInt_eq]

theorem lin_comb {ι κ : Type} [Fintype ι] [Fintype κ] (m : κ → ι → ℤ) (n : κ → ℤ) :
    (lin fun i => ((∑ j, n j * m j i : ℤ) : ℝ)) = ∑ j, (n j : ℝ) • lin fun i => (m j i : ℝ) := by
  simp only [lin, Int.cast_sum, Int.cast_mul, map_sum, map_mul, Finset.sum_mul, smul_eq_C_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lin_add {ι : Type} [Fintype ι] (m n : ι → ℤ) :
    (lin fun i => (((m + n) i : ℤ) : ℝ)) = (lin fun i => (m i : ℝ)) + lin fun i => (n i : ℝ) := by
  simp only [lin, Pi.add_apply, Int.cast_add, map_add, add_mul, Finset.sum_add_distrib]

theorem mixArch_eq {ι : Type} [Fintype ι] {e : ℕ} (F : ι → HermLB q) (M : HermLB q) {r : M.B.ι → Y.functionFieldˣ}
    (hr : IsRatSec M.B r) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hΨ : ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb F n).archInt M e hr)
    (L : Fin e → HermLB q) (m : Fin e → ι → ℤ) (h : ∀ a, (comb F (m a)).Isometric (L a)) :
    mixArch L M hr = Ψ (∏ a, lin fun i => (m a i : ℝ)) := by
  have h₁ : (fun n => (comb L n).archInt M e hr) =
      fun n : Fin e → ℤ => Ψ ((∑ a, (n a : ℝ) • lin fun i => (m a i : ℝ)) ^ e) := by
    funext n
    rw [← lin_comb, hΨ]
    exact (archInt_congr ((isometric_comb_comb F m n).trans (isometric_comb_congr h n)) M e hr).symm
  rw [mixArch, h₁, FibreProj.pol_pow _ Ψ (Fintype.card_fin e), mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.2 e.factorial_ne_zero

theorem mixArch_add_diag : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r),
    (∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ (A B : HermLB q) (L : Fin e → HermLB q),
      mixArch (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr =
        mixArch (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) M hr) ∧
    ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ N : HermLB q,
      mixArch (fun _ : Fin e => N) M hr = N.archInt M e hr := by
  intro hI k _ Y _ q hq M r hr
  classical
  refine ⟨fun e he A B L => ?_, fun e he N => ?_⟩
  · let F : Bool ⊕ Fin e → HermLB q := Sum.elim (fun b => cond b A B) L
    obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_linear_functional_arch_integral_chern_power k Y q hq (e + 1) _ F M r hr
      fun n => GlobalTheory.T.archIntegrable_of_projArithAmbient hI k Y q hq (e + 1) he M _ r hr
    let u : Bool ⊕ Fin e → Bool ⊕ Fin e → ℤ := fun j => Pi.single j 1
    have key (C : HermLB q) (c : Bool ⊕ Fin e → ℤ) (hc : (comb F c).Isometric C) :
        mixArch (Fin.cons C L : Fin (e + 1) → HermLB q) M hr =
          Ψ ((lin fun i => (c i : ℝ)) * ∏ a : Fin e, lin fun i => (u (Sum.inr a) i : ℝ)) := by
      rw [mixArch_eq F M hr Ψ hΨ (Fin.cons C L) (Fin.cons c fun a => u (Sum.inr a)) (fun a => by
        cases a using Fin.cases with
        | zero => exact hc
        | succ a => exact isometric_comb_single F (Sum.inr a)), Fin.prod_univ_succ]
      rfl
    have hA : (comb F (u (Sum.inl true))).Isometric A := isometric_comb_single F (Sum.inl true)
    have hB : (comb F (u (Sum.inl false))).Isometric B := isometric_comb_single F (Sum.inl false)
    rw [key A _ hA, key B _ hB, key _ _ ((isometric_comb_add F _ _).trans (hA.tens hB)), lin_add, add_mul, map_add]
  · let F : Unit → HermLB q := fun _ => N
    obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_linear_functional_arch_integral_chern_power k Y q hq e _ F M r hr fun n => GlobalTheory.T.archIntegrable_of_projArithAmbient hI k Y q hq e he M _ r hr
    have hN : (comb F (Pi.single () 1)).Isometric N := isometric_comb_single F ()
    rw [mixArch_eq F M hr Ψ hΨ _ (fun _ => Pi.single () 1) fun _ => hN, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hΨ]
    exact archInt_congr hN M e hr

end GlobalTheory.MixAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosurePullback
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.CycPush

theorem isProjOver_comp {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsProjOver p)
    (i : Z ⟶ X) [IsClosedImmersion i] : IsProjOver (i ≫ p) := by
  obtain ⟨N, j, hj, rfl⟩ := hp
  exact ⟨N, i ≫ j, inferInstance, by rw [Category.assoc]⟩

theorem pull_congr {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (A : MLine p σ) {a b : Y ⟶ X} (hab : a = b) (ha : a ≫ p = q) (hb : b ≫ p = q) :
    A.pull a ha = A.pull b hb := by
  subst hab; rfl

theorem dim_le_of_dominant : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ n : ℕ, topologicalKrullDim Y = n → ∃ m : ℕ, m ≤ n ∧ topologicalKrullDim X = m := by
  intro F _ W M _ _ p q hp hq f hπ hη n hM
  obtain ⟨N, i, hi, hcomp⟩ := hp
  obtain ⟨N', j, hj, hcomp'⟩ := hq
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : IsProper (PSpace.str F N') := isProper_str F N'
  haveI : IsProper p := by rw [← hcomp]; infer_instance
  haveI : IsProper (f ≫ p) := by rw [hπ, ← hcomp']; infer_instance
  haveI : IsProper f := IsProper.of_comp f p
  have hf : LocallyOfFiniteType f := inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  have hV : IsAffineOpen V := hV
  have hx : f (genericPoint M) ∈ V := hη ▸ hxV
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hUV⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint M ∈ f ⁻¹ᵁ V from hx) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let φ := Spec.preimage (hV.fromSpec ≫ p)
  have hφ : Spec.map φ = hV.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(W, V) := φ.hom.toAlgebra
  have hftA : Algebra.FiniteType F Γ(W, V) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  letI : Algebra Γ(W, V) Γ(M, U) := (f.appLE V U e).hom.toAlgebra
  have hftB : Algebra.FiniteType Γ(W, V) Γ(M, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf ⟨V, hV⟩ ⟨U, hU⟩ e
  letI : Algebra F Γ(M, U) := (φ ≫ f.appLE V U e).hom.toAlgebra
  haveI : IsScalarTower F Γ(W, V) Γ(M, U) := IsScalarTower.of_algebraMap_eq' rfl
  have hftC : Algebra.FiniteType F Γ(M, U) := Algebra.FiniteType.trans hftA hftB
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(W, V)
  have hd : topologicalKrullDim (V : Set W) = d := by
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
      hV.range_fromSpec
  rw [GlobalTheory.OpenDim.topologicalKrullDim_open F p V ⟨_, hx⟩] at hd
  have hB : Algebra.trdeg F Γ(M, U) = n := GlobalTheory.GenFinite.trdeg_affineOpen_eq F (f ≫ p) hU ⟨_, hy⟩ n hM
  letI := (W.evaluation V _ hx).hom.toAlgebra
  have nat : f.appLE V U e ≫ M.evaluation U _ hy =
      W.evaluation V _ hx ≫ f.residueFieldMap (genericPoint M) := by
    rw [Scheme.evaluation_naturality f _ hx, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation]
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  haveI := GenFiniteEtale.isFractionRing_eval W hV hη hx
  have hinj : Function.Injective (IsScalarTower.toAlgHom F Γ(W, V) Γ(M, U)) := by
    have h₃ : Function.Injective (f.appLE V U e ≫ M.evaluation U _ hy).hom := by
      rw [nat]
      exact (f.residueFieldMap (genericPoint M)).hom.injective.comp
        (IsFractionRing.injective Γ(W, V) (W.residueField (f (genericPoint M))))
    exact Function.Injective.of_comp (f := (M.evaluation U _ hy).hom) h₃
  have hle := trdeg_le_of_injective _ hinj
  rw [h₂, hB] at hle
  exact ⟨d, by exact_mod_cast hle, hd⟩

theorem cycInt_pull : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (e : ℕ) (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∀ w : Y, topologicalKrullDim (closure ({w} : Set Y)) = e → (topologicalKrullDim (closure ({π w} : Set X)) = e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = π.residueDegree w * cycInt L f (π w)) ∧ (topologicalKrullDim (closure ({π w} : Set X)) ≠ e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = 0) := by
  intro F _ X Y p q σ hp hq π hπ e L f hf w hw
  obtain ⟨hIw, hgw, hdw, -⟩ := GlobalTheory.ClosFacts.clos_facts Y w
  obtain ⟨hIx, hgx, hdx, hfac⟩ := GlobalTheory.ClosFacts.clos_facts X (π w)
  have hη : (closι w ≫ π) (genericPoint (clos w)) = π w := by
    rw [Scheme.Hom.comp_apply, hgw]
  obtain ⟨g, hg, hgg, hgdeg, -⟩ := hfac (clos w) (closι w ≫ π) hη
  have hpX : IsProjOver (closι (π w) ≫ p) := isProjOver_comp hp _
  have hpY : IsProjOver (closι w ≫ q) := isProjOver_comp hq _
  have hgp : g ≫ closι (π w) ≫ p = closι w ≫ q := by
    rw [← Category.assoc, hg, Category.assoc, hπ]
  have hdY : topologicalKrullDim (clos w) = e := hdw.trans hw
  let L' : Fin e → MLine (closι (π w) ≫ p) σ := fun i => (L i).pull (closι (π w)) rfl
  let f' : CxPts (closι (π w) ≫ p) σ → ℝ := fun y => f (ptMap (closι (π w)) rfl σ y)
  have hf' : Measurable f' := hf.comp (PtsOver.continuous_map _ _ _).measurable

  have h1 : (closι w ≫ π) ≫ p = closι w ≫ q := by rw [Category.assoc, hπ]
  have h2 : (g ≫ closι (π w)) ≫ p = closι w ≫ q := by rw [Category.assoc, hgp]
  have hpart : ∀ ε : ℤˣ, part (fun i => ((L i).pull π hπ).pull (closι w) rfl) ε = part (fun i => (L' i).pull g hgp) ε := by
    intro ε
    have c1 := (GlobalTheory.Mix.isom_calculus F X Y p q σ π hπ).2.2.2.2.2 (clos w) (closι w ≫ q) (closι w) rfl h1
    have c2 := (GlobalTheory.Mix.isom_calculus F X (clos (π w)) p (closι (π w) ≫ p) σ (closι (π w)) rfl).2.2.2.2.2 (clos w)
      (closι w ≫ q) g hgp h2
    have e1 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c1 (L i)) ε
    have e2 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c2 (L i)) ε
    rw [e1, e2]
    congr 1
    funext i
    exact pull_congr _ hg.symm _ _
  have hfun : (fun y => (fun y => f (ptMap π hπ σ y)) (ptMap (closι w) rfl σ y)) = fun y => f' (ptMap g hgp σ y) := by
    funext y
    show f _ = f _
    congr 1
    apply Subtype.ext
    simp only [PtsOver.map_val, Category.assoc, hg]
  have hint : cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w =
      Mix.int (fun i => (L' i).pull g hgp) (fun y => f' (ptMap g hgp σ y)) := by
    simp only [cycInt, Mix.int]
    rw [hfun, hpart 1, hpart (-1)]
  refine ⟨fun hX => ?_, fun hX => ?_⟩
  · have hdX : topologicalKrullDim (clos (π w)) = e := hdx.trans hX
    have hne := GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint F (clos (π w)) (clos w)
      (closι (π w) ≫ p) (closι w ≫ q) e hpX hpY hdX hdY g hgp hgg
    have hpush := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e hpX hdX hpY g hgp
      hgg hne L' f' hf').2
    have hdeg : g.residueDegree (genericPoint (clos w)) = π.residueDegree w := by
      rw [hgdeg, GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.ProperCut.residueDegree_of_isClosedImmersion (closι w),
        mul_one, hgw]
    rw [hint, hpush, hdeg]
    rfl
  · obtain ⟨m, hm, hdX⟩ := dim_le_of_dominant F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) hpX hpY g hgp
      hgg e hdY
    have hlt : m < e := lt_of_le_of_ne hm fun h => hX (by rw [← hdx, hdX, h])
    have h0 := GlobalTheory.T.mixedChernMeasure_pullback_eq_zero_of_lt_dim F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e m hlt hpX hdX hpY g hgp hgg L'
    rw [hint]
    simp only [Mix.int, h0, integral_zero_measure, sub_zero]

end GlobalTheory.CycPush
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureFiniteIntegrableProjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixFin

theorem finite_and_intg : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → ∀ (L : Fin D → MLine p σ), (∀ ε : ℤˣ, IsFiniteMeasure (part L ε)) ∧ ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
  intro hP F _ X _ _ p σ D hX hdim L
  haveI : CharZero F := RingHom.charZero σ
  obtain ⟨Y, hY, π, hsm, hproj, -, hgen, hdeg, -⟩ :=
    GlobalTheory.T.exists_logResolution_projective_of_principalisation hP F X p D hX hdim ⊥ (fun h => by rwa [← SetLike.mem_coe, Closeds.coe_bot] at h)
  haveI := hY
  haveI : SmoothOfRelativeDimension D (π ≫ p) := hsm
  haveI := CxPts.compactSpace (p := π ≫ p) σ hproj
  haveI := CxPts.t2Space_cxPts_of_isProjOver (p := π ≫ p) σ hproj
  haveI := CxPts.secondCountableTopology_of_isProjOver (p := π ≫ p) σ hproj
  let R := AnRead.all (π ≫ p) σ D
  have key : ∀ f : CxPts p σ → ℝ, Continuous f → Intg L f := by
    intro f hf
    have hf' : Continuous (fun y => f (ptMap π rfl σ y)) := hf.comp (PtsOver.continuous_map _ _ _)
    have h1 := (GlobalTheory.T.mixedChernIntegral_eq_mongeAmpereIntegral_compact F Y (π ≫ p) σ D R.finAtlas R.isAlgAtlas_finAtlas
      (fun i => (L i).pull π rfl) _ hf'.measurable).1
    have hI := h1.2 (mIntegrableCont _ _ (fun i => Weight.isPotential_locPot
      ((Weight.isCInf_iff_isSmooth R).1 ((L i).pull π rfl).cInf)) _ hf')
    exact ((GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F X Y p (π ≫ p) σ D hX hdim hproj π rfl hgen
      (by rw [hdeg]; exact one_ne_zero) L f hf.measurable).1).1 hI
  refine ⟨fun ε => ?_, key⟩
  have h := key (fun _ => (1 : ℝ)) continuous_const
  rcases Int.units_eq_one_or ε with rfl | rfl
  · exact (integrable_const_iff.1 h.1).resolve_left one_ne_zero
  · exact (integrable_const_iff.1 h.2).resolve_left one_ne_zero

end GlobalTheory.MixFin
end
end

