import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0521
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0520
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfDetectingCoboundaryCharacters
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0493
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGammaLayerPadicCoordinates
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueFits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0496

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFamilyPotentiallyCrystallineFrobStableStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedFamily_potentiallyCrystalline_frobStable : ∀ (D : D7), PcrisTensorL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig0 : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ)) (c : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ) (n : ℕ),
  c ∈ Sig0 → Sig0.card ≤ n →
  (∀ x ∈ Xs, Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))) →
  (∀ x ∈ Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) Sig0) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) {c} →
  PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n := by
  first | exact @GlobalTheory.PotTwist.main | exact GlobalTheory.PotTwist.main | (intros; apply GlobalTheory.PotTwist.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformizerFamilyFrobeniusCongrPow
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section
variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

theorem zero_mem_QSet_goodU : (0 : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW]
  simp

theorem uPow_mem_QSet_goodU [CharZero K] (m : ℕ) :
    (fun _ => C (X ^ m) : ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨fun p => if p = (0, m) then ((dpDen e 0 m : ℕ) : Wq l a) else 0, ?_⟩
  funext τ
  ext i n
  rw [coeff_ofW, coeff_C]
  by_cases h : (i, n) = (0, m)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have : (dpDen e 0 n : K) ≠ 0 := Nat.cast_ne_zero.mpr (dpDen_pos e 0 n).ne'
    simp only [if_true, map_natCast, coeff_X_pow_self]
    exact div_self this
  · rw [if_neg h]
    simp only [map_zero, zero_div]
    by_cases hi : i = 0
    · subst hi
      have hn : n ≠ m := fun hn => h (by rw [hn])
      rw [if_pos rfl, coeff_X_pow, if_neg hn]
    · rw [if_neg hi, map_zero]

end

theorem uFam_mem_GoodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → uFam a K ∈ GoodSet t e φ₂ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC _
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hf : frob2 φ₂ (uFam a K) = (fun _ => C (X ^ l) : ZMod a → K⟦X⟧⟦X⟧) := by
    funext τ
    show φ₂ (C X) = _
    rw [hC, frob_X]
  refine ⟨?_, ?_, 0, zero_mem_QSet_goodU t K e, ?_⟩
  · have := uPow_mem_QSet_goodU t K e 1
    rw [pow_one] at this
    exact this
  · rw [hf]; exact uPow_mem_QSet_goodU t K e l
  · rw [hf, mul_zero, add_zero]
    funext τ
    simp [uFam]

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittEmbeddingTwistedAlgebraMapInjectiv
section
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

theorem injective_of_charZero {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {K : Type} [Field K] [CharZero K]
    (f : Wq l a →+* K) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  by_contra h0
  obtain ⟨m, b, rfl⟩ := WittVector.exists_eq_pow_p_mul' (p := l) (k := Fq l a) w h0
  rw [map_mul, map_pow, map_natCast] at hw
  have hb : f b ≠ 0 := (b.isUnit.map f).ne_zero
  have hl : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  exact mul_ne_zero (pow_ne_zero m hl) hb hw

theorem emb_algebraMap_injective : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ t τ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  exact injective_of_charZero ((algebraMap O K).comp (emb t τ).toRingHom)

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedWittPowerSeriesMemDividedPowerSeriesGeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedWittPowerSeries_mem_dividedPowerSeriesGeneratorSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ x : (Wq l a)⟦X⟧, inclS t K x ∈ SdSet t K e := by
  first | exact @GlobalTheory.CrysPrism.inclS_mem_SdSet | exact GlobalTheory.CrysPrism.inclS_mem_SdSet | (intros; apply GlobalTheory.CrysPrism.inclS_mem_SdSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesLinearIndependentOfFirstTerStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untiltFrobeniusSeries_linearIndependent_of_firstTerms : ∀ (l : ℕ) [Fact l.Prime] (h d : ℕ) (r : ℝ) (y : Fin d → ℕ → Fl l), 2 ≤ h → 0 ≤ r → r < 1 → (∀ a k, ‖sh (y a k)‖ ≤ r) → (∀ n : Fin d → ℕ, ‖sh (∑ a, n a • y a 0)‖ ≤ r ^ l ^ h → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0 := by
  first | exact @GlobalTheory.PSer.Lam_indep_of_first_terms | exact GlobalTheory.PSer.Lam_indep_of_first_terms | (intros; apply GlobalTheory.PSer.Lam_indep_of_first_terms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibilityStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachExpansion_basis_divisibility : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → Full (Di (HW l) h T i) (Lat C h T i ζ) → (∀ (a : AA K LL) (x : ↥(W.N T)), ex C h T i ζ (a • x) = conv (W.lev i ζ a) (ex C h T i ζ x)) ∧ ∀ (r : ℕ) (nb : Module.Basis (Fin r) (AA K LL) ↥(W.N T)), (∀ e : Fin r → PowerSeries ↥LL.1, ∑ j, conv (e j) (ex C h T i ζ (nb j)) = 0 → e = 0) ∧ (∀ f ∈ Lat C h T i ζ, ∃ e : Fin r → PowerSeries ↥LL.1, f = ∑ j, conv (e j) (ex C h T i ζ (nb j))) ∧ ∀ (y : ↥(W.N T)) (k : ℕ), (∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ y j = f (j - k)) ↔ ∀ j, nb.repr y j ∈ van W i ζ k := by
  first | exact @GlobalTheory.NL.LevInj.expansion_basis | exact GlobalTheory.NL.LevInj.expansion_basis | (intros; apply GlobalTheory.NL.LevInj.expansion_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPower
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.CokerFin

set_option maxHeartbeats 1000000 in

theorem coker_killed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → ∃ c : ℕ, ∀ z ∈ W.N T₂, (∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : AA K LL) ^ c • z) ∧ ∃ y ∈ W.N T₁, W.map π y = (letπ : AA K LL) ^ c • z := by
  intro D HW F Cm l _ K s LL h W E C T₀ T₁ T₂ ι π h0 h1 h2 hs
  have hP : WachCharacterisationLattice W := GlobalTheory.T.wachModule_uniqueness_characterisation D HW F l K s LL h
  have hp10 : p10 W T₂ := hP T₂ h2
  haveI := GlobalTheory.EtaleExact.finite_OL LL
  haveI : IsNoetherianRing ↥(OL LL) := IsNoetherianRing.of_finite ℤ_[l] ↥(OL LL)
  haveI := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hfl : Module.Flat (AA K LL) W.EE :=
    GlobalTheory.T.flat_wachLetterRing_completion_of_dense_saturated ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)) ((D.loc l).PD K).p W.EE W.EE_π
      W.EE_complete W.EE_dense W.EE_sat
  obtain ⟨hfree, hbc⟩ := GlobalTheory.T.wachSaturation_image_free_and_spans D HW F l K s LL h T₀ T₁ T₂ ι π h0 h1 h2 hs hfl
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.saturation_gamma_stable_of_good D HW F l K s LL h T₁ T₂ π h1 h2
  have hS := hp10 _ hfree hbc hg1 hg2 (GlobalTheory.T.wachSaturation_frobenius_mem_up_to_Q_power D HW F l K s LL h T₁ T₂ π h1 h2)
    (GlobalTheory.T.wachSaturation_Q_power_mem_frobenius_span D HW F l K s LL h T₁ T₂ π h1 h2 hfree hbc)
  obtain ⟨c, hc⟩ := GlobalTheory.NL.Coker.uniform (W.N_fg T₂) hS.ge
  refine ⟨c, fun z hz => ?_⟩
  obtain ⟨⟨y, hy, e1⟩, ⟨y', hy', e2⟩⟩ := hc z hz
  exact ⟨⟨y, hy, e1⟩, ⟨y', hy', e2⟩⟩

end GlobalTheory.NL.CokerFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassPreparationWittOfTiltFiniteFieldStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_preparation_wittOfTiltFiniteField : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : (Wq l a)⟦X⟧), ¬ (l : (Wq l a)⟦X⟧) ∣ g →
    ∃ (P : Polynomial (Wq l a)) (U : (Wq l a)⟦X⟧), IsUnit U ∧ P.Monic ∧
      (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) ∧ g = U * (P : (Wq l a)⟦X⟧) := by
  first | exact @GlobalTheory.weierstrass_prep_not_dvd_l | exact GlobalTheory.weierstrass_prep_not_dvd_l | (intros; apply GlobalTheory.weierstrass_prep_not_dvd_l <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfDetectingCoboundaryCharactersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wildJumpSum_le_of_detecting_coboundary_characters : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Detects p r A B → jumpSum (wild K L) A B ≤ 6 * E := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_le_of_detects | exact GlobalTheory.PMon.Ram.jumpSum_le_of_detects | (intros; apply GlobalTheory.PMon.Ram.jumpSum_le_of_detects <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTiltFrobeniusEqPowAddMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.FrobCong

theorem sigma_eq_pow_add (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (w : Wq l a) :
    ∃ x : Wq l a, sigma l a w = w ^ l + (l : Wq l a) * x := by
  have h0 : sigma l a w - w ^ l ∈ Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow]
    simp [WittVector.constantCoeff_apply, coeff_sigma]
  obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.1 h0
  exact ⟨x, by rw [mul_comm, hx]; ring⟩

end GlobalTheory.FrobCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZgFormula
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.ZgAll

theorem eq_top_of_closed {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G)
    (h₀ : lam g₀ = Multiplicative.ofAdd 1) (S : Subgroup G) (hS : IsClosed (S : Set G))
    (hker : ∀ h, lam h = 1 → h ∈ S) (hg₀ : g₀ ∈ S) (g : G) : g ∈ S := by
  have hc : IsClosed (lam '' (S : Set G)) := (hS.isCompact.image hlam).isClosed
  have hsub : Set.range (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) ⊆ lam '' (S : Set G) := by
    rintro _ ⟨n, rfl⟩
    refine ⟨g₀ ^ n, S.zpow_mem hg₀ n, ?_⟩
    rw [map_zpow, h₀, ← ofAdd_zsmul]
    simp
  have hd : DenseRange (fun n : ℤ => Multiplicative.ofAdd (n : ℤ_[l])) :=
    PadicInt.denseRange_intCast
  have hmem : lam g ∈ lam '' (S : Set G) := hc.closure_subset_iff.2 hsub (hd (lam g))
  obtain ⟨a, ha, hag⟩ := hmem
  have h1 : g * a⁻¹ ∈ S := hker _ (by rw [map_mul, map_inv, hag, mul_inv_cancel])
  simpa using S.mul_mem h1 ha

end GlobalTheory.NL.ZgAll

namespace GlobalTheory.NL.ZgAll

variable {l : ℕ} [Fact l.Prime] {G M : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
  [AddCommGroup M] [TopologicalSpace M] [T2Space M]

theorem coc_inv (a : G → M →+ M) (Z : G → M) (hZm : ∀ g h, Z (g * h) = Z g + a g (Z h))
    (h1 : Z 1 = 0) (g : G) : Z g⁻¹ = -a g⁻¹ (Z g) := by
  have := hZm g⁻¹ g
  rw [inv_mul_cancel, h1] at this
  exact eq_neg_of_add_eq_zero_left this.symm

theorem mem_and_comm (a : G → M →+ M)
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G) (h₀ : lam g₀ = Multiplicative.ofAdd 1)
    (J : AddSubgroup M) (hJ : IsClosed (J : Set M)) (hJa : ∀ g, ∀ x ∈ J, a g x ∈ J)
    (hJk : ∀ h, lam h = 1 → ∀ x ∈ J, a h x = x) (z : M) (hz : z ∈ J)
    (Z : G → M) (hZc : Continuous Z) (hZm : ∀ g h, Z (g * h) = Z g + a g (Z h))
    (hZk : ∀ h, lam h = 1 → Z h = 0) (hZ₀ : Z g₀ = z) :
    (∀ g, Z g ∈ J) ∧ ∀ g, a g₀ (Z g) - Z g = a g z - z := by
  have h1 : Z 1 = 0 := hZk 1 (map_one lam)
  let S : Subgroup G :=
    { carrier := {g | Z g ∈ J}
      one_mem' := by simp [h1]
      mul_mem' := by
        intro g h hg hh
        simp only [Set.mem_setOf_eq, hZm] at hg hh ⊢
        exact J.add_mem hg (hJa g _ hh)
      inv_mem' := by
        intro g hg
        simp only [Set.mem_setOf_eq, coc_inv a Z hZm h1] at hg ⊢
        exact J.neg_mem (hJa _ _ hg) }
  have hS : IsClosed (S : Set G) := hJ.preimage hZc
  have hall : ∀ g, Z g ∈ J := fun g =>
    eq_top_of_closed lam hlam g₀ h₀ S hS (fun h hh => by
      change Z h ∈ J
      rw [hZk h hh]; exact J.zero_mem) (by change Z g₀ ∈ J; rw [hZ₀]; exact hz) g
  refine ⟨hall, fun g => ?_⟩
  set k := g₀ * g * (g * g₀)⁻¹ with hk
  have hk1 : lam k = 1 := by
    simp only [hk, map_mul, map_inv]
    rw [mul_comm (lam g) (lam g₀), mul_inv_cancel]
  have e1 : g₀ * g = k * (g * g₀) := by rw [hk, inv_mul_cancel_right]
  have e2 : Z (g₀ * g) = Z (g * g₀) := by
    rw [e1, hZm, hZk k hk1, zero_add, hJk k hk1 _ (hall _)]
  rw [hZm, hZm, hZ₀] at e2
  rw [sub_eq_sub_iff_add_eq_add, add_comm (a g z), ← e2, add_comm]

theorem uniq (a : G → M →+ M)
    (lam : G →* Multiplicative ℤ_[l]) (hlam : Continuous lam) (g₀ : G) (h₀ : lam g₀ = Multiplicative.ofAdd 1)
    (Z Z' : G → M) (hZc : Continuous Z) (hZc' : Continuous Z')
    (hZm : ∀ g h, Z (g * h) = Z g + a g (Z h)) (hZm' : ∀ g h, Z' (g * h) = Z' g + a g (Z' h))
    (hZk : ∀ h, lam h = 1 → Z h = 0) (hZk' : ∀ h, lam h = 1 → Z' h = 0) (h₀' : Z g₀ = Z' g₀) (g : G) :
    Z g = Z' g := by
  have h1 : Z 1 = 0 := hZk 1 (map_one lam)
  have h1' : Z' 1 = 0 := hZk' 1 (map_one lam)
  let S : Subgroup G :=
    { carrier := {g | Z g = Z' g}
      one_mem' := by simp [h1, h1']
      mul_mem' := by
        intro g h hg hh
        simp only [Set.mem_setOf_eq, hZm, hZm'] at hg hh ⊢
        rw [hg, hh]
      inv_mem' := by
        intro g hg
        simp only [Set.mem_setOf_eq, coc_inv a Z hZm h1, coc_inv a Z' hZm' h1'] at hg ⊢
        rw [hg] }
  exact eq_top_of_closed lam hlam g₀ h₀ S (isClosed_eq hZc hZc')
    (fun h hh => by change Z h = Z' h; rw [hZk h hh, hZk' h hh]) h₀' g

end GlobalTheory.NL.ZgAll

namespace GlobalTheory.NL.ZgAll

set_option maxHeartbeats 8000000 in

theorem zg_formula_let : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (y z : W.DD T), z ∈ aN W T letπ → ∀ hyz : (y, z) ∈ W.divisibleCocycles T, ∃ zz : ↥W.GKs → W.DD T, (∀ g, zz g ∈ aN W T letπ) ∧ (∀ g, W.γ T (zz g) - zz g = W.γD T (W.resΓ g) z - z) ∧ ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = E.jD T y → ∃ c : ↥(latticeCocycles (resLat T W.GKs)), Submodule.Quotient.mk c = W.cl T ⟨(y, z), hyz⟩ ∧ ∀ g : ↥W.GKs, ∃ t : ↥T.L.T, (t : T.V) = (c : ↥W.GKs → T.V) g ∧ (1 : RW LL) ⊗ₜ[↥(OL LL)] t = E.jD T (zz g) - (TWact ((D.locA l).gRW LL ((g : ↥(GK K)) : GQ l)) T g b - b) := by
  intro D HW F l _ K s LL h W E T hT y z hz hyz
  have hc := GlobalTheory.HerrClassMaps.compact_GK K
  have H2 := GlobalTheory.HWL.Coord.exists_gamma_coordinates l (D.loc l) K s LL h (gamOf W ((HW l).W_s K s LL h))
  rcases H2 with ⟨⟨lam₀, hlc₀, hl1₀, hlg₀, ⟨g₁, hg₁⟩, hcl⟩, -⟩
  have hcs : CompactSpace ↥W.GKs := isCompact_iff_compactSpace.1 hcl.isCompact
  have hlamW : ∃ lam : ↥W.GKs →* Multiplicative ℤ_[l], Continuous lam ∧
      (∀ g : ↥W.GKs, lam g = 1 ↔ W.resΓ (g : ↥(GK K)) = 1) ∧
      (∀ g : ↥W.GKs, lam g = Multiplicative.ofAdd 1 ↔ W.resΓ (g : ↥(GK K)) = W.gam) ∧
      ∃ g : ↥W.GKs, lam g = Multiplicative.ofAdd 1 := ⟨lam₀, hlc₀, hl1₀, hlg₀, g₁, hg₁⟩
  rcases hlamW with ⟨lam, hlc, hl1, hlg, g₀, hg₀⟩
  have H1 := GlobalTheory.T.etaleComparison_pi_wachLattice_closed_weak D HW F l K s LL h T hT
  rcases H1 with ⟨τ, hT2, hTG, hact, hemb, hclo⟩

  let a : ↥W.GKs → TW (RW LL) T →+ TW (RW LL) T := fun g =>
    (TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K))).toAddMonoidHom
  have ha1 : ∀ g x, a g x = TWact ((D.locA l).gRW LL (((g : ↥(GK K))) : GQ l)) T (g : ↥(GK K)) x :=
    fun g x => rfl
  have hamul : ∀ g g' x, a (g * g') x = a g (a g' x) := by
    intro g g' x
    simp only [ha1]
    exact GlobalTheory.HerrClassMaps.TWact_mul _ _ _
      (fun r => GlobalTheory.HerrClassMaps.gRW_mul (D.locA l) LL _ _ r) T _ _ x
  have ha1t : ∀ g (t : ↥T.L.T), a g ((1 : RW LL) ⊗ₜ[↥(OL LL)] t) =
      (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨T.ρ (g : ↥(GK K)) t, T.L.stable _ t t.2⟩ : ↥T.L.T) := fun g t =>
    GlobalTheory.HerrClassMaps.TWact_one_tmul _ T _ t
  have haj : ∀ g (w : W.DD T), a g (E.jD T w) = E.jD T (W.γD T (W.resΓ (g : ↥(GK K))) w) := fun g w =>
    (E.jD_act T (g : ↥(GK K)) w).symm
  letI := τ
  have hl1' := hl1
  have hlg' := hlg
  have hstab : ∀ (γ' : W.Gam) (w : W.DD T), w ∈ aN W T letπ → W.γD T γ' w ∈ aN W T letπ := by
    intro γ' w hw
    obtain ⟨n, hn, rfl⟩ := hw
    have hx : (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • n ∈ W.N T := (W.N T).smul_mem _ hn
    obtain ⟨y', hy', e⟩ := W.N_π T γ' _ hx
    refine ⟨n + y', (W.N T).add_mem hn hy', ?_⟩
    change (letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • (n + y') =
      W.γD T γ' ((letπ : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) • n)
    rw [smul_add, ← e]
    abel
  let J : AddSubgroup (TW (RW LL) T) :=
    (aN W T letπ).toAddSubgroup.map (E.jD T).toAddMonoidHom
  have hJm : ∀ x, x ∈ J ↔ ∃ w ∈ aN W T letπ, E.jD T w = x := fun x => AddSubgroup.mem_map
  have hJ : IsClosed (J : Set (TW (RW LL) T)) := by
    have : (J : Set (TW (RW LL) T)) = E.jD T '' (aN W T letπ : Set (W.DD T)) := by
      ext x
      exact (hJm x).trans Iff.rfl
    rw [this]; exact hclo
  have hJa : ∀ g, ∀ x ∈ J, a g x ∈ J := by
    intro g x hx
    obtain ⟨w, hw, rfl⟩ := (hJm x).1 hx
    rw [haj]
    exact (hJm _).2 ⟨_, hstab _ w hw, rfl⟩
  have hJk : ∀ h' : ↥W.GKs, lam h' = 1 → ∀ x ∈ J, a h' x = x := by
    intro h' hh x hx
    obtain ⟨w, -, rfl⟩ := (hJm x).1 hx
    rw [haj, (hl1' h').1 hh, W.γD_one]
  haveI hCA : ContinuousAdd (TW (RW LL) T) := hTG.toContinuousAdd
  haveI hCN : ContinuousNeg (TW (RW LL) T) := hTG.toContinuousNeg
  haveI hCS : ContinuousSub (TW (RW LL) T) :=
    ⟨Continuous.congr (continuous_fst.add continuous_snd.neg) (fun p => (sub_eq_add_neg p.1 p.2).symm)⟩
  let Zf : TW (RW LL) T → ↥(latticeCocycles (resLat T W.GKs)) → ↥W.GKs → TW (RW LL) T := fun b c g =>
    (1 : RW LL) ⊗ₜ[↥(OL LL)] (⟨(c : ↥W.GKs → T.V) g, GlobalTheory.HerrClassMaps.mem_T c g⟩ : ↥T.L.T) + (a g b - b)
  have hZc : ∀ b c, Continuous (Zf b c) := fun b c =>
    (hemb.comp (c.2.1.1.subtype_mk fun g => GlobalTheory.HerrClassMaps.mem_T c g)).add
      (((hact b).comp continuous_subtype_val).sub continuous_const)
  have hZm : ∀ b c g g', Zf b c (g * g') = Zf b c g + a g (Zf b c g') := by
    intro b c g g'
    have e : (⟨(c : ↥W.GKs → T.V) (g * g'), GlobalTheory.HerrClassMaps.mem_T c (g * g')⟩ : ↥T.L.T) =
        ⟨(c : ↥W.GKs → T.V) g, GlobalTheory.HerrClassMaps.mem_T c g⟩ +
          ⟨T.ρ (g : ↥(GK K)) ((c : ↥W.GKs → T.V) g'), T.L.stable _ _ (GlobalTheory.HerrClassMaps.mem_T c g')⟩ :=
      Subtype.ext (c.2.1.2 g g')
    simp only [Zf, map_add, map_sub, ha1t, hamul, e, TensorProduct.tmul_add]
    abel
  have hfit : ∀ b, TWmap (φRW LL) T b - b = E.jD T y → ∃ c : ↥(latticeCocycles (resLat T W.GKs)),
      Submodule.Quotient.mk c = W.cl T ⟨(y, z), hyz⟩ ∧ (∀ h' : ↥W.GKs, lam h' = 1 → Zf b c h' = 0) ∧
        Zf b c g₀ = E.jD T z := by
    intro b hb
    have H := E.cl_def T ⟨(y, z), hyz⟩ b hb
    rcases H with ⟨c, hc1, hc2⟩
    refine ⟨c, hc1, fun h' hh => ?_, ?_⟩
    · have e := (hc2 h' ⟨_, GlobalTheory.HerrClassMaps.mem_T c h'⟩ rfl).1 ((hl1' h').1 hh)
      simp only [Zf]
      rw [e]
      exact neg_add_cancel _
    · have e := (hc2 g₀ ⟨_, GlobalTheory.HerrClassMaps.mem_T c g₀⟩ rfl).2 ((hlg' g₀).1 hg₀)
      simp only [Zf]
      simp only [e]
      exact sub_add_cancel _ _
  have hb₀ex := (GlobalTheory.WittTensorFixed.main l K LL T).1 (E.jD T y)
  rcases hb₀ex with ⟨b₀, hb₀⟩
  have H0 := hfit b₀ hb₀
  rcases H0 with ⟨c₀, -, hk₀, hg₀'⟩
  have hzJ : E.jD T z ∈ J := (hJm _).2 ⟨z, hz, rfl⟩
  have HM := mem_and_comm a lam hlc g₀ hg₀ J hJ hJa hJk _ hzJ (Zf b₀ c₀) (hZc b₀ c₀) (hZm b₀ c₀) hk₀ hg₀'
  rcases HM with ⟨hall, hcomm⟩
  choose zz hzz hzzj using fun g => (hJm _).1 (hall g)
  refine ⟨zz, hzz, fun g => ?_, fun b hb => ?_⟩
  · apply E.jD_inj T
    have h1 := hcomm g
    simp only [← hzzj g, haj, (hlg' g₀).1 hg₀] at h1
    simp only [map_sub, LocWach.γ]
    exact h1
  · have H := hfit b hb
    rcases H with ⟨c, hc1, hk, hgc⟩
    refine ⟨c, hc1, fun g => ⟨⟨_, GlobalTheory.HerrClassMaps.mem_T c g⟩, rfl, ?_⟩⟩
    have hu := uniq a lam hlc g₀ hg₀ (Zf b c) (Zf b₀ c₀) (hZc b c) (hZc b₀ c₀) (hZm b c) (hZm b₀ c₀) hk hk₀
      (hgc.trans hg₀'.symm) g
    simp only [hzzj g, ← hu]
    simp only [Zf]
    exact (add_sub_cancel_right _ _).symm

theorem zg_formula : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (y z : ((HW l).W K s LL h).DD T), z ∈ aN ((HW l).W K s LL h) T letπ → ∀ hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T, ∃ zz : ↥((HW l).W K s LL h).GKs → ((HW l).W K s LL h).DD T, (∀ g, zz g ∈ aN ((HW l).W K s LL h) T letπ) ∧ (∀ g, ((HW l).W K s LL h).γ T (zz g) - zz g = ((HW l).W K s LL h).γD T (((HW l).W K s LL h).resΓ g) z - z) ∧ ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = ((F l).E K s LL h).tie.jD T y → ∃ c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs)), Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧ ∀ g : ↥((HW l).W K s LL h).GKs, ∃ t : ↥T.L.T, (t : T.V) = (c : ↥((HW l).W K s LL h).GKs → T.V) g ∧ (1 : RW LL) ⊗ₜ[↥(OL LL)] t = ((F l).E K s LL h).tie.jD T (zz g) - (TWact ((D.locA l).gRW LL ((g : ↥(GK K)) : GQ l)) T g b - b) :=
  fun D HW F l _ K s LL h => zg_formula_let D HW F l K s LL h

end GlobalTheory.NL.ZgAll
end

