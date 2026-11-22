import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0702
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0825
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0823
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0827
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0826
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormValuesBoundedOnHolomorphicArcStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_values_bounded_on_holomorphicArc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ) (Uw : UnfWit (U σ)) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F) (th : a.D₀.P.L.Sec) (Θ : ThetaDat Ha th) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)), (∀ σ', Formalism.L2.PjFree.GoodEmb c σ' → Formalism.L2.PjFree.IsUnf (U σ')) → Formalism.L2.PjFree.GoodEmb c σ → (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i jj, z τ i jj ≠ 0 → (Uw.e jj).1 = τ) → ∀ (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), Dom a' n → F ∈ Formalism.L2.PjFree.cusp Xo c U a' n → ∃ T C : ℝ, ∀ w : ℂ, T < w.im → ∀ yw, AnFr Ha Θ z w yw → ‖Formalism.L2.PjFree.toC (evR Xo c F yw)‖ ≤ C := by
  first | exact @GlobalTheory.ArcBdd.cusp_values_bounded_on_arc | exact GlobalTheory.ArcBdd.cusp_values_bounded_on_arc | (intros; apply GlobalTheory.ArcBdd.cusp_values_bounded_on_arc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotentiallySemistable
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory

theorem deRham_potentiallySemistable : GlobalTheory.Published.DeRhamPotSemistable :=
  GlobalTheory.T.deRham_potSemistable_of_matrix_monodromy GlobalTheory.T.pAdicMonodromyTheorem_matrixForm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementLocalComponentsLevelNumber
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

namespace GlobalTheory.LevelFieldApprox

open Formalism.L2.Host

theorem val_eq_one_of_close {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} {y : E}
    (h : v.valuation E (y - 1) < 1) : v.valuation E y = 1 := by
  have e : y = (y - 1) + 1 := by ring
  rw [e, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])]
  exact map_one _

theorem locK_eq_one {E : Type} [Field E] [NumberField E] (χ : HChar E) (v : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (hn : χ.LevelLe v n) (y : Eˣ) (h : v.valuation E ((y : E) - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) :
    χ.locK v y = 1 ∧ v.valuation E (y : E) = 1 := by
  have hlt : v.valuation E ((y : E) - 1) < 1 :=
    lt_of_le_of_lt h (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hv := val_eq_one_of_close hlt
  have e1 : ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (y : E) := rfl
  have hval : ∀ x : E, Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  refine ⟨?_, hv⟩
  show χ.loc v (atFin v y) = 1
  refine hn _ ?_ ?_
  · show Valued.v ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1
    rw [e1, hval, hv]
  · rw [e1, ← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, hval]
    exact h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem exists_approx : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ : ℕ) (u : Eˣ), (u : E) = ((M₀ : ℕ) : E) → ∀ (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ a : Eˣ, IsIntegral ℤ (a : E) ∧ (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) ∧ ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1 := by
  intro E _ _ χ M₀ u hu T
  classical
  have hM0 : M₀ ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hu]; simp)
  have hM : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hM0
  have hMe : ((M₀ : ℕ) : E) ≠ 0 := by exact_mod_cast hM0
  have hfin : {v : HeightOneSpectrum (𝓞 E) | ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((M₀ : ℕ) : 𝓞 E)}) ?_).subset fun v hv => ?_
    · rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · exact Ideal.dvd_span_singleton.2 hv
  set S : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hfin.toFinset with hS
  choose n hn using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  have hm : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℕ, v.intValuation ((M₀ : ℕ) : 𝓞 E) = WithZero.exp (-(m : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg hM⟩
  choose m hm using hm
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => if v ∈ T then m v + n v + 1 else n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h'))
    (fun v => if (v : HeightOneSpectrum (𝓞 E)) ∈ T then ((M₀ : ℕ) : 𝓞 E) else 1)
  have hvz : ∀ v : HeightOneSpectrum (𝓞 E), ∀ z : 𝓞 E, v.valuation E (z : E) = v.intValuation z :=
    fun v z => HeightOneSpectrum.valuation_of_algebraMap (K := E) v z
  have hT : ∀ v ∈ T, v.valuation E ((y : E) - ((M₀ : ℕ) : E)) ≤ WithZero.exp (-((m v : ℤ) + n v + 1)) := by
    intro v hv
    have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v (Finset.mem_union_left _ hv))
    simp only [hv, if_true] at h1
    have e : (y : E) - ((M₀ : ℕ) : E) = ((y - ((M₀ : ℕ) : 𝓞 E) : 𝓞 E) : E) := by push_cast; rfl
    rw [e, hvz]
    convert h1 using 2
    push_cast; ring
  have hO : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T →
      v.valuation E ((y : E) - 1) ≤ WithZero.exp (-((n v : ℤ) + 1)) := by
    intro v hv hvT
    have h1 := (v.intValuation_le_pow_iff_mem _ _).2
      (hy v (Finset.mem_union_right _ (hfin.mem_toFinset.2 hv)))
    simp only [hvT, if_false] at h1
    have e : (y : E) - 1 = ((y - 1 : 𝓞 E) : E) := by push_cast; rfl
    rw [e, hvz]
    convert h1 using 2
    push_cast; ring
  have hMv : ∀ v, v.valuation E ((M₀ : ℕ) : E) = WithZero.exp (-(m v : ℤ)) := by
    intro v
    rw [← hm v, ← hvz]; simp
  have hTv : ∀ v ∈ T, v.valuation E (y : E) = v.valuation E ((M₀ : ℕ) : E) := by
    intro v hv
    have e : (y : E) = ((y : E) - ((M₀ : ℕ) : E)) + ((M₀ : ℕ) : E) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    rw [hMv]
    exact lt_of_le_of_lt (hT v hv) (WithZero.exp_lt_exp.mpr (by omega))
  have hOv : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → v.valuation E (y : E) = 1 :=
    fun v hv hvT => val_eq_one_of_close (lt_of_le_of_lt (hO v hv hvT)
      (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega))
  by_cases hy0 : (y : E) = 0
  · refine ⟨1, by simpa using isIntegral_one, fun v hv => ?_, fun v hv hvT => ?_⟩
    · exact absurd (hTv v hv) (by rw [hy0, map_zero, hMv]; exact (WithZero.exp_ne_zero).symm)
    · exact absurd (hOv v hv hvT) (by rw [hy0, map_zero]; exact zero_ne_one)
  set a : Eˣ := Units.mk0 (y : E) hy0 with ha
  refine ⟨a, y.isIntegral_coe, fun v hv => ?_, fun v hv hvT => ?_⟩
  · have hw := (locK_eq_one χ v (hn v) (a * u⁻¹) ?_).1
    · refine ⟨?_, hTv v hv⟩
      have : a = (a * u⁻¹) * u := by group
      rw [this, map_mul, hw, one_mul]
    · rw [Units.val_mul, Units.val_inv_eq_inv_val, hu, ha, Units.val_mk0]
      have e : (y : E) * ((M₀ : ℕ) : E)⁻¹ - 1 = ((y : E) - ((M₀ : ℕ) : E)) / ((M₀ : ℕ) : E) := by
        field_simp
      rw [e, map_div₀, hMv]
      calc _ ≤ WithZero.exp (-((m v : ℤ) + n v + 1)) / WithZero.exp (-(m v : ℤ)) :=
            div_le_div_of_nonneg_right (hT v hv) zero_le'
        _ = _ := by rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; ring
  · exact locK_eq_one χ v (hn v) a (by rw [ha, Units.val_mk0]; exact hO v hv hvT)

end GlobalTheory.LevelFieldApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSumSubsetAndConjugateFlip
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

namespace GlobalTheory.IdemFlip

theorem idemSum_sub_and_flip : ∀ (D : D7) (e : AE D) (P T : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → T ⊆ P →
    (∃ eT : AE D, IsIdemSum eT T) ∧ ∃ e' : AE D, IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) := by
  intro D e P T he hT
  have hnc := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he
  obtain ⟨⟨es, hes, hsum⟩, h0⟩ := he
  have hmul : ∀ S R : Finset (Formalism.L2.DIV.Pl D.host.E), S ⊆ R → R ⊆ P →
      (∑ a ∈ S, es a) * (∑ b ∈ R, es b) = ∑ a ∈ S, es a := by
    intro S R hSR hRP
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single a]
    · exact (hes a (hRP (hSR ha))).1.1
    · intro b hb hba
      exact Formalism.IndefR.Fin.idem_orth (hnc a (hRP (hSR ha)) a (hRP (hSR ha))) (hes a (hRP (hSR ha))) (hes b (hRP hb))
        (Ne.symm hba)
    · intro h; exact absurd (hSR ha) h
  have h1 : (∑ a ∈ T, es a) * e = ∑ a ∈ T, es a := by rw [hsum]; exact hmul T P hT subset_rfl
  have h2 : (∑ a ∈ T, es a) * (∑ a ∈ T, es a) = ∑ a ∈ T, es a := hmul T T subset_rfl hT
  have hTT : (∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a) = 0 := by
    calc (∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a)
        = ((∑ a ∈ T, es a) * e) * cA D ((∑ a ∈ T, es a) * e) := by rw [h1]
      _ = ((∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a)) * (e * cA D e) := by rw [map_mul]; ring
      _ = 0 := by rw [h0, mul_zero]
  have hIT : IsIdemSum (∑ a ∈ T, es a) T := ⟨⟨es, fun a ha => hes a (hT ha), rfl⟩, hTT⟩
  refine ⟨⟨_, hIT⟩, ?_⟩
  obtain ⟨⟨es2, hes2, hsum2⟩, -⟩ := Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hIT
  have hdisj : Disjoint (P \ T) (T.image Formalism.L2.DIV.conjPl) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha'
    exact hnc b (hT hb) _ (Finset.mem_sdiff.1 ha).1 (fun c hc => ⟨Formalism.L2.DIV.starO c,
      (Formalism.L2.DIV.isConjPl_conjPl b c _ (by rw [Formalism.L2.DIV.starO_coe])).1 hc, by rw [Formalism.L2.DIV.starO_coe]⟩)
  have hf : ∑ a ∈ P \ T, es a = e - ∑ a ∈ T, es a := by
    rw [eq_sub_iff_add_eq, Finset.sum_sdiff hT, hsum]
  refine ⟨(e - ∑ a ∈ T, es a) + cA D (∑ a ∈ T, es a),
    ⟨⟨fun a => if a ∈ P \ T then es a else es2 a, ?_, ?_⟩, ?_⟩⟩
  · intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · simp only [if_pos h]; exact hes a (Finset.mem_sdiff.1 h).1
    · simp only [if_neg (Finset.disjoint_right.1 hdisj h)]; exact hes2 a h
  · rw [Finset.sum_union hdisj, ← hf, hsum2]
    congr 1
    · exact Finset.sum_congr rfl fun a ha => (if_pos ha).symm
    · exact Finset.sum_congr rfl fun a ha => (if_neg (Finset.disjoint_right.1 hdisj ha)).symm
  · generalize (∑ a ∈ T, es a) = t at h1 h2 hTT ⊢
    have h4 : cA D t * cA D e = cA D t := by rw [← map_mul, h1]
    have h5 : cA D t * cA D t = cA D t := by rw [← map_mul, h2]
    rw [map_add, map_sub, Formalism.L2.Theta.cA_cA]
    linear_combination h0 - (-(e) * h4 + cA D t * h0) + h1 - (-(cA D e) * h1 + t * h0)
      + 2 * hTT - h2 + h4 - h5

end GlobalTheory.IdemFlip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsJointHarmonicOfLoweringStableSubmodule
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.LowerHarm

open MvPolynomial

theorem deg_pderiv_succ {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (k : ℕ) (h : f.totalDegree ≤ k + 1) :
    (pderiv i f).totalDegree ≤ k := by
  classical
  rw [f.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [pderiv_monomial]
  by_cases h0 : s i = 0
  · simp [h0]
  · refine (totalDegree_monomial_le _ _).trans ?_
    have e : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := by
      rw [tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      omega
    have e2 := congrArg Finsupp.degree e
    rw [map_add, Finsupp.degree_single] at e2
    have h3 := (le_totalDegree hs).trans h
    change s.degree ≤ k + 1 at h3
    change (s - Finsupp.single i 1).degree ≤ k
    omega

theorem pderiv_of_deg_zero {σ : Type} (i : σ) (f : MvPolynomial σ ℂ) (h : f.totalDegree ≤ 0) : pderiv i f = 0 := by
  rw [totalDegree_eq_zero_iff_eq_C.1 (Nat.le_zero.1 h), pderiv_C]

theorem fockT_lower {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P = - ∑ j : Fin n, pderiv (τ, i, j) (pderiv (τ, l, j) P) := by
  classical
  have hil : i ≠ l := by intro h; subst h; omega
  have h1 : decide ((i : ℕ) < p τ) = false := decide_eq_false (by omega)
  have h2 : decide ((l : ℕ) < p τ) = true := decide_eq_true hl
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT
  rw [Finset.sum_eq_single i, Finset.sum_eq_single l]
  · simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.raiO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.lowO, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn, h1, h2, hil, LinearMap.sum_apply]
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp
  · intro k _ hk; simp [Matrix.single_apply, Ne.symm hk]
  · simp

theorem lower_deg {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) (k : ℕ) (h : P.totalDegree ≤ k + 2) :
    (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P).totalDegree ≤ k := by
  rw [fockT_lower τ p i l hi hl, totalDegree_neg]
  exact totalDegree_finsetSum_le fun j _ => deg_pderiv_succ _ _ _ (deg_pderiv_succ _ _ (k + 1) h)

theorem lower_zero {D : D7} {n m : ℕ} (τ : D.what₂.Tau) (p : D.what₂.Tau → ℕ) (i l : Fin m)
    (hi : p τ ≤ (i : ℕ)) (hl : (l : ℕ) < p τ) (P : PolF D m n) (h : P.totalDegree ≤ 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) P = 0 := by
  rw [fockT_lower τ p i l hi hl]
  simp [pderiv_of_deg_zero _ _ (deg_pderiv_succ _ _ 0 h)]

theorem lower_to_harmonic : ∀ (D : D7) (n m : ℕ) (p : D.what₂.Tau → ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (M : Submodule ℂ (W →ₗ[ℂ] PolF D m n)), (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (i l : Fin m), p τ ≤ (i : ℕ) → (l : ℕ) < p τ → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ M) → M ≠ ⊥ → ∃ ψ ∈ M, ψ ≠ 0 ∧ ∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), p τ' ≤ (i : ℕ) → (l : ℕ) < p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ')) (Matrix.single i l (1 : ℂ)) (ψ w') = 0 := by
  intro D n m p W _ _ _ M hM hne
  classical
  have hex : ∃ d, ∃ ψ ∈ M, ψ ≠ 0 ∧ ∀ w, (ψ w).totalDegree ≤ d := by
    obtain ⟨ψ, hψ, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    let b := Module.finBasis ℂ W
    refine ⟨Finset.univ.sup fun j => (ψ (b j)).totalDegree, ψ, hψ, hψ0, fun w => ?_⟩
    rw [← b.sum_repr w, map_sum]
    refine totalDegree_finsetSum_le fun j _ => ?_
    rw [map_smul]
    exact (totalDegree_smul_le _ _).trans
      (Finset.le_sup (f := fun j => (ψ (b j)).totalDegree) (Finset.mem_univ j))
  obtain ⟨ψ, hψ, hψ0, hdeg⟩ := Nat.find_spec hex
  refine ⟨ψ, hψ, hψ0, fun w τ i l hi hl => ?_⟩
  by_contra hne'
  have hL := hM ψ hψ τ i l hi hl
  have hL0 : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < p τ))
      (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ≠ 0 := fun h => hne' (by simpa using LinearMap.congr_fun h w)
  rcases Nat.lt_or_ge (Nat.find hex) 2 with h2 | h2
  · exact hne' (lower_zero τ p i l hi hl _ (by have := hdeg w; omega))
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 2 := ⟨Nat.find hex - 2, by omega⟩
    have := Nat.find_min' hex ⟨_, hL, hL0, fun w' => lower_deg τ p i l hi hl _ k (hk ▸ hdeg w')⟩
    omega

end GlobalTheory.LowerHarm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStandardFrameKeepsMatricesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standard_frameKeepsMatrices : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (j : Fin D.R.m), FWT.VStd D j → ∃ P : principalLevelFrame.RowPsi (Vc D j) D.R.nV, IdFrame hF P ∧ GlobalTheory.Mem.R3.StdFrame hF P := by
  first | exact @GlobalTheory.MtRead.IdFrameStd.exists_idFrame | exact GlobalTheory.MtRead.IdFrameStd.exists_idFrame | (intros; apply GlobalTheory.MtRead.IdFrameStd.exists_idFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsToricCharactersInTwistCoefficientRings
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LamInstall
open ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NT Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.LamTie GlobalTheory.LamTie.TrueList

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_reading {D : D7} {N : NData D.R D.host D.what₂} (T : TwR D.LL0 N) (i : T.Tw) :
    ∃ (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ),
      (∀ z : ℤ_[T.l i], κ (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
        algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i])) ∧
      ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL) := by
  haveI : CharZero (FractionRing (T.O0 i)) := (T.emb0 i).charZero_iff (T.emb0 i).injective |>.1 inferInstance
  let f : ℤ_[T.l i] →+* FractionRing (T.O0 i) :=
    (algebraMap (T.O0 i) (FractionRing (T.O0 i))).comp (algebraMap ℤ_[T.l i] (T.O0 i))
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hz
    rcases mul_eq_zero.1 hz with h | h
    · exact ((PadicInt.unitCoeff h0).isUnit.map f).ne_zero h
    · exact (pow_ne_zero _ (Nat.cast_ne_zero.2 (T.lPrime i).out.ne_zero)) h
  have hf0 : Function.Injective (algebraMap ℤ_[T.l i] (T.O0 i)) :=
    Function.Injective.of_comp (f := algebraMap (T.O0 i) (FractionRing (T.O0 i))) hf
  haveI : Module.IsTorsionFree ℤ_[T.l i] (T.O0 i) := Module.isTorsionFree_iff_algebraMap_injective.2 hf0
  haveI : Module.IsTorsionFree ℤ_[T.l i] (Qbar (T.l i)) := Module.isTorsionFree_iff_algebraMap_injective.2
    (by rw [IsScalarTower.algebraMap_eq ℤ_[T.l i] ℚ_[T.l i] (Qbar (T.l i))]
        exact (algebraMap ℚ_[T.l i] (Qbar (T.l i))).injective.comp Subtype.val_injective)
  let g : T.O0 i →ₐ[ℤ_[T.l i]] Qbar (T.l i) := IsAlgClosed.lift
  have hg : Function.Injective g := by
    refine (RingHom.injective_iff_ker_eq_bot g.toRingHom).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[T.l i]) ?_)
    rw [eq_bot_iff]
    intro z hz
    have h1 : algebraMap ℤ_[T.l i] (Qbar (T.l i)) z = 0 := (g.commutes z).symm.trans hz
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).1 h1
  haveI : Countable ↥D.LL0 := (Module.finBasis ℚ ↥D.LL0).equivFun.injective.countable
  let κ : FractionRing (T.O0 i) →+* Qbar (T.l i) := IsFractionRing.lift (g := g.toRingHom) hg
  obtain ⟨ι, hι⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable (T.l i) ↥D.LL0
    (κ.comp (T.emb0 i)) (embLL0 D)
  exact ⟨κ, ι, fun z => (IsFractionRing.lift_algebraMap hg _).trans (g.commutes z), hι⟩

theorem delta_isGal (hC : GlobalTheory.Published.ChebotarevDegreeOne) {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)}
    {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}
    (ha : IsGlobalArtin art) (i : T.Tw) (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ)
    (hι : ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) :
    IsGal art κ ι (cf.delAt (T.l i)) 0 (T.delta i) := GlobalTheory.T.twist_character_is_ladic_of_finite_order_hecke hC Sp ha i κ ι hι

theorem read_of_isGal {D : D7} {N : NData D.R D.host D.what₂} {T : TwR D.LL0 N} {art : Ideles D.host.E →* Gab D.host.E N.Om}
    (ha : IsGlobalArtin art) {i : T.Tw} (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ)
    (hι : ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (b : Bool) (embO : ↥D.LL0 →+* FractionRing (T.O i))
    (hO : ∀ (x : ↥D.LL0) (y : T.O0 i), algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = (if b then T.emb0 i else T.emb0b i) x →
      embO x = algebraMap (T.O i) (FractionRing (T.O i)) (algebraMap (T.O0 i) (T.O i) y))
    (χ : HChar D.host.E) (hu : χ.IsUnitary) (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hv : ∀ P ∉ S, χ.UnrAt P ∧ ∃ y : ↥D.LL0, embLL0 D y = ((χ.val P : ℂˣ) : ℂ))
    (H : NC.HC D.host.E) (hH : ∀ x, H.χ x = χ.1 x) {n : (D.host.E →+* ℂ) → ℤ} {r : G D.host.E N.Om →* (T.O0 i)ˣ}
    (hr : IsGal art κ (sideIso ι b) χ n r) :
    NC.Read N.plOm.1 ((Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) (algebraMap (T.O i) (FractionRing (T.O i)))
      embO (NC.complexEmbeddingRestrictedToSubfield D) H 0 := GlobalTheory.T.twistCharacter_eq_galois_of_ladic_unitaryHecke ha κ ι hι b embO hO χ hu S hv H hH hr

set_option maxHeartbeats 4000000 in

theorem exists_twL_installed : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.ToricRational.RatioConj → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (Z : GlobalTheory.LamTie.LamDat D), Z.C = cf → Z.Ok → (∀ a, GlobalTheory.LamTie.TeichTriv D.host (Z.chi a)) → ValLL0 D cf → (∀ a, (Z.chi a).ValuesIn 0 (embLL0 D)) → (∀ i P, (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → P ∈ T.S0 i) → ∃ L : TwL T, ∀ F : TwF T, GlobalTheory.LamTie.IsLamTieFull (T.ntw hE F L) Z ∧ ∀ (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))) (h0 : _) th, Nonempty (SideB (⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) → ∀ th', Nonempty (SideB (⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) := by
  intro hC hA hR D hE cf Rw low Pq S hL eig θ b0 b1 Sx T Sp Z hZC hZ hT hV hχv hS
  subst hZC
  obtain ⟨art, ha⟩ := hA D.host.E D.nd.Om
  choose κ ι hκ hι using fun i => exists_reading T i
  have hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)) := fun i j v hv' => by
    obtain ⟨y, hy⟩ := hV.mu0 j v hv'
    exact ⟨T.emb0 i y, by rw [← hy]; exact hι i y⟩
  have hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)) := fun i a v hv' => by
    obtain ⟨y, hy⟩ := hχv a v hv'
    exact ⟨T.emb0 i y, by rw [← hy]; exact hι i y⟩
  have hδ := fun i => delta_isGal hC Sp ha i (κ i) (ι i) (hι i)
  obtain ⟨L, e, hcl, hfull⟩ := exists_twL_full_teich hA hR D D.nd hE T Z hZ art ha κ ι hκ hι hμ hχ hδ hS hT
  refine ⟨L, fun F => ⟨hfull F, fun ex h0 th hB th' => ?_⟩⟩
  obtain ⟨B⟩ := hB
  refine sideB_keep B (fun s lam => FitTw.toHC (Z.chi (e s lam).2.1)) ?_ ?_
  · intro i lam P _
    obtain ⟨-, -, h2, -, h4⟩ := hcl i lam
    rw [h4 P, h2]
    let f : FractionRing (T.O i) →+* ℂ := B.twF.iCq i
    show f (((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) = _
    rw [map_zpow₀, map_natCast]
    have e2 : (-(((2 * ((e i lam).2.2.1.1 : ℤ) : ℤ) : ℝ)) / 2) = ((-((e i lam).2.2.1.1 : ℤ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [e2, Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_natCast]
  · intro s lam
    obtain ⟨h1, h2, -, ⟨n, r, hr, hG⟩, -⟩ := hcl s lam
    let C : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j) :=
      ⟨Z.C.P, Z.C.W, Z.C.mu0, Z.C.eta, Z.C.chiPsi, Z.C.del, Z.C.del', Z.C.isMu0, Z.C.isEta, Z.C.isChi, Z.C.isDel, Z.C.isDel'⟩
    have hpD : ∀ v, v ∈ T.pD s ↔ OverP D.host (if T.l s = D.host.pde then D.host.pde' else D.host.pde) v := fun v => by
      rw [← Finset.mem_coe, T.pD_eq]; rfl
    have hmu : ∀ P, P ∉ T.S0 s → (Z.C.mu0 (e s lam).1).UnrAt P := fun P hP =>
      (Z.C.isMu0 _).unr P fun k hk => hP (T.placesOver_subset_exceptional s k hk)
    have hde : ∀ P, P ∉ T.S0 s → (Z.C.delAt (T.l s)).UnrAt P := fun P hP =>
      (inertialOrderFifteenChar_auxiliaryPrime_spec C (l := T.l s)).2.2.2.2.unr P fun hk => hP (T.primes_subset_exceptional s ((hpD P).2 hk))
    have hcu : ∀ P, P ∉ T.S0 s → (Z.chi (e s lam).2.1).UnrAt P := fun P hP =>
      chi_unr hZ _ fun h => hP (hS s P h)
    have hdel : (Z.C.delAt (T.l s)).ValuesIn 0 (embLL0 D) := by
      unfold CharFrame.delAt
      split_ifs
      exacts [hV.del', hV.del]
    rw [hG, h2]
    refine read_of_isGal ha (κ s) (ι s) (hι s) _ _ (fun x y h => B.chi.ringSpec_sidedEmbedding_fixedField s _ x y h)
      (Z.lam0 (T.l s) (e s lam).1 (e s lam).2.1) ?_ (T.S0 s) ?_ _ ?_ hr
    · intro x
      have e1 := (Z.C.isMu0 (e s lam).1).unitary x
      have e2 := Z.C.delAt_unitary (T.l s) x
      have e3 := (hZ.aux (e s lam).2.1).unitary x
      show ‖(((Z.C.mu0 (e s lam).1).1 x * (Z.C.delAt (T.l s)).1 x * ((Z.chi (e s lam).2.1).1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
      rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_mul, norm_inv, e1, e2, e3]
      norm_num
    · intro P hP
      refine ⟨((hmu P hP).mul (hde P hP)).mul (hcu P hP).inv, ?_⟩
      obtain ⟨y1, hy1⟩ := hV.mu0 (e s lam).1 P (hmu P hP)
      obtain ⟨y2, hy2⟩ := hdel P (hde P hP)
      obtain ⟨y3, hy3⟩ := hχv (e s lam).2.1 P (hcu P hP)
      simp only [HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one] at hy1 hy2 hy3
      refine ⟨y1 * y2 * y3⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv₀, hy1, hy2, hy3, LamDat.lam0, HChar.val_mul, HChar.val_mul, HChar.val_inv,
        Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    · intro x
      rw [h1]
      have e1 : (B.chiD.mu0 ((e s lam).1.1 + 1)).χ x = (Z.C.mu0 (e s lam).1).1 x := B.ringSpec_normalisedCharacter_eq _ x
      have e2 : (B.chiD.del s).χ x = (Z.C.delAt (T.l s)).1 x := B.del_eq s x
      show (B.chiD.mu0 ((e s lam).1.1 + 1)).χ x * (B.chiD.del s).χ x * ((Z.chi (e s lam).2.1).1 x)⁻¹ = _
      rw [e1, e2]
      rfl

end GlobalTheory.LamInstall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenIntegralityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_integrality : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ big₀ L₀, Built A M C tp.tup big₀ L₀ → ∃ big₁, ∀ L₁, Built A M C tp.tup big₁ L₁ → ∀ i₁, ∃ i₀, ExtOf L₀ L₁ i₀ i₁ := by
  first | exact @GlobalTheory.CoefDuty.ExtBuilt.extOf_built | exact GlobalTheory.CoefDuty.ExtBuilt.extOf_built | (intros; apply GlobalTheory.CoefDuty.ExtBuilt.extOf_built <;> assumption)
end

