import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0858
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0767
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0884
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0876
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0791
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0882
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0873
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0870
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicIwasawaDecompositionOffFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0949

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.GenFinite

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem downInt_transl (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g g' : GA D (Wc D i)) :
    downInt R i t y (R.ωP i t (1, g') f) l g = downInt R i t y f l (g * g') := by
  have e : ∀ h : GA D (Vc D i), thetaKO (R.ωP i t) h g (R.ωP i t (1, g') f) = thetaKO (R.ωP i t) h (g * g') f := by
    intro h
    have hm : ((h, g) : GA D (Vc D i) × GA D (Wc D i)) * (1, g') = (h, g * g') := by
      rw [Prod.mk_mul_mk, mul_one]
    show R.ωP i t (h, g) (R.ωP i t (1, g') f) 0 = R.ωP i t (h, g * g') f 0
    rw [← hm, map_mul, Module.End.mul_apply]
  simp only [downInt, e]

theorem downInt_add (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f f' : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i))
    (hf : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)) (R.fdV i t) (R.νV i t))
    (hf' : IntegrableOn (fun h => thetaKO (R.ωP i t) h g f' * l (R.extV i t y h)) (R.fdV i t) (R.νV i t)) :
    downInt R i t y (f + f') l g = downInt R i t y f l g + downInt R i t y f' l g := by
  unfold downInt
  rw [← integral_add hf hf']
  congr 1
  funext h
  simp only [thetaKO, map_add, Pi.add_apply, add_mul]

theorem downInt_smul (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (c : ℂ) (f : WO (Vc D i) (Wc D i) → ℂ)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) :
    downInt R i t y (c • f) l g = c * downInt R i t y f l g := by
  unfold downInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.DownLift.GenFinite

namespace GlobalTheory.DownLift.GenFinite

theorem genFin : GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GenFin R i t := by
  intro hH D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hNC hvan
  rintro ⟨f, l, g, hf, hne⟩
  apply hne
  have hθ : ∀ (p : GA D (Vc D i) × GA D (Wc D i)) (φ : WO (Vc D i) (Wc D i) → ℂ),
      IsThetaFunO R.ψ (Vc D i) (Wc D i) φ → IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.ωP i t p φ) :=
    fun p φ hφ => (hP i t).datum.om_pres p φ hφ
  let Pr : (WO (Vc D i) (Wc D i) → ℂ) → Prop := fun φ =>
    IsThetaFunO R.ψ (Vc D i) (Wc D i) φ ∧ ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y φ l g = 0
  have hint := GlobalTheory.T.integrableOn_downwardThetaLift_integrand D G Pl0 T A Ks R F hG hP i t y
  have hadd : ∀ φ φ', Pr φ → Pr φ' → Pr (φ + φ') := by
    intro φ φ' h1 h2
    refine ⟨theta_add h1.1 h2.1, fun l g => ?_⟩
    rw [downInt_add R i t y φ φ' l g (hint φ l g h1.1) (hint φ' l g h2.1), h1.2 l g, h2.2 l g, add_zero]
  have hsmul : ∀ (c : ℂ) φ, Pr φ → Pr (c • φ) := by
    intro c φ h1
    exact ⟨theta_smul c h1.1, fun l g => by rw [downInt_smul, h1.2 l g, mul_zero]⟩
  have hzero : Pr 0 :=
    ⟨by simpa using theta_smul (0 : ℂ) hf,
      fun l g => by simpa using downInt_smul R i t y 0 f l g⟩
  have hspan : ∀ s : Set (WO (Vc D i) (Wc D i) → ℂ), (∀ φ ∈ s, Pr φ) → ∀ φ ∈ Submodule.span ℂ s, Pr φ := by
    intro s hs φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hs x hx
    | zero => exact hzero
    | add x y' _ _ hx hy => exact hadd x y' hx hy
    | smul c x _ hx => exact hsmul c x hx
  have hGen : ∀ φ ∈ Gen R i t, Pr φ := by
    rintro φ ⟨g', f', hf', rfl⟩
    exact ⟨hθ _ _ hf'.1, fun l g => by rw [downInt_transl]; exact hvan f' hf' l (g * g')⟩
  have hAvg : ∀ φ ∈ AvgIm R i t, Pr φ := by
    rintro φ ⟨PP, a, ha, tr, ε, hε, κ, hκ, f', hf', rfl⟩
    refine ⟨?_, fun l g => GlobalTheory.T.level_averages_theta_pair_zero_without_character D G Pl0 T A Ks R F hG hP i t y hNC PP a ha tr ε hε κ hκ f' hf' l g⟩
    unfold avgW
    exact theta_sum _ _ f' hf' fun k _ => theta_smul _ (hθ _ _ hf')
  have hType : ∀ φ, TypeVec R i t φ → Pr φ := by
    intro φ hφ
    refine hspan _ ?_ φ (GlobalTheory.T.thetaFunction_levelType_mem_span_averages D G Pl0 T A Ks R F hG hP i t φ hφ)
    rintro x (hx | hx)
    · exact hspan _ hGen x (GlobalTheory.T.thetaFunction_levelType_mem_span_translates hH D G Pl0 T A Ks R F hG hP i t x hx.1 hx.2)
    · exact hAvg x hx
  have hDiff : ∀ φ ∈ TypeDiff R i t, Pr φ := by
    rintro φ ⟨κ, hκ, f', hf', rfl⟩
    refine ⟨theta_sub (hθ _ _ hf') (theta_smul _ hf'), fun l g => ?_⟩
    have e : R.ωP i t (κ, 1) f' - (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • f' =
        R.ωP i t (κ, 1) f' + (-(levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹) • f' := by
      rw [neg_smul, sub_eq_add_neg]
    rw [e, downInt_add R i t y _ _ l g (hint _ l g (hθ _ _ hf'))
      (hint _ l g (theta_smul _ hf')), downInt_smul,
      GlobalTheory.T.downwardLift_level_acts_by_inverse_character D G Pl0 T A Ks R F hG hP i t y f' hf' κ hκ l g]
    ring
  refine (hspan _ ?_ f (GlobalTheory.T.thetaFunction_mem_span_levelType_differences D G Pl0 T A Ks R F hG hP i t f hf)).2 l g
  rintro x (hx | hx)
  · exact hType x hx
  · exact hDiff x hx

end GlobalTheory.DownLift.GenFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumSchurSquareCellProductEqEulerProductStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tsum_schurSquareCellProduct_eq_eulerProduct : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ) (l₀ : GlobalTheory.CellDec.abelian₂ E n T),
    ∑' l : GlobalTheory.CellDec.abelian₂ E n T, GlobalTheory.RSCell.cellProd T α x (l.1 - l₀.1) =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) α x := by
  first | exact @GlobalTheory.RSCellSum.tsum_cellProd_sub_eq_eulD | exact GlobalTheory.RSCellSum.tsum_cellProd_sub_eq_eulD | (intros; apply GlobalTheory.RSCellSum.tsum_cellProd_sub_eq_eulD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBounded
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

open GlobalTheory.RSJ

namespace GlobalTheory.ZEulProps

theorem norm_prod_le (W W' c₁ c₂ c₃ : ℂ) :
    ‖W * conj W' * c₁ * c₂ * c₃‖ ≤ (‖W * conj W * c₁ * c₂ * c₃‖ + ‖W' * conj W' * c₁ * c₂ * c₃‖) / 2 := by
  simp only [norm_mul, Complex.norm_conj]
  have hK : 0 ≤ ‖c₁‖ * ‖c₂‖ * ‖c₃‖ := by positivity
  nlinarith [mul_nonneg (sq_nonneg (‖W‖ - ‖W'‖)) hK]

theorem psiN_mul_conj {E : Type} [Field E] [NumberField E] {a : ℕ} (u : GA E a) :
    GlobalTheory.JSW.psiN u * conj (GlobalTheory.JSW.psiN u) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [GlobalTheory.JSW.psiN, Circle.norm_coe]

theorem lastRow_unip {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ} {u : GA E (m + 1)}
    (hu : u ∈ GlobalTheory.CellDec.NA E (m + 1)) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (u * g) = GlobalTheory.ZEul.lastRow g := by
  have h := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  refine GlobalTheory.ZUnf.lastRow_mul_of_row fun l => ?_
  by_cases hl : l = Fin.last m
  · subst hl; rw [h.2, Matrix.one_apply_eq]
  · have hlt : l < Fin.last m := lt_of_le_of_ne (Fin.le_last l) hl
    rw [h.1 _ _ hlt, Matrix.one_apply_ne (Ne.symm hl)]

theorem detPow_unip {E : Type} [Field E] [NumberField E] {a : ℕ} {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) (x : ℝ) :
    GlobalTheory.RSJ.detPow E a x u = 1 := by
  have hd : Matrix.GeneralLinearGroup.det u = 1 := Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu)
  unfold GlobalTheory.RSJ.detPow chiDet
  rw [MonoidHom.comp_apply, hd, map_one]
  simp

end GlobalTheory.ZEulProps

theorem GlobalTheory.ZEulProps.uInt_props : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (φ φ' : GA E (m + 1) → ℂ)
    (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous Φ → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    Measurable (GlobalTheory.ZEul.uInt φ φ' Φ N x) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, GlobalTheory.ZEul.uInt φ φ' Φ N x (u * g) = GlobalTheory.ZEul.uInt φ φ' Φ N x g) ∧
    ∀ g, ‖GlobalTheory.ZEul.uInt φ φ' Φ N x g‖ ≤ (‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ + ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖) / 2 := by
  intro E _ _ _ m φ φ' Φ N x hW hW' hl hl' hΦ _
  refine ⟨?_, fun u hu g => ?_, fun g => ?_⟩
  · exact GlobalTheory.ZUnfTheta.measurable_integrand hW.measurable hW'.measurable hΦ N x
  · have hu' : u ∈ GlobalTheory.JSW.NA E (m + 1) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    unfold GlobalTheory.ZEul.uInt
    rw [GlobalTheory.ZEulProps.lastRow_unip hu g, mul_assoc u g, hl u hu', hl' u hu', GlobalTheory.RSJ.Model.detPow_mul,
      GlobalTheory.ZEulProps.detPow_unip hu x, one_mul, map_mul]
    have h1 := GlobalTheory.ZEulProps.psiN_mul_conj u
    linear_combination (GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) *
      conj (GlobalTheory.JSW.whit φ' (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))) *
      Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) *
      (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ)) * h1
  · unfold GlobalTheory.ZEul.uInt
    exact GlobalTheory.ZEulProps.norm_prod_le _ _ _ _ _
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandContinuousInvarianStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedRankinSelbergIntegrand_continuous_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a), (ℓ : ℕ) + 1 = a →
    ∀ (F : GA E a → ℂ) (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E),
    Continuous (GlobalTheory.JSW.whit F) → (∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, ‖GlobalTheory.JSW.whit F (u * g)‖ = ‖GlobalTheory.JSW.whit F g‖) →
    Continuous Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    Continuous (fun p : ℝ × GA E a => GlobalTheory.RSCell.bInt ℓ F Φ J η p.1 p.2) ∧
      (∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E a, ∀ g, GlobalTheory.RSCell.bInt ℓ F Φ J η x (u * g) = GlobalTheory.RSCell.bInt ℓ F Φ J η x g) ∧
      ∀ x g, GlobalTheory.RSCell.bInt ℓ F Φ J η x g ≠ ⊤ := by
  first | exact @GlobalTheory.RSCellB.bInt_continuous_invariant_finite | exact GlobalTheory.RSCellB.bInt_continuous_invariant_finite | (intros; apply GlobalTheory.RSCellB.bInt_continuous_invariant_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergIntegrandNeZeroIdentityStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedRankinSelbergIntegrand_ne_zero_identity : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (F : GA E (m + 1) → ℂ) (Φ : (Fin (m + 1) → Cinf E) → ℂ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (l₀ : GlobalTheory.CellDec.abelian₂ E (m + 1) T), (∀ w, l₀.1 w (Fin.last m) = 0) →
    GlobalTheory.JSW.whit F (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 → Φ (Pi.single (Fin.last m) 1) ≠ 0 → ∀ x : ℝ, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1) ≠ 0 := by
  first | exact @GlobalTheory.RSCell.bInt_tl_last_ne_zero | exact GlobalTheory.RSCell.bInt_tl_last_ne_zero | (intros; apply GlobalTheory.RSCell.bInt_tl_last_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitone
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellVanish

theorem eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (w : HeightOneSpectrum (𝓞 E)), w ∉ S →
    (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ), IsUnifV E w (ϖ w : w.adicCompletion E) →
    ∀ (W : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, W (g * finGL E (m + 1) κ) = W g) →
    ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ)), ¬ Antitone (l w) →
    ∀ p : GA E (m + 1), Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1 →
    W (p * GlobalTheory.CellDec.tl (m + 1) ϖ l) = 0 := by
  intro E _ _ _ m S J w hwS hψ ϖ hϖ W hWN hWK l hl p hp
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l with ht
  set D : GL (Fin (m + 1)) (w.adicCompletion E) := GlobalTheory.CellDec.compV E (m + 1) w t with hD
  have hDv : (D : Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) =
      Matrix.diagonal fun a => ((ϖ w ^ l w a : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
    rw [hD, ht, GlobalTheory.CellDec.tl, GlobalTheory.CellDec.compV_finGL]
    refine Matrix.ext fun i j => ?_
    change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin (m + 1)) _ : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) i j) = _
    rw [GlobalTheory.SmGL.val_diagT]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin (m + 1) → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      simp
    · simp [Matrix.diagonal_apply_ne _ hij]
  set t' := t * (finGL E (m + 1) (locGL E (m + 1) w D))⁻¹ with ht'
  have ht'w : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t' = 1 := by
    change GlobalTheory.CellDec.compV E (m + 1) w t' = 1
    rw [ht', map_mul, map_inv, GlobalTheory.CellDec.compV_finGL_locGL_same, ← hD, mul_inv_cancel]
  have htt : t' * finGL E (m + 1) (locGL E (m + 1) w D) = t := by rw [ht', inv_mul_cancel_right]
  have hlev : ∀ k ∈ GlobalTheory.LFun.KGL w (m + 1), locGL E (m + 1) w k ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J := by
    intro k hk
    refine ⟨fun v => ?_, fun v hv i j => ?_⟩
    · by_cases hvw : v = w
      · subst hvw; rw [pLoc_locGL]; exact hk
      · rw [pLoc_locGL_of_ne hvw]; exact one_mem _
    · have hvw : v ≠ w := fun h => hwS (h ▸ hv)
      have h1 := congrArg (fun x : GL (Fin (m + 1)) (v.adicCompletion E) => (x : Matrix (Fin (m + 1)) (Fin (m + 1)) (v.adicCompletion E)) i j)
        (pLoc_locGL_of_ne hvw k)
      have h0 : ((locGL E (m + 1) w k).val - 1) i j v = 0 := by
        change pLoc E v (((locGL E (m + 1) w k).val - 1) i j) = 0
        rw [Matrix.sub_apply, map_sub]
        change (Matrix.GeneralLinearGroup.map (pLoc E v) (locGL E (m + 1) w k)).val i j - _ = 0
        rw [h1]
        simp [Matrix.one_apply]
      rw [h0, map_zero]
      exact zero_le'
  let f : GL (Fin (m + 1)) (w.adicCompletion E) → ℂ := fun g => W (p * t' * finGL E (m + 1) (locGL E (m + 1) w g))
  have hfD : f D = W (p * t) := by
    simp only [f]
    rw [mul_assoc, htt]
  have hpt : Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (p * t') = 1 := by
    rw [map_mul, hp, ht'w, mul_one]
  have hfN : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ g,
      f (u * g) = GlobalTheory.JSW.psiLocChar w (GlobalTheory.Whittaker.superDiag u) * f g := by
    intro u hu g
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc (p * t'), GlobalTheory.JSW.commute_finGL_locGL w hpt, mul_assoc,
      hWN _ (GlobalTheory.JSW.CutTransfer.finGL_locGL_mem_NA' w hu), GlobalTheory.JSW.CutTransfer.psiN_finGL_locGL]
    rfl
  have hfK : ∀ g, ∀ k ∈ GlobalTheory.LFun.KGL w (m + 1), f (g * k) = f g := by
    intro g k hk
    simp only [f]
    rw [map_mul, map_mul, ← mul_assoc]
    exact hWK _ (hlev k hk) _
  have h := GlobalTheory.WhitTorus.eq_zero_of_not_antitone_int E w (m + 1) (GlobalTheory.JSW.psiLocChar w) hψ f hfN hfK (ϖ w) hϖ (l w) hl D hDv
  rwa [hfD] at h

end GlobalTheory.CellVanish
end
end

