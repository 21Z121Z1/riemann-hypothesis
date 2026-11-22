import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0288
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0278
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0004
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FormsAre
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThCLeftStab
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LevelNeQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0094
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0175
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelsOverOfFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0404

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJetsOfTranslateJets
section
noncomputable section

namespace GlobalTheory.LiftTypePrime.Jets

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions GlobalTheory.GalTheta

section Integral

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : @IsIntegral ℤ C _ _ (Ring.toIntAlgebra C) x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

variable {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]}

theorem intAt_iff {x : ℂ} : IntAt lam x ↔ ∃ h : x ∈ Qbar, ‖lam ⟨x, h⟩‖ ≤ 1 := by
  unfold IntAt lamC
  exact ⟨fun ⟨h, h1⟩ => ⟨h, by rwa [dif_pos h] at h1⟩, fun ⟨h, h1⟩ => ⟨h, by rwa [dif_pos h]⟩⟩

theorem intAt_mul {x y : ℂ} (hx : IntAt lam x) (hy : IntAt lam y) : IntAt lam (x * y) := by
  obtain ⟨h, h1⟩ := intAt_iff.1 hx
  obtain ⟨h', h2⟩ := intAt_iff.1 hy
  refine intAt_iff.2 ⟨mul_mem h h', ?_⟩
  change ‖lam (⟨x, h⟩ * ⟨y, h'⟩)‖ ≤ 1
  rw [map_mul, norm_mul]
  exact mul_le_one₀ h1 (norm_nonneg _) h2

theorem intAt_add {x y : ℂ} (hx : IntAt lam x) (hy : IntAt lam y) : IntAt lam (x + y) := by
  obtain ⟨h, h1⟩ := intAt_iff.1 hx
  obtain ⟨h', h2⟩ := intAt_iff.1 hy
  refine intAt_iff.2 ⟨add_mem h h', ?_⟩
  change ‖lam (⟨x, h⟩ + ⟨y, h'⟩)‖ ≤ 1
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

theorem intAt_of_isIntegral {x : ℂ} (hx : IsIntegral ℤ x) : IntAt lam x := by
  have h : x ∈ Qbar := mem_algebraicClosure_iff'.2 hx.tower_top
  refine intAt_iff.2 ⟨h, ?_⟩
  have h1 : IsIntegral ℤ (⟨x, h⟩ : Qbar) :=
    (isIntegral_algHom_iff ((algebraMap Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 hx
  exact norm_le_one_of_isIntegral (map_isIntegral_int lam h1)

theorem intAt_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, IntAt lam (f i)) : IntAt lam (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IntAt lam) (fun _ _ => intAt_add) (intAt_of_isIntegral isIntegral_zero) h

end Integral

theorem isIntegral_exp (k : ℤ) (x : ℝ) (n : ℕ) (hn : 0 < n) (m : ℤ) (h : (n : ℝ) * x = m) :
    IsIntegral ℤ (Complex.exp ((k : ℂ) * ((Real.pi : ℂ) * Complex.I) * (x : ℂ))) := by
  have h' : (n : ℂ) * (x : ℂ) = m := by exact_mod_cast h
  refine IsIntegral.of_pow (n := 2 * n) (by omega) ?_
  rw [← Complex.exp_nat_mul]
  have : ((2 * n : ℕ) : ℂ) * ((k : ℂ) * ((Real.pi : ℂ) * Complex.I) * (x : ℂ)) =
      ((k * m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    linear_combination (2 * (k : ℂ) * ((Real.pi : ℂ) * Complex.I)) * h'
  rw [this, Complex.exp_int_mul_two_pi_mul_I]
  exact isIntegral_one

variable {D : D7} {N N' : ℕ}

theorem taylor_sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (α : Mono D N N') :
    TaylorLogMetric.taylor D (fun z => ∑ i ∈ s, c i * f i z) α = ∑ i ∈ s, c i * TaylorLogMetric.taylor D (f i) α := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact GlobalTheory.ThetaConj.taylor_zero D α
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [← ih, ← GlobalTheory.ThetaConj.taylor_mul D _ (hf i)]
    exact GlobalTheory.ThetaConj.taylor_add D ((hf i).const_mul _) (by fun_prop) α

theorem applyAt0_comb {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → VC D N N' → ℂ)
    (hf : ∀ i, Differentiable ℂ (f i)) (P : MvPolynomial (Idx D N N') ℂ) :
    applyAt0 D P (fun z => ∑ i ∈ s, c i * f i z) = ∑ i ∈ s, c i * applyAt0 D P (f i) := by
  unfold applyAt0
  simp only [taylor_sum s c f hf, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => by ring

end GlobalTheory.LiftTypePrime.Jets

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions GlobalTheory.GalTheta Jets

end GlobalTheory.LiftTypePrime

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorSourceLawCoupledLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLawG

theorem locTopG_source : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' y'' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → k.1 y'' - y' ∈ stdAt X.E _ P.1 →
    (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (y ∘ₗ k.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (y ∘ₗ k.1.toLinearMap)) y'') * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr _hsel hL b P hP g z hmid
  have hgC : g ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) :=
    (exists_midLev_iff Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g).1 ⟨z, hmid⟩
  have hgI : g ∈ GLint X.E (R.N (m2 + 1)) P.1 := hL.int (m2 + 1) b P hgC
  refine ⟨⟨g, hgI⟩, rfl, ?_⟩
  intro k hk y y' y'' hy' hky
  obtain ⟨r, hr, hrg, hz⟩ := hmid
  have hred : ∀ x ∈ stdAt X.E (R.N (m2 + 1)) P.1, redV P.1 (g x) = (redGL _ P.1 k).1.mulVec (redV P.1 x) := by
    intro x hx
    rw [hk]
    exact redV_redGL (⟨g, hgI⟩ : GLint X.E (R.N (m2 + 1)) P.1) hx
  have hmem : redGL _ P.1 k ∈ (L.levG (m2 + 1) b ⟨P.1, hP⟩).H :=
    (hL.grpG (m2 + 1) b ⟨P.1, hP⟩ (redGL _ P.1 k)).2 ⟨g, hgC, hred⟩
  set c : X.Kˣ := (L.levG (m2 + 1) b ⟨P.1, hP⟩).lam ⟨redGL _ P.1 k, hmem⟩ with hcdef
  have hcz : (c : X.K) = z := by
    rw [hz]
    exact hL.chrG (m2 + 1) b ⟨P.1, hP⟩ ⟨redGL _ P.1 k, hmem⟩ g r hr hrg hred
  have hlev : GlobalTheory.TopLaw.LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P k c :=
    ⟨fun _ => ⟨hmem, rfl⟩, fun _ h => absurd hP h⟩
  have hrho : rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) := by
    unfold rhoS
    refine unitV_congr _ ?_
    rw [(det_glint k).2, ← redGL_val, hk, redGL_val]
    exact (det_glint (⟨g, hgI⟩ : GLint X.E (R.N (m2 + 1)) P.1)).2
  rw [hrho, ← hcz]
  have hm := hL.hm
  have key := GlobalTheory.TopLaw.locTop_source hX hPr hL hlev
  clear_value c
  clear hcdef hcz hrho hred hz hrg hr hmem
  revert key y
  cases R with
  | mk e k0 m t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    change m = m2 + 2 at hm
    subst hm
    intro y key
    have := key y (fun _ => hy') (fun h => absurd hP h) (fun _ => hky) (fun h => absurd hP h)
    unfold locTop at this
    rw [PhiTopG_eq]
    exact this

end GlobalTheory.TopLawG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorTargetLawTopLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwTop

open GlobalTheory.DatumLaw GlobalTheory.TopLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem rowLevTop_glint {sharp : Bool} {n : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    {g : Sp X.E ((n - 1) + 0) ≃ₗ[X.E] Sp X.E ((n - 1) + 0)} (hg : g ∈ rowLevTop Pr R sharp n P) : g ∈ GLint X.E (n - 1) P := by
  unfold rowLevTop at hg
  rw [if_pos hP] at hg
  have h : g ∈ stabL X.E ((n - 1) + 0) (LocE.lamY P (qOf P) (n - 1) 0 fun i => i + 1) := by
    split_ifs at hg
    · exact hg.1
    · exact hg.1
  rw [GlobalTheory.TopLawSym.lamY_eq] at h
  exact h

theorem phiTop_rowLevTop (hm : R.m = m2 + 2) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    {g : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)} (hg : g ∈ rowLevTop Pr R sharp (R.N R.m) P)
    (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) :
    PhiTop Ch mu sharp m2 P (g.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det g : X.Eˣ) : X.E) =
      rowChrTop Ch mu sharp R.m (R.N R.m) P g.toLinearMap * PhiTop Ch mu sharp m2 P x := by
  obtain ⟨-, -, -, a4⟩ := ranks R (j := 0) (by omega)
  have a5 := r_le_X' R
  have b1 : R.N R.m - 1 + 0 = R.r + (m2 + 1) * R.t + R.t := by
    rw [add_zero, rank_X'_eq R, hm]; ring
  unfold rowLevTop at hg
  unfold PhiTop rowChrTop
  rw [if_pos hP] at hg
  rw [if_pos hP, if_pos hP]
  generalize R.N R.m - 1 = n at *
  generalize psi0P Ch P = ψ
  generalize chiP Ch P = χ
  rw [hm]
  split_ifs at hg ⊢
  · rw [DatumLaw.phiGS_eq]
    exact phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left
      (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x
  · rw [phiG_eq, LocE.lamGB, lamGv_eq]
    exact phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left
      (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x

theorem locTop_topLev (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hP : P.1 ∈ Pr.vGs) (g : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (z : X.K) (hg : TopLev Ch sel mu cst R.m P g z) :
    ∃ Gg : GLint X.E (R.N R.m) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N R.m) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
      ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (y' : Sp X.E (R.N (m2 + 1))), (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) →
        z * locTop Ch sel mu cst m2 P ((k⁻¹).1.toLinearMap ∘ₗ y) y' * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
          locTop Ch sel mu cst m2 P y y' := by
  classical
  obtain ⟨g', hg', h1, h2, rfl⟩ := hg
  let j : GLint X.E (R.N R.m - 1) P.1 := ⟨g', rowLevTop_glint hP hg'⟩
  have eg : (extI (N_m_succ R) P.1 j).1 = g := by
    refine LinearEquiv.ext fun v => ext_prH (N_m_succ R) ?_ ?_
    · exact (prH_sumE (N_m_succ R) _ _ _).trans (LinearMap.congr_fun h1 v).symm
    · refine (sumE_last (N_m_succ R) _ _ _).trans ?_
      rw [Units.val_one, one_mul]
      exact (atNL_last v).symm.trans ((LinearMap.congr_fun h2 v).symm.trans (atNL_last _))
  refine ⟨extI (N_m_succ R) P.1 j, eg, fun k hk y y' hy' => ?_⟩
  have e3 : (k⁻¹).1.toLinearMap ∘ₗ y = (k⁻¹ * extI (N_m_succ R) P.1 j).1.toLinearMap ∘ₗ
      ((extI (N_m_succ R) P.1 j⁻¹).1.toLinearMap ∘ₗ y) := by
    rw [map_inv]
    exact LinearMap.ext fun v => congrArg (k⁻¹).1 (LinearEquiv.apply_symm_apply (extI (N_m_succ R) P.1 j).1 (y v)).symm
  rw [e3, locTop_inv hm hc hP hq _ (by rw [map_mul, map_inv, hk, inv_mul_cancel]) _ hy', locTop_extI, ← eg]
  unfold rhoT
  rw [if_pos hP, unitV_det_ext _ (N_m_succ R) j _ rfl]
  have h3 := phiTop_rowLevTop (Ch := Ch) (mu := mu) hm cst.sharp hP hg' ((j⁻¹).1.toLinearMap ∘ₗ
    (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))))
  have e4 : g'.toLinearMap ∘ₗ ((j⁻¹).1.toLinearMap ∘ₗ
      (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))) =
      prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) :=
    LinearMap.ext fun v => g'.apply_symm_apply _
  rw [e4] at h3
  have hu : IsUnit (redP P.1 ((LinearEquiv.det j.1 : X.Eˣ) : X.E)) := by
    rw [(det_glint j).2, ← redGL_val, ← Matrix.isUnit_iff_isUnit_det]
    exact Units.isUnit _
  have h4 : LocE.unitV (chiP Ch P.1 (m2 + 1)) ((LinearEquiv.det g' : X.Eˣ) : X.E) *
      LocE.unitV (chiP Ch P.1 (m2 + 1))⁻¹ ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = 1 := by
    rw [DatumLaw.unitV_eq, DatumLaw.unitV_eq, extendByZeroOffSubset_mul_left_of_mem_lattice]
    exact mul_inv_cancel₀ (unitCharacterExtendByZero_ne_zero_of_isUnit _ hu)
  unfold locTop
  rw [← mul_assoc, mul_right_comm]
  congr 1
  refine (congrArg (· * _) h3.symm).trans ?_
  rw [mul_assoc, h4, mul_one]

theorem topF_target_vG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) →
    z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y)) y') * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hL P hP
  have hm : R.m = m2 + 1 + 1 := hL.hm
  generalize m2 + 1 + 1 = j at hm ⊢
  subst hm
  intro g z hg
  exact locTop_topLev hL.hm hL.cst_ok (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2 hP g z hg

end GlobalTheory.TwTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairKernelLawOfFiniteDatumLaw
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory GlobalTheory.KerJ NumberField IsDedekindDomain Classical

namespace GlobalTheory.KFiDat

theorem termLaw_of_xi : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.X.Ok → IsSel t.X t.sel → (∀ i, t.Pr.g i ∈ t.S) → (∀ v, t.Pr.T v ∈ t.S) → (∀ l ∈ D.host.small, l ∈ t.S) → D.host.q ∈ t.S → (∃ eta, t.Ch.Tied t.glob.σ₀ (fun j τ => (D.hc (t.seam.iT τ)).e j) t.glob.mu0 eta) → ∀ u μ i, i < D.R.m → ∀ (c : (D.chTw u μ).cls i) (c' : (D.chTw u μ).cls (i + 1)) (γ : UF t.X.E (D.R.N (i + 1))) (k : t.X.K), gmap γ.1 ((t.rd u μ).N (i + 1) c') = (t.rd u μ).N (i + 1) c' → (∀ x, ∀ z ∈ mulLat (t.rd u μ).lev (homAt (t.rd u μ).SS ((t.rd u μ).N i c) ((t.rd u μ).N (i + 1) c')), (t.rd u μ).Xi i c c' (x + z) = (t.rd u μ).Xi i c c' x) → (∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) * t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E)) = t.seam.σ₀ k * (t.rd u μ).Xi i c c' x) → TermLaw (t.O u μ) i c c' (matE t.seam γ.1, t.seam.σ₀ k) := by
  intro D L hT Gi Gl K Y cX ex t hX hsel hgS hTS h2S hqS hTied u μ i hi c c' γ k hγ hΞ hXi
  obtain ⟨eta, hTied⟩ := hTied
  have hok := t.seam_ok
  obtain ⟨hSS, hlev, -⟩ := t.rd_chain u μ
  set z : t.X.E := ((LinearEquiv.det γ.1 : t.X.Eˣ) : t.X.E) with hz
  have hz0 : z ≠ 0 := Units.ne_zero _
  have hSD' : IsSDLat D.host.E _ (t.seam.lat ((t.rd u μ).N (i + 1) c')) :=
    t.O_lat u μ (i + 1) c' ▸ ((t.O u μ).lat (i + 1) c').2
  obtain ⟨hzs, hzi, hprod1⟩ := GlobalTheory.T.det_unitaryStabiliser_selfDualLattice_normOne D t.X t.seam t.χ hok t.χ_ok _ _ hSD' γ hγ
  let eZ : Fin D.R.m → t.X.Tau → ℤ := fun j τ => (D.chTw u μ).sDiv j (t.seam.iT τ) + ((D.R.N j / 2 : ℕ) : ℤ)
  have heZ : ∀ j τ, ((eZ j τ : ℤ) : ℚ) = (D.hc (t.seam.iT τ)).e j := by
    intro j τ
    have h1 := (D.chTw u μ).sDiv_eq j j.2 (t.seam.iT τ)
    rw [D.hcW_e] at h1
    obtain ⟨m, hm⟩ := rank_even D.R j
    have h2 : ((D.R.N j / 2 : ℕ) : ℚ) = (D.R.N j : ℚ) / 2 := by
      rw [hm]; push_cast; rw [show m + m = 2 * m by ring, Nat.mul_div_cancel_left _ two_pos]; push_cast; ring
    simp only [eZ]
    rw [Int.cast_add, h1, Int.cast_natCast, h2, sExp, Nat.add_sub_cancel]
    ring
  have hTied' : t.Ch.Tied t.glob.σ₀ (fun j τ => ((eZ j τ : ℤ) : ℚ)) t.glob.mu0 eta := by
    have e : (fun j τ => ((eZ j τ : ℤ) : ℚ)) = (fun j τ => (D.hc (t.seam.iT τ)).e j) := funext fun j => funext fun τ => heZ j τ
    rw [e]; exact hTied
  have hP := GlobalTheory.NormOneUnit.prod_muAt t.Ch t.sel (t.tup μ) (t.cst μ) t.glob.σ₀ eZ t.glob.mu0 eta hX t.pr_ok hsel hgS
    (GlobalTheory.T.columnField_ramificationIdxIn_eq_one D t.X t.seam hX hok) hTied' ⟨i, hi⟩ z hzs hzi
  rw [t.glob_σ] at hP
  set M := t.seam.σ₀ (∏ P : rowSG t.Pr t.sel (t.tup μ), muAt t.Ch t.sel (t.tup μ) (t.cst μ) i P z) with hMdef
  have hw0 : ∀ τ, t.X.embC t.seam.σ₀ τ z ≠ 0 := fun τ => (map_ne_zero _).2 hz0
  have hP' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(eZ ⟨i, hi⟩ τ)) := hP
  have hM0 : M ≠ 0 := by
    rw [hP']
    exact Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hw0 τ)
  have hk : ∀ x, (t.rd u μ).Xi i c c' (γ.1.toLinearMap ∘ₗ x) = (t.seam.σ₀ k / M) * (t.rd u μ).Xi i c c' x := by
    intro x
    have := hXi x
    field_simp
    linear_combination this
  have hA : TaylorLogMetric.admitted D _ _ (t.seam.lat ((t.rd u μ).N i c)) (t.seam.lat ((t.rd u μ).N (i + 1) c')) := by
    rw [← t.O_lat, ← t.O_lat]
    exact ⟨rank_even _ _, rank_even _ _, ((t.O u μ).lat i c).2, ((t.O u μ).lat (i + 1) c').2⟩
  have hSSc : ∀ P ∈ (t.rd u μ).SS, conjPrime₂ P ∉ (t.rd u μ).SS := by
    rw [hSS]
    exact GlobalTheory.T.memberBadPrimes_no_conjugatePair t.sel (t.tup μ) hX t.pr_ok hsel (t.word u) (hTS _) hgS
  have h2q : ∀ P ∈ (t.rd u μ).SS, ((D.host.QS : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal ∧ ((D.host.q : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
    intro P hP
    rw [hSS] at hP
    obtain ⟨p, hp, hpP, hk⟩ := sall_nat t.sel (t.tup μ) t.pr_ok hsel (t.word u) hP
    have hp2 : p ∉ D.host.small ∧ p ≠ D.host.q := by
      rcases hk with e | ⟨j, e⟩ | hn
      · rw [e, t.T_rec]; exact ⟨UpperTheory.Small.not_mem_of_mod D.host (D.T_mod_cond u), D.T_ne_q u⟩
      · rw [e, t.g_rec]; exact ⟨UpperTheory.Ram.g_notMem_small D j, GlobalTheory.ShortOwnCompare.level_ne_q D j⟩
      · exact ⟨fun e => hn (h2S _ e), fun e => hn (e ▸ hqS)⟩
    have key : ∀ l : ℕ, l.Prime → l ≠ p → ((l : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
      intro l hl hlp hlP
      have hc : IsCoprime ((p : ℕ) : 𝓞 t.X.E) ((l : ℕ) : 𝓞 t.X.E) := by
        have h1 := (Nat.coprime_primes hp hl).2 (Ne.symm hlp)
        have h2 := (Nat.isCoprime_iff_coprime.2 h1).map (Int.castRingHom (𝓞 t.X.E))
        simpa using h2
      obtain ⟨a, b, hab⟩ := hc
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (hab ▸ add_mem (P.asIdeal.mul_mem_left a hpP) (P.asIdeal.mul_mem_left b hlP)))
    exact ⟨UpperTheory.Ram.natCast_notMem_of_coprime P.isPrime.ne_top hpP
      ((Nat.Prime.coprime_iff_not_dvd hp).2 (UpperTheory.Small.not_dvd_QS D.host hp hp2.1)).symm, key _ D.host.hyp.1 hp2.2.symm⟩
  have hlev0 : 0 < (t.rd u μ).lev := by
    rw [hlev]
    exact modulus_pos t.sel (t.tup μ) (t.cst μ) (t.word u) (t.pr_ok.T_prime _).pos
  have key := GlobalTheory.KerLaw.thC_left_stab D t.X t.seam t.cc t.δ t.B t.χ t.cD hok t.cc_ok t.δ_ok t.χ_ok _ _ _ _ hA
    (t.rd u μ).SS (t.rd u μ).lev ((t.rd u μ).Xi i c c') hlev0 hSSc h2q hΞ γ hγ _ hk
  have hdet : (matE t.seam γ.1).det = t.seam.iE z := by
    rw [matE]
    change ((t.seam.iE : t.X.E →+* D.host.E).mapMatrix (LinearMap.toMatrix' γ.1.toLinearMap)).det = _
    rw [← RingHom.map_det, LinearMap.det_toMatrix', hz, LinearEquiv.coe_det]
    rfl
  refine ⟨by rw [hdet]; exact (map_ne_zero _).2 hz0, t.seam.σ₀ k / M, fun w => ?_, ?_⟩
  · rw [t.O_Th]
    unfold KerRead.Th Seam.push
    refine (congrArg _ ?_).trans (key (fun τ => w (t.seam.iT τ)))
    funext τ
    refine congrArg (· * Matrix.of (w (t.seam.iT τ))) ?_
    ext a b
    simp only [matE, Matrix.map_apply]
    exact (hok.1 τ _).symm
  · show t.seam.σ₀ k = t.seam.σ₀ k / M * ∏ τ, TaylorLogMetric.embT D τ (matE t.seam γ.1).det ^ (-(D.chTw u μ).sDiv i τ)
    rw [hdet]
    have hw : ∀ τ, t.X.embC t.seam.σ₀ τ z = TaylorLogMetric.embT D (t.seam.iT τ) (t.seam.iE z) := fun τ => hok.1 τ z
    have hR : ∏ τ, TaylorLogMetric.embT D τ (t.seam.iE z) ^ (-(D.chTw u μ).sDiv i τ) =
        ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) :=
      (Fintype.prod_equiv t.seam.iT _ _ fun τ => by rw [hw]).symm
    have h1 : ∏ τ, t.X.embC t.seam.σ₀ τ z = 1 := by
      rw [← hprod1]
      exact Fintype.prod_equiv t.seam.iT _ _ fun τ => hw τ
    have hM' : M = ∏ τ, t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) := by
      rw [hP']
      simp only [eZ]
      have e1 : ∀ τ, t.X.embC t.seam.σ₀ τ z ^ (-((D.chTw u μ).sDiv i (t.seam.iT τ) + ((D.R.N i / 2 : ℕ) : ℤ))) =
          t.X.embC t.seam.σ₀ τ z ^ (-(D.chTw u μ).sDiv i (t.seam.iT τ)) * t.X.embC t.seam.σ₀ τ z ^ (-((D.R.N i / 2 : ℕ) : ℤ)) :=
        fun τ => by rw [neg_add, zpow_add₀ (hw0 τ)]
      rw [Finset.prod_congr rfl fun τ _ => e1 τ, Finset.prod_mul_distrib, Finset.prod_zpow, h1, one_zpow, mul_one]
    rw [hR, ← hM']
    field_simp

end GlobalTheory.KFiDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueChainStabilisersEqStandardReaderPointsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChain_stabilizers_eq_standardBaseLevel_points : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.Pdv.ColNorm I → I.StdKer l Z t → GlobalTheory.Pdv.StdRd I l Z t → ∀ u a, GlobalTheory.KerJ.StabPin t u a (GlobalTheory.Pdv.stabStd I l Z u a) := by
  first | exact @GlobalTheory.Pdv.stab_pin | exact GlobalTheory.Pdv.stab_pin | (intros; apply GlobalTheory.Pdv.stab_pin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnTupleKernelsRational
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix GlobalTheory.TwU GlobalTheory.TwU.AtTrue
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU.AtTrue

theorem tuple_kernels_rational : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Tw : TwForms (I.rec7 l Z)), ColIn.JetsIn I → Tw = I.tw l l0 Z →
    ∀ (u : B.Word) (a : I.ι) j, j < B.R.m → (Tw.fm u a).KRat j := by
  intro B X I h _ l Z l0 Tw hJ hTw u a j hj
  subst hTw
  exact ((KerRat.kernels_rational I l Z h hJ
    (Or.inr (GlobalTheory.Core.Ht2.family_laws I h (base_fields_primes_ok B X).1 l Z))).2.2 l0 u a).1 j hj

end GlobalTheory.TwU.AtTrue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedCompNormOfKilledInertiaFixingStatement
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_comp_norm_of_killed_inertia_fixing : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra E M] [IsScalarTower E M Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (u : HeightOneSpectrum (𝓞 M)) (h : IsPlaceOver A w) (h' : IsPlaceOver A u) [u.asIdeal.LiesOver w.asIdeal] (n : ℕ) (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → (∀ t : Weil h, deg t = 0 → (∀ x : M, (t : G E Ω) (algebraMap M Ω x) = algebraMap M Ω x) → ∀ j, ξ j (a t) = 1) → ∀ j (x : (u.adicCompletion M)ˣ), Valued.v (x : u.adicCompletion M) = 1 → ξ j (GlobalTheory.BCChar.normU w u x) = 1 := by
  first | (exact @GlobalTheory.RoadU.unram_comp_normU_of_fix) | (exact GlobalTheory.RoadU.unram_comp_normU_of_fix) | (intros; apply GlobalTheory.RoadU.unram_comp_normU_of_fix  <;> assumption)
end

