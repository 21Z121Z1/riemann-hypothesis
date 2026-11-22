import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDownStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0002
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.Bundle0001
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0004
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0003
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SumGammaNnMinus
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0010
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0009
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.PsiDatum
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TMapSpec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.CapIdx
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Transport

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepDown
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap

theorem stepDown : StepDownStatement := by
  intro hIS k r ε u h hsg hp hq lam s hHC hGap hHC' hGap' hu hBNZ
  classical
  obtain ⟨T, μ, P, z, c, Vp, _, _, _, π, μW, μN, hμ, hP, hBd, v₁, v₂, ξ, x₀, x, hx₀, hx, hne⟩ := hBNZ
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hsg
  obtain ⟨H, _, _, _, σ, D, E, V, ι, hσ, hD, hV, hc, hVK, hcoef⟩ :=
    LemK.psiDatum (2 * r + k + 1) ε lam h T μ hHC hGap hNeed hq0 hμ
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  set y₀ : Mat k r := P * x₀ * P⁻¹ with hy₀
  have hy₀J : y₀ ∈ UJset ε := CurveContinuity.inUJ_conj hP hx₀
  have hy₀inv : y₀⁻¹ = P * (x₀⁻¹ * P⁻¹) := by
    rw [hy₀, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv P hdet]
  set v : V := ι.symm v₁ with hv
  set w : V := ι.symm v₂ with hw

  have hper : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (coefX σ y₀ ((w : D) : H) ((v : D) : H)) ξ x ≠ 0 := by
    have hcg : ∀ g ∈ UJset ε, coefX σ y₀ ((w : D) : H) ((v : D) : H) g =
        ⟪v₂, S7.PsiM T μ (y₀⁻¹ * g) v₁⟫_ℂ := by
      intro g hg
      have hm : y₀⁻¹ * g ∈ UJset ε := CapelliClosureMembership.inUJ_mul (TDAux.inv_mem hy₀J) hg
      unfold coefX
      rw [hcoef _ hm v w, hv, hw, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rw [QuotA.per_congr hP hBd _ hcg ξ hx]
    intro h0
    apply hne
    rw [← h0]
    unfold per aaFun
    congr 1
    funext g
    unfold psiCoef
    congr 2
    rw [hy₀inv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P⁻¹ P, hPP', Matrix.one_mul]
  obtain ⟨β, hβ⟩ := evalM k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp π
    μW μN P hP hBd y₀ w v ξ s x hy₀J hx hu hper

  have hGs : ∀ a b, ∀ m ∈ genSub E V, E a b m ∈ genSub E V := fun a b m hm => LemK.generated_submodule_stable_under_action V a b hm
  have hvG : (v : D) ∈ genSub E V := LemK.le_generatedSubmodule_dual V v.2
  have hC : ∀ m ∈ genSub E V, Capelli.capelliC E (((-(LemK.thV lam s)) : ℝ) : ℂ) m = 0 := by
    intro m hm
    rw [capVal (2 * r + k + 1) ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hHC hGap hNeed hq0 _ m hm]
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (by push_cast; ring), zero_smul]
  have hxs : Capelli.nnMinus E β (((-(LemK.thV lam s)) : ℝ) : ℂ) (v : D) ∈
      LemK.Xs (LemK.eeVd E) (genSub E V) (LemK.thVd lam s) := by
    have he := (eig D (2 * r + k) E (genSub E V) (-(LemK.thV lam s)) β β (v : D) hD.glRep hGs hC hvG).2
    have hθ : LemK.thVd lam s = -(LemK.thV lam s) - ((2 * r + k : ℕ) : ℝ) := by
      unfold LemK.thV LemK.thVd
      push_cast
      ring
    rw [hθ]
    exact he
  obtain ⟨Wf, W', hWf, hW', hirr, hcas, hK, hinj⟩ :=
    quotM k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap z c Vp π μW μN P hP hBd
      y₀ w ξ s _ hy₀J hHC' hGap' hxs ⟨x, hx, hβ⟩
  refine finStep hIS k r ε u (lam - Pi.single s 1) h z c Vp π μW μN P hP hBd hp hq hsg hHC' hGap' ξ Wf W'
    ?_ hW' hirr hcas hK hinj
  intro F hF
  obtain ⟨y, hy, rfl⟩ := hWf F hF
  have hyG : ∀ c', y c' ∈ genSub E V := (LemK.mem_euler_eigenspace_iff.1 hy).1
  have hspec := tMapD_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hsg hHC hGap (xJ P z) y₀ w
    hy₀J y hyG
  exact ⟨QuotA.contOn_of_smooth hspec.1.1, hspec.2.2 []⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.StepUp
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

theorem stepUp : StepUpStatement := by
  intro hIS k r ε u h hgap hp hq lam s hlam hgl hlam' hgl' hu hB
  classical
  obtain ⟨T, μ, P, z, c, Vp, _, _, _, π, μW, μN, hμ, hP, hBD, v₁, v₂, ξ, x₀, x, hx₀, hx, hne⟩ := hB
  obtain ⟨hq0, hNeed⟩ := gapNeed k r ε h hp hq hgap
  obtain ⟨H, _, _, _, σ, D, E, V, ι, hσ, hD, hV, hc, hVK, hcoef⟩ :=
    LemK.psiDatum (2 * r + k + 1) ε lam h T μ hlam hgl hNeed hq0 hμ
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have hX₀ : P * x₀ * P⁻¹ ∈ UJset ε := cayley_conj_mem_unitary_group hP hx₀
  have hper : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
      (coefX σ (P * x₀ * P⁻¹) (((ι.symm v₂ : V) : D) : H) (((ι.symm v₁ : V) : D) : H)) ξ x =
      aaFun T μ P μW μN (Formalism.MainNotions.S.psiGen k r z c) π v₁ v₂ ξ x₀ x := by
    have hHW := hBD.2.2.2.2.1
    have hHN := hBD.2.2.2.2.2
    have : SigmaFinite μW := hHW.1
    have : SigmaFinite μN := hHN.1
    unfold per aaFun sInt
    apply integral_congr_ae
    filter_upwards [ae_mem_unitary_nilpotent_product z μW μN hHW hHN] with p hp'
    have hs : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      unitary_hermitian_form_mul_mem hp'.1.1 hp'.2.1
    have hg := unitary_hermitian_form_mul_mem hs hx
    have hinv : x₀⁻¹ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := (Transport.uh_facts hP hx₀).2.1
    have hG : P * (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹ ∈ UJset ε :=
      cayley_conj_mem_unitary_group hP (unitary_hermitian_form_mul_mem hinv hg)
    have hX : P⁻¹ * (P * x₀ * P⁻¹) * P = x₀ := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd, Matrix.nonsing_inv_mul _ hd,
        Matrix.mul_one]
    have heq : (P * x₀ * P⁻¹)⁻¹ * (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) =
        P * (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) * P⁻¹ := by
      have h1 := conj_inv_mul_conj P (P * x₀ * P⁻¹) (Matrix.of p.1 * Matrix.of p.2 * x) hd
      rw [hX] at h1
      exact h1.symm
    show coefX σ (P * x₀ * P⁻¹) _ _ (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) • _ =
      psiCoef T μ P v₁ v₂ (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) • _
    unfold coefX psiCoef
    rw [heq, hcoef _ hG (ι.symm v₁) (ι.symm v₂)]
    simp only [LinearEquiv.apply_symm_apply]
  have hne' : per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π
      (coefX σ (P * x₀ * P⁻¹) (((ι.symm v₂ : V) : D) : H) (((ι.symm v₁ : V) : D) : H)) ξ x ≠ 0 := by
    rw [hper]; exact hne
  obtain ⟨y, hy⟩ := evalP k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hgap hlam hgl z c Vp π
    μW μN P hP hBD (P * x₀ * P⁻¹) (ι.symm v₂) (ι.symm v₁) ξ s x hX₀ hx hu hne'
  have hGl : IsGlRep E := hD.glRep
  have hstab : ∀ a b, ∀ m ∈ genSub E V, E a b m ∈ genSub E V := fun a b m hm =>
    Submodule.mem_sInf.2 fun S hS => hS.2 a b m (Submodule.mem_sInf.1 hm S hS)
  have hkill : ∀ m ∈ genSub E V, Capelli.capelliC E (((-(LemK.thV lam s)) : ℝ) : ℂ) m = 0 := by
    intro m hm
    rw [capVal (2 * r + k + 1) ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hlam hgl hNeed hq0 _ m hm,
      Finset.prod_eq_zero (Finset.mem_univ s) (by push_cast; ring), zero_smul]
  have hvS : (((ι.symm v₁ : V) : D)) ∈ genSub E V :=
    Submodule.mem_sInf.2 fun S hS => hS.1 (ι.symm v₁).2
  have hXs := (eig D (2 * r + k) E (genSub E V) (-(LemK.thV lam s)) y y ((ι.symm v₁ : V) : D) hGl hstab
    hkill hvS).1
  rw [neg_neg] at hXs
  obtain ⟨Wf, W', hWf, hW', hirr, hcas, hK, hinj⟩ := quotP k r ε u lam h H σ D E V T μ ι hσ hD hV hc hVK hμ
    hcoef hp hq hgap hlam hgl z c Vp π μW μN P hP hBD (P * x₀ * P⁻¹) (ι.symm v₂) ξ s
    (Capelli.nnPlus E y (((-(LemK.thV lam s)) : ℝ) : ℂ) ((ι.symm v₁ : V) : D)) hX₀ hlam' hgl' hXs ⟨x, hx, hy⟩
  refine finStep hIS k r ε u (lam + Pi.single s 1) h z c Vp π μW μN P hP hBD hp hq hgap hlam' hgl' ξ Wf W'
    ?_ hW' hirr hcas hK hinj
  intro F hF
  obtain ⟨y', hy', rfl⟩ := hWf F hF
  have hyS : ∀ c', y' c' ∈ genSub E V := fun c' =>
    (Submodule.mem_pi.1 (Submodule.mem_inf.1 hy').1) c' (Set.mem_univ _)
  obtain ⟨hsm, -, hbd⟩ := tMap_spec k r ε lam h H σ D E V T μ ι hσ hD hV hc hVK hμ hcoef hp hq hgap hlam hgl
    (xJ P z) (P * x₀ * P⁻¹) (ι.symm v₂) hX₀ y' hyS
  obtain ⟨C, hC⟩ := hbd []
  exact ⟨CapelliMinorRestriction.cont_of_smoothOnG hsm.1, C, hC⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

