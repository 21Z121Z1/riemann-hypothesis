import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0133

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceOverTypePrimeDividesOrConjugateStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_over_typePrime_divides_or_conjugate : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → P.Div k PP ∨ ∃ PP', P.Div k PP' ∧ IsConjPl PP' PP := by
  first | exact @GlobalTheory.StepLaw.div_or_isConjPl_div | exact GlobalTheory.StepLaw.div_or_isConjPl_div | (intros; apply GlobalTheory.StepLaw.div_or_isConjPl_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleUnitaryGroupConcrete
section
namespace GlobalTheory.RegSSObj

theorem regularSemisimple : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple :=
  GlobalTheory.RegSS.regularSemisimple

end GlobalTheory.RegSSObj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeHeightEntryLeAdelicHeightGLStatement
section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeHeight_entry_le_adelicHeightGL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ) := by
  first | exact @GlobalTheory.RatCount.htE_entry_le_heightGL | exact GlobalTheory.RatCount.htE_entry_le_heightGL | (intros; apply GlobalTheory.RatCount.htE_entry_le_heightGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoInfMulProd
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeInfExp

theorem tendsto_inf_mul_prod {L : Type} [Field L] [NumberField L] (χ : HChar L) (k : Lˣ) :
    Filter.Tendsto (fun T : Finset (HeightOneSpectrum (𝓞 L)) =>
      ((χ.inf k : ℂˣ) : ℂ) * ∏ P ∈ T, ((χ.locK P k : ℂˣ) : ℂ)) Filter.atTop (nhds 1) := by
  have hlim := GlobalTheory.Mem.Chr.CharModel.tendsto_prod_local (F := L) k
  have hcont : Continuous fun a => ((χ.1 a : ℂˣ) : ℂ) := Units.continuous_val.comp χ.2.1
  have h1 := (hcont.tendsto _).comp hlim
  have hd : ((χ.1 (GlobalTheory.Mem.Chr.diagUnits L k) : ℂˣ) : ℂ) = 1 := congrArg Units.val (χ.2.2 k)
  rw [hd] at h1
  refine h1.congr fun T => ?_
  simp only [Function.comp_apply, map_mul, map_prod, Units.val_mul, Units.coe_prod]
  rfl

theorem finite_bad {L : Type} [Field L] [NumberField L] (k : Lˣ) (N : ℕ) (hN : 0 < N) :
    {P : HeightOneSpectrum (𝓞 L) | ¬ (P.valuation L (k : L) = 1 ∧ (N : 𝓞 L) ∉ P.asIdeal)}.Finite := by
  have hS : (HeightOneSpectrum.Support (𝓞 L) (k : L) ∪ HeightOneSpectrum.Support (𝓞 L) ((k : L)⁻¹)).Finite :=
    (HeightOneSpectrum.Support.finite _ _).union (HeightOneSpectrum.Support.finite _ _)
  have hN0 : (N : 𝓞 L) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap (𝓞 L) L) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
    omega
  have hD : {P : HeightOneSpectrum (𝓞 L) | P.asIdeal ∣ Ideal.span {(N : 𝓞 L)}}.Finite :=
    Ideal.finite_factors (by simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot] using hN0)
  refine (hS.union hD).subset ?_
  intro P hP
  rw [Set.mem_ofPred_eq, not_and_or, not_not] at hP
  rcases hP with h | h
  · left
    rcases lt_or_gt_of_ne h with h' | h'
    · right
      show 1 < P.valuation L ((k : L)⁻¹)
      rw [map_inv₀]
      have h0 : P.valuation L (k : L) ≠ 0 := by simp
      exact one_lt_inv_iff₀.mpr ⟨zero_lt_iff.mpr h0, h'⟩
    · left
      exact h'
  · right
    exact Ideal.dvd_span_singleton.mpr h

theorem eq_inf (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ) (k : D.host.Eˣ)
    (x y : (AE D)ˣ) (hxy : Units.map (incA D).toMonoidHom k = x * y) (hy : infPart D (y : AE D) = 1)
    (hy' : finPart D (y : AE D) = (1 : Af D.host.F) ⊗ₜ[D.host.F] (k : D.host.E)) :
    ((c x : Circle) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
  obtain ⟨ι, hι1, hι2, hι3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  have hid := GlobalTheory.PlaceIdem.exists_isPlIdem D ι hι1 hι2 hι3
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι hι1 hι2 hid c χ hc
  have hfin := finite_bad k N hN
  have hcomp : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      ι (finPart D (y : AE D)) P = algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E) := by
    intro P
    rw [hy', hι1]
    exact GlobalTheory.CharLocProd.evalAt_algebraMap P (k : D.host.E)
  have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      Valued.v (ι (finPart D (y : AE D)) P) = P.valuation D.host.E (k : D.host.E) := by
    intro P
    rw [hcomp]
    exact GlobalTheory.CharLocProd.val_algebraMap P _
  have hT : ∀ T : Finset (HeightOneSpectrum (𝓞 D.host.E)), hfin.toFinset ⊆ T →
      ((c y : Circle) : ℂ) = ∏ P ∈ T, ((χ.locK P k : ℂˣ) : ℂ) := by
    intro T hsub
    refine hprod y hy T (fun _ => k) (fun P _ => ⟨hval P, ?_⟩) (fun P hP => ?_)
    · rw [hcomp, sub_self, map_zero]
      exact zero_le
    · have hP' : P ∉ hfin.toFinset := fun h => hP (hsub h)
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hP'
      exact ⟨(hval P).trans hP'.1, hP'.2⟩
  have hev : (fun T : Finset (HeightOneSpectrum (𝓞 D.host.E)) =>
      ((χ.inf k : ℂˣ) : ℂ) * ∏ P ∈ T, ((χ.locK P k : ℂˣ) : ℂ)) =ᶠ[Filter.atTop]
      fun _ => ((χ.inf k : ℂˣ) : ℂ) * ((c y : Circle) : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop hfin.toFinset] with T hsub
    rw [hT T hsub]
  have h1 : ((χ.inf k : ℂˣ) : ℂ) * ((c y : Circle) : ℂ) = 1 :=
    tendsto_nhds_unique tendsto_const_nhds ((tendsto_inf_mul_prod χ k).congr' hev)
  have h2 : ((c x : Circle) : ℂ) * ((c y : Circle) : ℂ) = 1 := by
    have h := hc.1.2 k
    rw [hxy, map_mul] at h
    rw [← Circle.coe_mul, h, Circle.coe_one]
  exact mul_right_cancel₀ (Circle.coe_ne_zero _) (h2.trans h1.symm)

private theorem coe_circle_exp_arg_eq_div_norm (z : ℂˣ) :
    ((Circle.exp (Complex.arg (z : ℂ)) : Circle) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := by
  rw [Circle.coe_exp]
  have hn : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr (Units.ne_zero z))
  rw [eq_div_iff hn]
  linear_combination Complex.norm_mul_exp_arg_mul_I (z : ℂ)

set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare GlobalTheory.HeckeFinTrivial in

theorem hasInfExp_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (a : D.what₂.Tau → ℚ), ChrEq c χ → χ.HasInfQ (tauE D) a → ∀ τ, HasInfExp D c τ (a τ) := by
  intro D c χ a hc hχ τ
  obtain ⟨n, hn, hinf⟩ := hχ
  unfold HasInfExp AllSome
  refine ⟨n τ, hn τ, ?_, ?_⟩
  · obtain ⟨⟨θ0, hθ0⟩, -⟩ := GlobalTheory.Member.infiniteAdele_bijective D
    exact ⟨fun ρ => θ0 (tauE D ρ), fun ρ => hθ0 (tauE D ρ)⟩
  intro θ hθ x hx1 hx2
  obtain ⟨-, A, B, hA, -, hAB, hAparts, hBparts⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D

  let e : ℂˣ →* Circle := MonoidHom.mk' (fun z => Circle.exp (Complex.arg (z : ℂ))) (by
    intro z w
    apply Circle.ext
    rw [Circle.coe_mul, coe_circle_exp_arg_eq_div_norm, coe_circle_exp_arg_eq_div_norm, coe_circle_exp_arg_eq_div_norm, Units.val_mul, norm_mul,
      Complex.ofReal_mul, div_mul_div_comm])

  let h : D.what₂.Tau → ((AE D)ˣ →* Circle) := fun ρ =>
    (zpowGroupHom (n ρ)).comp (e.comp (Units.map ((θ ρ).comp (infPart D)).toMonoidHom))
  let g : (AE D)ˣ →* Circle := c.comp A * (∏ ρ, h ρ)⁻¹
  have hcoe : ∀ (z : (AE D)ˣ) (ρ : D.what₂.Tau), ((h ρ z : Circle) : ℂ) =
      (θ ρ (infPart D (z : AE D)) / ((‖θ ρ (infPart D (z : AE D))‖ : ℝ) : ℂ)) ^ (n ρ) := by
    intro z ρ
    show ((Circle.exp (Complex.arg ((Units.map ((θ ρ).comp (infPart D)).toMonoidHom z : ℂˣ) : ℂ)) ^ (n ρ) :
      Circle) : ℂ) = _
    rw [Circle.coe_zpow, coe_circle_exp_arg_eq_div_norm]
    rfl
  have hprodv : ∀ z : (AE D)ˣ, (((∏ ρ, h ρ) z : Circle) : ℂ) = ∏ ρ, ((h ρ z : Circle) : ℂ) := by
    intro z
    rw [MonoidHom.finsetProd_apply]
    exact map_prod Circle.coeHom (fun ρ => h ρ z) Finset.univ
  have hne : ∀ (z : (AE D)ˣ) (ρ : D.what₂.Tau), θ ρ (infPart D (z : AE D)) ≠ 0 := fun z ρ =>
    ((z.isUnit.map (infPart D)).map (θ ρ)).ne_zero
  have hcont_h : ∀ ρ, Continuous (h ρ) := by
    intro ρ
    apply continuous_induced_rng.mpr
    show Continuous fun z : (AE D)ˣ => ((h ρ z : Circle) : ℂ)
    simp_rw [hcoe]
    have hc1 : Continuous fun z : (AE D)ˣ => θ ρ (infPart D (z : AE D)) :=
      (continuous_comp hθ ρ).comp Units.continuous_val
    have hc2 : Continuous fun z : (AE D)ˣ => ((‖θ ρ (infPart D (z : AE D))‖ : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_norm.comp hc1)
    have hn2 : ∀ z : (AE D)ˣ, ((‖θ ρ (infPart D (z : AE D))‖ : ℝ) : ℂ) ≠ 0 := fun z => by
      exact_mod_cast (norm_ne_zero_iff.mpr (hne z ρ))
    exact (hc1.div hc2 hn2).zpow₀ (n ρ) fun z => Or.inl (div_ne_zero (hne z ρ) (hn2 z))
  have hP : Continuous fun z => (∏ ρ, h ρ) z := by
    simp_rw [MonoidHom.finsetProd_apply]
    exact continuous_finsetProd _ fun ρ _ => hcont_h ρ
  have hg_cont : Continuous g := by
    show Continuous fun z => c (A z) * ((∏ ρ, h ρ) z)⁻¹
    exact (hc.1.1.comp hA).mul hP.inv
  have hg_E : ∀ k : D.host.Eˣ, g (Units.map (incA D).toMonoidHom k) = 1 := by
    intro k
    have hAu : ((c (A (Units.map (incA D).toMonoidHom k)) : Circle) : ℂ) = ((χ.inf k : ℂˣ) : ℂ) := by
      refine eq_inf D c χ hc k _ (B (Units.map (incA D).toMonoidHom k)) (hAB _) (hBparts _).1 ?_
      rw [(hBparts _).2]
      show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
        ((1 : AF D.host.F) ⊗ₜ[D.host.F] (k : D.host.E)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl
    have hθk : ∀ ρ, θ ρ (infPart D ((Units.map (incA D).toMonoidHom k : (AE D)ˣ) : AE D)) =
        tauE D ρ (k : D.host.E) := fun ρ => comp_incA hθ ρ (k : D.host.E)
    apply Circle.ext
    show ((c (A (Units.map (incA D).toMonoidHom k)) * ((∏ ρ, h ρ) (Units.map (incA D).toMonoidHom k))⁻¹ :
      Circle) : ℂ) = ((1 : Circle) : ℂ)
    rw [Circle.coe_mul, Circle.coe_inv, hprodv, hAu, Circle.coe_one]
    simp_rw [hcoe, hθk]
    rw [← hinf k]
    exact mul_inv_cancel₀ (Units.ne_zero _)
  have hg_fin : ∀ z : (AE D)ˣ, infPart D (z : AE D) = 1 → g z = 1 := by
    intro z hz
    have hA1 : A z = 1 := Units.ext (GlobalTheory.PlaceIdem.parts_inj D _ _
      (by rw [(hAparts z).1, hz, Units.val_one, map_one]) (by rw [(hAparts z).2, Units.val_one, map_one]))
    apply Circle.ext
    show ((c (A z) * ((∏ ρ, h ρ) z)⁻¹ : Circle) : ℂ) = ((1 : Circle) : ℂ)
    rw [hA1, map_one, one_mul, Circle.coe_inv, hprodv]
    simp_rw [hcoe, hz, map_one, norm_one, Complex.ofReal_one, div_one, one_zpow, Finset.prod_const_one,
      inv_one, Circle.coe_one]
  have hg1 := eq_one_of_trivial_on_finite D g ⟨hg_cont, hg_E⟩ hg_fin
  have hB1 : B x = 1 := Units.ext (GlobalTheory.PlaceIdem.parts_inj D _ _
    (by rw [(hBparts x).1, Units.val_one, map_one]) (by rw [(hBparts x).2, hx1, Units.val_one, map_one]))
  have hxA : x = A x := by
    have hx := hAB x
    rw [hB1, mul_one] at hx
    exact hx
  have hcx : ((c x : Circle) : ℂ) = (((∏ ρ, h ρ) x : Circle) : ℂ) := by
    have hgx : c (A x) * ((∏ ρ, h ρ) x)⁻¹ = 1 := hg1 x
    rw [← hxA] at hgx
    rw [mul_inv_eq_one.mp hgx]
  rw [hcx, hprodv, Finset.prod_eq_single τ]
  · exact hcoe x τ
  · intro ρ _ hρ
    rw [hcoe, hx2 ρ hρ, norm_one, Complex.ofReal_one, div_one, one_zpow]
  · intro hτ
    exact absurd (Finset.mem_univ τ) hτ

end GlobalTheory.HeckeInfExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TprodNeZeroOfNe
section
noncomputable section

open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.Contr

open GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels

section Hilbert

variable {H₁ H₂ FF : Type}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
  [NormedAddCommGroup FF] [InnerProductSpace ℂ FF] [CompleteSpace FF]

omit [CompleteSpace H₁] [CompleteSpace FF] in

theorem norm_isoBilin {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) (x : H₁) (y : H₂) :
    ‖Tm x y‖ = ‖x‖ * ‖y‖ := by
  have h := hI x x y y
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← mul_pow] at h
  have h2 : ‖Tm x y‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by exact_mod_cast h
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem exists_isContr {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} (hI : IsIsoBilin Tm) :
    ∃ It : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁, IsContr Tm It := by
  let L : H₂ → (H₁ →L[ℂ] FF) := fun y =>
    (Tm.flip y).mkContinuous ‖y‖ fun x => by simp [norm_isoBilin hI, mul_comm]
  let f : FF → H₂ → H₁ := fun φ y => ContinuousLinearMap.adjoint (L y) φ
  have hf : ∀ φ y x, ⟪x, f φ y⟫_ℂ = ⟪Tm x y, φ⟫_ℂ := fun φ y x => by
    simp only [f, ContinuousLinearMap.adjoint_inner_right]
    rfl
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) f ?_ ?_ ?_ ?_, hf⟩
  · intro a b y
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, RingHom.id_apply]
  · intro a y z
    exact ext_inner_left ℂ fun x => by simp only [inner_add_right, hf, map_add, inner_add_left]
  · intro c a y
    exact ext_inner_left ℂ fun x => by simp only [inner_smul_right, hf, map_smul, inner_smul_left]

omit [CompleteSpace H₁] [CompleteSpace FF] in

theorem isContr_unique {Tm : H₁ →ₗ[ℂ] H₂ →ₗ[ℂ] FF} {It It' : FF →ₗ[ℂ] H₂ →ₛₗ[starRingEnd ℂ] H₁}
    (h : IsContr Tm It) (h' : IsContr Tm It') : It = It' := by
  ext φ y
  exact ext_inner_left ℂ fun x => by rw [h, h']

end Hilbert

theorem contrHilbert : ContrHilbert := by
  intro H₁ H₂ FF _ _ _ _ _ _ _ _ _ G₁ G₂ _ _ π₁ π₂ ρ Tm hI hE
  obtain ⟨It, hIt⟩ := exists_isContr hI
  exact ⟨⟨It, hIt, fun It' h' => isContr_unique h' hIt⟩, fun It' h' => contrProps_of hI hE h'⟩

theorem tprod_ne_zero_of_ne {ι : Type} [Fintype ι] {B : ι → Type} [∀ τ, AddCommGroup (B τ)]
    [∀ τ, Module ℂ (B τ)] (w : ∀ τ, B τ) (hw : ∀ τ, w τ ≠ 0) : PiTensorProduct.tprod ℂ w ≠ 0 := by
  classical
  have : ∀ τ, ∃ f : Module.Dual ℂ (B τ), f (w τ) ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hw τ ((Module.forall_dual_apply_eq_zero_iff ℂ (w τ)).1 hc)
  choose f hf using this
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap f)) h
  simp [Finset.prod_eq_zero_iff, hf] at this

theorem contrTensor : ContrTensor := by
  intro ι _ σ Var e A B _ _ _ _ Itl
  classical
  have hinj : ∀ τ, Function.Injective fun s : σ τ => e ⟨τ, s⟩ := fun τ =>
    e.injective.comp sigma_mk_injective
  let r : (Var →₀ ℕ) → ∀ τ, σ τ →₀ ℕ := fun m τ => m.comapDomain (fun s => e ⟨τ, s⟩) (hinj τ).injOn
  let It : MvPolynomial Var ℂ →ₗ[ℂ] (⨂[ℂ] τ, A τ) →ₗ[ℂ] ⨂[ℂ] τ, B τ :=
    (MvPolynomial.basisMonomials Var ℂ).constr ℂ fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1)
  have hr : ∀ m : ∀ τ, σ τ →₀ ℕ, r (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩) = m := by
    intro m
    funext τ
    ext s
    simp only [r, Finsupp.comapDomain_apply, Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single τ]
    · exact Finsupp.mapDomain_apply (hinj τ) _ _
    · intro τ' _ hne
      apply Finsupp.mapDomain_notin_range
      rintro ⟨s', hs'⟩
      exact hne (congrArg Sigma.fst (e.injective hs'))
    · simp
  have key : It.compMultilinearMap ((MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial Var ℂ)).compLinearMap
      fun τ => (MvPolynomial.rename (fun s : σ τ => e ⟨τ, s⟩)).toLinearMap) =
      (PiTensorProduct.mapMultilinear ℂ A B).compLinearMap Itl := by
    apply Module.Basis.ext_multilinear fun τ => MvPolynomial.basisMonomials (σ τ) ℂ
    intro m
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials,
      MvPolynomial.rename_monomial, PiTensorProduct.mapMultilinear_apply]
    rw [← MvPolynomial.monomial_sum_one]
    have := (MvPolynomial.basisMonomials Var ℂ).constr_basis ℂ (fun m =>
      PiTensorProduct.map fun τ => Itl τ (MvPolynomial.monomial (r m τ) 1))
      (∑ τ, (m τ).mapDomain fun s => e ⟨τ, s⟩)
    rw [hr] at this
    simpa [It] using this
  have hT : IsTensorIt e Itl It := by
    intro P v
    have := congrArg (fun F => F P (PiTensorProduct.tprod ℂ v)) key
    simpa using this
  refine ⟨It, hT, fun hne h0 => ?_⟩
  have : ∀ τ, ∃ P v, Itl τ P v ≠ 0 := fun τ => by
    by_contra hc
    push_neg at hc
    exact hne τ (LinearMap.ext fun P => LinearMap.ext fun v => hc P v)
  choose P v hPv using this
  apply tprod_ne_zero_of_ne _ hPv
  rw [← hT P v, h0]
  rfl

theorem contraction : Contraction := ⟨contrHilbert, contrTensor⟩

theorem contrTensorModels : ContrTensorModels := contrTensorModels_of contrTensor

end GlobalTheory.Contr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistPlacesLocalDatumBlockTriangularLawStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlaces_localDatum_blockTriangular_law : ∀ (D : D7) (a b r : ℕ), r ≤ a → r ≤ b → ∀ (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Q, gS PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, gT PP ∈ blockTri (blk2 r)) → (∀ PP ∈ Q, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Q, (((ξ PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y' = (∏ PP ∈ Q, (((ξ PP (dBlk (blk2 r) 1 (gS PP)) : ℂˣ) : ℂ)⁻¹ * ((ξ PP (dBlk (blk2 r) 1 (gT PP)) : ℂˣ) : ℂ))) ^ k * omegaQ Q r ξ k y := by
  first | exact @GlobalTheory.OmegaTwistLaw.omegaQ_blockTri | exact GlobalTheory.OmegaTwistLaw.omegaQ_blockTri | (intros; apply GlobalTheory.OmegaTwistLaw.omegaQ_blockTri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesLocalDatumBlockTriangularLawStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_localDatum_blockTriangular_law : ∀ (D : D7) (a b r t j : ℕ) (ha : r ≤ a) (hb : r ≤ b), a = r + j * t → b = r + (j + 1) * t → ∀ (Pg Q : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (gS : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP)) (gT : ∀ PP : Pl D.host.E, GL (Fin b) (kP PP)) (y y' : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)), (∀ PP ∈ Pg, gS PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, gT PP ∈ blockTri (blkOf r t)) → (∀ PP ∈ Pg, upperLeftBlock ha (gS PP) = upperLeftBlock hb (gT PP)) → (∀ PP ∈ Pg, y' PP = ((gT PP)⁻¹).val * y PP * (gS PP).val) → (∏ PP ∈ Pg, (((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gS PP)) : ℂˣ) : ℂ) * ((χ (j + 1) PP (Matrix.GeneralLinearGroup.det (gT PP)) : ℂˣ) : ℂ)⁻¹)) * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y' = ((∏ PP ∈ Pg, ∏ c ∈ Finset.range j, χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gS PP)) : ℂˣ) : ℂ) * ((∏ PP ∈ Pg, ∏ c ∈ Finset.range (j + 1), χ (c + 1) PP (dBlk (blkOf r t) (c + 1) (gT PP)) : ℂˣ) : ℂ)⁻¹ * omegaG (datY a r t j ha Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) (χ (j + 1)) y := by
  first | exact @GlobalTheory.StepLaw.TypeDatum.omegaG_law | exact GlobalTheory.StepLaw.TypeDatum.omegaG_law | (intros; apply GlobalTheory.StepLaw.TypeDatum.omegaG_law <;> assumption)
end

