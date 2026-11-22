import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1798
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0195
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1795
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantLinearFormLocalExistence
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

open MeasureTheory ComplexConjugate
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LagLocForm

section
variable {F : Type} [Field F] [NumberField F] {v : Pl F}

theorem schr_adj (ψ₀ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ₀) {κ : Type} [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure]
    (w : (κ → Fv F v) × (κ → Fv F v)) (f g : (κ → Fv F v) → ℂ) :
    ∫ y, schr ψ₀ w f y * conj (g y) ∂μ = ∫ y, f y * conj (schr ψ₀ (-w) g y) ∂μ := by
  have h1 : ∀ s, conj (ψ₀ s) = ψ₀ (-s) := by
    intro s
    have h := GlobalTheory.norm_addChar_nonarch ψ₀ hψ s
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h]
    simp
  rw [← integral_add_right_eq_self (fun y => f y * conj (schr ψ₀ (-w) g y)) w.1]
  congr 1
  funext y
  simp only [schr, Prod.fst_neg, Prod.snd_neg, map_mul, h1, add_neg_cancel_right]
  have h2 : ⅟(2 : Fv F v) * 2 = 1 := invOf_mul_self 2
  have e : -((y + w.1) ⬝ᵥ -w.2 + ⅟(2 : Fv F v) * (-w.1 ⬝ᵥ -w.2)) = y ⬝ᵥ w.2 + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ w.2) := by
    simp only [add_dotProduct, dotProduct_neg, neg_dotProduct, neg_neg]
    linear_combination (-(w.1 ⬝ᵥ w.2)) * h2
  rw [e]; ring

theorem ip_self_ne {κ : Type} [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure] (g : (κ → Fv F v) → ℂ) (hg : g ∈ SB (κ → Fv F v))
    (h0 : g ≠ 0) : ∫ y, g y * conj (g y) ∂μ ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  have e : (fun y => g y * conj (g y)) = fun y => ((Complex.normSq (g y) : ℝ) : ℂ) := by
    funext y; exact Complex.mul_conj (g y)
  rw [e, integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine ne_of_gt ?_
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x)
    (Complex.continuous_normSq.comp hg.1.continuous) (hg.2.comp_left (g := Complex.normSq) (map_zero _))
    (fun y => Complex.normSq_nonneg _) ?_
  simpa using hx

end

theorem lagr_local_form : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    (Λ Γ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (vac : (κ → Fv F v) → ℂ), Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    (∀ w ∈ Λ, ∀ w' ∈ Λ, w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2 = 0) →
    IsOpen (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) → IsCompact (Γ : Set ((κ → Fv F v) × (κ → Fv F v))) →
    (∀ w, w ∈ Γ ↔ ∀ γ ∈ Γ, ψ₀ (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) = 1) →
    vac ∈ SB (κ → Fv F v) → vac ≠ 0 → (∀ γ ∈ Γ, ∃ c : ℂ, schr ψ₀ γ vac = c • vac) → (∀ γ ∈ Γ ⊓ Λ, schr ψ₀ γ vac = vac) →
    ∃ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ Λ, ∀ φ ∈ SB (κ → Fv F v), l (schr ψ₀ w φ) = l φ) ∧ l vac ≠ 0 := by
  intro F _ _ v ψ₀ κ _ Λ Γ vac hψ hcond hiso hΓo hΓc hdual hvSB hv0 heig hfix
  letI : MeasurableSpace (κ → Fv F v) := borel _
  haveI : BorelSpace (κ → Fv F v) := ⟨rfl⟩
  let μ : Measure (κ → Fv F v) := Measure.addHaar
  let c : ((κ → Fv F v) → ℂ) → ((κ → Fv F v) × (κ → Fv F v)) → ℂ :=
    fun φ w => ∫ y, schr ψ₀ w φ y * conj (vac y) ∂μ
  have hc : ∀ (φ : (κ → Fv F v) → ℂ) (w : (κ → Fv F v) × (κ → Fv F v)), c φ w = ∫ y, schr ψ₀ w φ y * conj (vac y) ∂μ := fun _ _ => rfl
  have schr_zero : ∀ φ : (κ → Fv F v) → ℂ, schr ψ₀ 0 φ = φ := by
    intro φ; funext x; simp [schr]
  have schr_add : ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (φ₁ φ₂ : (κ → Fv F v) → ℂ), schr ψ₀ w (φ₁ + φ₂) = schr ψ₀ w φ₁ + schr ψ₀ w φ₂ := by
    intro w φ₁ φ₂; funext x; simp [schr, mul_add]
  have schr_smul : ∀ (w : (κ → Fv F v) × (κ → Fv F v)) (a : ℂ) (φ : (κ → Fv F v) → ℂ), schr ψ₀ w (a • φ) = a • schr ψ₀ w φ := by
    intro w a φ; funext x; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
  have comp_iso : ∀ w ∈ Λ, ∀ w' ∈ Λ, ∀ φ : (κ → Fv F v) → ℂ, schr ψ₀ w (schr ψ₀ w' φ) = schr ψ₀ (w + w') φ := by
    intro w hw w' hw' φ
    rw [GlobalTheory.ThetaQuasiRat.schr_schr, hiso w hw w' hw', mul_zero, AddChar.map_zero_eq_one, one_smul]

  have hconst : ∀ φ : (κ → Fv F v) → ℂ, ∀ l ∈ Λ, ∀ γ ∈ Γ, γ ∈ Λ → c φ (l + γ) = c φ l := by
    intro φ l hl γ hγ hγΛ
    rw [hc, hc, add_comm, ← comp_iso γ hγΛ l hl, schr_adj ψ₀ hψ μ γ (schr ψ₀ l φ) vac,
      hfix (-γ) (AddSubgroup.mem_inf.2 ⟨Γ.neg_mem hγ, Λ.neg_mem hγΛ⟩)]
  let H : AddSubgroup Λ := Γ.addSubgroupOf Λ
  let ct : ((κ → Fv F v) → ℂ) → Λ ⧸ H → ℂ := fun φ =>
    Quotient.lift (s := QuotientAddGroup.leftRel H) (fun l : Λ => c φ l) (by
      intro a b hab
      have hab : -a + b ∈ H := QuotientAddGroup.leftRel_apply.1 hab
      rw [AddSubgroup.mem_addSubgroupOf] at hab
      have e : (b : (κ → Fv F v) × (κ → Fv F v)) = a + ((-a + b : Λ) : (κ → Fv F v) × (κ → Fv F v)) := by
        simp
      show c φ a = c φ b
      rw [e, hconst φ a a.2 _ hab (-a + b).2])
  have hct : ∀ (φ : (κ → Fv F v) → ℂ) (l : Λ), ct φ (l : Λ ⧸ H) = c φ l := fun _ _ => rfl

  have hfin : ∀ φ ∈ SB (κ → Fv F v), (Function.support (ct φ)).Finite := by
    intro φ hφ
    obtain ⟨C, hCc, hC⟩ := GlobalTheory.T.schwartzBruhat_matrixCoefficient_compactSupport_finitePlace v ψ₀ κ μ hψ hcond φ hφ vac hvSB
    obtain ⟨t, ht⟩ := hCc.elim_finite_subcover (fun i : C => (fun z => z - (i : (κ → Fv F v) × (κ → Fv F v))) ⁻¹' Γ)
      (fun i => hΓo.preimage (continuous_sub_right _))
      (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, by simp [Set.mem_preimage, sub_self, zero_mem]⟩)
    refine Set.Finite.subset (t.finite_toSet.biUnion fun i _ =>
      (Set.Subsingleton.finite (s := (QuotientAddGroup.mk : Λ → Λ ⧸ H) ''
        {l : Λ | (l : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ}) ?_)) ?_
    · rintro _ ⟨l₁, h₁, rfl⟩ _ ⟨l₂, h₂, rfl⟩
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have := Γ.sub_mem (show (l₂ : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ from h₂)
        (show (l₁ : (κ → Fv F v) × (κ → Fv F v)) - i ∈ Γ from h₁)
      simpa [sub_sub_sub_cancel_right, neg_add_eq_sub] using this
    · intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H l =>
        rw [Function.mem_support, hct] at hq
        have hlC := hC _ hq
        obtain ⟨i, hi, hli⟩ := Set.mem_iUnion₂.1 (ht hlC)
        exact Set.mem_biUnion hi ⟨l, hli, rfl⟩
  have hint : ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v),
      Integrable (fun y => schr ψ₀ w φ y * conj (vac y)) μ := by
    intro w φ hφ
    have h1 := GlobalTheory.SchrSBFin.schr_mem_SB v ψ₀ hψ w φ hφ
    exact (h1.1.continuous.mul (Complex.continuous_conj.comp hvSB.1.continuous)).integrable_of_hasCompactSupport
      (hvSB.2.comp_left (g := conj) (map_zero _)).mul_left
  have ct_add : ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ → Fv F v), ct (φ₁ + φ₂) = ct φ₁ + ct φ₂ := by
    intro φ₁ h₁ φ₂ h₂
    funext q
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      simp only [hct, Pi.add_apply, hc, schr_add, add_mul]
      exact integral_add (hint _ _ h₁) (hint _ _ h₂)
  have ct_smul : ∀ (a : ℂ) (φ : (κ → Fv F v) → ℂ), ct (a • φ) = a • ct φ := by
    intro a φ
    funext q
    induction q using QuotientAddGroup.induction_on with
    | H m =>
      simp only [hct, Pi.smul_apply, smul_eq_mul, hc, schr_smul, mul_assoc]
      exact integral_const_mul a _
  let l₀ : SB (κ → Fv F v) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∑ᶠ q, ct φ q
      map_add' := fun φ₁ φ₂ => by
        show ∑ᶠ q, ct ((φ₁ : (κ → Fv F v) → ℂ) + φ₂) q = ∑ᶠ q, ct φ₁ q + ∑ᶠ q, ct φ₂ q
        rw [ct_add _ φ₁.2 _ φ₂.2]
        exact finsum_add_distrib (hfin _ φ₁.2) (hfin _ φ₂.2)
      map_smul' := fun a φ => by
        show ∑ᶠ q, ct (a • (φ : (κ → Fv F v) → ℂ)) q = (RingHom.id ℂ) a • ∑ᶠ q, ct φ q
        rw [ct_smul, RingHom.id_apply, smul_eq_mul, mul_finsum]
        rfl }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend l₀
  have hl' : ∀ φ (hφ : φ ∈ SB (κ → Fv F v)), l φ = ∑ᶠ q, ct φ q := fun φ hφ => LinearMap.congr_fun hl ⟨φ, hφ⟩
  refine ⟨l, fun w hw φ hφ => ?_, ?_⟩
  · rw [hl' _ (GlobalTheory.SchrSBFin.schr_mem_SB v ψ₀ hψ w φ hφ), hl' φ hφ]
    have e : ct (schr ψ₀ w φ) = fun q => ct φ (q + ((⟨w, hw⟩ : Λ) : Λ ⧸ H)) := by
      funext q
      induction q using QuotientAddGroup.induction_on with
      | H m =>
        rw [← QuotientAddGroup.mk_add, hct, hct, hc, hc, comp_iso m m.2 w hw]
        rfl
    rw [e]
    exact finsum_comp_equiv (Equiv.addRight _)
  · have hX0 : c vac 0 ≠ 0 := by
      rw [hc, schr_zero]; exact ip_self_ne μ vac hvSB hv0
    have hd : ∀ w, c vac w ≠ 0 → w ∈ Γ := by
      intro w hw
      rw [hdual]
      intro γ hγ
      obtain ⟨a, ha⟩ := heig γ hγ
      have hinv : a • schr ψ₀ (-γ) vac = vac := by
        rw [← schr_smul, ← ha, GlobalTheory.ThetaQuasiRat.schr_schr, neg_add_cancel, schr_zero]
        have : (-γ).1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ (-γ).2 = 0 := by
          simp only [Prod.fst_neg, Prod.snd_neg, neg_dotProduct, dotProduct_neg]; ring
        rw [this, mul_zero, AddChar.map_zero_eq_one, one_smul]
      have ha0 : a ≠ 0 := by
        rintro rfl; apply hv0; rw [← hinv, zero_smul]
      have hneg : schr ψ₀ (-γ) vac = a⁻¹ • vac := by
        rw [← hinv, smul_smul, inv_mul_cancel₀ ha0, one_smul, hinv]
      have key : ∀ w : (κ → Fv F v) × (κ → Fv F v),
          ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a * c vac w = conj a⁻¹ * c vac w := by
        intro w
        have e1 : schr ψ₀ γ (schr ψ₀ w vac) = (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) • schr ψ₀ w vac := by
          have h1 := GlobalTheory.ThetaQuasiRat.schr_schr ψ₀ γ w vac
          have h2 := GlobalTheory.ThetaQuasiRat.schr_schr ψ₀ w γ vac
          rw [ha, schr_smul, add_comm w γ] at h2
          rw [h1, mul_smul, h2, smul_smul, ← AddChar.map_add_eq_mul]
          have h3 : ⅟(2 : Fv F v) * 2 = 1 := invOf_mul_self 2
          have e4 : ⅟(2 : Fv F v) * (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) =
              (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) + ⅟(2 : Fv F v) * (w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2) := by
            linear_combination (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * h3
          rw [e4]
        have e3 : ∫ y, (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) * (schr ψ₀ w vac y * conj (vac y)) ∂μ =
            ∫ y, conj a⁻¹ * (schr ψ₀ w vac y * conj (vac y)) ∂μ := by
          calc ∫ y, (ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) * a) * (schr ψ₀ w vac y * conj (vac y)) ∂μ
              = ∫ y, schr ψ₀ γ (schr ψ₀ w vac) y * conj (vac y) ∂μ := by
                congr 1; funext y; rw [e1, Pi.smul_apply, smul_eq_mul]; ring
            _ = ∫ y, schr ψ₀ w vac y * conj (schr ψ₀ (-γ) vac y) ∂μ := schr_adj ψ₀ hψ μ γ _ vac
            _ = ∫ y, conj a⁻¹ * (schr ψ₀ w vac y * conj (vac y)) ∂μ := by
                congr 1; funext y; rw [hneg, Pi.smul_apply, smul_eq_mul, map_mul]; ring
        rw [integral_const_mul, integral_const_mul] at e3
        rw [hc]; exact e3
      have haa : a = conj a⁻¹ := by
        have k0 := key 0
        simp only [Prod.snd_zero, Prod.fst_zero, dotProduct_zero, zero_dotProduct, sub_zero,
          AddChar.map_zero_eq_one, one_mul] at k0
        exact mul_right_cancel₀ hX0 k0
      have hk := key w
      rw [← haa] at hk
      have hψω : ψ₀ (γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) = 1 := by
        have := mul_right_cancel₀ hw hk
        exact mul_right_cancel₀ ha0 (by rw [this, one_mul])
      rw [show w.1 ⬝ᵥ γ.2 - γ.1 ⬝ᵥ w.2 = -(γ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ γ.2) by ring, AddChar.map_neg_eq_inv, hψω, inv_one]
    rw [hl' vac hvSB, finsum_eq_single _ (0 : Λ ⧸ H)]
    · show ct vac ((0 : Λ) : Λ ⧸ H) ≠ 0
      rw [hct]; simpa using hX0
    · intro q hq
      induction q using QuotientAddGroup.induction_on with
      | H m =>
        by_contra hm
        rw [hct] at hm
        exact hq ((QuotientAddGroup.eq_zero_iff m).2 (AddSubgroup.mem_addSubgroupOf.2 (hd m hm)))

end GlobalTheory.LagLocForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDeterminantIndexIdealMapInjectiveEqColonStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeDeterminantIndexIdeal_map_injective_eq_colon : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    [IsScalarTower (𝓞 F) F V] (p : ℕ) (φ : (Fin p → F) →ₗ[F] V), Function.Injective φ →
    ∀ (L N : Submodule (𝓞 F) (Fin p → F)),
    GlobalTheory.FlatCM.idx F p (L.map (φ.restrictScalars (𝓞 F))) (N.map (φ.restrictScalars (𝓞 F))) =
      (GlobalTheory.IdxTensor.dets F p N).colon (GlobalTheory.IdxTensor.dets F p L : Set F) := by
  first | exact @GlobalTheory.IdxMap.idx_map_eq_colon_dets | exact GlobalTheory.IdxMap.idx_map_eq_colon_dets | (intros; apply GlobalTheory.IdxMap.idx_map_eq_colon_dets <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerSkewConjMemThetaFunctionsStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeIntertwiner_skewConj_mem_thetaFunctions : ∀ (D : D7) (δ t0 : ℂ) (hc : Crv D ⊤ δ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) (a d : ℕ) (hd : Even d) (e0 : VC D a d → ℂ) (hv : oddE0 D ⊤ δ t0 a d e0) (W : WeilO D ⊤ δ a d e0) (hep : W.ep = 1) (hep' : W.ep' = 1) (𝔪 : Ideal (𝓞 D.host.E)) (hm : 𝔪 ≠ ⊥) (hcop : 𝔪 ⊔ D.host.conj • 𝔪 = ⊤) (hcond : ∀ u : (AE D)ˣ, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) (o : ℕ) (ho : o + a = d), (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • 𝔪) d)) e0) ∈ TT D (tor0 D ⊤ δ) a d := by
  first | exact @GlobalTheory.BotPairSmall.iop_skew_conj_mem_TT | exact GlobalTheory.BotPairSmall.iop_skew_conj_mem_TT | (intros; apply GlobalTheory.BotPairSmall.iop_skew_conj_mem_TT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePairingTrivialMatricesSubMemStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticePairingTrivialMatrices_sub_mem : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ Y h : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), Y ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → Y + h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ → h ∈ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂ := by
  first | exact @GlobalTheory.VacShapeBd.bd_sub | exact GlobalTheory.VacShapeBd.bd_sub | (intros; apply GlobalTheory.VacShapeBd.bd_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqPrincipalRowsOfType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.LevelRowsPrincipal

theorem pLevE_of : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → R.PLevE F := by
  intro hCusp hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hC hEx hJunk hGE hPos hScal hB hRT
  have hBlock : (R.toCx3 F).zs.InBlock := GlobalTheory.T.adjointLift_range_le_goodBlock_eigenspaces hCusp R F hLI hOk hC hEx hGE
  have hCarry : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c := GlobalTheory.T.thetaLift_carrying_of_base_tuple_rows hCusp hHowe R F hLI hOk hC hEx hJunk hGE hPos
  have hSpan : (⨆ p, R.EEp3 p) = ⊤ :=
    GlobalTheory.T.iSup_eEp3_eq_whole_space_of_weakCharacterisation R F hC hEx (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) hCarry
  have hTop := GlobalTheory.T.EEg3_eq_univ_of_weakCharacterisation R F hOk hC hSpan hScal hB hRT hBlock
  obtain ⟨h0, h1⟩ := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
  refine ⟨?_, ?_⟩
  · show (R.toCx3 F).EEl false = _ ⊓ _
    rw [hTop, top_inf_eq, h0]
  · show (R.toCx3 F).EEl true = _ ⊓ _
    rw [hTop, top_inf_eq, h1]

end GlobalTheory.LevelRowsPrincipal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsOrthogonalSumOfParts
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.RowsSum3

theorem rowTypePart_map_finiteGroup_le {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (hC : R.WeakCharacterisation F) (hE : R.toRealDat.ExAt) (p : A3.fam3.base3.Ix) (g : G) :
    (R.EEp3 p).map (R.gE g) ≤ R.EEp3 p := by
  obtain ⟨hcore, hSF, hEE, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hC hE
  simp only [RealDat3.EEp3, Submodule.map_iSup]
  refine iSup_le fun c => iSup_le fun hc => ?_
  refine le_trans ?_ (le_iSup₂_of_le c hc le_rfl)
  rw [hEE]
  exact GlobalTheory.RowPartStable.map_gE_le (s := 0) R.toRealDat F.lv2 hcore _ hSF c g

theorem iSup_EEp_inf_typeSp3 {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (hC : R.WeakCharacterisation F) (hE : R.toRealDat.ExAt) (htop : (⨆ p, R.EEp3 p) = ⊤) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) :
    (⨆ p, (R.toCx3 F).EEp p ⊓ typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ) = typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ := by
  have hsup : (⨆ p, (R.toCx3 F).EEp p) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x ∈ ⨆ p, R.EEp3 p := htop ▸ Submodule.mem_top
    exact Submodule.iSup_induction R.EEp3
      (motive := fun y => (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈ ⨆ p, (R.toCx3 F).EEp p) hx
      (fun p y hy => Submodule.mem_iSup_of_mem (p := (R.toCx3 F).EEp) p hy) (Submodule.zero_mem _)
      fun y z hy hz => Submodule.add_mem _ hy hz
  have hst : ∀ p g, ((R.toCx3 F).EEp p).map (R.gEx F g) ≤ (R.toCx3 F).EEp p := by
    rintro p g _ ⟨x, hx, rfl⟩
    exact rowTypePart_map_finiteGroup_le R F hC hE p g ⟨_, hx, rfl⟩
  have h := GlobalTheory.iSup_stable_inf_typeSpace (R.gEx F) P ((Units.map (A3.A.fam.v0.embedding : D.what₂.LL →+* ℂ).toMonoidHom).comp ψ)
    (R.toCx3 F).EEp (fun _ => True) hst
  simp only [iSup_pos, hsup, top_inf_eq] at h
  exact h.symm

theorem partsE : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ b, (R.toCx3 F).PartsE b := by
  intro hCR hHU D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hC hE hJ hOkH hPG hPos hkl hB b
  have hcar := GlobalTheory.T.thetaLift_carrying_of_base_tuple_rows hCR hHU R F hLI hOk hC hE hJ hPG hPos
  have htop := GlobalTheory.T.iSup_eEp3_eq_whole_space_of_weakCharacterisation R F hC hE (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCR R.toRealDat) hcar
  have hor := GlobalTheory.T.orthogonal_rowParts_of_distinct_types R F hOk hC hOkH hkl hB
  refine ⟨fun p q hpq e he e' he' => ?_, ?_⟩
  · exact (congrArg (cj _) (hor p q hpq _ he.1 _ he'.1)).trans (map_zero _)
  · obtain ⟨h0, h1⟩ := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
    cases b
    · rw [h0]; exact iSup_EEp_inf_typeSp3 R F hC hE htop _ _
    · rw [h1]; exact iSup_EEp_inf_typeSp3 R F hC hE htop _ _

end GlobalTheory.RowsSum3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinePairExtensionCosSqBoundStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_pair_extension_cosSq_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (V L Q L' Q' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V) (m' : V ⟶ Q') (w' : l' ≫ m' = 0) (hS : (ShortComplex.mk l m w).ShortExact) (hS' : (ShortComplex.mk l' m' w').ShortExact) (hL : IsVB L 1) (hQ : IsVB Q 1) (hL' : IsVB L' 1) (hQ' : IsVB Q' 1) (hl : IsSubbundle l) (hl' : IsSubbundle l') (h : Met p σ V (1 + 1)), h.IsCInf → ∀ v : CxPts p σ → ℝ, IsCosSq h l l' v → ∀ n : ℕ, total (fun (c : AlgChart p σ 1) y => v y ^ (n + 1) * (c.chernDens (h.restrict hl hL).detWeight y - c.chernDens (h.restrict hl' hL').detWeight y) + (n + 1) * v y ^ n * (1 - v y) * (Met.bcDens (S := ShortComplex.mk l m w) h hS hL hQ c y - Met.bcDens (S := ShortComplex.mk l' m' w') h hS' hL' hQ' c y)) = 0 := by
  first | exact @GlobalTheory.CurveDens.green_cosSq | exact GlobalTheory.CurveDens.green_cosSq | (intros; apply GlobalTheory.CurveDens.green_cosSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicHaarSplitArchimedeanFiniteStatement
section
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_adelicHaar_split_archimedean_finite : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (μ : Measure (κ → AF F)) [μ.IsAddHaarMeasure] (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure],
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ (fi : (κ → mixedEmbedding.mixedSpace F) → ℝ≥0∞) (g : (κ → Af F) → ℝ≥0∞),
      Measurable fi → Measurable g →
        ∫⁻ x, fi (fun i => evI F (x i)) * g (fun i => sndA F (x i)) ∂μ = c * ((∫⁻ z, fi z ∂μi) * ∫⁻ y, g y ∂μf) := by
  first | exact @GlobalTheory.WeilAdm.HaarSplit.lintegral_split_mul | exact GlobalTheory.WeilAdm.HaarSplit.lintegral_split_mul | (intros; apply GlobalTheory.WeilAdm.HaarSplit.lintegral_split_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFiniteAdelicFactorOffPlaceStatement
section
open scoped Matrix GlobalTheory.VacAny ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_finiteAdelic_factor_offPlace : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] [MeasurableSpace (κ → Af F)] [BorelSpace (κ → Af F)]
    (w : HeightOneSpectrum (𝓞 F)) [MeasurableSpace (κ → Fv F w)] [BorelSpace (κ → Fv F w)]
    (μf : Measure (κ → Af F)) [μf.IsAddHaarMeasure] (μw : Measure (κ → Fv F w)) [μw.IsAddHaarMeasure],
    μw {t | ∀ i, t i ∈ w.adicCompletionIntegers F} = 1 →
    ∀ (K : (κ → Af F) → ℝ≥0∞), Measurable K → (∀ (y : κ → Af F) (t : κ → Fv F w), K (fun i => y i + singleFin w (t i)) = K y) →
    ∀ (g : (κ → Fv F w) → ℝ≥0∞), Measurable g →
      ∫⁻ y, g (fun i => evalV F w (y i)) * K y ∂μf =
        (∫⁻ t, g t ∂μw) * ∫⁻ y, {t : κ → Fv F w | ∀ i, t i ∈ w.adicCompletionIntegers F}.indicator 1 (fun i => evalV F w (y i)) * K y ∂μf := by
  first | exact @GlobalTheory.HaarFactorOffPlace.lintegral_evalV_mul_shiftInvariant | exact GlobalTheory.HaarFactorOffPlace.lintegral_evalV_mul_shiftInvariant | (intros; apply GlobalTheory.HaarFactorOffPlace.lintegral_evalV_mul_shiftInvariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdentityOfTensorHeisenbergEigenStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localIdentity_of_tensorHeisenbergEigen : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : Darboux B κ) (ψ : AddChar (AF F) ℂ) (γ : W) (f : (κ → Fv F v) → ℂ)
    (R : (κ → AF F) → ℂ) (c : ℂ), At (evFin F v) γ → (∀ x z, At (evFin F v) z → R (x + z) = R x) →
    ∀ x₀, R x₀ ≠ 0 → co.rho ψ γ (tens (evFin F v) f R) = c • tens (evFin F v) f R →
    ∀ ξ : κ → Fv F v, GlobalTheory.LatVac.psiAt ψ v (ξ ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2 +
        (2 : Fv F v)⁻¹ * ((GlobalTheory.LatVac.locCo co v γ).1 ⬝ᵥ (GlobalTheory.LatVac.locCo co v γ).2)) *
      f (ξ + (GlobalTheory.LatVac.locCo co v γ).1) = c * f ξ := by
  first | exact @GlobalTheory.DblVacEigen.local_identity_of_tens_eigen | exact GlobalTheory.DblVacEigen.local_identity_of_tens_eigen | (intros; apply GlobalTheory.DblVacEigen.local_identity_of_tens_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
section
noncomputable section

open NumberField

namespace GlobalTheory.VacRead

def cE (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {x | ∃ c ∈ cc, x = ((c : D.host.K) : D.host.E)}

def bInv (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {y | ∃ α ∈ cE D cc, ∃ γ ∈ cE D D.host.ccK,
    y = r * D.host.conj α * γ / (Ideal.absNorm cc : D.host.E)}

def lsB (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ) : GlobalTheory.InertSign.Lat D a :=
  Submodule.pi Set.univ fun _ => bInv D cc r

theorem mem_lsB {D : Formalism.BasicNotions.D7} {cc : Ideal (𝓞 D.host.K)} {r : D.host.E} {a : ℕ} {y : Fin a → D.host.E} :
    y ∈ lsB D cc r a ↔ ∀ i, y i ∈ bInv D cc r := by
  simp [lsB, Submodule.mem_pi]

end GlobalTheory.VacRead
end
end

