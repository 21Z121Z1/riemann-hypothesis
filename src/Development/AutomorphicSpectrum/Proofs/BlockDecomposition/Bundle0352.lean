import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0340
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0341
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import GroundTheory.AutomorphicForms.Bundle0020
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0322
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfCommuteOfSeparable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0344
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0342
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0326

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralProdSubgroup
section
noncomputable section

open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotProduct

variable {G₁ G₂ : Type} [Group G₁] [Group G₂] [MeasurableSpace G₁] [MeasurableSpace G₂]
  [MeasurableMul₂ G₁] [MeasurableMul₂ G₂] {T₁ : Subgroup G₁} {T₂ : Subgroup G₂}
  {ν₁ : Measure T₁} [SFinite ν₁] {ν₂ : Measure T₂} [SFinite ν₂] {ν : Measure (T₁.prod T₂)}

def split (t : T₁.prod T₂) : T₁ × T₂ :=
  (⟨t.1.1, (Subgroup.mem_prod.1 t.2).1⟩, ⟨t.1.2, (Subgroup.mem_prod.1 t.2).2⟩)

theorem measurable_split : Measurable (split : T₁.prod T₂ → T₁ × T₂) :=
  ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
    ((measurable_snd.comp measurable_subtype_coe).subtype_mk)

theorem lintegral_prod_subgroup (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : Measurable ρ) (g : G₁ × G₂) :
    ∫⁻ h : T₁.prod T₂, ρ ((h : G₁ × G₂) * g) ∂ν =
      ∫⁻ t₁ : T₁, ∫⁻ t₂ : T₂, ρ ((t₁ : G₁) * g.1, (t₂ : G₂) * g.2) ∂ν₂ ∂ν₁ := by
  have hm : Measurable fun p : T₁ × T₂ => ρ ((p.1 : G₁) * g.1, (p.2 : G₂) * g.2) :=
    hρ.comp ((((measurable_subtype_coe.comp measurable_fst).mul_const g.1)).prodMk
      ((measurable_subtype_coe.comp measurable_snd).mul_const g.2))
  rw [← lintegral_prod _ hm.aemeasurable, ← hν, lintegral_map hm measurable_split]
  rfl

theorem normaliser_fst (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : IsQuotNormaliser (T₁.prod T₂) ν ρ) :
    IsQuotNormaliser T₁ ν₁ fun x => ∫⁻ t₂ : T₂, ρ (x, (t₂ : G₂)) ∂ν₂ := by
  refine ⟨Measurable.lintegral_prod_right' (f := fun p : G₁ × T₂ => ρ (p.1, (p.2 : G₂)))
    (hρ.1.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))), fun g => ?_⟩
  have h := hρ.2 (g, 1)
  rw [lintegral_prod_subgroup hν hρ.1] at h
  simpa using h

theorem normaliser_snd (hν : ν.map split = ν₁.prod ν₂) {ρ : G₁ × G₂ → ℝ≥0∞}
    (hρ : IsQuotNormaliser (T₁.prod T₂) ν ρ) :
    IsQuotNormaliser T₂ ν₂ fun x => ∫⁻ t₁ : T₁, ρ ((t₁ : G₁), x) ∂ν₁ := by
  refine ⟨Measurable.lintegral_prod_right' (f := fun p : G₂ × T₁ => ρ ((p.2 : G₁), p.1))
    (hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk measurable_fst)), fun g => ?_⟩
  have h := hρ.2 (1, g)
  rw [lintegral_prod_subgroup hν hρ.1] at h
  rw [lintegral_lintegral_swap]
  · simpa using h
  · have hm : Measurable fun p : T₂ × T₁ => ρ ((p.2 : G₁), (p.1 : G₂) * g) :=
      hρ.1.comp ((measurable_subtype_coe.comp measurable_snd).prodMk
        ((measurable_subtype_coe.comp measurable_fst).mul_const g))
    exact hm.aemeasurable

theorem normaliser_mul (hν : ν.map split = ν₁.prod ν₂) {ρ₁ : G₁ → ℝ≥0∞} {ρ₂ : G₂ → ℝ≥0∞}
    (h₁ : IsQuotNormaliser T₁ ν₁ ρ₁) (h₂ : IsQuotNormaliser T₂ ν₂ ρ₂) :
    IsQuotNormaliser (T₁.prod T₂) ν fun x => ρ₁ x.1 * ρ₂ x.2 := by
  have hm : Measurable fun x : G₁ × G₂ => ρ₁ x.1 * ρ₂ x.2 :=
    (h₁.1.comp measurable_fst).mul (h₂.1.comp measurable_snd)
  refine ⟨hm, fun g => ?_⟩
  rw [lintegral_prod_subgroup hν hm]
  have hc : ∀ t₁ : T₁, ∫⁻ t₂ : T₂, ρ₁ ((t₁ : G₁) * g.1) * ρ₂ ((t₂ : G₂) * g.2) ∂ν₂ =
      ρ₁ ((t₁ : G₁) * g.1) := fun t₁ => by
    have hm₂ : Measurable fun t₂ : T₂ => ρ₂ ((t₂ : G₂) * g.2) :=
      h₂.1.comp (measurable_subtype_coe.mul_const g.2)
    rw [lintegral_const_mul _ hm₂, h₂.2, mul_one]
  simp only [hc]
  exact h₁.2 g.1

end GlobalTheory.CompanionTheory.QuotProduct

namespace GlobalTheory.CompanionTheory.QuotProduct

theorem quotProd_holds : PositivityTheory.Rg.BcB.D4.QuotProd := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ₁ _ μ₂ _ T₁ T₂ ν₁ _ _ ν₂ _ _ ν _ _ F hF hν hinv hfib
  by_cases hex : ∃ ρ, IsQuotNormaliser (T₁.prod T₂) ν ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hν' : ν.map split = ν₁.prod ν₂ := hν
    have n₁ := normaliser_fst hν' hρ
    have n₂ := normaliser_snd hν' hρ
    have n := normaliser_mul hν' n₁ n₂
    set ρ₁ : G₁ → ℝ≥0∞ := fun x => ∫⁻ t₂ : T₂, ρ (x, (t₂ : G₂)) ∂ν₂
    set ρ₂ : G₂ → ℝ≥0∞ := fun x => ∫⁻ t₁ : T₁, ρ ((t₁ : G₁), x) ∂ν₁
    rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hF hinv n]
    by_cases hi : Integrable (fun x : G₁ × G₂ => F x * (((ρ₁ x.1 * ρ₂ x.2).toReal : ℝ) : ℂ)) (μ₁.prod μ₂)
    · rw [integral_prod_symm _ hi]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x₂ => ?_)
      have hFx : Measurable fun x₁ => F (x₁, x₂) := hF.comp (measurable_id.prodMk measurable_const)
      have hinvx : ∀ h ∈ T₁, ∀ g, F (h * g, x₂) = F (g, x₂) := fun h hh g => by
        simpa using hinv (h, 1) (Subgroup.mem_prod.2 ⟨hh, T₂.one_mem⟩) (g, x₂)
      have hq := hfib x₂
      rw [GlobalTheory.CompanionTheory.QuotNorm.quotIntegral_eq hFx hinvx n₁] at hq
      have : ∀ x₁, F (x₁, x₂) * (((ρ₁ x₁ * ρ₂ x₂).toReal : ℝ) : ℂ) =
          (F (x₁, x₂) * (((ρ₁ x₁).toReal : ℝ) : ℂ)) * (((ρ₂ x₂).toReal : ℝ) : ℂ) := fun x₁ => by
        rw [ENNReal.toReal_mul]; push_cast; ring
      simp only [this, Pi.zero_apply]
      rw [integral_mul_const, hq, zero_mul]
    · exact integral_undef hi
  · simp only [quotIntegral, dif_neg hex]

theorem quotProd_of_normEq : PositivityTheory.Rg.BcB.D4.NormEq → PositivityTheory.Rg.BcB.D4.QuotProd :=
  fun _ => quotProd_holds

end GlobalTheory.CompanionTheory.QuotProduct

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFactsStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_abs_basic_facts : LogAbsBasic := by
  first | exact @GlobalTheory.CompanionTheory.LogAbs.logAbsBasic | exact GlobalTheory.CompanionTheory.LogAbs.logAbsBasic | (intros; apply GlobalTheory.CompanionTheory.LogAbs.logAbsBasic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegreeStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mahler_bound_of_degree : DegBdd → DegRat → MahlerC → Mahler := by
  first | exact @GlobalTheory.CompanionTheory.Cutoff.mahler_of | exact GlobalTheory.CompanionTheory.Cutoff.mahler_of | (intros; apply GlobalTheory.CompanionTheory.Cutoff.mahler_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharacterLeviStatement
section
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_character_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ g : Levi k m, ((deltaHalf k m g : ℂˣ) : ℂ) = sqrtModular k N β (leviIncl (φ g)) := by
  first | exact @GlobalTheory.CompanionTheory.DeltaLevi.deltaHalf_eq_sqrtModular | exact GlobalTheory.CompanionTheory.DeltaLevi.deltaHalf_eq_sqrtModular | (intros; apply GlobalTheory.CompanionTheory.DeltaLevi.deltaHalf_eq_sqrtModular <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.TorusCh

def IsPol {K : Type} [Field K] {n : ℕ} (γ e : Matrix (Fin n) (Fin n) K) : Prop := ∃ f : K[X], e = aeval γ f

structure IsPrim {K : Type} [Field K] {n : ℕ} (γ e : Matrix (Fin n) (Fin n) K) : Prop where
  pol : IsPol γ e
  idem : e * e = e
  ne : e ≠ 0
  inv : ∀ h : K[X], aeval γ h * e ≠ 0 → ∃ h' : K[X], aeval γ h' * (aeval γ h * e) = e

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def sg (d : GL (Fin n) E) (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) E :=
  d.val * (X.map (conjE E))ᵀ * (d⁻¹ : GL (Fin n) E).val

def rm (X : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (Ad E) := X.map (algebraMap E (Ad E))

def chi (e : Matrix (Fin n) (Fin n) E) (t : GA E n) : Ad E := (1 + rm e * (t.val - 1)).det

def lam (e : Matrix (Fin n) (Fin n) E) (t : GA E n) : ℝ := logAbs (chi e t)

section Pol

variable {K : Type} [Field K] {n : ℕ}

theorem pol_comm (γ a b : Matrix (Fin n) (Fin n) K) (ha : IsPol γ a) (hb : IsPol γ b) : a * b = b * a := by
  obtain ⟨f, rfl⟩ := ha
  obtain ⟨g, rfl⟩ := hb
  rw [← map_mul, mul_comm, map_mul]

theorem isPol_iff (γ e : Matrix (Fin n) (Fin n) K) : IsPol γ e ↔ e ∈ Algebra.adjoin K {γ} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨fun ⟨f, h⟩ => ⟨f, h.symm⟩, fun ⟨f, h⟩ => ⟨f, h.symm⟩⟩

theorem img_of_pol (γ : GL (Fin n) K) (p : Matrix (Fin n) (Fin n) K) (hp : IsPol γ.val p) :
    img γ (LinearMap.range (Matrix.toLin' p)) = LinearMap.range (Matrix.toLin' p) := by
  have hc : γ.val * p = p * γ.val := pol_comm γ.val _ _ ⟨X, (aeval_X _).symm⟩ hp
  have hs : LinearMap.range (Matrix.toLin' γ.val) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ⟨(γ⁻¹ : GL (Fin n) K).val *ᵥ y, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  unfold img
  rw [← LinearMap.range_comp, ← Matrix.toLin'_mul, hc, Matrix.toLin'_mul, LinearMap.range_comp, hs, Submodule.map_top]

theorem mem_range_idem {a : Matrix (Fin n) (Fin n) K} (ha : a * a = a) (w : Fin n → K) :
    w ∈ LinearMap.range (Matrix.toLin' a) ↔ a *ᵥ w = w := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ha]
  · intro h
    exact ⟨w, by rw [Matrix.toLin'_apply, h]⟩

theorem mul_eq_of_range_le {a b : Matrix (Fin n) (Fin n) K} (hb : b * b = b)
    (h : LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b)) : b * a = a := by
  refine Matrix.toLin'.injective (LinearMap.ext fun y => ?_)
  have h1 : a *ᵥ y ∈ LinearMap.range (Matrix.toLin' b) := h ⟨y, by rw [Matrix.toLin'_apply]⟩
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  exact (mem_range_idem hb _).1 h1

theorem idem_facts (γ a b : Matrix (Fin n) (Fin n) K) (ha : IsPol γ a) (hb : IsPol γ b)
    (ha2 : a * a = a) (hb2 : b * b = b) :
    (LinearMap.range (Matrix.toLin' a) ≤ LinearMap.range (Matrix.toLin' b) → a * b = a) ∧
    (LinearMap.range (Matrix.toLin' a) = LinearMap.range (Matrix.toLin' b) → a = b) ∧
    LinearMap.range (Matrix.toLin' (a * b)) =
      LinearMap.range (Matrix.toLin' a) ⊓ LinearMap.range (Matrix.toLin' b) := by
  have hc := pol_comm γ a b ha hb
  refine ⟨fun h => by rw [hc]; exact mul_eq_of_range_le hb2 h, fun h => ?_, ?_⟩
  · have h1 := mul_eq_of_range_le hb2 h.le
    have h2 := mul_eq_of_range_le ha2 h.ge
    rw [← h1, ← hc, h2]
  · apply le_antisymm
    · rintro _ ⟨y, rfl⟩
      refine ⟨⟨b *ᵥ y, ?_⟩, ⟨a *ᵥ y, ?_⟩⟩
      · simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec]
      · simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hc]
    · rintro w ⟨h1, h2⟩
      have h1' := (mem_range_idem ha2 w).1 h1
      have h2' := (mem_range_idem hb2 w).1 h2
      refine ⟨w, ?_⟩
      rw [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, h2', h1']

end Pol

section Chi

theorem uu_mul {R : Type} [Ring R] (A t t' : R) (hA : A * A = A) (ht : t * A = A * t) :
    (1 + A * (t - 1)) * (1 + A * (t' - 1)) = 1 + A * (t * t' - 1) := by
  have h1 : (t - 1) * A = A * (t - 1) := by rw [sub_mul, mul_sub, ht, one_mul, mul_one]
  have h2 : A * (t - 1) * (A * (t' - 1)) = A * (t - 1) * (t' - 1) := by
    calc A * (t - 1) * (A * (t' - 1)) = A * ((t - 1) * A) * (t' - 1) := by simp only [mul_assoc]
      _ = (A * A) * (t - 1) * (t' - 1) := by rw [h1]; simp only [mul_assoc]
      _ = _ := by rw [hA]
  rw [mul_add, add_mul, add_mul, h2]
  noncomm_ring

theorem uu_add {R : Type} [Ring R] (A B x : R) (hAB : A * B = 0) (hx : x * B = B * x) :
    (1 + A * x) * (1 + B * x) = 1 + (A + B) * x := by
  have h2 : A * x * (B * x) = 0 := by
    calc A * x * (B * x) = A * (x * B) * x := by simp only [mul_assoc]
      _ = (A * B) * x * x := by rw [hx]; simp only [mul_assoc]
      _ = 0 := by rw [hAB]; simp
  rw [mul_add, add_mul, add_mul, h2]
  noncomm_ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem rm_mul (a b : Matrix (Fin n) (Fin n) E) : rm (a * b) = rm a * rm b := Matrix.map_mul

theorem rm_add (a b : Matrix (Fin n) (Fin n) E) : rm (a + b) = rm a + rm b := by
  ext i j; simp [rm]

theorem rm_zero : rm (0 : Matrix (Fin n) (Fin n) E) = 0 := by
  ext i j; simp [rm]

theorem comm_inv {e : Matrix (Fin n) (Fin n) E} {t : GA E n} (ht : t.val * rm e = rm e * t.val) :
    (t⁻¹ : GA E n).val * rm e = rm e * (t⁻¹ : GA E n).val := by
  calc (t⁻¹ : GA E n).val * rm e = (t⁻¹ : GA E n).val * (rm e * (t.val * (t⁻¹ : GA E n).val)) := by
        rw [Units.mul_inv, mul_one]
    _ = (t⁻¹ : GA E n).val * (t.val * rm e) * (t⁻¹ : GA E n).val := by
        rw [ht]; simp only [mul_assoc]
    _ = rm e * (t⁻¹ : GA E n).val := by rw [← mul_assoc, Units.inv_mul, one_mul]

theorem chi_mul (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t t' : GA E n)
    (ht : t.val * rm e = rm e * t.val) : chi e (t * t') = chi e t * chi e t' := by
  unfold chi
  rw [← Matrix.det_mul, uu_mul (rm e) t.val t'.val (by rw [← rm_mul, he]) ht, Units.val_mul]

theorem chi_one (e : Matrix (Fin n) (Fin n) E) : chi e (1 : GA E n) = 1 := by
  simp [chi]

theorem chi_isUnit (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n)
    (ht : t.val * rm e = rm e * t.val) : IsUnit (chi e t) :=
  IsUnit.of_mul_eq_one (chi e t⁻¹) (by rw [← chi_mul e he t _ ht, mul_inv_cancel, chi_one])

theorem lam_mul (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t t' : GA E n) (ht : t.val * rm e = rm e * t.val)
    (ht' : t'.val * rm e = rm e * t'.val) : lam e (t * t') = lam e t + lam e t' := by
  unfold lam
  rw [chi_mul e he t t' ht]
  exact GlobalTheory.CompanionTheory.LogAbs.logAbs_mul _ _ (chi_isUnit e he t ht) (chi_isUnit e he t' ht')

theorem lam_inv (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (t : GA E n) (ht : t.val * rm e = rm e * t.val) :
    lam e t⁻¹ = - lam e t := by
  have h := lam_mul e he t t⁻¹ ht (comm_inv ht)
  have h0 : lam e (1 : GA E n) = 0 := by
    rw [lam, chi_one, ← map_one (algebraMap E (Ad E))]
    exact GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap 1 one_ne_zero
  rw [mul_inv_cancel, h0] at h
  linarith

theorem lam_zero (t : GA E n) : lam (0 : Matrix (Fin n) (Fin n) E) t = 0 := by
  have h1 : chi (0 : Matrix (Fin n) (Fin n) E) t = algebraMap E (Ad E) 1 := by
    simp [chi, rm_zero]
  rw [lam, h1]
  exact GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap 1 one_ne_zero

theorem chi_add (a b : Matrix (Fin n) (Fin n) E) (hab : a * b = 0) (t : GA E n)
    (hb : t.val * rm b = rm b * t.val) : chi (a + b) t = chi a t * chi b t := by
  unfold chi
  have h1 : (t.val - 1) * rm b = rm b * (t.val - 1) := by rw [sub_mul, mul_sub, hb, one_mul, mul_one]
  rw [← Matrix.det_mul, uu_add (rm a) (rm b) _ (by rw [← rm_mul, hab, rm_zero]) h1, rm_add]

theorem lam_sum {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) E) (hf : ∀ i ∈ s, f i * f i = f i)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) (t : GA E n) (ht : ∀ i ∈ s, t.val * rm (f i) = rm (f i) * t.val) :
    lam (∑ i ∈ s, f i) t = ∑ i ∈ s, lam (f i) t := by
  classical
  have key : (∑ i ∈ s, f i) * (∑ i ∈ s, f i) = ∑ i ∈ s, f i ∧
      t.val * rm (∑ i ∈ s, f i) = rm (∑ i ∈ s, f i) * t.val ∧ lam (∑ i ∈ s, f i) t = ∑ i ∈ s, lam (f i) t := by
    induction s using Finset.induction_on with
    | empty => simp [rm_zero, lam_zero]
    | insert a s ha ih =>
      obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj => ho i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
        (fun i hi => ht i (Finset.mem_insert_of_mem hi))
      have haa := hf a (Finset.mem_insert_self _ _)
      have hta := ht a (Finset.mem_insert_self _ _)
      have hl : f a * ∑ i ∈ s, f i = 0 := by
        rw [Finset.mul_sum]
        exact Finset.sum_eq_zero fun i hi => ho a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
      have hr : (∑ i ∈ s, f i) * f a = 0 := by
        rw [Finset.sum_mul]
        exact Finset.sum_eq_zero fun i hi => ho i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self _ _)
          (fun h => ha (h ▸ hi))
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine ⟨?_, ?_, ?_⟩
      · rw [add_mul, mul_add, mul_add, hl, hr, haa, h1]; simp
      · rw [rm_add, mul_add, add_mul, hta, h2]
      · unfold lam at h3 ⊢
        rw [chi_add _ _ hl t h2, GlobalTheory.CompanionTheory.LogAbs.logAbs_mul _ _ (chi_isUnit _ haa t hta) (chi_isUnit _ h1 t h2), h3]
  exact key.2.2

theorem lam_rat (e : Matrix (Fin n) (Fin n) E) (he : e * e = e) (r : GL (Fin n) E)
    (hr : (ratGL E n r).val * rm e = rm e * (ratGL E n r).val) : lam e (ratGL E n r) = 0 := by
  have h1 : chi e (ratGL E n r) = algebraMap E (Ad E) (1 + e * (r.val - 1)).det := by
    have : 1 + rm e * ((ratGL E n r).val - 1) = (1 + e * (r.val - 1)).map (algebraMap E (Ad E)) := by
      have h2 : (ratGL E n r).val = r.val.map (algebraMap E (Ad E)) := rfl
      rw [h2]
      ext i j
      simp [rm, Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, apply_ite, map_sum]
    rw [chi, this]
    exact (RingHom.map_det _ _).symm
  have h2 := chi_isUnit e he _ hr
  rw [h1] at h2
  rw [lam, h1]
  refine GlobalTheory.CompanionTheory.LogAbs.logAbs_algebraMap _ fun h0 => ?_
  rw [h0, map_zero] at h2
  obtain ⟨v⟩ : Nonempty (InfinitePlace E) := inferInstance
  exact (h2.map (cV v)).ne_zero (map_zero _)

end Chi

end GlobalTheory.CompanionTheory.TorusCh

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilradicalChangeOfVariables
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.NilChangeVar

namespace GlobalTheory.CompanionTheory.LocVan

theorem nilChange_of_flag : NilChange := by
  intro n d W₁ W₂ hreg _ hle h1 h2
  let L : nilrad W₁ W₂ ≃ₗ[ℝ] nilrad W₁ W₂ :=
    LinearEquiv.ofInjectiveEndo (slinN d h1 h2 - LinearMap.id) (slinN_injective d h1 h2 hreg)
  have hLval : ∀ X, (L X).1 = slin d X.1 - X.1 := fun X => by
    simp [L, slinN]
  have hLc : Continuous L := by
    refine Continuous.subtype_mk (f := fun X : nilrad W₁ W₂ => (L X).1) ?_ _ |>.congr fun X => rfl
    have e : (fun X : nilrad W₁ W₂ => (L X).1) = fun X => slin d X.1 - X.1 := funext hLval
    rw [e]
    exact ((continuous_slin d).comp continuous_subtype_val).sub continuous_subtype_val
  let Q : nilrad W₁ W₂ → nilrad W₁ W₂ := fun X =>
    ⟨quad d X.1, two_mem hle (quadratic_term_nilradical_mem d h1 h2 X.2).1 (quadratic_term_nilradical_mem d h1 h2 X.2).2⟩
  have hQc : Continuous Q :=
    Continuous.subtype_mk ((continuous_quad d).comp continuous_subtype_val) _
  have hLF : ∀ y ∈ nilrad2 W₁ W₂, L y ∈ nilrad2 W₁ W₂ := fun y hy => by
    obtain ⟨hT, hT'⟩ := semilinear_term_nilradical_mem d h1 h2 hy.1 hy.2
    refine ⟨fun z => ?_, fun z hz => ?_⟩
    · rw [hLval, Matrix.sub_mulVec]; exact W₁.sub_mem (hT z) (hy.1 z)
    · rw [hLval, Matrix.sub_mulVec, hT' z hz, hy.2 z hz, sub_zero]
  have hQF : ∀ X, Q X ∈ nilrad2 W₁ W₂ := fun X => quadratic_term_nilradical_mem d h1 h2 X.2
  have hQinv : ∀ X, ∀ Y ∈ nilrad2 W₁ W₂, Q (X + Y) = Q X := fun X Y hY =>
    Subtype.ext (quad_add d h1 h2 X.2 hle hY.1 hY.2)
  refine ⟨fun X => L X + Q X, hLc.add hQc, fun X => ?_, ?_⟩
  · rw [eq_inv_mul_iff_mul_eq]
    refine Units.ext ?_
    have e : (uOf (L X + Q X)).val = 1 + (slin d X.1 - X.1 + quad d X.1) := by
      rw [uOf_val, Submodule.coe_add, hLval]
    rw [Units.val_mul, e]
    exact twist_val d h1 h2 (uOf X) X.1 X.2 rfl
  · intro _ _ ν _
    obtain ⟨Φ, c, _, hΦ, hmap⟩ := exists_homeo_map_eq_smul ν (nilrad2 W₁ W₂) L hLF Q hQc hQF hQinv
    refine ⟨c, ?_⟩
    have e : (fun X => L X + Q X) = Φ := funext fun X => (hΦ X).symm
    rw [e]
    exact hmap

end GlobalTheory.CompanionTheory.LocVan
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilradicalTranslationMeasurePreserving
section
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

theorem det_one_add_sqZero {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (M : E →ₗ[ℝ] E) (hM : M * M = 0) : LinearMap.det (1 + M) = 1 := by
  have hnil : IsNilpotent (-M) := ⟨2, by rw [pow_two, neg_mul_neg, hM]⟩
  have hc := hnil.charpoly_eq_X_pow_finrank
  let b := Module.finBasis ℝ E
  have h1 : (LinearMap.toMatrix b b (-M)).charpoly.eval 1 = 1 := by
    rw [LinearMap.charpoly_toMatrix, hc]; simp
  rw [Matrix.eval_charpoly] at h1
  rw [← LinearMap.det_toMatrix b, ← h1]
  congr 1
  simp [map_add, LinearMap.toMatrix_one]

theorem measurePreserving_add_one_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (ν : Measure E)
    [ν.IsAddHaarMeasure] (M : E →ₗ[ℝ] E) (hM : M * M = 0) (Y : E) :
    MeasurePreserving (fun X => Y + (1 + M) X) ν ν := by
  have hdet := det_one_add_sqZero M hM
  have hL : MeasurePreserving (fun X => (1 + M : E →ₗ[ℝ] E) X) ν ν := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := ν) (f := (1 + M : E →ₗ[ℝ] E))
      (by rw [hdet]; exact one_ne_zero)
    rw [this, hdet]; simp
  exact (measurePreserving_add_left ν Y).comp hL

theorem nmul_measurePreserving : ∀ (n : ℕ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure] (Y : nilrad W₁ W₂),
  MeasurePreserving (nmul hW Y) ν ν := by
  intro n W₁ W₂ hW mS bS ν hν Y
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  let M : nilrad W₁ W₂ →ₗ[ℝ] nilrad W₁ W₂ :=
    { toFun := fun X => ⟨Y.1 * X.1, nil_mul_mem hW Y.2 X.2⟩
      map_add' := fun A B => Subtype.ext (by simp [mul_add])
      map_smul' := fun c A => Subtype.ext (by simp) }
  have hM : M * M = 0 := by
    ext1 X
    apply Subtype.ext
    change Y.1 * (Y.1 * X.1) = 0
    have h : ∀ y, (Y.1 * (Y.1 * X.1)) *ᵥ y = 0 := fun y => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact Y.2.2.2 _ (Y.2.2.1 _ (X.2.1 y))
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simpa using this
  haveI : FiniteDimensional ℝ (nilrad W₁ W₂) := FiniteDimensional.complexToReal _
  have key := @measurePreserving_add_one_add (nilrad W₁ W₂) (Submodule.normedAddCommGroup _)
    (Submodule.normedSpace _) _ mS bS ν hν M hM Y
  convert key using 1
  funext X
  apply Subtype.ext
  change Y.1 + X.1 + Y.1 * X.1 = Y.1 + (X.1 + Y.1 * X.1)
  abel

end GlobalTheory.CompanionTheory.LocVan
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspacesStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.only_isotropic_subspaces : OnlyStable → DegPairing → SizeBasic → OnlyIsotropic := by
  first | exact @GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of | exact GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of | (intros; apply GlobalTheory.CompanionTheory.IsotropicDegreeBound.onlyIsotropic_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspacesStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.only_stable_subspaces : DegSubmod → DegMove → DegBdd → DegPairing → SizeBasic → OnlyStable := by
  first | exact @GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of | exact GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of | (intros; apply GlobalTheory.CompanionTheory.OnlyStab.onlyStable_of <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OperatorSequenceSumEpiStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operator_sequence_sum_epi : ∀ {X : Scheme.{0}} {k : ℕ} {M : ℕ → X.Modules} {T : Fin k → ∀ e, M e ⟶ M (e + 1)} {d : ℕ}, OpSeq k M T d → ∀ e, Epi (KerSeq.sumMap T d e) := by
  first | exact @GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq | exact GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq | (intros; apply GlobalTheory.CompanionTheory.GE.KerSeq.epi_sumMap_of_opSeq <;> assumption)
end

