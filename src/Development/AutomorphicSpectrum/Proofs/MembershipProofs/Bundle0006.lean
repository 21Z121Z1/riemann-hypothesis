import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.SplitQuadraticAlgebraOrder
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0002
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.IntegrablePair
section
noncomputable section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchrSys

section Pair

variable {R : Type} [TopologicalSpace R] {κ : Type}

theorem integrable_pair (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ)
    (φ φ' : SB (κ → R)) :
    @Integrable ℂ _ _ _ (borel _) (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) μ := by
  letI : MeasurableSpace (κ → R) := borel _
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  have h1 : Continuous (φ : (κ → R) → ℂ) := φ.2.1.continuous
  have h2 : Continuous (φ' : (κ → R) → ℂ) := φ'.2.1.continuous
  have h3 : HasCompactSupport (φ' : (κ → R) → ℂ) := φ'.2.2
  exact Continuous.integrable_of_hasCompactSupport ((Complex.continuous_conj.comp h1).mul h2)
    (HasCompactSupport.mul_left (f := fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x)) h3)

def pairForm (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ) :
    SB (κ → R) →ₗ⋆[ℂ] SB (κ → R) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ φ' => pair μ φ φ')
    (by
      intro f f' g
      simp only [pair, Submodule.coe_add, Pi.add_apply, map_add, add_mul]
      exact integral_add (integrable_pair μ hμ f g) (integrable_pair μ hμ f' g))
    (by
      intro a f g
      simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
      exact integral_const_mul _ _)
    (by
      intro f g g'
      simp only [pair, Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_pair μ hμ f g) (integrable_pair μ hμ f g'))
    (by
      intro a f g
      simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ a]
      exact integral_const_mul _ _)

theorem pair_conj (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) :
    (starRingEnd ℂ) (pair μ φ φ') = pair μ φ' φ := by
  letI : MeasurableSpace (κ → R) := borel _
  unfold pair
  rw [← integral_conj]
  congr 1
  funext x
  simp [mul_comm]

theorem pair_pos (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ)
    (hμ' : @Measure.IsOpenPosMeasure _ _ (borel _) μ) (φ : SB (κ → R)) (hφ : φ ≠ 0) : 0 < (pair μ φ φ).re := by
  letI : MeasurableSpace (κ → R) := borel _
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  have h1 : Continuous (φ : (κ → R) → ℂ) := φ.2.1.continuous
  have h3 : HasCompactSupport (φ : (κ → R) → ℂ) := φ.2.2
  have e : pair μ φ φ = ((∫ x, ‖(φ : (κ → R) → ℂ) x‖ * ‖(φ : (κ → R) → ℂ) x‖ ∂μ : ℝ) : ℂ) := by
    unfold pair
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [Complex.conj_mul']
    simp [sq]
  rw [e, Complex.ofReal_re]
  obtain ⟨x, hx⟩ : ∃ x, (φ : (κ → R) → ℂ) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (Subtype.ext (funext h))
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x) (h1.norm.mul h1.norm)
    (HasCompactSupport.mul_left (f := fun x => ‖(φ : (κ → R) → ℂ) x‖) h3.norm)
    (fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  have := norm_pos_iff.2 hx
  exact (mul_pos this this).ne'

end Pair

theorem exists_isModel : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) , GoodChar ψ O u → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ S : Sys W (SB (κ → R)), IsModel ψ d μ S := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ hψ hμ
  have law := fun w w' φ φ' => GlobalTheory.CompanionTheory.SchrLaw.schr_law ψ O u d μ w w' φ φ' hψ hμ
  have hc : @IsFiniteMeasureOnCompacts _ (borel _) _ μ := hμ.toIsFiniteMeasureOnCompacts
  have ho : @Measure.IsOpenPosMeasure _ _ (borel _) μ := hμ.toIsOpenPosMeasure
  let rho : W → SB (κ → R) →ₗ[ℂ] SB (κ → R) := fun w =>
    { toFun := fun φ => ⟨d.rho ψ w φ, (law w 0 φ 0).2.2.1 φ.2⟩
      map_add' := fun φ φ' => by
        apply Subtype.ext
        funext x
        simp [Darboux.rho, schr, mul_add]
      map_smul' := fun a φ => by
        apply Subtype.ext
        funext x
        simp [Darboux.rho, schr, mul_left_comm] }
  refine ⟨{ c := fun w w' => ψ (⅟(2 : R) * B w w')
            rho := rho
            B := pairForm μ hc
            c_add_left := ?_
            c_add_right := ?_
            c_self := ?_
            c_norm := fun _ _ => hψ.norm_one _
            rho_zero := fun φ => Subtype.ext (law 0 0 φ 0).2.1
            rho_rho := fun w w' φ => Subtype.ext (law w w' φ 0).1
            B_conj := fun φ φ' => pair_conj μ φ φ'
            B_pos := fun φ hφ => pair_pos μ hc ho φ hφ
            B_rho := fun w φ φ' => (law w 0 φ φ').2.2.2 },
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro x x' y
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    ring
  · intro x y y'
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    ring
  · intro x
    simp [d.form]

end GlobalTheory.CompanionTheory.SchrSys
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.LagrangianStabilizerCharacterTrivial
section
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal

namespace GlobalTheory.CompanionTheory.SplitUnique

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [Fintype β]

theorem hTens_eq (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hTens_eq_zero (JA : Matrix α α E) {JB : Matrix β β E} {ν : Type} [Fintype ν] {Cy : Matrix β ν E}
    (h : Cyᵀ * JB * Cy.map c = 0) (z z' : Matrix α ν E) : hTens c JA JB (z * Cyᵀ) (z' * Cyᵀ) = 0 := by
  rw [hTens_eq]
  have hm : z * Cyᵀ * JB * ((z' * Cyᵀ).map c)ᵀ = 0 := by
    have hmap : (z' * Cyᵀ).map c = z'.map c * (Cyᵀ).map c := by
      simp
    rw [hmap, Matrix.transpose_mul, Matrix.transpose_map, Matrix.transpose_transpose,
      show z * Cyᵀ * JB * (Cy.map c * (z'.map c)ᵀ) = z * (Cyᵀ * JB * Cy.map c) * (z'.map c)ᵀ by
        simp only [Matrix.mul_assoc], h]
    simp
  rw [hm]
  simp

variable [DecidableEq β]

end Alg

end GlobalTheory.CompanionTheory.SplitUnique
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.LocallyCompactOfGoodChar
section
noncomputable section

open MeasureTheory GlobalTheory.WeilM GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.SchrLaw

namespace GlobalTheory.CompanionTheory.SchrModel

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

theorem locallyCompact_of_goodChar [T2Space R] {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) :
    LocallyCompactSpace R := by
  exact h.compact.locallyCompactSpace_of_mem_nhds_of_addGroup (h.isOpen.mem_nhds O.zero_mem)

omit [CommRing R] [IsTopologicalRing R] in

theorem integrable_pair {κ : Type} (μ : @Measure (κ → R) (borel _))
    (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ) (φ φ' : SB (κ → R)) :
    @Integrable _ _ _ _ (borel _) (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) μ := by
  haveI := hμ
  have hφ : IsLocallyConstant (φ : (κ → R) → ℂ) ∧ HasCompactSupport (φ : (κ → R) → ℂ) := φ.2
  have hφ' : IsLocallyConstant (φ' : (κ → R) → ℂ) ∧ HasCompactSupport (φ' : (κ → R) → ℂ) := φ'.2
  have hcont : Continuous (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) :=
    (Complex.continuous_conj.comp hφ.1.continuous).mul hφ'.1.continuous
  have hsupp : HasCompactSupport
      (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) :=
    HasCompactSupport.mul_left (f := fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x)) hφ'.2
  letI : MeasurableSpace (κ → R) := borel _
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  exact Continuous.integrable_of_hasCompactSupport hcont hsupp

omit [CommRing R] [IsTopologicalRing R] in

def form {κ : Type} (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ) :
    SB (κ → R) →ₗ⋆[ℂ] SB (κ → R) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ φ' => pair μ φ φ')
    (fun φ₁ φ₂ φ' => by
      unfold pair
      rw [← integral_add (integrable_pair μ hμ φ₁ φ') (integrable_pair μ hμ φ₂ φ')]
      congr 1
      funext x
      simp [add_mul])
    (fun a φ φ' => by
      unfold pair
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext x
      simp [mul_assoc])
    (fun φ φ₁ φ₂ => by
      unfold pair
      rw [← integral_add (integrable_pair μ hμ φ φ₁) (integrable_pair μ hμ φ φ₂)]
      congr 1
      funext x
      simp [mul_add])
    (fun a φ φ' => by
      unfold pair
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext x
      simp [mul_left_comm])

omit [CommRing R] [IsTopologicalRing R] in

theorem pair_conj {κ : Type} (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) :
    (starRingEnd ℂ) (pair μ φ φ') = pair μ φ' φ := by
  show (starRingEnd ℂ) (∫ x, (starRingEnd ℂ) (φ x) * φ' x ∂μ) = ∫ x, (starRingEnd ℂ) (φ' x) * φ x ∂μ
  rw [← @integral_conj (κ → R) (borel _) μ ℂ _ _]
  congr 1
  funext x
  rw [map_mul, Complex.conj_conj, mul_comm]

omit [IsTopologicalRing R] in

theorem pair_pos {κ : Type} (μ : @Measure (κ → R) (borel _))
    (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) (φ : SB (κ → R)) (hφ : φ ≠ 0) :
    0 < (pair μ (φ : (κ → R) → ℂ) φ).re := by
  haveI := hμ
  have hφl : IsLocallyConstant (φ : (κ → R) → ℂ) ∧ HasCompactSupport (φ : (κ → R) → ℂ) := φ.2
  have hcont : Continuous (φ : (κ → R) → ℂ) := hφl.1.continuous
  have hint := integrable_pair μ
    (@Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts _ _ _ (borel _) μ hμ) φ φ
  have hg : ∀ z : ℂ, ((starRingEnd ℂ) z * z).re = Complex.normSq z := by
    intro z
    rw [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hre : (pair μ (φ : (κ → R) → ℂ) φ).re =
      ∫ x, ((starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ : (κ → R) → ℂ) x).re ∂μ :=
    (@integral_re (κ → R) (borel _) μ ℂ _ _ hint).symm
  rw [hre]
  obtain ⟨x0, hx0⟩ : ∃ x, (φ : (κ → R) → ℂ) x ≠ 0 := by
    by_contra hc
    apply hφ
    apply Subtype.ext
    funext x
    by_contra hx
    exact hc ⟨x, hx⟩
  refine (MeasureTheory.integral_pos_iff_support_of_nonneg ?_ ?_).mpr ?_
  · intro x
    show (0 : ℝ) ≤ ((starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ : (κ → R) → ℂ) x).re
    rw [hg]
    exact Complex.normSq_nonneg _
  · exact hint.re
  · have hU : IsOpen ((φ : (κ → R) → ℂ) ⁻¹' {0}ᶜ) := hcont.isOpen_preimage _ isOpen_compl_singleton
    have hsub : (φ : (κ → R) → ℂ) ⁻¹' {0}ᶜ ⊆
        Function.support fun x => ((starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ : (κ → R) → ℂ) x).re := by
      intro x hx
      rw [Function.mem_support, hg]
      exact (Complex.normSq_pos.mpr hx).ne'
    exact lt_of_lt_of_le (hU.measure_pos μ ⟨x0, hx0⟩) (measure_mono hsub)

variable [T2Space R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ]

def sys {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) (d : Darboux B κ)
    (μ : @Measure (κ → R) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    GlobalTheory.CompanionTheory.FinHeis.Sys W (SB (κ → R)) :=
  haveI := locallyCompact_of_goodChar h
  { c := fun w w' => ψ (⅟(2 : R) * B w w')
    rho := fun w =>
      { toFun := fun φ => ⟨d.rho ψ w φ, (schr_law ψ O u d μ w w φ φ h hμ).2.2.1 φ.2⟩
        map_add' := fun φ φ' => Subtype.ext (funext fun x => by simp [Darboux.rho, schr, mul_add])
        map_smul' := fun a φ => Subtype.ext (funext fun x => by simp [Darboux.rho, schr, mul_left_comm]) }
    B := form μ (@Measure.IsAddHaarMeasure.toIsFiniteMeasureOnCompacts _ _ _ (borel _) μ hμ)
    c_add_left := fun x x' y => by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
      ring
    c_add_right := fun x y y' => by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
      ring
    c_self := fun x => by simp [d.form]
    c_norm := fun x y => h.norm_one _
    rho_zero := fun φ => Subtype.ext (schr_law ψ O u d μ 0 0 φ φ h hμ).2.1
    rho_rho := fun w w' φ => Subtype.ext (schr_law ψ O u d μ w w' φ φ h hμ).1
    B_conj := fun φ φ' => pair_conj μ φ φ'
    B_pos := fun φ hφ => pair_pos μ hμ φ hφ
    B_rho := fun w φ φ' => (schr_law ψ O u d μ w w φ φ' h hμ).2.2.2 }

theorem isModel_sys {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) (d : Darboux B κ)
    (μ : @Measure (κ → R) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    IsModel ψ d μ (sys h d μ hμ) := by
  show (∀ w φ, _) ∧ (∀ φ φ', _) ∧ ∀ w w', _
  exact ⟨fun w φ => rfl, fun φ φ' => rfl, fun w w' => rfl⟩

theorem exists_isModel {ψ : AddChar R ℂ} {O : Subring R} {u : Rˣ} (h : GoodChar ψ O u) (d : Darboux B κ)
    (μ : @Measure (κ → R) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ S : GlobalTheory.CompanionTheory.FinHeis.Sys W (SB (κ → R)), IsModel ψ d μ S := by
  exact ⟨sys h d μ hμ, isModel_sys h d μ hμ⟩

end GlobalTheory.CompanionTheory.SchrModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.SchrodingerModelSelfDualLatticeStatement
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_in_schrodinger_span : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {κ : Type} [Fintype κ] (v : Rˣ), GoodChar ψ O u → (v : R) ∈ O → (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) ∈ Submodule.span ℂ {f : (κ → R) → ℂ | ∃ y : κ → R, f = schr ψ (0, y) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ))} := by
  first | exact @GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span | exact GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span | (intros; apply GlobalTheory.CompanionTheory.CosetMod.indicator_mem_span <;> assumption)
end

