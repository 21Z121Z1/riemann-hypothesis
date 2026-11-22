import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0127
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

open MeasureTheory ComplexConjugate

namespace GlobalTheory.SqIntUnit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

variable (k) in

theorem exists_ne_zero_ne_one : ∃ x : k, x ≠ 0 ∧ x ≠ 1 := by
  have h : absPow k ((1 : ℝ) : ℂ) ≠ 1 := fun e => one_ne_zero (absPow_ofReal_eq_one.1 e)
  obtain ⟨z, hz⟩ : ∃ z : kˣ, absPow k ((1 : ℝ) : ℂ) z ≠ 1 := by
    by_contra! h'
    exact h (MonoidHom.ext h')
  refine ⟨z, z.ne_zero, fun e => hz ?_⟩
  rw [show z = 1 from Units.ext e, map_one]

variable (k N) in

theorem modularCharacterFun_eq_one (g : AdGL k N) : Measure.modularCharacterFun g = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  let φ : GL (Fin N) k →* NNReal :=
    Measure.modularCharacter.comp (QuotientGroup.mk' (Subgroup.center (GL (Fin N) k)))
  refine GlobalTheory.T.gl_hom_nnreal_trivial_of_scalar_trivial k (exists_ne_zero_ne_one k) N φ (fun z => ?_) g
  have hz : Matrix.GeneralLinearGroup.scalar (Fin N) z ∈ Subgroup.center (GL (Fin N) k) :=
    Subgroup.mem_center_iff.2 fun h => (Matrix.GeneralLinearGroup.scalar_commute z h).symm
  show Measure.modularCharacter (QuotientGroup.mk' _ _) = 1
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).2 hz, map_one]

theorem isMulRightInvariant [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)] (μ : Measure (AdGL k N))
    [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.map (· * g) μ) μ,
    ← Measure.modularCharacterFun_eq_haarScalarFactor μ g, modularCharacterFun_eq_one, one_smul]

variable (k) in

theorem compactOpen_basis (n : ℕ) : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
    IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin n) U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsSqIntCoeff π → IsUnitarisable π := by
  intro k _ _ _ _ N V _ _ π hs hi hsq
  classical
  have := Model.nontrivial_of_isIrreducible hi
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
  obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hs (compactOpen_basis k N) hv₀
  set L : Module.Dual ℂ V := (l : Module.Dual ℂ V) with hLdef
  have hLo : IsOpen {g : GL (Fin N) k | L ∘ₗ π g = L} := by
    have h1 : IsOpen {g : GL (Fin N) k | π.dual g L = L} := l.2
    have : {g : GL (Fin N) k | L ∘ₗ π g = L} = (fun g => g⁻¹) ⁻¹' {g | π.dual g L = L} := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Representation.dual_apply, inv_inv]
      rfl
    rw [this]
    exact h1.preimage continuous_inv
  borelize (AdGL k N)
  let μ : Measure (AdGL k N) := Measure.haar
  have hF : ∀ v, ∃ F : AdGL k N → ℝ, (∀ g, F (QuotientGroup.mk g) = ‖L (π g v)‖) ∧ MemLp F 2 μ := fun v => by
    obtain ⟨F, h1, h2⟩ := hsq μ inferInstance v L hLo
    exact ⟨F, h1, by simpa using h2⟩
  choose F hF1 hF2 using hF
  have hc : ∀ z ∈ Subgroup.center (GL (Fin N) k), ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, π z v = c • v := by
    intro z hz
    obtain ⟨c, hc⟩ := schur_GL hs hi ⟨π z, fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul]
      exact congrArg π (Subgroup.mem_center_iff.1 hz g).symm⟩
    refine ⟨c, ?_, hc⟩
    have h1 := hF1 v₀ z
    have h2 := hF1 v₀ 1
    rw [(QuotientGroup.eq_one_iff z).2 hz] at h1
    rw [QuotientGroup.mk_one, h1, map_one, Module.End.one_apply] at h2
    have h3 : L v₀ ≠ 0 := hl
    have : ‖c‖ * ‖L v₀‖ = 1 * ‖L v₀‖ := by
      rw [one_mul, ← norm_mul, ← smul_eq_mul, ← map_smul, ← hc]
      exact h2
    exact mul_right_cancel₀ (norm_ne_zero_iff.2 h3) this
  let f : V → V → GL (Fin N) k → ℂ := fun v w g => L (π g v) * conj (L (π g w))
  have hfz : ∀ v w g, ∀ z ∈ Subgroup.center (GL (Fin N) k), f v w (g * z) = f v w g := by
    intro v w g z hz
    obtain ⟨c, hc1, hc⟩ := hc z hz
    have h1 : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc1]
      simp
    simp only [f, map_mul, Module.End.mul_apply, hc, map_smul, smul_eq_mul]
    linear_combination (L (π g v) * conj (L (π g w))) * h1
  let Φ : V → V → AdGL k N → ℂ := fun v w x => f v w (Quotient.out x)
  have hΦ : ∀ v w g, Φ v w (QuotientGroup.mk g) = f v w g := by
    intro v w g
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center (GL (Fin N) k)) g
    show f v w (Quotient.out (QuotientGroup.mk g : AdGL k N)) = f v w g
    rw [hz]
    exact hfz v w g z z.2
  have hfc : ∀ v w, Continuous (f v w) := by
    intro v w
    have h1 : ∀ u, Continuous fun g : GL (Fin N) k => L (π g u) := fun u =>
      ((GlobalTheory.ContraRefl.isLocallyConstant_orbit hs u).comp L).continuous
    exact (h1 v).mul (Complex.continuous_conj.comp (h1 w))
  have hΦc : ∀ v w, Continuous (Φ v w) := by
    intro v w
    refine (QuotientGroup.isQuotientMap_mk (Subgroup.center (GL (Fin N) k))).continuous_iff.2 ?_
    have : Φ v w ∘ QuotientGroup.mk = f v w := funext (hΦ v w)
    rw [this]
    exact hfc v w
  have hnorm : ∀ v w x, ‖Φ v w x‖ = F v x * F w x := by
    intro v w x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hΦ, hF1, hF1]
    simp [f, norm_mul]
  have hint : ∀ v w, Integrable (Φ v w) μ := by
    intro v w
    refine Integrable.mono' ((hF2 v).integrable_mul (hF2 w)) (hΦc v w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [hnorm]
    rfl
  have hadd1 : ∀ v v' w, Φ (v + v') w = fun x => Φ v w x + Φ v' w x := fun v v' w => funext fun x => by
    simp only [Φ, f, map_add, add_mul]
  have hsmul1 : ∀ (a : ℂ) v w, Φ (a • v) w = fun x => a * Φ v w x := fun a v w => funext fun x => by
    simp only [Φ, f, map_smul, smul_eq_mul, mul_assoc]
  have hadd2 : ∀ v w w', Φ v (w + w') = fun x => Φ v w x + Φ v w' x := fun v w w' => funext fun x => by
    simp only [Φ, f, map_add, mul_add]
  have hsmul2 : ∀ (a : ℂ) v w, Φ v (a • w) = fun x => conj a * Φ v w x := fun a v w => funext fun x => by
    simp only [Φ, f, map_smul, smul_eq_mul, map_mul]
    ring
  let B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => ∫ x, Φ v w x ∂μ)
    (fun v v' w => by rw [hadd1, integral_add (hint _ _) (hint _ _)])
    (fun a v w => by rw [hsmul1, integral_const_mul, RingHom.id_apply, smul_eq_mul])
    (fun v w w' => by rw [hadd2, integral_add (hint _ _) (hint _ _)])
    (fun a v w => by rw [hsmul2, integral_const_mul, smul_eq_mul])
  have hB : ∀ v w, B v w = ∫ x, Φ v w x ∂μ := fun v w => rfl
  have hre : ∀ v x, (Φ v v x).re = F v x ^ 2 := by
    intro v x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [hΦ, hF1]
    simp only [f, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  refine ⟨B, fun v w => ?_, fun v hv => ?_, fun h v w => ?_⟩
  · rw [hB, hB, ← integral_conj]
    congr 1
    funext x
    simp only [Φ, f, map_mul, Complex.conj_conj]
    ring
  · have hcont : Continuous fun x => F v x ^ 2 := by
      have : (fun x => F v x ^ 2) = fun x => (Φ v v x).re := funext fun x => (hre v x).symm
      rw [this]
      exact Complex.continuous_re.comp (hΦc v v)
    have hi2 : Integrable (fun x => F v x ^ 2) μ := by
      have : (fun x => F v x ^ 2) = fun x => (Φ v v x).re := funext fun x => (hre v x).symm
      rw [this]
      exact (hint v v).re
    have hreB : (B v v).re = ∫ x, F v x ^ 2 ∂μ := by
      rw [hB]
      show RCLike.re (∫ x, Φ v v x ∂μ) = _
      rw [← integral_re (hint v v)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => hre v x)
    rw [hreB]
    refine lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) (fun h0 => hv ?_)
    have h1 : (fun x => F v x ^ 2) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hi2).1 h0.symm
    have h2 : (fun x => F v x ^ 2) = 0 := (Continuous.ae_eq_iff_eq μ hcont continuous_const).1 h1
    have h3 : ∀ g, L (π g v) = 0 := fun g => by
      have := congrFun h2 (QuotientGroup.mk g)
      rw [Pi.zero_apply, hF1] at this
      simpa using this
    let W : Subrepresentation π :=
      ⟨{ carrier := {u | ∀ g, L (π g u) = 0}
         add_mem' := fun {a b} ha hb g => by simp [ha g, hb g]
         zero_mem' := fun g => by simp
         smul_mem' := fun c u hu g => by simp [hu g] },
        fun g u hu h => by
          show L (π h (π g u)) = 0
          rw [← Module.End.mul_apply, ← map_mul]
          exact hu (h * g)⟩
    haveI : IsSimpleOrder (Subrepresentation π) := hi
    rcases eq_bot_or_eq_top W with hW | hW
    · have hvW : v ∈ W.toSubmodule := h3
      rw [hW] at hvW
      exact (Submodule.mem_bot ℂ).1 hvW
    · exfalso
      have hvW : v₀ ∈ W.toSubmodule := by
        rw [hW]
        exact Submodule.mem_top
      have := hvW 1
      rw [map_one, Module.End.one_apply] at this
      exact hl this
  · haveI := isMulRightInvariant μ
    have hinv : ∀ x, Φ (π h v) (π h w) x = Φ v w (x * QuotientGroup.mk h) := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      rw [← QuotientGroup.mk_mul, hΦ, hΦ]
      simp only [f, map_mul, Module.End.mul_apply]
    rw [hB, hB, funext hinv]
    exact integral_mul_right_eq_self (Φ v w) _

end GlobalTheory.SqIntUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryGroupNewtonLiftStep
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

variable {L : Type} [Field L]

theorem cT_smul' (σ : L →+* L) {n : ℕ} (s : L) (A : Matrix (Fin n) (Fin n) L) :
    cT σ (s • A) = σ s • cT σ A := by ext i j; simp [cT]

theorem cT_add' (σ : L →+* L) {n : ℕ} (A B : Matrix (Fin n) (Fin n) L) :
    cT σ (A + B) = cT σ A + cT σ B := by ext i j; simp [cT]

theorem cT_cT' {σ : L →+* L} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (A : Matrix (Fin n) (Fin n) L) :
    cT σ (cT σ A) = A := by ext i j; simp [cT, hσ]

theorem newton_identity {n : ℕ} (s c : L) (hc : c + c = 1) (Gc g J X Xc E : Matrix (Fin n) (Fin n) L)
    (h1 : Gc * J * g = J + s • E) (h2 : J * X = -(c • E)) (h3 : Xc * J = -(c • E)) :
    (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) - J =
      (s * s) • (E * X + Xc * E + Xc * (Gc * J * g) * X) := by
  have e : (Gc + s • (Xc * Gc)) * J * (g + s • (g * X)) =
      Gc * J * g + s • (Gc * J * g * X) + s • (Xc * (Gc * J * g)) + (s * s) • (Xc * (Gc * J * g) * X) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, smul_add]
    abel
  rw [e]
  nth_rewrite 1 [h1]; nth_rewrite 1 [h1]; nth_rewrite 1 [h1]
  rw [Matrix.add_mul, Matrix.mul_add, h2, h3, Matrix.smul_mul, Matrix.mul_smul]
  have hE : (c + c) • E = (1 : L) • E := by rw [hc]
  linear_combination (norm := module) (-s) • hE

end GlobalTheory.Hk3.UnitaryNewton

end

namespace GlobalTheory.Hk3.UnitaryNewton

open Formalism.UG GlobalTheory.Hk3.IntWitt GlobalTheory.Hk3.IntWittBase

theorem newton_step : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ),
    Formalism.UG.IsUnramInv ϖ σ q → Odd q → ∀ (n : ℕ) (J : GL (Fin n) L), J ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) →
    (∀ i j, σ ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i) →
    ∀ (k : ℕ) (g : Matrix (Fin n) (Fin n) L), (∀ i j, g i j ∈ Formalism.UG.intL L) →
    (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1)
      ((Formalism.UG.cT σ g * (J : Matrix (Fin n) (Fin n) L) * g - (J : Matrix (Fin n) (Fin n) L)) i j)) →
    ∃ g' : Matrix (Fin n) (Fin n) L, (∀ i j, g' i j ∈ Formalism.UG.intL L) ∧
      (∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 1) (g' i j - g i j)) ∧
      ∀ i j, GlobalTheory.Hk3.IntWitt.DvdPow ϖ (k + 2)
        ((Formalism.UG.cT σ g' * (J : Matrix (Fin n) (Fin n) L) * g' - (J : Matrix (Fin n) (Fin n) L)) i j) := by
  intro L _ _ ϖ σ q hU hq n J hJ hJh k g hg hD
  have h2 : Valued.v (2 : L) = 1 := GlobalTheory.Hk3.Inh.v_two hU hq
  obtain ⟨hσσ, hσv, hσϖ, hϖv, -⟩ := hU
  set Jm : Matrix (Fin n) (Fin n) L := (J : Matrix (Fin n) (Fin n) L) with hJm
  set Ji : Matrix (Fin n) (Fin n) L := ((J⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hJidef
  have hJi : Ji * Jm = 1 := by rw [hJm, hJidef, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJi' : Jm * Ji = 1 := by rw [hJm, hJidef, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨g0, hg0⟩ := hJ
  have hJI : ∀ i j, Jm i j ∈ intL L := by
    intro i j; rw [hJm, ← hg0]; exact ((g0 : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJiI : ∀ i j, Ji i j ∈ intL L := by
    intro i j; rw [hJidef, ← hg0, ← map_inv]
    exact (((g0⁻¹ : GL (Fin n) (intL L)) : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have hJc : cT σ Jm = Jm := by ext i j; rw [cT_apply]; exact hJh j i
  have hJic : cT σ Ji = Ji := by
    have h : cT σ Ji * Jm = 1 := by rw [← hJc, ← cT_mul, hJi', cT_one]
    calc cT σ Ji = cT σ Ji * Jm * Ji := by rw [Matrix.mul_assoc, hJi', Matrix.mul_one]
      _ = Ji := by rw [h, Matrix.one_mul]
  unfold DvdPow at hD
  choose E hE hEeq using hD
  set s : L := ϖ ^ (k + 1) with hs
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hϖv; exact WithZero.zero_ne_coe hϖv
  have hϖI : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖv]; exact_mod_cast (show (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1 from by decide)
  have hs0 : s ≠ 0 := pow_ne_zero _ hϖ0
  have hσs : σ s = s := by rw [hs, map_pow, hσϖ]
  have hsI : s ∈ intL L := (intL L).pow_mem hϖI _
  set Em : Matrix (Fin n) (Fin n) L := Matrix.of E with hEm
  have hEmI : ∀ i j, Em i j ∈ intL L := hE
  have hDE : cT σ g * Jm * g = Jm + s • Em := by
    ext i j
    have := hEeq i j
    rw [Matrix.sub_apply] at this
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hEm, Matrix.of_apply, ← this]; ring
  have hEh : cT σ Em = Em := by
    have h := congrArg (cT σ) hDE
    rw [cT_mul, cT_mul, cT_cT' hσσ, hJc, cT_add', cT_smul', hσs, hJc, ← Matrix.mul_assoc, hDE] at h
    exact (smul_right_injective _ hs0 (add_left_cancel h)).symm
  have h20 : (2 : L) ≠ 0 := by intro h0; rw [h0, map_zero] at h2; exact zero_ne_one h2
  set c : L := (2 : L)⁻¹ with hcdef
  have hc : c + c = 1 := by rw [← two_mul, hcdef, mul_inv_cancel₀ h20]
  have hσc : σ c = c := by rw [hcdef, map_inv₀, map_ofNat]
  have hcI : c ∈ intL L := by
    show Valued.v c ≤ 1
    rw [hcdef, map_inv₀, h2, inv_one]
  set X : Matrix (Fin n) (Fin n) L := (-c) • (Ji * Em) with hX
  have hXI : ∀ i j, X i j ∈ intL L := by
    intro i j; rw [hX, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (neg_mem hcI) (int_mul hJiI hEmI i j)
  have hXc : cT σ X = (-c) • (Em * Ji) := by
    rw [hX, cT_smul', cT_mul, hEh, hJic, map_neg, hσc]
  have hJX : Jm * X = -(c • Em) := by
    rw [hX, Matrix.mul_smul, ← Matrix.mul_assoc, hJi', Matrix.one_mul, neg_smul]
  have hXJ : cT σ X * Jm = -(c • Em) := by
    rw [hXc, Matrix.smul_mul, Matrix.mul_assoc, hJi, Matrix.mul_one, neg_smul]
  refine ⟨g + s • (g * X), ?_, ?_, ?_⟩
  · intro i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (hg i j) (mul_mem hsI (int_mul hg hXI i j))
  · intro i j
    refine ⟨(g * X) i j, int_mul hg hXI i j, ?_⟩
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  · have hg'c : cT σ (g + s • (g * X)) = cT σ g + s • (cT σ X * cT σ g) := by
      rw [cT_add', cT_smul', hσs, cT_mul]
    have key := newton_identity s c hc (cT σ g) g Jm X (cT σ X) Em hDE hJX hXJ
    rw [hg'c, key]
    have hgc : ∀ i j, cT σ g i j ∈ intL L := int_cT hσv hg
    have hXcI : ∀ i j, cT σ X i j ∈ intL L := int_cT hσv hXI
    have hR : ∀ i j, (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j ∈ intL L := by
      intro i j
      rw [Matrix.add_apply, Matrix.add_apply]
      exact add_mem (add_mem (int_mul hEmI hXI i j) (int_mul hXcI hEmI i j))
        (int_mul (int_mul hXcI (int_mul (int_mul hgc hJI) hg)) hXI i j)
    intro i j
    refine ⟨ϖ ^ k * (Em * X + cT σ X * Em + cT σ X * (cT σ g * Jm * g) * X) i j,
      mul_mem ((intL L).pow_mem hϖI _) (hR i j), ?_⟩
    rw [Matrix.smul_apply, smul_eq_mul, hs]; ring

end GlobalTheory.Hk3.UnitaryNewton
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.VacuumPhaseSubTraceMemIntegers
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.VacPhase

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem cT_mul' (σ : L →+* L) {a b c : ℕ} (A : Matrix (Fin a) (Fin b) L) (B : Matrix (Fin b) (Fin c) L) :
    Formalism.UG.cT σ (A * B) = Formalism.UG.cT σ B * Formalism.UG.cT σ A := by
  simp only [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one' (σ : L →+* L) {a : ℕ} : Formalism.UG.cT σ (1 : Matrix (Fin a) (Fin a) L) = 1 := by
  simp [Formalism.UG.cT, Matrix.map_one]

theorem cT_sub' (σ : L →+* L) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) L) :
    Formalism.UG.cT σ (A - B) = Formalism.UG.cT σ A - Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_add' (σ : L →+* L) {a b : ℕ} (A B : Matrix (Fin a) (Fin b) L) :
    Formalism.UG.cT σ (A + B) = Formalism.UG.cT σ A + Formalism.UG.cT σ B := by
  ext i j; simp [Formalism.UG.cT]

theorem mul_int {a b c : ℕ} {A : Matrix (Fin a) (Fin b) L} {B : Matrix (Fin b) (Fin c) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hB : ∀ i j, B i j ∈ Formalism.UG.intL L) (i : Fin a) (j : Fin c) :
    (A * B) i j ∈ Formalism.UG.intL L := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem cT_int (σ : L →+* L) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {a b : ℕ} {A : Matrix (Fin a) (Fin b) L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (i : Fin b) (j : Fin a) : Formalism.UG.cT σ A i j ∈ Formalism.UG.intL L := by
  have h := hA j i
  change Valued.v (σ (A j i)) ≤ 1
  rw [hσ]; exact h

theorem locH_sub_trace_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (δ : L), (∀ x, Valued.v (σ x) = Valued.v x) → δ ∈ Formalism.UG.intL L →
  ∀ (n n' : ℕ) (JS a k : GL (Fin n) L) (JT : GL (Fin n') L) (E : Matrix (Fin n) (Fin n) L) (y : Matrix (Fin n') (Fin n) L),
  (∀ i j, (JS : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) → (∀ i j, ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (JT : Matrix (Fin n') (Fin n') L) i j ∈ Formalism.UG.intL L) → GlobalTheory.Hk3.HoweG.SelfDual σ JS a →
  Formalism.UG.cT σ E * (JS : Matrix (Fin n) (Fin n) L) = -((JS : Matrix (Fin n) (Fin n) L) * E) →
  (∀ i j, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * E) i j ∈ Formalism.UG.intL L) → (∀ i j, (E * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  (k : Matrix (Fin n) (Fin n) L) = 1 + E → (∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L) →
  (∀ i j, (y * (a : Matrix (Fin n) (Fin n) L)) i j ∈ Formalism.UG.intL L) →
  GlobalTheory.Hk3.locH σ δ JS JT y (y * (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1)) -
    δ * Matrix.trace (E * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * Formalism.UG.cT σ y * (JT : Matrix (Fin n') (Fin n') L) * y) ∈ Formalism.UG.intL L := by
  intro L _ _ σ δ hσ hδ n n' JS a k JT E y hJ hP hT hSD hE hAiE hEA hk hKi hyA
  set J : Matrix (Fin n) (Fin n) L := (JS : Matrix (Fin n) (Fin n) L) with hJdef
  set P : Matrix (Fin n) (Fin n) L := ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  set T : Matrix (Fin n') (Fin n') L := (JT : Matrix (Fin n') (Fin n') L) with hTdef
  set K : Matrix (Fin n) (Fin n) L := (k : Matrix (Fin n) (Fin n) L) with hKdef
  set Ki : Matrix (Fin n) (Fin n) L := ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hKidef
  set A : Matrix (Fin n) (Fin n) L := (a : Matrix (Fin n) (Fin n) L) with hAdef
  set Ai : Matrix (Fin n) (Fin n) L := ((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAidef
  have hPJ : P * J = 1 := by rw [hPdef, hJdef]; exact JS.inv_mul
  have hJP : J * P = 1 := by rw [hPdef, hJdef]; exact JS.mul_inv
  have hKKi : K * Ki = 1 := by rw [hKdef, hKidef]; exact k.mul_inv
  have hAAi : A * Ai = 1 := by rw [hAdef, hAidef]; exact a.mul_inv
  set R : Matrix (Fin n) (Fin n) L := P * Formalism.UG.cT σ Ki * J with hRdef
  set Z : Matrix (Fin n) (Fin n) L := P * Formalism.UG.cT σ y * T * y with hZdef

  have h1 : GlobalTheory.Hk3.locH σ δ JS JT y (y * (Ki - 1)) = δ * Matrix.trace ((R - 1) * Z) := by
    unfold GlobalTheory.Hk3.locH
    have : ((y * (Ki - 1)).map σ)ᵀ = Formalism.UG.cT σ (Ki - 1) * Formalism.UG.cT σ y := cT_mul' σ y (Ki - 1)
    rw [← hPdef, ← hTdef, this, cT_sub', cT_one']
    congr 1
    rw [hRdef, hZdef]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J P, hJP, Matrix.one_mul]
  have h2 : δ * Matrix.trace (E * P * Formalism.UG.cT σ y * T * y) = δ * Matrix.trace (E * Z) := by
    rw [hZdef]; simp only [Matrix.mul_assoc]

  have hR : R * (1 - E) = 1 := by
    have hcK : Formalism.UG.cT σ K * J = J * (1 - E) := by
      rw [hk, cT_add', cT_one', Matrix.add_mul, hE, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, sub_eq_add_neg]
    rw [hRdef, Matrix.mul_assoc, ← hcK, ← Matrix.mul_assoc, Matrix.mul_assoc P, ← cT_mul', hKKi, cT_one', Matrix.mul_one, hPJ]
  have hR' : (1 - E) * R = 1 := mul_eq_one_comm.mp hR
  have hRE : R - 1 - E = E * R * E := by
    have e1 : R - 1 = R * E := by
      have := hR; rw [Matrix.mul_sub, Matrix.mul_one] at this
      rw [← this]; abel
    have e2 : R - 1 = E * R := by
      have := hR'; rw [Matrix.sub_mul, Matrix.one_mul] at this
      rw [← this]; abel
    calc R - 1 - E = (R - 1) * E := by rw [Matrix.sub_mul, Matrix.one_mul, e1]
      _ = E * R * E := by rw [e2]
  have h3 : GlobalTheory.Hk3.locH σ δ JS JT y (y * (Ki - 1)) - δ * Matrix.trace (E * P * Formalism.UG.cT σ y * T * y) =
      δ * Matrix.trace (R * (E * Z * E)) := by
    rw [h1, h2, ← mul_sub, ← Matrix.trace_sub, ← Matrix.sub_mul, hRE]
    congr 1
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm E]
    simp only [Matrix.mul_assoc]
  rw [h3]

  have hRint : ∀ i j, R i j ∈ Formalism.UG.intL L :=
    mul_int (mul_int hP (cT_int σ hσ hKi)) hJ
  have hy' : Formalism.UG.cT σ y = Formalism.UG.cT σ Ai * Formalism.UG.cT σ (y * A) := by
    rw [← cT_mul', Matrix.mul_assoc, hAAi, Matrix.mul_one]
  have hW : E * Z * E = ((E * A) * (Ai * P * Formalism.UG.cT σ Ai) * Formalism.UG.cT σ (y * A)) * T * ((y * A) * (Ai * E)) := by
    rw [hZdef, hy']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc A Ai, hAAi, Matrix.one_mul, ← Matrix.mul_assoc A Ai E, hAAi, Matrix.one_mul]
  have hWint : ∀ i j, (E * Z * E) i j ∈ Formalism.UG.intL L := by
    rw [hW]
    exact mul_int (mul_int (mul_int (mul_int hEA hSD.2) (cT_int σ hσ hyA)) hT) (mul_int hyA hAiE)
  refine Subring.mul_mem _ hδ ?_
  exact Subring.sum_mem _ fun i _ => mul_int hRint hWint i i

end GlobalTheory.Hk3.VacPhase

end
end

