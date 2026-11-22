import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0021

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasSumBilateral
section
noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG GlobalTheory.GLDoubling
open scoped NNReal Pointwise

namespace GlobalTheory.GLDoubling.Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_haar (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] :
    ∃ μ : Measure (GL (Fin n) k), μ.IsHaarMeasure ∧ μ (KO k (Fin n)) = 1 := by
  have ho : IsOpen (KO k (Fin n) : Set (GL (Fin n) k)) := SplitFlip.isOpen_KO
  have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := SplitFlip.isCompact_KO
  let K : TopologicalSpace.PositiveCompacts (GL (Fin n) k) := ⟨⟨_, hc⟩, by
    rw [show interior ((⟨_, hc⟩ : TopologicalSpace.Compacts (GL (Fin n) k)).carrier) = _ from ho.interior_eq]
    exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

theorem hasSum_bilateral {a Y : ℂ} (ha : a ≠ 0) (h1 : ‖a * Y‖ < 1) (h2 : ‖a⁻¹ * Y‖ < 1) :
    HasSum (fun e : ℤ => Y ^ |e| * a ^ e) ((1 - a * Y)⁻¹ * (1 - a⁻¹ * Y)⁻¹ * (1 - Y ^ 2)) := by
  have s1 := hasSum_geometric_of_norm_lt_one h1
  have s2 := (hasSum_geometric_of_norm_lt_one h2).mul_left (a⁻¹ * Y)
  have n1 : 1 - a * Y ≠ 0 := sub_ne_zero.2 fun h => by rw [← h] at h1; simp at h1
  have n2 : 1 - a⁻¹ * Y ≠ 0 := sub_ne_zero.2 fun h => by rw [← h] at h2; simp at h2
  have t1 : (fun m : ℕ => Y ^ |(m : ℤ)| * a ^ (m : ℤ)) = fun m => (a * Y) ^ m := funext fun m => by
    simp [mul_pow, mul_comm]
  have t2 : (fun m : ℕ => Y ^ |-((m : ℤ) + 1)| * a ^ (-((m : ℤ) + 1))) = fun m => a⁻¹ * Y * (a⁻¹ * Y) ^ m :=
    funext fun m => by
      rw [abs_neg, abs_of_nonneg (by positivity), ← pow_succ', mul_pow, _root_.zpow_neg, inv_pow, mul_comm]
      norm_cast
  have := HasSum.of_nat_of_neg_add_one (f := fun e : ℤ => Y ^ |e| * a ^ e) (t1 ▸ s1) (t2 ▸ s2)
  have hb : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have e : (1 - a * Y)⁻¹ * (1 - a⁻¹ * Y)⁻¹ * (1 - Y ^ 2) =
      (1 - a * Y)⁻¹ + a⁻¹ * Y * (1 - a⁻¹ * Y)⁻¹ := by
    have i1 := mul_inv_cancel₀ n1
    have i2 := mul_inv_cancel₀ n2
    generalize (1 - a * Y)⁻¹ = u at *
    generalize (1 - a⁻¹ * Y)⁻¹ = w at *
    generalize a⁻¹ = b at *
    linear_combination u * i2 + b * Y * w * i1 + u * w * Y ^ 2 * hb
  rw [e]
  exact this

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem act_one {π : Representation ℂ (GL (Fin 1) k) V} {a : Fin 1 → ℂˣ} (ha : HasSatake π a) (y : kˣ) (v : V) :
    π (diagT k (Fin 1) fun _ => y) v = (unrChar k (a 0) y : ℂ) • v := by
  refine GlobalTheory.SmGL.Model.scalar_of_isSubquotient ha.2.2 (fun f => ?_) v
  ext x
  have h1 := parInd_law (points (Fin 1)) _ f ⟨_, leviEmb_mem_parab k _ (leviTorus k _ fun _ => y)⟩ x
  rw [leviProj_leviEmb] at h1
  have hc : x * (diagT k (Fin 1) fun _ => y) = (diagT k (Fin 1) fun _ => y) * x := by
    ext i j
    simp [Matrix.mul_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0]
  show f.1.1 (x * (diagT k (Fin 1) fun _ => y)) = (unrChar k (a 0) y : ℂ) • f.1.1 x
  rw [hc]
  refine h1.trans ?_
  have hm : modExp (fun _ : Fin 1 => Unit) 0 = 0 := by rw [modExp_fin _ (fun _ => by simp)]; simp
  simp [deltaHalf_apply, hm]

theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; simp at hx; exact uniformizer_ne_zero hx.symm), hx⟩

theorem rank_one [MeasurableSpace (GL (Fin 1) k)] [BorelSpace (GL (Fin 1) k)]
    (μ : Measure (GL (Fin 1) k)) [μ.IsHaarMeasure] (hμ : μ (KO k (Fin 1)) = 1)
    (π : Representation ℂ (GL (Fin 1) k) V) (α : Fin 1 → ℂˣ) (hπ : HasSatake π α)
    (ω : GL (Fin 1) k → ℂ) (hω : IsZonal π (KO k (Fin 1)) ω) :
    ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      Integrable (fun g => sphSection k (Fin 1) s (io k (Fin 1) (g, 1)) * ω g) μ ∧
      ∫ g, sphSection k (Fin 1) s (io k (Fin 1) (g, 1)) * ω g ∂μ =
        lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) *
          invNormFactor (resCard k) 1 s := by
  obtain ⟨ϖ, hϖ⟩ := exists_unif (k := k)
  have hq1 : (1 : ℝ) < resCard k := by exact_mod_cast one_lt_resCard k
  have hq0 : 0 < resCard k := zero_lt_one.trans (one_lt_resCard k)
  have hqc : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  set M : ℝ := max ‖(α 0 : ℂ)‖ ‖(α 0 : ℂ)⁻¹‖ with hM
  have hM0 : 0 < M := lt_max_of_lt_left (norm_pos_iff.2 (α 0).ne_zero)
  refine ⟨Real.logb (resCard k) M, fun s hs => ?_⟩
  set Y : ℂ := (resCard k : ℂ) ^ (-(s + 1 / 2)) with hY
  have hMY : M * ‖Y‖ < 1 := by
    rw [hY, Complex.norm_natCast_cpow_of_pos hq0]
    have : M < (resCard k : ℝ) ^ (s.re + 1 / 2) := by
      rw [← Real.logb_lt_iff_lt_rpow hq1 hM0]; linarith
    have e : (-(s + 1 / 2)).re = -(s.re + 1 / 2) := by simp
    rw [e, Real.rpow_neg (by positivity), mul_inv_lt_iff₀ (by positivity), one_mul]
    exact this
  have h1 : ‖(α 0 : ℂ) * Y‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (by gcongr; exact le_max_left _ _) hMY
  have h2 : ‖(α 0 : ℂ)⁻¹ * Y‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (by gcongr; exact le_max_right _ _) hMY
  have hS := hasSum_bilateral (α 0).ne_zero h1 h2
  let E : {e : Fin 1 → ℤ // Antitone e} ≃ ℤ :=
    { toFun := fun e => e.1 0
      invFun := fun m => ⟨fun _ => m, antitone_const⟩
      left_inv := fun e => by ext i; simp [Subsingleton.elim i 0]
      right_inv := fun _ => rfl }
  set f : GL (Fin 1) k → ℂ := fun g => sphSection k (Fin 1) s (io k (Fin 1) (g, 1)) * ω g with hf
  have hb : ∀ g, ∀ x ∈ KO k (Fin 1), ∀ y ∈ KO k (Fin 1), f (x * g * y) = f g := fun g x hx y hy => by
    simp only [hf]
    rw [sphSection_io_biinv s g hx hy, zonal_biinv hω g hx hy]
  have hval : ∀ e : Fin 1 → ℤ, f (torusElt k (Fin 1) ϖ e) = Y ^ |e 0| * (α 0 : ℂ) ^ e 0 := fun e => by
    simp only [hf]
    rw [sphSection_torusElt hϖ]
    obtain ⟨v, -, l, -, hl, hω⟩ := hω
    have e1 : torusElt k (Fin 1) ϖ e = diagT k (Fin 1) fun _ => ϖ ^ e 0 := by
      unfold torusElt; congr 1; funext i; rw [Subsingleton.elim i 0]
    rw [hω, e1, act_one hπ, map_smul, hl, map_zpow, unrChar_uniformizer k _ hϖ, hY, ← Complex.cpow_mul_int]
    simp [add_comm]
  have hvol : ∀ e : Fin 1 → ℤ, μ (cell k (Fin 1) ϖ e) = 1 := fun e => by
    have : cell k (Fin 1) ϖ e = torusElt k (Fin 1) ϖ e • (KO k (Fin 1) : Set (GL (Fin 1) k)) := by
      ext g
      rw [cell, DoubleCoset.mem_doubleCoset]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        refine ⟨x * y, mul_mem hx hy, ?_⟩
        have hc : x * torusElt k (Fin 1) ϖ e = torusElt k (Fin 1) ϖ e * x := by
          ext i j
          simp [Matrix.mul_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0]
        show torusElt k (Fin 1) ϖ e * (x * y) = _
        rw [hc, mul_assoc]
      · rintro ⟨y, hy, rfl⟩
        exact ⟨1, one_mem _, y, hy, by simp⟩
    rw [this, measure_smul, hμ]
  have hconst : ∀ e : Fin 1 → ℤ, Set.EqOn f (fun _ => f (torusElt k (Fin 1) ϖ e)) (cell k (Fin 1) ϖ e) :=
    fun e g hg => by
      obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      exact hb _ x hx y hy
  have hint : Integrable f μ := by
    rw [← integrableOn_univ, ← iUnion_cell hϖ]
    refine integrableOn_iUnion_of_summable_integral_norm (fun e => ?_) ?_
    · exact (integrableOn_const (by simp [hvol])).congr_fun (hconst e.1).symm (isOpen_cell ϖ e.1).measurableSet
    · refine ((E.summable_iff (f := fun m : ℤ => ‖Y ^ |m| * (α 0 : ℂ) ^ m‖)).2 hS.summable.norm).congr
        fun e => ?_
      rw [setIntegral_congr_fun (isOpen_cell ϖ e.1).measurableSet
        (g := fun _ => ‖f (torusElt k (Fin 1) ϖ e)‖) fun g hg => congrArg norm (hconst e.1 hg)]
      simp [Measure.real, hvol, hval, E]
  refine ⟨hint, ?_⟩
  have h3 := hasSum_cell μ hϖ hint hb
  simp only [Measure.real, hvol, hval, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at h3
  rw [h3.unique ((E.hasSum_iff (f := fun m : ℤ => Y ^ |m| * (α 0 : ℂ) ^ m)).2 hS)]
  have hY2 : Y ^ 2 = (resCard k : ℂ) ^ (-(2 * s + 1)) := by
    rw [hY, ← Complex.cpow_mul_nat]; congr 1; push_cast; ring
  rw [hY2]
  simp only [lFactor, invNormFactor, Finset.Icc_self, Finset.prod_singleton, Fin.prod_univ_one, Pi.inv_apply,
    Units.val_inv_eq_inv_val, Nat.cast_one, ← hY]

theorem rank_zero [MeasurableSpace (GL (Fin 0) k)] [BorelSpace (GL (Fin 0) k)]
    (μ : Measure (GL (Fin 0) k)) [μ.IsHaarMeasure] (hμ : μ (KO k (Fin 0)) = 1)
    (π : Representation ℂ (GL (Fin 0) k) V) (α : Fin 0 → ℂˣ)
    (ω : GL (Fin 0) k → ℂ) (hω : IsZonal π (KO k (Fin 0)) ω) (s : ℂ) :
      Integrable (fun g => sphSection k (Fin 0) s (io k (Fin 0) (g, 1)) * ω g) μ ∧
      ∫ g, sphSection k (Fin 0) s (io k (Fin 0) (g, 1)) * ω g ∂μ =
        lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) *
          invNormFactor (resCard k) 0 s := by
  have hs : ∀ g : GL (Fin 0) k, g = 1 := fun g => by ext i; exact i.elim0
  have hu : (KO k (Fin 0) : Set (GL (Fin 0) k)) = Set.univ :=
    Set.eq_univ_of_forall fun g => by rw [hs g]; exact one_mem _
  rw [hu] at hμ
  haveI : IsProbabilityMeasure μ := ⟨hμ⟩
  obtain ⟨v, -, l, -, hl, hω⟩ := hω
  have : (fun g => sphSection k (Fin 0) s (io k (Fin 0) (g, 1)) * ω g) = fun _ => 1 := funext fun g => by
    rw [hs g, hω, show ((1 : GL (Fin 0) k), (1 : GL (Fin 0) k)) = 1 from rfl, map_one, sphSection_one]
    simpa using hl
  rw [this]
  simp [lFactor, invNormFactor]

end GlobalTheory.GLDoubling.Model
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsAdmissibleSubOfFiniteDimensional
section
noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix
open GlobalTheory.SmoothGlob (lieSet)
open scoped ContDiff

namespace GlobalTheory.GKModule

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def kFinVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Submodule ℂ H :=
  GlobalTheory.KFiniteVectors.kFiniteVectors ε σ

@[simp] theorem mem_kFinVec {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H} :
    v ∈ kFinVec ε σ ↔ IsKFin ε σ v := Iff.rfl

theorem isKStableOn_kFinVec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsKStableOn ε σ (kFinVec ε σ) := by
  rintro g hg v ⟨S, hS, hv, hSK⟩
  exact ⟨S, hS, hSK g hg v hv, hSK⟩

structure IsGKSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) : Prop where
  smooth : ∀ v ∈ V, SmoothVec (lieSet ε) σ v
  kFin : ∀ v ∈ V, IsKFin ε σ v
  kStable : IsKStableOn ε σ V
  lieStable : ∀ X ∈ lieSet ε, ∀ v ∈ V, dRep σ X v ∈ V

def IsAdmissibleSub (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) : Prop :=
  ∀ Λ : Fin n → ℝ, FiniteDimensional ℂ (sSup {S | S ≤ V ∧ IsKTypeOf ε σ Λ S} : Submodule ℂ H)

def IsGKHom {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (ε : Fin n → Bool) (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁))
    (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)) (e : kFinVec ε σ₁ →ₗ[ℂ] kFinVec ε σ₂) : Prop :=
  (∀ k ∈ Kset ε, ∀ v w : kFinVec ε σ₁, (w : H₁) = σ₁ k v → (e w : H₂) = σ₂ k (e v)) ∧
    ∀ X ∈ lieSet ε, ∀ v w : kFinVec ε σ₁, (w : H₁) = dRep σ₁ X v → (e w : H₂) = dRep σ₂ X (e v)

theorem isGKHom_id (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsGKHom ε σ σ LinearMap.id :=
  ⟨fun _ _ _ _ h => h, fun _ _ _ _ h => h⟩

theorem isAdmissibleSub_of_finiteDimensional (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (V : Submodule ℂ H) [FiniteDimensional ℂ V] : IsAdmissibleSub ε σ V :=
  fun _ => Submodule.finiteDimensional_of_le (sSup_le fun _ hS => hS.1)

theorem IsAdmissibleSub.mono {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {V W : Submodule ℂ H}
    (h : IsAdmissibleSub ε σ W) (hle : V ≤ W) : IsAdmissibleSub ε σ V := fun Λ =>
  haveI := h Λ
  Submodule.finiteDimensional_of_le (sSup_le_sSup (t := {S | S ≤ W ∧ IsKTypeOf ε σ Λ S})
    fun _ hS => ⟨hS.1.trans hle, hS.2⟩)

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem contDiff_det_expProd {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod).det := by
  have he : ∀ a b, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
      ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) a b := fun a b =>
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)).contDiff.comp
      (GlobalTheory.GardingVec.contDiff_expProd Xs)
  simp only [Matrix.det_apply']
  exact ContDiff.sum fun s _ => contDiff_const.mul (contDiff_prod fun i _ => he _ _)

end

theorem isURepOn_det (ε : Fin n → Bool) : IsURepOn (UJset ε) (fun g => g.det • (1 : H →L[ℂ] H)) := by
  refine ⟨⟨by simp, fun a _ b _ => by ext; simp [smul_smul, mul_comm]⟩, fun g hg v => ?_, fun v => ?_⟩
  · have h1 : ‖g.det‖ = 1 := by simpa using (GlobalTheory.Published.det_isURepOn ε).1.2.1 g hg 1
    simp [norm_smul, h1]
  · have : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => g.det • v :=
      (continuous_id.matrix_det).smul continuous_const
    simpa using this.continuousOn

theorem isGKSub_det (ε : Fin n → Bool) (V : Submodule ℂ H) [FiniteDimensional ℂ V] :
    IsGKSub ε (fun g => g.det • (1 : H →L[ℂ] H)) V ∧ IsAdmissibleSub ε (fun g => g.det • (1 : H →L[ℂ] H)) V := by
  have hK : IsKStableOn ε (fun g => g.det • (1 : H →L[ℂ] H)) V := fun g _ v hv => V.smul_mem _ hv
  refine ⟨⟨fun v _ k Xs _ => ?_, fun v hv => ⟨V, inferInstance, hv, hK⟩, hK, fun X _ v hv => ?_⟩,
    isAdmissibleSub_of_finiteDimensional _ _ _⟩
  · exact (contDiff_det_expProd Xs).smul contDiff_const
  · have h1 : ContDiff ℝ ∞ fun t : ℝ => (NormedSpace.exp (t • X)).det := by
      have := (contDiff_det_expProd (fun _ : Fin 1 => X)).comp
        (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (t : ℝ) (_ : Fin 1) => t)
      simpa [Function.comp_def] using this
    have h2 := ((h1.differentiable (by simp)) 0).hasDerivAt.smul_const v
    have h3 : dRep (fun g => g.det • (1 : H →L[ℂ] H)) X v = _ := h2.deriv
    rw [h3]
    exact V.smul_mem _ hv

theorem mem_UJset_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    k ∈ UJset ε := by
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  change kᴴ * Jm ε * k = Jm ε
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem conjTranspose_mem_UJset_of_mem_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) :
    kᴴ ∈ UJset ε := by
  have h1 : k * kᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hk.1
  change kᴴᴴ * Jm ε * kᴴ = Jm ε
  rw [Matrix.conjTranspose_conjTranspose, hk.2, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem dRep_mem_of_isClosed {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {W : Submodule ℂ H}
    (hc : IsClosed (W : Set H)) (hW : ∀ g ∈ UJset ε, ∀ w ∈ W, σ g w ∈ W) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ lieSet ε) {v : H} (hv : v ∈ W) : dRep σ X v ∈ W := by
  have hm : ∀ t : ℝ, σ (NormedSpace.exp (t • X)) v ∈ W := fun t =>
    hW _ (GlobalTheory.GardingVec.exp_mem (IsUnit.of_mul_eq_one _ (Jm_mul_self ε)) hX t) v hv
  unfold dRep
  by_cases hd : DifferentiableAt ℝ (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) 0
  · refine hc.mem_of_tendsto (hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt)
      (Filter.Eventually.of_forall fun t => ?_)
    rw [slope_def_module]
    exact (W.restrictScalars ℝ).smul_mem _ (W.sub_mem (hm t) (hm 0))
  · rw [deriv_zero_of_not_differentiableAt hd]
    exact W.zero_mem

theorem starProjection_comm {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hU : IsURepOn (UJset ε) σ) {W : Submodule ℂ H} [W.HasOrthogonalProjection]
    (hW : ∀ g ∈ UJset ε, ∀ w ∈ W, σ g w ∈ W) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) (x : H) :
    W.starProjection (σ k x) = σ k (W.starProjection x) := by
  have hk1 := mem_UJset_of_mem_Kset hk
  have hk2 := conjTranspose_mem_UJset_of_mem_Kset hk
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hW k hk1 _ (W.starProjection_apply_mem x))
    fun w hw => ?_
  have h1 : σ k (σ kᴴ w) = w := by
    have := hU.1.2 k hk1 kᴴ hk2
    rw [show k * kᴴ = 1 from Matrix.mem_unitaryGroup_iff.1 hk.1, hU.1.1] at this
    exact (congrArg (fun A : H →L[ℂ] H => A w) this).symm
  let L : H →ₗᵢ[ℂ] H := ⟨(σ k : H →ₗ[ℂ] H), hU.2.1 k hk1⟩
  have h2 := L.inner_map_map (x - W.starProjection x) (σ kᴴ w)
  rw [W.starProjection_inner_eq_zero x _ (hW _ hk2 w hw)] at h2
  change inner ℂ (σ k (x - W.starProjection x)) (σ k (σ kᴴ w)) = 0 at h2
  rwa [h1, map_sub] at h2

end GlobalTheory.GKModule

namespace GlobalTheory.Published

open GlobalTheory.GKModule

def AdmissibleClosure : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ →
    ∀ V : Submodule ℂ H, IsGKSub ε σ V → IsAdmissibleSub ε σ V →
      (∀ g ∈ UJset ε, ∀ w ∈ V.topologicalClosure, σ g w ∈ V.topologicalClosure) ∧
        ∀ w ∈ V.topologicalClosure, IsKFin ε σ w → w ∈ V

def InfinitesimalEquivalence : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool)
    (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [Nontrivial H₁]
    (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] [Nontrivial H₂]
    (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)) (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)),
    IsURepOn (UJset ε) σ₁ → IsIrredOn (UJset ε) σ₁ → IsURepOn (UJset ε) σ₂ → IsIrredOn (UJset ε) σ₂ →
    ∀ e : kFinVec ε σ₁ ≃ₗ[ℂ] kFinVec ε σ₂, IsGKHom ε σ₁ σ₂ e.toLinearMap →
      ∃ (U : H₁ ≃ₗᵢ[ℂ] H₂) (c : ℝ), 0 < c ∧ (∀ g ∈ UJset ε, ∀ x, U (σ₁ g x) = σ₂ g (U x)) ∧
        ∀ v : kFinVec ε σ₁, U v = (c : ℂ) • (e v : H₂)

def GKGlobalisation : Prop := AdmissibleClosure ∧ InfinitesimalEquivalence

section Consequences

variable {n : ℕ} {ε : Fin n → Bool}

theorem AdmissibleClosure.irreducible (h : AdmissibleClosure) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hU : IsURepOn (UJset ε) σ) {V : Submodule ℂ H} (hV : IsGKSub ε σ V) (hA : IsAdmissibleSub ε σ V)
    (hirr : ∀ V' ≤ V, IsGKSub ε σ V' → V' = ⊥ ∨ V' = V) {W : Submodule ℂ H} (hc : IsClosed (W : Set H))
    (hle : W ≤ V.topologicalClosure) (hW : ∀ g ∈ UJset ε, ∀ w ∈ W, σ g w ∈ W) :
    W = ⊥ ∨ W = V.topologicalClosure := by
  have hsub : IsGKSub ε σ (V ⊓ W) :=
    ⟨fun v hv => hV.smooth v hv.1, fun v hv => hV.kFin v hv.1,
      fun k hk v hv => ⟨hV.kStable k hk v hv.1, hW k (mem_UJset_of_mem_Kset hk) v hv.2⟩,
      fun X hX v hv => ⟨hV.lieStable X hX v hv.1, dRep_mem_of_isClosed hc hW hX hv.2⟩⟩
  rcases hirr _ inf_le_left hsub with h0 | h1
  · left
    have : CompleteSpace W := hc.completeSpace_coe
    have hperp : V ≤ Wᗮ := fun v hv => by
      obtain ⟨S, hS, hvS, hSK⟩ := hV.kFin v hv
      have hPW := W.starProjection_apply_mem v
      have hfin : IsKFin ε σ (W.starProjection v) := by
        refine ⟨S.map (W.starProjection : H →ₗ[ℂ] H), inferInstance, ⟨v, hvS, rfl⟩, ?_⟩
        rintro k hk _ ⟨x, hx, rfl⟩
        exact ⟨σ k x, hSK k hk x hx, starProjection_comm hU hW hk x⟩
      have hmem : W.starProjection v ∈ V ⊓ W := ⟨(h n ε H σ hU V hV hA).2 _ (hle hPW) hfin, hPW⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact (Submodule.starProjection_apply_eq_zero_iff W).1 hmem
    have hcl : V.topologicalClosure ≤ Wᗮ := V.topologicalClosure_minimal hperp W.isClosed_orthogonal
    exact (W.orthogonal_disjoint).eq_bot_of_le (hle.trans hcl)
  · exact Or.inr (le_antisymm hle (V.topologicalClosure_minimal (inf_eq_left.1 h1) hc))

theorem infinitesimalEquivalence_hyp_det (ε : Fin n → Bool) :
    IsURepOn (UJset ε) (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) ∧ IsIrredOn (UJset ε) (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) ∧
      kFinVec ε (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) = ⊤ ∧
      IsGKHom ε (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) (fun g => g.det • (1 : ℂ →L[ℂ] ℂ))
        (LinearEquiv.refl ℂ _).toLinearMap :=
  ⟨(det_isURepOn ε).1, (det_isURepOn ε).2.1, eq_top_iff.2 fun v _ => (det_isURepOn ε).2.2 v, isGKHom_id _ _⟩

end Consequences

end GlobalTheory.Published

end
end

