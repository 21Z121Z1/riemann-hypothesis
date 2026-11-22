import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0047
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
import Formalism.QuotientMetricDivisors.Statement
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0050

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorusWeightOfPolyRepGLComplexStatement
section
open Matrix GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusWeight_of_polyRep_GL_complex : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∃ μ : Fin n → ℤ, IsWt Φ μ := by
  first | exact @GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep | exact GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep | (intros; apply GlobalTheory.AlgWtHW.exists_isWt_of_isPolyRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtensionAcrossCoordinateHyperplanesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_extension_across_coordinate_hyperplanes : ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ) ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → F z = Φ z := by
  first | exact @GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes | exact GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes | (intros; apply GlobalTheory.HyperplaneExt.extension_across_coordinate_hyperplanes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteShiftsVanishingLeadingMinorStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_shifts_vanishing_leading_minor : ∀ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ), Set.Finite {s : ℂ | ¬ ∀ (k : ℕ) (hk : k ≤ n), ((B + s • (1 : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0} := by
  first | exact @GlobalTheory.shift_minors_vanish_finite | exact GlobalTheory.shift_minors_vanish_finite | (intros; apply GlobalTheory.shift_minors_vanish_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusRestrictScalarsPowModInertiaStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_restrictScalars_pow_mod_inertia : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] [NumberField K] (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 K)), w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w → IsPlaceOver A v ∧ normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 E) ∧ (∀ ι ∈ Ine (F := K) A, ι.restrictScalars E ∈ Ine (F := E) A) ∧ ∀ (σ : G K Ω) (φ : G E Ω), IsFrob A (normV w) σ → IsFrob A (normV v) φ → σ.restrictScalars E * (φ ^ w.asIdeal.inertiaDeg (𝓞 E))⁻¹ ∈ Ine (F := E) A := by
  first | exact @GlobalTheory.FrobRestrict.frob_restrict | exact GlobalTheory.FrobRestrict.frob_restrict | (intros; apply GlobalTheory.FrobRestrict.frob_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlRelOfCanonicalCommutationRelationsStatement
section
open Matrix GlobalTheory.Mem.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glRel_of_canonicalCommutationRelations : ∀ (A : Type) [Ring A] (n m : ℕ) (x d : Fin n × Fin m → A), IsCCR x d → Formalism.REAL.GlRel (fun i j : Fin n => ∑ a, x (i, a) * d (j, a)) ∧ Formalism.REAL.GlRel (fun a b : Fin m => -∑ i, x (i, b) * d (i, a)) := by
  first | exact @GlobalTheory.Mem.Lift.glRel_of_isCCR | exact GlobalTheory.Mem.Lift.glRel_of_isCCR | (intros; apply GlobalTheory.Mem.Lift.glRel_of_isCCR <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianDualLatticeBaseChange
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Mem.DualBC

variable {K : Type} [Field K] [NumberField K] [StarRing K]

omit [NumberField K] in

theorem mem_dual_iff {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (A : Submodule (𝓞 K) (Fin d → K)) (x : Fin d → K) :
    x ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A ↔
      ∀ y ∈ A, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = Formalism.DivisionValues.hform H y x := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]

omit [NumberField K] in

theorem hform_eq {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (x y : Fin d → K) :
    Formalism.DivisionValues.hform H x y = ∑ j, star (x j) * (H.mulVec y) j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul]
  ring

omit [NumberField K] in

theorem star_int (c : 𝓞 K) : algebraMap (𝓞 K) K (Formalism.DivisionValues.cO K c) = star (algebraMap (𝓞 K) K c) := rfl

omit [StarRing K] in

theorem exists_extend {d : ℕ} (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsLattice K A)
    (f : A →ₗ[𝓞 K] 𝓞 K) :
    ∃ F : (Fin d → K) →ₗ[K] K, ∀ x : A, F x = algebraMap (𝓞 K) K (f x) := by
  classical
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨s, hs, b, hb, hsA⟩ := Formalism.HermitianLatticesTheory.dualLattice_basis (R := 𝓞 K) A hA.span_eq_top
  obtain ⟨c, hc0, hc⟩ := Formalism.HermitianLatticesTheory.dualLattice_denom (R := 𝓞 K) b A hA.fg
  have hbA : ∀ i, b i ∈ A := fun i => by rw [hb i]; exact hsA i.2
  let F : (Fin d → K) →ₗ[K] K := b.constr K (fun i => algebraMap (𝓞 K) K (f ⟨b i, hbA i⟩))
  let F' : A →ₗ[𝓞 K] K := (F.restrictScalars (𝓞 K)).comp A.subtype
  let g' : A →ₗ[𝓞 K] K := (Algebra.linearMap (𝓞 K) K).comp f
  let P : Submodule (𝓞 K) (Fin d → K) := (LinearMap.eqLocus F' g').map A.subtype
  have hspan : Submodule.span (𝓞 K) (Set.range b) ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨b i, hbA i⟩, ?_, rfl⟩
    show F (b i) = algebraMap (𝓞 K) K (f ⟨b i, hbA i⟩)
    exact b.constr_basis K _ i
  refine ⟨F, fun x => ?_⟩
  obtain ⟨z, hz, hzx⟩ := hspan (hc x x.2)
  have hz' : z = c • x := Subtype.ext (by simpa using hzx)
  have hzF : F' z = g' z := hz
  rw [hz', map_smul, map_smul] at hzF
  simp only [F', g', LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.restrictScalars_apply,
    Algebra.linearMap_apply, Algebra.smul_def] at hzF
  exact mul_left_cancel₀ (by simpa using hc0) hzF

theorem exists_family {d : ℕ} (H : Matrix (Fin d) (Fin d) K) (hH : IsUnit H.det)
    (A : Submodule (𝓞 K) (Fin d → K)) (hA : Submodule.IsLattice K A) :
    ∃ (n : ℕ) (a b : Fin n → Fin d → K), (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A) ∧
      ∀ y, y = ∑ i, Formalism.DivisionValues.hform H (a i) y • b i := by
  classical
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨n, g, f, hgf⟩ := Formalism.HermitianLatticesTheory.finitely_generated_projective_coords (K := K) A hA.fg hinj
  choose F hF using fun i => exists_extend A hA (f i)
  let w : Fin n → Fin d → K := fun i => H⁻¹.mulVec (fun j => star (F i (Pi.single j 1)))
  have hFcoord : ∀ i (y : Fin d → K), F i y = ∑ j, y j * F i (Pi.single j 1) := by
    intro i y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (y j) : Fin d → K) = y j • Pi.single j 1 by
      ext k; by_cases hk : k = j <;> simp [hk], map_smul, smul_eq_mul]
  have hw : ∀ i (y : Fin d → K), Formalism.DivisionValues.hform H y (w i) = star (F i y) := by
    intro i y
    rw [hform_eq, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hH, Matrix.one_mulVec, hFcoord,
      star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul']
  have hexp : ∀ y : Fin d → K, y = ∑ i, F i y • (g i : Fin d → K) := by
    have hT : (∑ i, (F i).smulRight (g i : Fin d → K)) = LinearMap.id := by
      refine LinearMap.ext_on hA.span_eq_top fun x hx => ?_
      have h1 := congrArg (fun v : A => (v : Fin d → K)) (hgf ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      conv_rhs => rw [h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hF i ⟨x, hx⟩, algebraMap_smul]
    intro y
    have := LinearMap.congr_fun hT y
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply] at this
    exact this.symm
  have hnd : ∀ z : Fin d → K, (∀ u, Formalism.DivisionValues.hform H u z = 0) → z = 0 := by
    intro z hz
    have hHz : H.mulVec z = 0 := by
      ext i
      have := hz (Pi.single i 1)
      rw [hform_eq, Finset.sum_eq_single i (fun j _ hj => by simp [hj])
        (by simp)] at this
      simpa using this
    rw [← Matrix.one_mulVec z, ← Matrix.nonsing_inv_mul _ hH, ← Matrix.mulVec_mulVec, hHz,
      Matrix.mulVec_zero]
  refine ⟨n, fun i => (g i : Fin d → K), w, fun i => (g i).2, fun i => ?_, fun y => ?_⟩
  · rw [mem_dual_iff]
    intro y hy
    refine ⟨Formalism.DivisionValues.cO K (f i ⟨y, hy⟩), ?_⟩
    rw [star_int, hw, hF i ⟨y, hy⟩]
  · refine (sub_eq_zero.1 (hnd _ fun u => ?_)).symm
    rw [map_sub, sub_eq_zero, map_sum]
    conv_rhs => rw [hexp u]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, hw, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, mul_comm]

theorem dual_baseChange : ∀ (K K' : Type) [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K'] (φ : K →+* K') (d d' : ℕ)
  (G : Matrix (Fin d') (Fin d) K'), Function.Bijective G.mulVec → ∀ (H : Matrix (Fin d) (Fin d) K) (H' : Matrix (Fin d') (Fin d') K'),
  (∀ x y : Fin d → K, Formalism.DivisionValues.hform H' (Matrix.mulVec G fun k => φ (x k)) (Matrix.mulVec G fun k => φ (y k)) = φ (Formalism.DivisionValues.hform H x y)) →
  IsUnit H.det → ∀ A : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K A →
    Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H')
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K)))) =
    Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) ''
      ((Formalism.HermitianLatticesTheory.dual (Formalism.DivisionValues.hform H) A : Submodule (𝓞 K) (Fin d → K)) : Set (Fin d → K))) := by
  intro K K' _ _ _ _ _ _ φ d d' G hG H H' hHH' hH A hA
  classical
  set ι : (Fin d → K) → (Fin d' → K') := fun x => Matrix.mulVec G fun k => φ (x k) with hι
  have ι_add : ∀ x y, ι (x + y) = ι x + ι y := by
    intro x y
    simp only [hι, Pi.add_apply, map_add]
    rw [← Matrix.mulVec_add]
    rfl
  have ι_smul : ∀ (c : K) x, ι (c • x) = φ c • ι x := by
    intro c x
    simp only [hι, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [← Matrix.mulVec_smul]
    rfl
  have ι_sum : ∀ {m : ℕ} (v : Fin m → Fin d → K), ι (∑ i, v i) = ∑ i, ι (v i) := by
    intro m v
    simp only [hι, Finset.sum_apply, map_sum]
    rw [← Matrix.mulVec_sum]
    congr 1
    ext k
    simp [Finset.sum_apply]
  have ι_single : ∀ k : Fin d, ι (Pi.single k 1) = G.mulVec (Pi.single k 1) := by
    intro k
    simp only [hι]
    congr 1
    ext j
    by_cases hj : j = k <;> simp [hj]
  have hspanι : Submodule.span K' (Set.range ι) = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨v, rfl⟩ := hG.2 z
    rw [← Finset.univ_sum_single v, Matrix.mulVec_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [show (Pi.single k (v k) : Fin d → K') = v k • Pi.single k 1 by
      ext j; by_cases hj : j = k <;> simp [hj], Matrix.mulVec_smul, ← ι_single]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hιH : ∀ x y, Formalism.DivisionValues.hform H' (ι x) (ι y) = φ (Formalism.DivisionValues.hform H x y) := hHH'
  apply le_antisymm
  · intro x hx
    obtain ⟨n, a, b, ha, hb, hab⟩ := exists_family H hH A hA
    have hT : (∑ i, (Formalism.DivisionValues.hform H' (ι (a i))).smulRight (ι (b i))) = LinearMap.id := by
      refine LinearMap.ext_on hspanι ?_
      rintro _ ⟨y, rfl⟩
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply,
        hιH]
      conv_rhs => rw [hab y]
      rw [ι_sum]
      simp only [ι_smul]
    have hx' : x = ∑ i, Formalism.DivisionValues.hform H' (ι (a i)) x • ι (b i) := by
      have := LinearMap.congr_fun hT x
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply,
        LinearMap.id_apply] at this
      exact this.symm
    rw [hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := (mem_dual_iff H' _ x).1 hx (ι (a i))
      (Submodule.subset_span ⟨a i, ha i, rfl⟩)
    rw [← hc, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b i, hb i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, mem_dual_iff]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      obtain ⟨c, hc⟩ := (mem_dual_iff H A z).1 hz y hy
      refine ⟨RingOfIntegers.mapRingHom φ c, ?_⟩
      rw [hιH, ← hc]
      rfl
    | zero => exact ⟨0, by simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨c₁, hc₁⟩ := h₁
      obtain ⟨c₂, hc₂⟩ := h₂
      exact ⟨c₁ + c₂, by rw [map_add, map_add, LinearMap.add_apply, hc₁, hc₂]⟩
    | smul r y _ h =>
      obtain ⟨c, hc⟩ := h
      refine ⟨Formalism.DivisionValues.cO K' r * c, ?_⟩
      rw [← algebraMap_smul K' r y, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, hc,
        star_int, starRingEnd_apply]

end GlobalTheory.Mem.DualBC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaLiftOfResidualTrivial
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

namespace GlobalTheory.InertiaLift

theorem exists_mem_Ine_eq_on : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w →
    ∀ (L : IntermediateField E Ω) (ψ : G E Ω), ψ ∈ Dec (F := E) A →
    (∀ x ∈ L, IsIntegral ℤ x → A.valuation (ψ x - x) < 1) →
    ∃ ι ∈ Ine (F := E) A, ∀ x ∈ L, ι x = ψ x := by
  intro E Ω _ _ _ _ _ A w _ L ψ hψ hL
  letI : TopologicalSpace (IntCl E Ω) := ⊥
  haveI : DiscreteTopology (IntCl E Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl E Ω
  let H := L.fixingSubgroup
  have hH : IsClosed (H : Set (Ω ≃ₐ[E] Ω)) := by
    have e : (H : Set (Ω ≃ₐ[E] Ω)) = ⋂ x : L, ((MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω) :
        Subgroup (Ω ≃ₐ[E] Ω)) : Set (Ω ≃ₐ[E] Ω)) := by
      ext σ
      simp only [Set.mem_iInter, SetLike.mem_coe, MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      rw [IntermediateField.mem_fixingSubgroup_iff]
      exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩
    rw [e]
    exact isClosed_iInter fun x =>
      (MulAction.stabilizer (Ω ≃ₐ[E] Ω) (x : Ω)).isClosed_of_isOpen
        (stabilizer_isOpen_of_isIntegral (K := E) (x : Ω))
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let Q := primeBelow (F := E) A
  let R' := FixedPoints.subalgebra (𝓞 E) (IntCl E Ω) H
  have hR' : ∀ b : R', ∀ k ∈ H, k • (b : IntCl E Ω) = b := fun b k hk => b.2 ⟨k, hk⟩
  have : SMulCommClass H R' (IntCl E Ω) := ⟨fun k r b => by
    change (k : Ω ≃ₐ[E] Ω) • ((r : IntCl E Ω) * b) = (r : IntCl E Ω) * (k : Ω ≃ₐ[E] Ω) • b
    rw [smul_mul', hR' r k k.2]⟩
  have : Algebra.IsInvariant R' (IntCl E Ω) H := ⟨fun b hb => ⟨⟨b, hb⟩, rfl⟩⟩
  have : Q.LiesOver (Q.under R') := ⟨rfl⟩
  have hψQ : ψ • Q = Q := by
    have h1 : ψ • A = A := hψ
    rw [← primeBelow_smul, h1]
  have hfix : ∀ r : R', ψ • (r : IntCl E Ω) - r ∈ Q := by
    intro r
    have hrL : ((r : IntCl E Ω) : Ω) ∈ L := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup L, IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hR' r f hf)
    exact hL _ hrL (isIntegral_int_of_isIntegral (r : IntCl E Ω).2)
  let φ : (IntCl E Ω ⧸ Q) ≃ₐ[R' ⧸ Q.under R'] (IntCl E Ω ⧸ Q) := AlgEquiv.ofRingEquiv
    (f := Ideal.quotientEquiv Q Q (MulSemiringAction.toRingEquiv (Ω ≃ₐ[E] Ω) (IntCl E Ω) ψ)
      hψQ.symm)
    (fun r => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q (ψ • (r : IntCl E Ω)) = Ideal.Quotient.mk Q (r : IntCl E Ω)
      rw [Ideal.Quotient.eq]
      exact hfix r)
  obtain ⟨⟨v, hvQ⟩, hv⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := H)
    (Q.under R') Q φ
  refine ⟨ψ * (v : Ω ≃ₐ[E] Ω)⁻¹, GlobalTheory.InertiaMovesRoot.mem_Ine_of_cong fun b => ?_, fun x hx => ?_⟩
  · have h1 : Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω) • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b)) =
        Ideal.Quotient.mk Q (ψ • ((v : Ω ≃ₐ[E] Ω)⁻¹ • b)) :=
      DFunLike.congr_fun hv (Ideal.Quotient.mk Q ((v : Ω ≃ₐ[E] Ω)⁻¹ • b))
    rw [smul_inv_smul, eq_comm, Ideal.Quotient.eq] at h1
    rwa [mul_smul]
  · have hv' : ((v : Ω ≃ₐ[E] Ω)⁻¹) x = x :=
      (IntermediateField.mem_fixingSubgroup_iff L _).mp (H.inv_mem v.2) x hx
    rw [AlgEquiv.mul_apply, hv']

end GlobalTheory.InertiaLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntValuationNormEqSumResidueDegreeMulStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intValuation_norm_eq_sum_residueDegree_mul : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (a : Kˣ) (s : Finset (HeightOneSpectrum (𝓞 K))), (∀ w, w ∈ s ↔ w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) = v.asIdeal) → WithZero.log (v.valuation E (Algebra.norm E (a : K))) = ∑ w ∈ s, (w.asIdeal.inertiaDeg (𝓞 E) : ℤ) * WithZero.log (w.valuation K (a : K)) := by
  first | exact @GlobalTheory.NormValuation.log_valuation_norm_eq_sum | exact GlobalTheory.NormValuation.log_valuation_norm_eq_sum | (intros; apply GlobalTheory.NormValuation.log_valuation_norm_eq_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenIdeleSubgroupContainsCongruenceUnitsStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_idele_subgroup_contains_congruence_units : ∀ (F : Type) [Field F] [NumberField F] (V : Subgroup (Ideles F)), IsOpen (V : Set (Ideles F)) → ∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), S₀ ⊆ S ∧ (∀ v ∉ S, ∀ x, IsUnitAt v x → localIdele F v x ∈ V) ∧ ∀ v ∈ S, ∀ a : Fˣ, v.valuation F ((a : F) - 1) ≤ WithZero.exp (-(M : ℤ)) → locUnit F v a ∈ V := by
  first | exact @GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr | exact GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr | (intros; apply GlobalTheory.OpenIdeleCongr.open_subgroup_contains_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTorusWeightOfPolyRepCompSwapStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTorusWeightOfPolyRep_comp_swap : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ μ : Fin n → ℤ, IsWt Φ μ → ∀ i j : Fin n, IsWt Φ (μ ∘ Equiv.swap i j) := by
  first | exact @GlobalTheory.isWt_comp_swap | exact GlobalTheory.isWt_comp_swap | (intros; apply GlobalTheory.isWt_comp_swap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTotallyComplexOfAlgebraOfIsTotallyComplexStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.NormCompat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTotallyComplex_of_algebra_of_isTotallyComplex : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsTotallyComplex E], IsTotallyComplex K := by
  first | exact @GlobalTheory.isTotallyComplex_of_algebra | exact GlobalTheory.isTotallyComplex_of_algebra | (intros; apply GlobalTheory.isTotallyComplex_of_algebra <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDominStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerTransvection_mulVec_mem_spanWeightVectorsDominatedBy : ∀ {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (lam ν : Fin n → ℤ), DomLE ν lam → ∀ (w : ι → ℂ), IsWtVec Φ ν w → ∀ (i j : Fin n), j < i → ∀ (s : ℂ) (T : GL (Fin n) ℂ), T.val = transvection i j s → Φ T *ᵥ w ∈ Sle Φ lam := by
  first | exact @GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle | exact GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle | (intros; apply GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle <;> assumption)
end

