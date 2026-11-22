import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0058
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0061
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFiltrationApproxByEnvelopeKernelPower
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem dense_ker_of_bounded {A R C Q : Type} [CommRing A] [CommRing R] [CommRing C] [CommRing Q]
    (p : ℕ) (α : A →+* R) (i : R →+* C) (f : C →+* Q) (N : ℕ)
    (hd : ∀ (x : C) (r : ℕ), ∃ (s : R) (z : C), x = i s + (p : C) ^ r * z)
    (hb : ∀ x : C, ∃ a : A, (p : Q) ^ N * f x = f (i (α a)))
    (x : C) (hx : f x = 0) :
    ∃ (u : R) (z : C), f (i u) = 0 ∧ x = i u + (p : C) * z := by
  obtain ⟨s, z, rfl⟩ := hd x (N + 1)
  obtain ⟨a, ha⟩ := hb z
  refine ⟨s + (p : R) * α a, (p : C) ^ N * z - i (α a), ?_, ?_⟩
  · rw [map_add, map_mul, map_pow, map_natCast] at hx
    rw [map_add, map_mul, map_natCast, map_add, map_mul, map_natCast, ← ha, ← hx]
    ring
  · rw [map_add, map_mul, map_natCast]
    ring

theorem ev_algebraMap (l : ℕ) [Fact l.Prime] (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem fil_dense : ∀ (l : ℕ) [Fact l.Prime], ∀ j : Per.Acris l →+* Per.BdRp l, IsCrisP j → ∀ (n : ℕ) (x : Per.Acris l), j x ∈ Per.FilP l n → ∃ (u : Per.Acris0 l) (z : Per.Acris l), (u : Per.AinfP l) ∈ Per.kerP l ^ n ∧ x = algebraMap (Per.Acris0 l) (Per.Acris l) u + (l : Per.Acris l) * z := by
  intro l _ j hj n x hx
  obtain ⟨N, hN⟩ := hj.bdd n
  have h0 : ∀ u : Per.Acris0 l, ((Per.ev l n).comp j) (algebraMap (Per.Acris0 l) (Per.Acris l) u) =
      Ideal.Quotient.mk _ (u : Per.AinfP l) := fun u => by
    rw [RingHom.comp_apply, hj.on0, ev_algebraMap]
  obtain ⟨u, z, hu, hz⟩ := dense_ker_of_bounded l (algebraMap (Per.Ainf l) (Per.Acris0 l))
    (algebraMap (Per.Acris0 l) (Per.Acris l)) ((Per.ev l n).comp j) N (acris_basic l).2.2.1
    (fun y => by
      obtain ⟨a, ha⟩ := hN y
      refine ⟨a, ?_⟩
      rw [map_mul, map_pow, map_natCast] at ha
      rw [h0]
      exact ha) x ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l n (j x)).1 hx)
  refine ⟨u, z, ?_, hz⟩
  rw [h0] at hu
  exact Ideal.Quotient.eq_zero_iff_mem.1 hu

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfIsDomainAndAinfInvPInjectiveStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.usage : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Per.Ainf l) ∧ IsDomain (Per.AinfP l) ∧ Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
  first | exact @GlobalTheory.MemLoc.ainf_isDomain_and_injective | exact GlobalTheory.MemLoc.ainf_isDomain_and_injective | (intros; apply GlobalTheory.MemLoc.ainf_isDomain_and_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixChangeOfBasisStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicWeight_polyMatrix_change_of_basis : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (ι' : Type) [Fintype ι'] [DecidableEq ι'] (b' : Module.Basis ι' ℂ a.W) (P' : ι' → ι' → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → Agrees a b' P' → ∀ (τ : L →+* ℂ) (B : GL (Fin n) ℂ), evM P' (evPt τ B) = b'.toMatrix b * evM P (evPt τ B) * b.toMatrix b' := by
  first | exact @GlobalTheory.AlgWtHW.evM_change_of_basis | exact GlobalTheory.AlgWtHW.evM_change_of_basis | (intros; apply GlobalTheory.AlgWtHW.evM_change_of_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicWeightPolyMatrixMultiplicativeStatement
section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicWeight_polyMatrix_multiplicative : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), Agrees a b P → evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 ∧ ∀ X Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → IsUPt Y → evM P (upt (fun σ => X σ * Y σ)) = evM P (upt X) * evM P (upt Y) := by
  first | exact @GlobalTheory.AlgWtMul.evM_mul | exact GlobalTheory.AlgWtMul.evM_mul | (intros; apply GlobalTheory.AlgWtMul.evM_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOrbitHasNearbyFixedPointStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_orbit_has_nearby_fixed_point : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (x : Om l) (r : ℝ), (∀ g ∈ H, ‖g x - x‖ ≤ r) → ∃ y : Om l, (∀ g ∈ H, g y = y) ∧ ‖x - y‖ ≤ c * r := by
  first | exact @GlobalTheory.AxLemma.ax_lemma | exact GlobalTheory.AxLemma.ax_lemma | (intros; apply GlobalTheory.AxLemma.ax_lemma <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMatExp
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.UpqExpChart

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem continuous_matExp : Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous

theorem exists_chart : ∃ e : OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ),
    (e : Matrix n n ℂ → Matrix n n ℂ) = NormedSpace.exp ∧ (0 : Matrix n n ℂ) ∈ e.source := by
  open scoped Matrix.Norms.Operator in
  have h : HasStrictFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix n n ℂ) : Matrix n n ℂ ≃L[ℂ] Matrix n n ℂ) :
        Matrix n n ℂ →L[ℂ] Matrix n n ℂ) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)
  open scoped Matrix.Norms.Operator in
  exact ⟨h.toOpenPartialHomeomorph _, rfl, h.mem_toOpenPartialHomeomorph_source⟩

theorem exists_ball_subset {W : Set (Matrix n n ℂ)} (hW : W ∈ 𝓝 (0 : Matrix n n ℂ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Z : Matrix n n ℂ, ∑ i, ∑ j, ‖Z i j‖ < δ → Z ∈ W := by
  open scoped Matrix.Norms.Elementwise in
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hW
  refine ⟨δ, hδ, fun Z hZ => h ?_⟩
  open scoped Matrix.Norms.Elementwise in
  rw [mem_ball_zero_iff, Matrix.norm_lt_iff hδ]
  intro i j
  refine lt_of_le_of_lt ?_ hZ
  calc ‖Z i j‖ ≤ ∑ j, ‖Z i j‖ :=
        Finset.single_le_sum (f := fun j => ‖Z i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, ‖Z i j‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem exp_mul_exp_neg (X : Matrix n n ℂ) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute X (-X) (Commute.refl X).neg_right, add_neg_cancel,
    NormedSpace.exp_zero]

theorem exp_neg_mul_exp (X : Matrix n n ℂ) : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  simpa using exp_mul_exp_neg (-X)

theorem exp_conj_invol {J : Matrix n n ℂ} (hJ : J * J = 1) (X : Matrix n n ℂ) :
    NormedSpace.exp (J * X * J) = J * NormedSpace.exp X * J :=
  Matrix.exp_units_conj (⟨J, J, hJ, hJ⟩ : (Matrix n n ℂ)ˣ) X

theorem exp_unitary {J : Matrix n n ℂ} (hJ : J * J = 1) {X : Matrix n n ℂ}
    (hX : Xᴴ * J + J * X = 0) : (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J := by
  have h1 : Xᴴ = J * (-X) * J := by
    have : Xᴴ * J = J * (-X) := by rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hX
    rw [← this, Matrix.mul_assoc, hJ, Matrix.mul_one]
  rw [← Matrix.exp_conjTranspose, h1, exp_conj_invol hJ, Matrix.mul_assoc _ J J, hJ,
    Matrix.mul_one, Matrix.mul_assoc, exp_neg_mul_exp, Matrix.mul_one]

theorem exp_twist {J : Matrix n n ℂ} (hJ : J * J = 1) {Z : Matrix n n ℂ}
    (hZ : (NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z = J) :
    NormedSpace.exp (J * (-Z)ᴴ * J) = NormedSpace.exp Z := by
  rw [exp_conj_invol hJ, Matrix.exp_conjTranspose]
  have h1 : (NormedSpace.exp (-Z))ᴴ * (NormedSpace.exp Z)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, exp_mul_exp_neg, Matrix.conjTranspose_one]
  have h2 : (NormedSpace.exp (-Z))ᴴ * J = J * NormedSpace.exp Z := by
    calc (NormedSpace.exp (-Z))ᴴ * J
        = (NormedSpace.exp (-Z))ᴴ * ((NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z) := by rw [hZ]
      _ = J * NormedSpace.exp Z := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

end General

theorem jpq_sq (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem mat_unitary {P Q : ℕ} (g : UpqT P Q) :
    (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q := g.2

theorem continuous_mat {P Q : ℕ} : Continuous (UpqT.mat : UpqT P Q → _) :=
  Units.continuous_val.comp continuous_subtype_val

def expU (P Q : ℕ) (X : lieU P Q) : UpqT P Q :=
  (⟨⟨NormedSpace.exp X.1, NormedSpace.exp (-X.1), exp_mul_exp_neg _, exp_neg_mul_exp _⟩,
    exp_unitary (jpq_sq P Q) X.2⟩ : Formalism.UG.Upq P Q)

theorem continuous_expU (P Q : ℕ) : Continuous (expU P Q) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_matExp.comp continuous_subtype_val
  · exact continuous_matExp.comp continuous_subtype_val.neg

end GlobalTheory.UpqExpChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBoundedConvergentPowerSeriesMatrixETwoPi
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open Filter Topology

theorem tendsto_tsum_coeff_mul_pow_zero (a : ℕ → ℂ) (q₀ : ℂ) (hq₀ : q₀ ≠ 0)
    (hs : Summable (fun m : ℕ => a m * q₀ ^ m)) :
    Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0) (𝓝 (a 0)) := by
  have hlim : Tendsto (fun q : ℂ => ∑' m : ℕ, a m * q ^ m) (𝓝 0)
      (𝓝 (∑' m : ℕ, if m = 0 then a 0 else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun m => ‖a m * q₀ ^ m‖) hs.norm ?_ ?_
    · intro m
      have hc : Continuous (fun q : ℂ => a m * q ^ m) := by fun_prop
      have h := hc.tendsto 0
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa using h
      · have h0 : a m * (0 : ℂ) ^ m = 0 := by simp [hm.ne']
        rw [h0] at h
        simpa [hm.ne'] using h
    · have hpos : 0 < ‖q₀‖ := norm_pos_iff.mpr hq₀
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hpos] with q hq m
      have hq' : ‖q‖ ≤ ‖q₀‖ := by
        have : ‖q‖ < ‖q₀‖ := by simpa using hq
        exact this.le
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
      gcongr
  simpa using hlim

theorem det_bounded_eTwoPi : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ),
    IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) →
    ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im →
      C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧
      ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by
  intro g A w₀ hdet hsum
  have hq₀ : eTwoPi w₀ ≠ 0 := Complex.exp_ne_zero _
  set d₀ : ℂ := (A.map (PowerSeries.constantCoeff (R := ℂ))).det with hd₀
  have hd₀eq : d₀ = PowerSeries.constantCoeff (R := ℂ) A.det := by
    rw [RingHom.map_det]
    rfl
  have hd₀ne : d₀ ≠ 0 := by
    rw [hd₀eq]
    exact (hdet.map (PowerSeries.constantCoeff (R := ℂ))).ne_zero
  have hmat : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ)) (𝓝 0) (𝓝 (A.map (PowerSeries.constantCoeff (R := ℂ)))) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    have h := tendsto_tsum_coeff_mul_pow_zero (fun m => PowerSeries.coeff m (A i j))
      (eTwoPi w₀) hq₀ (hsum i j)
    simpa using h
  have hdetlim : Tendsto
      (fun q : ℂ => (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * q ^ m :
        Matrix (Fin g) (Fin g) ℂ).det) (𝓝 0) (𝓝 d₀) :=
    ((continuous_id.matrix_det).tendsto _).comp hmat
  have hdpos : 0 < ‖d₀‖ := norm_pos_iff.mpr hd₀ne
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hdetlim (‖d₀‖ / 2) (by positivity))
  refine ⟨-Real.log ε / (2 * Real.pi), 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1, by positivity, ?_⟩
  intro w hw
  have hpi : 0 < 2 * Real.pi := by positivity
  have hnorm : ‖eTwoPi w‖ < ε := by
    have hn : ‖eTwoPi w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
      rw [eTwoPi, Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    rw [hn, ← Real.lt_log_iff_exp_lt hε]
    rw [div_lt_iff₀ hpi] at hw
    linarith
  have hclose := hball (y := eTwoPi w) (by simpa using hnorm)
  rw [dist_eq_norm] at hclose
  set D : ℂ := (Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m :
    Matrix (Fin g) (Fin g) ℂ).det with hD
  have hlow : ‖d₀‖ / 2 ≤ ‖D‖ := by
    have := norm_sub_norm_le d₀ D
    rw [norm_sub_rev] at this
    linarith
  have hup : ‖D‖ ≤ 3 * ‖d₀‖ / 2 := by
    have := norm_sub_norm_le D d₀
    linarith
  have h2 : 0 < 2 / ‖d₀‖ := by positivity
  constructor
  · refine le_trans ?_ hlow
    have hC : 2 / ‖d₀‖ ≤ 2 / ‖d₀‖ + 3 * ‖d₀‖ / 2 + 1 := by
      have : 0 ≤ 3 * ‖d₀‖ / 2 := by positivity
      linarith
    have := inv_anti₀ h2 hC
    rwa [inv_div] at this
  · have : 0 < 2 / ‖d₀‖ := h2
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadicStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic : ∀ (l : ℕ) [Fact l.Prime], ∃ (ζ : ℕ → Om l) (ε : Per.Fl l), ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 ∧ ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m) := by
  first | exact @GlobalTheory.MemLoc.exists_zeta_eps | exact GlobalTheory.MemLoc.exists_zeta_eps | (intros; apply GlobalTheory.MemLoc.exists_zeta_eps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDensityOriginOfAlmostHomogeneous
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory

section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
theorem _root_.GlobalTheory.densHom_scale (l : Measure V) [l.IsAddHaarMeasure] (x : V) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) :
    l (Metric.closedBall x (s * r)) =
      ENNReal.ofReal (s ^ Module.finrank ℝ V) * l (Metric.ball 0 r) := by
  rw [Measure.addHaar_closedBall_mul_of_pos l x hs r, Measure.addHaar_closedBall l 0 hr.le,
    Measure.addHaar_ball_of_pos l 0 hr]

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
theorem _root_.GlobalTheory.densHom_tendsto_mul {s : ℝ} (hs : 0 < s) :
    Tendsto (fun r : ℝ => s * r) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have h : Tendsto (fun r : ℝ => s * r) (𝓝 0) (𝓝 (s * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr using mul_pos hs hr

end

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem closedBall_smul_div_ball_eq_ofReal_pow_mul (l ν : Measure V) [l.IsAddHaarMeasure] (x : V)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ν (Metric.closedBall x (s * r)) / l (Metric.ball 0 r) =
      ENNReal.ofReal (s ^ Module.finrank ℝ V) *
        (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r))) := by
  rw [_root_.GlobalTheory.densHom_scale l x hs hr, ← mul_div_assoc,
    ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 (pow_pos hs _)).ne' ENNReal.ofReal_ne_top]

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem ofReal_pow_mul_le_liminf_ball_ratio (l ν : Measure V) [l.IsAddHaarMeasure] {x : V} {s : ℝ}
    (hs : 0 < s) {D : ENNReal}
    (hD : Tendsto (fun r => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 D))
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Metric.closedBall x (s * r)) ≤ ν (Metric.ball 0 r)) :
    ENNReal.ofReal (s ^ Module.finrank ℝ V) * D ≤
      liminf (fun r => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) := by
  have htend : Tendsto (fun r => ENNReal.ofReal (s ^ Module.finrank ℝ V) *
      (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (s ^ Module.finrank ℝ V) * D)) :=
    ENNReal.Tendsto.const_mul (hD.comp (_root_.GlobalTheory.densHom_tendsto_mul hs))
      (Or.inr ENNReal.ofReal_ne_top)
  refine (le_of_eq htend.liminf_eq.symm).trans (Filter.liminf_le_liminf ?_)
  filter_upwards [h, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [← closedBall_smul_div_ball_eq_ofReal_pow_mul l ν x hs hr0]
  exact ENNReal.div_le_div_right hr _

open MeasureTheory Filter Topology Matrix in
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
private theorem limsup_ball_ratio_le_ofReal_pow_mul (l ν : Measure V) [l.IsAddHaarMeasure] {x : V} {s : ℝ}
    (hs : 0 < s) {D : ENNReal}
    (hD : Tendsto (fun r => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0) (𝓝 D))
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), ν (Metric.ball 0 r) ≤ ν (Metric.closedBall x (s * r))) :
    limsup (fun r => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) ≤
      ENNReal.ofReal (s ^ Module.finrank ℝ V) * D := by
  have htend : Tendsto (fun r => ENNReal.ofReal (s ^ Module.finrank ℝ V) *
      (ν (Metric.closedBall x (s * r)) / l (Metric.closedBall x (s * r)))) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (s ^ Module.finrank ℝ V) * D)) :=
    ENNReal.Tendsto.const_mul (hD.comp (_root_.GlobalTheory.densHom_tendsto_mul hs))
      (Or.inr ENNReal.ofReal_ne_top)
  refine (Filter.limsup_le_limsup ?_).trans (le_of_eq htend.limsup_eq)
  filter_upwards [h, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
  rw [← closedBall_smul_div_ball_eq_ofReal_pow_mul l ν x hs hr0]
  exact ENNReal.div_le_div_right hr _

open MeasureTheory Filter Topology Matrix in

theorem _root_.GlobalTheory.exists_density_origin_of_almost_homogeneous : ∀ (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V)
    [l.IsAddHaarMeasure] [IsLocallyFiniteMeasure ν], (∀ r : ℝ, 0 < r → ν (Metric.ball 0 r) ≠ 0) →
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ : ℝ, 0 < δ ∧ ∀ x : V, ‖x‖ < δ →
      ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧
        ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) →
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) := by
  intro V _ _ _ _ _ l ν _ _ hpos halmost
  set ρ := fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r) with hρ
  have key : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∃ D : ENNReal, D < ⊤ ∧
      ENNReal.ofReal ((1 - 2 * ε) ^ Module.finrank ℝ V) * D ≤ liminf ρ (𝓝[>] 0) ∧
      limsup ρ (𝓝[>] 0) ≤ ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V) * D := by
    intro ε hε hε2
    obtain ⟨δ, hδ, hx⟩ := halmost ε hε (by linarith)
    obtain ⟨x, hxmem, hxD, hxfin⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (Metric.measure_ball_pos l (0 : V) hδ).ne'
      (ae_restrict_of_ae ((Besicovitch.ae_tendsto_rnDeriv ν l).and (Measure.rnDeriv_lt_top ν l)))
    have hxr := hx x (mem_ball_zero_iff.1 hxmem)
    refine ⟨_, hxfin, ofReal_pow_mul_le_liminf_ball_ratio l ν (by linarith) hxD ?_,
      limsup_ball_ratio_le_ofReal_pow_mul l ν (by linarith) hxD ?_⟩
    · filter_upwards [hxr, self_mem_nhdsWithin] with r hr (hr0 : 0 < r)
      exact (measure_mono (Metric.closedBall_subset_ball (by nlinarith))).trans hr.1
    · filter_upwards [hxr] with r hr
      exact hr.2.trans (measure_mono Metric.ball_subset_closedBall)
  have hML : liminf ρ (𝓝[>] 0) ≤ limsup ρ (𝓝[>] 0) := liminf_le_limsup
  have hLtop : limsup ρ (𝓝[>] 0) < ⊤ := by
    obtain ⟨D, hD, -, hup⟩ := key (1 / 4) (by norm_num) (by norm_num)
    exact hup.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD)
  have hLM : limsup ρ (𝓝[>] 0) ≤ liminf ρ (𝓝[>] 0) := by
    have hK : Tendsto (fun ε : ℝ => ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V))
        (𝓝 0) (𝓝 1) := by
      have hc : ContinuousAt (fun ε : ℝ =>
          ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V)) 0 :=
        ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
      simpa using hc.tendsto
    have hT : Tendsto (fun ε : ℝ => ENNReal.ofReal
        ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V) * liminf ρ (𝓝[>] 0))
        (𝓝[>] 0) (𝓝 (liminf ρ (𝓝[>] 0))) := by
      have h1 := ENNReal.Tendsto.mul_const (b := liminf ρ (𝓝[>] 0)) (ENNReal.tendsto_ofReal hK)
        (Or.inr (hML.trans_lt hLtop).ne)
      simpa using h1.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hT ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    obtain ⟨D, -, hlow, hup⟩ := key ε hε.1 hε.2
    have hb : 0 < (1 - 2 * ε) ^ Module.finrank ℝ V := pow_pos (by linarith [hε.2]) _
    refine hup.trans ?_
    calc ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V) * D
        = ENNReal.ofReal ((1 + ε) ^ Module.finrank ℝ V / (1 - 2 * ε) ^ Module.finrank ℝ V) *
          (ENNReal.ofReal ((1 - 2 * ε) ^ Module.finrank ℝ V) * D) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (by linarith [hε.1]) _) hb.le),
            div_mul_cancel₀ _ hb.ne']
      _ ≤ _ := by gcongr
  have htend : Tendsto ρ (𝓝[>] 0) (𝓝 (limsup ρ (𝓝[>] 0))) :=
    tendsto_of_liminf_eq_limsup (le_antisymm hML hLM) rfl
  refine ⟨limsup ρ (𝓝[>] 0), ?_, hLtop.ne, htend⟩
  intro hL0
  rw [hL0] at htend
  obtain ⟨δ, hδ, hx⟩ := halmost (1 / 2) (by norm_num) (by norm_num)
  have hs_le : ∀ t : NNReal, 0 < t → ν (Metric.ball 0 δ) ≤ t * l (Metric.ball 0 δ) := by
    intro t ht
    have hle := VitaliFamily.measure_le_of_frequently_le (Besicovitch.vitaliFamily ν) (t • l)
      (Measure.AbsolutelyContinuous.refl ν) (Metric.ball (0 : V) δ) ?_
    · rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hle
      exact hle
    intro x hxs
    apply ((Besicovitch.tendsto_filterAt ν x).comp
      (_root_.GlobalTheory.densHom_tendsto_mul (show (0 : ℝ) < 1 / 4 by norm_num))).frequently
    refine Filter.Eventually.frequently ?_
    have hpos' : (0 : ENNReal) < t * ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ V) :=
      ENNReal.mul_pos (by exact_mod_cast ht.ne') (ENNReal.ofReal_pos.2 (by positivity)).ne'
    filter_upwards [(tendsto_order.1 htend).2 _ hpos', hx x (mem_ball_zero_iff.1 hxs),
      self_mem_nhdsWithin] with r hr hxr (hr0 : 0 < r)
    show ν (Metric.closedBall x (1 / 4 * r)) ≤ (t • l) (Metric.closedBall x (1 / 4 * r))
    have hlt : ν (Metric.ball 0 r) <
        t * ENNReal.ofReal ((1 / 4) ^ Module.finrank ℝ V) * l (Metric.ball 0 r) :=
      (ENNReal.div_lt_iff (Or.inl (Metric.measure_ball_pos l 0 hr0).ne')
        (Or.inl measure_ball_lt_top.ne)).1 hr
    rw [mul_assoc, ← _root_.GlobalTheory.densHom_scale l x (by norm_num) hr0] at hlt
    have hsub : Metric.closedBall x (1 / 4 * r) ⊆ Metric.ball x ((1 - 1 / 2) * r) :=
      Metric.closedBall_subset_ball (by linarith)
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ((measure_mono hsub).trans hxr.1).trans hlt.le
  have hzero : ν (Metric.ball 0 δ) = 0 := by
    have hT : Tendsto (fun t : NNReal => (t : ENNReal) * l (Metric.ball 0 δ)) (𝓝[>] 0) (𝓝 0) := by
      have h1 := ENNReal.Tendsto.mul_const (b := l (Metric.ball 0 δ))
        (ENNReal.tendsto_coe.2 (tendsto_id (x := 𝓝 (0 : NNReal)))) (Or.inr measure_ball_lt_top.ne)
      simpa using h1.mono_left nhdsWithin_le_nhds
    exact le_antisymm (ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun t ht => hs_le t ht))
      bot_le
  exact hpos δ hδ hzero

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBdRPlusSectionOfThetaStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isBdRPlusSectionOfTheta : ∀ (l : ℕ) [Fact l.Prime], ∃ o : Om l →+* Per.BdRp l, IsSec o := by
  first | exact @GlobalTheory.MemLoc.SecEx.exists_isSec | exact GlobalTheory.MemLoc.SecEx.exists_isSec | (intros; apply GlobalTheory.MemLoc.SecEx.exists_isSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeGramEqSgn
section
open NumberField

namespace GlobalTheory.HermSignature

theorem exists_le_gram_eq_sgn : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E), (∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a) → G.det ≠ 0 → ∀ τ : E →+* ℂ, ∃ p : ℕ, p ≤ r ∧ ∃ P : Matrix (Fin r) (Fin r) ℂ, P.det ≠ 0 ∧ ReciprocityTheory.ChartRestriction.G.FD.gram τ G P = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  intro E _ _ _ r G hG hd τ
  obtain ⟨p, Q, hQ, h⟩ := GlobalTheory.Published.LandherrSt.exists_gram_eq_sgn hG hd τ
  refine ⟨min p r, min_le_right _ _, Q, hQ, ?_⟩
  rw [h]
  congr 1
  funext a
  have ha := a.2
  simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, lt_min_iff, ha, and_true]

end GlobalTheory.HermSignature
end

