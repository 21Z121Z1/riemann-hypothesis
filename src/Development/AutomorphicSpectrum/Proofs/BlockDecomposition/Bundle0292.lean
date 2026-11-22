import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyRestrictionBetweenStableFamilies
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.ZariskiCocycleRefinement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0283
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0284
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnisotropicQuaternionNormOneCompact
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem isCompact_level_one_of_anisotropic {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    (q : K × K × K × K → K) (hq : Continuous q)
    (hh : ∀ (c : K) (v : K × K × K × K), q (c • v) = c ^ 2 * q v)
    (h0 : ∀ v, q v = 0 → v = 0) : IsCompact {v | q v = 1} := by
  obtain ⟨c, hc⟩ := NormedField.exists_one_lt_norm K
  have hcpos : 0 < ‖c‖ := lt_trans zero_lt_one hc
  have hq0 : q 0 = 0 := by
    have := hh 0 0
    simpa using this
  set S : Set (K × K × K × K) := {v | ‖c‖⁻¹ ≤ ‖v‖ ∧ ‖v‖ ≤ 1} with hS
  have hScl : IsClosed S :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have hSc : IsCompact S := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : K × K × K × K) 1) hScl ?_
    intro v hv
    simpa [mem_closedBall_zero_iff] using hv.2
  have hpos : ∀ v ∈ S, (0 : ℝ) < ‖q v‖ := by
    intro v hv
    rw [norm_pos_iff]
    intro hv0
    have h1 := h0 v hv0
    have h2 := hv.1
    rw [h1, norm_zero] at h2
    exact absurd h2 (not_le.2 (inv_pos.2 hcpos))
  obtain ⟨m, hm, hmS⟩ := hSc.exists_forall_le' (hq.norm.continuousOn) hpos
  have hbound : {v | q v = 1} ⊆ Metric.closedBall (0 : K × K × K × K) (1 + m⁻¹) := by
    intro v hv
    have hv1 : q v = 1 := hv
    have hvne : v ≠ 0 := by
      rintro rfl
      rw [hq0] at hv1
      exact zero_ne_one hv1
    obtain ⟨a, ha, hlt, hge, -⟩ := rescale_to_shell hc one_pos hvne
    have hmem : a • v ∈ S := ⟨by simpa [one_div] using hge, hlt.le⟩
    have h1 := hmS _ hmem
    rw [hh, hv1, mul_one, norm_pow] at h1
    rw [norm_smul] at hlt
    rw [mem_closedBall_zero_iff]
    by_contra hcon
    have hcon' : 1 + m⁻¹ < ‖v‖ := not_le.1 hcon
    have hminv : 0 < m⁻¹ := inv_pos.2 hm
    have ht1 : 1 < ‖v‖ := by linarith
    have hapos : 0 ≤ ‖a‖ := norm_nonneg a
    have h3 : (‖a‖ * ‖v‖) ^ 2 < 1 := by
      have : 0 ≤ ‖a‖ * ‖v‖ := by positivity
      nlinarith
    have h4 : m * ‖v‖ ^ 2 ≤ (‖a‖ * ‖v‖) ^ 2 := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have h5 : m * ‖v‖ < 1 := by
      have : m * ‖v‖ < m * ‖v‖ ^ 2 := by
        apply mul_lt_mul_of_pos_left _ hm
        nlinarith
      linarith
    have h6 : m * (1 + m⁻¹) < m * ‖v‖ := mul_lt_mul_of_pos_left hcon' hm
    have h7 : m * (1 + m⁻¹) = m + 1 := by
      field_simp
    linarith
  exact IsCompact.of_isClosed_subset (isCompact_closedBall _ _)
    (isClosed_eq hq continuous_const) hbound

theorem isCompact_qn_eq_one_of_normed {F : Type} [Field F] (d β : F)
    {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K]
    (h : ∀ x : Q d β K, qn x = 0 → x = 0) : IsCompact {x : Q d β K | qn x = 1} := by
  set D := algebraMap F K d
  set B := algebraMap F K β
  let q : K × K × K × K → K := fun v =>
    v.1 ^ 2 - D * v.2.1 ^ 2 - B * v.2.2.1 ^ 2 + D * B * v.2.2.2 ^ 2
  have hq : Continuous q := by fun_prop
  have hh : ∀ (c : K) (v : K × K × K × K), q (c • v) = c ^ 2 * q v := by
    intro c v
    simp only [q, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have h0 : ∀ v, q v = 0 → v = 0 := by
    rintro ⟨a, b, e, f⟩ hv
    have := h (⟨a, b, e, f⟩ : Q d β K) hv
    have h1 := congrArg QuaternionAlgebra.re this
    have h2 := congrArg QuaternionAlgebra.imI this
    have h3 := congrArg QuaternionAlgebra.imJ this
    have h4 := congrArg QuaternionAlgebra.imK this
    simp at h1 h2 h3 h4
    simp [h1, h2, h3, h4]
  have hc := isCompact_level_one_of_anisotropic q hq hh h0
  exact (qHomeo (d := d) (β := β) (R := K)).isCompact_preimage.2 hc

theorem isCompact_qn_eq_one_at_place {F : Type} [Field F] [NumberField F] (d β : F) (s : Pl F)
    (h : ∀ x : Q d β (Kp s), qn x = 0 → x = 0) : IsCompact {x : Q d β (Kp s) | qn x = 1} := by
  cases s with
  | inl w =>
    letI : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := ⟨2, by
          rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
            map_ofNat]
          simp⟩ }
    haveI : ProperSpace w.Completion :=
      ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace w.Completion
    exact isCompact_qn_eq_one_of_normed (K := w.Completion) d β h
  | inr v =>
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    haveI : ProperSpace (v.adicCompletion F) := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
    exact isCompact_qn_eq_one_of_normed (K := v.adicCompletion F) d β h

end GlobalTheory.CompanionTheory.PlaneSA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundOfNatDegree
section
open Polynomial

namespace GlobalTheory.CompanionTheory.LinRec

noncomputable def shift : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun u := fun i => u (i + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma shift_apply (u : ℕ → ℂ) (i : ℕ) : shift u i = u (i + 1) := rfl

lemma shift_pow (j : ℕ) (u : ℕ → ℂ) (i : ℕ) : (shift ^ j) u i = u (i + j) := by
  induction j generalizing u with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, shift_apply]
    rfl

lemma aeval_shift (p : ℂ[X]) (u : ℕ → ℂ) (i : ℕ) :
    aeval shift p u i = ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * u (i + j) := by
  rw [aeval_eq_sum_range, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, shift_pow, smul_eq_mul]

lemma aeval_diff (q : ℂ[X]) (z : ℂ) (u : ℕ → ℂ) (hu : aeval shift ((X - C z) * q) u = 0) :
    aeval shift q (fun i => u (i + 1) - z * u i) = 0 := by
  have h : aeval shift (X - C z : ℂ[X]) u = fun i => u (i + 1) - z * u i := by
    funext i
    simp [aeval_X, aeval_C, shift_apply, Module.algebraMap_end_apply]
  rw [← h, ← Module.End.mul_apply, ← map_mul, mul_comm]
  exact hu

lemma geom_step (z : ℂ) (κ c M : ℝ) (hz : ‖z‖ < Real.exp κ) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (u : ℕ → ℂ) (h0 : ‖u 0‖ ≤ M)
    (hv : ∀ i : ℕ, ‖u (i + 1) - z * u i‖ ≤ c * Real.exp (κ * i) * M) (i : ℕ) :
    ‖u i‖ ≤ (1 + c / (Real.exp κ - ‖z‖)) * Real.exp (κ * i) * M := by
  have hpos : 0 < Real.exp κ - ‖z‖ := sub_pos.2 hz
  set D : ℝ := 1 + c / (Real.exp κ - ‖z‖) with hDdef
  have hD1 : 1 ≤ D := by
    have : 0 ≤ c / (Real.exp κ - ‖z‖) := div_nonneg hc hpos.le
    linarith
  have hD : ‖z‖ * D + c ≤ D * Real.exp κ := by
    have : D * (Real.exp κ - ‖z‖) = (Real.exp κ - ‖z‖) + c := by
      rw [hDdef]; field_simp
    nlinarith
  induction i with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    nlinarith
  | succ i ih =>
    have hE : 0 < Real.exp (κ * i) := Real.exp_pos _
    have h1 : ‖u (i + 1)‖ ≤ ‖z‖ * ‖u i‖ + ‖u (i + 1) - z * u i‖ := by
      have : u (i + 1) = z * u i + (u (i + 1) - z * u i) := by ring
      calc ‖u (i + 1)‖ = ‖z * u i + (u (i + 1) - z * u i)‖ := by rw [← this]
        _ ≤ ‖z * u i‖ + ‖u (i + 1) - z * u i‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul]
    have hexp : Real.exp (κ * ((i + 1 : ℕ) : ℝ)) = Real.exp (κ * i) * Real.exp κ := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    rw [hexp]
    have hEM : 0 ≤ Real.exp (κ * i) * M := by positivity
    calc ‖u (i + 1)‖ ≤ ‖z‖ * (D * Real.exp (κ * i) * M) + c * Real.exp (κ * i) * M :=
          h1.trans (add_le_add (mul_le_mul_of_nonneg_left ih (norm_nonneg _)) (hv i))
      _ = (‖z‖ * D + c) * (Real.exp (κ * i) * M) := by ring
      _ ≤ (D * Real.exp κ) * (Real.exp (κ * i) * M) := mul_le_mul_of_nonneg_right hD hEM
      _ = _ := by ring

theorem bound_of_natDegree (n : ℕ) : ∀ (p : ℂ[X]) (κ : ℝ), p.Monic → p.natDegree = n →
    (∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℕ → ℂ) (M : ℝ), aeval shift p u = 0 →
      (∀ j < n, ‖u j‖ ≤ M) → 0 ≤ M → ∀ i : ℕ, ‖u i‖ ≤ C * Real.exp (κ * i) * M := by
  induction n with
  | zero =>
    intro p κ hp hd _
    refine ⟨0, le_rfl, fun u M hu _ _ i => ?_⟩
    have hp1 : p = 1 := by
      have h1 : p.coeff 0 = 1 := by
        have h2 := hp.coeff_natDegree
        rwa [hd] at h2
      rw [eq_C_of_natDegree_eq_zero hd, h1, C_1]
    subst hp1
    have hu0 : u = 0 := by simpa using hu
    simp [hu0]
  | succ n ih =>
    intro p κ hp hd hr
    obtain ⟨z, hz⟩ : ∃ z, p.IsRoot z := IsAlgClosed.exists_root p (by
      intro h0
      have : p.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h0.le
      omega)
    have hzlt := hr z hz
    obtain ⟨q, rfl⟩ := dvd_iff_isRoot.2 hz
    have hq : q.Monic := (monic_X_sub_C z).of_mul_monic_left hp
    have hqd : q.natDegree = n := by
      rw [(monic_X_sub_C z).natDegree_mul hq, natDegree_X_sub_C] at hd
      omega
    obtain ⟨C', hC', hB⟩ := ih q κ hq hqd fun w hw => hr w (by
      have hw' : eval w q = 0 := hw
      simp [IsRoot, hw'])
    have hpos : 0 < Real.exp κ - ‖z‖ := sub_pos.2 hzlt
    have hc : 0 ≤ C' * (1 + ‖z‖) := by positivity
    refine ⟨1 + C' * (1 + ‖z‖) / (Real.exp κ - ‖z‖), by positivity, fun u M hu hM hM0 i => ?_⟩
    refine geom_step z κ _ M hzlt hc hM0 u (hM 0 (Nat.succ_pos n)) (fun i => ?_) i
    have hb := hB (fun i => u (i + 1) - z * u i) ((1 + ‖z‖) * M) (aeval_diff q z u hu)
      (fun j hj => ?_) (by positivity) i
    · calc ‖u (i + 1) - z * u i‖ ≤ C' * Real.exp (κ * i) * ((1 + ‖z‖) * M) := hb
        _ = _ := by ring
    · calc ‖u (j + 1) - z * u j‖ ≤ ‖u (j + 1)‖ + ‖z * u j‖ := norm_sub_le _ _
        _ = ‖u (j + 1)‖ + ‖z‖ * ‖u j‖ := by rw [norm_mul]
        _ ≤ M + ‖z‖ * M := add_le_add (hM _ (by omega))
            (mul_le_mul_of_nonneg_left (hM _ (by omega)) (norm_nonneg _))
        _ = _ := by ring

theorem recBound : PositivityTheory.Rg.Rs.An.RecBound := by
  intro p κ hp hr
  obtain ⟨C, hC, h⟩ := bound_of_natDegree _ p κ hp rfl hr
  refine ⟨C, hC, fun u M hu hM hM0 i => h u M ?_ hM hM0 i⟩
  funext i
  rw [aeval_shift]
  exact hu i

end GlobalTheory.CompanionTheory.LinRec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartVanishingKillsFormMulPow
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace resG)
open GlobalTheory.ProjSpace (chart formOn ratioOn ratio)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GE

theorem app_presheaf_map {A B : Scheme.{0}} (φ : B ⟶ A) {U V : A.Opens} (h : V ≤ U)
    (h' : φ ⁻¹ᵁ V ≤ φ ⁻¹ᵁ U) (a : Γ(A, U)) :
    (φ.app V).hom ((A.presheaf.map (homOfLE h).op).hom a) =
      (B.presheaf.map (homOfLE h').op).hom ((φ.app U).hom a) := by
  have e := congrArg (fun g => CommRingCat.Hom.hom g a) (φ.naturality (homOfLE h).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

variable {R : Type} [CommRing R] {N : ℕ}

private theorem formOn_congr {U : (PSpace R N).Opens} {i : Fin (N + 1)} {hi : U ≤ chart R N i} {n : ℕ}
    {f g : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) (hg : g.IsHomogeneous n) (h : f = g) :
    formOn U i hi n f hf = formOn U i hi n g hg := by
  subst h
  rfl

theorem formOn_X_pow (U : (PSpace R N).Opens) (i : Fin (N + 1)) (hi : U ≤ chart R N i)
    (j : Fin (N + 1)) (m : ℕ) :
    formOn U i hi m (X j ^ m) (isHomogeneous_X_pow j m) = ratioOn U i hi j ^ m := by
  induction m with
  | zero =>
    rw [formOn_congr _ (isHomogeneous_C _ (1 : R)) (by simp), GlobalTheory.ProjSpace.formOn_C, map_one, pow_zero]
  | succ m ih =>
    rw [formOn_congr _ ((isHomogeneous_X_pow j m).mul (isHomogeneous_X R j)) (pow_succ _ _),
      GlobalTheory.ProjSpace.formOn_mul (isHomogeneous_X_pow j m) (isHomogeneous_X R j), ih, GlobalTheory.ProjSpace.formOn_X, pow_succ]

theorem exists_ratio_pow_mul_eq_zero {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ] (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) (k : Fin (N + 1))
    (h0 : (φ.app (chart R N k)).hom (formOn (chart R N k) k le_rfl n f hf) = 0)
    (j : Fin (N + 1)) :
    ∃ m : ℕ, (φ.app (chart R N j)).hom (ratio R N j k) ^ m *
      (φ.app (chart R N j)).hom (formOn (chart R N j) j le_rfl n f hf) = 0 := by
  have hW : φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) ≤ φ ⁻¹ᵁ chart R N j :=
    (TopologicalSpace.Opens.map φ.base).monotone inf_le_left
  have hW' : φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) ≤ φ ⁻¹ᵁ chart R N k :=
    (TopologicalSpace.Opens.map φ.base).monotone inf_le_right
  have e1 := GlobalTheory.ProjSpace.resG_formOn (U := chart R N j) (i := j) (hi := le_rfl)
    (inf_le_left : chart R N j ⊓ chart R N k ≤ chart R N j) hf
  have e2 := GlobalTheory.ProjSpace.resG_formOn (U := chart R N k) (i := k) (hi := le_rfl)
    (inf_le_right : chart R N j ⊓ chart R N k ≤ chart R N k) hf
  have e3 := GlobalTheory.ProjSpace.formOn_eq_ratioOn_pow_mul (U := chart R N j ⊓ chart R N k) (i := j)
    (hi := inf_le_left) (j := k) inf_le_right hf
  have key : (Y.presheaf.map (homOfLE hW).op).hom
      ((φ.app (chart R N j)).hom (formOn (chart R N j) j le_rfl n f hf)) = 0 := by
    rw [← app_presheaf_map φ inf_le_left hW]
    erw [e1]
    rw [e3, ← e2, map_mul]
    erw [app_presheaf_map φ inf_le_right hW']
    rw [h0, map_zero, mul_zero]
  have hle : Y.basicOpen ((φ.app (chart R N j)).hom (ratio R N j k)) ≤ φ ⁻¹ᵁ (chart R N j ⊓ chart R N k) := by
    rw [← Scheme.preimage_basicOpen, GlobalTheory.ProjSpace.basicOpen_ratioOn]
  refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Y (U := φ ⁻¹ᵁ chart R N j)
    (φ.isCompact_preimage (GlobalTheory.ProjSpace.isAffineOpen_chart R N j).isCompact) _ _ ?_
  show (Y.presheaf.map (homOfLE _).op).hom _ = 0
  rw [show (homOfLE (Y.basicOpen_le _) : Y.basicOpen ((φ.app (chart R N j)).hom (ratio R N j k)) ⟶ φ ⁻¹ᵁ chart R N j) =
      homOfLE hle ≫ homOfLE hW from rfl, op_comp, Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, key,
    map_zero]

theorem exists_killsForm_X_pow_mul :
    ∀ {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) [QuasiCompact φ] (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n) (k : Fin (N + 1)),
    (φ.app (GlobalTheory.ProjSpace.chart R N k)).hom
      (GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf) = 0 →
    ∃ (m : ℕ) (h : (X k ^ m * f : MvPolynomial (Fin (N + 1)) R).IsHomogeneous (m + n)),
      KillsForm φ (m + n) (X k ^ m * f) h := by
  intro R _ N Y φ _ n f hf k h0
  choose m hm using fun j => exists_ratio_pow_mul_eq_zero φ n f hf k h0 j
  refine ⟨∑ j, m j, (isHomogeneous_X_pow k _).mul hf, ?_⟩
  intro j
  rw [GlobalTheory.ProjSpace.formOn_mul (isHomogeneous_X_pow k _) hf, formOn_X_pow, map_mul, map_pow]
  have hle : m j ≤ ∑ j, m j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, hm j, mul_zero]

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedImmersionPullbackKernelSup
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE

theorem ker_inter_eq_sup {X Y A B Z : Scheme.{0}} (t : Y ⟶ X) (a : A ⟶ Y) (b : B ⟶ Y) (f : Z ⟶ A)
    (g : Z ⟶ B) [IsClosedImmersion t] [IsClosedImmersion a] [IsClosedImmersion b]
    (h : IsPullback f g a b) :
    Scheme.Hom.ker ((f ≫ a) ≫ t) = Scheme.Hom.ker (a ≫ t) ⊔ Scheme.Hom.ker (b ≫ t) := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · set K := Scheme.Hom.ker (a ≫ t) ⊔ Scheme.Hom.ker (b ≫ t) with hK
    have hA : Scheme.Hom.ker (a ≫ t) ≤ K.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_left
    have hB : Scheme.Hom.ker (b ≫ t) ≤ K.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_right
    let u : K.subscheme ⟶ A := IsClosedImmersion.lift (a ≫ t) K.subschemeι hA
    let v : K.subscheme ⟶ B := IsClosedImmersion.lift (b ≫ t) K.subschemeι hB
    have hu : u ≫ a ≫ t = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
    have hv : v ≫ b ≫ t = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
    have huv : u ≫ a = v ≫ b := by
      rw [← cancel_mono t, Category.assoc, Category.assoc, hu, hv]
    have hl : h.lift u v huv ≫ (f ≫ a) ≫ t = K.subschemeι := by
      rw [← Category.assoc, ← Category.assoc, h.lift_fst, Category.assoc]
      exact hu
    calc Scheme.Hom.ker ((f ≫ a) ≫ t) ≤ (h.lift u v huv ≫ (f ≫ a) ≫ t).ker :=
          Scheme.Hom.le_ker_comp _ _
      _ = K := by rw [hl, Scheme.IdealSheafData.ker_subschemeι]
  · rw [Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _
  · rw [h.w, Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _

end GlobalTheory.CompanionTheory.GE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClsEqOfEq
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

universe w

namespace GlobalTheory.CompanionTheory.RedPull

theorem cls_eq_of_eq {R : Type} [CommRing R] {K : Cx.{w} R} {n : ℕ} {a b : K.X n} (e : a = b)
    (ha : K.d n a = 0) (hb : K.d n b = 0) : K.cls a ha = K.cls b hb := by
  subst e
  rfl

theorem pull_square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] {F G : C ⥤ ModuleCat.{0} R} {F' G' : C' ⥤ ModuleCat.{0} R'}
    (a : CH.Mor F G (RingHom.id R)) (b : CH.Mor G G' σ) (c : CH.Mor F F' σ) (d : CH.Mor F' G' (RingHom.id R'))
    (j : ℕ) (h : ∀ x : CH.Cn F j, b.pullC j (a.pullC j x) = d.pullC j (c.pullC j x)) (z : CH.H F j) :
    b.pull j (a.pull j z) = d.pull j (c.pull j z) := by
  obtain ⟨x, hx, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) j).1 z
  have h1 := CrystallineSemistableComparison.CechClassBoundaries.cyc a.hom x hx
  have h2 := CrystallineSemistableComparison.CechClassBoundaries.cyc b.hom _ h1
  have h3 := CrystallineSemistableComparison.CechClassBoundaries.cyc c.hom x hx
  have h4 := CrystallineSemistableComparison.CechClassBoundaries.cyc d.hom _ h3
  change b.hom.mapH j (a.hom.mapH j _) = d.hom.mapH j (c.hom.mapH j _)
  rw [CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' a.hom x hx h1, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' b.hom _ h1 h2,
    CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' c.hom x hx h3, CrystallineSemistableComparison.CechClassBoundaries.mapH_cls' d.hom _ h3 h4]
  exact cls_eq_of_eq (h x) h2 h4

theorem sq_toSq {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C C' : Type 1} [Category.{0} C]
    [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R' C'} (mm : SMor Φ Φ' σ) (b : IdF Φ.A) (b' : IdF Φ'.A)
    (ha : mm.Le (IdF.top _) (IdF.top _)) (hb : mm.Le b b') (j : ℕ) (z : CH.H (CH.modF Φ.A) j) :
    (mm.sq ha hb).pull j ((toSq (IdF.top _) b fun _ => rfl).pull j z) =
      (toSq (IdF.top _) b' fun _ => rfl).pull j (mm.o.pull j z) := by
  refine pull_square _ _ _ _ j (fun x => ?_) z
  funext t
  exact Subtype.ext Ideal.quotientMap_mk

theorem nmHM_redM : ∀ {O A A' : Type} [CommRing O] [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O)}
    {σ : A →+* A'} (m : NMor γ q (κA O I) γ' q' (κA O I') σ) (l s : ℕ) (r : Option ℤ) (n j : ℕ) (z : HO (TS γ q l s {⊤}) j),
    nmHM m l s r n j (redM (TS γ q l s {⊤}) r ((l : A) ^ n) j z) = redM (TS γ' q' l s {⊤}) r ((l : A') ^ n) j (nmHO m l s j z) := by
  intro O A A' _ _ _ _ _ I I' γ γ' X X' q q' σ m l s r n j z
  exact sq_toSq (nmS m l s) _ _ (fun _ _ _ => trivial) (nm_std m l s r n) j z

end GlobalTheory.CompanionTheory.RedPull
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyRestrictionBetweenStableFamiliesStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_restriction_between_stable_families : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q₀ : ObjectProperty (Thick (nlFun γ p X q κ))) (hQ : Used Q₀)
    (𝒱 : Set X.Opens) (Q' : ObjectProperty (Thick (nlFun γ p X q κ))) (h : St Q₀ 𝒱 ≤ Q') (h' : Q' ≤ St Q₀ {sSup 𝒱})
    (hc : ∀ T T' : Thick (nlFun γ p X q κ), (T ⟶ T') → Q' T → Q₀ T' → Q' T') (j : ℕ),
    (∀ r r' : ℤ, Function.Bijective (((incl h).sq (incl_fil h r) (incl_fil h r')).pull j)) ∧
    (∀ (r r' : Option ℤ) (c c' : R), Function.Bijective (((incl h).sq (incl_std h r c) (incl_std h r' c')).pull j)) ∧
    Function.Bijective ((incl h).o.pull j) := by
  first | exact @GlobalTheory.CompanionTheory.ZarCosieve.main | exact GlobalTheory.CompanionTheory.ZarCosieve.main | (intros; apply GlobalTheory.CompanionTheory.ZarCosieve.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableSubgroupClosure
section
open MeasureTheory Filter Topology
open scoped ENNReal
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.LatCount

theorem countable_subgroupClosure {G : Type*} [Group G] (s : Set G) (hs : s.Countable) :
    ((Subgroup.closure s : Subgroup G) : Set G).Countable := by
  have ht : (s ∪ s⁻¹).Countable := hs.union (by simpa using hs.image (·⁻¹))
  haveI : Countable ↥(s ∪ s⁻¹) := ht.to_subtype
  haveI : Countable (FreeMonoid ↥(s ∪ s⁻¹)) :=
    inferInstanceAs (Countable (List ↥(s ∪ s⁻¹)))
  have h : ((Subgroup.closure s : Subgroup G) : Set G)
      = Set.range (FreeMonoid.lift ((↑) : ↥(s ∪ s⁻¹) → G)) := by
    have h1 : ((Subgroup.closure s : Subgroup G) : Set G)
        = ((Submonoid.closure (s ∪ s⁻¹) : Submonoid G) : Set G) := by
      rw [← Subgroup.closure_toSubmonoid]; rfl
    rw [h1, Submonoid.closure_eq_mrange]; rfl
  rw [h]
  exact Set.countable_range _

theorem countable_lat (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Countable (PositivityTheory.Rg.Rs.An.lat K n) := by
  haveI : Countable K := GroundTheory.Global.countable_numberField K
  haveI : Countable (Matrix (Fin n) (Fin n) K) :=
    inferInstanceAs (Countable (Fin n → Fin n → K))
  haveI : Countable (GL (Fin n) K) := Units.val_injective.countable
  have h1 : (Set.range (AdelicGLn.diagonal K n)).Countable := Set.countable_range _
  have h2 : ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
      Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)).Countable := by
    rw [Subgroup.coe_zpowers]
    exact Set.countable_range _
  have h3 := countable_subgroupClosure
    ((Set.range (AdelicGLn.diagonal K n)) ∪
      ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
      Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) (h1.union h2)
  have h4 : PositivityTheory.Rg.Rs.An.lat K n = Subgroup.closure
      ((Set.range (AdelicGLn.diagonal K n)) ∪
        ((Subgroup.zpowers (PositivityTheory.Rg.Rs.An.tor K fun _ : Fin n => (1 : ℝ)) :
        Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))) := by
    unfold PositivityTheory.Rg.Rs.An.lat
    rw [Subgroup.closure_union, Subgroup.closure_eq, ← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [h4]
  exact h3.to_subtype

end GlobalTheory.CompanionTheory.LatCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseRationalsPlusSinglePlaceAdelesStatement
section
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_rationals_plus_single_place_adeles : ∀ (F : Type) [Field F] [NumberField F] (w : NumberField.InfinitePlace F), Dense ((Set.range (algebraMap F (NumberField.AdeleRing (NumberField.RingOfIntegers F) F))) + {a : NumberField.AdeleRing (NumberField.RingOfIntegers F) F | a.2 = 0 ∧ ∀ w', w' ≠ w → a.1 w' = 0}) := by
  first | exact @GlobalTheory.CompanionTheory.AddSA.dense_add_place | exact GlobalTheory.CompanionTheory.AddSA.dense_add_place | (intros; apply GlobalTheory.CompanionTheory.AddSA.dense_add_place <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementPropertiesStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.epsilon_cyclotomic_element_properties : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) := by
  first | exact @GlobalTheory.CompanionTheory.EpsFacts.eps_facts | exact GlobalTheory.CompanionTheory.EpsFacts.eps_facts | (intros; apply GlobalTheory.CompanionTheory.EpsFacts.eps_facts <;> assumption)
end

