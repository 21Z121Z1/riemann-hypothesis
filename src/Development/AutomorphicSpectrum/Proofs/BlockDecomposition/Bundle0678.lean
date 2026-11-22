import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0664
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0629
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0041
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1510
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0449
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0573
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0565
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0569
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0559
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterAdelicGLEqOne
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalType
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContentZetaSeries
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content

theorem one_lt_qv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) : 1 < (qv v : ℝ) := by
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have : 1 < Ideal.absNorm v.asIdeal := by omega
  simp only [qv, NNReal.coe_natCast]
  exact_mod_cast this

theorem hasSum_field (q : ℝ) (hq : 1 < q) (s : ℕ) (hs : 1 ≤ s) :
    HasSum (fun k : ℕ => ((q ^ (2 * k))⁻¹) ^ s) (1 - (q ^ (2 * s))⁻¹)⁻¹ := by
  have h0 : 0 < q := by linarith
  have hr : (q ^ (2 * s))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  have := hasSum_geometric_of_lt_one (r := (q ^ (2 * s))⁻¹) (by positivity) hr
  convert this using 2 with k
  rw [inv_pow, inv_pow, ← pow_mul, ← pow_mul]
  congr 2
  ring

theorem hasSum_split (q : ℝ) (hq : 1 < q) (s : ℕ) (hs : 1 ≤ s) :
    HasSum (fun p : ℕ × ℕ => ((q ^ (p.1 + p.2))⁻¹) ^ s) (((1 - (q ^ s)⁻¹)⁻¹) ^ 2) := by
  have h0 : 0 < q := by linarith
  have hr : (q ^ s)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq (by omega))
  have hg := hasSum_geometric_of_lt_one (r := (q ^ s)⁻¹) (by positivity) hr
  have hn : Summable fun k : ℕ => ‖((q ^ s)⁻¹) ^ k‖ := hg.summable.norm
  have := hg.mul hg (summable_mul_of_summable_norm hn hn)
  have e : (fun p : ℕ × ℕ => ((q ^ (p.1 + p.2))⁻¹) ^ s) = fun p : ℕ × ℕ => ((q ^ s)⁻¹) ^ p.1 * ((q ^ s)⁻¹) ^ p.2 := by
    funext p
    rw [← pow_add, inv_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm s]
  rw [e, pow_two]
  exact this

theorem content : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ (ι : Type) (_ : Countable ι) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w ∧ ∀ s : ℕ, 1 ≤ s → HasSum (fun i => (((qv v : ℝ) ^ w i)⁻¹) ^ s) (zetaV E v s) := by
  intro F E _ _ _ _ _ σ h d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have hne : ∃ x, σ x ≠ x := by
    by_contra hc
    push_neg at hc
    obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
    have hreal : w.IsReal := by
      rw [← NumberField.InfinitePlace.mk_embedding w, NumberField.InfinitePlace.isReal_mk_iff,
        NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun x ↦ ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      change star (w.embedding x) = w.embedding x
      rw [← h.2.2.2, hc]
    exact NumberField.InfinitePlace.not_isReal_iff_isComplex.2 (h.2.1.isComplex w) hreal
  obtain ⟨D, b₂, hsq, hb0, hσ1, hD⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 hinv hne
  have hD0 : D ≠ 0 := fun h0 => hsq (h0 ▸ IsSquare.zero)
  have I := GlobalTheory.T.integral_almost_all_places F E σ h
  filter_upwards [(I d b).2 D hD0, (I d b).2 2 two_ne_zero,
    Filter.eventually_all.2 fun k => (I 2 b₂).1 (b k),
    Filter.eventually_all.2 fun j => (I d b).1 (b₂ j)] with v hD1 h21 hBC hCB
  have hq := one_lt_qv v
  by_cases hres : ∃ e : v.adicCompletionIntegers F, Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) < 1
  · obtain ⟨e, he⟩ : ∃ e : Fv F v, e ^ 2 = algebraMap F (Fv F v) D := by
      obtain ⟨e, he⟩ := hres
      have hDR : algebraMap F (Fv F v) D ∈ v.adicCompletionIntegers F := hD1.le
      have h2' : Valued.v (2 : Fv F v) = 1 := by simpa [map_ofNat] using h21
      have := GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2' ⟨_, hDR⟩ hD1 ?_
      · obtain ⟨r, hr⟩ := this
        exact ⟨r, by rw [pow_two]; exact hr.symm⟩
      · refine ⟨IsLocalRing.residue _ e, ?_⟩
        rw [← map_mul, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
          mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
        intro h1
        have : Valued.v ((e : Fv F v) ^ 2 - algebraMap F (Fv F v) D) = 1 := by
          rw [← Valuation.map_neg]
          simpa [pow_two] using h1
        exact absurd he (by rw [this]; exact lt_irrefl _)
    obtain ⟨hnf, c, c1, c3, c4, c5⟩ := GlobalTheory.T.quadratic_basis_integral_order F E σ h d b b₂ D hb0 hσ1 hD v hD1 h21 hBC hCB e he
    refine ⟨ℕ × ℕ, inferInstance, c, fun i => i.1 + i.2, ⟨c1, ?_, c3, c4, c5⟩, ?_⟩
    · intro i lam hlam
      obtain ⟨t, ht, hn⟩ := c3 i
      exact GlobalTheory.T.local_unit_scaling_norm_measure F E σ h d b v lam hlam (c i) t _ (c1 i).1 ht hn
    · intro s hs
      rw [zetaV, if_neg hnf]
      exact hasSum_split _ hq s hs
  · obtain ⟨hf, c, c1, c3, c4, c5⟩ := GlobalTheory.T.quadratic_basis_integral_unramified F E σ h d b b₂ D hb0 hσ1 hD v hD1 h21 hBC hCB hres
    refine ⟨ℕ, inferInstance, c, fun i => 2 * i, ⟨c1, ?_, c3, c4, c5⟩, ?_⟩
    · intro i lam hlam
      obtain ⟨t, ht, hn⟩ := c3 i
      exact GlobalTheory.T.local_unit_scaling_norm_measure F E σ h d b v lam hlam (c i) t _ (c1 i).1 ht hn
    · intro s hs
      rw [zetaV, if_pos hf]
      exact hasSum_field _ hq s hs

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedVolumeStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fibre_measure_unramified_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ (c : (HermR (Fv F v) σ n)) (A : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), IsCompact A → IsOpen A → ∀ Tt : ℕ → Set (Fin n → Fin M → (Fv F v ⊗[F] E)), Monotone Tt → (∀ j, IsCompact (Tt j) ∧ IsOpen (Tt j) ∧ Tt j ⊆ A ∧ Tt j ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X}) → A ∩ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ j, Tt j → ∀ ε : ℕ → ℝ≥0, Filter.Tendsto ε Filter.atTop (nhds 0) → (∀ (j : ℕ) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) ((A \ Tt j) ∩ gramIn (Fv F v) σ J Y) ≤ ε j * (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y) → mv c A ≠ ⊤ ∧ ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : (HermR (Fv F v) σ n)) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : (HermR (Fv F v) σ n))).smallSets → (∀ k, MeasurableSet (A ∩ gramNear (Fv F v) σ J c (U k)) ∧ (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (A ∩ gramNear (Fv F v) σ J c (U k)) ≠ ⊤) ∧ Filter.Tendsto (fun k => ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (A ∩ gramNear (Fv F v) σ J c (U k))).toReal / ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.Lim.avg_tendsto_free | exact GlobalTheory.CompanionTheory.AvgFree.Lim.avg_tendsto_free | (intros; apply GlobalTheory.CompanionTheory.AvgFree.Lim.avg_tendsto_free <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGoodReduction
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.LocGoodProof

section Generic

variable {G G' : Type} [Group G] [Group G']

theorem mem_twCent_prodMap (θ : G →* G) (θ' : G' →* G') (δ g : G × G') :
    g ∈ twCent (θ.prodMap θ') δ ↔ g.1 ∈ twCent θ δ.1 ∧ g.2 ∈ twCent θ' δ.2 := by
  change g * δ = δ * (θ.prodMap θ') g ↔ g.1 * δ.1 = δ.1 * θ g.1 ∧ g.2 * δ.2 = δ.2 * θ' g.2
  exact Prod.ext_iff

theorem mul_norm_comm (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) {δ g : G} (hg : g ∈ twCent θ δ) :
    g * (δ * θ δ) = δ * θ δ * g := by
  have h : g * δ = δ * θ g := hg
  have h' : θ g * θ δ = θ δ * g := by
    have := congrArg θ h
    simpa only [map_mul, hθ] using this
  rw [← mul_assoc, h, mul_assoc, h', mul_assoc]

variable [TopologicalSpace G] [TopologicalSpace G']

theorem isCompact_closure_zpowers_of_map [T2Space G'] (φ : G →* G') (hφ : Continuous φ) (t : G)
    (ht : IsCompact (closure (Subgroup.zpowers t : Set G))) :
    IsCompact (closure (Subgroup.zpowers (φ t) : Set G')) := by
  have hC := ht.image hφ
  refine hC.of_isClosed_subset isClosed_closure (closure_minimal ?_ hC.isClosed)
  rintro _ ⟨k, rfl⟩
  exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩

theorem cptPart_le_prod [T2Space G] [T2Space G'] [ContinuousMul G] [ContinuousMul G'] (S : Subgroup (G × G'))
    (T : Subgroup G) (T' : Subgroup G') (hS : ∀ g ∈ S, g.1 ∈ T ∧ g.2 ∈ T') :
    cptPart S ≤ (cptPart T).prod (cptPart T') := by
  rw [cptPart, Subgroup.closure_le]
  rintro t ⟨htS, htc⟩
  exact ⟨Subgroup.subset_closure ⟨(hS t htS).1,
      isCompact_closure_zpowers_of_map (MonoidHom.fst G G') continuous_fst t htc⟩,
    Subgroup.subset_closure ⟨(hS t htS).2,
      isCompact_closure_zpowers_of_map (MonoidHom.snd G G') continuous_snd t htc⟩⟩

theorem good_prod {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] [T2Space G'] (θ : G →* G) (θ' : G' →* G') (K : Subgroup G)
    (K' : Subgroup G') (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) (ho' : IsOpen (K' : Set G'))
    (hc' : IsCompact (K' : Set G')) (δ : G × G')
    (hcomm : ∀ a b, a ∈ twCent θ δ.1 → b ∈ twCent θ δ.1 → a * b = b * a)
    (hcomm' : ∀ a b, a ∈ twCent θ' δ.2 → b ∈ twCent θ' δ.2 → a * b = b * a)
    (H : Subgroup G) (H' : Subgroup G') (hH : IsCompact (H : Set G)) (hH' : IsCompact (H' : Set G'))
    (hP : cptPart (twCent θ δ.1) ≤ H) (hP' : cptPart (twCent θ' δ.2) ≤ H') :
    PositivityTheory.Rg.BcB.G8.Fin.Good (θ.prodMap θ') (K.prod K') δ := by
  have hmem := fun g => mem_twCent_prodMap θ θ' δ g
  have hKo : IsOpen ((K.prod K' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact ho.prod ho'
  have hKc : IsCompact ((K.prod K' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact hc.prod hc'
  have hHc : IsCompact ((H.prod H' : Subgroup (G × G')) : Set (G × G')) := by
    rw [Subgroup.coe_prod]; exact hH.prod hH'
  have hle : cptPart (twCent (θ.prodMap θ') δ) ≤ H.prod H' :=
    (cptPart_le_prod _ _ _ fun g hg => (hmem g).1 hg).trans (Subgroup.prod_mono hP hP')
  refine ⟨fun g hg g' hg' => ?_, fun x => ⟨GlobalTheory.LocFin.inf_le_cptPart _ _ (GlobalTheory.LocFin.isCompact_map_conj _ hKc x),
    GlobalTheory.LocFin.relIndex_cptPart_ne_zero _ _ _ (GlobalTheory.LocFin.isOpen_map_conj _ hKo x) hHc hle⟩⟩
  obtain ⟨ga, gb⟩ := (hmem g).1 hg
  obtain ⟨ga', gb'⟩ := (hmem g').1 hg'
  exact Prod.ext (hcomm _ _ ga ga') (hcomm' _ _ gb gb')

end Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mul_nrmL_comm (hU : Unr E) (n : ℕ) (w : Pl E) {y g : GLw n w} (hg : g ∈ twCent (thL n w) y) :
    g * nrmL n w y = nrmL n w y * g := by
  have hinv := (GlobalTheory.BCT.ThBasic.twist_basic E hU n w).2.1
  by_cases hs : IsSplitAt w
  · have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    rw [h1] at hg
    have h : g * y = y * g := hg
    simpa only [nrmL, if_pos hs] using h
  · have h1 : thL n w = thetaGL n (cj w) := by rw [thL, if_neg hs]
    rw [h1] at hg hinv
    simpa only [nrmL, if_neg hs] using mul_norm_comm _ hinv hg

theorem twCent_comm (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hy : (nrmL n w y).val.charpoly.Separable)
    (g h : GLw n w) (hg : g ∈ twCent (thL n w) y) (hh : h ∈ twCent (thL n w) y) : g * h = h * g := by
  have key : ∀ {u : GLw n w}, u ∈ twCent (thL n w) y → Commute (nrmL n w y).val u.val := fun {u} hu => by
    have := congrArg Units.val (mul_nrmL_comm hU n w hu)
    rw [Units.val_mul, Units.val_mul] at this
    exact this.symm
  exact Units.ext (GlobalTheory.BCT.CentComm.commute_of_commute_separable hy (key hg) (key hh)).eq

theorem cptPart_le_compact (hU : Unr E) (n : ℕ) (w : Pl E) (y : GLw n w) (hs : (nrmL n w y).val.charpoly.Separable) :
    ∃ H : Subgroup (GLw n w), IsCompact (H : Set (GLw n w)) ∧ cptPart (twCent (thL n w) y) ≤ H := by
  set M := nrmL n w y with hM
  set N : Matrix (Fin n) (Fin n) (w.adicCompletion E) := (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hN
  have hval : ∀ g : GLw n w, Commute g M → (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * N = N * g := by
    intro g hg
    have := congrArg (fun x : GLw n w => (x : Matrix (Fin n) (Fin n) (w.adicCompletion E))) hg.eq
    simpa [Units.val_mul] using this
  have hadj : ∀ g : GLw n w, Commute g M →
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) ∈ Algebra.adjoin (w.adicCompletion E) {N} :=
    fun g hg => GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute N _ hs (hval g hg)
  have hcomm : ∀ g h : GLw n w, Commute g M → Commute h M → Commute g h := by
    intro g h hg hh
    have h1 : Commute (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (h : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute (hadj h hh) ?_
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact hval g hg
    exact Units.ext (by simpa [Units.val_mul] using h1.eq)
  let S : Set (GLw n w) := {g | Commute g M ∧ IsCompact (closure (Subgroup.zpowers g : Set (GLw n w)))}
  let H0 : Subgroup (GLw n w) :=
    { carrier := S
      one_mem' := by
        refine ⟨Commute.one_left M, ?_⟩
        rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
        exact isCompact_singleton
      mul_mem' := by
        intro g h hg hh
        refine ⟨hg.1.mul_left hh.1, ?_⟩
        have hK := hg.2.mul hh.2
        refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
        rintro x ⟨k, rfl⟩
        simp only
        rw [(hcomm g h hg.1 hh.1).mul_zpow]
        exact Set.mul_mem_mul (subset_closure ⟨k, rfl⟩) (subset_closure ⟨k, rfl⟩)
      inv_mem' := by
        intro g hg
        refine ⟨hg.1.inv_left, ?_⟩
        show IsCompact (closure (Subgroup.zpowers g⁻¹ : Set (GLw n w)))
        rw [Subgroup.zpowers_inv]
        exact hg.2 }
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_valuation_bound_of_isIntegral_mem_adjoin E w n N hs
  have hB := GlobalTheory.T.isCompact_GL_bounded_entries_completion_finitePlace E w n c
  have hSB : (H0 : Set (GLw n w)) ⊆ {g : GL (Fin n) (w.adicCompletion E) | ∀ i j,
      Valued.v ((g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c ∧
      Valued.v (((g⁻¹ : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ c} := by
    intro g hg
    have hg' : g⁻¹ ∈ H0 := H0.inv_mem hg
    intro i j
    exact ⟨hc _ (hadj g hg.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g hg.2) i j,
      hc _ (hadj g⁻¹ hg'.1) (GlobalTheory.T.isIntegral_adicCompletionIntegers_of_isCompact_zpowers E w n g⁻¹ hg'.2) i j⟩
  refine ⟨H0.topologicalClosure, ?_, ?_⟩
  · rw [Subgroup.topologicalClosure_coe]
    exact hB.of_isClosed_subset isClosed_closure (closure_minimal hSB hB.isClosed)
  · refine le_trans ?_ (Subgroup.le_topologicalClosure H0)
    rw [cptPart, Subgroup.closure_le]
    rintro t ⟨ht, htc⟩
    exact ⟨mul_nrmL_comm hU n w ht, htc⟩

theorem good_pair (hU : Unr E) (a b : ℕ) (w : Pl E) (y : GLw a w × GLw b w)
    (h₁ : (nrmL a w y.1).val.charpoly.Separable) (h₂ : (nrmL b w y.2).val.charpoly.Separable) :
    PositivityTheory.Rg.BcB.G8.Fin.Good ((thL a w).prodMap (thL b w)) ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) y := by
  obtain ⟨ho₁, hc₁⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨ho₂, hc₂⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b
  obtain ⟨H₁, hH₁, hP₁⟩ := cptPart_le_compact hU a w y.1 h₁
  obtain ⟨H₂, hH₂, hP₂⟩ := cptPart_le_compact hU b w y.2 h₂
  exact good_prod (G := GLw a w) (G' := GLw b w) (thL a w) (thL b w) (GlobalTheory.LFun.KGL w a) (GlobalTheory.LFun.KGL w b)
    ho₁ hc₁ ho₂ hc₂ y (twCent_comm hU a w y.1 h₁) (twCent_comm hU b w y.2 h₂) H₁ H₂ hH₁ hH₂ hP₁ hP₂

theorem locGood : PositivityTheory.Rg.BcB.G8.Fin.LocGood := by
  intro E _ _ _ hU a b w y h₁ h₂
  exact good_pair hU a b w y h₁ h₂

end GlobalTheory.CompanionTheory.LocGoodProof

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInnerProductLeftIntegralStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_inner_product_left_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (κ : GL (Fin 2) F), κ ∈ integralGL F 2 → ∀ (h : GL (Fin 2) F) (g : GL (Fin 3) F),
  Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) (κ * h) g = Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h g := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.inn_Φ0_integral_mul | exact GlobalTheory.CompanionTheory.LFUDom.inn_Φ0_integral_mul | (intros; apply GlobalTheory.CompanionTheory.LFUDom.inn_Φ0_integral_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInnerProductSupportStatement
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_inner_product_support : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (h : GL (Fin 2) F) (l : Fin 3 → ℤ),
  ((¬ ∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) = 0) ∧
  ((∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) =
      ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ) := by
  first | exact @GlobalTheory.CompanionTheory.LFUDom.innred | exact GlobalTheory.CompanionTheory.LFUDom.innred | (intros; apply GlobalTheory.CompanionTheory.LFUDom.innred <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMatrixIntegral
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

theorem inclR_mem_Rv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E)
    (h : ∀ k, algebraMap F (Fv F v) (bs.repr e k) ∈ v.adicCompletionIntegers F) :
    inclR (F := F) (Fv F v) e ∈ Rv bs v := by
  simp only [Rv, Set.mem_ofPred_eq]
  intro k
  rw [show inclR (F := F) (Fv F v) e = (1 : Fv F v) ⊗ₜ[F] e from rfl,
    Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  exact h k

theorem sigR_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ ((1 : Fv F v) ⊗ₜ[F] e)
    = (1 : Fv F v) ⊗ₜ[F] σ e
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem coe_det_matS {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (S : Subring (Fv F v ⊗[F] E)) {m : ℕ} (X : Matrix (Fin m) (Fin m) E)
    (hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S) :
    (((matS S X hX).det : S) : Fv F v ⊗[F] E) = inclR (F := F) (Fv F v) X.det := by
  have h1 : S.subtype.mapMatrix (matS S X hX) = (inclR (F := F) (Fv F v)).mapMatrix X := by
    ext i j
    rfl
  rw [show (((matS S X hX).det : S) : Fv F v ⊗[F] E) = S.subtype (matS S X hX).det from rfl,
    RingHom.map_det, h1, ← RingHom.map_det]

theorem locMat : LocMat := by
  unfold LocMat
  intro F E _ _ _ _ _ σ d bs v S σS hS hσS m X hherm hdet hint
  have memS : ∀ e : E, (∀ k, algebraMap F (Fv F v) (bs.repr e k) ∈ v.adicCompletionIntegers F) →
      inclR (F := F) (Fv F v) e ∈ S := by
    intro e he
    have h := inclR_mem_Rv bs v e he
    rw [← hS] at h
    exact h
  have hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S := by
    intro i j
    apply memS
    intro k
    apply hint
    simp only [matSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl ⟨(i, j, k), rfl⟩
  have hinv : inclR (F := F) (Fv F v) X.det⁻¹ ∈ S := by
    apply memS
    intro k
    apply hint
    simp only [matSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨k, rfl⟩
  refine ⟨hX, ?_, ?_⟩
  · ext i j
    show ((σS (matS S X hX j i) : S) : Fv F v ⊗[F] E) = inclR (F := F) (Fv F v) (X i j)
    rw [hσS]
    show sigR (Fv F v) σ (inclR (F := F) (Fv F v) (X j i)) = inclR (F := F) (Fv F v) (X i j)
    rw [sigR_inclR, hherm]
  · refine isUnit_iff_exists_inv.mpr ⟨⟨inclR (F := F) (Fv F v) X.det⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    show (((matS S X hX).det : S) : Fv F v ⊗[F] E) * inclR (F := F) (Fv F v) X.det⁻¹ = 1
    rw [coe_det_matS, ← map_mul, mul_inv_cancel₀ hdet, map_one]

end GlobalTheory.CompanionTheory.Gunr

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LowerZetaIntegralBoundaryRelationStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_zeta_integral_boundary_relation : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Set0 μ 𝓕 mK 𝓓 → Aut H → IsOfFinOrder c → ∀ s : ℂ,
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) (𝓕 ∩ {g | Dt g < 1}) μ →
    GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s * (1 - 2 ^ (-s)) = GlobalTheory.CompanionTheory.RSZeta.Bd μ 𝓕 H c s * 2 ^ (-s) := by
  first | exact @GlobalTheory.CompanionTheory.RSZeta.Jl_shift | exact GlobalTheory.CompanionTheory.RSZeta.Jl_shift | (intros; apply GlobalTheory.CompanionTheory.RSZeta.Jl_shift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicRationalCompact
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.ParCocompact

theorem levi_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ C : Set (GAd σ J), IsCompact C ∧ C ⊆ leviMin σ J X Y ∩ minParOne σ J X ∧ ∀ m ∈ leviMin σ J X Y, m ∈ minParOne σ J X → ∃ δ ∈ ratPts σ J, δ ∈ leviMin σ J X Y ∧ ∃ c ∈ C, m = δ * c := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨L, hL, hLc⟩ := GlobalTheory.T.levi_parabolic_intersection_closed F E σ h n J hJ r X Y hW
  have hmem : ∀ g, g ∈ L ↔ g ∈ leviMin σ J X Y ∧ g ∈ minParOne σ J X := fun g => by
    rw [← SetLike.mem_coe, hL]; rfl
  obtain ⟨ε, hε, hh⟩ := GlobalTheory.T.idele_bound_of_joint_anisotropic F E σ h n J hJ _ (hermFam σ J X Y) (L : Set (GAd σ J))
    (GlobalTheory.T.hermitian_family_anisotropic_joint F E σ h n J hJ r X Y hW)
    (fun g hg j => GlobalTheory.T.levi_minimal_idele_hermitian_bound F E σ h n J hJ r X Y hW g ((hmem g).1 hg).1 ((hmem g).1 hg).2 j)
  obtain ⟨Ω, hΩ, hsub, hred⟩ := GlobalTheory.T.commutant_closed_subgroup_compact_quotient F E σ h n J hJ _ (projFam σ J X Y) L hLc
    (fun g hg k => GlobalTheory.T.levi_minimal_commutes_projection_family F E σ h n J hJ r X Y hW g ((hmem g).1 hg).1 k) ⟨ε, hε, hh⟩
    (fun γ hγ hc => (hmem γ).2 (GlobalTheory.T.mem_levi_minimal_of_commutes_projections F E σ h n J hJ r X Y hW γ hγ hc))
  refine ⟨Ω, hΩ, fun c hc => (hmem c).1 (hsub hc), fun m hm hm1 => ?_⟩
  obtain ⟨δ, hδ, hδL, hd⟩ := hred m ((hmem m).2 ⟨hm, hm1⟩)
  exact ⟨δ, hδ, ((hmem δ).1 hδL).1, _, hd, by group⟩

theorem minParOne_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ ∀ p ∈ minParOne σ J X, ∃ δ ∈ ratPts σ J, δ ∈ minPar σ J X ∧ ∃ ω ∈ Ω, p = δ * ω := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨hcl, hmul⟩ := minParOne_props h hJ hW
  obtain ⟨C, hC, hU⟩ := GlobalTheory.CompanionTheory.UnipCocompact.unipMin_cocompact F E σ h n J hJ r X Y hW
  obtain ⟨C', hC', hsub, hM⟩ := levi_cocompact F E σ h n J hJ r X Y hW
  refine ⟨(C ∩ minParOne σ J X) * C', (hC.inter_right hcl).mul hC', ?_, fun p hp => ?_⟩
  · rintro _ ⟨c, hc, c', hc', rfl⟩
    exact hmul _ hc.2 _ (hsub hc').2
  · obtain ⟨u, hu, m, hm, hm1, rfl⟩ := GlobalTheory.T.minimal_parabolic_levi_decomposition F E σ h n J hJ r X Y hW p hp
    obtain ⟨δ, hδ, hδL, c', hc', rfl⟩ := hM m hm hm1
    have hu' := GlobalTheory.T.levi_normalizes_unipotent_ter F E σ h n J hJ r X Y hW δ hδL u hu
    obtain ⟨δ', hδ', hδU, c, hc, hcU, e⟩ := hU _ hu'
    refine ⟨δ * δ', mul_mem hδ hδ', mul_mem_minPar (leviMin_subset X Y hδL)
      (minParOne_subset (unipMin_subset_minParOne X hδU)), c * c',
      ⟨c, ⟨hc, unipMin_subset_minParOne X hcU⟩, c', hc', rfl⟩, ?_⟩
    have e2 : u = δ * (δ' * c) * δ⁻¹ := by
      rw [← e]; group
    rw [e2]; group

end GlobalTheory.CompanionTheory.ParCocompact

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularCharacterAdelicGLEqOneStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularCharacter_adelic_GL_eq_one : ∀ (D : D7) (r : ℕ) [LocallyCompactSpace (GL (Fin r) (AE D))] (a : GL (Fin r) (AE D)), Measure.modularCharacterFun a = 1 := by
  first | exact @GlobalTheory.CompanionTheory.GLUnimod.modularCharacterFun_GL_adele | exact GlobalTheory.CompanionTheory.GLUnimod.modularCharacterFun_GL_adele | (intros; apply GlobalTheory.CompanionTheory.GLUnimod.modularCharacterFun_GL_adele <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalTypeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_local_type : Ad3.R.B0 → Ad3.R.HeckeSumLocalTranslates := by
  first | exact @GlobalTheory.CompanionTheory.RSq.f3a | exact GlobalTheory.CompanionTheory.RSq.f3a | (intros; apply GlobalTheory.CompanionTheory.RSq.f3a <;> assumption)
end

