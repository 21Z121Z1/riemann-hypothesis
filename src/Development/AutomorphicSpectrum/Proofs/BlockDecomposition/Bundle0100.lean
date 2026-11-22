import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0090
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import GroundTheory.AutomorphicForms.FiniteBruhat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0062
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0092
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorOpenCompactStatement
section
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_open_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → IsOpen {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} ∧ IsCompact {ξ : Fin n → k | ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1} := by
  first | exact @GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact | exact GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.CharPerp.perp_isOpen_isCompact <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFundamentalDomainIntegers
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Equi

open GlobalTheory.CompanionTheory.SW.RealCoord

section Domain

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def infToMixed (y : Ainf F) : mixedEmbedding.mixedSpace F := toMixed F (coord F y)

theorem infToMixed_add (x y : Ainf F) : infToMixed F (x + y) = infToMixed F x + infToMixed F y := by
  show toMixed F (coord F (x + y)) = toMixed F (coord F x) + toMixed F (coord F y)
  rw [map_add, toMixed_add]

theorem infToMixed_algebraMap (x : F) :
    infToMixed F (algebraMap F (Ainf F) x) = mixedEmbedding F x := toMixed_coord_algebraMap F x

theorem infToMixed_sub (x y : Ainf F) : infToMixed F (x - y) = infToMixed F x - infToMixed F y := by
  rw [eq_sub_iff_add_eq, ← infToMixed_add, sub_add_cancel]

theorem measurable_infToMixed : Measurable (infToMixed F) := (measurePreserving_toMixed F).measurable.comp (coord_measurable F)

def infDomain : Set (Ainf F) :=
  infToMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)

theorem measurableSet_infDomain : MeasurableSet (infDomain F) := measurable_infToMixed F (ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F))

theorem exists_mem_lattice {x : mixedEmbedding.mixedSpace F}
    (hx : x ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F))) :
    ∃ a : 𝓞 F, mixedEmbedding F (a : F) = x := by
  rw [mixedEmbedding.mem_span_latticeBasis F] at hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a, rfl⟩

theorem mem_lattice (a : 𝓞 F) :
    mixedEmbedding F (a : F) ∈ Submodule.span ℤ (Set.range (mixedEmbedding.latticeBasis F)) := (mixedEmbedding.mem_span_latticeBasis F).2 ⟨a, rfl⟩

theorem existsUnique_sub_mem_infDomain (y : Ainf F) :
    ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ infDomain F := by
  obtain ⟨v, hv, huniq⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (mixedEmbedding.latticeBasis F)
    (infToMixed F y)
  obtain ⟨a, ha⟩ := exists_mem_lattice F (Submodule.neg_mem _ v.2)
  have key : ∀ b : 𝓞 F, infToMixed F (y - algebraMap F (Ainf F) (b : F)) =
      -mixedEmbedding F (b : F) + infToMixed F y := fun b => by
    rw [infToMixed_sub, infToMixed_algebraMap]
    abel
  refine ⟨a, ?_, fun b hb => ?_⟩
  · show infToMixed F (y - algebraMap F (Ainf F) (a : F)) ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
    rw [key, ha, neg_neg]
    exact hv
  · have hw := huniq ⟨-mixedEmbedding F (b : F), neg_mem (mem_lattice F b)⟩ (by
      show -mixedEmbedding F (b : F) + infToMixed F y ∈ ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)
      rw [← key]
      exact hb)
    have hb' : mixedEmbedding F (b : F) = mixedEmbedding F (a : F) := by
      rw [ha]
      have := congrArg Subtype.val hw
      simp only at this
      rw [← this, neg_neg]
    exact RingOfIntegers.ext (mixedEmbedding_injective F hb')

theorem exists_isCompact_superset_infDomain :
    ∃ K₀ : Set (Ainf F), IsCompact K₀ ∧ infDomain F ⊆ K₀ := by
  let g : mixedEmbedding.mixedSpace F → (InfinitePlace F → ℝ) := fun x w => x.1 ⟨w, IsTotallyReal.isReal w⟩
  have hg : Continuous g := continuous_pi fun w => (continuous_apply _).comp continuous_fst
  have hC : IsCompact (closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))) :=
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure
  refine ⟨coord F ⁻¹' (g '' closure (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F))), ?_, ?_⟩
  · rw [← coordHomeo_coe]
    exact (coordHomeo F).isCompact_preimage.2 (hC.image hg)
  · intro y hy
    exact ⟨infToMixed F y, subset_closure hy, rfl⟩

theorem measure_infDomain (li : Measure (Ainf F)) (hl : IsStdInf li) : li (infDomain F) = 1 := by
  have hfd := ZSpan.fundamentalDomain_measurableSet (mixedEmbedding.latticeBasis F)
  have hmeas := (measurePreserving_toMixed F).measurable hfd
  have hpos : 0 < Real.sqrt |(discr F : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero F)))
  have hv : volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) := by
    rw [mixedEmbedding.volume_fundamentalDomain_latticeBasis, IsTotallyReal.nrComplexPlaces_eq_zero, pow_zero,
      one_mul, ← ENNReal.ofReal_coe_nnreal, Real.coe_sqrt, coe_nnnorm, Int.norm_eq_abs]
  calc li (infDomain F)
      = (li.map (coord F)) (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) :=
        (Measure.map_apply (coord_measurable F) hmeas).symm
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (toMixed F ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [map_coord_eq F li hl, Measure.smul_apply, smul_eq_mul]
    _ = ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|)⁻¹ *
          volume (ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis F)) := by
        rw [(measurePreserving_toMixed F).measure_preimage hfd.nullMeasurableSet]
    _ = 1 := by
        rw [hv, ← ENNReal.ofReal_mul (inv_nonneg.2 (Real.sqrt_nonneg _)), inv_mul_cancel₀ hpos.ne',
          ENNReal.ofReal_one]

end Domain

theorem exists_bounded_infDomain : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ li : Measure (Ainf F), IsStdInf li → ∃ D K₀ : Set (Ainf F), MeasurableSet D ∧ IsCompact K₀ ∧ D ⊆ K₀ ∧
      li D = 1 ∧ ∀ y : Ainf F, ∃! a : 𝓞 F, y - algebraMap F (Ainf F) (a : F) ∈ D := by
  intro F _ _ hTR li hl
  have := hTR
  obtain ⟨K₀, hK₀, hsub⟩ := exists_isCompact_superset_infDomain F
  exact ⟨infDomain F, K₀, measurableSet_infDomain F, hK₀, hsub, measure_infDomain F li hl,
    existsUnique_sub_mem_infDomain F⟩

end GlobalTheory.CompanionTheory.Equi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedCokernelLimitToLevel
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TwCok

theorem pow_torsion_bounded {W : Type} [CommRing W] [IsNoetherianRing W] (r : W) (T : Type 1)
    [AddCommGroup T] [Module W T] [Module.Finite W T] :
    ∃ c : ℕ, ∀ (k : ℕ) (t : T), r ^ k • t = 0 → r ^ c • t = 0 := by
  haveI := isNoetherian_of_isNoetherianRing_of_finite W T
  let f : ℕ →o Submodule W T :=
    ⟨fun k => LinearMap.ker ((r ^ k) • LinearMap.id : T →ₗ[W] T), fun a b hab t ht => by
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at ht ⊢
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
      rw [pow_add, mul_comm, mul_smul, ht, smul_zero]⟩
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance f
  refine ⟨n, fun k t ht => ?_⟩
  rcases le_total k n with hkn | hnk
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hkn
    rw [pow_add, mul_comm, mul_smul, ht, smul_zero]
  · have h1 : t ∈ f k := by
      simp only [f, OrderHom.coe_mk, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact ht
    rw [← hn k hnk] at h1
    have h2 : t ∈ LinearMap.ker ((r ^ n) • LinearMap.id : T →ₗ[W] T) := h1
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at h2
    exact h2

variable {W : Type} [CommRing W] {l : ℕ} {S S' : Sys.{1} W}

def conn (Q : LSeq l S S') (n : ℕ) (x : S.M n) : S'.lim :=
  ⟨fun a => Q.δ n a x, fun a => Q.δ_r n a x⟩

theorem conn_smul (Q : LSeq l S S') (n : ℕ) (s : W) (x : S.M n) :
    s • conn Q n x = conn Q n (s • x) := by
  apply Subtype.ext
  funext a
  simp [conn]

theorem conn_kill (Q : LSeq l S S') (n : ℕ) (x : S.M n) : ((l : W) ^ n) • conn Q n x = 0 := by
  rw [conn_smul, Q.kill n x]
  apply Subtype.ext
  funext a
  simp [conn]

theorem lift_of_conn_zero (Q : LSeq l S S') (hA : ∀ n, IsArtinian W (S.M n)) (n : ℕ) (x : S.M n)
    (h : ∀ a, Q.δ n a x = 0) : ∃ y : S.lim, y.1 n = x := by
  classical
  have hy : ∀ m, n ≤ m → ∃ u : S.M m, Q.ρ m n u = x := fun m hm =>
    Q.ex₂ (m - n) n m (by omega) x (h _)
  let y : ∀ m, S.M m := fun m => if hm : n ≤ m then (hy m hm).choose else 0
  have hyx : ∀ m (hm : n ≤ m), Q.ρ m n (y m) = x := by
    intro m hm
    simp only [y, dif_pos hm]
    exact (hy m hm).choose_spec
  let N : ∀ m, Submodule W (S.M m) := fun m => if n ≤ m then LinearMap.ker (Q.ρ m n) else ⊤
  have hN : ∀ m (hm : n ≤ m), N m = LinearMap.ker (Q.ρ m n) := fun m hm => if_pos hm
  have hN' : ∀ m (hm : ¬ n ≤ m), N m = ⊤ := fun m hm => if_neg hm
  have hNr : ∀ m, ∀ u ∈ N (m + 1), S.r m u ∈ N m := by
    intro m u hu
    by_cases hm : n ≤ m
    · rw [hN (m + 1) (by omega), LinearMap.mem_ker] at hu
      rw [hN m hm, LinearMap.mem_ker, ← Q.ρ_succ m n hm]
      exact hu
    · rw [hN' m hm]
      exact Submodule.mem_top
  have hyr : ∀ m, S.r m (y (m + 1)) - y m ∈ N m := by
    intro m
    by_cases hm : n ≤ m
    · rw [hN m hm, LinearMap.mem_ker, map_sub, ← Q.ρ_succ m n hm, hyx (m + 1) (by omega), hyx m hm,
        sub_self]
    · rw [hN' m hm]
      exact Submodule.mem_top
  obtain ⟨z, hz⟩ := GlobalTheory.T.artinian_limit_lift_of_compatible W S hA N y hNr hyr
  refine ⟨z, ?_⟩
  have h1 := hz n
  rw [hN n le_rfl, LinearMap.mem_ker, map_sub, Q.ρ_self, Q.ρ_self, sub_eq_zero] at h1
  have h2 := hyx n le_rfl
  rw [Q.ρ_self] at h2
  rw [← h2]
  exact h1

theorem lim_cokernel_bounded : ∀ (W : Type) [CommRing W] [IsNoetherianRing W] (l : ℕ) (S S' : Sys.{1} W)
    (_ : LSeq l S S'), (∀ n, IsArtinian W (S.M n)) → Module.Finite W S'.lim →
    ∃ c : ℕ, ∀ n (x : S.M n), ∃ y : S.lim, y.1 n = ((l : W) ^ c) • x := by
  intro W _ _ l S S' Q hA hF
  obtain ⟨c, hc⟩ := pow_torsion_bounded ((l : W)) S'.lim
  refine ⟨c, fun n x => lift_of_conn_zero Q hA n _ (fun a => ?_)⟩
  have h0 : conn Q n ((l : W) ^ c • x) = 0 := by
    rw [← conn_smul]
    exact hc n _ (conn_kill Q n x)
  have h3 := congrArg (fun v : S'.lim => (v : ∀ m, S'.M m) a) h0
  simpa [conn] using h3

end GlobalTheory.CompanionTheory.TwCok
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionTwoBlocks
section
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES GroundTheory.Automorphic

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.Bruhat

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

theorem pm_eq_permGL (σ : Equiv.Perm (Fin n)) : pm K σ = permGL K σ := rfl

theorem conj_pm_apply (τ : Equiv.Perm (Fin n)) (x : GL (Fin n) K) (i j : Fin n) :
    ((pm K τ * x * (pm K τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      (x : Matrix (Fin n) (Fin n) K) (τ⁻¹ i) (τ⁻¹ j) := by
  rw [pm_eq_permGL, ← map_inv, Units.val_mul, mul_permGL_apply, Units.val_mul, permGL_mul_apply]

theorem isBlockUT_conj {s : ℕ} (b : Fin n → Fin s) (τ : Equiv.Perm (Fin n))
    (hτ : Monotone (b ∘ τ)) {x : GL (Fin n) K} (hx : x ∈ borel n K) :
    IsBlockUT K b ((pm K τ * x * (pm K τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  intro i j hij
  rw [conj_pm_apply]
  refine (mem_borel_iff x).1 hx _ _ ?_
  by_contra hle
  have h : b i ≤ b j := by simpa [Function.comp_apply] using hτ (not_lt.1 hle)
  exact absurd hij (not_lt.2 h)

theorem conj_mem_parab {s : ℕ} (b : Fin n → Fin s) (τ : Equiv.Perm (Fin n))
    (hτ : Monotone (b ∘ τ)) {x : GL (Fin n) K} (hx : x ∈ borel n K) :
    pm K τ * x * (pm K τ)⁻¹ ∈ parab K b := by
  refine ⟨isBlockUT_conj b τ hτ hx, ?_⟩
  have e : (pm K τ * x * (pm K τ)⁻¹)⁻¹ = pm K τ * x⁻¹ * (pm K τ)⁻¹ := by group
  rw [e]
  exact isBlockUT_conj b τ hτ ((borel n K).inv_mem hx)

theorem conj_diag_mem_borel (ρ : Equiv.Perm (Fin n)) {t : GL (Fin n) K}
    (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) K) i j = 0) :
    pm K ρ * t * (pm K ρ)⁻¹ ∈ borel n K := by
  refine (mem_borel_iff _).2 fun i j hji => ?_
  rw [conj_pm_apply]
  exact ht _ _ fun e => hji.ne (ρ⁻¹.injective e).symm

theorem exists_diag_mul_uni {y : GL (Fin n) K} (hy : y ∈ borel n K) :
    ∃ t : GL (Fin n) K, (∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) K) i j = 0) ∧
      ∃ u ∈ patSet K (fun i j : Fin n => i < j), y = t⁻¹ * u := by
  have hd := borel_diag_ne_zero hy
  obtain ⟨t, -, htD⟩ := exists_borel_of_isUpperTriangular
    (Matrix.diagonal fun i => ((y : Matrix (Fin n) (Fin n) K) i i)⁻¹)
    (Matrix.blockTriangular_diagonal _) (fun i => by simpa using hd i)
  refine ⟨t, fun i j hij => by rw [htD, Matrix.diagonal_apply_ne _ hij], t * y, ?_, by group⟩
  intro i j
  have hval : ((t * y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      ((y : Matrix (Fin n) (Fin n) K) i i)⁻¹ * (y : Matrix (Fin n) (Fin n) K) i j := by
    rw [Units.val_mul, htD, Matrix.diagonal_mul]
  refine ⟨fun e => ?_, fun hne hlt => ?_⟩
  · subst e
    rw [hval, inv_mul_cancel₀ (hd i)]
  · have hji : j < i := lt_of_le_of_ne (not_lt.1 hlt) hne.symm
    rw [hval, (mem_borel_iff y).1 hy i j hji, mul_zero]

theorem bruhat_parab_parab {s s' : ℕ} (b : Fin n → Fin s) (b' : Fin n → Fin s')
    (g : GL (Fin n) K) :
    ∃ σ : Equiv.Perm (Fin n), ∃ β ∈ parab K b', ∃ α ∈ parab K b, g = β * pm K σ * α := by
  set τ := Tuple.sort b
  set τ' := Tuple.sort b'
  obtain ⟨ρ, hρ⟩ := exists_mem_doubleCoset_permGL ((pm K τ')⁻¹ * g * pm K τ)
  obtain ⟨x, hx, y, hy, hxy⟩ := DoubleCoset.mem_doubleCoset.1 hρ
  refine ⟨τ' * ρ * τ⁻¹, _, conj_mem_parab b' τ' (Tuple.monotone_sort b') hx,
    _, conj_mem_parab b τ (Tuple.monotone_sort b) hy, ?_⟩
  have hm : pm K (τ' * ρ * τ⁻¹) = pm K τ' * permGL K ρ * (pm K τ)⁻¹ := by
    simp only [pm_eq_permGL, map_mul, map_inv]
  have hg : g = pm K τ' * (x * permGL K ρ * y) * (pm K τ)⁻¹ := by
    rw [← hxy]; group
  rw [hm, hg]
  group

theorem bruhat_parab_uni {s : ℕ} (b : Fin n → Fin s) (g : GL (Fin n) K) :
    ∃ σ : Equiv.Perm (Fin n), ∃ β ∈ parab K b, ∃ u ∈ patSet K (fun i j : Fin n => i < j),
      g = β * pm K σ * u := by
  set τ := Tuple.sort b
  obtain ⟨ρ, hρ⟩ := exists_mem_doubleCoset_permGL ((pm K τ)⁻¹ * g)
  obtain ⟨x, hx, y, hy, hxy⟩ := DoubleCoset.mem_doubleCoset.1 hρ
  obtain ⟨t, ht, u, hu, hyu⟩ := exists_diag_mul_uni hy
  have hw := conj_diag_mem_borel ρ ht
  have hb : x * (pm K ρ * t * (pm K ρ)⁻¹)⁻¹ ∈ borel n K :=
    (borel n K).mul_mem hx ((borel n K).inv_mem hw)
  refine ⟨τ * ρ, _, conj_mem_parab b τ (Tuple.monotone_sort b) hb, u, hu, ?_⟩
  have hm : pm K (τ * ρ) = pm K τ * pm K ρ := by
    simp only [pm_eq_permGL, map_mul]
  have hg : g = pm K τ * (x * pm K ρ * (t⁻¹ * u)) := by
    rw [← hyu, pm_eq_permGL ρ, ← hxy]; group
  rw [hm, hg]
  group

theorem bruhatTwo : ReciprocityTheory.Ty.Fin.St.BruhatTwo :=
  fun _ _ _ _ _ => ⟨fun _ _ b b' g => bruhat_parab_parab b b' g,
    fun _ b g => bruhat_parab_uni b g⟩

end GlobalTheory.CompanionTheory.TyFin.Bruhat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionUnique
section
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.CompanionTheory.BruhatInv

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

def ind (K : Type) [Field K] {ι : Type} [DecidableEq ι] (p : ι → Prop) [DecidablePred p] :
    Matrix ι ι K :=
  Matrix.diagonal fun i => if p i then 1 else 0

theorem ind_mul_apply (p : ι → Prop) [DecidablePred p] (A : Matrix ι ι K) (i j : ι) :
    (ind K p * A) i j = (if p i then 1 else 0) * A i j := by
  simp [ind, Matrix.diagonal_mul]

theorem mul_ind_apply (p : ι → Prop) [DecidablePred p] (A : Matrix ι ι K) (i j : ι) :
    (A * ind K p) i j = A i j * (if p j then 1 else 0) := by
  simp [ind, Matrix.mul_diagonal]

theorem rank_cut_le (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (A M B : Matrix ι ι K)
    (hA : ∀ i j, p i → ¬ p j → A i j = 0) (hB : ∀ i j, q j → ¬ q i → B i j = 0) :
    (ind K p * (A * M * B) * ind K q).rank ≤ (ind K p * M * ind K q).rank := by
  have h1 : ind K p * A = ind K p * A * ind K p := by
    ext i j
    rw [mul_ind_apply, ind_mul_apply]
    by_cases hi : p i <;> by_cases hj : p j <;> simp [hi, hj, hA i j]
  have h2 : B * ind K q = ind K q * (B * ind K q) := by
    ext i j
    rw [ind_mul_apply, mul_ind_apply]
    by_cases hi : q i <;> by_cases hj : q j <;> simp [hi, hj, hB i j]
  have h3 : ind K p * (A * M * B) * ind K q =
      (ind K p * A) * (ind K p * M * ind K q) * (B * ind K q) := by
    calc ind K p * (A * M * B) * ind K q = (ind K p * A) * M * (B * ind K q) := by
          simp only [Matrix.mul_assoc]
      _ = (ind K p * A * ind K p) * M * (ind K q * (B * ind K q)) := by rw [← h1, ← h2]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h3]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem pm_apply (σ : Equiv.Perm ι) (i j : ι) :
    ((pm K σ : GL ι K) : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by
  simp only [pm, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    Equiv.Perm.inv_eq_iff_eq]

theorem rank_cut_pm (p q : ι → Prop) [DecidablePred p] [DecidablePred q] (σ : Equiv.Perm ι) :
    (ind K p * ((pm K σ : GL ι K) : Matrix ι ι K) * ind K q).rank =
      (Finset.univ.filter fun j => q j ∧ p (σ j)).card := by
  have h : ind K p * ((pm K σ : GL ι K) : Matrix ι ι K) * ind K q =
      ((pm K σ : GL ι K) : Matrix ι ι K) *
        Matrix.diagonal fun j => if q j ∧ p (σ j) then (1 : K) else 0 := by
    ext i j
    rw [mul_ind_apply, ind_mul_apply, Matrix.mul_diagonal, pm_apply]
    by_cases hij : i = σ j
    · subst hij
      by_cases h1 : p (σ j) <;> by_cases h2 : q j <;> simp [h1, h2]
    · simp [hij]
  rw [h, Matrix.rank_mul_eq_right_of_isUnit_det, Matrix.rank_diagonal, Fintype.card_subtype]
  · congr 1
    ext j
    by_cases h1 : q j ∧ p (σ j) <;> simp [h1]
  · exact (Matrix.isUnit_iff_isUnit_det _).1 (pm K σ).isUnit

def cnt {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ : Equiv.Perm ι) (a a' : ℕ) : ℕ :=
  (Finset.univ.filter fun j => (b j : ℕ) < a ∧ a' ≤ (b' (σ j) : ℕ)).card

theorem cnt_le {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ τ : Equiv.Perm ι)
    (h : ∃ β ∈ parab K b', ∃ α ∈ parab K b, pm K τ = β * pm K σ * α) (a a' : ℕ) :
    cnt b b' τ a a' ≤ cnt b b' σ a a' := by
  obtain ⟨β, hβ, α, hα, e⟩ := h
  have hM : ((pm K τ : GL ι K) : Matrix ι ι K) =
      (β : Matrix ι ι K) * ((pm K σ : GL ι K) : Matrix ι ι K) * (α : Matrix ι ι K) := by
    rw [e]; simp [Units.val_mul]
  have key := rank_cut_le (K := K) (fun i => a' ≤ (b' i : ℕ)) (fun j => (b j : ℕ) < a)
    (β : Matrix ι ι K) ((pm K σ : GL ι K) : Matrix ι ι K) (α : Matrix ι ι K)
    (fun i j hi hj => hβ.1 i j (by
      rw [Fin.lt_def]; exact lt_of_lt_of_le (not_le.mp hj) hi))
    (fun i j hj hi => hα.1 i j (by
      rw [Fin.lt_def]; exact lt_of_lt_of_le hj (not_lt.mp hi)))
  rw [← hM, rank_cut_pm, rank_cut_pm] at key
  exact key

theorem cnt_eq {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ τ : Equiv.Perm ι)
    (h : ∃ β ∈ parab K b', ∃ α ∈ parab K b, pm K τ = β * pm K σ * α) (a a' : ℕ) :
    cnt b b' τ a a' = cnt b b' σ a a' := by
  refine le_antisymm (cnt_le (K := K) b b' σ τ h a a') (cnt_le (K := K) b b' τ σ ?_ a a')
  obtain ⟨β, hβ, α, hα, e⟩ := h
  refine ⟨β⁻¹, inv_mem hβ, α⁻¹, inv_mem hα, ?_⟩
  rw [e]; group

theorem cnt_diff {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ : Equiv.Perm ι)
    (c : Fin s) (c' : Fin s') :
    cnt b b' σ (c + 1) c' + cnt b b' σ c (c' + 1) =
      cnt b b' σ c c' + cnt b b' σ (c + 1) (c' + 1) +
        Fintype.card {i // b i = c ∧ b' (σ i) = c'} := by
  rw [Fintype.card_subtype]
  simp only [cnt, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.ext_iff]
  split_ifs <;> omega

theorem bruhatUniq : ReciprocityTheory.Ty.Fin.St.BruhatUniq := by
  intro K _ _ _ ι _ _ s s' b b' σ τ h c c'
  have h1 := cnt_diff b b' σ c c'
  have h2 := cnt_diff b b' τ c c'
  simp only [cnt_eq (K := K) b b' σ τ h] at h2
  omega

end GlobalTheory.CompanionTheory.BruhatInv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardHermitianMatricesModPowStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_hermitian_matrices_mod_pow : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ n k : ℕ, Nat.card (hermMod σ ϖ n k) = q ^ (k * n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.card_hermMod | exact GlobalTheory.CompanionTheory.UnrDens.card_hermMod | (intros; apply GlobalTheory.CompanionTheory.UnrDens.card_hermMod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRangeMulQuotientBoundedLevelStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_range_mul_quotient_bounded_level : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ), IsLevelChars σ ϖ ψ → (∀ (j : ℕ) (a : R), σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j) → ∀ (k : ℕ) (d : R), σ d = d → ∃ e : ℕ, e ≤ k ∧ Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) d) = (q ^ 2) ^ e ∧ ∀ a : R, σ a = a → a ∉ lev ϖ 1 → (∑ w : R ⧸ lev ϖ k, ψ k (Ideal.Quotient.mk (lev ϖ k) (a * d) * (barσ σ ϖ hR.fix_ϖ k w * w))) = (q : ℂ) ^ (2 * k) * ((ε : ℂ) / q) ^ e := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level | exact GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.Scaled.gauss_image_level <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
section
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

def colGe (d j : ℕ) (i l : Fin d) : Prop := i < l ∧ j ≤ (l : ℕ)

variable (K : Type) [Field K]

def colGeE (d j : ℕ) (i l : Fin d) : K := if (l : ℕ) = i + 1 ∧ j ≤ (l : ℕ) then 1 else 0

def colGeR (d j : ℕ) (r : Fin j → K) (i l : Fin d) : K :=
  colGeE K d (j + 1) i l + if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0

def blkEmb (d j : ℕ) (A : Matrix (Fin j) (Fin j) K) : Matrix (Fin d) (Fin d) K := fun i l =>
  if h : (i : ℕ) < j ∧ (l : ℕ) < j then A ⟨i, h.1⟩ ⟨l, h.2⟩ else if i = l then 1 else 0

end GlobalTheory.CompanionTheory.TyFin.ColStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicityStatement
section
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_monotonicity : DetMono := by
  first | exact @GlobalTheory.CompanionTheory.DetMonotone.detMono | exact GlobalTheory.CompanionTheory.DetMonotone.detMono | (intros; apply GlobalTheory.CompanionTheory.DetMonotone.detMono <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleSurjectiveLocalSectionStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_surjective_local_section : ∀ {S : Type} [CommRing S] , Aic S → Loc S → ∀ (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of S)), Etale f → Surjective f → ∀ m : Ideal S, m.IsMaximal → ∃ e : S, IsIdempotentElem e ∧ e ∉ m ∧ SecOn f e := by
  first | exact @GlobalTheory.CompanionTheory.EtaleSections.exists_secOn_of_etale_surjective | exact GlobalTheory.CompanionTheory.EtaleSections.exists_secOn_of_etale_surjective | (intros; apply GlobalTheory.CompanionTheory.EtaleSections.exists_secOn_of_etale_surjective <;> assumption)
end

