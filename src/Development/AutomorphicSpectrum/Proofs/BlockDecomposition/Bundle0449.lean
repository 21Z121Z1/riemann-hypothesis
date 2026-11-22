import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CocompactOfMemIffAdelic
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.KroneckerWeber
import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
import GroundTheory.GlobalFields.LocalAtPlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0436
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0413

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.UnipCocompact

open GlobalTheory.UnipFlagCore

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

omit [NumberField E] in

theorem unipMin_eq_radSet (X : Matrix (Fin n) (Fin r) E) :
    unipMin σ J X = radSet σ J X Fin.val := by
  ext u
  constructor
  · rintro ⟨B, hB, hd, hX, hz⟩
    have e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * (B - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      exact congrArg (· - adMat F X) hX
    refine ⟨fun i => ⟨fun j => (B - 1) j i, fun j hij => ?_, ?_⟩, hz⟩
    · rcases (Fin.le_def.2 hij).eq_or_lt with e | e
      · subst e; simp [hd]
      · simp [hB e, e.ne']
    · funext k
      exact congrFun (congrFun e k) i
  · rintro ⟨h1, h2⟩
    choose a ha ha' using h1
    have e : ((HA.mat _ σ J u).1 - 1) * adMat F X = adMat F X * Matrix.of (fun j i => a i j) := by
      ext k i
      exact congrFun (ha' i) k
    refine ⟨1 + Matrix.of (fun j i => a i j), fun i j hij => ?_, fun i => ?_, ?_, h2⟩
    · have hij' : j < i := hij
      simp [ha j i hij'.le, hij'.ne']
    · simp [ha i i le_rfl]
    · rw [Matrix.mul_add, Matrix.mul_one, ← e, Matrix.sub_mul, Matrix.one_mul]
      exact (add_sub_cancel _ _).symm

theorem closure_radSet_subset (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {X : Matrix (Fin n) (Fin r) E}
    (hC : LinearIndependent E Xᵀ) (h0 : cT (σ : E →+* E) X * J * X = 0) {g : HA (AF F) σ J}
    (hg : g ∈ Subgroup.closure (radSet σ J X Fin.val)) : g ∈ radSet σ J X Fin.val := by
  obtain ⟨L, hL, hLL⟩ := exists_dual hσ hJ X hC h0
  have hd : ∀ j : Fin r, (j : ℕ) < r := fun j => j.2
  have he := idem_complete hσ hJ X L hL h0 hLL
  have hs := fam_st (adj_mul hσ hJ) (adj_adj hσ hJ) (idem (F := F) X L) (Fin.val : Fin r → ℕ) r
  have h1 := GlobalTheory.TwoStepUnipotent.st_one (adj_mul hσ hJ) (adj_adj hσ hJ)
  rw [mem_radSet_iff hσ hJ X L hL h0 hLL hd]
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact (mem_radSet_iff hσ hJ X L hL h0 hLL hd x).1 hx
  | one => exact (sub_self (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).symm ▸ zero_mem _
  | mul x y _ _ hx hy =>
    have e : (HA.mat _ σ J (x * y)).1 = (HA.mat _ σ J x).1 * (HA.mat _ σ J y).1 := rfl
    rw [e]
    generalize (HA.mat _ σ J x).1 = a at hx ⊢
    generalize (HA.mat _ σ J y).1 = b at hy ⊢
    have : a * b - 1 = (a - 1) * (b - 1) + (a - 1) + (b - 1) := by noncomm_ring
    rw [this]
    exact add_mem (add_mem (raise_le 0 (raise_mul he 0 hx hy)) hx) hy
  | inv x _ hx =>
    have := raise_st (adj_mul hσ hJ) (adj_adj hσ hJ) hs 0 hx
    rwa [map_sub, adj_mat hσ hJ, h1] at this

theorem linearIndependent_of_isWittFrame (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J)
    {X Y : Matrix (Fin n) (Fin r) E} (hW : IsWittFrame σ J X Y) : LinearIndependent E Xᵀ := by
  have e : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT' hσ hJ, cT_gram hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  refine Matrix.mulVec_injective_iff.1 fun v w h => ?_
  have := congrArg ((cT (σ : E →+* E) Y * J) *ᵥ ·) h
  simpa only [Matrix.mulVec_mulVec, e, Matrix.one_mulVec] using this

theorem unipMin_cocompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ C : Set (GAd σ J), IsCompact C ∧ ∀ u ∈ unipMin σ J X, ∃ δ ∈ ratPts σ J, δ ∈ unipMin σ J X ∧ ∃ c ∈ C, c ∈ unipMin σ J X ∧ u = δ * c := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  have hσ := sigma_sigma h
  have hC := linearIndependent_of_isWittFrame hσ hJ hW
  obtain ⟨K, hK, hcov⟩ := closure_radSet_cocompact hσ hJ X hC hW.xx Fin.val
  have hsub : ∀ g : Subgroup.closure (radSet σ J X Fin.val), g.1 ∈ unipMin σ J X := fun g => by
    rw [unipMin_eq_radSet]
    exact closure_radSet_subset hσ hJ hC hW.xx g.2
  refine ⟨Subtype.val '' K, hK.image continuous_subtype_val, fun u hu => ?_⟩
  rw [unipMin_eq_radSet] at hu
  obtain ⟨γ, hγ, k, hk, e⟩ := hcov ⟨u, Subgroup.subset_closure hu⟩
  exact ⟨γ.1, hγ, hsub γ, k.1, ⟨k, hk, rfl⟩, hsub k, congrArg Subtype.val e⟩

end GlobalTheory.CompanionTheory.UnipCocompact
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBridgeLubinTateField
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem eq_one_of_pow_eq_one_of_valuation_sub_lt {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {m : ℕ} {ξ : K}
    (hm : v (m : K) = 1) (hξ : ξ ^ m = 1) (h : v (ξ - 1) < 1) : ξ = 1 := by
  have hv : v ξ ≤ 1 := by
    have e : ξ = (ξ - 1) + 1 := by ring
    rw [e]
    exact (v.map_add _ _).trans (max_le h.le (by simp))
  have hp : ∀ i : ℕ, v (ξ ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : ξ ^ (i + 1) - 1 = ξ * (ξ ^ i - 1) + (ξ - 1) := by ring
      rw [e]
      refine Valuation.map_add_lt v ?_ h
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hv) ih
  have hs : v ((∑ i ∈ Finset.range m, ξ ^ i) - (m : K)) < 1 := by
    have e : (∑ i ∈ Finset.range m, ξ ^ i) - (m : K) = ∑ i ∈ Finset.range m, (ξ ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [e]
    exact Valuation.map_sum_lt v one_ne_zero fun i _ => hp i
  have hsum : (∑ i ∈ Finset.range m, ξ ^ i) ≠ 0 := by
    intro h0
    rw [h0, zero_sub, Valuation.map_neg, hm] at hs
    exact lt_irrefl _ hs
  have := mul_geom_sum ξ m
  rw [hξ, sub_self] at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hsum)

theorem natCast_residue_eq_zero {l : ℕ} [Fact l.Prime] {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra F (Om l)]
    [ValuativeExtension F (Om l)] : (l : 𝓀[F]) = 0 := by
  have hnl : ¬ ((1 : F) ≤ᵥ (l : F)) := by
    intro h
    have h2 := (ValuativeExtension.vle_iff_vle (A := F) (B := Om l) 1 (l : F)).2 h
    rw [map_one, map_natCast, GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le, norm_one,
      ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends] at h2
    exact absurd (Padic.norm_natCast_lt_one_iff.mpr (dvd_refl l)) (not_lt.mpr h2)
  have hlt : valuation F (((l : 𝒪[F]) : 𝒪[F]) : F) < 1 := by
    refine not_le.mp fun h => hnl ?_
    rw [Valuation.Compatible.vle_iff_le (v := valuation F), map_one]
    simpa using h
  have hmem : (l : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one]
    exact ne_of_lt hlt
  rw [← map_natCast (IsLocalRing.residue 𝒪[F]), IsLocalRing.residue_eq_zero_iff]
  exact hmem

theorem unramifiedDegree_eq_one_of_mem_inertia : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O), GlobalTheory.Pst.Induces Bw →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [IsSepClosure F (Om l)]
    (σ : ↥(Dec (F := E) A)), (σ : G E Ω) ∈ Ine (F := E) A → ∀ g : Om l ≃ₐ[F] Om l,
    (∀ y, g y = ((Bw.e σ : ↥(GK Bw.Kw)) : GQ l) y) → unramifiedDegree F (Om l) g = 1 := by
  intro l _ E Ω _ _ _ _ _ A O _ _ _ Bw hj F _ _ _ _ _ _ _ σ hσ g hg
  rw [GroundTheory.LocalField.unramifiedDegree_eq_one_iff]
  intro ζ hζ
  obtain ⟨m, hm, hζm⟩ := mem_unramifiedRoots_iff.1 hζ
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hcop : ¬ l ∣ m := by
    rintro ⟨k, rfl⟩
    apply hm
    rw [Nat.cast_mul, natCast_residue_eq_zero (l := l) (F := F), zero_mul]
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero m := ⟨hm0⟩
  have : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm0⟩
  obtain ⟨ζ₀, h₀⟩ : ∃ z : Ω, IsPrimitiveRoot z m := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hj0 := h₀.map_of_injective Bw.j.injective
  obtain ⟨i, -, hi⟩ := hj0.eq_pow_of_pow_eq_one hζm

  obtain ⟨z, hz, hzm⟩ : ∃ z : Ω, Bw.j z = ζ ∧ z ^ m = 1 :=
    ⟨ζ₀ ^ i, by rw [map_pow, hi], by rw [← pow_mul, mul_comm, pow_mul, h₀.pow_eq_one, one_pow]⟩
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp [hm0] at hzm
  let s : G E Ω := (σ : G E Ω)
  have hgz : g ζ = Bw.j (s z) := by
    rw [hg, ← hz]
    exact Bw.e_comm σ z
  have hnorm : ‖Bw.j z‖ = 1 := by
    refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm0).mp ?_
    rw [← norm_pow, ← map_pow, hzm, map_one, norm_one]
  have hzA : A.valuation z ≤ 1 := by
    rw [A.valuation_le_one_iff]
    exact (hj z).mpr hnorm.le
  have hzunit : A.valuation z = 1 :=
    le_antisymm hzA (not_lt.mp fun h => ((hj.valuation_lt_one_iff z).mp h).ne hnorm)
  have hlt : A.valuation (s z - z) < 1 := hσ.2 z hzA
  have hmn : ‖Bw.j (m : Ω)‖ = 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Om l)), PadicAlgCl.norm_extends,
      Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hcop
  have hmv : A.valuation (m : Ω) = 1 := by
    refine le_antisymm ?_ (not_lt.mp fun h => ((hj.valuation_lt_one_iff _).mp h).ne hmn)
    rw [A.valuation_le_one_iff]
    exact (hj _).mpr hmn.le
  have hsz : (s z / z) ^ m = 1 := by
    rw [div_pow, ← map_pow, hzm, map_one, div_one]
  have hone : s z / z = 1 := by
    refine eq_one_of_pow_eq_one_of_valuation_sub_lt A.valuation hmv hsz ?_
    have e : s z / z - 1 = (s z - z) / z := by field_simp
    rw [e, map_div₀, hzunit, div_one]
    exact hlt
  rw [hgz, (div_eq_one_iff_eq hz0).mp hone, hz]

end GlobalTheory.CompanionTheory.LTLink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTHodge.CompletionRange

theorem isClosed_finExt {l : ℕ} [Fact l.Prime] (K : FinExt l) : IsClosed (K.1 : Set (Om l)) := by
  haveI : FiniteDimensional ℚ_[l] K.1.toSubmodule := K.2
  exact Submodule.closed_of_finiteDimensional K.1.toSubmodule

theorem valued_le_one_of_norm_le_one {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ)
    (x : w.adicCompletion E) (hx : ‖φ x‖ ≤ 1) : Valued.v x ≤ 1 := by
  by_contra hv
  have hv' : 1 < Valued.v x := not_le.1 hv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hv'
  have hy : Valued.v x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hv'
  have ht : Filter.Tendsto (fun n : ℕ => x⁻¹ ^ n) Filter.atTop (nhds 0) :=
    Valued.tendsto_zero_pow_of_v_lt_one hy
  have ht' : Filter.Tendsto (fun n : ℕ => φ (x⁻¹ ^ n)) Filter.atTop (nhds 0) := by
    have h := (hφ.tendsto 0).comp ht
    rw [map_zero] at h
    exact h
  have hge : ∀ n : ℕ, 1 ≤ ‖φ (x⁻¹ ^ n)‖ := fun n => by
    have hφ0 : φ x ≠ 0 := (map_ne_zero φ).2 hx0
    rw [map_pow, map_inv₀, norm_pow, norm_inv]
    exact one_le_pow₀ ((one_le_inv₀ (norm_pos_iff.2 hφ0)).2 hx)
  have hn := ht'.norm
  rw [norm_zero] at hn
  have := ge_of_tendsto' hn hge
  linarith

theorem isClosed_image_integers {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l) (hφ : Continuous φ) :
    IsClosed (φ '' (w.adicCompletionIntegers E : Set (w.adicCompletion E))) := by
  have hc : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace (w.adicCompletionIntegers E)))
  exact (hc.image hφ).isClosed

theorem range_eq_Kw : ∀ {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
    (w : HeightOneSpectrum (𝓞 E)) (φ : w.adicCompletion E →+* Om l), Continuous φ →
    (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) →
    Set.range φ = (Bw.Kw.1 : Set (Om l)) := by
  intro l _ E Ω _ _ _ _ Gw O _ _ _ Bw w φ hφ hE
  have hcl := isClosed_finExt Bw.Kw

  have key : ∀ k ∈ (Bw.Kw.1 : Set (Om l)), ‖k‖ ≤ 1 → k ∈ Set.range φ := by
    intro k hk hk1
    have hden : k ∈ closure (Set.range φ) := by
      refine closure_mono ?_ (Bw.j_dense hk)
      rintro _ ⟨y, rfl⟩
      exact ⟨algebraMap E _ y, hE y⟩
    have hS : IsOpen (Metric.closedBall (0 : Om l) 1) :=
      IsUltrametricDist.isOpen_closedBall _ one_ne_zero
    have hk' : k ∈ Metric.closedBall (0 : Om l) 1 := by simpa using hk1
    have h2 : k ∈ closure (Metric.closedBall (0 : Om l) 1 ∩ Set.range φ) :=
      hS.inter_closure ⟨hk', hden⟩
    have h3 : Metric.closedBall (0 : Om l) 1 ∩ Set.range φ ⊆
        φ '' (w.adicCompletionIntegers E : Set (w.adicCompletion E)) := by
      rintro _ ⟨hb, x, rfl⟩
      refine ⟨x, ?_, rfl⟩
      exact valued_le_one_of_norm_le_one w φ hφ x (by simpa using hb)
    have h4 := closure_minimal h3 (isClosed_image_integers w φ hφ) h2
    obtain ⟨x, -, rfl⟩ := h4
    exact ⟨x, rfl⟩
  refine Set.Subset.antisymm ?_ fun k hk => ?_
  · rintro _ ⟨x, rfl⟩
    refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on
      (p := fun x => φ x ∈ (Bw.Kw.1 : Set (Om l))) x (hcl.preimage hφ) fun y => ?_
    rw [hE y]
    exact Bw.j_E y
  · rcases le_total ‖k‖ 1 with h | h
    · exact key k hk h
    · have hinv : k⁻¹ ∈ (Bw.Kw.1 : Set (Om l)) := inv_mem hk
      obtain ⟨a, ha⟩ := key k⁻¹ hinv (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h)
      exact ⟨a⁻¹, by rw [map_inv₀, ha, inv_inv]⟩

end GlobalTheory.CompanionTheory.LTHodge.CompletionRange
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalArtinCompatible
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

open GroundTheory.Global GroundTheory.Global.SemiLocal in

theorem local_restriction_abelianization_artin : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) {Ωv : Type} [Field Ωv] [Algebra (w.adicCompletion E) Ωv]
    [IsSepClosure (w.adicCompletion E) Ωv] (j : Ω →+* Ωv),
    (∀ y : E, j (algebraMap E Ω y) = algebraMap (w.adicCompletion E) Ωv (algebraMap E (w.adicCompletion E) y)) →
    ∀ (a : (w.adicCompletion E)ˣ) (σ : G E Ω) (g : Ωv ≃ₐ[w.adicCompletion E] Ωv),
    (∀ x : Ω, g (j x) = j (σ x)) →
    (∀ (y : Ωv) (hy : y ∈ maximalAbelianExtension (w.adicCompletion E) Ωv),
      ((localArtinMap (w.adicCompletion E) Ωv a ⟨y, hy⟩ : maximalAbelianExtension (w.adicCompletion E) Ωv) : Ωv) = g y) →
    ∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
    PositivityTheory.FamInh.res L (toAb E Ω σ) = PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) := by
  intro E Ω _ _ _ _ _ w Ωv _ _ _ j hj a σ g hgj hloc L _ _
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  obtain ⟨w'⟩ := GroundTheory.Global.IdeleGroup.nonempty_placesOver_of_finite (K := E) (L := L) w
  haveI : IsSepClosed Ωv := IsSepClosure.sep_closed (w.adicCompletion E)
  haveI : CharZero (w.adicCompletion E) := algebraRat.charZero _
  haveI : Algebra.IsSeparable (w.adicCompletion E) (w'.1.adicCompletion L) := inferInstance
  let ι : w'.1.adicCompletion L →ₐ[w.adicCompletion E] Ωv := IsSepClosed.lift
  set s := restrictAb L (le_maximalAbelianExtension L)
    (artinMap E Ω (GroundTheory.Global.IdeleClassGroup.mk E (IdeleGroup.finiteEmbedding w a))) with hs
  have hres : PositivityTheory.FamInh.res L (PositivityTheory.FamInh.art0 E Ω (localIdele E w a)) = s :=
    congrArg (restrictAb L (le_maximalAbelianExtension L))
      ((topologicalAbelianizationEquiv E Ω).apply_symm_apply _)
  have h1 : ∀ l : L, ι (algebraMap L (w'.1.adicCompletion L) (s l)) =
      g (ι (algebraMap L (w'.1.adicCompletion L) l)) := fun l => by
    rw [hs, artinMap_finiteEmbedding_apply L w w' ι a l]
    exact hloc _ _
  rw [hres, PositivityTheory.FamInh.res_toAb]
  letI : Algebra E Ωv := ((algebraMap (w.adicCompletion E) Ωv).comp (algebraMap E (w.adicCompletion E))).toAlgebra
  let m₂ : L →ₐ[E] Ωv :=
    { toRingHom := j.comp (algebraMap L Ω)
      commutes' := fun y => by
        show j (algebraMap L Ω (algebraMap E L y)) = _
        rw [← IsScalarTower.algebraMap_apply]
        exact hj y }
  have hcomp : ∀ y : E, algebraMap L (w'.1.adicCompletion L) (algebraMap E L y) =
      algebraMap (w.adicCompletion E) (w'.1.adicCompletion L) (algebraMap E (w.adicCompletion E) y) := by
    intro y
    rw [← IsScalarTower.algebraMap_apply E L (w'.1.adicCompletion L),
      ← IsScalarTower.algebraMap_apply E (w.adicCompletion E) (w'.1.adicCompletion L)]
  let m₁ : L →ₐ[E] Ωv :=
    { toRingHom := (ι : w'.1.adicCompletion L →+* Ωv).comp (algebraMap L (w'.1.adicCompletion L))
      commutes' := fun y => by
        show ι (algebraMap L (w'.1.adicCompletion L) (algebraMap E L y)) = _
        rw [hcomp, ι.commutes]
        rfl }
  letI : Algebra L Ωv := m₂.toRingHom.toAlgebra
  haveI : IsScalarTower E L Ωv := IsScalarTower.of_algebraMap_eq fun y => (m₂.commutes y).symm
  let τ : L ≃ₐ[E] L := Normal.algHomEquivAut E Ωv L m₁
  have hτ : ∀ l : L, m₂ (τ l) = m₁ l := fun l =>
    DFunLike.congr_fun ((Normal.algHomEquivAut E Ωv L).symm_apply_apply m₁) l
  have h2 : ∀ l : L, τ (s l) = AlgEquiv.restrictNormalHom L σ (τ l) := fun l => by
    apply m₂.toRingHom.injective
    show m₂ (τ (s l)) = j (algebraMap L Ω (AlgEquiv.restrictNormalHom L σ (τ l)))
    have hρ : algebraMap L Ω (AlgEquiv.restrictNormalHom L σ (τ l)) = σ (algebraMap L Ω (τ l)) :=
      AlgEquiv.restrictNormal_commutes σ L (τ l)
    rw [hρ, ← hgj, hτ]
    have hj₂ : j (algebraMap L Ω (τ l)) = m₁ l := hτ l
    rw [hj₂]
    exact h1 l
  have h3 : τ * s = AlgEquiv.restrictNormalHom L σ * τ := AlgEquiv.ext h2
  have h4 : τ * s = τ * AlgEquiv.restrictNormalHom L σ := by
    rw [h3]
    exact IsMulCommutative.is_comm.comm _ _
  exact (mul_left_cancel h4).symm

end GlobalTheory.CompanionTheory.LTLink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantFiniteBallSum
section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi

namespace GlobalTheory.CompanionTheory.MirFourier

theorem exists_finset_eq_sum_polyBall_translates :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] (φ : (Fin n → k) → E) (s S : kˣ), (∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → φ (v + a) = φ v) → (∀ v : Fin n → k, φ v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) → ∃ R : Finset (Fin n → k), ∀ v : Fin n → k, φ v = ∑ x ∈ R, @ite _ (Multiplicative.ofAdd (v - x) ∈ polyBall (k := k) n s) (Classical.propDecidable _) (φ x) 0 := by
  intro k _ _ _ _ n E _ _ φ s S hinv hsupp
  classical
  set L := polyBall (k := k) n s with hL
  let q : Multiplicative (Fin n → k) → Multiplicative (Fin n → k) ⧸ L := QuotientGroup.mk
  have hopen : IsOpen (L : Set (Multiplicative (Fin n → k))) := isOpen_polyBall n s
  have hcov : ∃ T : Finset (Multiplicative (Fin n → k)),
      ((polyBall (k := k) n S : Subgroup _) : Set (Multiplicative (Fin n → k))) ⊆
        ⋃ x ∈ T, (fun y => x * y) '' (L : Set (Multiplicative (Fin n → k))) := by
    refine (isCompact_polyBall n S).elim_finite_subcover
      (fun x : Multiplicative (Fin n → k) => (fun y => x * y) '' (L : Set (Multiplicative (Fin n → k))))
      (fun x => (Homeomorph.mulLeft x).isOpenMap _ hopen) ?_ |>.imp fun T hT => ?_
    · intro x _
      exact Set.mem_iUnion.2 ⟨x, 1, L.one_mem, by simp⟩
    · simpa using hT
  obtain ⟨T, hT⟩ := hcov
  let f : Multiplicative (Fin n → k) ⧸ L → (Fin n → k) := fun c => (Quotient.out c).toAdd
  have hf : Function.Injective f := fun a b hab =>
    Quotient.out_injective (Multiplicative.toAdd.injective hab)
  have hmem : ∀ (v : Fin n → k) (c : Multiplicative (Fin n → k) ⧸ L),
      Multiplicative.ofAdd (v - f c) ∈ L ↔ q (Multiplicative.ofAdd v) = c := by
    intro v c
    have hc : q (Quotient.out c) = c := QuotientGroup.out_eq' c
    have hinvEq : Multiplicative.ofAdd (v - f c) =
        ((Multiplicative.ofAdd v)⁻¹ * Quotient.out c)⁻¹ := by
      apply Multiplicative.toAdd.injective
      simp [f, sub_eq_add_neg, add_comm]
    rw [hinvEq, L.inv_mem_iff, ← QuotientGroup.eq]
    exact (by rw [hc] : q (Multiplicative.ofAdd v) = q (Quotient.out c) ↔ _)
  have hval : ∀ v : Fin n → k, φ (f (q (Multiplicative.ofAdd v))) = φ v := by
    intro v
    have h := hinv (f (q (Multiplicative.ofAdd v))) (v - f (q (Multiplicative.ofAdd v)))
      ((hmem v _).2 rfl)
    rw [add_sub_cancel] at h
    exact h.symm
  refine ⟨(T.image q).image f, fun v => ?_⟩
  rw [Finset.sum_image (fun a _ b _ h => hf h)]
  by_cases hv : q (Multiplicative.ofAdd v) ∈ T.image q
  · rw [Finset.sum_eq_single_of_mem _ hv
      (fun b _ hb => if_neg (fun h => hb ((hmem v b).1 h).symm)),
      if_pos ((hmem v _).2 rfl), hval]
  · have h0 : φ v = 0 := by
      by_contra hne
      obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hT (hsupp v hne))
      refine hv (Finset.mem_image.2 ⟨x, hx, ?_⟩)
      have hxv : x⁻¹ * Multiplicative.ofAdd v ∈ L := by
        rw [← hxy]
        simpa using hy
      exact QuotientGroup.eq.2 hxv
    rw [h0]
    refine (Finset.sum_eq_zero fun b hb => if_neg fun h => hv ?_).symm
    rw [(hmem v b).1 h]
    exact hb

end GlobalTheory.CompanionTheory.MirFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramifiedStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_infinite_place_of_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → Nontrivial (InfinitePlace E) := by
  first | exact @GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace | exact GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace | (intros; apply GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMultiplicityTopCycleStatement
section
open GlobalTheory.CompanionTheory.PairMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_multiplicity_top_cycle : GlobalTheory.CompanionTheory.PairMult.TopCyc := by
  first | exact @GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc | exact GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc | (intros; apply GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc <;> assumption)
end

