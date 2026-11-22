import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0079
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0193
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerOfNormEq
section
open Filter
open scoped InnerProductSpace Topology

namespace GlobalTheory.ClosableSchur

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma inner_of_norm_eq (R : H →L[ℂ] H) (hR : ∀ v, ‖R v‖ = ‖v‖) (v w : H) :
    ⟪R v, R w⟫_ℂ = ⟪v, w⟫_ℂ := by
  have h := (LinearMap.norm_map_iff_inner_map_map R).mp hR
  exact h v w

private lemma exists_isometry_extension_of_dense_of_norm_eq {K : Type} [NormedAddCommGroup K] [NormedSpace ℂ K] [CompleteSpace K]
    (V : Submodule ℂ K) (hV : Dense (V : Set K)) (u : V →ₗ[ℂ] K) (hu : ∀ v, ‖u v‖ = ‖v‖) :
    ∃ U : K →L[ℂ] K, (∀ v : V, U v = u v) ∧ ∀ γ, ‖U γ‖ = ‖γ‖ := by
  let uc : V →L[ℂ] K := u.mkContinuous 1 (fun v => by rw [hu, one_mul])
  have hd : DenseRange V.subtypeL := by
    have hr : Set.range (V.subtypeL : V → K) = (V : Set K) := by
      ext x
      simp
    rw [DenseRange, hr]
    exact hV
  have hi : IsUniformInducing V.subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
  have heq : ∀ v : V, uc.extend V.subtypeL v = u v := fun v => by
    have := ContinuousLinearMap.extend_eq uc hd hi v
    simpa [uc] using this
  refine ⟨uc.extend V.subtypeL, heq, fun γ => ?_⟩
  have hfun := hd.equalizer (g := fun γ => ‖uc.extend V.subtypeL γ‖) (h := fun γ => ‖γ‖)
    (continuous_norm.comp (ContinuousLinearMap.continuous _)) continuous_norm
    (funext fun v => by
      simp only [Function.comp_apply]
      rw [ContinuousLinearMap.extend_eq uc hd hi v]
      simp [uc, hu])
  exact congr_fun hfun γ

lemma abstract {ι K : Type} [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H) (hn : ∀ i v, ‖ρ i v‖ = ‖v‖)
    (hinv : ∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤)
    (hD : ∀ i, ∀ v ∈ D, ρ i v ∈ D) (J : K →L[ℂ] H) (hJ : Function.Injective J) (s : D → K)
    (hs : DenseRange s) (hJs : ∀ w, J (s w) = w)
    (hsn : ∀ i (w : D), ‖s ⟨ρ i w, hD i w w.2⟩‖ = ‖s w‖) :
    ∃ c : ℝ, ∀ γ : K, ‖J γ‖ ^ 2 = c * ‖γ‖ ^ 2 := by
  classical
  have hadd : ∀ a b : D, s (a + b) = s a + s b := fun a b =>
    hJ (by rw [map_add, hJs, hJs, hJs, Submodule.coe_add])
  have hsmul : ∀ (c : ℂ) (a : D), s (c • a) = c • s a := fun c a =>
    hJ (by rw [map_smul, hJs, hJs, Submodule.coe_smul])
  let sl : D →ₗ[ℂ] K := { toFun := s, map_add' := hadd, map_smul' := hsmul }
  have hinj : Function.Injective sl := fun a b hab => by
    apply Subtype.ext
    rw [← hJs a, ← hJs b]
    exact congrArg J hab
  let e := LinearEquiv.ofInjective sl hinj
  have he : ∀ w : D, e.symm ⟨s w, LinearMap.mem_range_self sl w⟩ = w := fun w => by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    simp [e, sl]
  have hVd : Dense ((LinearMap.range sl : Submodule ℂ K) : Set K) := by
    rw [LinearMap.coe_range]
    exact hs
  have hU : ∀ i, ∃ U : K →L[ℂ] K, (∀ w : D, U (s w) = s ⟨ρ i w, hD i w w.2⟩) ∧
      ∀ γ, ‖U γ‖ = ‖γ‖ := by
    intro i
    let r : D →ₗ[ℂ] D := (ρ i).toLinearMap.restrict (fun x hx => hD i x hx)
    let u : LinearMap.range sl →ₗ[ℂ] K := sl ∘ₗ r ∘ₗ e.symm.toLinearMap
    have hu : ∀ w : D, u ⟨s w, LinearMap.mem_range_self sl w⟩ = s ⟨ρ i w, hD i w w.2⟩ :=
      fun w => by
        simp only [u, LinearMap.comp_apply, LinearEquiv.coe_coe, he]
        rfl
    obtain ⟨U, hUeq, hUn⟩ := exists_isometry_extension_of_dense_of_norm_eq _ hVd u (fun v => by
      obtain ⟨w, hw⟩ := LinearMap.mem_range.mp v.2
      have hv : v = ⟨s w, LinearMap.mem_range_self sl w⟩ := Subtype.ext hw.symm
      rw [hv, hu, hsn]
      rfl)
    refine ⟨U, fun w => ?_, hUn⟩
    have := hUeq ⟨s w, LinearMap.mem_range_self sl w⟩
    rw [hu] at this
    exact this
  choose U hUs hUn using hU
  have hUinv : ∀ i j, (∀ v, ρ i (ρ j v) = v) → ∀ γ, U i (U j γ) = γ := by
    intro i j hij γ
    have := hs.equalizer (g := fun γ => U i (U j γ)) (h := id)
      ((U i).continuous.comp (U j).continuous) continuous_id (funext fun w => by
        simp only [Function.comp_apply, id]
        rw [hUs j w, hUs i]
        congr 1
        exact Subtype.ext (hij w))
    exact congr_fun this γ
  have hJU : ∀ i γ, J (U i γ) = ρ i (J γ) := by
    intro i γ
    have := hs.equalizer (g := fun γ => J (U i γ)) (h := fun γ => ρ i (J γ))
      (J.continuous.comp (U i).continuous) ((ρ i).continuous.comp J.continuous)
      (funext fun w => by
        simp only [Function.comp_apply]
        rw [hUs i w, hJs, hJs])
    exact congr_fun this γ
  have hadj : ∀ i x, ContinuousLinearMap.adjoint J (ρ i x) = U i (ContinuousLinearMap.adjoint J x) := by
    intro i x
    obtain ⟨j, _, hij⟩ := hinv i
    apply ext_inner_right ℂ
    intro γ
    rw [ContinuousLinearMap.adjoint_inner_left]
    conv_rhs => rw [← hUinv i j hij γ]
    rw [inner_of_norm_eq (U i) (hUn i) (ContinuousLinearMap.adjoint J x) (U j γ),
      ContinuousLinearMap.adjoint_inner_left, hJU j,
      ← inner_of_norm_eq (ρ i) (hn i) x (ρ j (J γ)), hij]
  have hadjρ : ∀ i, ∃ i', ρ i' = ContinuousLinearMap.adjoint (ρ i) := by
    intro i
    obtain ⟨j, _, hij⟩ := hinv i
    refine ⟨j, ?_⟩
    ext v
    apply ext_inner_right ℂ
    intro w
    rw [ContinuousLinearMap.adjoint_inner_left, ← inner_of_norm_eq (ρ i) (hn i) (ρ j v) w, hij]
  let T : H →L[ℂ] H := J ∘L ContinuousLinearMap.adjoint J
  have hcomm : ∀ i, T ∘L ρ i = ρ i ∘L T := by
    intro i
    ext x
    simp only [T, ContinuousLinearMap.comp_apply]
    rw [hadj, hJU]
  obtain ⟨c, hc⟩ := hilbert_schur_of_adjoint_closed ι H ρ hadjρ hirr T hcomm
  have hJJ : ∀ γ, ContinuousLinearMap.adjoint J (J γ) = c • γ := by
    intro γ
    apply hJ
    have := congrArg (fun T' : H →L[ℂ] H => T' (J γ)) hc
    simp only [T, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply] at this
    rw [this, map_smul]
  refine ⟨c.re, fun γ => ?_⟩
  have h1 : (⟪γ, γ⟫_ℂ).re = ‖γ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) γ
  have h2 : (⟪γ, γ⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) γ
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (J γ), ← ContinuousLinearMap.adjoint_inner_left J γ (J γ), hJJ,
    inner_smul_left, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re, Complex.conj_im, h1, h2]
  ring

theorem norm_sq_eq : ∀ (ι H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H), (∀ i v, ‖ρ i v‖ = ‖v‖) → (∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i, ∀ v ∈ D, ρ i v ∈ D) → ∀ A : H →ₗ[ℂ] E, (∀ i, ∀ w ∈ D, ‖A (ρ i w)‖ = ‖A w‖) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) → ∃ c : ℝ, ∀ w ∈ D, ‖A w‖ ^ 2 = c * ‖w‖ ^ 2 := by
  intro ι H E _ _ _ _ _ _ ρ D hn hinv hirr hD A hA hcl
  classical
  let g : D →ₗ[ℂ] WithLp 2 (H × E) :=
    (WithLp.linearEquiv 2 ℂ (H × E)).symm.toLinearMap ∘ₗ (D.subtype.prod (A ∘ₗ D.subtype))
  have hg : ∀ w : D, g w = WithLp.toLp 2 ((w : H), A w) := fun w => rfl
  let G : Submodule ℂ (WithLp 2 (H × E)) := LinearMap.range g
  let K : Submodule ℂ (WithLp 2 (H × E)) := G.topologicalClosure
  have : CompleteSpace K := G.isClosed_topologicalClosure.completeSpace_coe
  let J : K →L[ℂ] H := (WithLp.fstL 2 ℂ H E) ∘L K.subtypeL
  have hJapp : ∀ γ : K, J γ = (γ : WithLp 2 (H × E)).fst := fun γ => rfl
  let s : D → K := fun w => ⟨g w, G.le_topologicalClosure (LinearMap.mem_range_self g w)⟩
  have hJs : ∀ w, J (s w) = w := fun w => rfl
  have hns : ∀ x : D, ‖s x‖ ^ 2 = ‖(x : H)‖ ^ 2 + ‖A x‖ ^ 2 := fun x =>
    WithLp.prod_norm_sq_eq_of_L2 (g x)
  have hsn : ∀ i (w : D), ‖s ⟨ρ i w, hD i w w.2⟩‖ = ‖s w‖ := by
    intro i w
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hns, hns]
    show ‖ρ i w‖ ^ 2 + ‖A (ρ i w)‖ ^ 2 = _
    rw [hn, hA i w w.2]
  have hs : DenseRange s := by
    rw [Metric.denseRange_iff]
    intro γ ε hε
    have hmem : (γ : WithLp 2 (H × E)) ∈ closure (G : Set (WithLp 2 (H × E))) := by
      rw [← Submodule.topologicalClosure_coe]
      exact γ.2
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp hmem ε hε
    obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hb
    exact ⟨w, hd⟩
  have hJ : Function.Injective J := by
    rw [injective_iff_map_eq_zero]
    intro γ hγ
    have hmem : (γ : WithLp 2 (H × E)) ∈ closure (G : Set (WithLp 2 (H × E))) := by
      rw [← Submodule.topologicalClosure_coe]
      exact γ.2
    obtain ⟨x, hxG, hx⟩ := mem_closure_iff_seq_limit.mp hmem
    choose w hw using fun n => LinearMap.mem_range.mp (hxG n)
    have h1 : Tendsto (fun n => ((w n : D) : H)) atTop (𝓝 0) := by
      have := ((WithLp.fstL 2 ℂ H E).continuous.tendsto _).comp hx
      have h0 : (WithLp.fstL 2 ℂ H E) (γ : WithLp 2 (H × E)) = 0 := hγ
      rw [h0] at this
      refine this.congr (fun n => ?_)
      simp only [Function.comp_apply, ← hw n, hg]
      rfl
    have h2 : Tendsto (fun n => A ((w n : D) : H)) atTop (𝓝 (γ : WithLp 2 (H × E)).snd) := by
      have := ((WithLp.sndL 2 ℂ H E).continuous.tendsto _).comp hx
      refine this.congr (fun n => ?_)
      simp only [Function.comp_apply, ← hw n, hg]
      rfl
    have h3 := hcl (fun n => ((w n : D) : H)) _ (fun n => (w n).2) h1 h2
    have h4 : (γ : WithLp 2 (H × E)).fst = 0 := hγ
    apply Subtype.ext
    have h5 : ‖(γ : WithLp 2 (H × E))‖ ^ 2 = 0 := by
      rw [WithLp.prod_norm_sq_eq_of_L2, h3, h4]
      simp
    simpa using h5
  obtain ⟨c, hc⟩ := abstract (H := H) ρ D hn hinv hirr hD J hJ s hs hJs hsn
  refine ⟨(1 - c) / c, fun w hw => ?_⟩
  have h : ‖w‖ ^ 2 = c * (‖w‖ ^ 2 + ‖A w‖ ^ 2) := by
    have := hc (s ⟨w, hw⟩)
    rw [hJs, hns] at this
    exact this
  by_cases hc0 : c = 0
  · rw [hc0, zero_mul] at h
    have hw0 : w = 0 := by simpa using h
    subst hw0
    simp
  · rw [div_mul_eq_mul_div, eq_div_iff hc0]
    linear_combination (-1 : ℝ) * h

end GlobalTheory.ClosableSchur
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemZpowersOfTameGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.TameGenPowers
open scoped Pointwise

theorem wild_mem_Ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : Formalism.ConjugateSelfDual.G E Ω}
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) : σ ∈ Ine (F := E) A := by
  have hv : ∀ y : Ω, A.valuation (σ y) = A.valuation y := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    have h := A.valuation.map_one_add_of_lt (hσ y hy)
    rw [add_sub_cancel, map_div₀, div_eq_one_iff_eq (by simpa using hy)] at h
    exact h
  refine ⟨?_, fun x hx => ?_⟩
  · show σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def,
      ← A.valuation_le_one_iff, ← A.valuation_le_one_iff, ← hv, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    have e : σ x - x = (σ x / x - 1) * x := by field_simp
    rw [e, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) (hσ x hx0)

theorem finite_roots (K : Type) [Field K] (m : ℕ) (hm : m ≠ 0) :
    {u : Kˣ | u ^ m = 1}.Finite := by
  haveI : NeZero m := ⟨hm⟩
  have : Finite (rootsOfUnity m K) := inferInstance
  have h := Set.toFinite ((rootsOfUnity m K : Subgroup Kˣ) : Set Kˣ)
  exact h.subset fun u hu => (mem_rootsOfUnity m u).2 hu

theorem eq_one_of_wild_prime (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω)
    (hA : IsPlaceOver A v) (K : Type) [Field K] [TopologicalSpace K] [T2Space K]
    (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ) (hr : Continuous r) (l : ℕ) (hl : l.Prime)
    (hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (σ : Formalism.ConjugateSelfDual.G E Ω)
    (hσ : ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) (hσl : r σ ^ l = 1) : r σ = 1 := by
  have hvl : ¬ A.valuation (l : Ω) < 1 := by
    intro h
    apply hlv
    rw [← hA]
    simpa using h
  have hvl1 : A.valuation (l : Ω) = 1 :=
    le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A l)) (not_lt.mp hvl)
  have hfin : ({u : Kˣ | u ^ l = 1} \ {1}).Finite := (finite_roots K l hl.ne_zero).diff
  have hop : IsOpen (r ⁻¹' ({u : Kˣ | u ^ l = 1} \ {1})ᶜ) :=
    hfin.isClosed.isOpen_compl.preimage hr
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff E Ω _).mp
    (hop.mem_nhds (by simp))
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hidx : L.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  have hτ : σ ^ n ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro x hx
    refine GlobalTheory.WildInertiaChar.fixed_of_pow_fixed A (σ ^ n)
      (GlobalTheory.WildInertiaChar.wild_pow A σ hσ n) (l ^ a) ?_ x ?_
    · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
    · rw [← pow_mul, mul_comm]; exact hmem x hx
  have h1 : r σ ^ n = 1 := by
    have h2 : r (σ ^ n) ∉ ({u : Kˣ | u ^ l = 1} \ {1}) := hsub hτ
    by_contra hne
    apply h2
    refine ⟨?_, by rwa [map_pow]⟩
    show r (σ ^ n) ^ l = 1
    rw [map_pow, ← pow_mul, mul_comm, pow_mul, hσl, one_pow]
  have hc : Nat.Coprime l n := (Nat.Prime.coprime_iff_not_dvd hl).mpr hn
  have := (pow_gcd_eq_one (a := r σ) (m := l) (n := n)).mpr ⟨hσl, h1⟩
  rwa [hc, pow_one] at this

theorem mem_zpowers_of_tameGen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A v → ∀ (γ : Formalism.ConjugateSelfDual.G E Ω), TameGenAt A γ → ∀ (K : Type) [Field K] [TopologicalSpace K] [T2Space K] (r : Formalism.ConjugateSelfDual.G E Ω →* Kˣ), Continuous r → ∀ m : ℕ, ((m : ℕ) : 𝓞 E) ∉ v.asIdeal → (∀ σ ∈ Ine (F := E) A, r σ ^ m = 1) → ∀ σ ∈ Ine (F := E) A, r σ ∈ Subgroup.zpowers (r γ) := by
  intro E Ω _ _ _ _ _ v A hA γ hγ K _ _ _ r hr m hm hI σ hσ
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hw : ∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → r τ = 1 := by
    intro τ hτ
    by_contra hne
    have hd : orderOf (r τ) ∣ m := orderOf_dvd_of_pow_eq_one (hI τ (wild_mem_Ine hτ))
    have hne1 : orderOf (r τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
    have hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
      intro h
      apply hm
      obtain ⟨c, hc⟩ := hd
      rw [hc, hk]
      push_cast
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
    have h1 : r (τ ^ k) = 1 := by
      refine eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
        (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
      rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
    rw [map_pow] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    have ho : orderOf (r τ) ≠ 0 := fun h => hm0 (by simpa [h] using hd)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact ho (by simpa using hk)
    have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
    rw [hk] at h3
    have := hl.two_le
    have := Nat.pos_of_ne_zero hk0
    nlinarith
  have hfin : ((Subgroup.zpowers (r γ) : Subgroup Kˣ) : Set Kˣ).Finite := by
    refine (finite_roots K m hm0).subset ?_
    rintro u ⟨z, rfl⟩
    show (r γ ^ z) ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hI γ hγ.1, one_zpow]
  have hc : IsClosed (((Subgroup.zpowers (r γ)).comap r : Subgroup (Formalism.ConjugateSelfDual.G E Ω)) :
      Set (Formalism.ConjugateSelfDual.G E Ω)) := hfin.isClosed.preimage hr
  refine closure_minimal (SetLike.coe_subset_coe.2 ((Subgroup.closure_le _).2 ?_)) hc (hγ.2 hσ)
  rintro τ (rfl | hτ)
  · exact Subgroup.mem_zpowers _
  · show r τ ∈ Subgroup.zpowers (r γ)
    rw [hw τ hτ]
    exact one_mem _

end GlobalTheory.TameGenPowers
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowEqOneOfUnitary
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.L2.DIV

namespace GlobalTheory.MemberDetLaws

theorem exists_potential {G M X A : Type} [Group G] [CommGroup A] (act : G → M → M)
    (act_one : ∀ m, act 1 m = m) (act_mul : ∀ g h m, act (g * h) m = act g (act h m))
    (v : X → M) (χ : G →* A)
    (hχ : ∀ (x : X) (g : G), v x = act g (v x) → χ g = 1) :
    ∃ φ : X → A, ∀ (x y : X) (g : G), v y = act g (v x) → φ y = χ g * φ x := by
  classical
  let s : Setoid X :=
    { r := fun x y => ∃ g : G, v y = act g (v x)
      iseqv :=
        { refl := fun x => ⟨1, (act_one _).symm⟩
          symm := fun {x y} ⟨g, hg⟩ => ⟨g⁻¹, by rw [hg, ← act_mul, inv_mul_cancel, act_one]⟩
          trans := fun {x y z} ⟨g, hg⟩ ⟨h, hh⟩ => ⟨h * g, by rw [hh, hg, act_mul]⟩ } }
  have hb : ∀ x : X, ∃ g : G, v x = act g (v (Quotient.mk s x).out) := fun x =>
    Quotient.mk_out (s := s) x
  choose c hc using hb
  refine ⟨fun x => χ (c x), fun x y g hg => ?_⟩
  have hq : Quotient.mk s x = Quotient.mk s y := Quotient.sound ⟨g, hg⟩
  have hx := hc x
  have hy := hc y
  rw [← hq] at hy
  have h1 : χ ((c y)⁻¹ * (g * c x)) = 1 := by
    apply hχ (Quotient.mk s x).out
    rw [act_mul, act_mul, ← hx, ← hg, hy, ← act_mul, inv_mul_cancel, act_one]
  rw [map_mul, map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

theorem smulLat_one {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (1 : Matrix (Fin N) (Fin N) E) L = L := by
  unfold SDLat.smulLat
  rw [Matrix.toLin'_one]
  exact Submodule.map_id L

theorem smulLat_mul {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    (g h : Matrix (Fin N) (Fin N) E) (L : Submodule (𝓞 E) (Fin N → E)) :
    SDLat.smulLat (g * h) L = SDLat.smulLat g (SDLat.smulLat h L) := by
  unfold SDLat.smulLat
  rw [Matrix.toLin'_mul, ← Submodule.map_comp]
  rfl

def detU (E : Type) [Field E] [StarRing E] (N : ℕ) :
    Matrix.unitaryGroup (Fin N) E →* unitary E where
  toFun γ := ⟨(γ : Matrix (Fin N) (Fin N) E).det, Matrix.det_of_mem_unitary γ.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp)

noncomputable def invProd {E ι : Type} [Field E] [StarRing E] [Fintype ι] (σ : ι → E →+* ℂ) :
    unitary E →* ℂˣ :=
  ∏ i, ((Units.map (σ i : E →* ℂ)).comp Unitary.toUnits)⁻¹

theorem invProd_coe {E ι : Type} [Field E] [StarRing E] [Fintype ι] (σ : ι → E →+* ℂ)
    (z : unitary E) : ((invProd σ z : ℂˣ) : ℂ) = ∏ i, (σ i (z : E))⁻¹ := by
  unfold invProd
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  rfl

private theorem pow_eq_one_of_unitary {R : Ranks} (H : Formalism.BasicNotions.Host R) :
    letI := H.cmStar; ∀ z : H.E, z ∈ unitary H.E → IsIntegral ℤ z → ∃ m : ℕ, 0 < m ∧ z ^ m = 1 := by
  letI := H.cmStar
  intro z hu hz
  have := H.isCMField_hostE
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one H.E ℂ hz (fun φ => by
    have h1 : star z * z = 1 := hu.1
    have h2 : φ (star z) = starRingEnd ℂ (φ z) := IsCMField.complexEmbedding_complexConj H.E φ z
    have h3 := congrArg φ h1
    rw [map_mul, h2, map_one, Complex.conj_mul'] at h3
    have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4)
  exact ⟨n, hn, hp⟩

private theorem prod_emb_eq_one {R : Ranks} (H : Formalism.BasicNotions.Host R) [Fintype R.Psi] (x : H.E)
    (hx : ∃ m : ℕ, 0 < m ∧ x ^ m = 1) : ∏ τ : R.Psi, H.emb (τ : R.GG) x = 1 := by
  classical
  have := H.galois
  have : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ _ _
  have h := Algebra.norm_eq_prod_automorphisms H.K x
  rw [H.der.norm_mu x hx, map_one] at h
  have h2 := congrArg H.φ₀ h
  rw [map_one, map_prod] at h2
  rw [h2]
  symm
  have hmem : ∀ σ : H.E ≃ₐ[H.K] H.E, H.gal (σ.restrictScalars ℚ) ∈ R.Psi := fun σ =>
    (H.galE_mem_Psi_iff _).2 (σ.commutes ⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩)
  refine Fintype.prod_bijective (fun σ : H.E ≃ₐ[H.K] H.E => (⟨H.gal (σ.restrictScalars ℚ), hmem σ⟩ : R.Psi))
    ⟨fun σ τ hst => ?_, fun g => ?_⟩ _ _ fun σ => ?_
  · exact AlgEquiv.restrictScalars_injective ℚ (H.gal.injective (congrArg Subtype.val hst))
  · have hfix : H.gal.symm g.1 H.sqd = H.sqd :=
      (H.galE_mem_Psi_iff _).1 (by
        show H.gal (H.gal.symm g.1) ∈ _
        rw [MulEquiv.apply_symm_apply]; exact g.2)
    have hK : ∀ y : H.K, H.gal.symm g.1 (y : H.E) = y := by
      have hle : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers (H.gal.symm g.1)) := by
        refine IntermediateField.adjoin_simple_le_iff.2 ?_
        rw [IntermediateField.mem_fixedField_iff]
        intro f hf
        exact (Subgroup.zpowers_le.2
          (show H.gal.symm g.1 ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) H.sqd from hfix)) hf
      intro y
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle y.2) _ (Subgroup.mem_zpowers _)
    refine ⟨AlgEquiv.ofRingEquiv (f := (H.gal.symm g.1).toRingEquiv) hK, Subtype.ext ?_⟩
    exact H.gal.apply_symm_apply g.1
  · show H.φ₀ (σ x) = H.φ₀ (H.gal.symm (H.gal (σ.restrictScalars ℚ)) x)
    rw [MulEquiv.symm_apply_apply]
    rfl

theorem det_laws : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), letI := H.cmStar; ∃ (e1 : unitary H.E →* ℂˣ) (rel : ∀ N, SDLat H.E N → SDLat H.E N → ℂˣ ⧸ (⊥ : Subgroup ℂˣ)), (∀ z : unitary H.E, ((e1 z : ℂˣ) : ℂ) = ∏ᶠ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹) ∧ (∀ N L, rel N L L = 1) ∧ (∀ N L L' L'', rel N L L' * rel N L' L'' = rel N L L'') ∧ ∀ N (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E), L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → rel N L L' = QuotientGroup.mk (e1 ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩) := by
  intro R H
  letI := H.cmStar
  letI : Fintype (R.Psi) := Fintype.ofFinite _
  let e1 : unitary H.E →* ℂˣ := invProd fun τ : R.Psi => H.emb (τ : R.GG)
  have he1 : ∀ z : unitary H.E, ((e1 z : ℂˣ) : ℂ) =
      ∏ τ : R.Psi, (H.emb (τ : R.GG) (z : H.E))⁻¹ := invProd_coe _
  have hφ : ∀ N, ∃ φ : SDLat H.E N → ℂˣ,
      ∀ (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E),
        L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 →
          φ L' = (e1.comp (detU H.E N)) γ * φ L := by
    intro N
    refine exists_potential
      (fun (γ : Matrix.unitaryGroup (Fin N) H.E) L =>
        SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L)
      (fun m => smulLat_one m) (fun g h m => smulLat_mul _ _ m)
      (fun L : SDLat H.E N => L.1) _ ?_
    intro L γ hγ
    apply Units.ext
    rw [MonoidHom.comp_apply, he1]
    change ∏ τ : R.Psi, (H.emb (τ : R.GG) (γ : Matrix (Fin N) (Fin N) H.E).det)⁻¹ = 1
    rw [Finset.prod_inv_distrib, prod_emb_eq_one H _ (pow_eq_one_of_unitary H _
      (Matrix.det_of_mem_unitary γ.2)
      (GlobalTheory.Mem.StabDet.isIntegral_det L.1 L.2.1 L.2.2.1 _ fun v hv => ?_)), inv_one]
    rw [hγ]
    exact ⟨v, hv, by simp⟩
  choose φ hφ using hφ
  refine ⟨e1, fun N L L' => QuotientGroup.mk (φ N L' / φ N L), fun z => ?_, fun N L => ?_,
    fun N L L' L'' => ?_, fun N L L' γ hγ => ?_⟩
  · rw [he1, finprod_eq_prod_of_fintype]
  · simp
  · rw [← QuotientGroup.mk_mul, mul_comm, div_mul_div_cancel]
  · show QuotientGroup.mk (φ N L' / φ N L) = _
    rw [hφ N L L' γ hγ, mul_div_cancel_right]
    rfl

end GlobalTheory.MemberDetLaws
end

