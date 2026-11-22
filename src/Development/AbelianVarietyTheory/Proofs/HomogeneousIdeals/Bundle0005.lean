import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOpenPartialHomeomorphAnalytic
section
namespace GlobalTheory.AffinePoints

open Topology Filter Set MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

theorem analyticAt_aevalTower {σ ι : Type*} [Fintype σ] [Fintype ι]
    (q : MvPolynomial ι (MvPolynomial σ 𝕜)) (w : (σ → 𝕜) × (ι → 𝕜)) :
    AnalyticAt 𝕜 (fun w : (σ → 𝕜) × (ι → 𝕜) =>
      (aevalTower (aeval w.1) w.2 : MvPolynomial ι (MvPolynomial σ 𝕜) →ₐ[𝕜] 𝕜) q) w := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    simp only [aevalTower_C]
    exact AnalyticAt.aeval_mvPolynomial (A := 𝕜) (f := fun w : (σ → 𝕜) × (ι → 𝕜) => w.1)
      (fun i => ((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) i).comp
        (ContinuousLinearMap.fst 𝕜 (σ → 𝕜) (ι → 𝕜))).analyticAt w) a
  | add P Q hP hQ => simp only [map_add]; exact hP.add hQ
  | mul_X P i hP =>
    simp only [map_mul, aevalTower_X]
    exact hP.mul (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => 𝕜) i).comp
        (ContinuousLinearMap.snd 𝕜 (σ → 𝕜) (ι → 𝕜))).analyticAt w)

theorem hasDerivAt_aevalTower_line {R ι : Type*} [CommRing R] [Algebra 𝕜 R] [Fintype ι]
    (φ : R →ₐ[𝕜] 𝕜) (q : MvPolynomial ι R) (y v : ι → 𝕜) :
    HasDerivAt (fun t : 𝕜 => (aevalTower φ (y + t • v) : MvPolynomial ι R →ₐ[𝕜] 𝕜) q)
      (∑ i, (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv i q) * v i) 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : 𝕜) (φ a)
  | add P Q hP hQ =>
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    exact hP.add hQ
  | mul_X P i hP =>
    have hX : HasDerivAt (fun t : 𝕜 => y i + t * v i) (v i) 0 := by
      simpa using ((hasDerivAt_id (0 : 𝕜)).mul_const (v i)).const_add (y i)
    have h := hP.mul hX
    simp only [map_mul, aevalTower_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine HasDerivAt.congr_deriv h ?_
    have h1 : ∀ j, (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv j (P * X i)) * v j =
        (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) (pderiv j P) * v j * y i +
        if i = j then (aevalTower φ y : MvPolynomial ι R →ₐ[𝕜] 𝕜) P * v j else 0 := by
      intro j
      rw [pderiv_mul, pderiv_X]
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [hij, Pi.single_eq_of_ne hij]; ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.sum_mul]
    simp

variable [CompleteSpace 𝕜] {A : Type*} [CommRing A] [Algebra 𝕜 A] {d : ℕ}

theorem exists_openPartialHomeomorph_analytic {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (hdim : Module.finrank 𝕜 E = Module.finrank 𝕜 F) {Ψ : E → F} {x : E}
    (hΨ : AnalyticAt 𝕜 Ψ x) (hinj : Function.Injective (fderiv 𝕜 Ψ x)) :
    ∃ Φ : OpenPartialHomeomorph E F, (Φ : E → F) = Ψ ∧ x ∈ Φ.source ∧
      AnalyticOnNhd 𝕜 Φ.symm Φ.target := by
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  haveI : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  have hsurj : Function.Surjective (fderiv 𝕜 Ψ x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (fderiv 𝕜 Ψ x : E →ₗ[𝕜] F))).mp hinj
  let Le := ContinuousLinearEquiv.ofBijective (fderiv 𝕜 Ψ x) (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have hLe : (Le : E →L[𝕜] F) = fderiv 𝕜 Ψ x := ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hφ : HasStrictFDerivAt Ψ (Le : E →L[𝕜] F) x := by rw [hLe]; exact hΨ.hasStrictFDerivAt
  let Φ := hφ.toOpenPartialHomeomorph Ψ
  have hpS : x ∈ Φ.source := hφ.mem_toOpenPartialHomeomorph_source
  have hsymm : AnalyticAt 𝕜 Φ.symm (Φ x) :=
    Φ.analyticAt_symm' (i := Le) hpS hΨ hLe.symm
  obtain ⟨s, hs, hsan⟩ := hsymm.exists_mem_nhds_analyticOnNhd
  obtain ⟨T, hTs, hTo, hTp⟩ := mem_nhds_iff.mp hs
  refine ⟨(Φ.symm.restrOpen T hTo).symm, rfl, ⟨hpS, hTp⟩, fun z hz => hsan z (hTs hz.2)⟩

theorem exists_chart_of_etale (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale)
    (p : A →ₐ[𝕜] 𝕜) :
    ∃ e : OpenPartialHomeomorph (A →ₐ[𝕜] 𝕜) (Fin d → 𝕜), p ∈ e.source ∧
      (e : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) = coords g ∧
      ∀ a, AnalyticOnNhd 𝕜 (fun z => e.symm z a) e.target := by
  classical
  letI : Algebra (MvPolynomial (Fin d) 𝕜) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) 𝕜) A := hg
  haveI : IsScalarTower 𝕜 (MvPolynomial (Fin d) 𝕜) A :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  obtain ⟨ι, σ, _, _, P, hP⟩ := (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.1
    ‹Algebra.Etale (MvPolynomial (Fin d) 𝕜) A›).out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hcard : Fintype.card σ = Fintype.card ι := by
    have := P.card_relations_le_card_vars_of_isFinite
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] at this hP
    omega
  have hbij : Function.Bijective P.map :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨P.map_inj, hcard⟩
  let π : MvPolynomial ι (MvPolynomial (Fin d) 𝕜) →ₐ[𝕜] A := (aeval P.val).restrictScalars 𝕜
  have hπ : Function.Surjective π := P.aeval_val_surjective
  let ev : (Fin d → 𝕜) × (ι → 𝕜) → (MvPolynomial ι (MvPolynomial (Fin d) 𝕜) →ₐ[𝕜] 𝕜) :=
    fun w => aevalTower (aeval w.1) w.2
  let j : (A →ₐ[𝕜] 𝕜) → (Fin d → 𝕜) × (ι → 𝕜) := fun q => (coords g q, fun i => q (P.val i))
  have hjc : Continuous j :=
    (continuous_coords g).prodMk (continuous_pi fun _ => continuous_eval _)
  have hevj : ∀ q, ev (j q) = comap π q := by
    intro q
    refine MvPolynomial.algHom_ext' ?_ ?_
    · ext i
      simp [ev, j, π, RingHom.algebraMap_toAlgebra]
    · intro i; simp [ev, j, π]
  have hker : ∀ a, π a = 0 ↔ a ∈ Ideal.span (range P.relation) := by
    intro a
    rw [P.span_range_relation_eq_ker]
    rw [P.ker_eq_ker_aeval_val]
    rfl
  have hex : ∀ w, (∀ r, ev w (P.relation r) = 0) → ∃ q, j q = w ∧ comap π q = ev w := by
    intro w hw
    obtain ⟨q, hq⟩ := exists_comap_eq_of_surjective π hπ (ev w) fun a ha => by
      have : Ideal.span (range P.relation) ≤ RingHom.ker (ev w) := by
        rw [Ideal.span_le]; rintro _ ⟨r, rfl⟩; exact hw r
      exact this ((hker a).1 ha)
    refine ⟨q, ?_, hq⟩
    ext i
    · simpa [ev, π, j, RingHom.algebraMap_toAlgebra] using DFunLike.congr_fun hq (C (X i))
    · simpa [ev, π, j] using DFunLike.congr_fun hq (X i)
  have hjinj : Function.Injective j := by
    intro q q' h
    ext a
    obtain ⟨b, rfl⟩ := hπ a
    have := hevj q
    rw [h, hevj] at this
    exact (DFunLike.congr_fun this b).symm
  let Ψ : (Fin d → 𝕜) × (ι → 𝕜) → (Fin d → 𝕜) × (σ → 𝕜) :=
    fun w => (w.1, fun r => ev w (P.relation r))
  have hΨj : ∀ q, Ψ (j q) = (coords g q, 0) := by
    intro q
    ext r
    · rfl
    · change ev (j q) (P.relation r) = 0
      rw [hevj, comap_apply, (hker _).2 (Ideal.subset_span ⟨r, rfl⟩), map_zero]
  have hΨan : AnalyticAt 𝕜 Ψ (j p) :=
    analyticAt_fst.prod (analyticAt_pi_iff.2 fun r => analyticAt_aevalTower _ _)
  have hinj : Function.Injective (fderiv 𝕜 Ψ (j p)) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨u, v⟩ huv
    have hline : HasDerivAt (fun t : 𝕜 => Ψ (j p + t • (u, v))) 0 0 := by
      have h1 : HasDerivAt (fun t : 𝕜 => j p + t • (u, v)) (u, v) 0 := by
        simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const (u, v)).const_add (j p)
      have h2 : HasFDerivAt Ψ (fderiv 𝕜 Ψ (j p)) (j p + (0 : 𝕜) • (u, v)) := by
        simpa using hΨan.differentiableAt.hasFDerivAt
      have := h2.comp_hasDerivAt (0 : 𝕜) h1
      rwa [huv] at this
    have hu : u = 0 := by
      have h1 : HasDerivAt (fun t : 𝕜 => (j p).1 + t • u) u 0 := by
        simpa using ((hasDerivAt_id (0 : 𝕜)).smul_const u).const_add (j p).1
      have h2 := (ContinuousLinearMap.fst 𝕜 (Fin d → 𝕜) (σ → 𝕜)).hasFDerivAt.comp_hasDerivAt
        (0 : 𝕜) hline
      exact h1.unique h2
    subst hu
    have hv : ∀ r, ∑ i, ev (j p) (pderiv i (P.relation r)) * v i = 0 := by
      intro r
      have h1 := hasDerivAt_aevalTower_line (aeval (j p).1) (P.relation r) (j p).2 v
      have h2 := (((ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ => 𝕜) r).comp
        (ContinuousLinearMap.snd 𝕜 (Fin d → 𝕜) (σ → 𝕜))).hasFDerivAt.comp_hasDerivAt (0 : 𝕜) hline)
      refine h1.unique ?_
      simpa [Function.comp_def, Ψ, ev] using h2
    have hdet : ((ev (j p)).toRingHom.mapMatrix P.jacobiMatrix).det ≠ 0 := by
      rw [← RingHom.map_det, hevj]
      have := (P.jacobian_isUnit.map p).ne_zero
      rw [P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply] at this
      exact this
    have hw : (fun s => v (P.map s)) = 0 := by
      refine Matrix.eq_zero_of_vecMul_eq_zero hdet ?_
      ext r
      rw [Pi.zero_apply, ← hv r, ← hbij.sum_comp]
      simp [Matrix.vecMul, dotProduct, P.jacobiMatrix_apply, mul_comm]
    have : v = 0 := by
      ext i
      obtain ⟨s, rfl⟩ := hbij.2 i
      exact congrFun hw s
    rw [this]; rfl
  obtain ⟨Φ, hΦ, hpS, hsymm⟩ := exists_openPartialHomeomorph_analytic
    (by simp [Module.finrank_prod, hcard]) hΨan hinj
  have hex' : ∀ z : Fin d → 𝕜, ∃ q : A →ₐ[𝕜] 𝕜, (z, 0) ∈ Φ.target →
      j q = Φ.symm (z, 0) ∧ comap π q = ev (Φ.symm (z, 0)) := by
    intro z
    by_cases hz : (z, 0) ∈ Φ.target
    · obtain ⟨q, hq⟩ := hex (Φ.symm (z, 0)) fun r => by
        have := congrFun (congrArg Prod.snd (Φ.right_inv hz)) r
        rwa [hΦ] at this
      exact ⟨q, fun _ => hq⟩
    · exact ⟨p, fun h => absurd h hz⟩
  choose s hs using hex'
  have han : ∀ a, AnalyticOnNhd 𝕜 (fun z => s z a) {z | (z, 0) ∈ Φ.target} := by
    intro a
    obtain ⟨b, rfl⟩ := hπ a
    have hop : IsOpen {z : Fin d → 𝕜 | (z, 0) ∈ Φ.target} :=
      Φ.open_target.preimage (continuous_id.prodMk continuous_const)
    refine AnalyticOnNhd.congr hop (f := fun z => ev (Φ.symm (z, 0)) b) ?_ ?_
    · intro z hz
      have h1 : AnalyticAt 𝕜 (fun z : Fin d → 𝕜 => Φ.symm (z, 0)) z :=
        AnalyticAt.comp (f := fun z : Fin d → 𝕜 => (z, (0 : σ → 𝕜))) (hsymm _ hz)
          (analyticAt_id.prod analyticAt_const)
      exact AnalyticAt.comp (f := fun z : Fin d → 𝕜 => Φ.symm (z, 0))
        (analyticAt_aevalTower b _) h1
    · intro z hz
      exact (DFunLike.congr_fun (hs z hz).2 b).symm
  have hmap : ∀ q, j q ∈ Φ.source → (coords g q, 0) ∈ Φ.target := by
    intro q hq
    have := Φ.map_source hq
    rwa [hΦ, hΨj] at this
  refine ⟨{ toFun := coords g
            invFun := s
            source := j ⁻¹' Φ.source
            target := {z | (z, 0) ∈ Φ.target}
            map_source' := hmap
            map_target' := fun z hz => ?_
            left_inv' := fun q hq => ?_
            right_inv' := fun z hz => ?_
            open_source := Φ.open_source.preimage hjc
            open_target := Φ.open_target.preimage (continuous_id.prodMk continuous_const)
            continuousOn_toFun := (continuous_coords g).continuousOn
            continuousOn_invFun := continuousOn_iff.2 fun a => (han a).continuousOn },
    hpS, rfl, han⟩
  · rw [mem_preimage, (hs z hz).1]; exact Φ.map_target hz
  · apply hjinj
    rw [(hs _ (hmap q hq)).1, ← hΨj, ← hΦ, Φ.left_inv hq]
  · have := Φ.right_inv hz
    rw [← (hs z hz).1, hΦ, hΨj] at this
    exact congrArg Prod.fst this

theorem isLocalHomeomorph_coords_of_etale (g : MvPolynomial (Fin d) 𝕜 →ₐ[𝕜] A) (hg : g.Etale) :
    IsLocalHomeomorph (coords g : (A →ₐ[𝕜] 𝕜) → Fin d → 𝕜) := fun p => by
  obtain ⟨e, h1, h2, -⟩ := exists_chart_of_etale g hg p
  exact ⟨e, h1, h2.symm⟩

end GlobalTheory.AffinePoints
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.MvPolynomialIsHomogeneousComapWeighted
section
open TensorProduct Module

namespace GlobalTheory.GaloisDescent

section Decomposition

variable {ι M M' σ τ : Type*} [DecidableEq ι] [AddCommMonoid M] [AddCommMonoid M']
  [SetLike σ M] [AddSubmonoidClass σ M] [SetLike τ M'] [AddSubmonoidClass τ M']

theorem decompose_addMonoidHom (ℳ : ι → σ) (ℳ' : ι → τ) [DirectSum.Decomposition ℳ]
    [DirectSum.Decomposition ℳ'] (φ : M →+ M') (hφ : ∀ i, ∀ x ∈ ℳ i, φ x ∈ ℳ' i) (x : M) (i : ι) :
    (DirectSum.decompose ℳ' (φ x) i : M') = φ (DirectSum.decompose ℳ x i) := by
  induction x using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous j x =>
    by_cases h : j = i
    · subst h
      rw [DirectSum.decompose_of_mem_same ℳ' (hφ j _ x.2), DirectSum.decompose_of_mem_same ℳ x.2]
    · rw [DirectSum.decompose_of_mem_ne ℳ' (hφ j _ x.2) h, DirectSum.decompose_of_mem_ne ℳ x.2 h,
        map_zero]
  | add x y hx hy => simp [hx, hy]

end Decomposition

section Ideals

variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}

theorem restrictScalars_map_eq_span (hj : IsBaseChange L j.toLinearMap) (I : Ideal A) :
    (I.map j).restrictScalars L =
      Submodule.span L (j.toLinearMap '' (I.restrictScalars K : Submodule K A)) := by
  first
  | exact @_root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span
  | exact _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span
  | (apply _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RestrictScalarsSpan.restrictScalars_map_eq_span ..)

theorem ideal_comap_map (hj : IsBaseChange L j.toLinearMap) (I : Ideal A) :
    (I.map j).comap j = I := by
  ext a
  have := SetLike.ext_iff.1 (comap_span_image hj (I.restrictScalars K)) a
  rw [← restrictScalars_map_eq_span hj] at this
  exact this

theorem ideal_map_comap_of_span (I : Ideal B) (N : Submodule K A)
    (h : Submodule.span L (j.toLinearMap '' N) = I.restrictScalars L) :
    (I.comap j).map j = I := by
  refine le_antisymm Ideal.map_comap_le fun x hx => ?_
  have hle : Submodule.span L (j.toLinearMap '' N) ≤ ((I.comap j).map j).restrictScalars L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    refine Ideal.mem_map_of_mem j ?_
    exact h.le (Submodule.subset_span ⟨a, ha, rfl⟩)
  exact hle (h.ge hx)

theorem ideal_map_comap_of_stable (hj : IsBaseChange L j.toLinearMap) (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (φ : G → B →+ B) (hφ : ∀ g l a, φ g (l • j a) = s g l • j a)
    (I : Ideal B) (hI : ∀ g, ∀ x ∈ I, φ g x ∈ I) : (I.comap j).map j = I :=
  ideal_map_comap_of_span I _ (span_image_comap_eq hj s hs φ hφ (I.restrictScalars L) hI)

section Graded

variable {ι σ τ : Type*} [DecidableEq ι] [AddMonoid ι] [SetLike σ A] [AddSubmonoidClass σ A]
  [SetLike τ B] [AddSubmonoidClass τ B] (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ]

theorem isHomogeneous_comap (h : ∀ i, ∀ a ∈ 𝒜 i, j a ∈ ℬ i) {I : Ideal B}
    (hI : I.IsHomogeneous ℬ) : (I.comap j).IsHomogeneous 𝒜 :=
  (HomogeneousIdeal.comap (⟨j.toRingHom, fun {i a} => h i a⟩ : 𝒜 →+*ᵍ ℬ) ⟨I, hI⟩).isHomogeneous

end Graded

end Ideals

section Tensor

open Algebra.TensorProduct

variable {K L A G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

noncomputable def quotientEquivOfMapEq {A : Type*} [CommRing A] [Algebra K A] (I₀ : Ideal A)
    (I : Ideal (L ⊗[K] A)) (h : I₀.map (includeRight : A →ₐ[K] L ⊗[K] A) = I) :
    L ⊗[K] (A ⧸ I₀) ≃ₐ[L] (L ⊗[K] A) ⧸ I :=
  (tensorQuotientEquiv (R := K) L A L I₀).trans (Ideal.quotientEquivAlgOfEq L h)

@[simp]
theorem quotientEquivOfMapEq_tmul {A : Type*} [CommRing A] [Algebra K A] (I₀ : Ideal A)
    (I : Ideal (L ⊗[K] A)) (h : I₀.map (includeRight : A →ₐ[K] L ⊗[K] A) = I) (l : L) (a : A) :
    quotientEquivOfMapEq I₀ I h (l ⊗ₜ Ideal.Quotient.mk I₀ a) = Ideal.Quotient.mk I (l ⊗ₜ a) :=
  rfl

end Tensor

section Polynomial

open MvPolynomial

variable {K L G σ : Type*} [Field K] [Field L] [Algebra K L]

theorem isWeightedHomogeneous_map {M : Type*} [AddCommMonoid M] (w : σ → M) (m : M)
    (f : K →+* L) {p : MvPolynomial σ K} (hp : p.IsWeightedHomogeneous w m) :
    (map f p).IsWeightedHomogeneous w m := fun d hd =>
  hp fun h => hd (by rw [coeff_map, h, map_zero])

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem mvPolynomial_isHomogeneous_comap {I : Ideal (MvPolynomial σ L)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ L)) :
    (I.comap (map (algebraMap K L) : MvPolynomial σ K →+* _)).IsHomogeneous
      (homogeneousSubmodule σ K) :=
  isHomogeneous_comap (j := mapAlgHom (σ := σ) (Algebra.ofId K L)) _ _
    (fun i a ha => isWeightedHomogeneous_map 1 i _ ha) hI

end Polynomial

end GlobalTheory.GaloisDescent
end

