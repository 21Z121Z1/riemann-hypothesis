import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0083
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdNormEmbeddingsEqAbsNorm
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem prod_norm_embeddings_eq_abs_norm (E : Type) [Field E] [NumberField E] (γ : E) :
    ∏ φ : E →+* ℂ, ‖φ γ‖ = |((Algebra.norm ℚ γ : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ γ
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_prod, eq_ratCast] at h2
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ) (fun φ : E →+* ℂ => ‖φ γ‖)
    (fun φ : E →ₐ[ℚ] ℂ => ‖φ γ‖) (fun _ => rfl), ← h2]
  rw [← Real.norm_eq_abs, ← Complex.norm_real]
  simp

theorem norm_typeNorm_sq_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (γ : E) (σ : K →+* ℂ), ‖σ (∏ τ : E →+* ℂ, (⟨τ γ, hK τ γ⟩ : K) ^ r τ)‖ ^ 2 = |(Algebra.norm ℚ γ : ℝ)| ^ n := by
  intro E _ _ _ _ r n hr K _ hK γ σ
  let s : (E →+* ℂ) → (E →+* ℂ) := fun τ => σ.comp (τ.codRestrict K (hK τ))
  have hs : ∀ τ x, s τ x = σ ⟨τ x, hK τ x⟩ := fun _ _ => rfl
  have hinj : Function.Injective s := by
    intro a b hab
    ext x
    have := DFunLike.congr_fun hab x
    rw [hs, hs] at this
    exact congrArg Subtype.val (σ.injective this)
  have hbij : Function.Bijective s := Finite.injective_iff_bijective.mp hinj
  have hconj : ∀ τ, ‖s (ComplexEmbedding.conjugate τ) γ‖ = ‖s τ γ‖ := by
    intro τ
    have h1 : s (ComplexEmbedding.conjugate τ) γ = s τ (IsCMField.complexConj E γ) := by
      rw [hs, hs]
      congr 2
      rw [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    rw [h1, IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
  have hinv : Function.Involutive
      (fun τ : E →+* ℂ => ComplexEmbedding.conjugate τ) := fun τ => star_star τ
  have hP : ‖σ (∏ τ : E →+* ℂ, (⟨τ γ, hK τ γ⟩ : K) ^ r τ)‖ = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ := by
    rw [map_prod, norm_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, norm_pow, hs]
  have hQ : ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r τ
      = ∏ τ : E →+* ℂ, ‖s τ γ‖ ^ r (ComplexEmbedding.conjugate τ) := by
    rw [← hinv.bijective.prod_comp (fun τ => ‖s τ γ‖ ^ r τ)]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hconj]
  rw [hP, sq]
  nth_rewrite 2 [hQ]
  rw [← Finset.prod_mul_distrib, ← prod_norm_embeddings_eq_abs_norm,
    ← hbij.prod_comp (fun φ => ‖φ γ‖), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← pow_add, hr]

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionCompletionBlockTriLowerBlockDetStatement
section
open NumberField IsDedekindDomain Formalism.L2 Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_completion_blockTri_lowerBlockDet : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (φ : s.v.adicCompletionIntegers (maximalRealSubfield L) →+* kP s.w) (n r : ℕ) (h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) (g : GL (Fin n) (kP s.w)), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield L)) < 1) → (∀ a b, ∃ hab : (h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), (g : Matrix (Fin n) (Fin n) (kP s.w)) a b = φ ⟨_, hab⟩) → (g ∈ blockTri (blk2 r) ↔ ∀ a b : Fin n, r ≤ a.val → b.val < r → Valued.v ((h : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b) < 1) ∧ (g ∈ blockTri (blk2 r) → ∃ hd : NG.detDD s r h ∈ s.v.adicCompletionIntegers (maximalRealSubfield L), ((dBlk (blk2 r) 1 g : (kP s.w)ˣ) : kP s.w) = φ ⟨_, hd⟩) := by
  first | exact @GlobalTheory.reduction_blockTri_detDD | exact GlobalTheory.reduction_blockTri_detDD | (intros; apply GlobalTheory.reduction_blockTri_detDD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelevelCoprimeOfModOne
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory

theorem host_relevel : ∀ (R : Ranks) (H : Host R), H.ccK = ⊤ → ∀ (g : Fin 2 → ℕ) (p p' : ℕ) (S : Finset ℕ), (∀ i, (g i).Prime) → g 0 ≠ g 1 → p.Prime → p'.Prime → p ≠ p' → p % 15 = 1 → p' % 15 = 1 → (∀ i, p ≠ g i ∧ p' ≠ g i) → (∀ x ∈ insert (g 0) (insert (g 1) (insert p (insert p' S))), Nat.Coprime x H.QS) → ∃ (hg : ∀ i, (g i).Prime) (hne : g 0 ≠ g 1) (lv : Finset ℕ) (hl : ∀ i, g i ∈ lv) (hp : p.Prime) (hp' : p'.Prime) (hpp : p ≠ p') (hpl : p ∈ lv ∧ p' ∈ lv) (hm : p % 15 = 1 ∧ p' % 15 = 1) (hpg : ∀ i, p ≠ g i ∧ p' ≠ g i) (hc : ∀ x ∈ insert 2 (insert 3 (insert 5 (insert H.q (insert H.d lv)))), Nat.Coprime (Ideal.absNorm H.ccK) x) (hcs : ∀ x ∈ lv, Nat.Coprime x H.QS), lv = insert (g 0) (insert (g 1) (insert p (insert p' S))) ∧ ∃ H' : Host R, H' = { H with levelPrimes := lv, g := g, g_prime := hg, g_ne := hne, g_level := hl, pde := p, pde' := p', pde_prime := hp, pde'_prime := hp', pde_ne := hpp, pde_level := hpl, pde_mod := hm, pde_ne_g := hpg, ccK_coprime := hc, level_coprimeS := hcs } := by
  intro R H hK g p p' S hg hne hp hp' hpp h1 h2 hpg hcs
  refine ⟨hg, hne, insert (g 0) (insert (g 1) (insert p (insert p' S))), ?_, hp, hp', hpp, ?_,
    ⟨h1, h2⟩, hpg, ?_, hcs, rfl, _, rfl⟩
  · intro i
    fin_cases i <;> simp
  · constructor <;> simp
  · intro x _
    rw [hK]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideCardEqOfCoord
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem rowSide_card_eq_of_coord {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    [FiniteDimensional ℂ EE] (X : RowSide D EE) {n d : ℕ} (b : OrthonormalBasis (Fin n) ℂ EE)
    (e : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] X.RR.V) : n = d := by
  let bC : Module.Basis X.RR.ι ℂ EE := Module.Basis.mk X.jEE_basis.1 X.jEE_basis.2.ge
  let bL : Module.Basis (Fin d) D.what₂.LL X.RR.V := (Pi.basisFun D.what₂.LL (Fin d)).map e
  have e1 : Fin n ≃ X.RR.ι := b.toBasis.indexEquiv bC
  have e2 : X.RR.ι ≃ Fin d := X.RR.b.indexEquiv bL
  simpa using Fintype.card_congr (e1.trans e2)

theorem drows_eq_and_d0_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (S0 : IndefData (A.side P0 ψ0 Zs)) (S1 : IndefData (A.side Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A.side Ps ψs Zs)) (I : DivisionCompatibilityData D A P0 ψ0 Ps ψs Zs S0 S1 X0 Dc), D.what₂.Drows = S1.D ∧ D.what₂.D0 = S0.D := by
  intro D G _ _ Pl0 T A P0 ψ0 Ps ψs Zs S0 S1 X0 Dc I
  exact ⟨rowSide_card_eq_of_coord (RowSide.sharp D) D.what₂.onb I.eRR,
    rowSide_card_eq_of_coord X0.s D.what₂.onb0 I.eRR0⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurInnerEqPairClosableNormInvariant
section
open Filter
open scoped InnerProductSpace Topology

namespace GlobalTheory.ClosableSchur

theorem inner_eq_of_diag {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (D : Submodule ℂ H) (A A' : H →ₗ[ℂ] E) (c : ℂ)
    (h : ∀ w ∈ D, ⟪A w, A' w⟫_ℂ = c * ⟪w, w⟫_ℂ) :
    ∀ w ∈ D, ∀ w' ∈ D, ⟪A w, A' w'⟫_ℂ = c * ⟪w, w'⟫_ℂ := by
  intro w hw w' hw'
  have h1 := h (w + w') (D.add_mem hw hw')
  have h2 := h (w + Complex.I • w') (D.add_mem hw (D.smul_mem _ hw'))
  have h3 := h w hw
  have h4 := h w' hw'
  simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, Complex.conj_I] at h1 h2
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (1 / 2 : ℂ) * h1 - (Complex.I / 2) * h2 - (1 / 2 - Complex.I / 2) * h3
    - (1 / 2 - Complex.I / 2) * h4
    + (1 / 2 : ℂ) * (⟪A w, A' w'⟫_ℂ - c * ⟪w, w'⟫_ℂ - ⟪A w', A' w⟫_ℂ + c * ⟪w', w⟫_ℂ
      - Complex.I * (⟪A w', A' w'⟫_ℂ - c * ⟪w', w'⟫_ℂ)) * hI

theorem tendsto_zero_of_norm_sq {H E : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (D : Submodule ℂ H) (A : H →ₗ[ℂ] E) (a : ℝ)
    (h : ∀ w ∈ D, ‖A w‖ ^ 2 = a * ‖w‖ ^ 2) (u : ℕ → H) (hu : ∀ i, u i ∈ D)
    (h0 : Tendsto u atTop (𝓝 0)) : Tendsto (fun i => A (u i)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero] at h0 ⊢
  have h1 : Tendsto (fun i => a * ‖u i‖ ^ 2) atTop (𝓝 0) := by
    simpa using (h0.pow 2).const_mul a
  have h2 := h1.sqrt
  rw [Real.sqrt_zero] at h2
  refine h2.congr fun i => ?_
  rw [← h _ (hu i), Real.sqrt_sq (norm_nonneg _)]

theorem inner_eq_pair : ∀ (ι H E : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (ρ : ι → (H →L[ℂ] H)) (D : Submodule ℂ H), (∀ i v, ‖ρ i v‖ = ‖v‖) → (∀ i, ∃ j, (∀ v, ρ j (ρ i v) = v) ∧ ∀ v, ρ i (ρ j v) = v) → (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ i, ∀ v ∈ S, ρ i v ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ i, ∀ v ∈ D, ρ i v ∈ D) → ∀ A A' : H →ₗ[ℂ] E, (∀ i, ∀ w ∈ D, ‖A (ρ i w)‖ = ‖A w‖) → (∀ i, ∀ w ∈ D, ‖A' (ρ i w)‖ = ‖A' w‖) → (∀ i, ∀ w ∈ D, ⟪A (ρ i w), A' (ρ i w)⟫_ℂ = ⟪A w, A' w⟫_ℂ) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A (u i)) atTop (𝓝 f) → f = 0) → (∀ (u : ℕ → H) (f : E), (∀ i, u i ∈ D) → Tendsto u atTop (𝓝 0) → Tendsto (fun i => A' (u i)) atTop (𝓝 f) → f = 0) → ∃ c : ℂ, ∀ w ∈ D, ∀ w' ∈ D, ⟪A w, A' w'⟫_ℂ = c * ⟪w, w'⟫_ℂ := by
  intro ι H E _ _ _ _ _ _ ρ D hn hinv hirr hD A A' hA hA' hAA' hc hc'
  obtain ⟨a, ha⟩ := norm_sq_eq ι H E ρ D hn hinv hirr hD A hA hc
  obtain ⟨a', ha'⟩ := norm_sq_eq ι H E ρ D hn hinv hirr hD A' hA' hc'
  have hexp : ∀ (z : ℂ) (w : H), ‖(z • A + A') w‖ ^ 2 =
      ‖z‖ ^ 2 * ‖A w‖ ^ 2 + 2 * ((starRingEnd ℂ) z * ⟪A w, A' w⟫_ℂ).re + ‖A' w‖ ^ 2 := by
    intro z w
    rw [LinearMap.add_apply, LinearMap.smul_apply, @norm_add_sq ℂ, inner_smul_left, norm_smul,
      mul_pow]
    rfl
  have key : ∀ z : ℂ, ∃ b : ℝ, ∀ w ∈ D, ‖(z • A + A') w‖ ^ 2 = b * ‖w‖ ^ 2 := by
    intro z
    refine norm_sq_eq ι H E ρ D hn hinv hirr hD (z • A + A') ?_ ?_
    · intro i w hw
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), hexp, hexp, hA i w hw, hA' i w hw,
        hAA' i w hw]
    · intro u f hu h0 hf
      have h1 := tendsto_zero_of_norm_sq D A a ha u hu h0
      have h2 := tendsto_zero_of_norm_sq D A' a' ha' u hu h0
      have h3 := (h1.const_smul z).add h2
      rw [smul_zero, add_zero] at h3
      exact tendsto_nhds_unique hf h3
  obtain ⟨b, hb⟩ := key 1
  obtain ⟨b', hb'⟩ := key Complex.I
  refine ⟨⟨(b - a - a') / 2, (b' - a - a') / 2⟩, inner_eq_of_diag D A A' _ fun w hw => ?_⟩
  have e1 := hb w hw
  have e2 := hb' w hw
  rw [hexp, ha w hw, ha' w hw] at e1 e2
  have e3 : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e3]
  simp only [map_one, one_mul, norm_one, one_pow, Complex.norm_I, Complex.conj_I, Complex.mul_re,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at e1 e2
  apply Complex.ext
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; linarith
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; linarith

end GlobalTheory.ClosableSchur
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBlockDetEqBlockDetOfSumPartitionsStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dBlk_eq_blkDet_coarse : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (g : GL (Fin n) κ) (hg : g ∈ Formalism.L2.Col.blockUT n κ r [t]),
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 g = Formalism.L2.Col.blkDet n κ (Formalism.L2.Col.coarse r [t]) 1 ⟨g, hg⟩ := by
  first | exact @GlobalTheory.secondBlockDet_eq_blockDet_of_sum_partitions | exact GlobalTheory.secondBlockDet_eq_blockDet_of_sum_partitions | (intros; apply GlobalTheory.secondBlockDet_eq_blockDet_of_sum_partitions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmoduleEqSpanOfPowEqSpanPow
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped nonZeroDivisors

namespace GlobalTheory

theorem fractionalIdeal_eq_of_count_eq {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

theorem submodule_eq_span_of_pow_eq_span_pow :
    ∀ (K : Type) [Field K] [NumberField K] (I : Submodule (𝓞 K) K) (β : K) (h : ℕ),
      0 < h → β ≠ 0 → I.FG → I ^ h = Submodule.span (𝓞 K) {β ^ h} →
      I = Submodule.span (𝓞 K) {β} := by
  intro K _ _ I β h hh hβ hfg hpow
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg hfg⟩
  have hJI : (J : Submodule (𝓞 K) K) = I := rfl
  have hB : FractionalIdeal.spanSingleton (𝓞 K)⁰ β ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hβ
  have hp : J ^ h = FractionalIdeal.spanSingleton (𝓞 K)⁰ β ^ h := by
    rw [FractionalIdeal.spanSingleton_pow]
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_pow, FractionalIdeal.coe_spanSingleton, hJI, hpow]
  have hJ : J ≠ 0 := by
    intro h0
    rw [h0, zero_pow hh.ne'] at hp
    exact pow_ne_zero h hB hp.symm
  have hJB : J = FractionalIdeal.spanSingleton (𝓞 K)⁰ β := by
    refine fractionalIdeal_eq_of_count_eq hJ hB fun v => ?_
    have := congrArg (FractionalIdeal.count K v) hp
    rw [FractionalIdeal.count_pow, FractionalIdeal.count_pow] at this
    exact mul_left_cancel₀ (by exact_mod_cast hh.ne') this
  rw [← hJI, hJB, FractionalIdeal.coe_spanSingleton]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharacterIndependentUniformizer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem valuation_algebraMap_int_le_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (x : 𝓞 E) : A.valuation (algebraMap E Ω (x : E)) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A (RingOfIntegers.isIntegral_coe x).algebraMap)

theorem valuation_uniformiser_le {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 E)} (hP : IsPlaceOver A P) {ϖ ϖ' : 𝓞 E}
    (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) (h1' : ϖ' ∈ P.asIdeal) :
    A.valuation (algebraMap E Ω (ϖ' : E)) ≤ A.valuation (algebraMap E Ω (ϖ : E)) := by
  have hdvd : P.asIdeal ∣ Ideal.span {ϖ} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h1)
  obtain ⟨J, hJ⟩ := hdvd
  have hJP : ¬ (J : Set (𝓞 E)) ⊆ P.asIdeal := by
    intro hle
    apply h2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).1 this
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  have hmem : ϖ' * s ∈ Ideal.span {ϖ} := by
    rw [hJ]; exact Ideal.mul_mem_mul h1' hsJ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hmem
  have hs1 : A.valuation (algebraMap E Ω (s : E)) = 1 :=
    le_antisymm (valuation_algebraMap_int_le_one A s) (not_lt.1 fun h => hsP ((hP s).1 h))
  have e : algebraMap E Ω (a : E) * algebraMap E Ω (ϖ : E) = algebraMap E Ω (ϖ' : E) * algebraMap E Ω (s : E) := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact_mod_cast ha
  have hv := congrArg A.valuation e
  rw [map_mul, map_mul, hs1, mul_one] at hv
  rw [← hv]
  calc A.valuation (algebraMap E Ω (a : E)) * A.valuation (algebraMap E Ω (ϖ : E))
      ≤ 1 * A.valuation (algebraMap E Ω (ϖ : E)) := by
        gcongr; exact valuation_algebraMap_int_le_one A a
    _ = A.valuation (algebraMap E Ω (ϖ : E)) := one_mul _

theorem tame_quot_indep : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → ∀ (ϖ ϖ' : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ϖ' ∈ P.asIdeal → ϖ' ∉ P.asIdeal ^ 2 → ∀ (π π' : Ω), π ^ m = algebraMap E Ω (ϖ : E) → π' ^ m = algebraMap E Ω (ϖ' : E) → ∀ σ ∈ Ine (F := E) A, σ π / π = σ π' / π' := by
  intro E Ω _ _ _ _ _ A P hP m hm0 hmP ϖ ϖ' h1 h2 h1' h2' π π' hπ hπ' σ hσ
  have hne : ∀ x : 𝓞 E, x ∉ P.asIdeal ^ 2 → algebraMap E Ω (x : E) ≠ 0 := by
    intro x hx h0
    apply hx
    have hx0 : (x : E) = 0 := (map_eq_zero_iff _ (algebraMap E Ω).injective).1 h0
    have : x = 0 := by exact_mod_cast hx0
    rw [this]; exact zero_mem _
  have hπ0 : π ≠ 0 := by
    rintro rfl; exact hne ϖ h2 (by rw [← hπ, zero_pow hm0.ne'])
  have hπ0' : π' ≠ 0 := by
    rintro rfl; exact hne ϖ' h2' (by rw [← hπ', zero_pow hm0.ne'])
  have hv : A.valuation (algebraMap E Ω (ϖ : E)) = A.valuation (algebraMap E Ω (ϖ' : E)) :=
    le_antisymm (valuation_uniformiser_le hP h1' h2' h1) (valuation_uniformiser_le hP h1 h2 h1')
  set ρ := π' / π with hρ
  have hρ0 : ρ ≠ 0 := div_ne_zero hπ0' hπ0
  have hρm : ρ ^ m = algebraMap E Ω ((ϖ' : E) / (ϖ : E)) := by
    rw [hρ, div_pow, hπ, hπ', map_div₀]
  have hvρm : A.valuation ρ ^ m = 1 := by
    rw [← Valuation.map_pow, hρm, map_div₀, map_div₀, hv, div_self]
    simpa using hne ϖ' h2'
  have hvρ : A.valuation ρ = 1 := by
    rcases lt_trichotomy (A.valuation ρ) 1 with h | h | h
    · exact absurd hvρm (pow_lt_one₀ zero_le h hm0.ne').ne
    · exact h
    · exact absurd hvρm (one_lt_pow₀ h hm0.ne').ne'
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro h
    apply hmP
    apply (hP _).1
    simpa using h
  have hσρm : (σ ρ / ρ) ^ m = 1 := by
    rw [div_pow, ← map_pow, hρm, AlgEquiv.commutes, ← hρm]
    exact div_self (pow_ne_zero _ hρ0)
  have hclose : A.valuation (σ ρ / ρ - 1) < 1 := by
    have e : σ ρ / ρ - 1 = (σ ρ - ρ) / ρ := by field_simp
    rw [e, map_div₀, hvρ, div_one]
    exact hσ.2 ρ hvρ.le
  have hfix : σ ρ / ρ = 1 := root_eq_of_close A m hσρm (one_pow m) hmv hclose
  have hfix' : σ ρ = ρ := (div_eq_one_iff_eq hρ0).1 hfix
  have eπ' : π' = ρ * π := by rw [hρ]; field_simp
  rw [eπ', map_mul, hfix', mul_div_mul_left _ _ hρ0]

end GlobalTheory.TameTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameRepConjugateInertia
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
open scoped Pointwise

namespace GlobalTheory.TameTauConj

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem conj_mem_Ine_of_mem_Ine_smul [IsAlgClosure E Ω] {A : ValuationSubring Ω} {g σ : G E Ω}
    (hσ : σ ∈ Ine (F := E) (g • A)) : g⁻¹ * σ * g ∈ Ine (F := E) A := by
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        AlgEquiv.smul_def]
      have : (g⁻¹ : G E Ω) (g x) = x := by
        show (g⁻¹ * g) x = x
        simp
      rw [this]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (smul_valuation_lt_one_iff g A _).1 (hσ.2 _ hx')
    have e : (g⁻¹ : G E Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
      rw [map_sub]
      congr 1
      show (g⁻¹ : G E Ω) (g x) = x
      show (g⁻¹ * g) x = x
      simp
    rw [e] at h
    exact h

end GlobalTheory.TameTauConj

open GlobalTheory.TameTauConj in

theorem GlobalTheory.TameTauConj.tameRep_conj : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A₀ : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A₀ P → ∀ (e : ℤ) (σ : G E Ω) (u : 𝓞 E), NX.TameRep P e σ u → ∃ ρ : G E Ω, ρ⁻¹ * σ * ρ ∈ Ine (F := E) A₀ ∧ ∃ (ϖ : 𝓞 E) (π : Ω), ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ π ^ (normV P - 1) = algebraMap E Ω (ϖ : E) ∧ A₀.valuation ((ρ⁻¹ * σ * ρ) π / π - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ _ A₀ P hA₀ e σ u hT
  obtain ⟨A, hA, hσ, ϖ, π, h1, h2, h3, h4⟩ := hT
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isPlaceOver hA₀ hA
  subst hρ
  refine ⟨ρ, conj_mem_Ine_of_mem_Ine_smul hσ, ϖ, (ρ⁻¹ : G E Ω) π, h1, h2, ?_, ?_⟩
  · rw [← map_pow, h3, AlgEquiv.commutes]
  · have e1 : (ρ⁻¹ * σ * ρ) ((ρ⁻¹ : G E Ω) π) = (ρ⁻¹ : G E Ω) (σ π) := by
      show (ρ⁻¹ * σ * ρ * ρ⁻¹) π = (ρ⁻¹ * σ) π
      rw [show ρ⁻¹ * σ * ρ * ρ⁻¹ = ρ⁻¹ * σ by group]
    have e2 : (ρ⁻¹ * σ * ρ) ((ρ⁻¹ : G E Ω) π) / (ρ⁻¹ : G E Ω) π - (algebraMap E Ω (u : E)) ^ e
        = (ρ⁻¹ : G E Ω) (σ π / π - (algebraMap E Ω (u : E)) ^ e) := by
      rw [e1, map_sub, map_div₀, map_zpow₀, AlgEquiv.commutes]
    rw [e2]
    exact (smul_valuation_lt_one_iff ρ A₀ _).1 h4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopBlockEqOneIffMemColHKStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperLeftBlock_eq_one_iff_mem_HK : ∀ {κ : Type} [CommRing κ] {n r t : ℕ}, n = r + t → ∀ (hr : r ≤ n) (g : GL (Fin n) κ),
    g ∈ Formalism.L2.Col.blockUT n κ r [t] → (Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g ∈ Formalism.L2.Col.HK n κ r [t]) := by
  first | exact @GlobalTheory.topBlock_eq_one_iff_mem_colHK | exact GlobalTheory.topBlock_eq_one_iff_mem_colHK | (intros; apply GlobalTheory.topBlock_eq_one_iff_mem_colHK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderSmulOfFix
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Formalism.FrobeniusOrbits
open scoped Pointwise

namespace GlobalTheory.PlaceOverPair

theorem under_smul_of_fix {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra K E]
    (σ : E ≃ₐ[ℚ] E) (h : ∀ x : K, σ (algebraMap K E x) = algebraMap K E x) (I : Ideal (𝓞 E)) :
    (σ • I).under (𝓞 K) = I.under (𝓞 K) := by
  ext x
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have : σ⁻¹ • algebraMap (𝓞 K) (𝓞 E) x = algebraMap (𝓞 K) (𝓞 E) x := by
    rw [inv_smul_eq_iff]
    apply Subtype.val_injective
    exact (h x).symm
  rw [this]

theorem exists_over {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra K E]
    (v : HeightOneSpectrum (𝓞 K)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 K) = v := by
  haveI := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩

theorem exists_smul_eq {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {p : ℕ} (hp : p.Prime)
    (P Q : Ideal (𝓞 E)) [P.IsPrime] [Q.IsPrime] (hP : (p : 𝓞 E) ∈ P) (hQ : (p : 𝓞 E) ∈ Q) :
    ∃ σ : E ≃ₐ[ℚ] E, σ • P = Q := by
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal :=
    Ideal.IsPrime.isMaximal ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2
      (Nat.prime_iff_prime_int.1 hp)) (by simpa using hp.ne_zero)
  have key : ∀ (I : Ideal (𝓞 E)) [I.IsPrime], (p : 𝓞 E) ∈ I → I.LiesOver (Ideal.span {(p : ℤ)}) := by
    intro I _ hI
    refine ⟨hm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hI
  haveI := key P hP
  haveI := key Q hQ
  exact Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P Q (E ≃ₐ[ℚ] E)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem sqrt_sq : H.sqrtMinusD ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem conj_sqrt : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h2 := H.conjE_apply H.φ₀ H.sqrtMinusD
  refine h2.trans ?_
  have h3 : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem
  rw [map_neg, h3]
  simp

theorem fix_of_sqrt (σ : H.E ≃ₐ[ℚ] H.E) (h : σ H.sqrtMinusD = H.sqrtMinusD) (x : H.K) :
    σ (algebraMap H.K H.E x) = algebraMap H.K H.E x := by
  have : H.K ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
    apply IntermediateField.adjoin_simple_le_iff.2
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have : Subgroup.zpowers σ ≤ MulAction.stabilizer _ H.sqrtMinusD := by
      rw [Subgroup.zpowers_le]
      exact h
    exact this hf
  exact (IntermediateField.mem_fixedField_iff _ _).1 (this x.2) σ (Subgroup.mem_zpowers σ)

theorem exists_over_both {p : ℕ} (hp : p.Prime) (𝔭 : HeightOneSpectrum (𝓞 H.K)) (h𝔭 : (p : 𝓞 H.K) ∈ 𝔭.asIdeal)
    (v : HeightOneSpectrum (𝓞 H.F)) (hv : (p : 𝓞 H.F) ∈ v.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 H.E), w.under (𝓞 H.F) = v ∧ w.under (𝓞 H.K) = 𝔭 := by
  haveI := H.hostE_isGalois
  obtain ⟨w, rfl⟩ := exists_over (E := H.E) v
  obtain ⟨u, rfl⟩ := exists_over (E := H.E) 𝔭
  have hu : (p : 𝓞 H.E) ∈ u.asIdeal := by
    have : algebraMap (𝓞 H.K) (𝓞 H.E) (p : 𝓞 H.K) ∈ u.asIdeal := h𝔭
    rwa [map_natCast] at this
  have hw : (p : 𝓞 H.E) ∈ w.asIdeal := by
    have : algebraMap (𝓞 H.F) (𝓞 H.E) (p : 𝓞 H.F) ∈ w.asIdeal := hv
    rwa [map_natCast] at this
  haveI := u.isPrime
  haveI := w.isPrime
  obtain ⟨σ, hσ⟩ := exists_smul_eq hp u.asIdeal w.asIdeal hu hw
  have hs : σ H.sqrtMinusD = H.sqrtMinusD ∨ σ H.sqrtMinusD = -H.sqrtMinusD := by
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, sqrt_sq, map_neg, map_natCast]
  rcases hs with hs | hs
  · refine ⟨w, rfl, HeightOneSpectrum.ext ?_⟩
    show w.asIdeal.under _ = u.asIdeal.under _
    rw [← hσ]
    exact under_smul_of_fix σ (fix_of_sqrt H σ hs) _
  · have hne : H.conj • w.asIdeal ≠ ⊥ := by
      intro h
      apply w.ne_bot
      rw [← inv_smul_smul H.conj w.asIdeal, h, Ideal.smul_bot]
    refine ⟨⟨H.conj • w.asIdeal, inferInstance, hne⟩, HeightOneSpectrum.ext ?_, HeightOneSpectrum.ext ?_⟩
    · exact under_smul_of_fix H.conj (fun x => (H.conjE_mem_hostF_iff _).1 x.2) _
    · show (H.conj • w.asIdeal).under _ = u.asIdeal.under _
      rw [← hσ, smul_smul]
      refine under_smul_of_fix _ (fix_of_sqrt H _ ?_) _
      rw [AlgEquiv.mul_apply, hs, map_neg, conj_sqrt, neg_neg]

end GlobalTheory.PlaceOverPair
end

