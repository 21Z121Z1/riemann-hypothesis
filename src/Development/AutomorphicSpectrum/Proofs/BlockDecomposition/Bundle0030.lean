import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Bundle0001
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0004
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0005

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutatorCoerciveOnAnnihilator
section
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

theorem hs_eq_frobenius_sq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    Formalism.REAL.hs A = ‖A‖ ^ 2 := by
  have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt h0]
  rfl

theorem hs_le_commutator {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ)
    (h : ∀ A : Matrix (Fin m) (Fin m) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Matrix (Fin m) (Fin m) ℂ, A *ᵥ v = 0 →
      Formalism.REAL.hs A ≤ c * Formalism.REAL.hs (A * X - X * A) := by
  let Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) :=
    { toFun := fun A => (A * X - X * A, A *ᵥ v)
      map_add' := fun A B => by
        ext1
        · simp only [Prod.fst_add, add_mul, mul_add]; abel
        · simp only [Prod.snd_add, Matrix.add_mulVec]
      map_smul' := fun a A => by
        ext1
        · simp [smul_sub]
        · simp [Matrix.smul_mulVec] }
  have hker : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro A hA
    have h1 : A * X - X * A = 0 := congrArg Prod.fst hA
    have h2 : A *ᵥ v = 0 := congrArg Prod.snd hA
    exact h A (sub_eq_zero.mp h1) h2
  obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith Φ hker
  refine ⟨(K : ℝ) ^ 2, by positivity, fun A hA => ?_⟩
  have hle : ‖A‖ ≤ K * ‖A * X - X * A‖ := by
    have h3 := hanti.le_mul_dist A 0
    rw [map_zero, dist_zero_right, dist_zero_right] at h3
    have h4 : ‖Φ A‖ = ‖A * X - X * A‖ := by
      change ‖((A * X - X * A, A *ᵥ v) : Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ))‖ = _
      rw [hA, Prod.norm_def]
      simp
    rwa [h4] at h3
  rw [hs_eq_frobenius_sq, hs_eq_frobenius_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

end GlobalTheory.CompanionTheory.RgHeFrame
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutingHermitianSimultaneousDiag
section
open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.SimDiag

theorem exists_unitary_isDiag {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (hH : ∀ A ∈ S, Aᴴ = A) (hC : ∀ A ∈ S, ∀ B ∈ S, A * B = B * A) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A ∈ S, (Uᴴ * A * U).IsDiag := by
  classical
  let L : Matrix (Fin n) (Fin n) ℂ → (EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :=
    fun M => Matrix.toEuclideanLin M
  have hL : ∀ M v, L M v = WithLp.toLp 2 (M *ᵥ WithLp.ofLp v) := fun _ _ => rfl
  obtain ⟨m, b, hb⟩ := Formalism.IndefR.EigenDecomposition.exists_onb_of_commuting (L '' S)
    (by
      rintro _ ⟨M, hM, rfl⟩ _ ⟨N, hN, rfl⟩
      refine LinearMap.ext fun v => ?_
      change L M (L N v) = L N (L M v)
      simp only [hL, Matrix.mulVec_mulVec, hC M hM N hN])
    (by
      rintro _ ⟨M, hM, rfl⟩
      refine ⟨M, hM, ?_⟩
      change Matrix.toEuclideanLin M = LinearMap.adjoint (Matrix.toEuclideanLin M)
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hH M hM])
  have hm : m = n := by
    have := Module.finrank_eq_card_basis b.toBasis
    simpa [finrank_euclideanSpace] using this.symm
  subst hm
  have hinner : ∀ j k, ∑ i, star (WithLp.ofLp (b j) i) * WithLp.ofLp (b k) i =
      if j = k then 1 else 0 := by
    intro j k
    have := orthonormal_iff_ite.1 b.orthonormal j k
    rw [PiLp.inner_apply] at this
    simpa [RCLike.inner_apply, mul_comm] using this
  let U : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i k => WithLp.ofLp (b k) i
  refine ⟨U, ?_, fun A hA => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    ext j k
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply, U, Matrix.of_apply]
    exact hinner j k
  · intro j k hjk
    obtain ⟨μ, hμ⟩ := hb k (L A) ⟨A, hA, rfl⟩
    have hv : A *ᵥ WithLp.ofLp (b k) = μ • WithLp.ofLp (b k) := by
      have := congrArg WithLp.ofLp hμ
      simpa [hL] using this
    have hAU : ∀ i, (A * U) i k = μ * WithLp.ofLp (b k) i := by
      intro i
      have := congrFun hv i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, U] using this
    have h0 := hinner j k
    rw [if_neg hjk] at h0
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp_rw [hAU]
    calc ∑ i, Uᴴ j i * (μ * WithLp.ofLp (b k) i)
        = μ * ∑ i, star (WithLp.ofLp (b j) i) * WithLp.ofLp (b k) i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Matrix.conjTranspose_apply, U, Matrix.of_apply]
          ring
      _ = 0 := by rw [h0, mul_zero]

end GlobalTheory.CompanionTheory.SimDiag
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompInsertNthEq
section
open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.KAdjoint

variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]

theorem comp_insertNth_eq {m : ℕ} (b : β → P) (s : Fin (m + 1)) (i : β) (J : Fin m → β) :
    b ∘ (s.insertNth i J : Fin (m + 1) → β) = s.insertNth (b i) (b ∘ J) := by
  funext j
  refine Fin.succAboveCases s ?_ (fun k => ?_) j
  · simp
  · simp

theorem position_sum (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M)
    (h : ∀ X x y, B (T X x) y = B x (T' X y)) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M) (s : Fin (m + 1)) :
    ∑ I : Fin (m + 1) → β,
        B ((-1 : ℤ) ^ (s : ℕ) • T (b (I s)) (η (s.removeNth (b ∘ I)))) (θ (b ∘ I))
      = kIp B b η (kDel T' b θ) := by
  rw [← (Fin.insertNthEquiv (fun _ => β) s).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [kIp, kDel_apply, map_sum]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, comp_insertNth_eq, Fin.insertNth_apply_same,
    Fin.removeNth_insertNth]
  rw [← h, θ.map_insertNth]
  simp only [map_zsmul, LinearMap.smul_apply, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul]

theorem kIp_kD (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M)
    (h : ∀ X x y, B (T X x) y = B x (T' X y)) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M) :
    kIp B b (kD T η) θ = ((m : ℂ) + 1) * kIp B b η (kDel T' b θ) := by
  have hs : ∀ s : Fin (m + 1), ∑ I : Fin (m + 1) → β,
      B ((-1 : ℤ) ^ (s : ℕ) • T (b (I s)) (η (s.removeNth (b ∘ I)))) (θ (b ∘ I))
        = kIp B b η (kDel T' b θ) := fun s => position_sum B b T T' h η θ s
  simp only [kIp, kD_apply, Function.comp_apply, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  simp only [kIp] at hs
  rw [Finset.sum_congr rfl fun s _ => hs s]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.CompanionTheory.KAdjoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompKey
section
open MeasureTheory
open scoped ENNReal
open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KernelOperators

theorem comp_key (hB : KerBasic) (hR : RowInt) (hL : KernelL2RowsColumns) (hS : SchurInt) (hM : KerMul)
    (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ) (hψ : Tst ψ) (x : X.G) (f : X.G → ℂ)
    (hf : MemLp f 2 X.ν) :
    Integrable (fun z => ker X.Γ φ x z * ∫ y, ker X.Γ ψ z y * f y ∂X.ν) X.ν ∧
    ∫ z, ker X.Γ φ x z * (∫ y, ker X.Γ ψ z y * f y ∂X.ν) ∂X.ν
      = ∫ y, ker X.Γ (cv X.μ φ ψ) x y * f y ∂X.ν := by
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  obtain ⟨A, hA, hrow, hcol⟩ := hR X ψ hψ
  have hmeas : Measurable (Function.uncurry (ker X.Γ ψ)) := (hB X ψ hψ).2.1.measurable
  have hint := hS X.G X.ν (ker X.Γ ψ) A hmeas hA hrow hcol (fun z => ker X.Γ φ x z) f
    ((hL X φ hφ).2 x) hf
  have e1 : ∀ z, ∫ y, ker X.Γ φ x z * ker X.Γ ψ z y * f y ∂X.ν
      = ker X.Γ φ x z * ∫ y, ker X.Γ ψ z y * f y ∂X.ν := by
    intro z
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  constructor
  · have h := hint.integral_prod_left
    simpa only [e1] using h
  · have h := integral_integral_swap
      (f := fun z y => ker X.Γ φ x z * ker X.Γ ψ z y * f y) hint
    simp only [e1] at h
    rw [h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [integral_mul_const]
    rw [hM X φ ψ hφ hψ x y]

theorem opMul : KerBasic → KerLin → RowInt → KernelL2RowsColumns → SchurInt → CvTest → KerMul → OpMul := by
  intro hB hLin hR hL hS hC hM X ι _ Φ₁ Φ₂ T₁ T₂ h₁ h₂ o₁ o₂
  have tcv : ∀ i j k, Tst (cv X.μ (Φ₁ i k) (Φ₂ k j)) :=
    fun i j k => (hC X _ _ (h₁ i k) (h₂ k j)).1
  have lin : ∀ i j, Tst (fun y => ∑ k, cv X.μ (Φ₁ i k) (Φ₂ k j) y) ∧
      ∀ x y, ker X.Γ (fun y => ∑ k, cv X.μ (Φ₁ i k) (Φ₂ k j) y) x y
        = ∑ k, ker X.Γ (cv X.μ (Φ₁ i k) (Φ₂ k j)) x y := by
    intro i j
    have h := hLin X ι (fun k => cv X.μ (Φ₁ i k) (Φ₂ k j)) (fun _ => 1) (fun k => tcv i j k)
    simpa only [mul_one] using h
  refine ⟨fun i j => (lin i j).1, ?_⟩
  intro f i
  have a1 := o₁ (T₂ f) i
  show ((T₁ (T₂ f)) i : X.G → ℂ) =ᵐ[X.ν] _
  filter_upwards [a1] with x hx
  rw [hx]
  have hfj : ∀ j, MemLp (f j : X.G → ℂ) 2 X.ν := fun j => Lp.memLp _
  have step : ∀ k, ∫ z, ker X.Γ (Φ₁ i k) x z * ((T₂ f) k : X.G → ℂ) z ∂X.ν
      = ∑ j, ∫ y, ker X.Γ (cv X.μ (Φ₁ i k) (Φ₂ k j)) x y * (f j : X.G → ℂ) y ∂X.ν := by
    intro k
    have e : (fun z => ker X.Γ (Φ₁ i k) x z * ((T₂ f) k : X.G → ℂ) z) =ᵐ[X.ν]
        fun z => ∑ j, ker X.Γ (Φ₁ i k) x z *
          ∫ y, ker X.Γ (Φ₂ k j) z y * (f j : X.G → ℂ) y ∂X.ν := by
      filter_upwards [o₂ f k] with z hz
      rw [hz, Finset.mul_sum]
    rw [integral_congr_ae e, integral_finset_sum _ fun j _ =>
      (comp_key hB hR hL hS hM X _ _ (h₁ i k) (h₂ k j) x _ (hfj j)).1]
    exact Finset.sum_congr rfl fun j _ =>
      (comp_key hB hR hL hS hM X _ _ (h₁ i k) (h₂ k j) x _ (hfj j)).2
  rw [Finset.sum_congr rfl fun k _ => step k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [(lin i j).2, Finset.sum_mul]
  have hi : ∀ k, Integrable
      (fun y => ker X.Γ (cv X.μ (Φ₁ i k) (Φ₂ k j)) x y * (f j : X.G → ℂ) y) X.ν :=
    fun k => MemLp.integrable_mul ((hL X _ (tcv i j k)).2 x) (hfj j)
  exact (integral_finset_sum _ fun k _ => hi k).symm

end GlobalTheory.CompanionTheory.KernelOperators
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComparableQuotientOfValuation
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.ValQuot

theorem valuation_comparable_quotient : ∀ {S : Type} [CommRing S] (π : S), Val π → Val0 (S ⧸ Ideal.span {π}) := by
  intro S _ π hV f' g'
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f'
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g'
  have hpi : ∀ x : S, ∃ N : ℕ, π ^ N ∈ Ideal.span {x, π} := fun x =>
    ⟨1, Ideal.mem_span_pair.mpr ⟨0, 1, by ring⟩⟩
  obtain ⟨e₁, he1, h1f, h1π⟩ := hV f π (hpi f)
  obtain ⟨e₂, he2, h2g, h2π⟩ := hV g π (hpi g)
  obtain ⟨a1, ha1⟩ := Ideal.mem_span_singleton'.mp h1f
  obtain ⟨b1, hb1⟩ := Ideal.mem_span_singleton'.mp h1π
  obtain ⟨a2, ha2⟩ := Ideal.mem_span_singleton'.mp h2g
  have he1' : e₁ * e₁ = e₁ := he1
  have he2' : e₂ * e₂ = e₂ := he2
  obtain ⟨u, hu⟩ : ∃ u : S, u = (1 - e₁) * (1 - e₂) := ⟨_, rfl⟩
  have hu2 : u * u = u := by subst hu; linear_combination (1 - e₂) ^ 2 * he1' + (1 - e₁) * he2'
  have he1u : e₁ * u = 0 := by subst hu; linear_combination (-(1 - e₂)) * he1'
  have huπ : u * π = (1 - e₂) * b1 * f := by subst hu; linear_combination (-(1 - e₂)) * hb1
  obtain ⟨e₃, he3, h3, h3'⟩ := hV (u * f + (1 - u)) (u * g + (1 - u))
    ⟨1, Ideal.mem_span_pair.mpr ⟨(1 - e₂) * b1 * u + π * (1 - u), 0, by
      linear_combination ((1 - e₂) * b1 * f - (1 - e₂) * b1 - π * f + 2 * π) * hu2 - u * huπ⟩⟩
  have he3' : e₃ * e₃ = e₃ := he3
  obtain ⟨c3, hc3⟩ := Ideal.mem_span_singleton'.mp h3
  obtain ⟨d3, hd3⟩ := Ideal.mem_span_singleton'.mp h3'
  refine ⟨Ideal.Quotient.mk _ (e₁ + u * e₃), ?_, ?_, ?_⟩
  · show Ideal.Quotient.mk _ (e₁ + u * e₃) * Ideal.Quotient.mk _ (e₁ + u * e₃) =
      Ideal.Quotient.mk _ (e₁ + u * e₃)
    rw [← map_mul]
    exact congrArg (Ideal.Quotient.mk _)
      (by linear_combination he1' + 2 * e₃ * he1u + e₃ ^ 2 * hu2 + u * he3')
  · refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (c3 * u), ?_⟩
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton']
    exact ⟨-a1, by linear_combination -ha1 - u * hc3 + (c3 * g - c3 - e₃ * f + e₃) * hu2⟩
  · refine Ideal.mem_span_singleton'.mpr ⟨Ideal.Quotient.mk _ (d3 * u), ?_⟩
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {π})), ← map_sub, ← map_mul, ← map_mul, Ideal.Quotient.eq,
      Ideal.mem_span_singleton']
    exact ⟨-((1 - e₁) * a2), by
      linear_combination -(1 - e₁) * ha2 - g * hu - u * hd3 + (d3 * f - d3 - (1 - e₃) * g + (1 - e₃)) * hu2⟩

end GlobalTheory.CompanionTheory.ValQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompletionComplete
section
set_option autoImplicit false

noncomputable section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.AdicCompl

theorem completion_complete (B : Type) [CommRing B] (π : B) :
    IsAdicComplete (Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π})
      (AdicCompletion (Ideal.span {π}) B) := by
  have h := AdicCompletion.isAdicComplete (R := B) (I := Ideal.span {π}) (M := B)
    (Submodule.fg_span_singleton _)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (Ideal.span {π}) B)] at h
  simpa [Ideal.map_span] using h

theorem completion_surj (B : Type) [CommRing B] (π : B) (M : ℕ)
    (y : AdicCompletion (Ideal.span {π}) B) :
    ∃ x : B, y - algebraMap B (AdicCompletion (Ideal.span {π}) B) x ∈
      Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π ^ M} := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (y.1 M)
  refine ⟨a, ?_⟩
  have hx : y - algebraMap B (AdicCompletion (Ideal.span {π}) B) a ∈
      ((Ideal.span {π}) ^ M).map (algebraMap B (AdicCompletion (Ideal.span {π}) B)) := by
    rw [← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map,
      AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton π),
      AdicCompletion.algebraMap_apply]
    simpa [AdicCompletion.eval, sub_eq_zero] using ha.symm
  rwa [Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, map_pow] at hx

theorem completion_inj (B : Type) [CommRing B] (π : B) (M : ℕ) (x : B)
    (h : algebraMap B (AdicCompletion (Ideal.span {π}) B) x ∈
      Ideal.span {algebraMap B (AdicCompletion (Ideal.span {π}) B) π ^ M}) :
    x ∈ Ideal.span {π ^ M} := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h
  have h1 := congrArg (AdicCompletion.evalₐ (Ideal.span {π}) M) hz
  have hf : Ideal.Quotient.mk (Ideal.span {π} ^ M) (π ^ M) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (by
      rw [Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
  rw [map_mul, map_pow, AlgHom.commutes, ← map_pow, AlgHom.commutes, Ideal.Quotient.algebraMap_eq,
    hf, mul_zero] at h1
  rw [← Ideal.span_singleton_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.1 h1.symm

theorem exists_isCompl : ∀ (B : Type) [CommRing B] (π : B),
    ∃ (T : Type) (_ : CommRing T) (g : B →+* T), IsCompl π g := by
  intro B _ π
  exact ⟨AdicCompletion (Ideal.span {π}) B, inferInstance,
    algebraMap B (AdicCompletion (Ideal.span {π}) B),
    { compl := completion_complete B π
      surj := completion_surj B π
      inj := completion_inj B π }⟩

end GlobalTheory.CompanionTheory.AdicCompl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBlkM
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

open MeasureTheory Matrix
open scoped ComplexConjugate

def blkM {n : ℕ} (b : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (d : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks b (Matrix.replicateCol (Fin 1) u) (Matrix.replicateRow (Fin 1) (star u))
      (Matrix.of fun _ _ => (d : ℂ)))

theorem blkM_mem {n : ℕ} (b : hermC n) (u : Fin n → ℂ) (d : ℝ) :
    blkM (b : Matrix (Fin n) (Fin n) ℂ) u d ∈ hermC (n + 1) := by
  have hb : (b : Matrix (Fin n) (Fin n) ℂ).IsHermitian := mem_hermC.1 b.2
  rw [mem_hermC]
  unfold blkM
  simp only [Matrix.reindex_apply]
  apply Matrix.IsHermitian.submatrix
  apply Matrix.IsHermitian.fromBlocks hb
  · ext i j
    simp [Matrix.conjTranspose_apply]
  · ext i j
    simp [Matrix.conjTranspose_apply]

def blk {n : ℕ} (b : hermC n) (u : Fin n → ℂ) (d : ℝ) : hermC (n + 1) :=
  ⟨blkM (b : Matrix (Fin n) (Fin n) ℂ) u d, blkM_mem b u d⟩

theorem continuous_blkM {n : ℕ} :
    Continuous (fun x : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) × ℝ => blkM x.1 x.2.1 x.2.2) := by
  refine continuous_matrix fun i j => ?_
  unfold blkM
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases h1 : finSumFinEquiv.symm i with i' | i' <;> rcases h2 : finSumFinEquiv.symm j with j' | j' <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.replicateCol_apply, Matrix.replicateRow_apply, Pi.star_apply,
      Matrix.of_apply]
  all_goals fun_prop

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousIteratedDerivHolomorphicFamilyStatement
section
open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_iteratedDeriv_holomorphic_family : ∀ {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z := by
  first | exact @GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family | exact GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family | (intros; apply GlobalTheory.CompanionTheory.HolFamily.continuous_iteratedDeriv_family <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContourShiftParametrisedIntegral
section
universe u

namespace GlobalTheory.CompanionTheory.EisTube

theorem laplaceEntire_firstCountable : ∀ (ι : Type) [Fintype ι] (P : Type u) [TopologicalSpace P] [FirstCountableTopology P] (h : P → ℝ), (∀ p, 0 ≤ h p) →
    (∀ p, ∃ U ∈ nhds p, BddAbove (h '' U)) →
    ∀ ψ : P → (ι → ℝ) → ℂ, (∀ p, MeasureTheory.AEStronglyMeasurable (ψ p)) →
    (∀ t, Continuous (fun p => ψ p t)) →
    (∀ v : ι → ℝ, ∃ C : ℝ, ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, v i * t i))) →
    (∀ p (z : ι → ℂ), MeasureTheory.Integrable
        (fun t : ι → ℝ => ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    (∀ p, Differentiable ℂ (fun z : ι → ℂ =>
        ∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i))) ∧
    Continuous (fun q : (ι → ℂ) × P =>
        ∫ t : ι → ℝ, ψ q.2 t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, q.1 i * t i)) ∧
    (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p,
        ‖∫ t : ι → ℝ, ψ p t * Complex.exp (2 * (Real.pi : ℂ) * ∑ i, z i * t i)‖ ≤ C * h p) :=
  fun ι _ P _ _ h hh hloc ψ hm hc hv => laplaceEntire ι P h hh hloc ψ hm hc hv

end GlobalTheory.CompanionTheory.EisTube
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContourShiftTubeDomainStatement
section
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contour_shift_tube_domain : ∀ (ι : Type) [Fintype ι] (Ω : Set (ι → ℝ)), IsOpen Ω → IsPreconnected Ω →
    ∀ H : (ι → ℂ) → ℂ, DifferentiableOn ℂ H {z | (fun i => (z i).re) ∈ Ω} →
    (∀ K ⊆ Ω, IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ y : ι → ℝ,
      ‖H (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I)‖ ≤ C * Real.exp (-(∑ i, y i ^ 2) / 2)) →
    ∀ x₁ ∈ Ω, ∀ x₂ ∈ Ω,
      (∫ y : ι → ℝ, H (fun i => (x₁ i : ℂ) + (y i : ℂ) * Complex.I)) =
        ∫ y : ι → ℝ, H (fun i => (x₂ i : ℂ) + (y i : ℂ) * Complex.I) := by
  first | exact @GlobalTheory.CompanionTheory.EisTube.tubeShift | exact GlobalTheory.CompanionTheory.EisTube.tubeShift | (intros; apply GlobalTheory.CompanionTheory.EisTube.tubeShift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSeriesSummableShifted
section
open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis in

theorem cross_stage_pos : PositivityTheory.RgEis.PiLocalization₂ → ∀ (G : Type) [Group G] (Γ Q P : Subgroup G) (ξ lam : G → ℝ) (t : ℝ),
    P ≤ Q → (∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x) → (∀ γ ∈ Γ, γ ∈ P → ∀ x, lam (γ * x) = lam x) →
    PositivityTheory.RgEis.Conv Γ P (fun x => lam x + t * ξ x) → ∀ g : G,
    Summable fun r : PositivityTheory.RgEis.Cos (Γ ⊓ Q) Γ => Real.exp (t * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos (Γ ⊓ Q) P lam (PositivityTheory.RgEis.rep r * g) := by
  intro hS G _ Γ Q P ξ lam t hPQ hξ hlam hc g
  have key := (hS G ℝ P (Γ ⊓ Q) Γ (fun x => Real.exp (lam x + t * ξ x)) inf_le_left
    (fun γ h1 h2 => ⟨h1, hPQ h2⟩)
    (fun γ h1 h2 x => by
      show Real.exp (lam (γ * x) + t * ξ (γ * x)) = Real.exp (lam x + t * ξ x)
      rw [hlam γ h1 h2 x, hξ γ h1 (hPQ h2) x]) g
    (by
      have h := hc g
      refine h.congr (fun q => ?_)
      simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)])).2.1
  refine key.congr (fun r => ?_)
  rw [pos, ← tsum_mul_left]
  refine tsum_congr (fun q => ?_)
  have hq : rep q ∈ Γ ⊓ Q := (Quotient.out q).2
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hξ _ hq.1 hq.2, ← Real.exp_add, add_comm]

end GlobalTheory.CompanionTheory.RgEis
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetSumTranslateInvariantStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_sum_translate_invariant : ∀ {X : Type} [AddCommGroup X] {M : Type} [AddCommMonoid M] {A H : AddSubgroup X}, H ≤ A → ∀ {T : Finset X}, (∀ t ∈ T, t ∈ A) → (∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H) → ∀ (F : X → M), (∀ a, ∀ h ∈ H, F (a + h) = F a) → ∀ {a : X}, a ∈ A → ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by
  first | exact @GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal | exact GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal | (intros; apply GlobalTheory.CompanionTheory.Transversal.sum_add_eq_sum_of_transversal <;> assumption)
end

