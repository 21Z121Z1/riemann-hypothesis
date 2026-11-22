import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormConjugatesOverIdealClasses
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.RealMetaplecticRepresentationHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0150
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0433
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationModuleUnitDual

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanLogNormConjugatesOverIdealClassesStatement
section
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_log_norm_conjugates_over_ideal_classes : ∀ {K : Type} [Field K] [NumberField K] (φK : K →+* ℂ) (j₀ : ℂ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (β : ℂ) (F : (ℂ ≃+* ℂ) → ℝ), Module.finrank ℚ K = 2 → (starRingEnd ℂ).comp φK ≠ φK → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Equidistributed φK j₀ 𝔞 → IsAlgebraic ℚ β → β ≠ 0 → (∀ σ σ' : ℂ ≃+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ' → ClassGroup.mk K (𝔞 σ) = ClassGroup.mk K (𝔞 σ') → F σ = F σ') → (∀ σ : ℂ ≃+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK σ → Real.log ‖σ β‖ ≤ F σ) → ∃ rep : ClassGroup (𝓞 K) → (ℂ ≃+* ℂ), (∀ c, GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Fixes φK (rep c) ∧ ClassGroup.mk K (𝔞 (rep c)) = c) ∧ Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| ≤ (minpoly ℚ β).natDegree * ((∑ c, F (rep c)) / (NumberField.classNumber K : ℝ)) := by
  first | exact @GlobalTheory.GalMean.galmean | exact GlobalTheory.GalMean.galmean | (intros; apply GlobalTheory.GalMean.galmean <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHilbertLatticeTwistIffLift
section
set_option autoImplicit false

noncomputable section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam.TwistMem

variable {F : Type} [Field F] [NumberField F]

theorem vecMul_mem_std (B : Matrix (Fin 2) (Fin 2) ℤ) {y : Fin 2 → F} (hy : y ∈ stdLat F) :
    Matrix.vecMul y (B.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h0 := hy 0 (Set.mem_univ _)
  have h1 := hy 1 (Set.mem_univ _)
  have : Matrix.vecMul y (B.map (Int.cast : ℤ → F)) j = B 0 j • y 0 + B 1 j • y 1 := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  rw [this]
  exact Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ h0) (Submodule.smul_of_tower_mem _ _ h1)

theorem exists_lift_diff (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ,
      ((A.map (Int.cast : ℤ → ZMod N)).map (ZMod.cast : ZMod N → ℤ)).map (Int.cast : ℤ → F)
        = A.map (Int.cast : ℤ → F) + (N : F) • B.map (Int.cast : ℤ → F) := by
  have h : ∀ a : ℤ, ∃ b : ℤ, (ZMod.cast (a : ZMod N) : ℤ) = a + N * b := by
    intro a
    have h1 : ((a : ℤ) : ZMod N) = (((ZMod.cast (a : ZMod N) : ℤ) : ℤ) : ZMod N) := by
      simp
    obtain ⟨b, hb⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ N).1 h1
    exact ⟨b, by linarith⟩
  choose f hf using h
  refine ⟨A.map f, ?_⟩
  ext i j
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hf]
  push_cast
  ring

theorem vecMul_scalar (N : ℕ) (w : Fin 2 → F) :
    Matrix.vecMul w ((((N : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ))).map (Int.cast : ℤ → F)) = (N : F) • w := by
  ext j
  fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.one_apply, Matrix.natCast_apply, mul_comm]

theorem mem_twist_iff (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → F) (hL : L ≤ stdLat F) :
    (v ∈ twist N L (A.map (Int.cast : ℤ → ZMod N)) ↔
      ∃ y ∈ L, ∃ w ∈ stdLat F, v = Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) := by
  obtain ⟨B, hB⟩ := exists_lift_diff (F := F) N A
  unfold twist mulMat
  simp only [Submodule.mem_sup, Submodule.mem_map, LinearMap.restrictScalars_apply,
    Matrix.vecMulLinear_apply, hB, vecMul_scalar, Matrix.vecMul_add, Matrix.vecMul_smul]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨y, hy, Matrix.vecMul y (B.map (Int.cast : ℤ → F)) + w,
      Submodule.add_mem _ (vecMul_mem_std B (hL hy)) hw, ?_⟩
    rw [smul_add, add_assoc]
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨_, ⟨y, hy, rfl⟩, _, ⟨w - Matrix.vecMul y (B.map (Int.cast : ℤ → F)),
      Submodule.sub_mem _ hw (vecMul_mem_std B (hL hy)), rfl⟩, ?_⟩
    rw [smul_sub]
    abel

end GlobalTheory.HilbFam.TwistMem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulMatSmulOneIff
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem mem_mulMat_smul_one_iff {F : Type} [Field F] [NumberField F] (L : Lat F) (c : ℤ) (v : Fin 2 → F) :
    v ∈ mulMat L (c • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ↔ ∃ y ∈ L, v = (c : 𝓞 F) • y := by
  have h : ∀ y : Fin 2 → F,
      Matrix.vecMul y ((c • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → F)) = (c : 𝓞 F) • y := by
    intro y
    have hm : (c • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → F) = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [Int.cast_smul_eq_zsmul, hm, Matrix.vecMul_smul, Matrix.vecMul_one]
  unfold mulMat
  simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, h]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

theorem twist_one_of_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F),
    HasLevel N L → twist N L 1 = L := by
  intro F _ _ _ N L hL
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
      = (ZMod.cast (1 : ZMod N) : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  unfold twist
  rw [h1]
  apply le_antisymm
  · refine sup_le (fun v hv ↦ ?_) (fun v hv ↦ ?_)
    · obtain ⟨y, hy, rfl⟩ := (mem_mulMat_smul_one_iff _ _ _).1 hv
      exact L.smul_mem _ hy
    · obtain ⟨y, hy, rfl⟩ := (mem_mulMat_smul_one_iff _ _ _).1 hv
      simpa using hL.1 y hy
  · intro v hv
    by_cases hN : N = 1
    · subst hN
      refine Submodule.mem_sup_right ((mem_mulMat_smul_one_iff _ _ _).2 ⟨v, hL.2 hv, by simp⟩)
    · have hc : (ZMod.cast (1 : ZMod N) : ℤ) = 1 := by
        rcases N with _ | _ | N
        · rfl
        · exact absurd rfl hN
        · rw [ZMod.cast_eq_val, ZMod.val_one'' hN]; simp
      rw [hc]
      exact Submodule.mem_sup_left ((mem_mulMat_smul_one_iff _ _ _).2 ⟨v, hv, by simp⟩)

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTraceDualLocalizationIffForallRegularFormStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_traceDual_localization_iff_forall_regularForm_alt : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (p : Ideal A), p.IsPrime → p.height = 1 → ∀ z : K, (∀ b : B, ∃ r c : A, r ∉ p ∧ (r : F) * Algebra.trace F K (z * b) = c) ↔ ∀ Q : Ideal B, Q.IsPrime → (∀ a : A, ∀ b : B, (b : K) = algebraMap F K a → (b ∈ Q ↔ a ∈ p)) → (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) := by
  first | (exact @GlobalTheory.mem_traceDual_localization_iff_forall_regularForm) | (exact GlobalTheory.mem_traceDual_localization_iff_forall_regularForm) | (intros; apply GlobalTheory.mem_traceDual_localization_iff_forall_regularForm  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetaplecticGaussianNormalised
section
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

theorem metaplecticGaussianNormalised : ∀ (l : Type) [Fintype l] [DecidableEq l], ∃ (G : Type) (_ : Group G) (_ : TopologicalSpace G) (_ : IsTopologicalGroup G) (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)) (φ : Sch l), IsCoveringMap pr ∧ Function.Surjective pr ∧ (∃ ε : G, ε ≠ 1 ∧ (∀ g, pr g = 1 ↔ g = 1 ∨ g = ε) ∧ ∀ f, om ε f = -f) ∧ (∀ f : L2 l, Continuous fun g => om g f) ∧ (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) ∧ (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) ∧ (∀ x : EuclideanSpace ℝ l, φ x = cexp (-π * ((x.ofLp ⬝ᵥ x.ofLp : ℝ) : ℂ))) ∧ (∀ j : l, dRho (Pi.single (.inl j) 1) φ = I • dRho (Pi.single (.inr j) 1) φ) ∧ ∀ (g : G) (P : Matrix l l ℂ), (∀ a b, P a b = ((pr g).1 (.inl a) (.inl b) : ℂ) - I * ((pr g).1 (.inl a) (.inr b) : ℂ)) → omS g φ 0 ^ 2 * P.det = 1 := by
  intro l _ _
  have hS : CompanionTheory.ThKR.Mp.SecEx l := CompanionTheory.ThKR.Mp.secEx_of CompanionTheory.ThKR.Mp.mkElt CompanionTheory.ThKR.Mp.nrmUp
  have hO : CompanionTheory.ThKR.Mp.Surj l := CompanionTheory.ThKR.Mp.surj_of CompanionTheory.ThKR.Mp.ddNe hS
  have hC : CompanionTheory.ThKR.Mp.Cover l :=
    CompanionTheory.ThKR.Mp.cover_of CompanionTheory.ThKR.Mp.topG hO CompanionTheory.ThKR.Mp.ker hS CompanionTheory.ThKR.Mp.secDer
  haveI : IsTopologicalGroup (CompanionTheory.ThKR.Mp.G l) := CompanionTheory.ThKR.Mp.topG
  refine ⟨CompanionTheory.ThKR.Mp.G l, inferInstance, inferInstance, inferInstance, CompanionTheory.ThKR.Mp.pr, CompanionTheory.ThKR.Mp.om,
    CompanionTheory.ThKR.Mp.omS, CompanionTheory.ThKR.Mp.MpA.gs l, hC, hO, CompanionTheory.ThKR.Mp.ker, CompanionTheory.ThKR.Mp.continuous_om,
    CompanionTheory.ThKR.Mp.om_rho, CompanionTheory.ThKR.Mp.om_sch, ?_, ?_, ?_⟩
  · intro x
    rw [CompanionTheory.ThKR.Mp.MpA.gs, GroundTheory.Global.gaussianSchwartz_apply]
    have e : ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [dotProduct, sq]
    rw [e, Complex.ofReal_exp]
    push_cast
    ring_nf
  · intro j
    have h := CompanionTheory.ThKR.Mp.MpA.ann_gs (l := l) j
    have e1 : ((1 : CompanionTheory.ThKR.Mp.Sp l) : CompanionTheory.ThKR.Mp.Mat l) = 1 := rfl
    rw [e1, one_mulVec, one_mulVec] at h
    exact h
  · intro g P hP
    have h := CompanionTheory.ThKR.Mp.omS_nrm g 1 (CompanionTheory.ThKR.Mp.MpA.gs l) CompanionTheory.ThKR.Mp.MpA.ann_gs
    have e1 : ((1 : CompanionTheory.ThKR.Mp.Sp l) : CompanionTheory.ThKR.Mp.Mat l) = 1 := rfl
    rw [e1, Matrix.mul_one, CompanionTheory.ThKR.Mp.MpA.gs_zero, CompanionTheory.ThKR.Mp.MpA.dd_one, one_pow, one_mul] at h
    have eP : P = CompanionTheory.ThKR.Mp.upperParabolic (CompanionTheory.ThKR.Mp.pr g).1 := by
      ext a b; rw [hP]; rfl
    rw [eP]
    exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonZeroDivisorLocalizationGeneralOfNoetherian
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NzdDescent

open TensorProduct GlobalTheory.SmoothDescent

theorem model_data (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B] (b g : B) :
    ∃ (S B₁ : Type) (_ : CommRing S) (_ : IsNoetherianRing S) (_ : Algebra S A) (_ : CommRing B₁)
      (_ : Algebra S B₁) (_ : Algebra.Smooth S B₁) (e : A ⊗[S] B₁ ≃ₐ[A] B) (b₁ g₁ : B₁),
      Function.Injective (fun x : B₁ => e (1 ⊗ₜ x)) ∧ e (1 ⊗ₜ b₁) = b ∧ e (1 ⊗ₜ g₁) = g := by
  classical
  obtain ⟨A₀, B₀, _, _, h₀, hB, ⟨β⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A B
  haveI : IsNoetherianRing A₀ := isNoetherianRing_of_fg h₀
  obtain ⟨S, hS, hsub⟩ := exists_fg_subset_range_incl (C₁ := B₀) ({β b, β g} : Finset _)
  obtain ⟨b₁, hb₁⟩ := hsub (by simp : β b ∈ _)
  obtain ⟨g₁, hg₁⟩ := hsub (by simp : β g ∈ _)
  refine ⟨S, S ⊗[A₀] B₀, inferInstance, isNoetherianRing_of_fg hS, inferInstance, inferInstance,
    inferInstance, inferInstance,
    (Algebra.TensorProduct.cancelBaseChange A₀ S A A B₀).trans β.symm, b₁, g₁, ?_, ?_, ?_⟩
  · intro x y h
    simp only [AlgEquiv.trans_apply, cancel_one_tmul] at h
    exact incl_injective S (β.symm.injective h)
  · simp only [AlgEquiv.trans_apply, cancel_one_tmul]
    exact (congrArg β.symm hb₁).trans (β.symm_apply_apply b)
  · simp only [AlgEquiv.trans_apply, cancel_one_tmul]
    exact (congrArg β.symm hg₁).trans (β.symm_apply_apply g)

theorem of_model (hN : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0)) (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    (S B₁ : Type) (b g : B) [CommRing S] [IsNoetherianRing S] [Algebra S A] [CommRing B₁] [Algebra S B₁]
    [Algebra.Smooth S B₁] (e : A ⊗[S] B₁ ≃ₐ[A] B) (b₁ g₁ : B₁)
    (hinj : Function.Injective (fun x : B₁ => e (1 ⊗ₜ x))) (hb : e (1 ⊗ₜ b₁) = b) (hg : e (1 ⊗ₜ g₁) = g)
    (u : PrimeSpectrum B) (hgb : g * b = 0)
    (hmin : ∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes,
      Q ≤ u.asIdeal → g ∉ Q) :
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  let ι : B₁ →+* B := e.toAlgHom.toRingHom.comp
    (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).toRingHom
  have hι : ∀ x, ι x = e (1 ⊗ₜ x) := fun x => rfl
  have hιS : ∀ s : S, ι (algebraMap S B₁ s) = algebraMap A B (algebraMap S A s) := by
    intro s
    rw [hι, ← Algebra.TensorProduct.tmul_one_eq_one_tmul, ← Algebra.TensorProduct.algebraMap_apply,
      IsScalarTower.algebraMap_apply S A (A ⊗[S] B₁), AlgEquiv.commutes]
  have hgb₁ : g₁ * b₁ = 0 := by
    apply hinj
    show ι (g₁ * b₁) = ι 0
    rw [map_mul, hι, hι, hg, hb, hgb, map_zero]
  let u₁ : PrimeSpectrum B₁ := ⟨u.asIdeal.comap ι, Ideal.comap_isPrime _ _⟩
  have key := hN S B₁ b₁ g₁ u₁ hgb₁ ?_
  · obtain ⟨⟨t, ht⟩, htb⟩ := (IsLocalization.map_eq_zero_iff u₁.asIdeal.primeCompl _ b₁).mp key
    refine (IsLocalization.map_eq_zero_iff u.asIdeal.primeCompl _ b).mpr ⟨⟨ι t, ht⟩, ?_⟩
    show ι t * b = 0
    rw [← hb, ← hι, ← map_mul]
    simp only at htb
    rw [htb, map_zero]
  intro Q₁ hQ₁ hQ₁u hgQ₁
  haveI : Q₁.IsPrime := hQ₁.1.1
  let uT : Ideal (A ⊗[S] B₁) := u.asIdeal.comap e.toAlgHom.toRingHom
  haveI : uT.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨QT, hQTp, hQTu, hQT1, hQTA⟩ := GlobalTheory.T.exists_prime_le_comap_of_goingDown_tensor S A B₁ uT Q₁ (fun x hx => hQ₁u hx) (by
    apply le_antisymm
    · intro s hs
      have : algebraMap S B₁ s ∈ u₁.asIdeal := hQ₁u hs
      show e (algebraMap S (A ⊗[S] B₁) s) ∈ u.asIdeal
      rw [← (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).commutes]
      exact this
    · intro s hs
      apply hQ₁.1.2
      apply Ideal.mem_map_of_mem
      show ι (algebraMap S B₁ s) ∈ u.asIdeal
      have : e (algebraMap S (A ⊗[S] B₁) s) ∈ u.asIdeal := hs
      rwa [← (Algebra.TensorProduct.includeRight : B₁ →ₐ[S] A ⊗[S] B₁).commutes] at this)
  let Q' : Ideal B := QT.comap e.symm.toAlgHom.toRingHom
  haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hQ'u : Q' ≤ u.asIdeal := by
    intro x hx
    have := hQTu hx
    simpa [uT] using this
  have hmap : (u.asIdeal.comap (algebraMap A B)).map (algebraMap A B) ≤ Q' := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have h1 : a ∈ uT.comap (algebraMap A (A ⊗[S] B₁)) := by
      show e (algebraMap A _ a) ∈ u.asIdeal
      rw [AlgEquiv.commutes]; exact ha
    rw [← hQTA] at h1
    show e.symm (algebraMap A B a) ∈ QT
    rw [AlgEquiv.commutes]; exact h1
  obtain ⟨Q, hQmin, hQQ'⟩ := Ideal.exists_minimalPrimes_le hmap
  apply hmin Q hQmin (hQQ'.trans hQ'u)
  haveI : Q.IsPrime := hQmin.1.1
  have hJ : Q₁ ≤ Q.comap ι := by
    refine hQ₁.2 ⟨Ideal.comap_isPrime _ _, ?_⟩ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro s hs
      show ι (algebraMap S B₁ s) ∈ Q
      rw [hιS]
      apply hQmin.1.2
      apply Ideal.mem_map_of_mem
      show algebraMap A B (algebraMap S A s) ∈ u.asIdeal
      rw [← hιS]; exact hs
    · intro x hx
      rw [← hQT1]
      have := hQQ' hx
      have h2 : e.symm (e (1 ⊗ₜ x)) ∈ QT := this
      rw [AlgEquiv.symm_apply_apply] at h2
      exact h2
  have := hJ hgQ₁
  rw [← hg]; exact this

theorem of_noetherian : (∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0) →
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  intro hN A B _ _ _ _ b g u hgb hmin
  obtain ⟨S, B₁, _, _, _, _, _, _, e, b₁, g₁, hinj, hb, hg⟩ := model_data A B b g
  exact of_model hN A B S B₁ b g e b₁ g₁ hinj hb hg u hgb hmin

end GlobalTheory.NzdDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFactorPowTwoMul
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem omegaFactor_pow_two_mul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 : Frac F) (s : ℕ), (omegaFactor 𝔞 : ℂ) ^ (2 * s) = ((|(discr F : ℚ)| ^ s * FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) ^ (2 * s) : ℚ) : ℂ) := by
  intro F _ _ _ 𝔞 s
  have hsq : (omegaFactor 𝔞 : ℝ) ^ 2 = (|(discr F : ℝ)| * ((FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) ^ 2) := by
    simp only [omegaFactor, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm, ← Real.sqrt_eq_rpow]
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
  have h2 : (omegaFactor 𝔞 : ℂ) ^ (2 * s) = (((omegaFactor 𝔞 : ℝ) ^ 2) ^ s : ℝ) := by
    push_cast; rw [pow_mul]
  rw [h2, hsq]
  push_cast
  rw [mul_pow, ← pow_mul]
  congr 2
  rw [← Complex.ofReal_ratCast, Rat.cast_abs, Rat.cast_intCast]

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleInvertibleLocusIsCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneCocycle_invertibleLocus_isCoboundary_alt : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → F.obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), IsUnit (mp F u e) → y t t'' u (a ≫ b) = mp F (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = y t t' u a := by
  first | exact @GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary | exact GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary | (intros; apply GlobalTheory.CatCoh.Desc.Basis.oneCocycle_invertibleLocus_isCoboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleUpwardFamilyIsCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.van1_of_covBy_upward_sieve : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Van1 (G ⋙ F) Sg := by
  first | exact @GlobalTheory.CatCoh.Desc.Basis.oneCocycle_upwardFamily_isCoboundary | exact GlobalTheory.CatCoh.Desc.Basis.oneCocycle_upwardFamily_isCoboundary | (intros; apply GlobalTheory.CatCoh.Desc.Basis.oneCocycle_upwardFamily_isCoboundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValue
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem constTerm_eq_zetaVal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ) (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ), 1 ≤ k → ZetaVals k z → IsPartialZeta C Z → (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) = ((z C / 2 ^ Module.finrank ℚ F : ℚ) : ℂ) := by
  intro F _ _ _ k z C Z hk hz hZ
  obtain ⟨Z', hZ', e⟩ := hz C
  have hne : (1 - (k : ℂ)) ∈ ({1}ᶜ : Set ℂ) := by
    have : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    simpa using this
  have h : Z (1 - (k : ℂ)) = Z' (1 - (k : ℂ)) :=
    GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.IsClassZeta.eqOn (C := C) (Z := Z) (Z' := Z') hZ hZ' hne
  rw [h, e]
  push_cast
  rw [div_eq_mul_inv, mul_comm, inv_pow]

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationLatticeFgStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_lattice_fg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) → IsUnit (polMod L) → (polMod L * L).toAddSubgroup.FG := by
  first | exact @GlobalTheory.polMod_mul_fg | exact GlobalTheory.polMod_mul_fg | (intros; apply GlobalTheory.polMod_mul_fg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationModuleUnitDualStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_module_unit_dual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ (∀ x : 𝓞 E, (N : E) * algebraMap (𝓞 E) E x ∈ L) ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) →
    IsUnit (polMod L) ∧ polMod L * L = dualLat L := by
  first | exact @GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual | exact GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual | (intros; apply GlobalTheory.PolModLattice.polMod_isUnit_mul_eq_dual <;> assumption)
end

