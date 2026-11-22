import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftSquareZeroOfFormallyEtaleAwayDepth
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0150
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import ReciprocityTheory.Chebotarev.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0002
import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertSectionsRankAtStalkStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertSections_rankAtStalk : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (r : ℕ) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W : Z.affineOpens) (P : PrimeSpectrum Γ(Z, W)), Module.rankAtStalk (GlobalTheory.HilbAff.Sec A B y W) P = r := by
  first | (exact @GlobalTheory.HilbAff.rankAtStalk_sec) | (exact GlobalTheory.HilbAff.rankAtStalk_sec) | (intros; apply GlobalTheory.HilbAff.rankAtStalk_sec  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertTensorToSubschemeSectionsSurjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineHilbertTensorToSubschemeSections_surjective : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (I : (pullback (GlobalTheory.HilbAff.str A B) g).IdealSheafData) (U : T.affineOpens), Function.Surjective (GlobalTheory.HilbAff.kappa A B g I U) := by
  first | (exact @GlobalTheory.HilbAff.kappa_surjective) | (exact GlobalTheory.HilbAff.kappa_surjective) | (intros; apply GlobalTheory.HilbAff.kappa_surjective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPropertyOfLeKerAppStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PtClosed
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affinePointProperty_of_le_ker_app : ∀ (S : Scheme.{0}) (P : ∀ (R' : Type) [CommRing R'], (Sp R' ⟶ S) → Prop),
  (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S) (t : Finset R'), Ideal.span (t : Set R') = ⊤ →
     (∀ r ∈ t, P (Localization.Away r) (spMap (algebraMap R' (Localization.Away r)) ≫ x)) → P R' x) →
  (∀ (V : S.Opens) (hV : IsAffineOpen V), Represents (ptQ P V hV) (killIdeal (ptQ P V hV))) →
  ∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ S),
    (∀ (V : S.Opens) (hV : IsAffineOpen V), killIdeal (ptQ P V hV) ≤ RingHom.ker (x.app V).hom) → P R' x := by
  first | (exact @GlobalTheory.PtClosed.of_le_ker_app) | (exact GlobalTheory.PtClosed.of_le_ker_app) | (intros; apply GlobalTheory.PtClosed.of_le_ker_app  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrameSpanGeneration
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem frame_of_spanning : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N d h : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (ρ : Λ →+* Matrix (Fin h) (Fin h) (Ainf p O)) (x : Fin N → Fin h → Ainf p O), (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = ofPadic p O c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) → h = N * d → Submodule.span (Ainf p O) (Set.range fun ij : Fin N × Fin d => ρ (b ij.2) *ᵥ x ij.1) = ⊤ → ∃ e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O), IsFrame ρ e ∧ ∀ (i : Fin N) (l : Λ), e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = ρ l *ᵥ x i := by
  intro p _ O _ _ _ Λ _ _ N d h b ρ x hsc hh hspan
  subst hh
  classical
  let bR : Module.Basis (Fin d) (Ainf p O) (RL p O Λ) := Algebra.TensorProduct.basis (Ainf p O) b
  let bP := Pi.basis (fun _ : Fin N => bR)
  let L : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin (N * d) → Ainf p O) :=
    bP.constr (Ainf p O) (fun ij => ρ (b ij.2) *ᵥ x ij.1)
  have hL : ∀ i j, L (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j)) = ρ (b j) *ᵥ x i := by
    intro i j
    have hb : Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) = bP ⟨i, j⟩ := by
      simp [bP, bR, Pi.basis_apply, Algebra.TensorProduct.basis_apply]
    rw [hb]
    exact bP.constr_basis (Ainf p O) (fun ij : (Σ _ : Fin N, Fin d) => ρ (b ij.2) *ᵥ x ij.1) ⟨i, j⟩
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact ⟨_, hL i j⟩
  let σ : (Σ _ : Fin N, Fin d) ≃ Fin (N * d) := (Equiv.sigmaEquivProd _ _).trans finProdFinEquiv
  let E := (bP.reindex σ).equivFun
  have hinj : Function.Injective L := by
    have hf : Function.Surjective (L ∘ₗ E.symm.toLinearMap) := by
      intro y; obtain ⟨w, rfl⟩ := hsurj y; exact ⟨E w, by simp⟩
    have hi := OrzechProperty.injective_of_surjective_endomorphism _ hf
    intro u v huv
    have : E u = E v := hi (by simpa using huv)
    exact E.injective this
  let e := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  have he : ∀ w, e w = L w := fun w => rfl
  have hform : ∀ (i : Fin N) (l : Λ), e (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)) = ρ l *ᵥ x i := by
    intro i l
    rw [he]
    have hps : ∀ (f : Fin d → RL p O Λ), Pi.single i (∑ j, f j) = ∑ j, Pi.single (M := fun _ : Fin N => RL p O Λ) i (f j) :=
      fun f => map_sum (AddMonoidHom.single (fun _ : Fin N => RL p O Λ) i) f _
    rw [← b.sum_repr l, TensorProduct.tmul_sum, hps, map_sum, map_sum, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun j _ => ?_
    set c := (b.repr l) j
    have h1 : c • ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) = ofPadic p O c • ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) :=
      (algebraMap_smul (Ainf p O) c _).symm
    have h2 : Pi.single i (ofPadic p O c • ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j))
        = ofPadic p O c • Pi.single (M := fun _ : Fin N => RL p O Λ) i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) := by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [hk]
    rw [TensorProduct.tmul_smul, h1, h2, map_smul, hL, Algebra.smul_def c (b j), map_mul, hsc,
      smul_mul_assoc, one_mul, Matrix.smul_mulVec]
  refine ⟨e, ?_, hform⟩
  intro l w
  let f1 : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin (N * d) → Ainf p O) :=
    e.toLinearMap ∘ₗ DistribMulAction.toLinearMap (Ainf p O) (Fin N → RL p O Λ)
      ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l)
  let f2 : (Fin N → RL p O Λ) →ₗ[Ainf p O] (Fin (N * d) → Ainf p O) :=
    (Matrix.mulVecLin (ρ l)) ∘ₗ e.toLinearMap
  have hf : f1 = f2 := by
    refine bP.ext fun ij => ?_
    obtain ⟨i, j⟩ := ij
    have hb : bP ⟨i, j⟩ = Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) := by
      simp [bP, bR, Pi.basis_apply, Algebra.TensorProduct.basis_apply]
    have hs : ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • Pi.single (M := fun _ : Fin N => RL p O Λ) i
        ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] b j) = Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] (l * b j)) := by
      funext k; by_cases hk : k = i
      · subst hk; simp [Algebra.TensorProduct.tmul_mul_tmul]
      · simp [hk]
    show e (((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l) • bP ⟨i, j⟩) = ρ l *ᵥ e (bP ⟨i, j⟩)
    simp only [ hb, hs,
      LinearEquiv.coe_coe, hform, Matrix.mulVecLin_apply, map_mul, Matrix.mulVec_mulVec]
  exact LinearMap.congr_fun hf w

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfIsDomainMuNeZeroStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_isDomain_mu_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → IsDomain (Ainf p O) ∧ mu ε ≠ 0 := by
  first | exact @GlobalTheory.ainf_isDomain_and_mu_ne_zero | exact GlobalTheory.ainf_isDomain_and_mu_ne_zero | (intros; apply GlobalTheory.ainf_isDomain_and_mu_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomEqMulPowOfEqLocalizationAway
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem algHom_eq_mul_pow_of_eq_localizationAway :
    ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FiniteType R' A] (χ₁ χ₂ : A →ₐ[R'] S) (g : S),
    (∀ x, algebraMap S (Localization.Away g) (χ₁ x) = algebraMap S (Localization.Away g) (χ₂ x)) →
    ∃ N : ℕ, ∀ x, g ^ N * χ₁ x = g ^ N * χ₂ x := by
  intro R' A S _ _ _ _ _ _ χ₁ χ₂ g h
  have key : ∀ x, ∃ n : ℕ, g ^ n * χ₁ x = g ^ n * χ₂ x := by
    intro x
    obtain ⟨⟨c, hc⟩, hcx⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers g) (Localization.Away g)).1 (h x)
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hc
    exact ⟨n, hcx⟩
  choose n hn using key
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' A).FG)
  refine ⟨∑ x ∈ s, n x, fun x => ?_⟩
  set N := ∑ x ∈ s, n x
  have hx : x ∈ Algebra.adjoin R' (s : Set A) := by rw [hs]; exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hxs =>
    have hle : n x ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxs
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, mul_assoc, hn x]
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]
  | add x y _ _ hx hy => rw [map_add, map_add, mul_add, mul_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul]
    calc g ^ N * (χ₁ x * χ₁ y) = χ₁ x * (g ^ N * χ₁ y) := by ring
      _ = χ₁ x * (g ^ N * χ₂ y) := by rw [hy]
      _ = (g ^ N * χ₁ x) * χ₂ y := by ring
      _ = (g ^ N * χ₂ x) * χ₂ y := by rw [hx]
      _ = g ^ N * (χ₂ x * χ₂ y) := by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftSquareZeroOfFormallyEtaleAwayDepthStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algHom_lift_squareZero_of_formallyEtale_away_depth : ∀ (R : Type) [CommRing R] [IsLocalRing R] (A : Type) [CommRing A] [Algebra R A], (∀ g ∈ maximalIdeal R, Algebra.FormallyEtale (Localization.Away g) (TensorProduct R (Localization.Away g) A)) → ∀ (S T : Type) [CommRing S] [Algebra R S] [CommRing T] [Algebra R T], ReciprocityTheory.CA.ModDepthGE R S 2 → ReciprocityTheory.CA.ModDepthGE R T 1 → ∀ (π : S →ₐ[R] T), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (φ : A →ₐ[R] T), ∃ ψ : A →ₐ[R] S, π.comp ψ = φ := by
  first | exact @GlobalTheory.SquareZeroLift.squareZeroLift | exact GlobalTheory.SquareZeroLift.squareZeroLift | (intros; apply GlobalTheory.SquareZeroLift.squareZeroLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomQuotientSpanPowEqOfEtaleLowStatement
section
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algHom_quotient_span_pow_eq_of_etaleLow : ∀ (A R C : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing C] [Algebra R C] (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    GlobalTheory.GoodEtale.EtaleLow A R C →
    ∀ (n : ℕ) (f f' : C →ₐ[R] R ⧸ Ideal.span {t} ^ n),
      (∀ c : C, f c - f' c ∈ Ideal.span {Ideal.Quotient.mk (Ideal.span {t} ^ n) t}) → f = f' := by
  first | (exact @GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow) | (exact GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow) | (intros; apply GlobalTheory.GoodEtaleSection.algHom_quot_eq_of_etaleLow  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraNormRatGaussianExtensionOfPair
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.GaussExt

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

theorem X_sq_add_one_ne_zero : (X ^ 2 + 1 : F[X]) ≠ 0 := Monic.ne_zero (by monicity!)

theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!

def basisOneI : Module.Basis (Fin 2) F (Ext F) :=
  (AdjoinRoot.powerBasis (X_sq_add_one_ne_zero F)).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis_dim, natDegree_X_sq_add_one]))

theorem basisOneI_apply (j : Fin 2) : basisOneI F j = ii F ^ (j : ℕ) := by
  simp [basisOneI, Module.Basis.reindex_apply, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen, ii]

theorem basisOneI_zero : basisOneI F 0 = 1 := by simp [basisOneI_apply]
theorem basisOneI_one : basisOneI F 1 = ii F := by simp [basisOneI_apply]

theorem gEmb_eq (a b : F) : gEmb F (a, b) = a • basisOneI F 0 + b • basisOneI F 1 := by
  simp [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def]

theorem gEmb_mul_ii (a b : F) : gEmb F (a, b) * ii F = (-b) • basisOneI F 0 + a • basisOneI F 1 := by
  simp only [gEmb, basisOneI_zero, basisOneI_one, Algebra.smul_def, map_neg]
  linear_combination (algebraMap F (Ext F) b) * ii_sq F

theorem norm_gEmb_F (a b : F) : Algebra.norm F (gEmb F (a, b)) = a ^ 2 + b ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (basisOneI F), Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul,
    LinearMap.mul_apply']
  rw [basisOneI_zero, mul_one, basisOneI_one, gEmb_mul_ii, gEmb_eq]
  simp [Module.Basis.repr_self, Finsupp.single_apply]
  ring

theorem norm_gEmb (a b : F) :
    ((Algebra.norm ℚ (gEmb F (a, b)) : ℚ) : ℝ) = ∏ τ : F →+* ℝ, ((τ a) ^ 2 + (τ b) ^ 2) := by
  rw [← Algebra.norm_norm (S := F), norm_gEmb_F]
  have h := prod_emb (F := F) (a ^ 2 + b ^ 2)
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, ← h, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp

end GlobalTheory.GaussExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
section
namespace GlobalTheory.LogResInt

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions
open scoped ENNReal

noncomputable section

variable {d n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def chartSumInt (B : FinHolAtlas n Y) (Φ : LocPot Y) (U : Set Y) (f : Y → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j, ∫⁻ w in (B.chart j).target ∩ (B.chart j).symm ⁻¹' U,
    f ((B.chart j).symm w) * ‖locDens B (fun _ => Φ) j w‖ₑ

def IsJointSNC (B : FinHolAtlas n Y) (μ : Y → X) {q r : ℕ} (L : Fin q → LocPot X)
    (t : Fin q → X → X → ℂ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ) : Prop :=
  ∀ y, ∃ χ : OpenPartialHomeomorph Y (Fin n → ℂ), IsCompatChart B χ ∧ y ∈ χ.source ∧
    ∃ κ : Fin r → Option (Fin n), (∀ k k' a, κ k = some a → κ k' = some a → k = k') ∧
      (∀ k, W k ∩ χ.source = {w ∈ χ.source | ∃ a, κ k = some a ∧ χ w a = 0}) ∧
      ∀ i, χ.source ⊆ μ ⁻¹' (L i).U (μ y) ∧ ∃ u : Y → ℂ, B.HoloOn χ.source u ∧
        (∀ w ∈ χ.source, u w ≠ 0) ∧
        ∀ w ∈ χ.source, t i (μ y) (μ w) = u w * ∏ k, (match κ k with
          | some a => χ w a ^ e i k
          | none => 1)

def RankDropAlong (A : FinHolAtlas d X) (μ : Y → X) (B : FinHolAtlas n Y) (V : Set Y) : Prop :=
  ∀ w ∈ V, ∀ (χ : OpenPartialHomeomorph Y (Fin n → ℂ)) (a : Fin n), IsCompatChart B χ → w ∈ χ.source →
    V ∩ χ.source = {w' ∈ χ.source | χ w' a = 0} →
    Module.finrank ℂ (LinearMap.range
      (((fderiv ℂ (fun z => A.chart (chartIdx A (μ w)) (μ (χ.symm z))) (χ w) :
          (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)).comp
        (LinearMap.ker (LinearMap.proj a : (Fin n → ℂ) →ₗ[ℂ] ℂ)).subtype)) < n - 1

def AnalyticLogResolution : Prop :=
  ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X),
    IsProjective A →
  ∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
  ∀ (q : ℕ) (L : Fin q → LocPot X) (t : Fin q → X → X → ℂ),
    (∀ i, IsPotential A (L i) ∧ IsSection A (L i) (t i) ∧ ∃ y ∈ Z, t i y y ≠ 0) →
  ∃ (Y : Type) (_ : TopologicalSpace Y) (_ : CompactSpace Y) (_ : T2Space Y) (B : FinHolAtlas n Y)
    (μ : Y → X) (_ : HoloMap B A μ) (S : Set X) (r : ℕ) (W : Fin r → Set Y) (e : Fin q → Fin r → ℕ)
    (J : Finset (Fin r)),
    IsProjective B ∧ Set.range μ = Z ∧ A.IsAnalyticSubset S ∧ Z \ S ⊆ regularLocus A Z n ∧
    Z ⊆ closure (Z \ S) ∧ Set.InjOn μ (μ ⁻¹' S)ᶜ ∧
    (∀ y, y ∉ μ ⁻¹' S → ∀ j, y ∈ (B.chart j).source → ∀ v : Fin n → ℂ,
      fderiv ℂ (fun w => A.chart (chartIdx A (μ y)) (μ ((B.chart j).symm w))) (B.chart j y) v = 0 →
        v = 0) ∧
    μ ⁻¹' S = ⋃ k ∈ J, W k ∧ IsJointSNC B μ L t W e

end

end GlobalTheory.LogResInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorQuotientSmulTopOfFree
section
open IsLocalRing RingTheory.Sequence Pointwise

namespace GlobalTheory.AnnRegSeq

theorem free_of_maximalIdeal_eq_bot {B M : Type} [CommRing B] [IsLocalRing B] [AddCommGroup M]
    [Module B M] (hm : maximalIdeal B = ⊥) : Module.Free B M := by
  have hF : IsField B := IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm
  letI := hF.toField
  exact Module.Free.of_divisionRing B M

theorem maximalIdeal_eq_bot_of_le_sq {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (h : maximalIdeal B ≤ maximalIdeal B ^ 2) : maximalIdeal B = ⊥ :=
  Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal B) (maximalIdeal B)
    (maximalIdeal B).fg_of_isNoetherianRing (by rwa [smul_eq_mul, ← pow_two])
    (maximalIdeal_le_jacobson ⊥)

theorem exists_isSMulRegular_notMem_sq {B M : Type} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
    (hass : maximalIdeal B ∉ associatedPrimes B M) (hsq : ¬ maximalIdeal B ≤ maximalIdeal B ^ 2) :
    ∃ x ∈ maximalIdeal B, x ∉ maximalIdeal B ^ 2 ∧ IsSMulRegular M x := by
  by_contra hcon
  push_neg at hcon
  have hsub : ((maximalIdeal B : Ideal B) : Set B) ⊆
      ⋃ p ∈ insert (maximalIdeal B ^ 2) (associatedPrimes B M), (id p : Set B) := by
    intro z hz
    rw [Set.biUnion_insert]
    by_cases h2 : z ∈ maximalIdeal B ^ 2
    · exact Or.inl h2
    · right
      have : z ∈ ({r : B | IsSMulRegular M r}ᶜ) := hcon z hz h2
      rwa [← biUnion_associatedPrimes_eq_compl_regular B M] at this
  obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite ((associatedPrimes.finite B M).insert _)
    (f := id) (maximalIdeal B ^ 2) (maximalIdeal B ^ 2) (fun i hi h1 _ => by
      rcases hi with rfl | hi
      · exact absurd rfl h1
      · exact hi.isPrime)).mp hsub
  rcases hp with rfl | hp
  · exact hsq hle
  · have : p = maximalIdeal B := le_antisymm (le_maximalIdeal hp.isPrime.ne_top) hle
    exact hass (this ▸ hp)

theorem free_of_free_quotient {B M : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    [AddCommGroup M] [Module B M] [Module.Finite B M] {x : B} (hx : x ∈ maximalIdeal B)
    (reg : IsSMulRegular M x)
    [Module.Free (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M))] :
    Module.Free B M := by
  set I : Ideal B := Ideal.span {x} with hI
  set P : Submodule B M := I • ⊤ with hP
  have hIj : I ≤ (⊥ : Ideal B).jacobson := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    exact maximalIdeal_le_jacobson _ hx
  haveI : IsLocalRing (B ⧸ I) :=
    ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
  haveI : Module.Finite (B ⧸ I) (M ⧸ P) := Module.Finite.of_restrictScalars_finite B _ _
  let b := Module.finBasis (B ⧸ I) (M ⧸ P)
  set r := Module.finrank (B ⧸ I) (M ⧸ P)
  choose v hv using fun i => Submodule.Quotient.mk_surjective P (b i)
  let φ : (Fin r → B) →ₗ[B] M := Fintype.linearCombination B v
  have hφ : ∀ c, φ c = ∑ i, c i • v i := fun c => by simp [φ, Fintype.linearCombination_apply]
  have hmk : ∀ c : Fin r → B, (Submodule.Quotient.mk (φ c) : M ⧸ P) =
      ∑ i, Ideal.Quotient.mk I (c i) • b i := by
    intro c
    rw [hφ]
    change Submodule.mkQ P (∑ i, c i • v i) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_smul, hv i, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  have hsurj : LinearMap.range φ = ⊤ := by
    refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hIj ?_)
    intro m _
    choose c' hc' using fun i => Ideal.Quotient.mk_surjective (b.repr (Submodule.Quotient.mk m) i)
    have h1 : (Submodule.Quotient.mk (φ c') : M ⧸ P) = Submodule.Quotient.mk m := by
      rw [hmk]
      simp only [hc']
      exact b.sum_repr _
    rw [Submodule.Quotient.eq] at h1
    have h2 : m = φ c' - (φ c' - m) := by abel
    rw [h2]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨c', rfl⟩) (Submodule.mem_sup_right h1)
  have hker : LinearMap.ker φ = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I _ (IsNoetherian.noetherian _) ?_ hIj
    intro k hk
    rw [LinearMap.mem_ker] at hk
    have h0 : ∑ i, Ideal.Quotient.mk I (k i) • b i = 0 := by
      rw [← hmk, hk]
      rfl
    have hki : ∀ i, k i ∈ I := fun i =>
      Ideal.Quotient.eq_zero_iff_mem.mp ((Fintype.linearIndependent_iff.mp b.linearIndependent) _ h0 i)
    choose k' hk' using fun i => Ideal.mem_span_singleton'.mp (hki i)
    have hkx : k = x • k' := by
      ext i
      simp [← hk' i, mul_comm]
    have hk'ker : k' ∈ LinearMap.ker φ := by
      rw [LinearMap.mem_ker]
      apply reg
      show x • φ k' = x • 0
      rw [smul_zero, ← map_smul, ← hkx, hk]
    rw [hkx]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self x) hk'ker
  exact Module.Free.of_equiv (LinearEquiv.ofBijective φ
    ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hsurj⟩)

theorem free_of_modDepthGE (n : ℕ) : ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (M : Type) [AddCommGroup M] [Module B M] [Module.Finite B M],
    ReciprocityTheory.CA.ModDepthGE B M n → (maximalIdeal B).spanFinrank ≤ n → Module.Free B M := by
  induction n with
  | zero =>
    intro B _ _ _ M _ _ _ _ hsp
    exact free_of_maximalIdeal_eq_bot ((Submodule.spanFinrank_eq_zero_iff_eq_bot
      (maximalIdeal B).fg_of_isNoetherianRing).mp (by omega))
  | succ n ih =>
    intro B _ _ _ M _ _ _ hd hsp
    by_cases hsq : maximalIdeal B ≤ maximalIdeal B ^ 2
    · exact free_of_maximalIdeal_eq_bot (maximalIdeal_eq_bot_of_le_sq hsq)
    obtain ⟨rs, hlen, hmem, hreg⟩ := hd
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_length_eq_add_one hlen
    have hy : y ∈ maximalIdeal B := hmem y (by simp)
    have hass := ReciprocityTheory.CA.max_not_mem_ass_of_reg hy ((isRegular_cons_iff M y ys).mp hreg).1
    obtain ⟨x, hx, hx2, hxreg⟩ := exists_isSMulRegular_notMem_sq hass hsq
    have hd' := ReciprocityTheory.CA.ModDepthGE.quotSMulTop hx hxreg ⟨y :: ys, hlen, hmem, hreg⟩
    haveI : IsLocalRing (B ⧸ Ideal.span {x}) :=
      ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isLocalRing_quotient_span_singleton hx
    haveI : Module.Finite (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) :=
      Module.Finite.of_restrictScalars_finite B _ _
    have hsp' : (maximalIdeal (B ⧸ Ideal.span {x})).spanFinrank ≤ n := by
      have h1 :=
        ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le B hx hx2
      rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace] at h1
      omega
    have hd'' : ReciprocityTheory.CA.ModDepthGE (B ⧸ Ideal.span {x})
        (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) n := by
      obtain ⟨zs, hzl, hzm, hzr⟩ := hd'
      let e : QuotSMulTop x M ≃ₗ[B] M ⧸ Ideal.span {x} • (⊤ : Submodule B M) :=
        Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul x ⊤).symm
      refine ⟨zs.map (Ideal.Quotient.mk _), by simp [hzl], ?_, ?_⟩
      · intro r hr
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
        exact ReciprocityTheory.CA.mk_mem_maximalIdeal_quot _ (hzm z hz)
      · rw [← Ideal.Quotient.algebraMap_eq]
        exact (ReciprocityTheory.CA.isRegular_map_algebraMap_iff' zs).mpr ((e.isRegular_congr zs).mp hzr)
    haveI := ih (B ⧸ Ideal.span {x}) (M ⧸ Ideal.span {x} • (⊤ : Submodule B M)) hd'' hsp'
    exact free_of_free_quotient hx hxreg

end GlobalTheory.AnnRegSeq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinSchreierSystemIntegral
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem frobenius_affine_integral (p : ℕ) [Fact p.Prime] (S K : Type) [CommRing S] [IsDomain S]
    [ValuationRing S] [Field K] [Algebra S K] [IsFractionRing S K] (d : ℕ)
    (U : Matrix (Fin d) (Fin d) S) (z : Fin d → S) (y : Fin d → K)
    (h : ∀ i, y i ^ p = (U.map (algebraMap S K) *ᵥ y) i + algebraMap S K (z i)) :
    ∀ i, y i ∈ (algebraMap S K).range := by
  classical
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  set w := ValuationRing.valuation S K with hw
  have hint : ∀ s : S, w (algebraMap S K s) ≤ 1 := fun s =>
    (ValuationRing.mem_integer_iff S K _).2 ⟨s, rfl⟩
  intro i0
  have hi0 : Finset.univ.Nonempty := ⟨i0, Finset.mem_univ _⟩
  obtain ⟨i, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => w (y j)) hi0
  have hM : w (y i) ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    have hle : w (y i) ^ p ≤ w (y i) := by
      rw [← map_pow, h i]
      refine (Valuation.map_add_le w ?_ ?_)
      · simp only [Matrix.mulVec, dotProduct]
        refine Valuation.map_sum_le w fun j _ => ?_
        rw [map_mul, Matrix.map_apply]
        calc w (algebraMap S K (U i j)) * w (y j) ≤ 1 * w (y i) :=
              mul_le_mul' (hint _) (hmax j (Finset.mem_univ _))
          _ = w (y i) := one_mul _
      · exact (hint _).trans hgt.le
    have h2 : w (y i) ^ 2 ≤ w (y i) ^ p := pow_le_pow_right₀ hgt.le hp
    have h3 : w (y i) * w (y i) ≤ 1 * w (y i) := by
      rw [one_mul, ← sq]; exact h2.trans hle
    have h0 : 0 < w (y i) := lt_trans zero_lt_one hgt
    exact absurd (le_of_mul_le_mul_right h3 h0) (not_le.2 hgt)
  have : w (y i0) ≤ 1 := (hmax i0 (Finset.mem_univ _)).trans hM
  obtain ⟨s, hs⟩ := (ValuationRing.mem_integer_iff S K _).1 this
  exact ⟨s, hs⟩

end GlobalTheory
end

