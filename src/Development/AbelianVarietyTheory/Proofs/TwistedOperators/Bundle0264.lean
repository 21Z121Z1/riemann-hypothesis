import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0258
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultTEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0247
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0224
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryWittIsotropicCoordinateEqPairing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.AscFin

theorem coeff_monic_poly_sum {K R : Type} [CommRing K] [CommRing R] (φ : K →+* R) {n : ℕ} (u s : K) (h : s * u = 1)
    (b : Fin n → K) (G : Matrix (Fin n) (Fin n) K) (x : Fin n → R) :
    φ u * ∑ l, φ (∑ k, (s * b k) * G k l) * x l = ∑ k, ∑ l, φ (b k) * φ (G k l) * x l := by
  have hus : φ u * φ s = 1 := by rw [← map_mul, mul_comm, h, map_one]
  simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  linear_combination (φ (b k) * φ (G k l) * x l) * hus

private theorem cT_sig_eq_conjTranspose' {D : D7} {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) M = Mᴴ := rfl

private theorem cA_incA_apply_eq_incA_star {D : D7} (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem incA_neg_xi0_pow_mul_pX_mulVec_eq_sum : ∀ {D : D7} {A B B₀ : HSp D} {c ρ : ℕ} (a : HermitianOrthogonalExtensionData A B c (-1)) (d : HypDec B B₀ ρ), c = 2 * ρ → IsAuxiliaryVectorWittDec a d → ∀ (i : Fin ρ) (hi : 2 * ρ - 1 - i.1 < c) (x : Fin B.rank → AE D), incA D ((-D.host.xi0) ^ (i.1 + 1)) * (d.pX *ᵥ x) i = ∑ k, ∑ l, cA D (incA D (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) * incA D (B.gram k l) * x l := by
  intro D A B B₀ c ρ a d hc hA i hi x
  obtain ⟨h2, he, s, he'⟩ := hA
  have hle : ρ ≤ c := by omega
  have hj : ∀ hle : ρ ≤ c, (Fin.castLE hle i).rev = (⟨2 * ρ - 1 - i.1, hi⟩ : Fin c) := fun hle => by
    ext
    simp only [Fin.val_rev, Fin.coe_castLE]
    omega
  have g1 := congrFun (congrFun a.gram ⟨2 * ρ - 1 - i.1, hi⟩) (Fin.castLE hle i)
  have g2 := congrFun (congrFun d.e'e i) i
  rw [he, he'] at g2
  simp only [antiDiagonalSignGramMatrix, cT_sig_eq_conjTranspose', Matrix.mul_apply, Matrix.conjTranspose_apply, colsOf, star_mul', Matrix.one_apply_eq, hj,
    Fin.coe_castLE] at g1 g2
  rw [if_pos (by omega), if_neg (fun h => by have := congrArg Fin.val h; simp only [Fin.coe_castLE] at this; omega)] at g1
  have g3 : ∑ l, (∑ k, star (s i) * star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩) * HSpace.gram B k l) *
      ((-D.host.xi0) ^ (i.1 + 1) * a.a l (Fin.castLE hle i)) =
      star (s i) * (-D.host.xi0) ^ (i.1 + 1) *
        ∑ l, (∑ k, star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩) * HSpace.gram B k l) * a.a l (Fin.castLE hle i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [mul_assoc (star (s i)), ← Finset.mul_sum]
    ring
  have key : star (s i) * (-D.host.xi0) ^ (i.1 + 1) = 1 := by
    linear_combination g2 - g3 - (star (s i) * (-D.host.xi0) ^ (i.1 + 1)) * g1
  simp only [HypDec.pX, HypDec.qX, GlobalTheory.MixModel.rat, Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, he', colsOf, star_mul', hj, cA_incA_apply_eq_incA_star]
  exact coeff_monic_poly_sum (incA D) _ _ key (fun k => star (a.a k ⟨2 * ρ - 1 - i.1, hi⟩)) (HSpace.gram B) x

end GlobalTheory.AscFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AvgCharEqOfExt
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.OpTrace GlobalTheory.HCChar GlobalTheory.SUChar
open GlobalTheory.Orb (ujMat ujRep CcMat IsCharFn IsRegSS)
open GlobalTheory.DSSU (SUJ SUset Ext)
open GlobalTheory.SqIntSU (scalarMul circleHaar)

namespace GlobalTheory.ExtChar

theorem avgChar_eq_of_ext : ∀ (n : ℕ) [NeZero n] (ε : Fin n → Bool) (μ' : Measure (SUJ ε)) [μ'.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (h' : IsURepOn (SUset ε) π'), Ext ε m π' π → ∀ Θ' : SUJ ε → ℂ, IsCharFn (suMat ε) μ' (suRep h') Θ' → ∀ g : SUJ ε, IsRegSS (suMat ε g) → GlobalTheory.ExtChar.avgChar ε m Θ' g = Θ' g := by
  intro n _ ε μ' _ V _ _ _ m π' π h' hext Θ' hΘ g hg
  have hcen : ∀ j : ZMod n, Θ' (cen ε j * g) = (((ZMod.toCircle j : Circle) : ℂ) ^ m)⁻¹ * Θ' g := by
    intro j
    set ζ : Circle := ZMod.toCircle j
    have h1mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
      simpa using GlobalTheory.SUChar.suMat_mem ε 1
    have hmat : GlobalTheory.SUChar.suMat ε (cen ε j) = ((ζ : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [suMat_cen]
      show ((ζ⁻¹ : Circle) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = _
      rw [Circle.coe_inv]
    have hmem : ((ζ : ℂ)⁻¹) • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := hmat ▸ GlobalTheory.SUChar.suMat_mem ε (cen ε j)
    have hnorm : ‖(ζ : ℂ)⁻¹‖ = 1 := by rw [norm_inv, Circle.norm_coe, inv_one]
    have e1 := hext 1 (by simp) _ hmem
    have e2 := hext (ζ : ℂ)⁻¹ hnorm 1 h1mem
    rw [one_smul, _root_.one_zpow, one_smul] at e1
    have hone : π' 1 = 1 := h'.1.1
    have hrep : ∀ v, GlobalTheory.SUChar.suRep h' (cen ε j) v = ((ζ : ℂ) ^ m)⁻¹ • v := by
      intro v
      show π' (GlobalTheory.SUChar.suMat ε (cen ε j)) v = _
      rw [hmat, ← e1, e2, hone, _root_.inv_zpow]
      rfl
    have hne : ((ζ : ℂ) ^ m)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by simp))
    exact GlobalTheory.CentralCharSU.charFn_central_mul n ε μ' V π' h' Θ' hΘ (cen ε j) _ _ hmat hne hrep g hg
  rw [avgChar]
  have hz : ∀ j : ZMod n, ((ZMod.toCircle j : Circle) : ℂ) ^ m * Θ' (cen ε j * g) = Θ' g := by
    intro j
    rw [hcen, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (by simp)), one_mul]
  simp only [hz, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast NeZero.ne n), one_mul]

end GlobalTheory.ExtChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodAscentOfTowerRungs
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem ascent_of_rungs : TowerEx → Rung0 → RungB → RungJ → Ascent := by
  intro hT h0 hB hJ D hq T L μ0 hL sc G W M hM v Ψ hΨ u hu hper
  obtain ⟨F, hE, ΓL, hG⟩ := hT D hq T L μ0 hL sc G W M hM v
  have key : ∀ k (h : 2 * k + 2 ≤ D.R.m), NZB W M v F Ψ u k h := by
    intro k
    induction k with
    | zero =>
      intro h
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu 0 h
        (h0 D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu hper h)
    | succ k ih =>
      intro h
      have h' : 2 * k + 2 ≤ D.R.m := by omega
      exact hB D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu (k + 1) h
        (hJ D hq T L μ0 hL sc G W M hM v F ΓL hE hG Ψ hΨ u hu k h h' (ih h'))
  obtain ⟨r, hr⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  have hk : 2 * (r - 1) + 2 ≤ D.R.m := by omega
  have hk' : 2 * (r - 1) + 2 = D.R.m := by omega
  obtain ⟨ρ, Φ, hne⟩ := key (r - 1) hk
  refine ⟨ρ, Φ, ?_⟩
  let f : ∀ i, Fn G (.grid i 0) := fun i => if hi : i ≤ D.R.m then part W M ρ Φ u i hi else 0
  have hf : f D.R.m = thetaChi W M ρ Φ u := by
    simp only [f, dif_pos le_rfl]; rfl
  have := hE.top (r - 1) hk hk' Ψ f (hΨ.1 _ le_rfl) (by rw [hf, ← part_m]; exact hu ρ Φ _ le_rfl) (by
    simp only [f, dif_pos hk]; exact hne)
  rwa [hf] at this

end GlobalTheory.Asc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepCoreComponentMemDepthLatticeGridCore
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LatSandwich

variable {D : D7}

theorem incA_eq (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem rat_mul_tmul_mul {k l m n : ℕ} (A : Matrix (Fin k) (Fin l) D.host.E) (X : Matrix (Fin l) (Fin m) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (p : AF D.host.F) :
    rat A ⬝ (Matrix.of fun i j => p ⊗ₜ[D.host.F] X i j : Mx D l m) ⬝ rat B =
      Matrix.of fun i j => p ⊗ₜ[D.host.F] (A * X * B) i j := by
  ext i j
  simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, incA_eq, Finset.sum_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← TensorProduct.tmul_sum]

theorem sandwich_hatMx {k l m n : ℕ} {M : Submodule (𝓞 D.host.E) (Matrix (Fin l) (Fin m) D.host.E)}
    {M' : Submodule (𝓞 D.host.E) (Matrix (Fin k) (Fin n) D.host.E)} (A : Matrix (Fin k) (Fin l) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (h : ∀ x ∈ M, A * x * B ∈ M') {z : Mx D l m} (hz : z ∈ hatMx M) :
    rat A ⬝ z ⬝ rat B ∈ hatMx M' := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hw
    rw [rat_mul_tmul_mul]
    exact AddSubgroup.subset_closure ⟨α, hα, _, h x hx, rfl⟩
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem ha

theorem sandwich_homLat {k l m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin l → D.host.E)} {Λ₂ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ₂' : Submodule (𝓞 D.host.E) (Fin k → D.host.E)} (A : Matrix (Fin k) (Fin l) D.host.E)
    (B : Matrix (Fin m) (Fin n) D.host.E) (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ₂') (hB : ∀ y ∈ Λ₂, B *ᵥ y ∈ Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) : ∀ x ∈ 𝔪 • homLat Λ Λ', A * x * B ∈ 𝔪 • homLat Λ₂ Λ₂' := by
  intro x hx
  refine Submodule.smul_induction_on hx (fun r hr x hx => ?_) (fun x y hx hy => ?_)
  · have e : A * (r • x) * B = r • (A * x * B) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [e]
    refine Submodule.smul_mem_smul hr fun y hy => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hA _ (hx _ (hB y hy))
  · rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem hx hy

theorem sandwich_entry {k l m n : ℕ} (A : Matrix (Fin k) (Fin l) D.host.E) (B : Matrix (Fin m) (Fin n) D.host.E)
    (a : D.host.E) (t : Fin l → D.host.E) (r : Fin m → D.host.E) (i : Fin k) (j : Fin n) :
    (A * Matrix.of (fun i j => a * t i * r j) * B) i j = a * (A *ᵥ t) i * ∑ m, r m * B m j := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem sandwich_latO {S T S' T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LS' : Set (Fin S'.rank → D.host.E)} {LT' : Set (Fin T'.rank → D.host.E)} (A : Matrix (Fin T'.rank) (Fin T.rank) D.host.E)
    (B : Matrix (Fin S.rank) (Fin S'.rank) D.host.E) (hA : ∀ t ∈ LT, A *ᵥ t ∈ LT')
    (hB : ∀ s ∈ LS, ∃ s' ∈ LS', ∀ j, ∑ k, star (s' k) * S'.gram k j = ∑ m, (∑ k, star (s k) * S.gram k m) * B m j)
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) {w : WO S T} (hw : w ∈ latO S T LS LT P) :
    (rat A ⬝ w ⬝ rat B : WO S' T') ∈ latO S' T' LS' LT' P := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨s', hs', e⟩ := hB s hs
    have e1 : (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
        Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
          (Matrix.of (fun i j => a * t i * ∑ k, star (s k) * S.gram k j) : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j := rfl
    rw [e1, rat_mul_tmul_mul]
    refine AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s', hs', A *ᵥ t, hA t ht, ?_⟩
    ext i j
    simp only [Matrix.of_apply]
    rw [sandwich_entry, e j]
  | zero => rw [Matrix.mul_zero, Matrix.zero_mul]; exact zero_mem _
  | add a b _ _ ha hb => rw [Matrix.mul_add, Matrix.add_mul]; exact add_mem ha hb
  | neg a _ ha => rw [Matrix.mul_neg, Matrix.neg_mul]; exact neg_mem ha

theorem orthogonalSumAuxiliaryVectors_frame_mulVec_mem_lattice {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {M : Matrix (Fin B.rank) (Fin A.rank) D.host.E} (hM : M = frameMat B A d.ι) {y : Fin A.rank → D.host.E} (hy : y ∈ Λ) :
    M *ᵥ y ∈ d.lat Λ 𝔟 :=
  ⟨y, hy, 0, fun p => (𝔟 p).val.zero_mem, by rw [hM, Matrix.mulVec_zero, add_zero]⟩

theorem orthogonalSumAuxiliaryVectors_projection_mem_lattice {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    {M : Matrix (Fin B.rank) (Fin A.rank) D.host.E} (hM : M = frameMat B A d.ι) (hiso : Mᴴ * B.gram * M = A.gram)
    {x : Fin B.rank → D.host.E} (hx : x ∈ d.lat Λ 𝔟) : (A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ x ∈ Λ := by
  obtain ⟨y, hy, u, -, rfl⟩ := hx
  have h1 : A.gram⁻¹ * (Mᴴ * B.gram) * M = 1 := by
    rw [Matrix.mul_assoc, hiso, Matrix.nonsing_inv_mul _ (gram_isUnit_det A)]
  have h2 : A.gram⁻¹ * (Mᴴ * B.gram) * d.a = 0 := by
    have := d.perp
    rw [cT_sig, ← hM] at this
    rw [Matrix.mul_assoc, this, Matrix.mul_zero]
  rw [← hM, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1, h2, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero]
  exact hy

theorem proj_form {A B : HSp D} (M : Matrix (Fin B.rank) (Fin A.rank) D.host.E) (s : Fin B.rank → D.host.E) (j : Fin A.rank) :
    ∑ k, star (((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) k) * A.gram k j = ∑ m, (∑ k, star (s k) * B.gram k m) * M m j := by
  have e1 : (A.gram⁻¹ * (Mᴴ * B.gram))ᴴ * A.gram = B.gram * M := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, gram_conjTranspose,
      gram_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit_det A),
      Matrix.mul_one]
  have e2 : (fun j => ∑ k, star (((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) k) * A.gram k j) =
      star ((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) ᵥ* A.gram := by
    funext j; simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
  have e3 : (fun j => ∑ m, (∑ k, star (s k) * B.gram k m) * M m j) = (star s ᵥ* B.gram) ᵥ* M := by
    funext j; simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
  have key : star ((A.gram⁻¹ * (Mᴴ * B.gram)) *ᵥ s) ᵥ* A.gram = (star s ᵥ* B.gram) ᵥ* M := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, e1, ← Matrix.vecMul_vecMul]
  exact congrFun (e2.trans (key.trans e3.symm)) j

end GlobalTheory.LatSandwich

namespace GlobalTheory.AscFin

open GlobalTheory.LatSandwich

theorem pcBF_core_mem_latCore : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀,
    ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).1 ∈ latCore G (2 * ρ + 1) := by
  intro D hoff T L μ0 hL sc G W M hM F hF ρ h u hu
  simp only [pcBF, piecesOf, AddSubgroup.mem_comap, AddMonoidHom.coe_comp, Function.comp_apply] at hu
  rw [OrthDec.resS_apply]

  have key : rat (F.dJ ρ h).q0 ⬝ (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ⬝ rat ((F.dB ρ h).i₀ * (F.oB ρ h).iA) =
      u ⬝ (F.oB ρ h).jA := by
    rw [rat_mul, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply]
    change (F.dJ ρ h).p0 ⬝ ((F.dJ ρ h).j0 ⬝ u ⬝ (F.dB ρ h).p0) ⬝ ((F.dB ρ h).j0 ⬝ (F.oB ρ h).jA) = _
    simp only [← Matrix.mul_assoc]
    rw [HypDec.p0_j0, Matrix.one_mul, Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← key]

  have lat1 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  have lat2 : G.Λ (.grid (2 * ρ + 2) 0) = (G.colDec (2 * ρ + 2) (by omega) h).lat (G.Λ (.core (2 * ρ + 2)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := G.sp.colLat (2 * ρ + 2) (by omega) h
  have iso2 : ((F.dB ρ h).i₀ * (F.oB ρ h).iA)ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * ((F.dB ρ h).i₀ * (F.oB ρ h).iA) =
      (G.V (.core (2 * ρ + 2))).gram := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (F.oB ρ h).iAᴴ * ((F.dB ρ h).i₀ᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * (F.dB ρ h).i₀) * (F.oB ρ h).iA := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [(F.dB ρ h).iso, (F.oB ρ h).isoA]

  have hA : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), (F.dJ ρ h).q0 *ᵥ t ∈ G.Λ (.core (2 * ρ + 1)) := fun t ht =>
    orthogonalSumAuxiliaryVectors_projection_mem_lattice _ _ _ (hF.aJ ρ h) (F.dJ ρ h).iso (lat1 ▸ ht)

  have hB1 : ∀ y ∈ G.Λ (.core (2 * ρ + 2)), ((F.dB ρ h).i₀ * (F.oB ρ h).iA) *ᵥ y ∈ G.Λ (.grid (2 * ρ + 2) 0) :=
    fun y hy => lat2 ▸ orthogonalSumAuxiliaryVectors_frame_mulVec_mem_lattice _ _ _ (hF.aB ρ h) hy

  have hB : ∀ s ∈ (G.Λ (.grid (2 * ρ + 2) 0) : Set (Fin (negSp (G.V (.grid (2 * ρ + 2) 0))).rank → D.host.E)),
      ∃ s' ∈ (G.Λ (.core (2 * ρ + 2)) : Set (Fin (negSp (G.V (.core (2 * ρ + 2)))).rank → D.host.E)), ∀ j,
        ∑ k, star (s' k) * (negSp (G.V (.core (2 * ρ + 2)))).gram k j =
          ∑ m, (∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k m) * ((F.dB ρ h).i₀ * (F.oB ρ h).iA) m j := by
    intro s hs
    rw [SetLike.mem_coe, lat2] at hs
    refine ⟨_, orthogonalSumAuxiliaryVectors_projection_mem_lattice _ _ _ (hF.aB ρ h) iso2 hs, fun j => ?_⟩
    simp only [negSp_gram, Matrix.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_mul]
    rw [proj_form]
  have hu1 : (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ∈ latO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := hu.1
  have hu2 : ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (F.dB ρ h).ext0 _ ((F.dJ ρ h).inc0 _ u) ∈
      hatMx (G.modul • homLat (G.Λ (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 1) 0))) := hu.2
  refine ⟨?_, fun e he => ?_⟩
  · have h1 := sandwich_latO (S' := negSp (G.V (.core (2 * ρ + 2)))) (T' := G.V (.core (2 * ρ + 1)))
      (LS' := (G.Λ (.core (2 * ρ + 2)) : Set _)) (LT' := (G.Λ (.core (2 * ρ + 1)) : Set _)) _ _ hA hB _ hu1
    exact h1
  · have h2 := sandwich_hatMx _ _ (sandwich_homLat _ _ hA hB1 G.modul) (hu2 e he)
    rw [Matrix.mul_smul, Matrix.smul_mul] at h2
    exact h2

end GlobalTheory.AscFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Grid

variable {D : D7}

section Transfer

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem actO_eq_of_real {g : GA D S} {h : GA D T} (hg : g ∈ GinfC S) (hh : h ∈ GinfC T) {x : WO S T}
    (hx : x.map (infPart D) = 0) : actO S T g h x = x := by
  have e1 : (Formalism.L2.Theta.mt S g⁻¹).map (finPart D) = 1 := congrArg Units.val (show finHom S g⁻¹ = 1 from inv_mem hg)
  have e2 : (Formalism.L2.Theta.mt T h).map (finPart D) = 1 := congrArg Units.val (show finHom T h = 1 from hh)
  have e3 : (actO S T g h x).map (infPart D) = x.map (infPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]
  have e4 : (actO S T g h x).map (finPart D) = x.map (finPart D) := by
    unfold actO
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2, Matrix.mul_one, Matrix.one_mul]
  exact Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext (congrFun (congrFun e3 i) j) (congrFun (congrFun e4 i) j)

theorem isItW_of_mem_span {χS χT : (AE D)ˣ →* Circle} {ω : WRep S T} (hω : IsWeilDatumO ψ S T χS χT ω) (hθ : IsInfFam θ)
    {P P' : D.what₂.Tau → SPar} {M : DSModel S P} {M' : DSModel T P'}
    {sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {f₀ f : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀))
    {It : PolF D T.rank S.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M} (h : IsItW θ M M' ω (pureTensorO ψ θ S T sS sT BS BT f) It) :
    IsItW θ M M' ω (pureTensorO ψ θ S T sS sT BS BT f₀) It := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  let L : Module.End ℂ (WO S T → ℂ) := ∑ a ∈ c.support, c a • GlobalTheory.SplitScalar.heisL ψ S T a.1
  have hL : ∀ F, L F = ∑ a ∈ c.support, c a • heisO ψ S T a.1 F := fun F => by
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, GlobalTheory.SplitScalar.heisL_apply]
  have hd : ∀ τ z F, IsThetaFunO ψ S T F → L (dRho (heisO ψ S T) θ τ z F) = dRho (heisO ψ S T) θ τ z (L F) :=
    fun τ z F hF => by
      rw [hL, hL, GlobalTheory.FockTranslate.dRho_sum hω.std.1.1 hθ hF τ z c.support (fun a => a.1) c fun a _ => a.2]
  have hpt : ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f₀ Q) ∧
      L (pureTensorO ψ θ S T sS sT BS BT f₀ Q) = pureTensorO ψ θ S T sS sT BS BT (L f₀) Q := fun Q => by
    refine GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
      (fun _ _ => GlobalTheory.OrientedHeis.theta_add) (fun c _ => GlobalTheory.OrientedHeis.theta_smul c) _ _ L (fun k F hF => ?_) f₀ h₀ Q
    obtain ⟨τ, i, j⟩ := k
    refine ⟨GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_sub (GlobalTheory.OrientedHeis.theta_dRho hθ hω.std τ _ hF)
      (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.OrientedHeis.theta_dRho hθ hω.std τ _ hF))), ?_⟩
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul, hd _ _ _ hF, hd _ _ _ hF]
  have hom : ∀ g ∈ GinfC S, ∀ k ∈ GinfC T, ∀ Q, ω (g, k) (pureTensorO ψ θ S T sS sT BS BT (L f₀) Q) =
      L (ω (g, k) (pureTensorO ψ θ S T sS sT BS BT f₀ Q)) := fun g hg k hk Q => by
    rw [← (hpt Q).2, hL, hL, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, hω.om_heis _ _ _ _ (hpt Q).1, actO_eq_of_real hg hk a.2]
  have hder : ∀ (F : ℝ → WO S T → ℂ) (F' : WO S T → ℂ), (∀ z, HasDerivAt (fun t => F t z) (F' z) 0) →
      ∀ z, HasDerivAt (fun t => L (F t) z) (L F' z) 0 := fun F F' hF z => by
    simp only [hL, Finset.sum_apply, Pi.smul_apply, heisO, smul_eq_mul]
    exact HasDerivAt.fun_sum fun a _ => ((hF _).const_mul _).const_mul _
  have e : (c.sum fun i a => a • heisO ψ S T i.1 f₀) = L f₀ := (hL f₀).symm
  rw [e] at h
  refine ⟨h.ne, h.bdd, fun τ g hg φ φ' H => h.eqK τ g hg φ φ' ?_, fun τ X hX φ φ' H => h.eqg τ X hX φ φ' fun z => ?_,
    fun τ g hg φ φ' v v' H => h.invK τ g hg φ φ' v v' ?_, fun τ X hX φ φ' v v' H => h.invg τ X hX φ φ' v v' fun z => ?_⟩
  · rw [hom _ (GlobalTheory.FinTranslate.atTau_mem θ S τ g) _ (one_mem _), ← H, (hpt φ').2]
  · simp only [fun t => hom _ (GlobalTheory.FinTranslate.oneP_mem θ S τ X t) _ (one_mem _) φ, ← (hpt φ').2]
    exact hder _ _ H z
  · rw [hom _ (one_mem _) _ (GlobalTheory.FinTranslate.atTau_mem θ T τ g), ← H, (hpt φ').2]
  · simp only [fun t => hom _ (one_mem _) _ (GlobalTheory.FinTranslate.oneP_mem θ T τ X t) φ, ← (hpt φ').2]
    exact hder _ _ H z

theorem stepVec_mem_span
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Datum.EAf D)} {βT : GL (Fin T.rank) (Datum.EAf D)} {L : LevDat D.host.E ℂ S.rank}
    {χ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {Q : Finset (Pl D.host.E)}
    {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f : WO S T → ℂ} (dS : IsSelfDualC S ΛS) (dT : IsSelfDualC T ΛT)
    (h : IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT L χ Q ξ f₀ f) :
    f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀) := by
  classical
  obtain ⟨hv, e, he', ⟨Tm, hTm⟩, hall⟩ := h
  obtain ⟨P, he, hP⟩ : ∃ P, IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ PP ∈ L.Pg ∨ PP ∈ Q :=
    ⟨_, he', fun PP => Finset.mem_union⟩
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO dS.1 dT.1 βS βT
  have hSB := GlobalTheory.PlaceDatum.isSBHalf_of_red e _ (frMapO S T βS βT) (GlobalTheory.PlaceDatum.frMapO_add βS βT)
      (GlobalTheory.PlaceDatum.exists_den_frMapO dS.1.fg dT.1.fg βS βT)
      ⟨K, hK, fun t ht => hC t (GlobalTheory.PlaceDatum.infPart_of_half hinf ht)⟩ P
      (fun y => omegaG L χ y * omegaQ Q L.r ξ 1 y) fun y y' h => by
        rw [GlobalTheory.PlaceDatum.omegaG_congr _ _ y y' fun PP hPP => h PP ((hP PP).2 (Or.inl hPP)),
          GlobalTheory.PlaceDatum.omegaQ_congr _ _ _ 1 y y' fun PP hPP => h PP ((hP PP).2 (Or.inr hPP))]
  rw [hall Tm hTm]
  exact (GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 dS dT (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 hinf hTm hSB).1

theorem finVec_of_mem_span
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)} {f₀ f : WO S T → ℂ}
    (hv : IsVacO ψ θ S T sS sT ΛS ΛT f₀)
    (hf : f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f₀)) :
    IsThetaFunO ψ S T f ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f := by
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  exact ⟨GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hv.1.1 f₀ hv.2.theta _ c.support (fun a => a.1) c fun a _ => a.2,
    fun τ => GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hv.1.1 hv.2.inf f₀ hv.2.theta τ _ (hv.2.fock τ) _ c.support
      (fun a => a.1) c fun a _ => a.2⟩

end Transfer

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A}

theorem chrStep_eq_muAt (R : RealDat D A Ks) (t : T) (j : ℕ) : Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1) =
    (GridPre.muAt R t (j + 1) (rkV D 0 j), GridPre.muAt R t (j + 1) (rkV D 0 (j + 1))) := by
  have hr : Odd D.R.r := by
    have h1 := D.R.k_even; have h2 := D.R.m_even; have h3 := D.R.two_le_m
    unfold Ranks.r; grind
  rw [Lift.chrStep_eq_att _ _ hr D.R.t_odd (Nat.le_add_left 1 j)]
  simp [rkV]

end GlobalTheory.Grid

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeRightDerivativeCommutatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexDerivative_rightDerivative_commutator : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, (RderC θ V τ Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ Z φ) + RderC θ V τ (Z * X - X * Z) φ) ∧ (τ' ≠ τ → RderC θ V τ' Z (Rder θ V τ X φ) = Rder θ V τ X (RderC θ V τ' Z φ)) := by
  first | exact @GlobalTheory.DerBracket.RderC_Rder | exact GlobalTheory.DerBracket.RderC_Rder | (intros; apply GlobalTheory.DerBracket.RderC_Rder <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjFrameToRealLieAlgebraSpecStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjFrameToRealLieAlgebra_spec : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (R : GlobalTheory.SmoothForms.RealPoints C.θ T) (B : C.Bas), C.IsB B → ∀ Z ∈ GlobalTheory.HolRead.unitLie C.X, (∀ ρ, (GlobalTheory.AdSpan.ConjHol.toLieC C R B Z ρ).1 = B ρ * (mat Z (C.m.e ρ)).map (starRingEnd ℂ) * (B ρ)⁻¹) ∧ GlobalTheory.AdSpan.ConjHol.toLieC C R B (I • Z) = 0 := by
  first | exact @GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec | exact GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec | (intros; apply GlobalTheory.AdSpan.ConjHol.ToLie.toLieC_spec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParameterSphericalUnramifiedUnitaryStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satake_parameter_spherical_unramifiedUnitary : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (ϖ : w.adicCompletion E) (σ : w.adicCompletion E →+* w.adicCompletion E) (q n : ℕ), IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V), ρ.IsIrreducible → IsAdmissible ρ → GlobalTheory.LGrp.IsSpherical ρ (KU σ n) → ∃ α, HasSatU ϖ q ρ α := by
  first | exact @GlobalTheory.LFun.ExSatU.exists_hasSatU | exact GlobalTheory.LFun.ExSatU.exists_hasSatU | (intros; apply GlobalTheory.LFun.ExSatU.exists_hasSatU <;> assumption)
end

