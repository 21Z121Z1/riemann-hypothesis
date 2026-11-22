import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInHecke
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsZeroCoordNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.AdelicLattices₂.AlgebraMapNormOfBasisOneSqrt
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CmExtensionAdelesStandardModelDictionary
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory

theorem cmAdele_dictionary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∃ Φ : AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) ∧ (∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) ∧ (∀ v ε, IsPlaceIdem F v ε → (Φ (algebraMap (AF F) (AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (AF F) (AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) ∧ Continuous Φ.symm ∧ ∀ x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)ˣ, (x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).2 = 1 → (∀ w, ((x : (mixedSpace E × FiniteAdeleRing (𝓞 E) E)).1.2 w).im = 0) → ∃ a : (AF F)ˣ, Φ (idF F E a : (AE F E)ˣ) = x := by
  intro F E _ _ _ _ _ σ h
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨Φ, a1, a2, a3, a4, a5⟩ := GlobalTheory.T.exists_cm_adele_tensor_equiv_mixed_finite F E σ h1 h2 h3 h4
  refine ⟨Φ, a1, a2, ?_, a4, a5⟩
  rintro v ε ⟨α, rfl, hv, hv'⟩
  exact a3 v (pairA F 0 α) rfl hv hv'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicOfIndefinite
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.UTrans

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UTrans.herm_diagonal_self {r : ℕ} (g u : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal g) u u = ∑ i, u i * g i * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (u i) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, diagonal_apply, mul_ite, ite_mul]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UTrans.exists_isotropic_diagonal {n : ℕ} (hn : 3 ≤ n) {g : Fin n → E}
    (hg : ∀ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (g i) = g i) (hg0 : ∀ i, g i ≠ 0)
    (hs : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (g i)).re) ∧ ∃ j, (τ (g j)).re < 0) :
    ∃ z : Fin n → E, z ≠ 0 ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal g) z z = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hiso : _root_.GlobalTheory.LocalQuad.HermClass.Isotropy := fun F _ _ ι _ a h5 ha hsgn =>
    _root_.GlobalTheory.LocalQuad.isotropic_of_indefinite _root_.GlobalTheory.QNorm.hasseNormSt F a h5 ha hsgn
  have hsign : ∀ τ : E →+* ℂ, ∃ k : Fin m, 0 < (τ (g k.succ)).re ↔ 0 < (τ (-g 0)).re := by
    intro τ
    obtain ⟨⟨i, hi⟩, j, hj⟩ := hs τ
    have h0 : (τ (g 0)).re ≠ 0 := _root_.GlobalTheory.LocalQuad.HermClass.re_ne_zero τ (hg 0) (hg0 0)
    rw [map_neg, Complex.neg_re]
    by_cases hpos : 0 < (τ (g 0)).re
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨k, rfl⟩
      · exact absurd hj (not_lt.2 hpos.le)
      · exact ⟨k, iff_of_false (not_lt.2 hj.le) (by linarith)⟩
    · have hneg : (τ (g 0)).re < 0 := lt_of_le_of_ne (not_lt.1 hpos) h0
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
      · exact absurd hi hpos
      · exact ⟨k, iff_of_true hi (by linarith)⟩
  have hc : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (-g 0) = -g 0 := by
    show IsCMField.complexConj E (-g 0) = -g 0
    rw [map_neg]
    exact congrArg Neg.neg (hg 0)
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.LocalQuad.HermClass.exists_represent hiso (r := m) (by omega)
    (g := fun k => g k.succ) (fun k => hg _) (fun k => hg0 _) hc (neg_ne_zero.2 (hg0 0)) hsign
  refine ⟨Fin.cons 1 w, fun h => one_ne_zero (α := E) (by simpa using congr_fun h 0), ?_⟩
  rw [_root_.GlobalTheory.UTrans.herm_diagonal_self] at hw ⊢
  rw [Fin.sum_univ_succ]
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul, h1, mul_one]
  rw [hw]
  ring

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma herm_eq_dotProduct_mulVec_cc {r : ℕ} (H : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm H x y = x ⬝ᵥ (H *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y b)) := by
  simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma herm_mulVec_mulVec' {r : ℕ} (G P : Matrix (Fin r) (Fin r) E) (u v : Fin r → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (P *ᵥ u) (P *ᵥ v) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Pᵀ * G * P.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc) u v := by
  have hc : (fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((P *ᵥ v) b)) = P.map _root_.ReciprocityTheory.ChartRestriction.G.FD.cc *ᵥ fun b => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (v b) := by
    ext b
    simp [mulVec, dotProduct, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, map_sum, map_mul]
  rw [herm_eq_dotProduct_mulVec_cc, herm_eq_dotProduct_mulVec_cc, hc, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec u, vecMul_transpose]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma re_mul_cc_eq_normSq_mul_re (τ : E →+* ℂ) (y d : E) :
    (τ (y * d * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y)).re = Complex.normSq (τ y) * (τ d).re := by
  rw [map_mul, map_mul, _root_.GlobalTheory.Published.embedding_cc, mul_right_comm, Complex.mul_conj,
    Complex.re_ofReal_mul]

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_re_pos_of_herm_diagonal_re_pos {r : ℕ} (τ : E →+* ℂ) (d y : Fin r → E)
    (hy : 0 < (τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y)).re) : ∃ i, 0 < (τ (d i)).re := by
  by_contra h
  push_neg at h
  rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, map_sum, Complex.re_sum] at hy
  refine absurd hy (not_lt.2 (Finset.sum_nonpos fun i _ => ?_))
  rw [re_mul_cc_eq_normSq_mul_re]
  exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) (h i)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma exists_re_neg_of_herm_diagonal_re_neg {r : ℕ} (τ : E →+* ℂ) (d y : Fin r → E)
    (hy : (τ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y)).re < 0) : ∃ i, (τ (d i)).re < 0 := by
  by_contra h
  push_neg at h
  rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, map_sum, Complex.re_sum] at hy
  refine absurd hy (not_lt.2 (Finset.sum_nonneg fun i _ => ?_))
  rw [re_mul_cc_eq_normSq_mul_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (h i)

open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

theorem _root_.GlobalTheory.UTrans.exists_isotropic_of_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), (∀ a, σ a = IsCMField.complexConj E a) → _root_.GlobalTheory.UTrans.IsHerm σ G → 3 ≤ n → (∀ τ : E →+* ℂ, (∃ x, 0 < (τ (_root_.GlobalTheory.UTrans.hf σ G x x)).re) ∧ ∃ y, (τ (_root_.GlobalTheory.UTrans.hf σ G y y)).re < 0) → ∃ z : Fin n → E, z ≠ 0 ∧ _root_.GlobalTheory.UTrans.hf σ G z z = 0 := by
  intro E _ _ _ n σ G hσ hG hn hs
  have hf : ∀ x y, _root_.GlobalTheory.UTrans.hf σ G x y = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by
    intro x y
    simp only [_root_.GlobalTheory.UTrans.hf, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm, hσ]
    rfl
  have hGc : ∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a := fun a b => by
    rw [← hG.herm a b, hσ]
    rfl
  obtain ⟨P, d, hP, hPd, hd, -⟩ := _root_.GlobalTheory.HermDiag.exists_congr_diagonal_herm hGc
  have hPinv : ∀ x, P *ᵥ (P⁻¹ *ᵥ x) = x := fun x => by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hP), one_mulVec]
  have hform : ∀ y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (P *ᵥ y) (P *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y := fun y => by
    rw [herm_mulVec_mulVec', hPd]
  suffices ∃ y, y ≠ 0 ∧ _root_.ReciprocityTheory.ChartRestriction.G.FD.herm (Matrix.diagonal d) y y = 0 by
    obtain ⟨y, hy, hy0⟩ := this
    exact ⟨P *ᵥ y, fun h => hy (eq_zero_of_mulVec_eq_zero hP h), by rw [hf, hform, hy0]⟩
  by_cases hd0 : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hd0
    refine ⟨Pi.single i 1, fun h => one_ne_zero (α := E) (by simpa using congr_fun h i), ?_⟩
    rw [_root_.GlobalTheory.UTrans.herm_diagonal_self, Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  · push_neg at hd0
    refine _root_.GlobalTheory.UTrans.exists_isotropic_diagonal hn hd hd0 fun τ => ?_
    obtain ⟨⟨x, hx⟩, y, hy⟩ := hs τ
    rw [hf, ← hPinv x, hform] at hx
    rw [hf, ← hPinv y, hform] at hy
    exact ⟨exists_re_pos_of_herm_diagonal_re_pos τ d _ hx, exists_re_neg_of_herm_diagonal_re_neg τ d _ hy⟩

end GlobalTheory.UTrans
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPolynomialSectionBlockDiagonalMapStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_section_blockDiagonal_map : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → ∃ (c : ι × ι → ι × ι → ℚ) (b : ι → ι → MvPolynomial (ι × ι) ℚ), (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ (Matrix.of fun i j => ev (b i j) (1 : Matrix ι ι ℂ)) = 1 ∧ ∀ g ∈ Γ, (Matrix.of fun i j => ev (b i j) (blk e g)) ∈ Γ ∧ blk e (Matrix.of fun i j => ev (b i j) (blk e g)) = blk e g ∧ g = (1 + linExt c (e.map (algebraMap ℚ ℂ) * g * (1 - e.map (algebraMap ℚ ℂ)) * (blk e g).adjugate)) * (Matrix.of fun i j => ev (b i j) (blk e g)) := by
  first | exact @GlobalTheory.ClassFin.exists_blk_section | exact GlobalTheory.ClassFin.exists_blk_section | (intros; apply GlobalTheory.ClassFin.exists_blk_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalInvariantTensor
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.RatInvTensor

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def coordAlg (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Subalgebra ℂ (Matrix ι ι ℂ → ℂ) :=
  Algebra.adjoin ℂ {φ | ∃ p ∈ S, ∃ b, φ = fun y => ((fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 y) b}

def AllFixed (Γ : Set (Matrix ι ι ℂ)) (S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))) : Prop :=
  ∀ p ∈ S, ∀ g ∈ Γ, (fun a => ((p.2 a : ℚ) : ℂ)) ᵥ* tpow p.1 g = fun a => ((p.2 a : ℚ) : ℂ)

def Good (Γ : Set (Matrix ι ι ℂ)) (φ : Matrix ι ι ℂ → ℂ) : Prop :=
  ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧ φ ∈ coordAlg S

theorem coordAlg_mono {S T : Set (Σ n : ℕ, ((Fin n → ι) → ℚ))} (h : S ⊆ T) : coordAlg S ≤ coordAlg T := by
  apply Algebra.adjoin_mono
  rintro φ ⟨p, hp, b, rfl⟩
  exact ⟨p, h hp, b, rfl⟩

theorem good_zero (Γ : Set (Matrix ι ι ℂ)) : Good Γ 0 :=
  ⟨∅, Set.finite_empty, fun _ h => h.elim, Subalgebra.zero_mem _⟩

theorem Good.add {Γ : Set (Matrix ι ι ℂ)} {φ ψ : Matrix ι ι ℂ → ℂ} (h1 : Good Γ φ) (h2 : Good Γ ψ) :
    Good Γ (φ + ψ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  obtain ⟨T, hT, fT, mT⟩ := h2
  refine ⟨S ∪ T, hS.union hT, ?_, Subalgebra.add_mem _ (coordAlg_mono Set.subset_union_left mS)
    (coordAlg_mono Set.subset_union_right mT)⟩
  rintro p (hp | hp)
  · exact fS p hp
  · exact fT p hp

theorem Good.smul {Γ : Set (Matrix ι ι ℂ)} {φ : Matrix ι ι ℂ → ℂ} (c : ℂ) (h1 : Good Γ φ) :
    Good Γ (c • φ) := by
  obtain ⟨S, hS, fS, mS⟩ := h1
  exact ⟨S, hS, fS, Subalgebra.smul_mem _ mS c⟩

theorem good_sum {Γ : Set (Matrix ι ι ℂ)} {β : Type} (s : Finset β) (φ : β → Matrix ι ι ℂ → ℂ)
    (h : ∀ b, Good Γ (φ b)) : Good Γ (∑ b ∈ s, φ b) :=
  Finset.sum_induction φ (Good Γ) (fun _ _ => Good.add) (good_zero Γ) (fun b _ => h b)

theorem good_coord {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (n : ℕ) (l : (Fin n → ι) → ℂ)
    (hl : ∀ g ∈ Γ, l ᵥ* tpow n g = l) (b : Fin n → ι) : Good Γ (fun y => (l ᵥ* tpow n y) b) := by
  have h := GlobalTheory.T.mem_span_rational_kroneckerInvariants ι Γ hΓ.aut_mem n l hl
  clear hl
  induction h using Submodule.span_induction with
  | mem μ hμ =>
    obtain ⟨h1, h2⟩ := hμ
    choose q hq using h2
    have hμ : μ = fun a => ((q a : ℚ) : ℂ) := funext hq
    subst hμ
    refine ⟨{⟨n, q⟩}, Set.finite_singleton _, ?_, Algebra.subset_adjoin ⟨⟨n, q⟩, rfl, b, rfl⟩⟩
    rintro p rfl
    exact h1
  | zero =>
    have : (fun y : Matrix ι ι ℂ => ((0 : (Fin n → ι) → ℂ) ᵥ* tpow n y) b) = 0 := by
      funext y; simp
    rw [this]; exact good_zero Γ
  | add u v _ _ hu hv =>
    have : (fun y : Matrix ι ι ℂ => ((u + v) ᵥ* tpow n y) b) =
        (fun y => (u ᵥ* tpow n y) b) + fun y => (v ᵥ* tpow n y) b := by
      funext y; simp [Matrix.add_vecMul]
    rw [this]; exact hu.add hv
  | smul c u _ hu =>
    have : (fun y : Matrix ι ι ℂ => ((c • u) ᵥ* tpow n y) b) =
        c • (fun y => (u ᵥ* tpow n y) b) := by
      funext y; simp [Matrix.smul_vecMul]
    rw [this]; exact hu.smul c

theorem good_homog {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) (n : ℕ)
    (F : MvPolynomial (ι × ι) ℂ) (hF : IsInv Γ F) (hn : F.IsHomogeneous n) : Good Γ (evC F) := by
  obtain ⟨l, hl, hev⟩ := GlobalTheory.T.invariant_form_eq_sum_invariant_tensors' ι Γ hΓ hS n F hF hn
  have : evC F = ∑ b, fun y => (l b ᵥ* tpow n y) b := by
    funext y; rw [hev, Finset.sum_apply]
  rw [this]
  exact good_sum _ _ fun b => good_coord hΓ n (l b) (hl b) b

theorem exists_finite_family {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsPre Γ) (hS : SS Γ) :
    ∃ S : Set (Σ n : ℕ, ((Fin n → ι) → ℚ)), S.Finite ∧ AllFixed Γ S ∧
      ∀ f, IsInv Γ f → evC f ∈ coordAlg S := by
  obtain ⟨Rey, hR⟩ := GlobalTheory.T.exists_leftTranslation_reynoldsOperator ι Γ hΓ hS
  obtain ⟨s, hs, hgen⟩ := GlobalTheory.T.hilbert_finiteness_leftInvariantMatrixPoly ι Γ Rey hR
  have hg : ∀ F : s, Good Γ (evC F.1) := fun F => by
    obtain ⟨h1, n, h2⟩ := hs F.1 F.2
    exact good_homog hΓ hS n F.1 h1 h2
  choose S hfin hfix hmem using hg
  refine ⟨⋃ F, S F, Set.finite_iUnion hfin, ?_, ?_⟩
  · intro p hp
    obtain ⟨F, hF⟩ := Set.mem_iUnion.1 hp
    exact hfix F p hF
  · intro f hf
    have h := hgen f hf
    clear hf
    induction h using Algebra.adjoin_induction with
    | mem F hF => exact coordAlg_mono (Set.subset_iUnion S ⟨F, hF⟩) (hmem ⟨F, hF⟩)
    | algebraMap c =>
      have : evC (algebraMap ℂ (MvPolynomial (ι × ι) ℂ) c) = algebraMap ℂ (Matrix ι ι ℂ → ℂ) c := by
        funext y; simp [evC]
      rw [this]; exact Subalgebra.algebraMap_mem _ c
    | add u v _ _ hu hv =>
      have : evC (u + v) = evC u + evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.add_mem _ hu hv
    | mul u v _ _ hu hv =>
      have : evC (u * v) = evC u * evC v := by funext y; simp [evC]
      rw [this]; exact Subalgebra.mul_mem _ hu hv

theorem exists_rational_invariant_tensor : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → ℚ), (∀ g ∈ Γ, act d (fun k => ((t k : ℚ) : ℂ)) g = (fun k => ((t k : ℚ) : ℂ))) ∧ ∀ f, IsInv Γ f → ∃ P : MvPolynomial (TIdx ι d) ℂ, ∀ y : Matrix ι ι ℂ, evC f y = MvPolynomial.eval (act d (fun k => ((t k : ℚ) : ℂ)) y) P := by
  intro ι _ _ Γ hΓ hS
  obtain ⟨S, hfin, hfix, hmem⟩ := exists_finite_family hΓ hS
  obtain ⟨m, e, -, he⟩ := hfin.fin_param
  refine ⟨m, fun i => (e i).1, fun k => (e k.1).2 k.2, ?_, ?_⟩
  · intro g hg
    funext k
    exact congrFun (hfix (e k.1) (he ▸ Set.mem_range_self _) g hg) k.2
  · intro f hf
    have h := hmem f hf
    generalize evC f = φ at h
    induction h using Algebra.adjoin_induction with
    | mem φ hφ =>
      obtain ⟨p, hp, b, rfl⟩ := hφ
      rw [← he] at hp
      obtain ⟨i, rfl⟩ := hp
      exact ⟨MvPolynomial.X ⟨i, b⟩, fun y => by rw [MvPolynomial.eval_X]; rfl⟩
    | algebraMap c => exact ⟨MvPolynomial.C c, fun y => by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P + Q, fun y => by rw [map_add, ← hP, ← hQ]; rfl⟩
    | mul u v _ _ hu hv =>
      obtain ⟨P, hP⟩ := hu
      obtain ⟨Q, hQ⟩ := hv
      exact ⟨P * Q, fun y => by rw [map_mul, ← hP, ← hQ]; rfl⟩

end GlobalTheory.ClassFin.RatInvTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupportStatement
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_adelic_decomposition_split_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ (γ : GL (Fin n) E) (h k : GL (Fin n) (RA F E)), IsUnE c G γ.1 ∧ IsUnA c G h.1 ∧ IsUnA c G k.1 ∧ g.1 = fm F γ.1 * h.1 * k.1 ∧ SuppSplit c N h.1 ∧ (∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = N • w) ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), (k⁻¹).1 *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.exists_rep_suppSplit | exact GlobalTheory.UnRep.exists_rep_suppSplit | (intros; apply GlobalTheory.UnRep.exists_rep_suppSplit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtensionStatement
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasse_norm_theorem_quadratic_extension : GlobalTheory.Published.HasseNormSt := by
  first | exact @GlobalTheory.QNorm.hasseNormSt | exact GlobalTheory.QNorm.hasseNormSt | (intros; apply GlobalTheory.QNorm.hasseNormSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemPowsSUnitsChooseTStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_places_with_pth_roots_and_separating_units : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ : F) (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), Disjoint S T ∧ T.card + 1 = S.card + Fintype.card (InfinitePlace F) ∧ (∀ v ∈ T, ∃ r : v.adicCompletion F, r ^ p = algebraMap F (v.adicCompletion F) (δ : F)) ∧ ∀ v ∈ T, ∃ u ∈ sUnits F S, u ∉ powSub p (algebraMap F (v.adicCompletion F)) ∧ ∀ v' ∈ T, v' ≠ v → u ∈ powSub p (algebraMap F (v'.adicCompletion F)) := by
  first | exact @GlobalTheory.CNorm.exists_auxiliary_places_prime | exact GlobalTheory.CNorm.exists_auxiliary_places_prime | (intros; apply GlobalTheory.CNorm.exists_auxiliary_places_prime <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NpOfFinrankTwo
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_basis_one_sqrt_of_finrank_two {F E : Type} [Field F] [CharZero F] [Field E]
    [Algebra F E] (h : Module.finrank F E = 2) :
    ∃ (e : Module.Basis (Fin 2) F E) (δ : F), δ ≠ 0 ∧ e 0 = 1 ∧ e 1 * e 1 = algebraMap F E δ := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hr : 1 < Module.rank F E := by
    rw [← Module.finrank_eq_rank, h]; norm_num
  obtain ⟨s, hs⟩ := exists_linearIndependent_pair_of_one_lt_rank hr (one_ne_zero (α := E))
  let b := basisOfLinearIndependentOfCardEqFinrank hs (by simp [h])
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = s := by simp [b]
  obtain ⟨p, q, hpq⟩ : ∃ p q : F, s * s = algebraMap F E p + algebraMap F E q * s := by
    refine ⟨b.repr (s * s) 0, b.repr (s * s) 1, ?_⟩
    conv_lhs => rw [← b.sum_repr (s * s), Fin.sum_univ_two, hb0, hb1, Algebra.smul_def,
      Algebra.smul_def, mul_one]
  have ht : LinearIndependent F ![(1 : E), s - algebraMap F E (q / 2)] := by
    rw [LinearIndependent.pair_iff] at hs ⊢
    intro x y hxy
    have := hs (x - y * (q / 2)) y (by
      rw [← hxy]; simp only [Algebra.smul_def, map_sub, map_mul]; ring)
    obtain ⟨h1, rfl⟩ := this
    exact ⟨by simpa using h1, rfl⟩
  have hsq : (s - algebraMap F E (q / 2)) * (s - algebraMap F E (q / 2))
      = algebraMap F E (p + (q / 2) ^ 2) := by
    have hq : algebraMap F E q = 2 * algebraMap F E (q / 2) := by
      rw [← map_ofNat (algebraMap F E) 2, ← map_mul]; congr 1; ring
    rw [map_add, map_pow]
    rw [hq] at hpq
    linear_combination hpq
  refine ⟨basisOfLinearIndependentOfCardEqFinrank ht (by simp [h]), p + (q / 2) ^ 2, ?_,
    by simp, by simpa using hsq⟩
  intro h0
  rw [h0, map_zero, mul_self_eq_zero] at hsq
  exact ht.ne_zero 1 (by simpa using hsq)

theorem TNorm.exists_sq_sub {F E : Type} [Field F] [Field E] [Algebra F E]
    (e : Module.Basis (Fin 2) F E) (h0 : e 0 = 1) {δ : F} (h1 : e 1 * e 1 = algebraMap F E δ)
    (L : Type) [Field L] [Algebra F L] {x : F} (h : TNorm F E L x) :
    ∃ a b : L, algebraMap F L x = a ^ 2 - algebraMap F L δ * b ^ 2 := by
  obtain ⟨z, hz⟩ := h
  let e' := Algebra.TensorProduct.basis L e
  refine ⟨e'.repr z 0, e'.repr z 1, ?_⟩
  rw [← hz, ← GlobalTheory.Published.norm_of_basis_one_sqrt e'
    (by rw [Algebra.TensorProduct.basis_apply, h0]; rfl) (algebraMap F L δ)
    (by
      rw [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, h1,
        ← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.algebraMap_apply' δ).symm)]
  congr 1
  conv_lhs => rw [← e'.sum_repr z, Fin.sum_univ_two]

theorem np_of_finrank_two : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 → NP F E := by
  intro F E _ _ _ _ _ h x hx hloc
  obtain ⟨e, δ, hδ, h0, h1⟩ := exists_basis_one_sqrt_of_finrank_two h
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt F δ x hδ hx
    (fun σ => @TNorm.exists_sq_sub F E _ _ _ e h0 δ h1 ℝ _ σ.toAlgebra x (hloc.2 σ.toAlgebra))
    (fun v => TNorm.exists_sq_sub e h0 h1 _ (hloc.1 v))
  exact ⟨_, (GlobalTheory.Published.norm_of_basis_one_sqrt e h0 δ h1 a b).trans hab.symm⟩

end GlobalTheory.CNorm
end

