import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0062
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0104
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0102
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0100
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0106
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0093
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0108
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHermitianRepsCountSucc

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeriesEqDens
section
noncomputable section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
namespace GlobalTheory.CompanionTheory.SiegLoc

theorem gauss1 {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) (j : ℕ) (a : R) (ha : σ a = a) (ha' : a ∉ lev ϖ 1) :
    (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j := by
  induction j using Nat.twoStepInduction with
  | zero =>
    have : Subsingleton (R ⧸ lev ϖ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp [lev])
    rw [Fintype.sum_subsingleton _ 0]
    simp
  | one => simpa using GlobalTheory.T.gauss_sum_hermitian_norm_level_one R σ ϖ q ε hR ψ hψ a ha ha'
  | more j ih _ =>
    rw [GlobalTheory.T.gauss_sum_hermitian_norm_level_shift R σ ϖ q ε hR ψ hψ j a ha ha', ih, pow_add, mul_pow (ε : ℂ) (q : ℂ) 2, hε]
    ring

theorem gauss_full {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) {m n : ℕ} (k : ℕ) (S : Matrix (Fin m) (Fin m) R) (hS : IsUnimod σ S)
    (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) (hB : B ∈ hermMod σ ϖ n k) :
    (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), ψ k (Matrix.trace (B * (cT (barσ σ ϖ hR.fix_ϖ k) x * red ϖ k S * x)))) =
      (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) * (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B)) := by
  obtain ⟨h, hh, rfl⟩ := hB
  obtain ⟨g, g', d, hgg, hgg', hd, hgd⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR n h hh
  obtain ⟨p, p', e, hpp, hpp', he, hpe⟩ := GlobalTheory.T.hermitian_matrix_diagonalizable R σ ϖ q ε hR m S hS.1
  have hq0 : (q : ℂ) ≠ 0 := by
    have := hR.one_lt
    exact_mod_cast (by omega : q ≠ 0)
  have hunit : ∀ l, e l ∉ lev ϖ 1 := by
    intro l hl
    have h1 : IsUnit p.det := Matrix.isUnit_det_of_right_inverse hpp
    have h2 : IsUnit (cT σ p).det := by
      have : cT σ p * cT σ p' = 1 := by
        have : cT σ (p' * p) = cT σ p * cT σ p' := by
          simp [cT, Matrix.transpose_mul, Matrix.map_mul]
        rw [← this, hpp']
        simp [cT]
      exact Matrix.isUnit_det_of_right_inverse this
    have h3 : IsUnit (Matrix.diagonal e).det := by
      rw [← hpe, Matrix.det_mul, Matrix.det_mul]
      exact (h2.mul hS.2).mul h1
    rw [Matrix.det_diagonal] at h3
    have h4 : IsUnit (e l) := isUnit_of_dvd_unit (Finset.dvd_prod_of_mem _ (Finset.mem_univ l)) h3
    obtain ⟨c, hc⟩ := mem_lev_iff.1 hl
    rw [hc, pow_one] at h4
    exact hR.notUnit (isUnit_of_mul_isUnit_left h4)
  choose eI heI hcard hsum using fun i => GlobalTheory.T.card_range_mul_quotient_bounded_level R σ ϖ q ε hR ψ hψ (fun j a ha ha' => gauss1 hR hψ hε j a ha ha') k (d i) (hd i)
  rw [GlobalTheory.T.matrix_gauss_sum_congr_invariance R σ ϖ hR.fix_ϖ hR.inv k (ψ k) m n h _ g g' S _ p p' hgg hgg' hpp hpp' hgd hpe,
    GlobalTheory.T.matrix_gauss_sum_diagonal_factor R σ ϖ hR.fix_ϖ k (ψ k) m n d e,
    GlobalTheory.T.multiplicity_reduction_diagonal_prod R σ ϖ hR.fix_ϖ hR.inv k n h g g' d hgg hgg' hgd]
  have hq2 : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) hR.one_lt
  have hnu : (∏ i, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i))) = (q ^ 2) ^ (∑ i, eI i) := by
    rw [Finset.prod_congr rfl (fun i _ => hcard i), Finset.prod_pow_eq_pow_sum]
  rw [hnu, Nat.log_pow hq2]
  have hM : (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℂ) = ((q : ℂ) ^ (2 * k)) ^ (m * n) := by
    have hc : Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR k
    have : Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) = (q ^ (2 * k)) ^ (m * n) := by
      show Nat.card (Fin m → Fin n → R ⧸ lev ϖ k) = _
      rw [Nat.card_fun, Nat.card_fun, hc]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
      rw [← pow_mul, mul_comm n m]
    rw [this]; push_cast; rfl
  rw [hM]
  have hc' : ((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) = ((ε : ℂ) / q) ^ m := by
    rw [div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]
  rw [hc']
  simp only [fun i l => hsum i (e l) (he l) (hunit l), Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_pow, Finset.prod_mul_distrib]
  rw [← pow_mul, ← pow_mul]
  congr 1
  have hx : ∀ x, (((ε : ℂ) / q) ^ eI x) ^ m = (((ε : ℂ) / q) ^ m) ^ eI x := fun x => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp only [hx]
  rw [Finset.prod_pow_eq_pow_sum]

theorem seriesEqDens : SeriesEqDens := by
  intro R _ σ ϖ q ε hR ψ hψ m n _ S T hS hT α hα
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => Nat.finite_of_card_ne_zero (by
    rw [GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR k]
    have := hR.one_lt
    exact pow_ne_zero _ (by omega))
  letI : ∀ k, Fintype (R ⧸ lev ϖ k) := fun k => Fintype.ofFinite _
  have hε : (ε : ℂ) ^ 2 = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have : siegAt ϖ σ ψ q ε m T = fun k => ((densAt σ ϖ S T k : ℝ) : ℂ) := funext fun k =>
    GlobalTheory.T.hermitian_rep_count_fourier_expansion R σ ϖ q ε hR ψ hψ m n k S T hS.1 hT.1 (GlobalTheory.T.hermitian_character_orthogonality R σ ϖ q ε hR ψ hψ n k)
      (fun B hB => gauss_full hR hψ hε k S hS B hB)
  rw [this]
  exact (Complex.continuous_ofReal.tendsto α).comp hα

end GlobalTheory.CompanionTheory.SiegLoc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothUniformExponent
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.SmoothUniform

theorem smooth_uniform_exponent : ∀ {R : Type} [CommRing R] (l : ℕ) [Fact l.Prime] (k : ℕ) {M : Type w} [AddCommGroup M] [Module R M] (ρ : Multiplicative (Fin k → ℤ_[l]) →* (M →ₗ[R] M)) (n : ℕ), (∀ x : M, ∃ a : ℕ, ∀ g : Fin k → ℤ_[l], ρ (Multiplicative.ofAdd ((l : ℤ_[l]) ^ a • g)) x = x) → ∀ f : LocallyConstant (Fin (n + 1) → Fin k → ℤ_[l]) M, ∃ a : ℕ, ∀ (g : Fin k → ℤ_[l]) (x : Fin (n + 1) → Fin k → ℤ_[l]), f (fun i => (l : ℤ_[l]) ^ a • g + x i) = f x ∧ ρ (Multiplicative.ofAdd ((l : ℤ_[l]) ^ a • g)) (f x) = f x := by
  intro R _ l _ k M _ _ ρ n hsm f
  have hl : (1 : ℝ) < (l : ℝ) := by
    exact_mod_cast (Fact.out : l.Prime).one_lt
  have hfin : (Set.range f).Finite := f.range_finite
  choose A hA using hsm
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : ℕ, ∀ m ∈ Set.range f, A m ≤ a₁ := by
    obtain ⟨b, hb⟩ := (hfin.image A).bddAbove
    exact ⟨b, fun m hm => hb (Set.mem_image_of_mem A hm)⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (s := (Set.univ : Set (Fin (n + 1) → Fin k → ℤ_[l])))
    (c := fun m : M => f ⁻¹' {m}) isCompact_univ
    (fun m => f.isLocallyConstant.isOpen_fiber m)
    (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : ℕ, (1 / (l : ℝ)) ^ a₂ < δ :=
    exists_pow_lt_of_lt_one hδ (by
      rw [div_lt_one (by linarith)]
      exact hl)
  refine ⟨max a₁ a₂, fun g x => ⟨?_, ?_⟩⟩
  · have hnorm : ‖(l : ℤ_[l]) ^ (max a₁ a₂) • g‖ < δ := by
      have hle : ‖(l : ℤ_[l]) ^ (max a₁ a₂) • g‖ ≤ (1 / (l : ℝ)) ^ a₂ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
        have h1 : ‖(l : ℤ_[l]) ^ (max a₁ a₂)‖ = (1 / (l : ℝ)) ^ (max a₁ a₂) := by
          rw [PadicInt.norm_p_pow, zpow_neg, zpow_natCast, one_div, inv_pow]
        have h2 : (1 / (l : ℝ)) ^ (max a₁ a₂) ≤ (1 / (l : ℝ)) ^ a₂ :=
          pow_le_pow_of_le_one (by positivity)
            (by rw [div_le_one (by linarith)]; exact hl.le) (le_max_right _ _)
        calc ‖((l : ℤ_[l]) ^ (max a₁ a₂) • g) j‖
            = ‖(l : ℤ_[l]) ^ (max a₁ a₂)‖ * ‖g j‖ := by
              simp [Pi.smul_apply, norm_mul]
          _ ≤ ‖(l : ℤ_[l]) ^ (max a₁ a₂)‖ * 1 :=
              mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
          _ ≤ (1 / (l : ℝ)) ^ a₂ := by rw [mul_one, h1]; exact h2
      exact hle.trans_lt ha₂
    obtain ⟨m, hm⟩ := hball x (Set.mem_univ x)
    have hx : f x = m := hm (Metric.mem_ball_self hδ)
    have hy : f (fun i => (l : ℤ_[l]) ^ (max a₁ a₂) • g + x i) = m := by
      apply hm
      rw [Metric.mem_ball, dist_eq_norm]
      refine lt_of_le_of_lt ?_ hnorm
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      simp
    rw [hx, hy]
  · have hle : A (f x) ≤ max a₁ a₂ := (ha₁ _ ⟨x, rfl⟩).trans (le_max_left _ _)
    have hsplit : (l : ℤ_[l]) ^ (max a₁ a₂) • g
        = (l : ℤ_[l]) ^ (A (f x)) • ((l : ℤ_[l]) ^ (max a₁ a₂ - A (f x)) • g) := by
      rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hle]
    rw [hsplit]
    exact hA (f x) _

end GlobalTheory.CompanionTheory.SmoothUniform
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotalComplexFlipIsomorphism
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.DCFlip

variable {R : Type} [CommRing R]

def sw (K : DCx.{w} R) (x : ∀ p q, K.X p q) : ∀ q p, K.flip.X q p :=
  fun q p => (-1 : ℤ) ^ (p * q) • x p q

theorem sw_apply (K : DCx.{w} R) (x : ∀ p q, K.X p q) (q p : ℕ) :
    sw K x q p = (-1 : ℤ) ^ (p * q) • x p q := rfl

theorem neg_one_pow_eq_of_even {m n : ℕ} (h : Even (m + n)) : (-1 : ℤ) ^ m = (-1 : ℤ) ^ n := by
  have hm : (-1 : ℤ) ^ m * (-1 : ℤ) ^ n = 1 := by rw [← pow_add]; exact h.neg_one_pow
  have hn : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by rw [← mul_pow]; simp
  exact mul_right_cancel₀ (pow_ne_zero n (by norm_num : (-1 : ℤ) ≠ 0)) (hm.trans hn.symm)

theorem sign_smul_sign_smul {M : Type w} [AddCommGroup M] (k : ℕ) (z : M) :
    (-1 : ℤ) ^ k • (-1 : ℤ) ^ k • z = z := by
  rw [smul_smul, ← mul_pow]; simp

theorem D_sw (K : DCx.{w} R) (x : ∀ p q, K.X p q) : K.flip.D (sw K x) = sw K (K.D x) := by
  funext a b
  rcases a with _ | a <;> rcases b with _ | b
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]
  · simp [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply]
  · have e1 : (-1 : ℤ) ^ ((b + 1) * a) = (-1 : ℤ) ^ ((b + 1) * (a + 1) + (b + 1)) :=
      neg_one_pow_eq_of_even ⟨(b + 1) * a + (b + 1), by ring⟩
    have e2 : (-1 : ℤ) ^ (a + 1 + b * (a + 1)) = (-1 : ℤ) ^ ((b + 1) * (a + 1)) := by
      congr 1; ring
    simp only [DCx.D_apply, DCx.Dh, DCx.Dv, sw_apply, map_zsmul, smul_add, smul_smul, ← pow_add]
    rw [e1, e2]
    exact add_comm _ _

def swHom (K : DCx.{w} R) : Cx.Hom K.tot K.flip.tot (RingHom.id R) where
  f n :=
    { toFun := fun x => ⟨sw K x.1, fun q p h => by
        change (-1 : ℤ) ^ (p * q) • x.1 p q = 0
        rw [x.2 p q (by omega), smul_zero]⟩
      map_add' := fun x y => Subtype.ext (funext fun q => funext fun p =>
        smul_add ((-1 : ℤ) ^ (p * q)) (x.1 p q) (y.1 p q))
      map_smul' := fun c x => Subtype.ext (funext fun q => funext fun p =>
        smul_comm ((-1 : ℤ) ^ (p * q)) c (x.1 p q)) }
  comm n x := Subtype.ext (D_sw K x.1)

theorem flip_tot : ∀ {R : Type} [CommRing R] (K : DCx.{w} R), ∃ φ : Cx.Hom K.tot K.flip.tot (RingHom.id R), (∀ n, Function.Bijective (φ.f n)) ∧ ∀ n (x : K.tot.X n) p q, (φ.f n x).1 q p = (-1 : ℤ) ^ (p * q) • x.1 p q := by
  intro R _ K
  refine ⟨swHom K, fun n => ⟨fun x y h => ?_, fun y => ?_⟩, fun n x p q => rfl⟩
  · refine Subtype.ext (funext fun p => funext fun q => ?_)
    have h' : (-1 : ℤ) ^ (p * q) • x.1 p q = (-1 : ℤ) ^ (p * q) • y.1 p q :=
      congrFun (congrFun (congrArg Subtype.val h) q) p
    have h'' := congrArg (fun z => (-1 : ℤ) ^ (p * q) • z) h'
    simpa only [sign_smul_sign_smul] using h''
  · refine ⟨⟨fun p q => (-1 : ℤ) ^ (p * q) • y.1 q p, fun p q h => ?_⟩, ?_⟩
    · change (-1 : ℤ) ^ (p * q) • y.1 q p = 0
      rw [y.2 q p (by omega), smul_zero]
    · refine Subtype.ext (funext fun q => funext fun p => ?_)
      exact sign_smul_sign_smul (p * q) (y.1 q p)

end GlobalTheory.CompanionTheory.DCFlip
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotalComplexPairingSign
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

noncomputable section

namespace GlobalTheory.CompanionTheory.TotPairing

variable {R : Type} [CommRing R] {K : DCx.{w} R} {L : DCx.{w'} R} {M : DCx.{w''} R}

theorem eq_sum_sgl (K : DCx.{w} R) {n : ℕ} {x : ∀ p q, K.X p q} (hx : x ∈ K.T n) :
    x = ∑ c ∈ Finset.HasAntidiagonal.antidiagonal n, K.sgl c.1 c.2 (x c.1 c.2) := by
  funext r s
  rw [Finset.sum_apply, Finset.sum_apply]
  by_cases h : r + s = n
  · rw [Finset.sum_eq_single (r, s)]
    · exact (K.sgl_self r s _).symm
    · rintro ⟨a, b⟩ _ hne
      refine K.sgl_ne _ ?_
      by_contra hc
      push_neg at hc
      exact hne (by rw [hc.1, hc.2])
    · intro hh
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 h) hh
  · rw [hx r s h, Finset.sum_eq_zero]
    rintro ⟨a, b⟩ hab
    have hab' : a + b = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    exact K.sgl_ne _ (by omega)

def cmp (K : DCx.{w} R) (p q : ℕ) : (∀ a b, K.X a b) →ₗ[R] K.X p q :=
  (LinearMap.proj (R := R) (φ := fun b => K.X p b) q).comp
    (LinearMap.proj (R := R) (φ := fun a => ∀ b, K.X a b) p)

theorem cmp_apply (K : DCx.{w} R) (p q : ℕ) (x : ∀ a b, K.X a b) : cmp K p q x = x p q := rfl

def gen (P : DPairing K L M) (p q p' q' : ℕ) : K.X p q →ₗ[R] L.X p' q' →ₗ[R] (∀ a b, M.X a b) :=
  (-1 : ℤ) ^ (q * p') • (P.μ (p := p) (q := q) (p' := p') (q' := q') rfl rfl).compr₂ (M.sgl (p + p') (q + q'))

theorem gen_apply (P : DPairing K L M) (p q p' q' : ℕ) (x : K.X p q) (y : L.X p' q') :
    gen P p q p' q' x y = (-1 : ℤ) ^ (q * p') • M.sgl (p + p') (q + q') (P.μ rfl rfl x y) := by
  simp [gen, LinearMap.smul_apply, LinearMap.compr₂_apply]

def fam (P : DPairing K L M) (a b : ℕ) :
    (∀ p q, K.X p q) →ₗ[R] (∀ p q, L.X p q) →ₗ[R] (∀ p q, M.X p q) :=
  ∑ c ∈ Finset.HasAntidiagonal.antidiagonal a, ∑ c' ∈ Finset.HasAntidiagonal.antidiagonal b,
    (gen P c.1 c.2 c'.1 c'.2).compl₁₂ (cmp K c.1 c.2) (cmp L c'.1 c'.2)

theorem fam_apply (P : DPairing K L M) (a b : ℕ) (x : ∀ p q, K.X p q) (y : ∀ p q, L.X p q) :
    fam P a b x y = ∑ c ∈ Finset.HasAntidiagonal.antidiagonal a, ∑ c' ∈ Finset.HasAntidiagonal.antidiagonal b,
      gen P c.1 c.2 c'.1 c'.2 (x c.1 c.2) (y c'.1 c'.2) := by
  simp only [fam, LinearMap.sum_apply, LinearMap.compl₁₂_apply, cmp_apply]

theorem fam_sgl (P : DPairing K L M) {p q p' q' a b : ℕ} (h : p + q = a) (h' : p' + q' = b)
    (x : K.X p q) (y : L.X p' q') :
    fam P a b (K.sgl p q x) (L.sgl p' q' y) = gen P p q p' q' x y := by
  rw [fam_apply, Finset.sum_eq_single (p, q), Finset.sum_eq_single (p', q')]
  · simp only [DCx.sgl_self]
  · rintro ⟨r, s⟩ _ hne
    have : L.sgl p' q' y r s = 0 := L.sgl_ne _ (by
      by_contra hc
      push_neg at hc
      exact hne (by rw [hc.1, hc.2]))
    simp only [this, map_zero]
  · intro hh
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 h') hh
  · rintro ⟨r, s⟩ _ hne
    have : K.sgl p q x r s = 0 := K.sgl_ne _ (by
      by_contra hc
      push_neg at hc
      exact hne (by rw [hc.1, hc.2]))
    simp only [this, map_zero, LinearMap.zero_apply, Finset.sum_const_zero]
  · intro hh
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 h) hh

theorem fam_mem (P : DPairing K L M) {a b n : ℕ} (h : a + b = n) (x : ∀ p q, K.X p q) (y : ∀ p q, L.X p q) :
    fam P a b x y ∈ M.T n := by
  rw [fam_apply]
  refine Submodule.sum_mem _ fun c hc => Submodule.sum_mem _ fun c' hc' => ?_
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hc
  have e' := Finset.HasAntidiagonal.mem_antidiagonal.1 hc'
  rw [gen_apply]
  refine Submodule.smul_of_tower_mem _ _ ?_
  intro r s hrs
  exact M.sgl_ne _ (by omega)

theorem sgl_mu (P : DPairing K L M) {p q p' q' a b : ℕ} (h : p + p' = a) (h' : q + q' = b)
    (x : K.X p q) (y : L.X p' q') :
    M.sgl a b (P.μ h h' x y) = M.sgl (p + p') (q + q') (P.μ rfl rfl x y) := by
  subst h h'
  rfl

theorem sign_id {A : Type*} [AddCommGroup A] (e s t r : ℤ) (ht : t * t = 1) (A₁ A₂ A₃ A₄ : A) :
    e • (A₁ + s • A₂ + (s * r) • (A₃ + t • A₄)) =
      e • A₁ + (s * (e * r)) • A₃ + (s * t) • ((e * t) • A₂ + (r * e) • A₄) := by
  match_scalars
  · ring
  · linear_combination (-e * s) * ht
  · ring
  · linear_combination (-e * s * r) * ht + (e * s * r) * ht

theorem leib_gen (P : DPairing K L M) (p q p' q' : ℕ) (x : K.X p q) (y : L.X p' q') :
    M.D (gen P p q p' q' x y) =
      gen P (p + 1) q p' q' (K.dh p q x) y + (-1 : ℤ) ^ p • gen P p (q + 1) p' q' (K.dv p q x) y +
        (-1 : ℤ) ^ (p + q) • (gen P p q (p' + 1) q' x (L.dh p' q' y) +
          (-1 : ℤ) ^ p' • gen P p q p' (q' + 1) x (L.dv p' q' y)) := by
  have e₁ := sgl_mu P (p := p + 1) (p' := p') (a := p + p' + 1) (by omega) (rfl : q + q' = q + q') (K.dh p q x) y
  have e₂ := sgl_mu P (p := p) (p' := p' + 1) (a := p + p' + 1) (by omega) (rfl : q + q' = q + q') x (L.dh p' q' y)
  have e₃ := sgl_mu P (q := q + 1) (q' := q') (b := q + q' + 1) (rfl : p + p' = p + p') (by omega) (K.dv p q x) y
  have e₄ := sgl_mu P (q := q) (q' := q' + 1) (b := q + q' + 1) (rfl : p + p' = p + p') (by omega) x (L.dv p' q' y)
  simp only [gen_apply, map_zsmul, DCx.D_sgl, P.lh rfl rfl, P.lv rfl rfl, map_add, e₁, e₂, e₃, e₄]
  have ht : ((-1 : ℤ) ^ q) * ((-1 : ℤ) ^ q) = 1 := by
    rw [← mul_pow]; simp
  have s₁ : (-1 : ℤ) ^ (p + p') = (-1) ^ p * (-1) ^ p' := pow_add _ _ _
  have s₂ : (-1 : ℤ) ^ (p + q) = (-1) ^ p * (-1) ^ q := pow_add _ _ _
  have s₃ : (-1 : ℤ) ^ ((q + 1) * p') = (-1) ^ (q * p') * (-1) ^ p' := by rw [add_mul, one_mul, pow_add]
  have s₄ : (-1 : ℤ) ^ (q * (p' + 1)) = (-1) ^ (q * p') * (-1) ^ q := by rw [mul_add, mul_one, pow_add]
  rw [s₁, s₂, s₃, s₄, smul_smul, smul_smul]
  exact sign_id _ _ _ _ ht _ _ _ _

theorem leib_fam (P : DPairing K L M) {a b : ℕ} {x : ∀ p q, K.X p q} {y : ∀ p q, L.X p q}
    (hx : x ∈ K.T a) (hy : y ∈ L.T b) :
    M.D (fam P a b x y) = fam P (a + 1) b (K.D x) y + (-1 : ℤ) ^ a • fam P a (b + 1) x (L.D y) := by
  rw [eq_sum_sgl K hx, eq_sum_sgl L hy]
  simp only [map_sum, LinearMap.sum_apply, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun c' hc' => ?_
  have e' := Finset.HasAntidiagonal.mem_antidiagonal.1 hc
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hc'
  obtain ⟨p', q'⟩ := c
  obtain ⟨p, q⟩ := c'
  dsimp only at e e' ⊢
  rw [fam_sgl P e e', leib_gen, DCx.D_sgl, DCx.D_sgl]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [fam_sgl P (by omega) e', fam_sgl P (by omega) e', fam_sgl P e (by omega), fam_sgl P e (by omega), e]

def totP (P : DPairing K L M) : CxPairing K.tot L.tot M.tot where
  μ {a b n} h := LinearMap.mk₂ R (fun x y => ⟨fam P a b x.1 y.1, fam_mem P h _ _⟩)
    (fun x x' y => Subtype.ext (by simp))
    (fun r x y => Subtype.ext (by simp))
    (fun x y y' => Subtype.ext (by simp))
    (fun r x y => Subtype.ext (by simp))
  leib {a b n} h x y := Subtype.ext (leib_fam P x.2 y.2)

end GlobalTheory.CompanionTheory.TotPairing
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformIndependentOfBase
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem phi_eq_of_convex : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), IsOpen Ω → Convex ℝ Ω → GaussTube G Ω →
    ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ t : ℝ × ℝ, phi G x t = phi G x' t := by
  intro X _ _ _ Ω G hΩ hconv hG x hx x' hx' t
  have hhor : ∀ a b c : ℝ, (∀ s ∈ Set.uIcc a b, (s, c) ∈ Ω) →
      GlobalTheory.CompanionTheory.TubeFourier.phi G (a, c) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (b, c) t := by
    intro a b c h
    rcases le_total a b with hab | hba
    · exact GlobalTheory.T.tube_transform_horizontal_invariance X Ω G hG a b c hab
        (fun s hs => h s (Set.Icc_subset_uIcc hs)) t
    · exact (GlobalTheory.T.tube_transform_horizontal_invariance X Ω G hG b a c hba
        (fun s hs => h s (Set.Icc_subset_uIcc' hs)) t).symm
  have hver : ∀ a b c : ℝ, (∀ s ∈ Set.uIcc a b, (c, s) ∈ Ω) →
      GlobalTheory.CompanionTheory.TubeFourier.phi G (c, a) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (c, b) t := by
    intro a b c h
    rcases le_total a b with hab | hba
    · exact GlobalTheory.T.tube_transform_vertical_invariance X Ω G hG a b c hab
        (fun s hs => h s (Set.Icc_subset_uIcc hs)) t
    · exact (GlobalTheory.T.tube_transform_vertical_invariance X Ω G hG b a c hba
        (fun s hs => h s (Set.Icc_subset_uIcc' hs)) t).symm
  have hf : IsLocallyConstant (fun p : Ω => GlobalTheory.CompanionTheory.TubeFourier.phi G (p : ℝ × ℝ) t) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨⟨p₁, p₂⟩, hp⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ (p₁, p₂) hp
    have hmem : {q : Ω | (q : ℝ × ℝ) ∈ Metric.ball (p₁, p₂) ε} ∈ 𝓝 (⟨(p₁, p₂), hp⟩ : Ω) :=
      continuousAt_subtype_val.preimage_mem_nhds (Metric.ball_mem_nhds _ hε)
    filter_upwards [hmem]
    rintro ⟨⟨q₁, q₂⟩, hq⟩ hqball
    have hd : dist q₁ p₁ < ε ∧ dist q₂ p₂ < ε := by
      have h' : dist (q₁, q₂) (p₁, p₂) < ε := hqball
      rwa [Prod.dist_eq, max_lt_iff] at h'
    obtain ⟨h₁, h₂⟩ := hd
    rw [Real.dist_eq] at h₁ h₂
    have hv : GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, p₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, q₂) t := by
      refine hver p₂ q₂ q₁ (fun s hs => hball ?_)
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
      exact ⟨h₁, lt_of_le_of_lt (Set.abs_sub_left_of_mem_uIcc hs) h₂⟩
    have hh : GlobalTheory.CompanionTheory.TubeFourier.phi G (p₁, p₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, p₂) t := by
      refine hhor p₁ q₁ p₂ (fun s hs => hball ?_)
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, dist_self, Real.dist_eq]
      exact ⟨lt_of_le_of_lt (Set.abs_sub_left_of_mem_uIcc hs) h₁, hε⟩
    show GlobalTheory.CompanionTheory.TubeFourier.phi G (q₁, q₂) t = GlobalTheory.CompanionTheory.TubeFourier.phi G (p₁, p₂) t
    rw [← hv, ← hh]
  haveI : PreconnectedSpace Ω := Subtype.preconnectedSpace hconv.isPreconnected
  exact hf.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ (⟨x, hx⟩ : Ω))
    (Set.mem_univ (⟨x', hx'⟩ : Ω))

end GlobalTheory.CompanionTheory.TubeFourier
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHermitianRepsCountSuccStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unimodular_hermitian_reps_count_succ : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → ∀ k : ℕ, 1 ≤ k → solCount σ ϖ S T (k + 1) = solCount σ ϖ S T k * q ^ (2 * m * n - n ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.solCount_succ | exact GlobalTheory.CompanionTheory.UnrDens.solCount_succ | (intros; apply GlobalTheory.CompanionTheory.UnrDens.solCount_succ <;> assumption)
end

