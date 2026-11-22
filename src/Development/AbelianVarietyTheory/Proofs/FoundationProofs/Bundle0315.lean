import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0261
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackFirstGroupRationalPointEqSmul
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.RatRow

variable {D : D7} {N N' : ℕ}

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  have h : ∀ y, D.host.φ₀ (D.host.conj y) = (starRingEnd ℂ) (D.host.φ₀ y) := fun y =>
    D.host.conjE_apply _ y
  rw [h, h, Complex.conj_conj]

theorem adj_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (adj D M) = M := by
  refine Matrix.ext fun i j => ?_
  simp [adj, conj_conj]

theorem moves_one (D : D7) (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D N
  rw [← h2]; exact (h1 _).1

theorem sd_of_moves {g : GA D N} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  have : L = Lt g := by
    ext x; rw [h x, (h1 g).1 x]
  rw [this]; exact (h1 g).2

theorem klat (T : Tor D) {g : GA D N} {g' : GA D N'} {L₁ L₁'}
    (h : Moves D (g : GL (Fin N) (AE D)) L₁) (h' : Moves D (g' : GL (Fin N') (AE D)) L₁') :
    KLat D T (La D T L₁ L₁') := Or.inr ⟨_, _, sd_of_moves h, sd_of_moves h', rfl⟩

theorem isRat_one (D : D7) (N : ℕ) : IsRat D ((1 : GA D N) : GL (Fin N) (AE D)) 1 := by
  unfold IsRat
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

theorem hf_unitary (T : Tor D) {M' : Matrix (Fin N') (Fin N') D.host.E} {M : Matrix (Fin N) (Fin N) D.host.E}
    (h' : adj D M' * M' = 1) (h : M * adj D M = 1) (z w : VC D N N') :
    Hf D T (mulV D M' M z) (mulV D M' M w) = Hf D T z w := by
  rw [Hf_mulV, mulV_mulV, h', h, mulV_one]

theorem mulV_comm (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E) (z : VC D N N') :
    mulV D M' 1 (mulV D 1 M z) = mulV D 1 M (mulV D M' 1 z) := by
  simp only [mulV_mulV, Matrix.mul_one, Matrix.one_mul]

theorem mulV_scalar (a : D.host.E) (z : VC D N N') (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    mulV D (Matrix.diagonal fun _ => a) 1 z τ i j = embT D τ a * z τ i j := by
  rw [mulV_apply, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
  rfl

def revM (D : D7) (n : ℕ) : Matrix (Fin n) (Fin n) D.host.E := Matrix.of fun i j => if j = i.rev then 1 else 0

def halfM (D : D7) (n : ℕ) : Matrix (Fin n) (Fin n) D.host.E :=
  Matrix.diagonal fun i => if i < i.rev then 1 else 0

theorem revM_mul_self (n : ℕ) : revM D n * revM D n = 1 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev (fun k _ hk => by simp [revM, hk]) (by simp)]
  simp [revM, Matrix.one_apply, eq_comm]

theorem adj_revM (n : ℕ) : adj D (revM D n) = revM D n := by
  refine Matrix.ext fun i j => ?_
  have : i = j.rev ↔ j = i.rev := by
    constructor <;> rintro rfl <;> simp
  simp only [adj, revM, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, this]
  split_ifs <;> simp

theorem halfM_mul_self (n : ℕ) : halfM D n * halfM D n = halfM D n := by
  rw [halfM, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem adj_halfM (n : ℕ) : adj D (halfM D n) = halfM D n := by
  rw [adj, halfM, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
  congr 1
  funext i
  split_ifs <;> simp

theorem revM_mul_halfM {n : ℕ} (hn : Even n) : revM D n * halfM D n = revM D n - halfM D n * revM D n := by
  refine Matrix.ext fun i j => ?_
  obtain ⟨k, rfl⟩ := hn
  simp only [halfM, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sub_apply, revM, Matrix.of_apply]
  by_cases h : j = i.rev
  · subst h
    have hi := i.2
    by_cases h1 : i < i.rev
    · have h2 : ¬ i.rev < i := not_lt.2 h1.le
      simp [h1, h2]
    · have h2 : i.rev < i := by
        rw [Fin.lt_def, Fin.val_rev] at *
        omega
      simp [h1, h2]
  · simp [h]

theorem integral_diagonal {n : ℕ} {d : Fin n → D.host.E} (hd : ∀ i, IsIntegral ℤ (d i)) (i j : Fin n) :
    IsIntegral ℤ (Matrix.diagonal d i j) := by
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hd i
  · exact isIntegral_zero

theorem integral_one {n : ℕ} (i j : Fin n) : IsIntegral ℤ ((1 : Matrix (Fin n) (Fin n) D.host.E) i j) :=
  integral_diagonal (fun _ => isIntegral_one) i j

theorem det_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : (adj D M).det = D.host.conj M.det := by
  rw [adj, Matrix.det_transpose]
  exact ((D.host.conj : D.host.E →+* D.host.E).map_det M).symm

theorem adj_one_sub {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (1 - M) = 1 - adj D M := by
  refine Matrix.ext fun i j => ?_
  simp [adj, Matrix.one_apply, eq_comm]

theorem det_mul_conj (hN : Even N) {γ : Matrix (Fin N) (Fin N) D.host.E} (h : γ * adj D γ = 1) :
    γ.det * D.host.conj (1 - γ).det = (1 - γ).det := by
  rw [← det_adj, adj_one_sub, ← Matrix.det_mul, Matrix.mul_sub, h, Matrix.mul_one, ← neg_sub, Matrix.det_neg,
    Fintype.card_fin, hN.neg_one_pow, one_mul]

theorem phase {g w : ℂ} (hw : w ≠ 0) (h : g * (starRingEnd ℂ) w = w) (k : ℕ) :
    ((‖w ^ (k + k)‖ : ℝ) : ℂ) / w ^ (k + k) = g ^ (-(k : ℤ)) := by
  have hg : g ≠ 0 := by rintro rfl; exact hw (by simpa using h.symm)
  have h1 : ((‖w ^ (k + k)‖ : ℝ) : ℂ) = (w * (starRingEnd ℂ) w) ^ k := by
    rw [Complex.mul_conj', norm_pow, ← two_mul, pow_mul]; push_cast; rfl
  rw [h1, zpow_neg, zpow_natCast, div_eq_iff (pow_ne_zero _ hw), eq_inv_mul_iff_mul_eq₀ (pow_ne_zero _ hg), ← mul_pow,
    mul_left_comm, h, mul_pow, pow_add]

theorem pull_eq_smul_iop : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (γA : GA D N) (γ : Matrix (Fin N) (Fin N) D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → (1 - γ).det ≠ 0 → Moves D (γA : GL (Fin N) (AE D)) L₁ → pull D (tor0 D cc δ) γ 1 th = (∏ τ, embT D τ γ.det ^ (-((N' / 2 : ℕ) : ℤ))) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ (stdL D N')) th := by
  intro D cc δ hc N N' hN hN' th hth γA γ L₁ hr hdet hm
  have hu : γ * adj D γ = 1 := (mem_ratG_intG D N).2.2.2.1 γA γ hr
  have hu' : adj D γ * γ = 1 := mul_eq_one_comm.1 hu
  obtain ⟨hint, hden, hmov⟩ := GlobalTheory.T.rationalMatrixMul_thetaLattices D cc δ hc N N'
  let u : VC D N N' ≃ₗ[ℂ] VC D N N' := LinearEquiv.ofLinear (mulV D 1 (adj D γ)) (mulV D 1 γ)
    (LinearMap.ext fun z => by simp [mulV_mulV, hu, mulV_one])
    (LinearMap.ext fun z => by simp [mulV_mulV, hu', mulV_one])
  have ua : ∀ z, u z = mulV D 1 (adj D γ) z := fun _ => rfl
  have us : ∀ z, u.symm z = mulV D 1 γ z := fun _ => rfl
  have hid : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D 1 (1 - γ) :=
    LinearMap.ext fun z => by rw [mulV_sub_right, mulV_one]; rfl
  have hd : LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) =
      ∏ τ, embT D τ (1 - γ).det ^ N' := by
    rw [hid, GlobalTheory.T.det_rationalMatrixTwoSidedMul_eq_prod_embeddings]; simp
  have hw : ∀ τ, embT D τ (1 - γ).det ≠ 0 := fun τ => (map_ne_zero _).2 hdet
  have key := GlobalTheory.T.unitaryThetaConstant_eq_inverseDeterminantPhase D cc δ hc N N' (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L₁ (stdL D N'))
    (klat _ (moves_one D N) (moves_one D N')) (klat _ hm (moves_one D N')) u
    (hf_unitary _ (by rw [adj_one, Matrix.one_mul]) (by rw [adj_adj, hu']))
    (hmov γA 1 γ 1 L₁ _ hr (isRat_one D N') hm (moves_one D N'))
    (by rw [hd]; exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hw τ)) ?_
    (mulV D (halfM D N') 1) (mulV D (revM D N') 1) ?_
    (fun x => by rw [mulV_mulV, halfM_mul_self, Matrix.one_mul])
    (fun x y => by rw [Hf_mulV, adj_halfM, adj_one])
    (fun x => by rw [mulV_mulV, revM_mul_self, Matrix.one_mul, mulV_one])
    (hf_unitary _ (by rw [adj_revM, revM_mul_self]) (by rw [adj_one, Matrix.one_mul]))
    (fun x => by rw [mulV_mulV, mulV_mulV, revM_mul_halfM hN', Matrix.one_mul, mulV_sub_left])
    (fun x => mulV_comm _ _ x) (fun x => mulV_comm _ _ x) ?_ th hth
  · rw [pull_eq, adj_one]
    refine key.trans ?_
    congr 1
    obtain ⟨k, rfl⟩ := hN'
    rw [hd, norm_prod, Complex.ofReal_prod, ← Finset.prod_div_distrib, show (k + k) / 2 = k by omega]
    refine Finset.prod_congr rfl fun τ _ => phase (hw τ) ?_ k
    rw [← embT_conj, ← map_mul, det_mul_conj hN hu]
  · obtain ⟨m₁, h₁, g₁⟩ := hden 1 (1 - γ)⁻¹
    obtain ⟨m₂, h₂, g₂⟩ := hden 1 ((1 - γ)⁻¹ * γ)
    have e : ∀ x : VC D N N', u.symm ((m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x) = (m₁ * m₂) • mulV D 1 ((1 - γ)⁻¹ * γ) x := by
      intro x
      rw [map_nsmul, us, mulV_mulV, Matrix.one_mul]
    refine ⟨m₁ * m₂, Nat.mul_pos h₁ h₂, fun x hx => ⟨(m₁ * m₂) • mulV D 1 (1 - γ)⁻¹ x, ?_, ?_, ?_⟩⟩
    · rw [mul_comm, mul_smul]; exact nsmul_mem (g₁ x hx) _
    · rw [e, mul_smul]; exact nsmul_mem (g₂ x hx) _
    · have h1 : (1 - γ)⁻¹ - (1 - γ)⁻¹ * γ = 1 := by
        have := Matrix.nonsing_inv_mul (1 - γ) (Ne.isUnit hdet)
        rwa [Matrix.mul_sub, Matrix.mul_one] at this
      rw [e, ← smul_sub, ← mulV_sub_right, h1, mulV_one]
  · refine fun x hx => ⟨hint _ _ (integral_diagonal fun i => ?_) integral_one x hx,
      hint _ _ (fun i j => ?_) integral_one x hx⟩
    · split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · rw [revM, Matrix.of_apply]
      split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
  · intro M hM
    obtain ⟨l, b, hlb⟩ := GlobalTheory.NegOneNorm.exists_norm_eq_neg_one D M hM
    have hM' : (M : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
    have hb : D.host.conj (b : D.host.E) = b := by
      have := congrArg D.host.conj hlb
      rw [map_mul, conj_conj, mul_comm, hlb, map_add, map_neg, map_one, map_mul, map_natCast] at this
      exact (mul_left_cancel₀ hM' (add_left_cancel this)).symm
    refine ⟨mulV D (Matrix.diagonal fun _ => (l : D.host.E)) 1, mulV D (Matrix.diagonal fun _ => (b : D.host.E)) 1,
      fun x hx => ⟨hint _ _ (integral_diagonal fun _ => l.2) integral_one x hx,
        hint _ _ (integral_diagonal fun _ => b.2) integral_one x hx⟩,
      fun x => mulV_comm _ _ x, fun x => mulV_comm _ _ x, fun x => ?_, fun x y => ?_, fun x y => ?_⟩
    · rw [mulV_mulV, mulV_mulV, halfM, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      simp only [mul_comm]
    · rw [Hf_mulV, adj_one, adj, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose]
      simp only [hb]
    · have h : ∀ τ, embT D τ l * (starRingEnd ℂ) (embT D τ l) = -1 + M * embT D τ b := by
        intro τ
        rw [← embT_conj, ← map_mul, hlb]; simp
      simp only [Hf, mulV_scalar, ← neg_div, ← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib, map_mul]
      congr 1
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      linear_combination (x τ i j * (starRingEnd ℂ) (y τ i j)) * h τ

end GlobalTheory.RatRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackSecondGroupRationalPointEqDetSmul
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.RatEqui.Col

variable (D : D7) {N N' : ℕ}

theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  have h : ∀ y : D.host.E, D.host.φ₀ (D.host.conj y) = (starRingEnd ℂ) (D.host.φ₀ y) := fun y =>
    D.host.conjE_apply D.host.φ₀ y
  apply (D.host.φ₀ : D.host.E →+* ℂ).injective
  change D.host.φ₀ _ = D.host.φ₀ _
  rw [h, h, Complex.conj_conj]

theorem adj_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (adj D M) = M := by
  ext i j; simp [adj, conj_conj]

theorem adj_one_sub {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : adj D (1 - M) = 1 - adj D M := by
  ext i j
  by_cases h : i = j
  · subst h; simp [adj]
  · simp [adj, Matrix.one_apply, h, Ne.symm h]

theorem det_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) : (adj D M).det = D.host.conj M.det := by
  unfold adj
  rw [Matrix.det_transpose]
  exact (RingHom.map_det (D.host.conj : D.host.E →+* D.host.E) M).symm

theorem adj_diagonal {n : ℕ} (d : Fin n → D.host.E) :
    adj D (Matrix.diagonal d) = Matrix.diagonal fun i => D.host.conj (d i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [adj]
  · simp [adj, Matrix.diagonal_apply, h, Ne.symm h]

theorem sd_of_moves {g : GA D N} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  have : L = Lt g := by ext x; rw [h x, (h1 g).1 x]
  rw [this]; exact (h1 g).2

theorem moves_one (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D N
  rw [← h2]; exact (h1 _).1

theorem isRat_one (N : ℕ) : IsRat D ((1 : GA D N) : GL (Fin N) (AE D)) 1 := by
  unfold IsRat
  rw [Matrix.map_one _ (map_zero _) (map_one _)]
  rfl

def halfP (N : ℕ) : Matrix (Fin N) (Fin N) D.host.E := Matrix.diagonal fun i => if i < i.rev then 1 else 0

def revS (N : ℕ) : Matrix (Fin N) (Fin N) D.host.E := Matrix.of fun i j => if i = j.rev then 1 else 0

theorem halfP_mul : halfP D N * halfP D N = halfP D N := by
  unfold halfP
  rw [Matrix.diagonal_mul_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem adj_halfP : adj D (halfP D N) = halfP D N := by
  unfold halfP
  rw [adj_diagonal]
  congr 1; funext i; split_ifs <;> simp

theorem revS_mul : revS D N * revS D N = 1 := by
  ext i j
  simp only [revS, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem adj_revS : adj D (revS D N) = revS D N := by
  ext i j
  simp only [adj, revS, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
  by_cases h : i = j.rev
  · subst h; simp
  · have h' : ¬ j = i.rev := fun e => h (by rw [e, Fin.rev_rev])
    simp [h, h']

theorem halfP_revS (hN : Even N) : halfP D N * revS D N = revS D N - revS D N * halfP D N := by
  ext i j
  simp only [halfP, revS, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply, Matrix.of_apply]
  by_cases h : i = j.rev
  · subst h
    obtain ⟨k, hk⟩ := hN
    have hj := j.2
    simp only [Fin.rev_rev, if_true, Fin.lt_def, Fin.val_rev]
    split_ifs with h1 h2 h2
    · omega
    · simp
    · simp
    · omega
  · simp [h]

theorem int_ite (p : Prop) [Decidable p] {a : D.host.E} (ha : IsIntegral ℤ a) :
    IsIntegral ℤ (if p then a else 0) := by
  split_ifs
  · exact ha
  · exact isIntegral_zero

theorem mulV_scalar_right (M : ℕ) (b : D.host.E) (x : VC D N N') :
    mulV D 1 (Matrix.diagonal fun _ => -1 + (M : D.host.E) * b) x =
      -x + (M : ℂ) • mulV D 1 (Matrix.diagonal fun _ => b) x := by
  funext τ i j
  change mulV D 1 _ x τ i j = -(x τ i j) + (M : ℂ) * (mulV D 1 _ x τ i j)
  rw [mulV_apply, mulV_apply]
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul,
    Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_map (map_zero _), Matrix.mul_diagonal, Matrix.mul_diagonal]
  simp
  ring

theorem hf_neg_add_smul (T : Tor D) (c : ℂ) (x z y : VC D N N') :
    Hf D T (-x + c • z) y = -Hf D T x y + c * Hf D T z y := by
  simp only [Hf, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, add_mul, neg_mul, mul_assoc,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

theorem Hf_mulV' (T : Tor D) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (z w : VC D N N') : Hf D T z (mulV D M' M w) = Hf D T (mulV D (adj D M') (adj D M) z) w := by
  rw [Hf_mulV, adj_adj, adj_adj]

theorem norm_div_prod {ι : Type} [Fintype ι] (w g : ι → ℂ) (k : ℕ) (hw : ∀ i, w i ≠ 0)
    (h : ∀ i, (starRingEnd ℂ) (w i) = g i * w i) :
    ((‖∏ i, w i ^ (k + k)‖ : ℝ) : ℂ) / ∏ i, w i ^ (k + k) = ∏ i, g i ^ k := by
  rw [norm_prod, Complex.ofReal_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : ((‖w i‖ : ℝ) : ℂ) ^ 2 = g i * w i ^ 2 := by
    rw [← Complex.mul_conj', h]; ring
  rw [norm_pow, Complex.ofReal_pow, ← two_mul, pow_mul, pow_mul, h1, mul_pow,
    mul_div_cancel_right₀ _ (pow_ne_zero _ (pow_ne_zero _ (hw i)))]

end GlobalTheory.RatEqui.Col

open GlobalTheory.RatEqui.Col in

theorem GlobalTheory.RatEqui.pull_right_eq_det_smul : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), Even N → Even N' → ∀ th ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ (γA' : GA D N') (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsRat D (γA' : GL (Fin N') (AE D)) γ' → (1 - γ').det ≠ 0 → Moves D (γA' : GL (Fin N') (AE D)) L₁' → pull D (tor0 D cc δ) 1 γ' th = (∏ τ, embT D τ γ'.det ^ (N / 2)) • Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) (stdL D N) L₁') th := by
  intro D cc δ hc N N' hN hN' th hth γA γ L₁ hrat hdet hmov
  have h1 : γ * adj D γ = 1 := (mem_ratG_intG D N').2.2.2.1 γA γ hrat
  have h2 : adj D γ * γ = 1 := mul_eq_one_comm.1 h1
  obtain ⟨st1, st2, st3⟩ := GlobalTheory.T.rationalMatrixMul_thetaLattices D cc δ hc N N'
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') :=
    Or.inr ⟨_, _, sd_of_moves D (moves_one D N), sd_of_moves D (moves_one D N'), rfl⟩
  have k1 : KLat D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) L₁) :=
    Or.inr ⟨_, _, sd_of_moves D (moves_one D N), sd_of_moves D hmov, rfl⟩
  let u : VC D N N' ≃ₗ[ℂ] VC D N N' := LinearEquiv.ofLinear (mulV D γ 1) (mulV D (adj D γ) 1)
    (LinearMap.ext fun x => by simp [mulV_mulV, h1, mulV_one])
    (LinearMap.ext fun x => by simp [mulV_mulV, h2, mulV_one])
  have hu : ∀ x, u x = mulV D γ 1 x := fun x => rfl
  have hu' : ∀ x, u.symm x = mulV D (adj D γ) 1 x := fun x => rfl
  have hsub : LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N') = mulV D (1 - adj D γ) 1 :=
    LinearMap.ext fun x => by
      rw [mulV_sub_left, mulV_one]; rfl
  have hd : (1 - adj D γ).det = D.host.conj (1 - γ).det := by rw [← adj_one_sub, det_adj]
  have hd0 : (1 - adj D γ).det ≠ 0 := by
    rw [hd]; exact (map_ne_zero _).2 hdet
  have hdV : LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) =
      ∏ τ, embT D τ (1 - adj D γ).det ^ N := by
    rw [hsub, GlobalTheory.T.det_rationalMatrixTwoSidedMul_eq_prod_embeddings]; simp
  have hw : ∀ τ, embT D τ (1 - adj D γ).det ≠ 0 := fun τ => (map_ne_zero _).2 hd0
  have i1 : ∀ i j, IsIntegral ℤ ((1 : Matrix (Fin N') (Fin N') D.host.E) i j) := fun i j => by
    rw [Matrix.one_apply]; exact int_ite D _ isIntegral_one
  have comm : ∀ (M : Matrix (Fin N) (Fin N) D.host.E) x, mulV D 1 M (u x) = u (mulV D 1 M x) := fun M x => by
    simp [hu, mulV_mulV]
  have key := GlobalTheory.T.unitaryThetaConstant_eq_inverseDeterminantPhase D cc δ hc N N' _ _ k0 k1 u
    (fun z w => by rw [hu, hu, Hf_mulV, mulV_mulV, h2, adj_one, mul_one, mulV_one])
    (fun x => by
      rw [st3 1 γA 1 γ _ _ (isRat_one D N) hrat (moves_one D N) hmov x, adj_one, hu])
    (by rw [hdV]; exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (hw τ))
    (by
      obtain ⟨m, hm, hm'⟩ := st2 (1 - adj D γ)⁻¹ 1
      have e : ∀ x : VC D N N', m • x = m • mulV D (1 - adj D γ)⁻¹ 1 x - u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x) := by
        intro x
        have := LinearMap.congr_fun hsub (m • mulV D (1 - adj D γ)⁻¹ 1 x)
        rw [map_nsmul (mulV D (1 - adj D γ) 1), mulV_mulV, Matrix.mul_nonsing_inv _ (Ne.isUnit hd0), mul_one,
          mulV_one] at this
        exact this.symm
      refine ⟨m, hm, fun x hx => ⟨_, hm' x hx, ?_, e x⟩⟩
      have : u.symm (m • mulV D (1 - adj D γ)⁻¹ 1 x) = m • mulV D (1 - adj D γ)⁻¹ 1 x - m • x := by
        rw [e x]; abel
      rw [this]
      exact sub_mem (hm' x hx) (nsmul_mem hx m))
    (mulV D 1 (halfP D N)) (mulV D 1 (revS D N))
    (fun x hx => ⟨st1 _ _ i1 (fun i j => by
        rw [halfP, Matrix.diagonal_apply]; exact int_ite D _ (int_ite D _ isIntegral_one)) x hx,
      st1 _ _ i1 (fun i j => int_ite D _ isIntegral_one) x hx⟩)
    (fun x => by rw [mulV_mulV, halfP_mul, mul_one])
    (fun x y => by rw [Hf_mulV, adj_one, adj_halfP])
    (fun x => by rw [mulV_mulV, revS_mul, mul_one, mulV_one])
    (fun x y => by rw [Hf_mulV, adj_one, adj_revS, mulV_mulV, revS_mul, mul_one, mulV_one])
    (fun x => by rw [mulV_mulV, mulV_mulV, mul_one, halfP_revS D hN, mulV_sub_right])
    (comm _) (comm _)
    (fun M hM => by
      obtain ⟨l, b, hl⟩ := GlobalTheory.NegOneNorm.exists_norm_eq_neg_one D M hM
      have hb : D.host.conj (b : D.host.E) = b := by
        have h3 := congrArg D.host.conj hl
        rw [map_mul, conj_conj, mul_comm, hl, map_add, map_neg, map_one, map_mul, map_natCast] at h3
        exact (mul_left_cancel₀ (Nat.cast_ne_zero.2 hM.ne') (add_left_cancel h3)).symm
      have idg : ∀ a : 𝓞 D.host.E, ∀ i j : Fin N,
          IsIntegral ℤ (Matrix.diagonal (fun _ => (a : D.host.E)) i j) := fun a i j => by
        rw [Matrix.diagonal_apply]; exact int_ite D _ a.2
      refine ⟨mulV D 1 (Matrix.diagonal fun _ => (l : D.host.E)), mulV D 1 (Matrix.diagonal fun _ => (b : D.host.E)),
        fun x hx => ⟨st1 _ _ i1 (idg l) x hx, st1 _ _ i1 (idg b) x hx⟩, comm _, comm _, fun x => ?_,
        fun x y => ?_, fun x y => ?_⟩
      · simp only [mulV_mulV, halfP, Matrix.diagonal_mul_diagonal, mul_comm]
      · rw [Hf_mulV, adj_one, adj_diagonal, hb]
      · rw [Hf_mulV', adj_one, adj_diagonal, mulV_mulV, mul_one, Matrix.diagonal_mul_diagonal, hl,
          mulV_scalar_right, hf_neg_add_smul])
    th hth
  rw [pull_eq]
  refine key.trans ?_
  congr 1
  obtain ⟨k, hk⟩ := hN
  have hk2 : N / 2 = k := by omega
  rw [hdV, hk2]
  have hconj : ∀ τ, (starRingEnd ℂ) (embT D τ (1 - adj D γ).det) =
      embT D τ γ.det * embT D τ (1 - adj D γ).det := fun τ => by
    rw [← embT_conj, ← map_mul, ← Matrix.det_mul, mul_sub, h1, mul_one, hd, conj_conj, ← neg_sub γ 1,
      Matrix.det_neg, Fintype.card_fin, hN'.neg_one_pow, one_mul]
  have := norm_div_prod _ _ k hw hconj
  rwa [← hk] at this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationThetaMovedLatticeStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_theta_moved_lattice : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h : GA D N) (g' h' : GA D N') (L₁ L₂ : Lat D N) (L₁' L₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → ∀ F ∈ Th D (tor0 D cc δ) L₁ L₁', W.Om g g' F ∈ Th D (tor0 D cc δ) L₂ L₂' := by
  first | exact @GlobalTheory.WeilTheta.om_mem_Th_moved | exact GlobalTheory.WeilTheta.om_mem_Th_moved | (intros; apply GlobalTheory.WeilTheta.om_mem_Th_moved <;> assumption)
end

