import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0222
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0231
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeRightBasisExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnAverageHermitianPositive
section
noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel ComplexConjugate

namespace GlobalTheory.CompanionTheory.JSBoundStep

theorem column_average_hermitian_positive : L0 → L3 → ColumnsMirabolic → FormHermitianPositive := by
  intro h0 h3 h3c
  unfold FormHermitianPositive ForR ForF
  intro F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hsm l k B B' hk hW hI hC
  unfold L0 ForF at h0
  unfold L3 ForR ForF at h3
  unfold ColumnsMirabolic ForF at h3c
  obtain ⟨-, hlat⟩ := h0 F μ ψ hψ
  obtain ⟨hlatM, hcv⟩ := hlat (k + 1)
  have h3' := h3 F μ ψ hψ n V ρ hsm
  obtain ⟨hcadd, hc0, hcP, -, -, -⟩ := h3c F μ ψ hψ n k hk
  obtain ⟨herm, psd, null, quasi, -⟩ := hI
  clear h0 h3 h3c hlat
  have hψinv : ∀ t : F, ψ (-t) * ψ t = 1 := fun t => by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hψconj : ∀ t : F, conj (ψ (-t)) = ψ t := by
    intro t
    have hn : ‖ψ (-t)‖ = 1 := hψ.2.2 (-t)
    calc conj (ψ (-t)) = conj (ψ (-t)) * (ψ (-t) * ψ t) := by rw [hψinv, mul_one]
      _ = (conj (ψ (-t)) * ψ (-t)) * ψ t := by ring
      _ = ψ t := by rw [Complex.conj_mul', hn]; simp
  have hinv : ∀ (x : Fin (k + 1) → F) (b : V),
      ρ (PositivityTheory.JacquetShalikaLocal.col n k x) (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) = b := by
    intro x b
    have h1 : PositivityTheory.JacquetShalikaLocal.col n k x * PositivityTheory.JacquetShalikaLocal.col n k (-x) = 1 := by
      rw [← hcadd, add_neg_cancel, hc0]
    calc ρ (PositivityTheory.JacquetShalikaLocal.col n k x) (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b)
        = (ρ (PositivityTheory.JacquetShalikaLocal.col n k x * PositivityTheory.JacquetShalikaLocal.col n k (-x))) b := by rw [map_mul]; rfl
      _ = b := by rw [h1, map_one]; rfl
  have hB : ∀ (x : Fin (k + 1) → F) (a b : V),
      B (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) a) b = B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) := by
    intro x a b
    have hq := quasi (PositivityTheory.JacquetShalikaLocal.col n k x) (hcP x).1 a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b)
    rw [hinv, (hcP x).2.2.1, map_one] at hq
    simpa using hq

  have hnegS : ∀ (M : ℕ), ∀ x ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, -x ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M := by
    intro M x hx
    simp only [PositivityTheory.JacquetShalikaLocal.lat, Set.mem_setOf_eq, Pi.neg_apply, mul_neg] at hx ⊢
    exact fun i => neg_mem (hx i)
  have hvol : ∀ M : ℕ, 0 < (Measure.pi fun _ => μ).real (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) :=
    fun M => (hlatM M).2.2.2
  have hmeas : ∀ M : ℕ, MeasurableSet (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) := fun M => (hlatM M).2.2.1
  have hvol' : ∀ M : ℕ, ∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)
      = (((Measure.pi fun _ => μ).real (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) : ℝ) : ℂ) := by
    intro M
    rw [setIntegral_const]
    simp
  have hv : ∀ M : ℕ, ∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ) ≠ 0 := by
    intro M
    rw [hvol' M]
    exact Complex.ofReal_ne_zero.mpr (hvol M).ne'
  have hmv : ∀ x : Fin (k + 1) → F,
      (↑(-1 : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).mulVec x = -x := by
    intro x
    rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
  have hcvS : ∀ (M : ℕ) (f : (Fin (k + 1) → F) → ℂ),
      ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, f (-x) ∂(Measure.pi fun _ => μ)
        = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, f x ∂(Measure.pi fun _ => μ) := by
    intro M f
    have himg : (fun x => (↑(-1 : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F).mulVec x)
        '' PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M = PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [hmv]
        exact hnegS M y hy
      · intro hx
        exact ⟨-x, hnegS M x hx, by simp only [hmv, neg_neg]⟩
    have e1 := hcv (-1) (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) (fun _ => (1 : ℂ)) (hmeas M)
    have e2 := hcv (-1) (PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M) f (hmeas M)
    rw [himg] at e1 e2
    simp only [hmv] at e2
    have alg : ∀ c v I J : ℂ, v ≠ 0 → v = c * v → I = c * J → J = I := by
      intro c v I J hv0 h1 h2
      have hc : c = 1 := by
        have : c * v = 1 * v := by rw [← h1, one_mul]
        exact mul_right_cancel₀ hv0 this
      rw [h2, hc, one_mul]
    exact alg _ _ _ _ (hv M) e1 e2

  have hξ : ∀ x : Fin (k + 1) → F, Pi.single (Fin.last k) (1 : F) ⬝ᵥ x = x (Fin.last k) := by
    intro x
    simp [dotProduct, Pi.single_apply]
  choose P hP1 hP2 using fun (M : ℕ) (u : V) => h3' k M (Pi.single (Fin.last k) (1 : F)) u
  simp only [hξ] at hP1 hP2
  have hSA : ∀ (M : ℕ) (a b : V), B (P M a) b = B a (P M b) := by
    intro M a b
    calc B (P M a) b = conj (B b (P M a)) := (herm b (P M a)).symm
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            conj (ψ (-x (Fin.last k)) * B b (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) a)) ∂(Measure.pi fun _ => μ) := by
          rw [hP1 M a (B b), integral_conj]
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            ψ (-(-x) (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k (-x)) b) ∂(Measure.pi fun _ => μ) := by
          congr 1
          funext x
          rw [map_mul, hψconj, herm, hB x a b]
          simp only [Pi.neg_apply, neg_neg]
      _ = ∫ x in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M,
            ψ (-x (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) b) ∂(Measure.pi fun _ => μ) :=
          hcvS M (fun x => ψ (-x (Fin.last k)) * B a (ρ (PositivityTheory.JacquetShalikaLocal.col n k x) b))
      _ = B a (P M b) := (hP1 M b (B a)).symm
  have hE : ∀ (M : ℕ) (u v : V),
      (∀ y ∈ PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, ρ (PositivityTheory.JacquetShalikaLocal.col n k y) v = ψ (y (Fin.last k)) • v) →
      B u (P M v) = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * B u v := by
    intro M u v hv0
    rw [hP1 M v (B u), ← integral_mul_const]
    refine setIntegral_congr_fun (hmeas M) ?_
    intro x hx
    beta_reduce
    rw [hv0 x hx, map_smul, smul_eq_mul, ← mul_assoc, hψinv]
  have hL : ∀ (M : ℕ) (u : V),
      l (P M u) = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * l u := by
    intro M u
    rw [hP1 M u l, ← integral_mul_const]
    congr 1
    funext x
    rw [hW (PositivityTheory.JacquetShalikaLocal.col n k x) (hcP x).2.1.1 u, (hcP x).2.2.2, ← mul_assoc, hψinv]
  have hrel : ∀ (M : ℕ) (u : V), B (P M u) (P M u)
      = (∫ _ in PositivityTheory.JacquetShalikaLocal.lat F (k + 1) M, (1 : ℂ) ∂(Measure.pi fun _ => μ)) * B u (P M u) := by
    intro M u
    rw [hSA M u (P M u), hE M u (P M u) (hP2 M u)]
  have hchar : ∀ u u' : V, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → B' u' u = B u' (P M u) := by
    intro u u'
    obtain ⟨M₀, h⟩ := hC u u'
    exact ⟨M₀, fun M hM => by rw [h M hM, hP1 M u (B u')]⟩
  refine ⟨fun u u' => ?_, fun u => ?_, fun u hu => ?_⟩
  · obtain ⟨M1, h1⟩ := hchar u u'
    obtain ⟨M2, h2⟩ := hchar u' u
    rw [h2 (max M1 M2) (le_max_right _ _), h1 (max M1 M2) (le_max_left _ _), herm, hSA]
  · obtain ⟨M1, h1⟩ := hchar u u
    rw [h1 M1 le_rfl]
    have hp := psd (P M1 u)
    rw [hrel M1 u, hvol' M1, Complex.re_ofReal_mul] at hp
    exact (mul_nonneg_iff_of_pos_left (hvol M1)).mp hp
  · obtain ⟨M1, h1⟩ := hchar u u
    rw [h1 M1 le_rfl] at hu
    have h0' : B (P M1 u) (P M1 u) = 0 := by rw [hrel, hu, mul_zero]
    have hl0 := null (P M1 u) h0'
    rw [hL M1 u] at hl0
    exact (mul_eq_zero.mp hl0).resolve_left (hv M1)

end GlobalTheory.CompanionTheory.JSBoundStep

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColumnAverageQuasiInvariant
section
noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.JSBound

section Lattice

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem unif_ne_zero : (uniformizer F : F) ≠ 0 := fun h =>
  valuation_uniformizer_ne_zero F (by rw [h, map_zero])

theorem unif_pow_ne_zero (M : ℕ) : (uniformizer F : F) ^ M ≠ 0 := pow_ne_zero _ unif_ne_zero

theorem exists_unif_pow_mul_mem (x : F) : ∃ m : ℕ, (uniformizer F : F) ^ m * x ∈ 𝒪[F] := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hvx : ValuativeRel.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  obtain ⟨m, hm⟩ := exists_pow_lt₀ (valuation_uniformizer_lt_one F) (Units.mk0 _ hvx)⁻¹
  refine ⟨m, ?_⟩
  have h1 : ValuativeRel.valuation F (uniformizer F : F) ^ m * ValuativeRel.valuation F x < 1 := by
    have := mul_lt_mul_of_pos_right hm (zero_lt_iff.mpr hvx)
    simpa [hvx] using this
  rw [Valuation.mem_integer_iff, map_mul, map_pow]
  exact h1.le

theorem unif_pow_mul_mem_of_le {m m' : ℕ} (h : m ≤ m') {y : F}
    (hy : (uniformizer F : F) ^ m * y ∈ 𝒪[F]) : (uniformizer F : F) ^ m' * y ∈ 𝒪[F] := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have h1 : (uniformizer F : F) ^ d ∈ 𝒪[F] := pow_mem (uniformizer F).2 d
  have := mul_mem h1 hy
  rwa [← mul_assoc, ← pow_add, add_comm d m] at this

theorem exists_div_unif_pow_smul {ι : Type} [Finite ι] (A : Matrix ι ι F) (c : ℕ) :
    ∃ N : ℕ, ∀ M, N ≤ M → Div c ((uniformizer F : F) ^ M • A) := by
  classical
  cases nonempty_fintype ι
  choose f hf using fun p : ι × ι => exists_unif_pow_mul_mem (A p.1 p.2)
  refine ⟨c + Finset.univ.sup f, fun M hM i j => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
  have hle : f (i, j) ≤ Finset.univ.sup f + d :=
    (Finset.le_sup (f := f) (Finset.mem_univ (i, j))).trans (Nat.le_add_right _ _)
  refine ⟨_, unif_pow_mul_mem_of_le hle (hf (i, j)), ?_⟩
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_add, add_assoc]

def scG (m M : ℕ) : GL (Fin m) F where
  val := ((uniformizer F : F) ^ M)⁻¹ • (1 : Matrix (Fin m) (Fin m) F)
  inv := ((uniformizer F : F) ^ M) • (1 : Matrix (Fin m) (Fin m) F)
  val_inv := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ (unif_pow_ne_zero M), one_mul, one_smul]
  inv_val := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ (unif_pow_ne_zero M), one_mul, one_smul]

theorem image_scG_lat (m M : ℕ) :
    (fun x => ((scG m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) *ᵥ x) '' lat F m 0 =
      lat F m M := by
  have hval : ((scG m M : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      ((uniformizer F : F) ^ M)⁻¹ • (1 : Matrix (Fin m) (Fin m) F) := rfl
  ext x
  simp only [Set.mem_image, hval, Matrix.smul_mulVec, Matrix.one_mulVec]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    have := hy i
    simp only [pow_zero, one_mul] at this
    simpa [unif_pow_ne_zero M] using this
  · intro hx
    refine ⟨(uniformizer F : F) ^ M • x, fun i => ?_, ?_⟩
    · simpa using hx i
    · rw [smul_smul, inv_mul_cancel₀ (unif_pow_ne_zero M), one_smul]

end Lattice

theorem column_average_quasi_invariant : L0 → ColumnsMirabolic → FormCoefficientStability → FormQuasiInvariantMirabolic := by
  intro h0 h3 h4 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B B' hk hI hC g hg u' u
  have H0 := h0 F μ ψ hψ
  obtain ⟨-, -, -, hPP, hT, -⟩ := h3 F μ ψ hψ n k hk
  have hg1 := hPP g hg
  obtain ⟨t, hdet, hcomm, hlast⟩ := hT g hg1
  have hlast' := hlast hg
  have := Measures.metrizableSpace F
  obtain ⟨T, hTdef⟩ : ∃ T, T = (t : Matrix (Fin (k + 1)) (Fin (k + 1)) F) := ⟨_, rfl⟩
  obtain ⟨Ti, hTidef⟩ : ∃ Ti, Ti = ((t⁻¹ : GL (Fin (k + 1)) F) : Matrix (Fin (k + 1)) (Fin (k + 1)) F) :=
    ⟨_, rfl⟩
  rw [← hTdef] at hdet hcomm hlast'
  have hTTi : ∀ x, T *ᵥ (Ti *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hTdef, hTidef, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hTiT : ∀ x, Ti *ᵥ (T *ᵥ x) = x := fun x => by
    rw [Matrix.mulVec_mulVec, hTdef, hTidef, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  let h : (Fin (k + 1) → F) → ℂ := fun x => ψ (-x (Fin.last k)) * B u' (ρ (col n k x) u)
  have hpt : ∀ x, ψ (-x (Fin.last k)) * B (ρ g u') (ρ (col n k x) (ρ g u)) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        h (Ti *ᵥ x) := by
    intro x
    have e1 : col n k x * g = g * col n k (Ti *ᵥ x) := by rw [hcomm, hTTi]
    have e2 : ρ (col n k x) (ρ g u) = ρ g (ρ (col n k (Ti *ᵥ x)) u) := by
      rw [← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply]
    have e3 : (Ti *ᵥ x) (Fin.last k) = x (Fin.last k) := by
      have := hlast' (Ti *ᵥ x)
      rw [hTTi] at this
      exact this.symm
    rw [e2, hI.quasi g hg1]
    simp only [h, e3]
    ring
  obtain ⟨M₁, hM₁⟩ := hC (ρ g u) (ρ g u')
  obtain ⟨M₂, hM₂⟩ := hC u u'
  obtain ⟨-, c, hc⟩ := h4 F μ ψ hψ n V ρ hρ l k B hk hI u u'
  obtain ⟨N, hN⟩ := exists_div_unif_pow_smul T (c + 1)
  obtain ⟨N', hN'⟩ := exists_div_unif_pow_smul (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (c + 1)

  obtain ⟨M, hMM₁, hMN⟩ : ∃ M, M₁ ≤ M ∧ N ≤ M := ⟨max M₁ N, le_max_left _ _, le_max_right _ _⟩
  have step1 : B' (ρ g u') (ρ g u) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        ∫ x in lat F (k + 1) M, h (Ti *ᵥ x) ∂(Measure.pi fun _ => μ) := by
    rw [hM₁ M hMM₁, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hcont : Continuous fun x : Fin (k + 1) → F => Ti *ᵥ x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  have hmeas : MeasurableSet ((fun x => Ti *ᵥ x) '' lat F (k + 1) M) :=
    (((H0.2 (k + 1)).1 M).1.image hcont).measurableSet
  have step2 := (H0.2 (k + 1)).2 t ((fun x => Ti *ᵥ x) '' lat F (k + 1) M)
    (fun x => h (Ti *ᵥ x)) hmeas
  rw [← hTdef, Set.image_image] at step2
  simp only [hTTi, hTiT, Set.image_id'] at step2

  have hG : (fun x => (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F) : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x) '' lat F (k + 1) 0 =
      (fun x => Ti *ᵥ x) '' lat F (k + 1) M := by
    rw [← image_scG_lat (k + 1) M, Set.image_image]
    refine Set.image_congr fun x _ => ?_
    rw [Units.val_mul, ← hTidef, Matrix.mulVec_mulVec]
  have hGdiv : Div (c + 1) (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) := by
    have : (((t⁻¹ * scG (k + 1) M : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) F) = (uniformizer F : F) ^ M • T := by
      rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, hTdef]
      change ((uniformizer F : F) ^ M • (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F)) * _ = _
      rw [Matrix.smul_mul, Matrix.one_mul]
    rw [this]
    exact hN M hMN
  have step3 := hc _ hGdiv
  rw [hG] at step3

  obtain ⟨M', hM'₂, hM'N⟩ : ∃ M', M₂ ≤ M' ∧ N' ≤ M' :=
    ⟨max M₂ N', le_max_left _ _, le_max_right _ _⟩
  have hSdiv : Div (c + 1) (((scG (k + 1) M' : GL (Fin (k + 1)) F)⁻¹ : GL (Fin (k + 1)) F) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) F) := hN' M' hM'N
  have step4 := hc _ hSdiv
  rw [image_scG_lat] at step4
  have step5 := hM₂ M' hM'₂
  have hmod : (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - k) =
      (((Measures.modulus (g : Matrix (Fin n) (Fin n) F).det : ℝ) : ℂ)) ^ (n - 1 - (k + 1)) *
        ((Measures.modulus T.det : ℝ) : ℂ) := by
    rw [hdet, ← pow_succ]
    congr 1
    omega
  rw [step1, step2, hmod, mul_assoc]
  congr 2
  rw [step5, step4]
  exact step3

end GlobalTheory.CompanionTheory.JSBound

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfTrivialInteger
section
open PositivityTheory.JacquetShalikaLocal

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel NNReal Pointwise

namespace GlobalTheory.CompanionTheory.JSBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_of_trivial_integer {ψ : AddChar F ℂ} (h : ∀ x ∈ 𝒪[F], ψ x = 1) : Continuous ψ := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' (𝒪[F] : Set F),
    (Valuation.isOpen_integer).preimage (by fun_prop), ?_, ?_⟩
  · simpa using (𝒪[F]).zero_mem
  · intro y hy
    have hxy : y = x + (y - x) := by ring
    rw [hxy, AddChar.map_add_eq_mul, h _ hy, mul_one]

theorem uniformizer_pow_ne_zero (M : ℕ) : (uniformizer F : F) ^ M ≠ 0 :=
  pow_ne_zero _ ((Valuation.ne_zero_iff _).mp (valuation_uniformizer_ne_zero F))

theorem lat_eq_preimage (m M : ℕ) : lat F m M =
    (Homeomorph.smulOfNeZero ((uniformizer F : F) ^ M) (uniformizer_pow_ne_zero M)) ⁻¹'
      Measures.box F (Fin m) := by
  ext x
  simp [lat, Measures.mem_box]

theorem isOpen_lat (m M : ℕ) : IsOpen (lat F m M) := by
  rw [lat_eq_preimage]
  exact Measures.isOpen_box.preimage (Homeomorph.continuous _)

theorem isCompact_lat (m M : ℕ) : IsCompact (lat F m M) := by
  rw [lat_eq_preimage]
  exact (Homeomorph.isCompact_preimage _).2 Measures.isCompact_box

theorem zero_mem_lat (m M : ℕ) : (0 : Fin m → F) ∈ lat F m M := by
  intro i
  simpa using (𝒪[F]).zero_mem

variable [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

theorem lat_measure_pos (m M : ℕ) :
    0 < (Measure.pi fun _ : Fin m => μ).real (lat F m M) := by
  haveI := Measures.sigmaCompactSpace F
  have h0 := (isOpen_lat (F := F) m M).measure_ne_zero (Measure.pi fun _ : Fin m => μ)
    ⟨0, zero_mem_lat m M⟩
  have h1 := (isCompact_lat (F := F) m M).measure_lt_top (μ := Measure.pi fun _ : Fin m => μ)
  exact ENNReal.toReal_pos h0 h1.ne

theorem setIntegral_image_mulVec {m : ℕ} (g : GL (Fin m) F) (A : Set (Fin m → F))
    (f : (Fin m → F) → ℂ) :
    ∫ x in (fun x => (g : Matrix (Fin m) (Fin m) F) *ᵥ x) '' A, f x ∂(Measure.pi fun _ => μ) =
      ((Measures.modulus (g : Matrix (Fin m) (Fin m) F).det : ℝ) : ℂ) *
        ∫ x in A, f ((g : Matrix (Fin m) (Fin m) F) *ᵥ x) ∂(Measure.pi fun _ => μ) := by
  haveI := Measures.sigmaCompactSpace F
  haveI := Measures.metrizableSpace F
  set ν : Measure (Fin m → F) := Measure.pi fun _ => μ with hν
  set L := Measures.glEquiv g with hL
  let e : (Fin m → F) ≃ᵐ (Fin m → F) := (Homeomorph.smul L).toMeasurableEquiv
  have he : ∀ x, e x = (g : Matrix (Fin m) (Fin m) F) *ᵥ x := fun x => Measures.glEquiv_apply g x
  have hc : distribHaarChar (Fin m → F) L =
      Measures.modulus (g : Matrix (Fin m) (Fin m) F).det := by
    rw [hL, Measures.distribHaarChar_glEquiv, ← Measures.modulus_units]
    rfl
  have hmap : ν.map e.symm = (Measures.modulus (g : Matrix (Fin m) (Fin m) F).det) • ν := by
    refine Measure.ext fun s _ => ?_
    have hs : e.symm ⁻¹' s = L • s := (e.image_eq_preimage_symm s).symm
    rw [e.symm.map_apply, hs, ← distribHaarChar_mul ν L s, hc, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul]
  have himg : (fun x => (g : Matrix (Fin m) (Fin m) F) *ᵥ x) '' A = e.symm ⁻¹' A := by
    rw [← e.image_eq_preimage_symm]
    exact Set.image_congr fun x _ => (he x).symm
  have key := setIntegral_map_equiv (μ := ν) e.symm (fun x => f (e x)) A
  simp only [MeasurableEquiv.apply_symm_apply] at key
  rw [himg, ← key, hmap, Measure.restrict_smul, integral_smul_nnreal_measure]
  simp only [he, NNReal.smul_def, Complex.real_smul]

theorem l0 : L0 := by
  intro F _ _ _ _ _ _ μ _ ψ hψ
  refine ⟨continuous_of_trivial_integer hψ.1, fun m => ⟨fun M => ?_, fun g A f _ => ?_⟩⟩
  · exact ⟨isCompact_lat m M, isOpen_lat m M, (isOpen_lat m M).measurableSet, lat_measure_pos μ m M⟩
  · exact setIntegral_image_mulVec μ g A f

end GlobalTheory.CompanionTheory.JSBound

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetRepsOfFactorization
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

namespace GlobalTheory.CompanionTheory.SatPow.RepsGen

private theorem mem_map_conj_iff_inv_mul_mul_mem {G : Type*} [Group G] (I : Subgroup G) (t y : G) :
    y ∈ I.map (MulAut.conj t).toMonoidHom ↔ t⁻¹ * y * t ∈ I := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hx
  · intro h
    exact ⟨t⁻¹ * y * t, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem reps_of_quotient_with_property (G : Type) [Group G] (I : Subgroup G) (t : G) (P : G → Prop)
    (hP1 : P 1)
    (hfin : Finite (I ⧸ (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I))
    (hfac : ∀ i ∈ I, ∃ u ∈ I, P u ∧ ∃ y ∈ I, t⁻¹ * y * t ∈ I ∧ i = u * y) :
    ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ r ∈ R, r ∈ I ∧ P r) ∧
      ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I := by
  classical
  set H := (I ⊓ I.map (MulAut.conj t).toMonoidHom).subgroupOf I with hH
  have : Fintype (I ⧸ H) := @Fintype.ofFinite _ hfin
  have hmem : ∀ a b : I, (QuotientGroup.mk a : I ⧸ H) = QuotientGroup.mk b ↔
      t⁻¹ * ((a : G)⁻¹ * b) * t ∈ I := by
    intro a b
    rw [QuotientGroup.eq, hH, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      and_iff_right (a⁻¹ * b).2, mem_map_conj_iff_inv_mul_mul_mem]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  have key : ∀ c : I ⧸ H, ∃ r : I, P r ∧ (QuotientGroup.mk r : I ⧸ H) = c ∧
      (c = QuotientGroup.mk 1 → r = 1) := by
    intro c
    obtain ⟨i, rfl⟩ := QuotientGroup.mk_surjective c
    by_cases h : (QuotientGroup.mk i : I ⧸ H) = QuotientGroup.mk 1
    · exact ⟨1, by simpa using hP1, h.symm, fun _ => rfl⟩
    · obtain ⟨u, hu, hPu, y, hy, hty, hi⟩ := hfac i i.2
      refine ⟨⟨u, hu⟩, hPu, ?_, fun h' => absurd h' h⟩
      rw [hmem]
      have hy' : u⁻¹ * (i : G) = y := by rw [hi, inv_mul_cancel_left]
      show t⁻¹ * (u⁻¹ * (i : G)) * t ∈ I
      rw [hy']
      exact hty
  choose f hfP hfmk hf1 using key
  refine ⟨Finset.univ.image (fun c => (f c : G)), ?_, ?_, ?_⟩
  · exact Finset.mem_image.2 ⟨QuotientGroup.mk 1, Finset.mem_univ _, by rw [hf1 _ rfl]; simp⟩
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    exact ⟨(f c).2, hfP c⟩
  · intro i hi
    refine ⟨f (QuotientGroup.mk ⟨i, hi⟩),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · exact (hmem (f (QuotientGroup.mk ⟨i, hi⟩)) ⟨i, hi⟩).1 (hfmk _)
    · rintro r ⟨hr, hri⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
      have hc : c = QuotientGroup.mk ⟨i, hi⟩ := (hfmk c).symm.trans ((hmem _ _).2 hri)
      subst hc
      rfl

end GlobalTheory.CompanionTheory.SatPow.RepsGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeRightBasisExpansionStatement
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_right_basis_expansion : ∀ n : ℕ, ∃ A : (Bool × Fin n × Fin n) → Mat n → CLof (Mat n) ℝ, (∀ p, ContDiffOn ℝ ∞ (A p) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (D : CLof (Mat n) V), ∀ z ∈ GLs n, D = ∑ p, (A p z).smulRight (D (z * bs p)) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.Frame.frame | exact GlobalTheory.CompanionTheory.PresSobA.Frame.frame | (intros; apply GlobalTheory.CompanionTheory.PresSobA.Frame.frame <;> assumption)
end
end

