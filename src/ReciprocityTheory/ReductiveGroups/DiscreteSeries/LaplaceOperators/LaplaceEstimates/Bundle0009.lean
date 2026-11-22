import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMC
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0007
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ThreeAddLeGapBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.Bundle0004
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinProj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.FinFub

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMD
section
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvalC

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

section Alg

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰]

theorem cminor_reindex {n n' : ℕ} (F : Fin n → Fin n → 𝒰) (e : Fin n' → Fin n) (he : Function.Injective e)
    {p : ℕ} (R C : Fin p → Fin n') (x : ℂ) :
    cminor (fun a b => F (e a) (e b)) R C x = cminor F (e ∘ R) (e ∘ C) x := by
  unfold cminor capEntry
  simp only [Function.comp_apply, he.eq_iff]

theorem cminor_cast {n p p' : ℕ} (h : p = p') (F : Fin n → Fin n → 𝒰) (R C : Fin p' → Fin n) (x : ℂ) :
    cminor F (R ∘ Fin.cast h) (C ∘ Fin.cast h) x = cminor F R C x := by
  subst h; rfl

theorem sign_mul_self_C {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ((Equiv.Perm.sign σ : ℤˣ) : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem cminor_frameAB_minor {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → 𝒰) (hE : GlRelR E)
    (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hAB : A * B = 1) (a b : Fin (m + 1)) (x : ℂ) :
    cminor (frameAB A B E) a.succAbove b.succAbove x = ∑ c : Fin (m + 1), ∑ d : Fin (m + 1),
      ((A.submatrix a.succAbove c.succAbove).det * (B.submatrix d.succAbove b.succAbove).det) •
        cminor E c.succAbove d.succAbove x := by
  set f : ℂ := ((m.factorial : ℕ) : ℂ)
  have hf : f * f ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
  suffices key : (f * f) • cminor (frameAB A B E) a.succAbove b.succAbove x = (f * f) •
      ∑ c : Fin (m + 1), ∑ d : Fin (m + 1),
        ((A.submatrix a.succAbove c.succAbove).det * (B.submatrix d.succAbove b.succAbove).det) •
          cminor E c.succAbove d.succAbove x by
    have := congrArg (fun y => (f * f)⁻¹ • y) key
    simpa only [inv_smul_smul₀ hf] using this
  rw [cminor_frameAB_cb E hE A B hAB]
  rw [sum_symm_inj (fun ρ => ∑ τ : Fin m → Fin (m + 1),
      ((A.submatrix a.succAbove ρ).det * (B.submatrix τ b.succAbove).det) • cminor E ρ τ x)]
  · rw [mul_smul]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sum_symm_inj (fun τ => ((A.submatrix a.succAbove c.succAbove).det * (B.submatrix τ b.succAbove).det) •
      cminor E c.succAbove τ x)]
    · intro τ σ
      have h1 : B.submatrix (τ ∘ σ) b.succAbove = (B.submatrix τ b.succAbove).submatrix σ id := rfl
      simp only [h1, Matrix.det_permute]
      rw [cminor_perm_cols E hE, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
      congr 1
      linear_combination ((A.submatrix a.succAbove c.succAbove).det * (B.submatrix τ b.succAbove).det) *
        sign_mul_self_C σ
    · intro τ hτ
      have : (B.submatrix τ b.succAbove).det = 0 := by
        simp only [Function.Injective, not_forall] at hτ
        obtain ⟨i, j, hij, hne⟩ := hτ
        exact Matrix.det_zero_of_row_eq hne (by funext l; simp [hij])
      simp [this]
  · intro ρ σ
    have h1 : A.submatrix a.succAbove (ρ ∘ σ) = (A.submatrix a.succAbove ρ).submatrix id σ := rfl
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [h1, Matrix.det_permute']
    rw [cminor_perm_rows E, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    congr 1
    linear_combination ((A.submatrix a.succAbove ρ).det * (B.submatrix τ b.succAbove).det) * sign_mul_self_C σ
  · intro ρ hρ
    have : (A.submatrix a.succAbove ρ).det = 0 := by
      simp only [Function.Injective, not_forall] at hρ
      obtain ⟨i, j, hij, hne⟩ := hρ
      exact Matrix.det_zero_of_column_eq hne (fun l => by simp [hij])
    simp [this]

end Alg

section Cov

theorem adjugate_eq_of_mul {n : ℕ} (g g' : Matrix (Fin n) (Fin n) ℂ) (h : g' * g = 1) :
    Matrix.adjugate g = g.det • g' := by
  calc Matrix.adjugate g = (g' * g) * Matrix.adjugate g := by rw [h, Matrix.one_mul]
    _ = g' * (g * Matrix.adjugate g) := by rw [Matrix.mul_assoc]
    _ = g' * (g.det • (1 : Matrix (Fin n) (Fin n) ℂ)) := by rw [Matrix.mul_adjugate]
    _ = g.det • g' := by rw [Matrix.mul_smul, Matrix.mul_one]

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
  rw [← mul_pow]; simp

theorem det_sub_succAbove {m : ℕ} (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (h : g' * g = 1)
    (i j : Fin (m + 1)) :
    (g.submatrix i.succAbove j.succAbove).det = (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (g.det * g' j i) := by
  have h1 := Matrix.adjugate_fin_succ_eq_det_submatrix g j i
  rw [adjugate_eq_of_mul g g' h, Matrix.smul_apply, smul_eq_mul] at h1
  rw [h1, ← mul_assoc, neg_one_pow_mul_self, one_mul]

end Cov

end ReciprocityTheory.ChartRestriction.DS.Lap.EvalC

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Matrix ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.EvalC

universe u

def CapelliCovStatement : Prop :=
  ∀ (𝒰 : Type u) [Ring 𝒰] [Algebra ℂ 𝒰] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → 𝒰)
    (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (x : ℂ), Capelli.GlRelR E → g * g' = 1 →
    ∀ d c : Fin (m + 1),
      ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
          Capelli.cminor (fun a b => ∑ c', ∑ d', (g c' a * g' b d') • E c' d') d.succAbove c.succAbove x =
        ∑ d', ∑ c', (g' d d' * g c' c * (-1 : ℂ) ^ ((d' : ℕ) + (c' : ℕ))) •
          Capelli.cminor E d'.succAbove c'.succAbove x

theorem capelliCov : CapelliCovStatement.{u} := by
  intro 𝒰 _ _ m E g g' x hE hgg' d c
  have hg'g : g' * g = 1 := mul_eq_one_comm.mp hgg'
  have hAB : gᵀ * g'ᵀ = 1 := by rw [← Matrix.transpose_mul, hg'g, Matrix.transpose_one]
  have hfam : (fun a b => ∑ c', ∑ d', (g c' a * g' b d') • E c' d') = frameAB gᵀ g'ᵀ E := rfl
  have hD : g.det * g'.det = 1 := by rw [← Matrix.det_mul, hgg', Matrix.det_one]
  rw [hfam, cminor_frameAB_minor E hE _ _ hAB d c x, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [smul_smul]
  congr 1
  have e1 : (gᵀ.submatrix d.succAbove d'.succAbove).det = (g.submatrix d'.succAbove d.succAbove).det := by
    rw [← Matrix.det_transpose]; rfl
  have e2 : (g'ᵀ.submatrix c'.succAbove c.succAbove).det = (g'.submatrix c.succAbove c'.succAbove).det := by
    rw [← Matrix.det_transpose]; rfl
  rw [e1, e2, det_sub_succAbove g g' hg'g, det_sub_succAbove g' g hgg']
  simp only [pow_add]
  linear_combination (g' d d' * g c' c * (-1 : ℂ) ^ (d' : ℕ) * (-1 : ℂ) ^ (c' : ℕ)) *
    (((-1 : ℂ) ^ (c : ℕ) * (-1 : ℂ) ^ (c : ℕ) * (g.det * g'.det)) * neg_one_pow_mul_self (d : ℕ) +
      (g.det * g'.det) * neg_one_pow_mul_self (c : ℕ) + hD)

section Frame

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem frameE_eq_frameAB {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → Module.End ℂ M) :
    frameE Q E = EvalC.frameAB (Q⁻¹)ᵀ Qᵀ E := rfl

theorem frameE_glRep {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Q * Q⁻¹ = 1)
    (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) : IsGlRep (frameE Q E) := by
  rw [frameE_eq_frameAB]
  exact EvalC.frameAB_glRel _ _ (by rw [← Matrix.transpose_mul, hQ, Matrix.transpose_one]) E hE

theorem frameE_cov {m : ℕ} (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hQ : Q⁻¹ * Q = 1)
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : IsGlRep E) (α γ : Fin (m + 1) → ℂ) (x : ℂ) :
    ∑ d : Fin (m + 1), ∑ c : Fin (m + 1), (α d * γ c * (-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        Capelli.cminor (frameE Q E) d.succAbove c.succAbove x =
      ∑ d : Fin (m + 1), ∑ c : Fin (m + 1), ((Qᵀ *ᵥ α) d * (Q⁻¹ *ᵥ γ) c * (-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        Capelli.cminor E d.succAbove c.succAbove x := by
  have hcov := capelliCov (Module.End ℂ M) m E Q⁻¹ Q x hE hQ
  have e : ∀ d c : Fin (m + 1), (α d * γ c * (-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
      Capelli.cminor (frameE Q E) d.succAbove c.succAbove x =
      (α d * γ c) • ∑ d' : Fin (m + 1), ∑ c' : Fin (m + 1),
        (Q d d' * Q⁻¹ c' c * (-1 : ℂ) ^ ((d' : ℕ) + (c' : ℕ))) • Capelli.cminor E d'.succAbove c'.succAbove x := by
    intro d c; rw [mul_smul, ← hcov d c]; rfl
  simp only [e, Finset.smul_sum, smul_smul]
  rw [EvalC.sum_four_swap_pairs_alt (fun d' c' d c => (α d * γ c * (Q d d' * Q⁻¹ c' c * (-1 : ℂ) ^ ((d' : ℕ) + (c' : ℕ)))) •
    Capelli.cminor E d'.succAbove c'.succAbove x)]
  refine Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp only [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end Frame

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.QuotPA
section
noncomputable section

open Matrix MeasureTheory Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.QuotA

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.LemK

section Map

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def tL (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) : (Fin (2 * r + k + 1) → D) →ₗ[ℂ] (Mat k r → ℂ) where
  toFun f := tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H))
  map_add' f f' := by
    funext g
    simp only [tMap, coefX, Pi.add_apply, Submodule.coe_add, map_add, inner_add_right, mul_add,
      Finset.sum_add_distrib]
  map_smul' a f := by
    funext g
    simp only [tMap, coefX, Pi.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring

theorem tL_apply (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (f : Fin (2 * r + k + 1) → D) :
    tL ε σ x₁ x₀ w f = tMap ε σ x₁ x₀ w (fun c => ((f c : D) : H)) := rfl

end Map

section Hull

variable {n : ℕ} {ε : Fin n → Bool} {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem exists_kStable_finiteDimensional_submodule_of_mem_Xs (hE : IsGlRep E) (hVfd : FiniteDimensional ℂ V) (hVk : IsKStableSub ε E V) {θ : ℝ}
    {x : Fin n → M} (hx : x ∈ Xs (LemK.eeV E) (genSub E V) θ) :
    ∃ S : Submodule ℂ (Fin n → M), S ≤ Xs (LemK.eeV E) (genSub E V) θ ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensV E) S ∧ x ∈ S := by
  classical
  have hxg := (mem_eigenTensorSpace_gen_iff.1 hx).1
  choose m hm using fun c => exists_layer_of_mem_genSub hE hVk (hxg c)
  set K := Finset.univ.sup m
  have hxK : ∀ c, x c ∈ layer ε E V K := fun c => layer_mono (Finset.le_sup (mem_univ c)) (hm c)
  have hfdL : FiniteDimensional ℂ (layer ε E V K) := finiteDimensional_layer hVfd K
  have hLk := layer_kStable hE hVk K
  have := pi_submodule_finiteDimensional (n := n) (layer ε E V K)
  refine ⟨Submodule.pi Set.univ (fun _ => layer ε E V K) ⊓ Xs (LemK.eeV E) (genSub E V) θ, inf_le_right,
    Submodule.finiteDimensional_of_le inf_le_left, ?_, ⟨mem_pi_submodule_iff.2 hxK, hx⟩⟩
  intro a b hab f hf
  refine ⟨mem_pi_submodule_iff.2 fun c => ?_, eigenTensorSpace_stable hE a b hf.2⟩
  rw [entry_bounds_of_partialSum]
  refine add_mem (hLk a b hab _ (mem_pi_submodule_iff.1 hf.1 c)) ?_
  split_ifs
  · exact mem_pi_submodule_iff.1 hf.1 b
  · exact zero_mem _

end Hull

section Line

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ} {H : Type}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D}

theorem line_V (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v)
    (hint : ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) (hmono : StrictAnti lam) (hGL : GapLap ε lam h)
    (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) (s : Fin n) {N : Type*} [AddCommGroup N] [Module ℂ N]
    (EN : Fin n → Fin n → Module.End ℂ N) :
    ∃ ys ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), ∀ ψ : (Fin n → D) →ₗ[ℂ] N,
      (∀ a b, ∀ y ∈ Submodule.pi Set.univ (fun _ => genSub E V), ψ (LemK.tensV E a b y) = EN a b (ψ y)) →
      ∀ w' ∈ (Xs (LemK.eeV E) (genSub E V) (thV lam s)).map ψ,
        IsKHWVec ε EN (lowK ε (lam + Pi.single s 1)) w' → ∃ c : ℂ, w' = c • ψ ys := by
  classical
  have hK2 := (k2V n ε lam h H σ D E V s hσ hD hV hc hVK hint hmono hGL hp hq).2
  have hKD : IsKUnitary ε E := isKUnitary_of_isInfUnitary (isInfUnitary_of_isDerivedOn hσ hD)
  have hE : IsGlRep E := hD.glRep
  have hXG : ∀ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), y ∈ Submodule.pi Set.univ (fun _ => genSub E V) :=
    fun y hy => by simpa [Submodule.mem_pi] using (mem_eigenTensorSpace_gen_iff.1 hy).1

  have hlift : ∀ ψ : (Fin n → D) →ₗ[ℂ] N,
      (∀ a b, ∀ y ∈ Submodule.pi Set.univ (fun _ => genSub E V), ψ (LemK.tensV E a b y) = EN a b (ψ y)) →
      ∀ w' ∈ (Xs (LemK.eeV E) (genSub E V) (thV lam s)).map ψ,
        IsKHWVec ε EN (lowK ε (lam + Pi.single s 1)) w' →
        ∃ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), IsKHWVec ε (LemK.tensV E) (lowK ε (lam + Pi.single s 1)) y ∧
          ψ y = w' := by
    intro ψ hψ w' hw' hw'K
    obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.1 hw'
    obtain ⟨S, hSX, hfd, hSk, hy₀S⟩ := exists_kStable_finiteDimensional_submodule_of_mem_Xs hE hV.1 hV.2.1 hy₀
    obtain ⟨y, hyS, hyK, hyeq⟩ := partialSum_succ_alt hKD ψ hfd hSk (fun a b _ z hz => hψ a b z (hXG z (hSX hz)))
      hy₀S hw'K
    exact ⟨y, hSX hyS, hyK, hyeq⟩
  by_cases hex : ∃ y ∈ Xs (LemK.eeV E) (genSub E V) (thV lam s), y ≠ 0 ∧
      IsKHWVec ε (LemK.tensV E) (lowK ε (lam + Pi.single s 1)) y
  · obtain ⟨ys, hysX, hys0, hysK⟩ := hex
    refine ⟨ys, hysX, fun ψ hψ w' hw' hw'K => ?_⟩
    obtain ⟨y, hyX, hyK, rfl⟩ := hlift ψ hψ w' hw' hw'K
    obtain ⟨c₁, c₂, hne, hrel⟩ := hK2 y ys hyX hysX hyK hysK
    by_cases hc1 : c₁ = 0
    · exfalso
      rw [hc1, zero_smul, zero_add] at hrel
      exact hys0 ((smul_eq_zero.1 hrel).resolve_left (hne.resolve_left (not_not.2 hc1)))
    · refine ⟨-(c₁⁻¹ * c₂), ?_⟩
      have h2 : c₁ • y = -(c₂ • ys) := eq_neg_of_add_eq_zero_left hrel
      have hy : y = -(c₁⁻¹ * c₂) • ys := by
        calc y = c₁⁻¹ • (c₁ • y) := by rw [smul_smul, inv_mul_cancel₀ hc1, one_smul]
          _ = -(c₁⁻¹ * c₂) • ys := by rw [h2, smul_neg, smul_smul, neg_smul]
      rw [hy, map_smul]
  · refine ⟨0, zero_mem _, fun ψ hψ w' hw' hw'K => ⟨0, ?_⟩⟩
    obtain ⟨y, hyX, hyK, rfl⟩ := hlift ψ hψ w' hw' hw'K
    have hy0 : y = 0 := by
      by_contra hy0
      exact hex ⟨y, hyX, hy0, hyK⟩
    rw [hy0, map_zero, zero_smul]

end Line

end ReciprocityTheory.ChartRestriction.DS.Lap.QuotA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ToL2EqZeroOfEqZeroOnUJset
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

theorem toL2_eq_zero_of_eq_zero_on_UJset {n : ℕ} (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ g ∈ UJset ε, F g = 0) : toL2 ε F = 0 := by
  have h0 : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun _ => 0 := by
    funext g; exact hF _ (unitary_matrix_mem_set ε g)
  have hm : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
    rw [h0]; exact MemLp.zero
  rw [toL2_eq_memLp_toLp ε hm]
  simp only [h0]
  exact MemLp.toLp_zero _

theorem finStep : FinStatement := by
  intro hIS k r ε u lam' h z c Vp _ _ _ π μW μN P hP hB hp hq hgap hlam hgl ξ Wf W' hWf hW' hirr hcas hK hinj
  obtain ⟨w, hwW, hw0, -⟩ := hirr.2.2.2
  obtain ⟨F, hF, hwF⟩ := (hW' w).1 hwW
  have hne : ∃ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 := toL2_eq_zero_of_eq_zero_on_UJset ε F (hinj F hF hcon)
    apply hw0
    apply Subtype.ext
    rw [hwF, h0]
    rfl
  obtain ⟨x, hx, hxne⟩ := hne
  obtain ⟨T', μ', v₁, v₂, hμ, hrep⟩ :=
    finProj k r ε lam' h hp hq hgap hlam hgl Wf W' hWf hW' hirr hcas hK F hF ⟨w, hwW, hw0, hwF⟩
  obtain ⟨hFc, C, hFb⟩ := hWf F hF
  obtain ⟨x₀, hx₀, hne0⟩ := finFub hIS k r ε u lam' h z c Vp π μW μN P hP hB hp hq hgap hlam hgl T' μ' hμ v₁ v₂ ξ F C
    hFc hFb hrep x hx hxne
  exact ⟨T', μ', P, z, c, Vp, inferInstance, inferInstance, inferInstance, π, μW, μN, hμ, hP, hB,
    v₁, v₂, ξ, x₀, x, hx₀, hx, hne0⟩

end ReciprocityTheory.ChartRestriction.DS.Lap
end
end

