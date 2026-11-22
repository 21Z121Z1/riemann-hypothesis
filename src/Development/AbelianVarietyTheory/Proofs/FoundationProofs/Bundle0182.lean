import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0166
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0082
import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AtkinLehnerSlashInverseCharacterStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atkinLehner_slash_inverse_character : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → Inv k (N * l) (ch χ) f → Inv k (N * l) (ch χ⁻¹) (slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] f) := by
  first | exact @GlobalTheory.EisM.inv_slz_atkinLehner | exact GlobalTheory.EisM.inv_slz_atkinLehner | (intros; apply GlobalTheory.EisM.inv_slz_atkinLehner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeTOperatorQExpansionSlashSum
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem polyB_add_smul {u v : ℕ → ℂ} (c : ℂ) (hu : PolyB u) (hv : PolyB v) :
    PolyB (fun n => u n + c * v n) := by
  obtain ⟨C₁, A₁, h₁⟩ := hu
  obtain ⟨C₂, A₂, h₂⟩ := hv
  have hC₁ : 0 ≤ C₁ := by
    have := h₁ 0; simp at this; exact le_trans (norm_nonneg _) this
  have hC₂ : 0 ≤ C₂ := by
    have := h₂ 0; simp at this; exact le_trans (norm_nonneg _) this
  refine ⟨C₁ + ‖c‖ * C₂, A₁ + A₂, fun n => ?_⟩
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have e1 : ((n : ℝ) + 1) ^ A₁ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) := pow_le_pow_right₀ h1 (by omega)
  have e2 : ((n : ℝ) + 1) ^ A₂ ≤ ((n : ℝ) + 1) ^ (A₁ + A₂) := pow_le_pow_right₀ h1 (by omega)
  calc ‖u n + c * v n‖ ≤ ‖u n‖ + ‖c‖ * ‖v n‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ C₁ * ((n : ℝ) + 1) ^ A₁ + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ A₂) := by
        gcongr; exacts [h₁ n, h₂ n]
    _ ≤ C₁ * ((n : ℝ) + 1) ^ (A₁ + A₂) + ‖c‖ * (C₂ * ((n : ℝ) + 1) ^ (A₁ + A₂)) := by
        gcongr
    _ = (C₁ + ‖c‖ * C₂) * ((n : ℝ) + 1) ^ (A₁ + A₂) := by ring

theorem qs_To_hsum : ∀ (k q : ℕ) (ε : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → 0 < q → ε 1 = 1 → PolyB a →
    PolyB (To k (ε q) q a) ∧ qs (To k (ε q) q a) = hsum k ε (repT q) (qs a) := by
  intro k q ε a hk hq hε ha
  obtain ⟨hU, hUq⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k q a hk hq ha
  obtain ⟨hV, hVq⟩ := GlobalTheory.T.coeffHeckeVOperator_polynomialGrowth_qExpansion q a hq ha
  have hTo : To k (ε q) q a = fun n => Uo q a n + (ε q * (q : ℂ) ^ (k - 1)) * Vo q a n := by
    funext n; simp only [To, Uo]
  refine ⟨by rw [hTo]; exact polyB_add_smul _ hU hV, ?_⟩
  funext τ
  have sU : Summable fun n : ℕ => Uo q a n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous _ hU).1 τ).of_norm
  have sV : Summable fun n : ℕ => Vo q a n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous _ hV).1 τ).of_norm
  have hsplit : qs (To k (ε q) q a) τ = qs (Uo q a) τ + (ε q * (q : ℂ) ^ (k - 1)) * qs (Vo q a) τ := by
    rw [hTo]; simp only [qs]
    rw [← tsum_mul_left, ← sU.tsum_add (sV.mul_left _)]
    congr 1; funext n; ring
  have him : 0 < ((q : ℂ) * (τ : ℂ)).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hq) τ.im_pos
  have hσ : qs (Vo q a) τ = qs a ⟨(q : ℂ) * τ, him⟩ := hVq τ ⟨(q : ℂ) * τ, him⟩ rfl
  rw [hsplit, hUq τ, hσ, hsum, Fintype.sum_option]
  have hnone : ε (repT q none 0 0) * slz k (repT q none) (qs a) τ
      = (ε q * (q : ℂ) ^ (k - 1)) * qs a ⟨(q : ℂ) * τ, him⟩ := by
    have : ofComplex ((((q : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ))) = ⟨(q : ℂ) * τ, him⟩ := by
      rw [show (((q : ℤ) : ℂ) * (τ : ℂ) + ((0 : ℤ) : ℂ)) / (((0 : ℤ) : ℂ) * (τ : ℂ) + ((1 : ℤ) : ℂ)) = (q : ℂ) * τ by
        push_cast; ring]
      exact ofComplex_apply_of_im_pos him
    simp only [repT, slz, Matrix.det_fin_two_of, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.head_fin_const]
    rw [this]
    push_cast
    simp
    ring
  have hsome : ∀ j : Fin q, ε (repT q (some j) 0 0) * slz k (repT q (some j)) (qs a) τ
      = slz k (repU q j) (qs a) τ := by
    intro j
    simp only [repT, repU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hε, one_mul]
  rw [hnone, Finset.sum_congr rfl (fun j _ => hsome j)]
  ring

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUOperatorLowersLevel
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.LevelLower

def idx (l : ℕ) [NeZero l] (b d : ℤ) (j : Fin l) : Fin l :=
  ⟨(((b + ((j : ℕ) : ℤ) * d) * d : ℤ) : ZMod l).val, ZMod.val_lt _⟩

lemma idx_cast (l : ℕ) [NeZero l] (b d : ℤ) (j : Fin l) :
    ((idx l b d j : ℕ) : ZMod l) = (((b + ((j : ℕ) : ℤ) * d) * d : ℤ) : ZMod l) := by
  simp [idx, ZMod.natCast_zmod_val]

lemma idx_inj (l : ℕ) [NeZero l] (a b d : ℤ) (had : ((a * d : ℤ) : ZMod l) = 1) :
    Function.Injective (idx l b d) := by
  intro j₁ j₂ h
  have h' := congrArg (fun x : Fin l => ((x : ℕ) : ZMod l)) h
  simp only [idx_cast] at h'
  push_cast at h' had
  have e : ((j₁ : ℕ) : ZMod l) = ((j₂ : ℕ) : ZMod l) := by
    linear_combination (a : ZMod l) ^ 2 * h' -
      (((j₁ : ℕ) : ZMod l) - ((j₂ : ℕ) : ZMod l)) * (1 + (a : ZMod l) * d) * had
  apply Fin.ext
  rw [ZMod.natCast_eq_natCast_iff'] at e
  simpa [Nat.mod_eq_of_lt j₁.2, Nat.mod_eq_of_lt j₂.2] using e

lemma coset (L l : ℕ) [NeZero l] (hlL : l ∣ L) (γ : SL(2, ℤ)) (hc : (L : ℤ) ∣ γ 1 0) (j : Fin l) :
    ∃ γ' : SL(2, ℤ), ((L * l : ℕ) : ℤ) ∣ γ' 1 0 ∧
      γ' 1 1 = γ 1 1 - γ 1 0 * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) ∧
      repU l j * (γ : M2) = (γ' : M2) * repU l (idx l (γ 0 1) (γ 1 1) j) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hlc : (l : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hlL).trans hc
  have hdiv : (l : ℤ) ∣ γ 0 1 + ((j : ℕ) : ℤ) * γ 1 1 -
      (γ 0 0 + ((j : ℕ) : ℤ) * γ 1 0) * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hc0 : ((γ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hlc
    have hj' := idx_cast l (γ 0 1) (γ 1 1) j
    have hd1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod l) = 1 := by rw [hdet]; simp
    push_cast at hj' hd1 ⊢
    rw [hj']
    linear_combination (-((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l))) * hd1 -
      ((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l)) *
      ((γ 0 1 : ZMod l) + ((j : ℕ) : ZMod l) * (γ 1 1 : ZMod l)) * hc0
  obtain ⟨B, hB⟩ := hdiv
  obtain ⟨m, hm⟩ := hc
  refine ⟨⟨!![γ 0 0 + ((j : ℕ) : ℤ) * γ 1 0, B; (l : ℤ) * γ 1 0,
      γ 1 1 - γ 1 0 * ((idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ)], ?_⟩, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hdet + γ 1 0 * hB
  · refine ⟨m, ?_⟩
    simp only [Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
    rw [hm]; push_cast; ring
  · simp
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [repU, Matrix.mul_apply, Fin.sum_univ_two] <;> first | ring1 | linear_combination hB | linear_combination -hB

end GlobalTheory.LevelLower

namespace GlobalTheory.LevelLower

lemma slz_sum (k : ℕ) (δ : M2) {ι : Type} [Fintype ι] (F : ι → ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun τ => ∑ i, F i τ) τ = ∑ i, slz k δ (F i) τ := by
  simp only [slz, Finset.mul_sum]

lemma slz_smul (k : ℕ) (δ : M2) (c : ℂ) (f : ℍ → ℂ) (τ : ℍ) :
    slz k δ (fun τ => c * f τ) τ = c * slz k δ f τ := by
  simp only [slz]; ring

lemma per (L : ℕ) (χ : ℤ → ℂ) (hχ : ∀ d, χ (d + L) = χ d) (m : ℤ) : ∀ d : ℤ, χ (d + m * L) = χ d := by
  refine Int.induction_on m ?_ ?_ ?_
  · intro d; simp
  · intro i ih d
    rw [show d + ((i : ℤ) + 1) * (L : ℤ) = (d + (i : ℤ) * L) + L by ring, hχ, ih]
  · intro i ih d
    have := hχ (d + (-(i : ℤ) - 1) * L)
    rw [show d + (-(i : ℤ) - 1) * (L : ℤ) + L = d + -(i : ℤ) * L by ring, ih] at this
    exact this.symm

end GlobalTheory.LevelLower

theorem GlobalTheory.Uo_lowers_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 1 ≤ k → l.Prime → l ∣ L →
    (∀ d, χ (d + L) = χ d) → MF k (L * l) χ a → MF k L χ (Uo l a) := by
  intro k L l χ a hk hl hlL hχ hMF
  obtain ⟨hP, hI⟩ := hMF
  haveI : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨hPU, hqs⟩ := GlobalTheory.T.qExpansion_heckeU_eq_sum_slash k l a hk hl.pos hP
  obtain ⟨hcoc, -, hinv, -, -⟩ := GlobalTheory.T.slashIntMatrixPosDet_properties k (qs a) hk
  have hI' := (hinv (L * l) χ).mp hI
  refine ⟨hPU, ?_⟩
  rw [(GlobalTheory.T.slashIntMatrixPosDet_properties k (qs (Uo l a)) hk).2.2.1]
  intro γ hc
  have hg : qs (Uo l a) = fun τ => ∑ j : Fin l, slz k (repU l j) (qs a) τ := funext hqs
  have hdU : ∀ j : Fin l, 0 < (repU l j).det := by
    intro j; simp [repU, Matrix.det_fin_two_of]; exact hl.pos
  have hdγ : ∀ γ : SL(2, ℤ), 0 < (γ : M2).det := by
    intro γ; rw [Matrix.SpecialLinearGroup.det_coe]; exact one_pos

  have had : ((γ 0 0 * γ 1 1 : ℤ) : ZMod l) = 1 := by
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2
      rw [Matrix.det_fin_two] at this
      exact this
    have hlc : (l : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hlL).trans hc
    have hc0 : ((γ 1 0 : ℤ) : ZMod l) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hlc
    have h1 : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ZMod l) = 1 := by rw [hdet]; simp
    push_cast at h1 hc0 ⊢
    rw [hc0, mul_zero, sub_zero] at h1
    exact h1
  let e : Fin l ≃ Fin l := Equiv.ofBijective (GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1))
    (Finite.injective_iff_bijective.mp (GlobalTheory.LevelLower.idx_inj l _ _ _ had))
  have key : ∀ (τ : ℍ) (j : Fin l), slz k (γ : M2) (slz k (repU l j) (qs a)) τ =
      χ (γ 1 1) * slz k (repU l (e j)) (qs a) τ := by
    intro τ j
    obtain ⟨γ', h1, h2, h3⟩ := GlobalTheory.LevelLower.coset L l hlL γ hc j
    rw [← hcoc _ _ (hdU j) (hdγ γ), h3, hcoc _ _ (hdγ γ') (hdU _), hI' γ' h1,
      GlobalTheory.LevelLower.slz_smul, h2]
    obtain ⟨m, hm⟩ := hc
    have : χ (γ 1 1 - γ 1 0 * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ)) = χ (γ 1 1) := by
      rw [hm, show γ 1 1 - (L : ℤ) * m * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ) =
        γ 1 1 + (-(m * ((GlobalTheory.LevelLower.idx l (γ 0 1) (γ 1 1) j : ℕ) : ℤ))) * L by ring,
        GlobalTheory.LevelLower.per L χ hχ]
    rw [this]
    rfl
  rw [hg]
  funext τ
  rw [GlobalTheory.LevelLower.slz_sum]
  simp_rw [key τ]
  rw [← Finset.mul_sum, Equiv.sum_comp e (fun j => slz k (repU l j) (qs a) τ)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMatrixMulCommModGamma1CapGamma0
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory.KZ

theorem isDiam_mul_comm_mod_Gam (N l d d' : ℕ) (σ σ' : SL(2, ℤ)) (h : IsDiam N l d σ) (h' : IsDiam N l d' σ') :
    ∃ g : SL(2, ℤ), g ∈ Gam N l ∧ σ' * σ = g * (σ * σ') := by
  obtain ⟨⟨h0, h1⟩, -⟩ := h
  obtain ⟨⟨h0', h1'⟩, -⟩ := h'
  refine ⟨σ' * σ * (σ * σ')⁻¹, ⟨?_, ?_⟩, by group⟩
  · set a : CongruenceSubgroup.Gamma0 N := ⟨σ, h0⟩ with ha
    set b : CongruenceSubgroup.Gamma0 N := ⟨σ', h0'⟩ with hb
    have hu : (CongruenceSubgroup.Gamma0Map N).toHomUnits (b * a * (a * b)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul,
        mul_comm ((CongruenceSubgroup.Gamma0Map N).toHomUnits b), mul_inv_cancel]
    have h3 : b * a * (a * b)⁻¹ ∈ CongruenceSubgroup.Gamma1' N := by
      rw [CongruenceSubgroup.Gamma1_mem', ← MonoidHom.coe_toHomUnits, hu, Units.val_one]
    exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h3)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1' h1) (Subgroup.inv_mem _ (Subgroup.mul_mem _ h1 h1'))

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinLatticeSumGcdFactorOut
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.GcdOut

abbrev CopVec (L : ℕ) : Type := {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}

def scl (L : ℕ) (p : ℕ+ × CopVec L) : ℤ × ℤ := (((p.1 : ℕ) : ℤ) * p.2.1.1, ((p.1 : ℕ) : ℤ) * p.2.1.2)

lemma scl_injective (L : ℕ) : Function.Injective (scl L) := by
  rintro ⟨δ, ⟨⟨a, b⟩, hab, ha⟩⟩ ⟨δ', ⟨⟨a', b'⟩, hab', ha'⟩⟩ h
  simp only [scl, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have g1 : Int.gcd a b = 1 := Int.isCoprime_iff_gcd_eq_one.1 hab
  have g2 : Int.gcd a' b' = 1 := Int.isCoprime_iff_gcd_eq_one.1 hab'
  have hd : (δ : ℕ) = (δ' : ℕ) := by
    have e1 := Int.gcd_mul_left ((δ : ℕ) : ℤ) a b
    have e2 := Int.gcd_mul_left ((δ' : ℕ) : ℤ) a' b'
    rw [h1, h2, e2, g1, g2] at e1
    simpa using e1.symm
  have hδ : δ = δ' := PNat.coe_injective hd
  subst hδ
  have hne : ((δ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast δ.ne_zero
  have := mul_left_cancel₀ hne h1
  have := mul_left_cancel₀ hne h2
  subst_vars
  rfl

lemma trm_zero (j : ℕ) (s : ℝ) (hj : 2 ≤ j) : trm j s 0 = 0 := by
  simp [trm, zero_pow (by omega : j ≠ 0)]

lemma trm_smul (j : ℕ) (s : ℝ) (δ : ℕ) (z : ℂ) :
    trm j s ((δ : ℂ) * z) = (((δ : ℂ) ^ j)⁻¹ * ((((δ : ℝ) ^ (2 * s))⁻¹ : ℝ) : ℂ)) * trm j s z := by
  unfold trm
  rw [norm_mul, Complex.norm_natCast, Real.mul_rpow (Nat.cast_nonneg _) (norm_nonneg _), neg_mul,
    Real.rpow_neg (Nat.cast_nonneg _), ← neg_mul, mul_pow, mul_inv]
  push_cast
  ring

lemma cpow_split (j : ℕ) (s : ℝ) (δ : ℕ) (hδ : 0 < δ) :
    (δ : ℂ) ^ ((j : ℂ) + 2 * (s : ℂ)) = (δ : ℂ) ^ j * ((((δ : ℝ) ^ (2 * s)) : ℝ) : ℂ) := by
  rw [Complex.cpow_add _ _ (by exact_mod_cast hδ.ne'), Complex.cpow_natCast,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  rfl

end GlobalTheory.EisM.GcdOut

open GlobalTheory.EisM.GcdOut in
theorem GlobalTheory.EisM.lattice_sum_gcd_out (j L : ℕ) (s : ℝ) (φ : DirichletCharacter ℂ L) (τ : ℍ)
    (hj : 2 ≤ j) (hs : 0 < s) (hL : 0 < L) :
    ∑' x : ℤ × ℤ, latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2) =
      LSeries (fun n => φ n) (j + 2 * s) *
        ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1},
          φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2) := by
  let F : ℤ × ℤ → ℂ := fun x => latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2)
  let f : ℕ+ → ℂ := fun δ => LSeries.term (fun n => φ n) ((j : ℂ) + 2 * (s : ℂ)) (δ : ℕ)
  let g : CopVec L → ℂ := fun x => φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2)
  change ∑' x, F x = LSeries (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) * ∑' x, g x
  have hsumT := (GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills j L s 0 0 τ hj hs hL ⟨0, by simp⟩ (fun x => by simp [Kills])).1
  have hgs : Summable fun x => ‖g x‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_)
      (hsumT.comp_injective Subtype.val_injective)
    simp only [g, Function.comp, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  have hLS : LSeriesSummable (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) := by
    rw [DirichletCharacter.LSeriesSummable_iff hL.ne']
    have : (2:ℝ) ≤ j := by exact_mod_cast hj
    simp
    linarith
  have hfs : Summable fun δ => ‖f δ‖ :=
    (summable_norm_iff.2 hLS).comp_injective PNat.coe_injective
  have hterm : ∀ p : ℕ+ × CopVec L, F (scl L p) = f p.1 * g p.2 := by
    rintro ⟨δ, ⟨⟨a, b⟩, hab, ha⟩⟩
    have hδ : 0 < (δ : ℕ) := δ.pos
    simp only [F, f, g, scl, latF]
    rw [if_pos (dvd_mul_of_dvd_right ha _), LSeries.term_of_ne_zero hδ.ne', cpow_split j s _ hδ]
    have e : ((((δ : ℕ) : ℤ) * a : ℤ) : ℂ) * (τ : ℂ) + ((((δ : ℕ) : ℤ) * b : ℤ) : ℂ)
        = ((δ : ℕ) : ℂ) * ((a : ℂ) * τ + b) := by push_cast; ring
    rw [e, trm_smul]
    have e2 : (((((δ : ℕ) : ℤ) * b : ℤ)) : ZMod L) = ((δ : ℕ) : ZMod L) * (b : ZMod L) := by push_cast; ring
    rw [e2, map_mul]
    have h1 : ((δ:ℕ) : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hδ.ne')
    have h2 : ((((δ : ℕ) : ℝ) ^ (2 * s) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hδ) _).ne'
    push_cast
    field_simp
  have hsupp : Function.support F ⊆ Set.range (scl L) := by
    rintro ⟨x1, x2⟩ hx
    simp only [Function.mem_support, F, latF] at hx
    by_cases hL1 : (L : ℤ) ∣ x1
    swap
    · simp [hL1] at hx
    rw [if_pos hL1, one_mul] at hx
    have hφ : φ (x2 : ZMod L) ≠ 0 := left_ne_zero_of_mul hx
    have ht : trm j s ((x1 : ℂ) * τ + x2) ≠ 0 := right_ne_zero_of_mul hx
    have hgpos : 0 < Int.gcd x1 x2 := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      rw [Int.gcd_eq_zero_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [trm_zero j s hj] at ht
    obtain ⟨a, b, hab, h1, h2⟩ := Int.exists_gcd_one hgpos
    generalize Int.gcd x1 x2 = d at h1 h2 hgpos
    have hunit : IsUnit (x2 : ZMod L) := by
      by_contra h
      exact hφ (MulChar.map_nonunit φ h)
    have hdu : IsUnit ((d : ℕ) : ZMod L) := by
      rw [h2] at hunit
      push_cast at hunit
      exact isUnit_of_mul_isUnit_right hunit
    have hcop : Nat.Coprime d L := (ZMod.isUnit_iff_coprime d L).1 hdu
    have hLa : (L : ℤ) ∣ a := by
      have hc : IsCoprime (L : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
      rw [h1] at hL1
      exact hc.dvd_of_dvd_mul_right hL1
    refine ⟨(⟨d, hgpos⟩, ⟨(a, b), Int.isCoprime_iff_gcd_eq_one.2 hab, hLa⟩), ?_⟩
    simp only [scl, PNat.mk_coe]
    rw [h1, h2, mul_comm a, mul_comm b]
  have hLser : ∑' δ : ℕ+, f δ = LSeries (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) := by
    unfold LSeries
    refine (PNat.coe_injective.tsum_eq (f := LSeries.term (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ))) ?_)
    intro n hn
    have : n ≠ 0 := by
      rintro rfl
      exact hn (LSeries.term_zero _ _)
    exact ⟨⟨n, Nat.pos_of_ne_zero this⟩, rfl⟩
  calc ∑' x, F x = ∑' p, F (scl L p) := ((scl_injective L).tsum_eq hsupp).symm
    _ = ∑' p : ℕ+ × CopVec L, f p.1 * g p.2 := tsum_congr hterm
    _ = (∑' δ, f δ) * ∑' x, g x := (tsum_mul_tsum_of_summable_norm hfs hgs).symm
    _ = _ := by rw [hLser]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinProductSeriesEqDepletedEisensteinProduStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinProductSeries_eq_depleted_eisenstein_product : ∀ (k l j : ℕ) (u w A A' : ℤ → ℂ) (c c' : ℂ), j + 2 ≤ k → Zm k l u w (fun x y => A x * A' y * ((y : ℂ) / x) ^ j) = mul (dep l (eis (k - 1 - j) c (fun x => u x * A x) fun _ => 1)) (dep l (eis (j + 1) c' A' w)) := by
  first | exact @GlobalTheory.zm_eq_mul_dep_eis | exact GlobalTheory.zm_eq_mul_dep_eis | (intros; apply GlobalTheory.zm_eq_mul_dep_eis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EisensteinTameWeightSecondEqCharacterSumStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tw2_eq_inv_totient_mul_sum_characters : ∀ (N : ℕ) (s : ℂ), 0 < N → ∀ B : ℤ, tw2 N s B = ((N.totient : ℂ))⁻¹ * ∑ ν : DirichletCharacter ℂ N, (1 - s * ν (-1)) * ch ν B := by
  first | exact @GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum | exact GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum | (intros; apply GlobalTheory.EisM.eisensteinTameWeightSecond_eq_character_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBettiCocycleKummerRelationStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_betti_cocycle_kummer_relation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := by
  first | exact @GlobalTheory.KZ.BettiEx.exists_betti_cocycle | exact GlobalTheory.KZ.BettiEx.exists_betti_cocycle | (intros; apply GlobalTheory.KZ.BettiEx.exists_betti_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsColumnChainNonempty
section
open Formalism.BasicNotions NumberField

namespace GlobalTheory

theorem unitChain_num_sub_half (R : Ranks) (q : ℚ) (hq : ∃ z : ℤ, q = z) (j : ℕ) :
    (((q - (R.N j : ℚ) / 2).num : ℤ) : ℚ) = q - (R.N j : ℚ) / 2 := by
  obtain ⟨z, rfl⟩ := hq
  have hN : Even (R.N j) := by
    unfold Ranks.N
    exact R.k_even.add ((R.t_odd.add_one).mul_left j)
  obtain ⟨a, ha⟩ := hN
  have h : (z : ℚ) - (R.N j : ℚ) / 2 = ((z - a : ℤ) : ℚ) := by
    rw [ha]; push_cast; ring
  rw [h, Rat.num_intCast]

def unitColumnChain (R : Ranks) (ι : Type) [Fintype ι] (hc : ι → HCParam R) :
    ColumnChain R ι hc where
  cls _ := Unit
  stab _ _ := PUnit
  DGam := 1
  DGam_pos := Nat.one_pos
  dvd_DGam _ _ _ := by simp
  Y _ := Unit
  de _ _ _ := 1
  de_ne _ _ _ := one_ne_zero
  rhoDet _ _ := 1
  rhoDet' _ _ := 1
  rho_norm _ _ _ := norm_one
  rho'_norm _ _ _ := norm_one
  unf _ _ _ := LinearMap.id
  sSharp i τ := if h : i < R.m then (sExp' R ((hc τ).e ⟨i, h⟩) (i + 1)).num else 0
  sSharp_eq i h τ := by
    rw [dif_pos h]
    exact unitChain_num_sub_half R _ ((hc τ).e_int _) _
  sDiv i τ := if h : i < R.m then (sExp R ((hc τ).e ⟨i, h⟩) (i + 1)).num else 0
  sDiv_eq i h τ := by
    rw [dif_pos h]
    exact unitChain_num_sub_half R _ ((hc τ).e_int _) _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerPotentialRelationPadicStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerPotentialRelation_padic : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], [IsAlgClosed Ω] → JHol X → ∀ (N w : ℕ), 4 ≤ N → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ b ∈ X.B N l w, ∃ F ∈ Pot ℤ_[l] w (Gam N l), Rel X l b F := by
  first | exact @GlobalTheory.KZ.H3.exists_pot_rel | exact GlobalTheory.KZ.H3.exists_pot_rel | (intros; apply GlobalTheory.KZ.H3.exists_pot_rel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelFunctionsIntermediateFieldStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelFunctions_intermediateField : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M → ∃ L : IntermediateField Ω X.K, (∀ f : X.K, f ∈ L ↔ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) ∧ ∃ hj : X.jK ∈ L, FiniteDimensional (IntermediateField.adjoin Ω {(⟨X.jK, hj⟩ : L)}) L := by
  first | exact @GlobalTheory.KZ.LevelField.exists_level_field | exact GlobalTheory.KZ.LevelField.exists_level_field | (intros; apply GlobalTheory.KZ.LevelField.exists_level_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FunctionFieldClassGroupPowersStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_class_group_powers : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ), 2 ≤ N → ∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N := by
  first | exact @GlobalTheory.exists_class_group_mk0_eq_mul_pow | exact GlobalTheory.exists_class_group_mk0_eq_mul_pow | (intros; apply GlobalTheory.exists_class_group_mk0_eq_mul_pow <;> assumption)
end

