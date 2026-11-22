import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSameFactorFormula
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0008

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLinearTermValue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

def rowOne (r : ℕ) : Fin r → ℕ := fun i => if (i : ℕ) = 0 then 1 else 0

theorem partitionsOf_one (r : ℕ) (hr : 1 ≤ r) : partitionsOf r 1 = {rowOne r} := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  ext lam
  rw [mem_partitionsOf_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨hs, ha⟩
    rw [Fin.sum_univ_succ] at hs
    have hle : ∀ i : Fin r', lam i.succ ≤ lam 0 := fun i => ha (Fin.zero_le _)
    have h0 : lam 0 = 1 := by
      by_contra h
      have hz : lam 0 = 0 := by omega
      have : ∑ i : Fin r', lam i.succ = 0 :=
        Finset.sum_eq_zero fun i _ => by have := hle i; omega
      omega
    have hrest : ∑ i : Fin r', lam i.succ = 0 := by omega
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [rowOne, h0]
    · have := Finset.sum_eq_zero_iff.mp hrest j (Finset.mem_univ j)
      simp [rowOne, this]
  · rintro rfl
    refine ⟨?_, fun i j hij => ?_⟩
    · rw [Fin.sum_univ_succ]
      simp [rowOne]
    · simp only [rowOne]
      split_ifs with h1 h2 <;> first | omega | (exfalso; have : (i : ℕ) ≤ j := hij; omega)

theorem schur_rowOne (σ : Type*) [Fintype σ] [DecidableEq σ] (r : ℕ) (hr : 1 ≤ r) :
    schur σ (rowOne r) = ∑ i : σ, X i := by
  unfold schur
  rw [Matrix.det_of_isUpperTriangular]
  · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [Fin.prod_univ_succ]
    have h1 : ∏ i : Fin r', Matrix.of (fun i j : Fin (r' + 1) =>
        completeSymmetric σ ((rowOne (r' + 1) i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ)))
        i.succ i.succ = 1 :=
      Finset.prod_eq_one fun i _ => by simp [rowOne, completeSymmetric_zero]
    rw [h1, mul_one]
    simp [rowOne, completeSymmetric, hsymm_one]
  · intro i j hij
    simp only [Matrix.of_apply]
    apply completeSymmetric_neg
    have : (j : ℕ) < i := hij
    simp only [rowOne]
    split_ifs with h
    · omega
    · push_cast; omega

end

end Top

open Top MvPolynomial Finset

noncomputable section

theorem LinearTermValue.proof (hA : LemmaA.Statement) (hB : LemmaB.Statement)
    (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) :
    LinearTermValue.Statement := by
  intro r a hr ha Q hQ
  obtain ⟨κ, hκpm, hκ⟩ := hasDD_schur hB r a .last
  obtain ⟨c0, hc0, hInt, hMain⟩ := hA 1 (r + a)
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hJ := fibreDegree_eq hF hCI hV 1 r a .last hr ha κ hκ c0 hInt
  have hGF : (1 : RootRing 1 (r + a)) * restPolynomial 1 r a .last =
      gmf 1 r a .last 0 (1 * (r * a) + 1) := by
    simp [gmf, extraFactor, restPolynomial]
  obtain ⟨P, hP, -, S', hS', hI⟩ := hMain _ Q hQ 1 le_rfl (by omega) 0 1 (isHomogeneous_one _ _)
  have hPeq : P = gmfOut 1 r a .last κ 0 (1 * (r * a) + 1) := by
    apply IsFractionRing.injective (RootRing 1 (r + a)) (FractionRing (RootRing 1 (r + a)))
    rw [hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF 1 r a .last κ hκ 0 _)]
  have herase : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
  have hres := restrict_gmfOut 1 r a .last κ 0 (1 * (r * a) + 1) 0
    (fun σ hσ => absurd (Subsingleton.elim σ 0) hσ) (by simp [herase])
  have hm : mstar 1 r a 0 (1 * (r * a) + 1) 0 = fun _ => r * a + 1 := by
    funext σ
    rw [Subsingleton.elim σ 0]
    simp [mstar, herase]
  rw [hm, herase, Finset.prod_empty, Pi.zero_apply,
    toN_blockOut r a .last κ 0 (r * a + 1) 1 (by omega), partitionsOf_one r hr,
    Finset.sum_singleton, schur_rowOne _ r hr] at hres
  have hmult : (Nat.multinomial Finset.univ (fun _ : Fin 1 => r * a + 1) : ℚ) = 1 := by
    rw [multinomial_const]
    have : ((r * a + 1).factorial : ℚ) ≠ 0 := by positivity
    simp [this]
  rw [hmult] at hres
  set b := blockCoeff 0 (r * a + 1) (fun i => a + rowOne r i) with hb
  have hb' : b = numStandardTable (fun i : Fin r => a + if (i : ℕ) = 0 then 1 else 0) := by
    rw [hb, blockCoeff, if_pos rfl, if_neg (by omega)]
    have h := hCI r (fun i => a + rowOne r i) (fun i j hij => by
      simp only [rowOne]
      split_ifs with h1 h2 <;> first | omega | (exfalso; have : (i : ℕ) ≤ j := hij; omega))
    have hs : ∑ i, (a + rowOne r i) = r * a + 1 := by
      obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      rw [Finset.sum_add_distrib, Fin.sum_univ_succ]
      simp [rowOne, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    rw [hs] at h
    exact h
  have hS'eq : S' = C (κ * b) * X (⟨0, by omega⟩ : Fin (r + a)) := by
    apply Flag.powerSumHom_injective
    rw [hS', hPeq, hres]
    simp only [powerSumHom, map_mul, aeval_C, aeval_X, algebraMap_eq, psum, map_sum,
      SmallBlock.sign, map_one, one_mul, one_smul, zero_add, pow_one]
    first | done | ring
  rw [hS'eq, one_mul] at hI
  rw [hI, hJ]
  simp only [coeff_C_mul, coeff_X, mul_one]
  rw [← hb']
  have h01 : (⟨1 - 1, by omega⟩ : Fin (r + a)) = ⟨0, by omega⟩ := rfl
  have hfac : ((r * a).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  simp only [if_true, mul_one, one_mul]

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.POtherFactorFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

theorem isSymmetric_aeval_smul_X {N : ℕ} (s : ℚ) {p : MvPolynomial (Fin N) ℚ} (hp : p.IsSymmetric) :
    (aeval (fun i : Fin N => C s * X i) p).IsSymmetric := by
  intro e
  have key : (rename e).comp (aeval (fun i : Fin N => C s * X i)) =
      (aeval (fun i : Fin N => C s * X i)).comp (rename e) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have := congrArg (fun φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ p) key
  simp only [AlgHom.comp_apply] at this
  rw [this, hp e]

theorem k_sub_one_le (r a k : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ a) (hk : k ≤ r + a) : k - 1 ≤ r * a := by
  have : r + a ≤ r * a + 1 := by nlinarith
  omega

end

end Top

open Top MvPolynomial Finset

noncomputable section

theorem OtherFactorFormula.proof (hA : LemmaA.Statement) (hB : LemmaB.Statement)
    (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (hRP : RectangleTablePos.Statement) :
    OtherFactorFormula.Statement := by
  intro f r a c hf hr ha
  obtain ⟨κ, hκpm, hκ⟩ := hasDD_schur hB r a c
  obtain ⟨c0, hc0, hInt, hMain⟩ := hA f (r + a)
  have hκ0 := kappa_ne_zero hκpm
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hfR : (numStandardTable (rectangle r a) : ℚ) ≠ 0 := by exact_mod_cast (hRP r a).ne'
  refine ⟨c0 * κ ^ f, mul_ne_zero hc0 (pow_ne_zero _ hκ0),
    fibreDegree_eq hF hCI hV f r a c hr ha κ hκ c0 hInt, ?_⟩
  intro Q hQ k hk2 hkN τ τ' hττ'
  have hk1 := k_sub_one_le r a k hr ha hkN
  set q : Fin f → ℕ := fun σ => if σ = τ' then k - 1 else 0 with hqdef
  have hGF := smallPowerSum_mul_restPolynomial f r a c k hk2 τ'
  obtain ⟨P, hP, -, S', hS', hI⟩ := hMain _ Q hQ k (by omega) hkN τ _
    (by simpa using isHomogeneous_smallPowerSum f r a c (k - 1) τ')
  have hPeq : P = gmfOut f r a c κ q (f * (r * a) + 1) := by
    apply IsFractionRing.injective (RootRing f (r + a)) (FractionRing (RootRing f (r + a)))
    rw [hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ q _)]
  have hτ'mem : τ' ∈ Finset.univ.erase τ := Finset.mem_erase.mpr ⟨hττ', Finset.mem_univ τ'⟩
  have hsum : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') = (f - 1) * (r * a) - (k - 1) := by
    rw [← Finset.add_sum_erase _ _ hτ'mem]
    have h2 : ∑ σ' ∈ (Finset.univ.erase τ).erase τ', (r * a - q σ') = (f - 2) * (r * a) := by
      rw [Finset.sum_congr rfl (fun σ hσ => show r * a - q σ = r * a by
        simp [hqdef, Finset.ne_of_mem_erase hσ]), Finset.sum_const,
        Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      congr 1
    rw [h2]
    simp only [hqdef, if_true]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
    simp only [Nat.add_sub_cancel, show f' + 2 - 1 = f' + 1 by omega]
    rw [add_mul, one_mul]
    omega
  have hle : (f - 1) * (r * a) - (k - 1) ≤ f * (r * a) + 1 :=
    (Nat.sub_le _ _).trans ((Nat.mul_le_mul_right _ (Nat.sub_le f 1)).trans (Nat.le_succ _))
  have hres := restrict_gmfOut f r a c κ q (f * (r * a) + 1) τ
    (fun σ hσ => by simp only [hqdef]; split_ifs <;> omega) (by rw [hsum]; exact hle)
  have hmτ : mstar f r a q (f * (r * a) + 1) τ τ = r * a + k := by
    simp only [mstar, if_true, hsum]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
    simp only [show f' + 2 - 1 = f' + 1 by omega]
    have h3 : r * a ≤ (f' + 1) * (r * a) := Nat.le_mul_of_pos_left _ (by omega)
    rw [show (f' + 2) * (r * a) = (f' + 1) * (r * a) + r * a by ring]
    omega
  have hms : mstar f r a q (f * (r * a) + 1) τ = fun σ =>
      if σ = τ then r * a + k else if σ = τ' then r * a - (k - 1) else r * a := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; rw [hmτ, if_pos rfl]
    · by_cases hσ' : σ = τ'
      · subst hσ'; simp [mstar, hσ, hqdef]
      · simp [mstar, hσ, hσ', hqdef]
  have hqτ : q τ = 0 := by simp [hqdef, Ne.symm hττ']
  rw [hmτ, hqτ, toN_blockOut r a c κ 0 (r * a + k) k (by omega)] at hres
  set χR := symmetricGroupCharacter (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
    with hχR
  have hprod : ∏ σ ∈ Finset.univ.erase τ,
      (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ) =
      (χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2) := by
    rw [← Finset.mul_prod_erase _ _ hτ'mem]
    congr 1
    · simp only [hqdef, if_true]
      rw [blockCoeff, if_neg (by omega)]
    · rw [Finset.prod_congr rfl fun σ hσ => by
        rw [show q σ = 0 by simp [hqdef, Finset.ne_of_mem_erase hσ], Nat.sub_zero,
          blockCoeff_rect_eq hCI r a hra]]
      rw [Finset.prod_const, Finset.card_erase_of_mem hτ'mem,
        Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ, Fintype.card_fin]
      congr 1
  have hmult : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) =
      ((f * (r * a) + 1).factorial : ℚ) /
        (((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
          ((r * a).factorial : ℚ) ^ (f - 2)) := by
    have hp : ∏ σ, (mstar f r a q (f * (r * a) + 1) τ σ).factorial =
        (r * a + k).factorial * ((r * a - (k - 1)).factorial * (r * a).factorial ^ (f - 2)) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), hmτ, ← Finset.mul_prod_erase _ _ hτ'mem]
      congr 2
      · simp only [hms, if_neg hττ', if_true]
      · rw [Finset.prod_congr rfl (fun σ hσ =>
          show (mstar f r a q (f * (r * a) + 1) τ σ).factorial = (r * a).factorial by
            simp only [hms, if_neg (Finset.ne_of_mem_erase hσ),
              if_neg (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hσ))]), Finset.prod_const,
          Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),
          Finset.card_univ, Fintype.card_fin]
        congr 1
    have hs' := (Finset.mem_piAntidiag.mp
      (mstar_mem f r a q (f * (r * a) + 1) τ (by rw [hsum]; exact hle))).1
    have h := Nat.multinomial_spec (Finset.univ : Finset (Fin f))
      (mstar f r a q (f * (r * a) + 1) τ)
    rw [hp, hs'] at h
    have hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
        ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0 := by positivity
    rw [eq_div_iff hden, ← h]
    push_cast
    ring
  set T := ∑ nu ∈ partitionsOf r k,
      C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) with hT
  have hTeq : ∑ nu ∈ partitionsOf r k, C (blockCoeff 0 (r * a + k) (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) = T := by
    rw [hT]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [blockCoeff, if_pos rfl, if_neg (by omega)]
    have hs := sum_of_mem_partitionsOf hnu
    have hanti := antitone_of_mem_partitionsOf hnu
    have h := hCI r (fun i => a + nu i) (fun i j hij => Nat.add_le_add_left (hanti hij) a)
    have hs2 : ∑ i, (a + nu i) = r * a + k := by
      rw [Finset.sum_add_distrib, hs]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]
    rw [hs2] at h
    rw [h]
  rw [hTeq, hprod] at hres
  have hTsym : T.IsSymmetric := by
    intro e
    rw [hT, map_sum]
    refine Finset.sum_congr rfl fun nu _ => ?_
    rw [map_mul, rename_C, isSymmetric_aeval_smul_X _ (Schur.schur_isSymmetric _) e]
  set K : ℚ := (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) *
    ((χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2)) * κ with hK
  have hPS : powerSumHom (r + a) S' = K • T := by
    rw [hS', hPeq, hres, hK, smul_eq_C_mul, smul_eq_C_mul]
    simp only [map_mul, map_pow]
    ring
  have hmultpos : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  by_cases hχ : χR = 0
  · obtain ⟨S, hS⟩ := Flag.exists_powerSumHom_eq hTsym
    have hS'0 : S' = 0 := by
      apply Flag.powerSumHom_injective
      rw [hPS, hK, hχ, map_zero]
      simp
    refine ⟨S, hS, ?_⟩
    rw [restTerm, hI, hS'0, coeff_zero, hχ]
    ring
  · have hK0 : K ≠ 0 := by
      rw [hK]
      exact mul_ne_zero (mul_ne_zero hmultpos (mul_ne_zero (mul_ne_zero hχ hκ0)
        (pow_ne_zero _ (mul_ne_zero hfR hκ0)))) hκ0
    refine ⟨K⁻¹ • S', ?_, ?_⟩
    · rw [map_smul, hPS, smul_smul, inv_mul_cancel₀ hK0, one_smul]
    · rw [restTerm, hI, coeff_smul, smul_eq_mul]
      rw [hK, hmult]
      have hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
          ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0 := by positivity
      have hnum : ((f * (r * a) + 1).factorial : ℚ) ≠ 0 := by positivity
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
      simp only [Nat.add_sub_cancel] at hden ⊢
      field_simp
      ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.SumPderivRealApply
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

namespace TwoCasesDerivatives

open MvPolynomial Finset

noncomputable section

variable (f j k : ℕ)

def sumPderivReal {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k)) :
    Derivation ℝ (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :=
  ∑ l ∈ s, pderiv (τ, g l)

theorem sumPderivReal_apply {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k))
    (P : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    sumPderivReal f j k τ s g P = ∑ l ∈ s, pderiv (τ, g l) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumPderivReal]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, ← ih]
    simp [sumPderivReal, Finset.sum_insert hb]

theorem sumPderivReal_X {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k))
    (σ : Fin f) (i : Fin (j + k)) :
    sumPderivReal f j k τ s g (X (σ, i)) =
      ∑ l ∈ s, if σ = τ ∧ i = g l then (1 : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) else 0 := by
  classical
  rw [sumPderivReal_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pderiv_X, Pi.single_apply]
  simp only [Prod.mk.injEq]

theorem deriv_restPoly (D : Derivation ℝ (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (IndefiniteRowSideFullHecke.RestTerms.Roots f j k))
    (bot : Bool) (α β : Fin f → ℝ)
    (ht : ∀ σ (a : Fin j), D (X (σ, Fin.castAdd k a)) = C (α σ))
    (hb : ∀ σ (b : Fin k), D (X (σ, Fin.natAdd j b)) = C (β σ)) :
    D (IndefiniteRowSideFullHecke.RestTerms.restPoly f j k bot) =
      C (((IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1) *
          (if bot then (k : ℝ) * ∑ σ, β σ else -((j : ℝ) * ∑ σ, α σ))) *
        IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot := by
  have hfib : D (IndefiniteRowSideFullHecke.RestTerms.fibClass f j k bot) = 0 := by
    unfold IndefiniteRowSideFullHecke.RestTerms.fibClass
    refine Flag.derivation_prod_eq_zero D _ _ (fun σ _ => ?_)
    cases bot <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      rw [Derivation.leibniz, ← vandermondeOf_eq_vandermonde, ← vandermondeOf_eq_vandermonde,
        Flag.derivation_vandermondeOf_eq_zero D _ (fun i i' => by simp [ht, hb]),
        Flag.derivation_vandermondeOf_eq_zero D _ (fun i i' => by simp [ht, hb]),
        smul_zero, smul_zero, add_zero]
  have hmu : D (IndefiniteRowSideFullHecke.RestTerms.muClass f j k bot) =
      C (if bot then (k : ℝ) * ∑ σ, β σ else -((j : ℝ) * ∑ σ, α σ)) := by
    cases bot <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.muClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, map_sum, ht, hb, Finset.mul_sum]
  rw [IndefiniteRowSideFullHecke.RestTerms.restPoly, Derivation.leibniz, hfib, smul_zero, zero_add,
    Derivation.leibniz_pow, hmu, IndefiniteRowSideFullHecke.RestTerms.degPoly]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  simp only [map_mul, map_natCast, map_add, map_one]
  push_cast
  ring

end

end TwoCasesDerivatives

open MvPolynomial Finset TwoCasesDerivatives

theorem TwoCases.intersectionNumber_baseChange : IndefiniteRowSideFullHecke.RestTerms.TwoCases.Statement := by
  classical
  intro f j k I τ
  have hI : ∀ (c : ℝ) (P : IndefiniteRowSideFullHecke.RestTerms.Roots f j k), I (C c * P) = c * I P := by
    intro c P
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  have hsh : ∀ F, IndefiniteRowSideFullHecke.RestTerms.shiftAt f j k I τ F =
      I (sumPderivReal f j k τ univ (Fin.castAdd k) F) := by
    intro F
    rw [sumPderivReal_apply]
    rfl
  have hto : ∀ F, IndefiniteRowSideFullHecke.RestTerms.totalAt f j k I τ F = I (sumPderivReal f j k τ univ id F) := by
    intro F
    rw [sumPderivReal_apply]
    rfl
  have shT : ∀ σ (a : Fin j), sumPderivReal f j k τ univ (Fin.castAdd k) (X (σ, Fin.castAdd k a)) =
      C (if σ = τ then 1 else 0) := by
    intro σ a
    rw [sumPderivReal_X]
    by_cases h : σ = τ <;> simp [h, Fin.castAdd_inj]
  have shB : ∀ σ (b : Fin k), sumPderivReal f j k τ univ (Fin.castAdd k) (X (σ, Fin.natAdd j b)) =
      C 0 := by
    intro σ b
    rw [sumPderivReal_X]
    refine (Finset.sum_eq_zero fun a _ => ?_).trans C_0.symm
    rw [if_neg]
    rintro ⟨-, h⟩
    have := congrArg Fin.val h
    simp at this
    omega
  have toX : ∀ σ i, sumPderivReal f j k τ univ id (X (σ, i)) = C (if σ = τ then 1 else 0) := by
    intro σ i
    rw [sumPderivReal_X]
    by_cases h : σ = τ <;> simp [h]
  have hs : ∑ σ : Fin f, (if σ = τ then (1 : ℝ) else 0) = 1 := by simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hsh, deriv_restPoly f j k _ true (fun σ => if σ = τ then 1 else 0) (fun _ => 0) shT shB,
      hI]
    simp
  · rw [hto, deriv_restPoly f j k _ true (fun σ => if σ = τ then 1 else 0)
      (fun σ => if σ = τ then 1 else 0) (fun σ a => toX σ _) (fun σ b => toX σ _), hI, if_pos rfl,
      hs]
    ring
  · rw [hsh, deriv_restPoly f j k _ false (fun σ => if σ = τ then 1 else 0) (fun _ => 0) shT shB,
      hI, if_neg Bool.false_ne_true, hs]
    ring
  · rw [hto, deriv_restPoly f j k _ false (fun σ => if σ = τ then 1 else 0)
      (fun σ => if σ = τ then 1 else 0) (fun σ a => toX σ _) (fun σ b => toX σ _), hI,
      if_neg Bool.false_ne_true, hs]
    ring

end GroundTheory.Heights₂.Heights.RestTerms
end

