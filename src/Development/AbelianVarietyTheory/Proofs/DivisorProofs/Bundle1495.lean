import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1476
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledIntegralOfLocal
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus.IntegralOfAdic

theorem evFin_realAd (F : Type) [Field F] [NumberField F] (v : Pl F) (x : ℝ) :
    evFin F v (realAd F x) = 0 := by
  show evalV F v 0 = 0
  exact map_zero _

theorem evFin_tAd (F : Type) [Field F] [NumberField F] (v : Pl F) (s : ℝ) :
    evFin F v (tAd F s) = 1 := by
  rw [tAd, map_add, evFin_realAd, map_one, add_zero]

theorem integral_of_evFin_mem (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ}
    (blk : Fin q → Finset κ) (t : Fin q → ℝ) (m : ℕ) (ξ : κ → F) (j : κ)
    (h : ∀ v : Pl F, evFin F v ((m : AF F) * blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j) ∈ v.adicCompletionIntegers F) :
    IsIntegral ℤ ((m : F) * ξ j) := by
  have key : ∀ v : Pl F, v.valuation F ((m : F) * ξ j) ≤ 1 := by
    intro v
    have hv := h v
    have e : evFin F v ((m : AF F) * blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j)
        = algebraMap F (Fv F v) ((m : F) * ξ j) := by
      simp only [blkScale, map_mul, map_natCast, map_prod, AlgHom.commutes]
      have : ∀ i, evFin F v (if j ∈ blk i then tAd F (t i) else 1) = 1 := by
        intro i; split_ifs
        · exact evFin_tAd F v _
        · exact map_one _
      simp only [this, Finset.prod_const_one, one_mul]
    rw [e] at hv
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hv
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ key
  rw [← hy]
  exact (y.isIntegral_coe)

end GlobalTheory.ThKTorus.IntegralOfAdic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledNormDecay
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

noncomputable section

namespace GlobalTheory.ThKTorus.MajCompare

theorem evI_add' (F : Type) [Field F] [NumberField F] (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul' (F : Type) [Field F] [NumberField F] (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_one' (F : Type) [Field F] [NumberField F] : evI F (1 : AF F) = 1 :=
  map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem evI_prod' (F : Type) [Field F] [NumberField F] {ι : Type} (s : Finset ι) (f : ι → AF F) :
    evI F (∏ i ∈ s, f i) = ∏ i ∈ s, evI F (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evI_one']
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, evI_mul', ih]

theorem evI_tAd (F : Type) [Field F] [NumberField F] (s : ℝ) :
    evI F (tAd F s) = algebraMap ℝ (mixedEmbedding.mixedSpace F) s := by
  have h : evI F (realAd F (s - 1)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (s - 1) := by
    simp [evI, realAd]
  rw [tAd, evI_add', evI_one', h, map_sub, map_one]; ring

theorem evI_algMap (F : Type) [Field F] [NumberField F] (x : F) :
    evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl

theorem evI_blkScale (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ}
    (blk : Fin q → Finset κ) (t : Fin q → ℝ) (ξ : κ → F) (j : κ) :
    evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j) =
      (∏ i, if j ∈ blk i then t i else 1) • mixedEmbedding F (ξ j) := by
  simp only [blkScale]
  rw [evI_mul', evI_prod', evI_algMap, Algebra.smul_def, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · rw [evI_tAd]
  · rw [evI_one', map_one]

end GlobalTheory.ThKTorus.MajCompare

namespace GlobalTheory.ThKTorus.MajCompare

theorem weight_le_majorant : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ] {q : ℕ} (blk : Fin q → Finset κ),
    (∀ i j, i ≠ j → Disjoint (blk i) (blk j)) → ∀ c : ℝ, 0 < c → ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ (t : Fin q → ℝ), (∀ i, c ≤ t i) → ∀ ξ : κ → F,
      ((1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j))) ^ ((q + 1) * N))⁻¹ ≤
        C * ((∏ i, (1 + t i * ∑ j ∈ blk i, ∑ w : InfinitePlace F, w (ξ j)) ^ N) *
          (1 + ∑ j, ∑ w : InfinitePlace F, w (ξ j)) ^ N)⁻¹ := by
  intro F _ _ κ _ _ q blk hdis c hc N
  set m : ℝ := min c 1 with hm_def
  have hm0 : 0 < m := lt_min hc one_pos
  refine ⟨(m ^ N)⁻¹, inv_nonneg.2 (pow_nonneg hm0.le N), ?_⟩
  intro t ht ξ
  set r : κ → ℝ := fun j => ∏ i, if j ∈ blk i then t i else 1 with hr_def
  set a : κ → ℝ := fun j => ∑ w : InfinitePlace F, w (ξ j) with ha_def
  have ha0 : ∀ j, 0 ≤ a j := fun j => Finset.sum_nonneg fun w _ => apply_nonneg w _
  have hrt : ∀ i, ∀ j ∈ blk i, r j = t i := by
    intro i j hj
    simp only [hr_def]
    rw [Finset.prod_eq_single i]
    · rw [if_pos hj]
    · intro i' _ hi'
      rw [if_neg]
      exact fun hj' => Finset.disjoint_left.1 (hdis i' i hi') hj' hj
    · intro h; exact absurd (Finset.mem_univ i) h
  have hrm : ∀ j, m ≤ r j := by
    intro j
    by_cases h : ∃ i, j ∈ blk i
    · obtain ⟨i, hi⟩ := h
      rw [hrt i j hi]; exact (min_le_left c 1).trans (ht i)
    · push_neg at h
      have : r j = 1 := by
        simp only [hr_def]
        exact Finset.prod_eq_one fun i _ => if_neg (h i)
      rw [this]; exact min_le_right c 1
  have hr0 : ∀ j, 0 < r j := fun j => hm0.trans_le (hrm j)
  have hS : (1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w
      (evI F (blkScale blk t (fun j => algebraMap F (AF F) (ξ j)) j))) = 1 + ∑ j, r j * a j := by
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [evI_blkScale, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mixedEmbedding.normAtPlace_smul, mixedEmbedding.normAtPlace_apply, abs_of_pos (hr0 j)]
  rw [hS]
  set S : ℝ := 1 + ∑ j, r j * a j with hS_def
  have hS1 : 1 ≤ S := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => mul_nonneg (hr0 j).le (ha0 j))
  have hS0 : 0 < S := one_pos.trans_le hS1
  have hA : ∀ i, 1 + t i * ∑ j ∈ blk i, a j ≤ S := by
    intro i
    rw [hS_def, Finset.mul_sum]
    refine add_le_add le_rfl ?_
    calc ∑ j ∈ blk i, t i * a j = ∑ j ∈ blk i, r j * a j :=
          Finset.sum_congr rfl fun j hj => by rw [hrt i j hj]
      _ ≤ ∑ j, r j * a j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun j _ _ => mul_nonneg (hr0 j).le (ha0 j)
  have hA0 : ∀ i, 0 ≤ 1 + t i * ∑ j ∈ blk i, a j := fun i =>
    add_nonneg zero_le_one (mul_nonneg (hc.le.trans (ht i)) (Finset.sum_nonneg fun j _ => ha0 j))
  have hB : m * (1 + ∑ j, a j) ≤ S := by
    rw [mul_add, mul_one, Finset.mul_sum, hS_def]
    exact add_le_add (min_le_right c 1) (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_right (hrm j) (ha0 j))
  have hB0 : 0 < 1 + ∑ j, a j := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => ha0 j)
  have hP0 : 0 < (∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (1 + ∑ j, a j) ^ N := by
    refine mul_pos (Finset.prod_pos fun i _ => pow_pos ?_ N) (pow_pos hB0 N)
    exact one_pos.trans_le (le_add_of_nonneg_right (mul_nonneg (hc.le.trans (ht i))
      (Finset.sum_nonneg fun j _ => ha0 j)))
  have key : m ^ N * ((∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (1 + ∑ j, a j) ^ N) ≤ S ^ ((q + 1) * N) := by
    have h1 : ∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N ≤ S ^ (q * N) := by
      calc ∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N ≤ ∏ _i : Fin q, S ^ N :=
            Finset.prod_le_prod (fun i _ => pow_nonneg (hA0 i) N) fun i _ => pow_le_pow_left₀ (hA0 i) (hA i) N
        _ = S ^ (q * N) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
    have h2 : (m * (1 + ∑ j, a j)) ^ N ≤ S ^ N := pow_le_pow_left₀ (mul_nonneg hm0.le hB0.le) hB N
    calc m ^ N * ((∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (1 + ∑ j, a j) ^ N)
        = (∏ i, (1 + t i * ∑ j ∈ blk i, a j) ^ N) * (m * (1 + ∑ j, a j)) ^ N := by rw [mul_pow]; ring
      _ ≤ S ^ (q * N) * S ^ N := mul_le_mul h1 h2 (pow_nonneg (mul_nonneg hm0.le hB0.le) N) (pow_nonneg hS0.le _)
      _ = S ^ ((q + 1) * N) := by rw [← pow_add]; ring_nf
  rw [← mul_inv]
  exact inv_anti₀ (mul_pos (pow_pos hm0 N) hP0) key

end GlobalTheory.ThKTorus.MajCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariant
section
open ValuativeRel Matrix

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.RankCoinv

theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hν1 i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0
  set g : Matrix A D k → ℂ := boxFn ϖ C (fun _ => m) with hg
  set g' : Matrix A D k → ℂ := boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) with hg'
  set lam : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) * apow ϖ (-(Fintype.card D : ℂ) / 2) with hlam
  set N : ℕ := Fintype.card (Fin r → Res k 1) with hN
  let F : (Fin r → Res k 1) → Matrix A D k → ℂ := fun b => boxFn ϖ (Matrix.updateRow C i₀
    ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m)

  have hz := GlobalTheory.T.box_function_diagonal_action k A D ϖ ν β i₀ C hC0 m (m - 1)
  have hupd : Function.update (fun _ : A => m) i₀ m = fun _ => m := Function.update_eq_self _ _
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m), hupd] at hz
  have h3 : lam • g - g' ∈ twistSpan ν β := by
    rw [hlam, hg, ← hz]; exact sub_mem_twistSpan ν β _ (boxFn_mem_SB _ _ _)

  have h1 : g' - ∑ b, F b ∈ lowRank (r + 1) :=
    GlobalTheory.T.integral_box_bounded_valuation k A D ϖ hϖ i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0

  have hv1 : valuation k (ϖ : k) ≤ 1 := by rw [hϖ]; exact (uniformizer_lt_one (R := k)).le
  have h2 : ∀ b, F b - g ∈ twistSpan ν β := by
    intro b
    have ht : ∀ l, valuation k ((ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ≤
        valuation k ((ϖ ^ c : kˣ) : k) := by
      intro l
      have hout : valuation k ((Quotient.out (b l) : 𝒪[k]) : k) ≤ 1 := (Quotient.out (b l)).2
      rw [map_mul, map_pow, Units.val_pow_eq_pow_val, map_pow]
      exact (mul_le_of_le_one_right' hout).trans (pow_le_pow_right_of_le_one' hv1 (by omega))
    have hu := GlobalTheory.T.box_function_action_bounded_matrix k A D ϖ ν β i₀ r c m C H _ hH0 hHv ht
    have hrow : C i₀ = 0 := funext hC0
    rw [hrow, zero_add] at hu
    exact hu

  have key : (lam - (N : ℂ)) • g ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    have e : (lam - (N : ℂ)) • g = (g' - ∑ b, F b) + ∑ b, (F b - g) + (lam • g - g') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, sub_smul, Nat.cast_smul_eq_nsmul ℂ]
      abel
    rw [e]
    exact add_mem (add_mem (Submodule.mem_sup_left h1)
      (Submodule.mem_sup_right (Submodule.sum_mem _ fun b _ => h2 b))) (Submodule.mem_sup_right h3)

  have hne : lam - (N : ℂ) ≠ 0 := by
    intro h
    have hl : lam = N := sub_eq_zero.1 h
    set a : ℝ := nabs k ϖ ^ (-(Fintype.card D : ℝ) / 2) with ha_def
    have hapos : 0 < a := Real.rpow_pos_of_pos (nabs_pos ϖ) _
    have ha : apow ϖ (-(Fintype.card D : ℂ) / 2) = (a : ℂ) := by
      rw [apow, ha_def, Complex.ofReal_cpow (nabs_pos ϖ).le]
      push_cast; ring_nf
    set u : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) with hu_def
    have hua : u * a = N := by rw [← ha]; exact hl
    have hu : u = ((N / a : ℝ) : ℂ) := by
      have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hapos.ne'
      rw [Complex.ofReal_div, Complex.ofReal_natCast, ← hua, mul_div_cancel_right₀ _ ha0]
    have hnorm : ‖u‖ = 1 := by
      rw [hu_def, Units.val_inv_eq_inv_val, norm_inv, hν, inv_one]
    rw [hu, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hapos.le)] at hnorm
    have hu1 : u = 1 := by rw [hu, hnorm]; simp
    apply hν1
    have : (ν ϖ)⁻¹ = 1 := Units.ext (by simpa [hu_def] using hu1)
    exact inv_eq_one.1 this
  exact (Submodule.smul_mem_iff _ hne).1 key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
section
noncomputable section

namespace GlobalTheory.HCFinU

open NumberField Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def starOf (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) : StarRing E where
  star := σ
  star_involutive := hσ
  star_mul x y := by simp only [map_mul, mul_comm]
  star_add := map_add σ

def mkI (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (cm : @Formalism.BasicNotions.CMData F E _ _ _ _ (starOf σ hσ) _) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hdual : ∀ x : Fin n → E, x ∈ L ↔
      ∀ y ∈ L, Formalism.UG.hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range)
    (ε : InfinitePlace F → Fin n → Bool) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) (P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ)
    (hPu : ∀ v, IsUnit (P v)) (hP : ∀ v, (P v)ᴴ * J.map (φ v) * P v = Formalism.REAL.Jm (ε v)) :
    Formalism.MainNotions.S.AutInst :=
  letI := starOf σ hσ
  { F := F, E := E, cm := cm, n := n, J := J
    J_herm := Matrix.ext fun i j => hJ i j
    J_det := hdet
    L := L
    L_span := hspan
    L_fg := hfg
    L_dual := hdual
    ε := ε
    φ := φ
    φ_over := hφ
    P := P
    P_unit := hPu
    P_spec := hP
    topf := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose
    topf_group := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose_spec.1
    topf_open := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose_spec.2.1
    topf_basis := (Formalism.MainNotions.S.Inh.aut_HTop_holds cm J L hfg hspan).choose_spec.2.2 }

theorem mkI_sig (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x)
    (cm : @Formalism.BasicNotions.CMData F E _ _ _ _ (starOf σ hσ) _) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hdual : ∀ x : Fin n → E, x ∈ L ↔
      ∀ y ∈ L, Formalism.UG.hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range)
    (ε : InfinitePlace F → Fin n → Bool) (φ : InfinitePlace F → (E →+* ℂ))
    (hφ : ∀ v (a : F), φ v (algebraMap F E a) = v.embedding a) (P : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ)
    (hPu : ∀ v, IsUnit (P v)) (hP : ∀ v, (P v)ᴴ * J.map (φ v) * P v = Formalism.REAL.Jm (ε v)) :
    σ = (mkI σ hσ cm J hJ hdet L hfg hspan hdual ε φ hφ P hPu hP).cm.sig :=
  AlgHom.ext fun _ => rfl

def bridgeS (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) :
    I.GA ≃ₜ* GlobalTheory.AdelicU.GAd s I.J := by
  subst hs
  exact Formalism.L2.SG.AdBridge.toHA I (Formalism.L2.SG.Closed.AdBridgeIso_holds I)

theorem bridgeS_isBridge (I : Formalism.MainNotions.S.AutInst) :
    Formalism.L2.SG.AdBridge.IsBridge I (bridgeS I I.cm.sig rfl) :=
  Formalism.L2.SG.AdBridge.toHA_isBridge I _

theorem bridgeS_rat (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) :
    ∀ γ ∈ I.GFset, bridgeS I s hs γ ∈ GlobalTheory.AdelicU.ratPts s I.J := by
  subst hs
  intro γ hγ
  have h := Formalism.L2.SG.Closed.AdBridgeGF_holds I (bridgeS I _ rfl) (bridgeS_isBridge I)
  have h2 : bridgeS I _ rfl γ ∈ Formalism.L2.SG.AdBridge.ratHA I := h ▸ Set.mem_image_of_mem _ hγ
  exact Subgroup.mem_subgroupOf.2 h2

end GlobalTheory.HCFinU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralOperatorCommutesLineDerivative
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

noncomputable section
namespace GlobalTheory.UAut.CentralComm

theorem hasDerivAt_snd {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {H : X × ℝ → ℂ}
    (hH : Differentiable ℝ H) (x : X) : HasDerivAt (fun t => H (x, t)) (fderiv ℝ H (x, 0) (0, 1)) 0 :=
  (hH (x, 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))

theorem hasDerivAt_fst {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {H : ℝ × X → ℂ}
    (hH : Differentiable ℝ H) (x : X) : HasDerivAt (fun t => H (t, x)) (fderiv ℝ H (0, x) (1, 0)) 0 :=
  (hH (0, x)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))

theorem contDiff_deriv_snd {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {H : X × ℝ → ℂ}
    (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ fun x => deriv (fun t => H (x, t)) 0 := by
  simp only [fun x => (hasDerivAt_snd (hH.differentiable (by simp)) x).deriv]
  exact ((hH.fderiv_right (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const

theorem deriv_deriv_comm {H : ℝ × ℝ → ℂ} (hH : ContDiff ℝ ∞ H) :
    deriv (fun s => deriv (fun t => H (s, t)) 0) 0 = deriv (fun t => deriv (fun s => H (s, t)) 0) 0 := by
  have hd := hH.differentiable (by simp)
  have h2 : Differentiable ℝ (fderiv ℝ H) := (hH.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  simp only [fun x => (hasDerivAt_snd hd x).deriv, fun x => (hasDerivAt_fst hd x).deriv]
  have e1 : HasDerivAt (fun s : ℝ => fderiv ℝ H (s, 0)) (fderiv ℝ (fderiv ℝ H) (0, 0) (1, 0)) 0 :=
    (h2 (0, 0)).hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, (0 : ℝ))) (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)))
  have e2 : HasDerivAt (fun t : ℝ => fderiv ℝ H (0, t)) (fderiv ℝ (fderiv ℝ H) (0, 0) (0, 1)) 0 :=
    (h2 (0, 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ)))
  have e3 := (e1.clm_apply (hasDerivAt_const (0 : ℝ) ((0, 1) : ℝ × ℝ))).deriv
  have e4 := (e2.clm_apply (hasDerivAt_const (0 : ℝ) ((1, 0) : ℝ × ℝ))).deriv
  rw [e3, e4]
  simp only [map_zero, add_zero]
  exact (hH.contDiffAt.isSymmSndFDerivAt (by simpa using ENat.LEInfty.out)) _ _

theorem prod_snoc {G : Type} [Monoid G] {m : ℕ} (δ : Fin m → ℝ → G) (γ : ℝ → G) (s : Fin m → ℝ) (t : ℝ) :
    (List.ofFn fun i : Fin (m + 1) => (Fin.snoc (α := fun _ => ℝ → G) δ γ i) (Fin.snoc (α := fun _ => ℝ) s t i)).prod =
      (List.ofFn fun i => δ i (s i)).prod * γ t := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem contDiff_snoc {k : ℕ} :
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using contDiff_snd
  · simp only [Fin.snoc_castSucc]
    exact (contDiff_apply ℝ ℝ j).comp contDiff_fst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

variable (σ J) in

def IsSmFamily (u : ℝ → GAd σ J → ℂ) : Prop :=
  ∀ (k : ℕ) (δ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (δ i)) → ∀ g,
    ContDiff ℝ ∞ fun p : ℝ × (Fin k → ℝ) => u p.1 (g * (List.ofFn fun i => δ i (p.2 i)).prod)

omit [NumberField E] in
theorem isRealLine_snoc {k : ℕ} {δ : Fin k → ℝ → GAd σ J} (hδ : ∀ i, IsRealLine σ J (δ i)) {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) (i : Fin (k + 1)) : IsRealLine σ J (Fin.snoc (α := fun _ => ℝ → GAd σ J) δ γ i) :=
  Fin.lastCases (by simpa using hγ) (fun j => by simpa using hδ j) i

omit [NumberField E] in

theorem isSmFamily_translate {f : GAd σ J → ℂ} (hf : IsSm σ J f) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    IsSmFamily σ J fun s x => f (x * γ s) := fun k δ hδ g => by
  have h := (hf (k + 1) _ (isRealLine_snoc hδ hγ) g).comp (contDiff_snoc.comp (contDiff_snd.prodMk contDiff_fst))
  simpa only [Function.comp_def, prod_snoc, ← mul_assoc] using h

omit [NumberField E] in

theorem IsSmFamily.lineDer {u : ℝ → GAd σ J → ℂ} (hu : IsSmFamily σ J u) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    IsSmFamily σ J fun s => lineDer γ (u s) := fun k δ hδ g => by
  have h := (hu (k + 1) _ (isRealLine_snoc hδ hγ) g).comp
    (((contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_snoc.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))) :
      ContDiff ℝ ∞ fun q : (ℝ × (Fin k → ℝ)) × ℝ => (q.1.1, (Fin.snoc (α := fun _ => ℝ) q.1.2 q.2 : Fin (k + 1) → ℝ)))
  simpa only [Function.comp_def, prod_snoc, ← mul_assoc, SiegelSet.lineDer] using contDiff_deriv_snd h

omit [NumberField E] in

theorem IsSmFamily.differentiable {u : ℝ → GAd σ J → ℂ} (hu : IsSmFamily σ J u) (g : GAd σ J) :
    Differentiable ℝ fun s => u s g := by
  have h := (hu 0 Fin.elim0 (fun i => i.elim0) g).comp
    (contDiff_id.prodMk contDiff_const : ContDiff ℝ ∞ fun s : ℝ => (s, (0 : Fin 0 → ℝ)))
  simpa [Function.comp_def] using h.differentiable (by simp)

omit [NumberField E] in

theorem IsSmFamily.deriv_lineDer {u : ℝ → GAd σ J → ℂ} (hu : IsSmFamily σ J u) {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) (g : GAd σ J) :
    deriv (fun s => SiegelSet.lineDer γ (u s) g) 0 = SiegelSet.lineDer γ (fun x => deriv (fun s => u s x) 0) g := by
  have h := (hu 1 (fun _ => γ) (fun _ => hγ) g).comp
    (contDiff_fst.prodMk (contDiff_pi.2 fun _ => contDiff_snd) :
      ContDiff ℝ ∞ fun q : ℝ × ℝ => (q.1, fun _ : Fin 1 => q.2))
  have h' : ContDiff ℝ ∞ fun q : ℝ × ℝ => u q.1 (g * γ q.2) := by simpa [Function.comp_def] using h
  exact deriv_deriv_comm h'

omit [NumberField E] in

theorem IsSmFamily.foldr {u : ℝ → GAd σ J → ℂ} (hu : IsSmFamily σ J u) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsSmFamily σ J (fun s => l.foldr SiegelSet.lineDer (u s)) ∧
      (fun x => deriv (fun s => l.foldr SiegelSet.lineDer (u s) x) 0) =
        l.foldr SiegelSet.lineDer fun x => deriv (fun s => u s x) 0
  | [], _ => ⟨hu, rfl⟩
  | γ :: l, hl => by
    obtain ⟨h1, h2⟩ := hu.foldr l fun γ' h => hl γ' (List.mem_cons_of_mem _ h)
    have hγ := hl γ List.mem_cons_self
    refine ⟨h1.lineDer hγ, funext fun x => ?_⟩
    simp only [List.foldr_cons]
    rw [← h2]
    exact h1.deriv_lineDer hγ x

theorem lineDer_dop_comm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (z : List (ℝ → GAd σ J) →₀ ℂ), IsCentral σ J z →
    ∀ f : GAd σ J → ℂ, IsSm σ J f → ∀ γ : ℝ → GAd σ J, IsRealLine σ J γ →
      lineDer γ (dop z f) = dop z (lineDer γ f) := by
  intro F E _ _ _ _ _ σ n J z hz f hf γ hγ
  have hinf : ∀ s, γ s ∈ infPts σ J := fun s => by
    obtain ⟨w, τ, Z, -, h⟩ := hγ
    obtain ⟨y, e, -⟩ := h s
    exact e ▸ mem_infPts.2 (projFin_embArch _ _ _ _)
  have hu := isSmFamily_translate hf hγ
  funext g
  have e : (fun s => dop z f (g * γ s)) =
      fun s => ∑ l ∈ z.support, z l * l.foldr lineDer (fun x => f (x * γ s)) g :=
    funext fun s => (hz.2 f hf _ (hinf s) g).symm
  change deriv (fun s => dop z f (g * γ s)) 0 = ∑ l ∈ z.support, z l * l.foldr lineDer (lineDer γ f) g
  rw [e]
  refine (HasDerivAt.fun_sum fun l hl => HasDerivAt.const_mul (z l) ?_).deriv
  obtain ⟨h1, h2⟩ := hu.foldr l (hz.1 l hl)
  have h3 := (h1.differentiable g 0).hasDerivAt
  rw [congrFun h2 g] at h3
  exact h3

end GlobalTheory.UAut.CentralComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperatorStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_local_operator : ∀ {F : Type} [Field F] [NumberField F] {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ), IsLocOp e → IsLocOp (conjLin e) := by
  first | exact @GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin | exact GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin | (intros; apply GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin <;> assumption)
end

