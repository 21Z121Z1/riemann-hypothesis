import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0769
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapOrbUnitEqOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitOrbCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cp_conj {n : ℕ} {w : Pl E} (g γ : UL n w) :
    (g⁻¹ * γ * g).1.val.charpoly = γ.1.val.charpoly := by
  have h : ((g⁻¹ * γ * g : UL n w) : GLw n w) = (g : GLw n w)⁻¹ * (γ : GLw n w) * (g : GLw n w) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have h2 : (g⁻¹ * γ * g).1.val = ((g : GLw n w)⁻¹ : GLw n w).val * γ.1.val * (g : GLw n w).val := by
    rw [← Units.val_mul, ← Units.val_mul]
    exact congrArg Units.val h
  rw [h2, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' (g : GLw n w) γ.1.val

theorem mk_eq_iff {G : Type} [Group G] (x y : G) :
    (Quot.mk _ x : TwCl (MonoidHom.id G)) = Quot.mk _ y ↔ ∃ g : G, y = g⁻¹ * x * g := by
  constructor
  · intro h
    have h' := Quot.eqvGen_exact h
    clear h
    induction h' with
    | rel a b hab => obtain ⟨g, hg⟩ := hab; exact ⟨g, by simpa using hg⟩
    | refl a => exact ⟨1, by simp⟩
    | symm a b _ ih => obtain ⟨g, hg⟩ := ih; exact ⟨g⁻¹, by rw [hg]; group⟩
    | trans a b c _ _ ih1 ih2 =>
      obtain ⟨g, hg⟩ := ih1; obtain ⟨k, hk⟩ := ih2; exact ⟨g * k, by rw [hk, hg]; group⟩
  · rintro ⟨g, hg⟩
    exact Quot.sound ⟨g, by simpa using hg⟩

theorem exists_section : ∃ S : Set (Pl E), IsSection S := by
  refine ⟨{u | u = @Classical.epsilon _ ⟨u⟩ fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      u.under (𝓞 (maximalRealSubfield E))}, fun w => ?_⟩
  haveI : Nonempty (Pl E) := ⟨w⟩
  have hspec := Classical.epsilon_spec (p := fun u' : Pl E => u'.under (𝓞 (maximalRealSubfield E)) =
      w.under (𝓞 (maximalRealSubfield E))) ⟨w, rfl⟩
  refine ⟨_, ⟨?_, hspec⟩, ?_⟩
  · show _ = _
    simp only [hspec]
  · rintro u ⟨hu, hu'⟩
    rw [Set.mem_setOf_eq] at hu
    rw [hu]
    simp only [hu']

theorem ell_mul {n : ℕ} (p₁ p₂ : E[X]) (h1 : p₁ ∈ Ell E p₁.natDegree) (h2 : p₂ ∈ Ell E p₂.natDegree)
    (hc : IsCoprime p₁ p₂) (hn : p₁.natDegree + p₂.natDegree = n) : p₁ * p₂ ∈ Ell E n := by
  obtain ⟨m1, -, s1, r1⟩ := h1
  obtain ⟨m2, -, s2, r2⟩ := h2
  refine ⟨m1.mul m2, by rw [m1.natDegree_mul m2, hn], s1.mul s2 hc, fun τ z hz => ?_⟩
  rw [Polynomial.map_mul, Polynomial.roots_mul] at hz
  · rcases Multiset.mem_add.1 hz with h | h
    · exact r1 τ z h
    · exact r2 τ z h
  · rw [← Polynomial.map_mul]
    exact ((m1.mul m2).map τ).ne_zero

end GlobalTheory.UnitOrbCount

namespace GlobalTheory.UnitOrbCount

theorem kapOrb_unit_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ p₁ p₂ : E[X], p₁ ∈ Ell E p₁.natDegree → p₂ ∈ Ell E p₂.natDegree → IsCoprime p₁ p₂ → p₁.natDegree + p₂.natDegree = n → ∀ᶠ w in cofinite, kapOrb n w (atPl w p₁) (atPl w p₂) ((KL n w : Set (UL n w)).indicator 1) = 1 := by
  intro E _ _ _ hU n hn p₁ p₂ h1 h2 hc hd
  have hP := ell_mul p₁ p₂ h1 h2 hc hd
  obtain ⟨S, hS⟩ := exists_section (E := E)
  filter_upwards [GlobalTheory.T.orbitalIntegral_unitIndicator_eventually_oneClass E hU n hn S hS _ hP, GlobalTheory.T.eventually_exists_integral_charpoly_split_place E hU n hn _ hP, GlobalTheory.T.exists_integral_element_char_poly_nonsplit E hU n hn _ hP,
    GlobalTheory.T.eventually_unitary_conj_of_same_elliptic_charpoly_inert E hU n hn _ hP] with w hA hE1 hE2 hU2
  have hmap : atPl w (p₁ * p₂) = atPl w p₁ * atPl w p₂ := Polynomial.map_mul _
  rw [hmap] at hA hE1 hE2 hU2
  obtain ⟨γ₀, hγ₀K, hγ₀P⟩ : ∃ γ : UL n w, γ ∈ KL n w ∧ γ.1.val.charpoly = atPl w p₁ * atPl w p₂ := by
    by_cases hs : IsSplitAt w
    · exact hE1 hs
    · exact hE2 hs
  have huniq : ∀ γ γ' : UL n w, γ ∈ KL n w → γ' ∈ KL n w → γ.1.val.charpoly = atPl w p₁ * atPl w p₂ →
      γ'.1.val.charpoly = atPl w p₁ * atPl w p₂ → ∃ g : UL n w, γ' = g⁻¹ * γ * g := by
    intro γ γ' hk hk' hp hp'
    by_cases hs : IsSplitAt w
    · have := GlobalTheory.T.exists_conj_same_separable_charpoly_split_place E n _ hP w hs γ γ'
      rw [hmap] at this
      exact this hp hp'
    · exact hU2 hs γ γ' hk hk' hp hp'
  have key : ∀ γ : UL n w, γ.1.val.charpoly = atPl w p₁ * atPl w p₂ →
      ((∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w) ↔ (Quot.mk _ γ : TwCl (MonoidHom.id (UL n w))) = Quot.mk _ γ₀) := by
    intro γ hp
    rw [mk_eq_iff]
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨k, hk⟩ := huniq _ γ₀ hg hγ₀K (by rw [cp_conj, hp]) hγ₀P
      exact ⟨g * k, by rw [hk]; group⟩
    · rintro ⟨g, hg⟩
      exact ⟨g, hg ▸ hγ₀K⟩
  unfold kapOrb clSum
  simp only [Set.mem_setOf_eq]
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : TwCl (MonoidHom.id (UL n w)), Quot.mk _ γ₀ = c₀ := ⟨_, rfl⟩
  rw [hc₀] at key
  rw [finsum_eq_single _ c₀]
  · have hc : (Quot.mk _ c₀.rep : TwCl (MonoidHom.id (UL n w))) = Quot.mk _ γ₀ := by
      rw [hc₀]; exact Quot.out_eq _
    obtain ⟨g, hg⟩ := (mk_eq_iff _ _).1 hc
    have hp : c₀.rep.1.val.charpoly = atPl w p₁ * atPl w p₂ := by
      rw [← hγ₀P, hg, cp_conj]
    have hex : ∃ g : UL n w, g⁻¹ * c₀.rep * g ∈ KL n w :=
      ⟨g, hg ▸ hγ₀K⟩
    obtain ⟨hT, -, hQ⟩ := hA _ hp
    rw [if_pos hp, hT, if_pos hex, hQ (atPl w p₁) (dvd_mul_right _ _) hex, mul_one]
  · intro c hne
    have hc : (Quot.mk _ c.rep : TwCl (MonoidHom.id (UL n w))) = c := Quot.out_eq c
    by_cases hp : c.rep.1.val.charpoly = atPl w p₁ * atPl w p₂
    · obtain ⟨hT, -, -⟩ := hA c.rep hp
      rw [if_pos hp, hT, if_neg, mul_zero]
      intro hex
      apply hne
      rw [← hc]
      exact (key _ hp).1 hex
    · rw [if_neg hp]

end GlobalTheory.UnitOrbCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingHyperbolicFirst
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.FrameInv

open Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem gram_entry (σ : E →ₐ[F] E) {N : ℕ} {ι₁ ι₂ : Type*} (J : Matrix (Fin N) (Fin N) E) (A : Matrix (Fin N) ι₁ E)
    (B : Matrix (Fin N) ι₂ E) (i : ι₁) (j : ι₂) :
    (Aᵀ * J * B.map σ) i j = form σ J (fun r => A r i) (fun r => B r j) := by
  simp only [Matrix.mul_apply, form, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ e, σ (σ e) = e) {N : ℕ} {J : Matrix (Fin N) (Fin N) E}
    (hsk : ∀ i j, σ (J j i) = -J i j) (a b : Fin N → E) :
    form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hsk]; ring

def idx (n₁ : ℕ) : Fin (1 + n₁ + 1) → Fin n₁ ⊕ Fin 2 :=
  Fin.addCases (Fin.addCases (fun _ => Sum.inr 0) fun k => Sum.inl k) fun _ => Sum.inr 1

theorem one_idx {n₁ : ℕ} (i j : Fin (1 + n₁ + 1)) :
    (1 : Matrix (Fin n₁ ⊕ Fin 2) (Fin n₁ ⊕ Fin 2) E) (idx n₁ i) (idx n₁ j) = (1 : Matrix _ _ E) i j := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left a =>
      induction j using Fin.addCases with
      | left j =>
        induction j using Fin.addCases with
        | left b => simp [idx, one_apply, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]
        | right k => simp [idx, one_apply, Fin.ext_iff] <;> omega
      | right b => simp [idx, one_apply, Fin.ext_iff] <;> omega
    | right k =>
      induction j using Fin.addCases with
      | left j =>
        induction j using Fin.addCases with
        | left b => simp [idx, one_apply, Fin.ext_iff] <;> omega
        | right l => simp [idx, one_apply, Fin.ext_iff]
      | right b => simp [idx, one_apply, Fin.ext_iff] <;> omega
  | right a =>
    induction j using Fin.addCases with
    | left j =>
      induction j using Fin.addCases with
      | left b => simp [idx, one_apply, Fin.ext_iff] <;> omega
      | right l => simp [idx, one_apply, Fin.ext_iff] <;> omega
    | right b => simp [idx, one_apply, Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]

variable [NumberField F] [NumberField E]

theorem frame_invertible : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∃ R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E, frame H * R = 1 ∧ R * frame H = 1 := by
  intro F E _ _ _ _ _ σ hcm n n₁ Y Y₁ H hsk hn hxx hyy hxy horth hgram hdet
  have hσ : ∀ e, σ (σ e) = e := GlobalTheory.SiegelSet.sigma_sigma hcm
  subst hn
  set XY : Matrix (Fin (n₁ + 2)) (Fin 2) E := Matrix.of fun r t => ![H.x, H.y] t r with hXY
  set Q : Matrix (Fin (n₁ + 2)) (Fin n₁ ⊕ Fin 2) E := fromCols H.ι XY with hQ
  set S₂ : Matrix (Fin 2) (Fin 2) E := !![0, 1; -1, 0] with hS₂
  have hyx : form σ Y.J H.y H.x = -1 := by rw [form_swap hσ hsk, hxy, map_one]
  have horth' : ∀ i, form σ Y.J (fun r => H.ι r i) H.x = 0 ∧ form σ Y.J (fun r => H.ι r i) H.y = 0 := by
    intro i
    have e : (fun r => H.ι r i) = H.ι *ᵥ Pi.single i 1 := by
      funext r; simp [mulVec, dotProduct, Pi.single_apply]
    rw [e]; exact horth _
  have hK : Qᵀ * Y.J * Q.map σ = fromBlocks Y₁.J 0 0 S₂ := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rw [fromBlocks_apply₁₁, ← hgram, gram_entry, gram_entry]; rfl
    · rw [fromBlocks_apply₁₂, gram_entry]
      fin_cases j
      · simpa [Q, XY] using (horth' i).1
      · simpa [Q, XY] using (horth' i).2
    · rw [fromBlocks_apply₂₁, gram_entry, form_swap hσ hsk]
      fin_cases i
      · simp [Q, XY, (horth' j).1]
      · simp [Q, XY, (horth' j).2]
    · rw [fromBlocks_apply₂₂, gram_entry]
      fin_cases i <;> fin_cases j <;> simp [Q, XY, S₂, hxx, hyy, hxy, hyx]
  have hdetK : (fromBlocks Y₁.J 0 0 S₂).det ≠ 0 := by
    rw [det_fromBlocks_zero₂₁]; simp [S₂, Matrix.det_fin_two_of, hdet]
  have hKu : IsUnit (fromBlocks Y₁.J 0 0 S₂).det := isUnit_iff_ne_zero.2 hdetK
  set R' : Matrix (Fin n₁ ⊕ Fin 2) (Fin (n₁ + 2)) E := ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J).map σ with hR'
  have h0 : (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = 1 := by
    have : (fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ = (fromBlocks Y₁.J 0 0 S₂)⁻¹ * (Qᵀ * Y.J * Q.map σ) := by
      simp only [Matrix.mul_assoc]
    rw [this, hK, nonsing_inv_mul _ hKu]
  have hQQ : (Q.map σ).map (σ : E →+* E) = Q := by ext i j; simp [hσ]
  have hRQ : R' * Q = 1 := by
    calc R' * Q = ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J).map (σ : E →+* E) * (Q.map σ).map (σ : E →+* E) := by
          rw [hQQ]; rfl
      _ = ((fromBlocks Y₁.J 0 0 S₂)⁻¹ * Qᵀ * Y.J * Q.map σ).map (σ : E →+* E) := Matrix.map_mul.symm
      _ = 1 := by rw [h0]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have hfr : ∀ r c, frame H r c = Q r (idx n₁ c) := by
    intro r c
    induction c using Fin.addCases with
    | left c =>
      induction c using Fin.addCases with
      | left a => simp [frame, idx, Q, XY]
      | right k => simp [frame, idx, Q, XY]
    | right a => simp [frame, idx, Q, XY]
  refine ⟨Matrix.of fun i r => R' (idx n₁ i) r, ?_, ?_⟩
  · refine (mul_eq_one_comm_of_card_eq (Fin (n₁ + 2)) (Fin (1 + n₁ + 1)) E (by simp; omega)).2 ?_
    ext i j
    simp only [mul_apply, of_apply, hfr]
    rw [← one_idx (E := E) i j, ← hRQ, mul_apply]
  · ext i j
    simp only [mul_apply, of_apply, hfr]
    rw [← one_idx (E := E) i j, ← hRQ, mul_apply]

end GlobalTheory.LeviHC.FrameInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingHyperbolicThird
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC

open Matrix

theorem blk_le_two (n₁ : ℕ) (i : Fin (1 + n₁ + 1)) : blk n₁ i ≤ 2 := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left a => simp [blk]
    | right k => simp [blk]
  | right a => simp [blk]

theorem blk_cases {n₁ : ℕ} (i : Fin (1 + n₁ + 1)) :
    (∃ a, i = Fin.castAdd 1 (Fin.castAdd n₁ a)) ∨ (∃ k, i = mid k) ∨ (∃ a, i = Fin.natAdd (1 + n₁) a) := by
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left a => exact Or.inl ⟨a, rfl⟩
    | right k => exact Or.inr (Or.inl ⟨k, rfl⟩)
  | right a => exact Or.inr (Or.inr ⟨a, rfl⟩)

theorem one_sub_four_mul_ne_zero {a b : ℕ} (ha : a ≤ 2) (hb : b ≤ 2) (hab : a + b ≠ 2) :
    (1 - 4 * (2⁻¹ : ℂ) ^ (a + b)) ≠ 0 := by
  interval_cases a <;> interval_cases b <;> first | exact absurd rfl hab | norm_num

theorem blk_support_of_mul_eq_one {n₁ : ℕ} {M N : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) ℂ}
    (hM : ∀ i j, blk n₁ i + blk n₁ j ≠ 2 → M i j = 0) (hMN : M * N = 1) :
    ∀ i j, blk n₁ i + blk n₁ j ≠ 2 → N i j = 0 := by
  obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) ℂ, D = diagonal fun i => (2 : ℂ) ^ blk n₁ i :=
    ⟨_, rfl⟩
  obtain ⟨Di, hDi⟩ : ∃ D : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) ℂ, D = diagonal fun i => (2⁻¹ : ℂ) ^ blk n₁ i :=
    ⟨_, rfl⟩
  have hDDi : D * Di = 1 := by
    rw [hD, hDi, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext i; rw [← mul_pow]; norm_num
  have hMDi : M * Di = (4⁻¹ : ℂ) • (D * M) := by
    ext i j
    rw [hD, hDi, mul_diagonal, Matrix.smul_apply, diagonal_mul, smul_eq_mul]
    by_cases h : blk n₁ i + blk n₁ j = 2
    · have e : (2 : ℂ) ^ blk n₁ i = 4 * 2⁻¹ ^ blk n₁ j := by
        have : (2 : ℂ) ^ blk n₁ i * 2 ^ blk n₁ j = 4 := by rw [← pow_add, h]; norm_num
        rw [← this, mul_assoc, ← mul_pow]; norm_num
      rw [e]; ring
    · rw [hM i j h]; ring
  have hNM : N * M = 1 := mul_eq_one_comm.1 hMN
  have h1 : M * ((4 : ℂ) • (Di * N * Di)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hMDi, Matrix.smul_mul, Matrix.smul_mul, smul_smul,
      Matrix.mul_assoc D M N, hMN, Matrix.mul_one, hDDi]
    norm_num
  have key : N = (4 : ℂ) • (Di * N * Di) := by
    calc N = N * (M * ((4 : ℂ) • (Di * N * Di))) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hNM, Matrix.one_mul]
  intro i j hij
  have e := congrFun (congrFun key i) j
  rw [Matrix.smul_apply, hDi, mul_diagonal, diagonal_mul, smul_eq_mul] at e
  have h0 : (1 - 4 * (2⁻¹ : ℂ) ^ (blk n₁ i + blk n₁ j)) * N i j = 0 := by
    rw [pow_add]; linear_combination e
  exact (mul_eq_zero.1 h0).resolve_left (one_sub_four_mul_ne_zero (blk_le_two n₁ i) (blk_le_two n₁ j) hij)

theorem adj_frame_blockTri : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
    (∀ i j, σ (Y.J j i) = -Y.J i j) → n = n₁ + 2 → form σ Y.J H.x H.x = 0 → form σ Y.J H.y H.y = 0 → form σ Y.J H.x H.y = 1 →
    (∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * Y.J * H.ι.map σ = Y₁.J → Y₁.J.det ≠ 0 →
    ∀ R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E, frame H * R = 1 → R * frame H = 1 →
    ∀ c : E, c ≠ 0 → IsHermND σ (c • Y.J.map σ) → IsHermND σ (c • Y₁.J.map σ) →
    ∀ (τ : E →+* ℂ) (s : ℕ) (X : Matrix (Fin n) (Fin n) ℂ),
      (∀ i j, blk n₁ j < blk n₁ i + s → (R.map τ * X * (frame H).map τ) i j = 0) →
      ∀ i j, blk n₁ j < blk n₁ i + s → (R.map τ * adj ((c • Y.J.map σ).map τ) X * (frame H).map τ) i j = 0 := by
  intro F E _ _ _ _ _ σ h n n₁ Y Y₁ H hsk hn hxx hyy hxy horth hgram hdet1 R hQR hRQ c hc hA hA₁ τ s X hX i j hij
  have hσ : ∀ e, σ (σ e) = e := fun e => τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])
  have hQR' : (frame H).map τ * R.map τ = 1 := by
    rw [← Matrix.map_mul, hQR, Matrix.map_one _ τ.map_zero τ.map_one]
  have hRQ' : R.map τ * (frame H).map τ = 1 := by
    rw [← Matrix.map_mul, hRQ, Matrix.map_one _ τ.map_zero τ.map_one]
  have hAu : IsUnit ((c • Y.J.map σ).map τ).det := isUnit_det_map hA τ

  have hGf : ∀ a b, ((frame H)ᵀ * Y.J * (frame H).map σ) a b =
      form σ Y.J (fun r => frame H r a) (fun r => frame H r b) := by
    intro a b
    simp only [Matrix.mul_apply, form, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum,
      mul_assoc]
    exact Finset.sum_comm
  have hskew : ∀ u v : Fin n → E, form σ Y.J u v = -σ (form σ Y.J v u) := by
    intro u v
    simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsk]; ring
  have hcol : ∀ k : Fin n₁, (fun r => H.ι r k) = H.ι *ᵥ Pi.single k 1 := by
    intro k; ext r; simp [mulVec, dotProduct, Pi.single_apply]
  have hGs : ∀ a b, blk n₁ a + blk n₁ b ≠ 2 → ((frame H)ᵀ * Y.J * (frame H).map σ) a b = 0 := by
    intro a b hab
    rw [hGf]
    rcases blk_cases a with ⟨a, rfl⟩ | ⟨k, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases blk_cases b with ⟨b, rfl⟩ | ⟨l, rfl⟩ | ⟨b, rfl⟩ <;>
      simp only [block_matrix_mulVec_basis, blk_mid, blk_y, frame_alt, frame_mid, frame_y] at hab ⊢
    · exact hxx
    · rw [hcol, hskew, (horth _).1, map_zero, neg_zero]
    · exact absurd rfl hab
    · rw [hcol]; exact (horth _).1
    · exact absurd rfl hab
    · rw [hcol]; exact (horth _).2
    · exact absurd rfl hab
    · rw [hcol, hskew, (horth _).2, map_zero, neg_zero]
    · exact hyy

  have hA'e : ∀ a b, (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) a b =
      τ c * star (τ (((frame H)ᵀ * Y.J * (frame H).map σ) a b)) := by
    intro a b
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      transpose_apply, map_mul, map_sum, h.2.2.2, star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  have hA's : ∀ a b, blk n₁ a + blk n₁ b ≠ 2 →
      (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) a b = 0 := by
    intro a b hab
    rw [hA'e, hGs a b hab, map_zero, star_zero, mul_zero]
  have hAB : (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) *
      (R.map τ * ((c • Y.J.map σ).map τ)⁻¹ * (R.map τ)ᴴ) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((frame H).map τ) (R.map τ), hQR', Matrix.one_mul,
      ← Matrix.mul_assoc ((c • Y.J.map σ).map τ), Matrix.mul_nonsing_inv _ hAu, Matrix.one_mul, ← conjTranspose_mul,
      hRQ', conjTranspose_one]
  have hB's := blk_support_of_mul_eq_one hA's hAB
  have hcancel : ∀ {p : Type} (M : Matrix (Fin n) p ℂ), (R.map τ)ᴴ * (((frame H).map τ)ᴴ * M) = M := by
    intro p M
    rw [← Matrix.mul_assoc, ← conjTranspose_mul, hQR', conjTranspose_one, Matrix.one_mul]
  have hid : R.map τ * adj ((c • Y.J.map σ).map τ) X * (frame H).map τ =
      (R.map τ * ((c • Y.J.map σ).map τ)⁻¹ * (R.map τ)ᴴ) * (R.map τ * X * (frame H).map τ)ᴴ *
        (((frame H).map τ)ᴴ * (c • Y.J.map σ).map τ * (frame H).map τ) := by
    simp only [adj, conjTranspose_mul, Matrix.mul_assoc, hcancel]
  rw [hid, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h1 : blk n₁ i + blk n₁ k = 2
  · by_cases h2 : blk n₁ l + blk n₁ j = 2
    · rw [conjTranspose_apply, hX l k (by omega), star_zero, mul_zero, zero_mul]
    · rw [hA's l j h2, mul_zero]
  · rw [hB's i k h1, zero_mul, zero_mul]

end GlobalTheory.LeviHC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormsTransportToOrthonormalChartOriginStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviForms_transport_to_orthonormal_chart_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 x1 b : Frame X.Ψ r) (z : V (nd X)), IsOrth X x1 → z ∈ OmF X x0 → b ∈ Bor X.Ψ r → cpt X x0 z = rmul x1 b → ∀ ξ : Fin (nd X) → ℂ, ∃ ξ' : Fin (nd X) → ℂ, (∀ la : Wt X.Ψ r, leviM X (phla X la) x0 z ξ = leviM X (phla X la) x1 0 ξ') ∧ ∃ B : Frame X.Ψ r, (∀ τ (a c : Fin r), c < a → B τ a c = 0) ∧ ∀ τ, mat x0 τ * (mat (nmat X (WithLp.toLp 2 ξ)) τ - 1) = mat x1 τ * ((mat (nmat X (WithLp.toLp 2 ξ')) τ - 1) * mat b τ + mat B τ) := by
  first | exact @GlobalTheory.LeviWeightChart.levi_transport_origin | exact GlobalTheory.LeviWeightChart.levi_transport_origin | (intros; apply GlobalTheory.LeviWeightChart.levi_transport_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMarginOrthonormalChartOriginStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviMargin_orthonormal_chart_origin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x : Frame X.Ψ r) (g bb : ℝ), 0 < X.p0 → X.p0 < r → IsOrth X x → 0 ≤ g → 0 ≤ bb → (∀ τ (a b : Fin r), (b : ℕ) = a + 1 → (b : ℕ) ≠ X.p0 → g ≤ (la τ a : ℝ) - la τ b) → (∀ τ (a b : Fin r), (a : ℕ) = 0 → (b : ℕ) = r - 1 → g ≤ (la τ b : ℝ) - la τ a) → ∀ ξ : Fin (nd X) → ℂ, (g - bb - 2 * r) * ∑ j, ‖ξ j‖ ^ 2 ≤ leviM X (phla X la) x 0 ξ - bb * leviM X (phla X (GlobalTheory.CurvMargin.blockWt X)) x 0 ξ - leviM X (phla X (kapW X)) x 0 ξ := by
  first | exact @GlobalTheory.LeviOriginMargin.levi_margin_origin | exact GlobalTheory.LeviOriginMargin.levi_margin_origin | (intros; apply GlobalTheory.LeviOriginMargin.levi_margin_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviNormalizesUnipotentBis
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

namespace GlobalTheory.LeviHC

theorem levi_conj_mem_unip : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (h₁ : UA σ Y₁.J) (m : UA σ Y.J),
    IsLevi (W₁ := Y₁) H 1 h₁ m → ∀ u ∈ unip σ Y H, m * u * m⁻¹ ∈ unip σ Y H := by
  intro F E _ _ _ _ _ σ n n₁ Y Y₁ H h₁ m hm
  obtain ⟨hx, -, hι⟩ := hm
  have hx' : mat m *ᵥ incV F H.x = incV F H.x := by simpa using hx
  have hxi : mat m⁻¹ *ᵥ incV F H.x = incV F H.x := by
    conv_lhs => rw [← hx']
    rw [Matrix.mulVec_mulVec, FlagPar.mat_inv_mul, Matrix.one_mulVec]
  have hh : mat h₁ * mat h₁⁻¹ = 1 := by rw [← FlagPar.mat_mul, mul_inv_cancel, FlagPar.mat_one]
  have hιi : mat m⁻¹ * incM F H.ι = incM F H.ι * mat h₁⁻¹ := by
    calc mat m⁻¹ * incM F H.ι = mat m⁻¹ * (incM F H.ι * mat h₁) * mat h₁⁻¹ := by
          rw [Matrix.mul_assoc (mat m⁻¹), Matrix.mul_assoc (incM F H.ι), hh, Matrix.mul_one]
      _ = incM F H.ι * mat h₁⁻¹ := by rw [← hι, ← Matrix.mul_assoc, FlagPar.mat_inv_mul, Matrix.one_mul]
  intro u hu
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
    obtain ⟨h1, h2⟩ := hu
    apply Subgroup.subset_closure
    refine ⟨?_, fun z => ?_⟩
    · rw [FlagPar.mat_mul, FlagPar.mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxi, h1, hx']
    · obtain ⟨a, ha⟩ := h2 (mat h₁⁻¹ *ᵥ z)
      refine ⟨a, ?_⟩
      have e1 : mat m⁻¹ *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat h₁⁻¹ *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, hιi, ← Matrix.mulVec_mulVec]
      have e2 : mat m *ᵥ (incM F H.ι *ᵥ (mat h₁⁻¹ *ᵥ z)) = incM F H.ι *ᵥ z := by
        rw [Matrix.mulVec_mulVec, hι, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec z (mat h₁), hh, Matrix.one_mulVec]
      rw [FlagPar.mat_mul, FlagPar.mat_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, ha, Matrix.mulVec_add,
        Matrix.mulVec_smul, hx', e2]
  | one => simp
  | mul x y _ _ hx hy =>
    have := mul_mem hx hy
    simpa [mul_assoc] using this
  | inv x _ hx =>
    have := inv_mem hx
    simpa [mul_assoc] using this

end GlobalTheory.LeviHC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrintsStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieSecond_of_prints_derEx_fockEx_vacLine_lieScalar : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := by
  first | exact @GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar | exact GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar | (intros; apply GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar <;> assumption)
end

