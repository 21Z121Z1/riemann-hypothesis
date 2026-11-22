import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.ExistsHarrisTaylorObjectOfLevelLift

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsSkewOfDiagonal
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.CommonTransversal

theorem exists_skew_isUnit_det {F : Type} [Field F] (σ : F →+* F) {β : Type} [Fintype β]
    [DecidableEq β] (a b : Matrix β β F) (hσ : ∀ z, σ (σ z) = z) (hz : ∃ z, σ z ≠ z)
    (h : a * (b.map σ)ᵀ + b * (a.map σ)ᵀ = 0)
    (hv : ∀ v : β → F, Matrix.vecMul v a = 0 → Matrix.vecMul v b = 0 → v = 0) :
    ∃ s : Matrix β β F, (s.map σ)ᵀ = -s ∧ IsUnit (a + b * s).det := by
  classical
  obtain ⟨L, L', D, hD⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec a
  obtain ⟨P, hP⟩ : ∃ P, P = (L.map Matrix.TransvectionStruct.toMatrix).prod := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (L'.map Matrix.TransvectionStruct.toMatrix).prod := ⟨_, rfl⟩
  rw [← hP, ← hQ] at hD
  have hP1 : P.det = 1 := by rw [hP]; exact Matrix.TransvectionStruct.det_toMatrix_prod L
  have hQ1 : Q.det = 1 := by rw [hQ]; exact Matrix.TransvectionStruct.det_toMatrix_prod L'
  have hst1 : ∀ M : Matrix β β F, M.det = 1 → ((M.map σ)ᵀ).det = 1 := by
    intro M hM
    rw [Matrix.det_transpose]
    have e : (M.map σ).det = σ M.det := (RingHom.map_det σ M).symm
    rw [e, hM, map_one]
  have cancel : ∀ (M : Matrix β β F) (x : β → F), M.det = 1 → x ᵥ* M = 0 → x = 0 := by
    intro M x hM hx
    have hu : IsUnit M.det := by rw [hM]; exact isUnit_one
    calc x = x ᵥ* (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv (A := M) hu, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, hx, Matrix.zero_vecMul]
  obtain ⟨z, hz⟩ := hz
  obtain ⟨c, hcdef⟩ : ∃ c, c = z - σ z := ⟨_, rfl⟩
  have hc : c ≠ 0 := by rw [hcdef]; exact sub_ne_zero.2 (Ne.symm hz)
  have hσc : σ c = -c := by rw [hcdef, map_sub, hσ]; ring
  obtain ⟨s0, hs0⟩ : ∃ s0 : Matrix β β F, s0 = diagonal (fun i => if D i = 0 then c else 0) :=
    ⟨_, rfl⟩
  have hss : (s0.map σ)ᵀ = -s0 := by
    rw [hs0, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.diagonal_neg]
    congr 1
    funext i
    split_ifs <;> simp [hσc]
  have hQQ : ((((Q.map σ)ᵀ).map σ)ᵀ) = Q := by
    ext i j
    simp [hσ]
  have hsta : (a.map σ)ᵀ = (Q.map σ)ᵀ * diagonal (fun i => σ (D i)) * (P.map σ)ᵀ := by
    rw [hD, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_assoc]
  refine ⟨(Q.map σ)ᵀ * s0 * Q, ?_, ?_⟩
  · rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hss, hQQ,
      Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc]
  · rw [isUnit_iff_ne_zero]
    intro hdet
    obtain ⟨v, hv0, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    apply hv0
    have e1 : a + b * ((Q.map σ)ᵀ * s0 * Q) = (P * diagonal D + b * (Q.map σ)ᵀ * s0) * Q := by
      rw [hD]
      simp only [Matrix.add_mul, Matrix.mul_assoc]
    have h0 : v ᵥ* (P * diagonal D + b * (Q.map σ)ᵀ * s0) = 0 :=
      cancel Q _ hQ1 (by rw [Matrix.vecMul_vecMul, ← e1]; exact hvM)
    have h0' : (v ᵥ* P) ᵥ* diagonal D + ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* s0 = 0 := by
      simpa only [Matrix.vecMul_vecMul, Matrix.vecMul_add] using h0
    have hE : ∀ j, (v ᵥ* P) j * D j +
        ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) j * (if D j = 0 then c else 0) = 0 := by
      intro j
      have e := congr_fun h0' j
      rw [Pi.add_apply, Matrix.vecMul_diagonal, hs0, Matrix.vecMul_diagonal] at e
      exact e
    have hwD : (v ᵥ* P) ᵥ* diagonal D = 0 := by
      funext j
      rw [Matrix.vecMul_diagonal, Pi.zero_apply]
      by_cases hDj : D j = 0
      · rw [hDj, mul_zero]
      · have e := hE j
        rw [if_neg hDj, mul_zero, add_zero] at e
        rw [(mul_eq_zero.1 e).resolve_right hDj, zero_mul]
    have hva : v ᵥ* a = 0 := by
      rw [hD, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hwD, Matrix.zero_vecMul]
    have hc1 : v ᵥ* (a * (b.map σ)ᵀ + b * (a.map σ)ᵀ) = 0 := by rw [h, Matrix.vecMul_zero]
    rw [Matrix.vecMul_add, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hva, Matrix.zero_vecMul,
      zero_add, hsta, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul] at hc1
    have hud : ((v ᵥ* b) ᵥ* (Q.map σ)ᵀ) ᵥ* diagonal (fun i => σ (D i)) = 0 :=
      cancel _ _ (hst1 P hP1) hc1
    have hu : (v ᵥ* b) ᵥ* (Q.map σ)ᵀ = 0 := by
      funext j
      rw [Pi.zero_apply]
      by_cases hDj : D j = 0
      · have e := hE j
        rw [if_pos hDj, hDj, mul_zero, zero_add] at e
        exact (mul_eq_zero.1 e).resolve_right hc
      · have e := congr_fun hud j
        rw [Matrix.vecMul_diagonal, Pi.zero_apply] at e
        exact (mul_eq_zero.1 e).resolve_right ((map_ne_zero σ).2 hDj)
    exact hv v hva (cancel _ _ (hst1 Q hQ1) hu)

end GlobalTheory.CompanionTheory.CommonTransversal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.NormIteratedFDerivCexpCompLe
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Complex GlobalTheory.CompanionTheory.OM GlobalTheory.WeilM
open scoped ContDiff Nat

namespace GlobalTheory.CompanionTheory.OM

namespace GaussSch

theorem one_add_pow_mul_exp_le {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (N : ℕ) :
    (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ Real.exp (N ^ 2 / (4 * c)) := by
  have h1 : (1 + r) ^ N ≤ Real.exp r ^ N :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp r]) N
  calc (1 + r) ^ N * Real.exp (-c * r ^ 2) ≤ Real.exp r ^ N * Real.exp (-c * r ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (N * r + -c * r ^ 2) := by rw [← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ Real.exp (N ^ 2 / (4 * c)) := by
        apply Real.exp_le_exp.2
        rw [le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg ((N : ℝ) - 2 * c * r)]

theorem norm_iteratedFDeriv_cexp (i : ℕ) (y : ℂ) :
    ‖iteratedFDeriv ℝ i cexp y‖ = Real.exp y.re := by
  rw [← ((Complex.contDiff_exp : ContDiff ℂ (i : WithTop ℕ∞) cexp).contDiffAt (x := y)).restrictScalars_iteratedFDeriv (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, Complex.iter_deriv_exp,
    Complex.norm_exp]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_cexp_comp_le {q : E → ℂ} (hq : q.HasTemperateGrowth) (n : ℕ) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ x : E, ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖ ≤
      C * (1 + ‖x‖) ^ k * Real.exp (q x).re := by
  obtain ⟨m, K, hK, hbd⟩ := hq.norm_iteratedFDeriv_le_uniform n
  refine ⟨n ! * (max K 1) ^ n, m * n, by positivity, fun x ↦ ?_⟩
  have h1x : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hD1 : 1 ≤ max K 1 * (1 + ‖x‖) ^ m :=
    one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ h1x)
  have hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i q x‖ ≤ (max K 1 * (1 + ‖x‖) ^ m) ^ i := by
    intro i hi hin
    calc ‖iteratedFDeriv ℝ i q x‖ ≤ K * (1 + ‖x‖) ^ m := hbd i hin x
      _ ≤ max K 1 * (1 + ‖x‖) ^ m := by gcongr; exact le_max_left _ _
      _ = (max K 1 * (1 + ‖x‖) ^ m) ^ 1 := (pow_one _).symm
      _ ≤ (max K 1 * (1 + ‖x‖) ^ m) ^ i := pow_le_pow_right₀ hD1 hi
  have hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i cexp (q x)‖ ≤ Real.exp (q x).re :=
    fun i _ => (norm_iteratedFDeriv_cexp i (q x)).le
  calc ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖
      ≤ n ! * Real.exp (q x).re * (max K 1 * (1 + ‖x‖) ^ m) ^ n :=
        norm_iteratedFDeriv_comp_le (N := n) Complex.contDiff_exp (hq.1.of_le (mod_cast le_top))
          le_rfl x hC hD
    _ = n ! * (max K 1) ^ n * (1 + ‖x‖) ^ (m * n) * Real.exp (q x).re := by
        rw [mul_pow, ← pow_mul]; ring

def cexpSchwartz {q : E → ℂ} (hq : q.HasTemperateGrowth) {c : ℝ} (hc : 0 < c)
    (hre : ∀ x, (q x).re ≤ -c * ‖x‖ ^ 2) : SchwartzMap E ℂ where
  toFun := cexp ∘ q
  smooth' := Complex.contDiff_exp.comp hq.1
  decay' k n := by
    obtain ⟨C, j, hC, hb⟩ := norm_iteratedFDeriv_cexp_comp_le hq n
    refine ⟨C * Real.exp ((k + j : ℕ) ^ 2 / (4 * c)), fun x ↦ ?_⟩
    have hk : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
    have he : Real.exp (q x).re ≤ Real.exp (-c * ‖x‖ ^ 2) := Real.exp_le_exp.2 (hre x)
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (cexp ∘ q) x‖
        ≤ (1 + ‖x‖) ^ k * (C * (1 + ‖x‖) ^ j * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul hk ((hb x).trans (by gcongr)) (norm_nonneg _) (by positivity)
      _ = C * ((1 + ‖x‖) ^ (k + j) * Real.exp (-c * ‖x‖ ^ 2)) := by rw [pow_add]; ring
      _ ≤ C * Real.exp ((k + j : ℕ) ^ 2 / (4 * c)) :=
          mul_le_mul_of_nonneg_left (one_add_pow_mul_exp_le hc (norm_nonneg x) _) hC

variable {κ : Type} [Fintype κ]

end GaussSch

end GlobalTheory.CompanionTheory.OM

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MembershipProofs.SchrodingerModelSelfDualLattice
section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.CosetMod

theorem sum_out {G : Type} [AddCommGroup G] (H : AddSubgroup G) [Fintype (G ⧸ H)] (χ : AddChar G ℂ)
    (hχ : ∀ h ∈ H, χ h = 1) :
    ((∀ g, χ g = 1) → ∑ q : G ⧸ H, χ q.out = Fintype.card (G ⧸ H)) ∧
      (¬ (∀ g, χ g = 1) → ∑ q : G ⧸ H, χ q.out = 0) := by
  have hcoset : ∀ a b : G, (a : G ⧸ H) = b → χ a = χ b := by
    intro a b hab
    have hmem : -a + b ∈ H := QuotientAddGroup.eq.mp hab
    calc χ a = χ a * χ (-a + b) := by rw [hχ _ hmem, mul_one]
      _ = χ b := by rw [← AddChar.map_add_eq_mul, add_neg_cancel_left]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp [h]
  · push_neg at h
    obtain ⟨g, hg⟩ := h
    have hshift : ∀ q : G ⧸ H, χ g * χ q.out = χ ((QuotientAddGroup.mk g + q).out) := by
      intro q
      rw [← AddChar.map_add_eq_mul]
      apply hcoset
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
    have key : χ g * ∑ q : G ⧸ H, χ q.out = ∑ q : G ⧸ H, χ q.out := by
      rw [Finset.mul_sum]
      simp_rw [hshift]
      exact Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk g)) _ _ (fun q => rfl)
    have h0 : (χ g - 1) * ∑ q : G ⧸ H, χ q.out = 0 := by rw [sub_mul, key, one_mul, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hg
    · exact h1

private theorem addChar_sum_eq_one_of_forall {R ι : Type} [CommRing R] (ψ : AddChar R ℂ) (s : Finset ι) (f : ι → R)
    (h : ∀ i ∈ s, ψ (f i) = 1) : ψ (∑ i ∈ s, f i) = 1 := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro a s ha ih h
  rw [Finset.sum_insert ha, AddChar.map_add_eq_mul, h a (Finset.mem_insert_self a s),
    ih (fun i hi => h i (Finset.mem_insert_of_mem hi)), one_mul]

theorem indicator_mem_span : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {κ : Type} [Fintype κ] (v : Rˣ), GoodChar ψ O u → (v : R) ∈ O → (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) ∈ Submodule.span ℂ {f : (κ → R) → ℂ | ∃ y : κ → R, f = schr ψ (0, y) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ))} := by
  intro R _ _ _ _ _ _ ψ O u κ _ v hG hv
  classical
  let L : AddSubgroup (κ → R) := AddSubgroup.pi Set.univ (fun _ => O.toAddSubgroup)
  have memL : ∀ y : κ → R, y ∈ L ↔ ∀ i, y i ∈ O := by
    intro y; simp [L, AddSubgroup.mem_pi]
  let Gs : AddSubgroup (κ → R) :=
    L.comap (DistribMulAction.toAddMonoidHom (κ → R) (((u⁻¹ * v : Rˣ)) : R))
  let Hs : AddSubgroup (κ → R) :=
    L.comap (DistribMulAction.toAddMonoidHom (κ → R) (((u⁻¹ : Rˣ)) : R))
  have memG : ∀ y : κ → R, y ∈ Gs ↔ ∀ i, (((u⁻¹ * v : Rˣ)) : R) * y i ∈ O := by
    intro y; simp only [Gs, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, memL,
      Pi.smul_apply, smul_eq_mul]
  have memH : ∀ y : κ → R, y ∈ Hs ↔ ∀ i, (((u⁻¹ : Rˣ)) : R) * y i ∈ O := by
    intro y; simp only [Hs, AddSubgroup.mem_comap, DistribMulAction.toAddMonoidHom_apply, memL,
      Pi.smul_apply, smul_eq_mul]
  have hLset : (L : Set (κ → R)) = Set.univ.pi (fun _ => (O : Set R)) := by
    ext y; simp [memL]
  have hLopen : IsOpen (L : Set (κ → R)) := by
    rw [hLset]; exact isOpen_set_pi Set.finite_univ (fun _ _ => hG.isOpen)
  have hLcpt : IsCompact (L : Set (κ → R)) := by
    rw [hLset]; exact isCompact_univ_pi (fun _ => hG.compact)
  have hGset : (Gs : Set (κ → R)) =
      (fun y : κ → R => ((((u⁻¹ * v : Rˣ))⁻¹ : Rˣ) : R) • y) '' (L : Set (κ → R)) := by
    ext y
    constructor
    · intro hy
      refine ⟨(((u⁻¹ * v : Rˣ)) : R) • y, hy, ?_⟩
      simp only [smul_smul, Units.inv_mul, one_smul]
    · rintro ⟨z, hz, rfl⟩
      show (((u⁻¹ * v : Rˣ)) : R) • ((((u⁻¹ * v : Rˣ))⁻¹ : Rˣ) : R) • z ∈ L
      rw [smul_smul, Units.mul_inv, one_smul]; exact hz
  have hGcpt : IsCompact (Gs : Set (κ → R)) := by
    rw [hGset]; exact hLcpt.image (continuous_const_smul _)
  have hHopen : IsOpen (Hs : Set (κ → R)) :=
    hLopen.preimage (continuous_const_smul (((u⁻¹ : Rˣ)) : R))
  let H : AddSubgroup Gs := Hs.addSubgroupOf Gs
  have hHopen' : IsOpen (H : Set Gs) := hHopen.preimage continuous_subtype_val
  haveI : CompactSpace Gs := isCompact_iff_compactSpace.mp hGcpt
  haveI : Finite (Gs ⧸ H) := AddSubgroup.quotient_finite_of_isOpen H hHopen'
  letI : Fintype (Gs ⧸ H) := Fintype.ofFinite _
  have hfun : (Set.indicator {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} fun _ => (1 : ℂ)) =
      ∑ q : Gs ⧸ H, ((Fintype.card (Gs ⧸ H) : ℂ)⁻¹) •
        schr ψ (0, ((q.out : Gs) : κ → R)) (Set.indicator {x : κ → R | ∀ i, x i ∈ O} fun _ => (1 : ℂ)) := by
    funext x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.WeilM.schr, zero_dotProduct, mul_zero, add_zero]
    by_cases hx : ∀ i, x i ∈ O
    · let χx : AddChar Gs ℂ :=
        { toFun := fun y => ψ (x ⬝ᵥ (y : κ → R))
          map_zero_eq_one' := by simp
          map_add_eq_mul' := by intro a b; simp [dotProduct_add, AddChar.map_add_eq_mul] }
      have hχ : ∀ h ∈ H, χx h = 1 := by
        intro h hh
        have hh' : ((h : Gs) : κ → R) ∈ Hs := AddSubgroup.mem_addSubgroupOf.mp hh
        show ψ (x ⬝ᵥ ((h : Gs) : κ → R)) = 1
        apply addChar_sum_eq_one_of_forall
        intro i _
        have h1 := (hG.ann _).mpr ((memH _).mp hh' i) (x i) (hx i)
        rwa [mul_comm] at h1
      obtain ⟨hA, hB⟩ := sum_out H χx hχ
      have hrw : ∀ q : Gs ⧸ H, (Fintype.card (Gs ⧸ H) : ℂ)⁻¹ *
          (ψ (x ⬝ᵥ ((q.out : Gs) : κ → R)) *
            Set.indicator {x : κ → R | ∀ i, x i ∈ O} (fun _ => (1 : ℂ)) x) =
          (Fintype.card (Gs ⧸ H) : ℂ)⁻¹ * χx q.out := by
        intro q
        simp only [Set.indicator_of_mem (show x ∈ {x : κ → R | ∀ i, x i ∈ O} from hx), mul_one]
        rfl
      rw [Finset.sum_congr rfl (fun q _ => hrw q), ← Finset.mul_sum]
      by_cases hs : ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O
      · have htriv : ∀ g, χx g = 1 := by
          intro g
          show ψ (x ⬝ᵥ ((g : Gs) : κ → R)) = 1
          apply addChar_sum_eq_one_of_forall
          intro i _
          have hg := (memG _).mp g.2 i
          have hz : ((u⁻¹ : Rˣ) : R) * ((v : R) * (g : κ → R) i) ∈ O := by
            rw [← mul_assoc, ← Units.val_mul]; exact hg
          have h1 := (hG.ann _).mpr hz _ (hs i)
          have e : (v : R) * (g : κ → R) i * (((v⁻¹ : Rˣ) : R) * x i) = x i * (g : κ → R) i := by
            rw [mul_comm (v : R) ((g : κ → R) i), mul_assoc, Units.mul_inv_cancel_left, mul_comm]
          rwa [e] at h1
        rw [hA htriv, Set.indicator_of_mem (show x ∈ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]
        exact (inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm
      · have hnt : ¬ ∀ g, χx g = 1 := by
          push_neg at hs
          obtain ⟨i, hi⟩ := hs
          have hz : ¬ ((u⁻¹ : Rˣ) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * x i) ∈ O := by
            have e : ((u⁻¹ : Rˣ) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * x i) = ((v⁻¹ : Rˣ) : R) * x i := by
              rw [mul_comm (((v⁻¹ : Rˣ) : R)) (u : R), mul_assoc (u : R), Units.inv_mul_cancel_left]
            rw [e]; exact hi
          rw [← hG.ann] at hz
          push_neg at hz
          obtain ⟨y, hy, hψ⟩ := hz
          intro hall
          have hmem : (Pi.single i (((v⁻¹ : Rˣ) : R) * (u : R) * y) : κ → R) ∈ Gs := by
            rw [memG]
            intro j
            by_cases hj : j = i
            · subst hj
              simp only [Pi.single_eq_same]
              have e : (((u⁻¹ * v : Rˣ)) : R) * (((v⁻¹ : Rˣ) : R) * (u : R) * y) = y := by
                rw [Units.val_mul, mul_assoc, ← mul_assoc (v : R), ← mul_assoc (v : R),
                  Units.mul_inv, one_mul, Units.inv_mul_cancel_left]
              rw [e]; exact hy
            · simp only [Pi.single_eq_of_ne hj, mul_zero]; exact O.zero_mem
          have h1 := hall ⟨_, hmem⟩
          apply hψ
          have e2 : x ⬝ᵥ (Pi.single i (((v⁻¹ : Rˣ) : R) * (u : R) * y) : κ → R) =
              ((v⁻¹ : Rˣ) : R) * (u : R) * x i * y := by
            rw [dotProduct_single]; ring
          rw [← e2]; exact h1
        rw [hB hnt, mul_zero, Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]
    · have hs : ¬ ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O := by
        intro h
        apply hx
        intro i
        have := O.mul_mem hv (h i)
        rwa [Units.mul_inv_cancel_left] at this
      rw [Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, ((v⁻¹ : Rˣ) : R) * x i ∈ O} from hs)]
      symm
      apply Finset.sum_eq_zero
      intro q _
      rw [Set.indicator_of_notMem (show x ∉ {x : κ → R | ∀ i, x i ∈ O} from hx), mul_zero, mul_zero]
  rw [hfun]
  exact Submodule.sum_mem _ (fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

end GlobalTheory.CompanionTheory.CosetMod
end

