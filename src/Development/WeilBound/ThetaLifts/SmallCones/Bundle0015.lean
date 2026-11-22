import Development.WeilBound.ThetaLifts.SmallCones.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0893
import Development.WeilBound.ThetaLifts.SmallCones.IdeleTop
import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq
import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.SoStatement

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.NormLeSum
section
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField.mixedEmbedding
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.HeisSchA PositivityTheory.ThKCT.Arch PositivityTheory.ThKCT.Ad

namespace Ad

variable {F : Type} [Field F] [NumberField F] {κ κ₁ : Type} [Fintype κ] [Fintype κ₁]

theorem norm_le_sum (x : mixedSpace F) : ‖x‖ ≤ ∑ w : InfinitePlace F, normAtPlace w x := by
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.sup'_le _ _ fun w hw => Finset.single_le_sum (fun v _ => normAtPlace_nonneg v x) hw

theorem sum_le_norm (x : mixedSpace F) : ∑ w : InfinitePlace F, normAtPlace w x ≤ Fintype.card (InfinitePlace F) * ‖x‖ := by
  rw [← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun w hw => ?_
  rw [norm_eq_sup'_normAtPlace]
  exact Finset.le_sup' (fun w => normAtPlace w x) hw

set_option maxHeartbeats 800000 in
theorem slice_core {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ)
    (ei : SInf F κ →L[ℂ] SInf F κ₁) (ef : ((κ → Af F) → ℂ) → (κ₁ → Af F) → ℂ) (h0 : ei ≠ 0)
    (he : ∀ φ ∈ SB (κ → Af F), ef φ ∈ SB _ ∧ ∀ f : SInf F κ, e (pureA F f φ) = pureA F (ei f) (ef φ))
    {m : ℕ} (c ζ : Fin m → (κ → AF F) × (κ → AF F)) (hinv : ∀ j (a : AF F), ∀ Φ ∈ schA F κ, e (schr ψ (a • ζ j) Φ) = e Φ)
    (hp : ∀ i j, (ζ i).1 ⬝ᵥ (c j).2 - (c j).1 ⬝ᵥ (ζ i).2 = if i = j then 1 else 0) {φ : (κ → Af F) → ℂ} (hφ : φ ∈ SB _) :
    ∃ (r : ℕ) (φ₁ : Fin r → (κ₁ → Af F) → ℂ) (C : Set (Fin m → Af F))
      (A : Fin r → (Fin m → AF F) → SInf F κ →L[ℂ] SInf F κ₁),
      (∀ i, φ₁ i ∈ SB _) ∧ IsCompact C ∧ (∀ i f, Continuous fun y => A i y f) ∧
      (∀ y (f : SInf F κ), e (schr ψ (∑ j, y j • c j) (pureA F f φ)) = ∑ i, pureA F (A i y f) (φ₁ i)) ∧
      (∀ i y, (fun j => (y j).2) ∉ C → A i y = 0) ∧
      ∀ (q : Seminorm ℂ (SInf F κ₁)) (N : ℕ), Continuous q → ∃ p : Seminorm ℂ (SInf F κ),
        Continuous p ∧ ∀ i y f, q (A i y f) * (1 + ∑ j, ∑ w : InfinitePlace F, normAtPlace w (evI F (y j))) ^ N ≤ p f := by
  have key : ∀ (y : Fin m → AF F) j (a : AF F), ∀ Φ ∈ schA F κ,
      e (schr ψ (∑ i, y i • c i) (schr ψ (a • ζ j) Φ)) = ψ (-(a * y j)) • e (schr ψ (∑ i, y i • c i) Φ) := fun y j a Φ hΦ => by
    rw [schr_comm, map_smul, hinv _ _ _ (schr_mem_schA ψ hψ _ _ hΦ)]
    congr 2
    have : a * y j = ∑ i, a * y i * ((ζ j).1 ⬝ᵥ (c i).2 - (c i).1 ⬝ᵥ (ζ j).2) := by simp [hp]
    rw [this]
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd, sum_dotProduct, dotProduct_sum, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  let wy : (Fin m → AF F) → _ := fun y => aw0 F κ (∑ j, qI F (y j) • ev2 (c j))
  let T : (Fin m → AF F) → SInf F κ →L[ℂ] SInf F κ₁ := fun y => ei.comp (S (wy y))
  let G : (Fin m → Af F) → (κ₁ → Af F) → ℂ := fun b => ef (fw ψ (∑ j, b j • fn2 (c j)) φ)
  have main : ∀ y (f : SInf F κ), e (schr ψ (∑ j, y j • c j) (pureA F f φ)) = pureA F (T y f) (G fun j => p2 (y j)) :=
    fun y f => by rw [schr_pure hψ, (he _ (fw_mem hψ _ hφ)).2, pairEvaluation_linear_combination, pairFunctional_linear_combination]; rfl
  have hG : IsLocallyConstant G := ((fw_lc hψ hφ).comp_continuous (f := fun b : Fin m → Af F => ∑ j, b j • fn2 (c j))
    (continuous_finsetSum _ fun j _ => (continuous_apply j).smul continuous_const)).comp ef
  have hGm : ∀ b, G b ∈ SB _ := fun b => (he _ (fw_mem hψ _ hφ)).1
  obtain ⟨C, hC, hC'⟩ : ∃ C : Set (Fin m → Af F), IsCompact C ∧ ∀ b, G b ≠ 0 → b ∈ C := by
    have hU : ∀ᶠ a : Af F in 𝓝 0, ∀ j, fw ψ (a • fn2 (ζ j)) φ = φ := eventually_all.2 fun j => by
      have := ((fw_lc hψ hφ).comp_continuous (f := fun a : Af F => a • fn2 (ζ j))
        (continuous_id.smul continuous_const)).eventually_eq 0
      simpa only [Function.comp_apply, zero_smul, fw_zero] using this
    obtain ⟨C₀, h₀, h₀'⟩ := annih hψ hU
    refine ⟨Set.pi Set.univ fun _ => -C₀, isCompact_univ_pi fun _ => h₀.neg, fun b hb j _ => h₀' _ fun a ha => ?_⟩
    obtain ⟨f₀, hf₀⟩ : ∃ f₀, ei f₀ ≠ 0 := by
      by_contra! h
      exact h0 (ContinuousLinearMap.ext h)
    let y : Fin m → AF F := fun j => pt 0 (b j)
    have h1 := key y j (pt 0 a) _ (pureA_mem (S (-wy y) f₀) hφ)
    rw [schr_pure hψ (pt 0 a • ζ j), pairEvaluation_smul, pairFunctional_smul, qI_pt, finite_projection_mixed_point, ha j, zero_smul, map_zero, S_zero, main,
      ← pureA_smul_left] at h1
    have h2 := pureA_cancel hb h1
    rw [show T y (S (-wy y) f₀) = ei f₀ from congrArg ei (S_neg _ _)] at h2
    have h3 : ψ (-(pt 0 a * y j)) = 1 := by
      by_contra h
      exact hf₀ ((smul_eq_zero.1 (show (ψ (-(pt 0 a * y j)) - 1) • ei f₀ = 0 by
        rw [sub_smul, one_smul, ← h2, sub_self])).resolve_left (sub_ne_zero.2 h))
    rw [psi_eq hψ, map_neg, map_mul, qI_pt, zero_mul, neg_zero, map_zero, map_neg, map_mul, finite_projection_mixed_point, finite_projection_mixed_point] at h3
    simpa using h3
  have hfin : (G '' C \ {0}).Finite := by
    haveI := isCompact_iff_compactSpace.1 hC
    have := (hG.comp_continuous (continuous_subtype_val : Continuous ((↑) : C → _))).range_finite
    rw [Set.range_comp, Subtype.range_coe] at this
    exact this.diff
  let φ₁ : Fin hfin.toFinset.card → (κ₁ → Af F) → ℂ := fun i => (hfin.toFinset.equivFin.symm i).1
  have hφ₁ : ∀ i, φ₁ i ∈ G '' C \ {0} := fun i => hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm i).2
  let A : Fin hfin.toFinset.card → (Fin m → AF F) → SInf F κ →L[ℂ] SInf F κ₁ := fun i y =>
    if G (fun j => p2 (y j)) = φ₁ i then T y else 0
  have z0 : ∀ g : (κ₁ → Af F) → ℂ, pureA F (0 : SInf F κ₁) g = 0 := fun g => funext fun x => zero_mul _
  obtain ⟨K₁, hK₁, hK₁'⟩ := (LinearMap.toContinuousLinearMap (aw0 F κ)).bound
  refine ⟨_, φ₁, C, A, fun i => by obtain ⟨b, -, hb⟩ := (hφ₁ i).1; exact hb ▸ hGm b, hC, fun i f => ?_, fun y f => ?_,
    fun i y hy => if_neg fun h : G (fun j => p2 (y j)) = φ₁ i => hy (hC' _ fun h' => (hφ₁ i).2 (h.symm.trans h')), fun q N hq => ?_⟩
  · have h1 : IsLocallyConstant fun y : Fin m → AF F => if G (fun j => p2 (y j)) = φ₁ i then (1 : ℂ) else 0 :=
      (hG.comp_continuous (f := fun (y : Fin m → AF F) j => p2 (y j))
        (continuous_pi fun j => continuous_snd.comp (continuous_apply j))).comp fun g => if g = φ₁ i then (1 : ℂ) else 0
    have h2 : Continuous wy := (aw0 F κ).continuous_of_finiteDimensional.comp
      (continuous_finsetSum _ fun j _ => Continuous.smul (f := fun y : Fin m → AF F => qI F (y j))
        (continuous_qI.comp (continuous_apply j)) continuous_const)
    refine (h1.continuous.smul (ei.continuous.comp ((continuous_S f).comp h2))).congr fun y => ?_
    simp only [A]
    split_ifs with h
    · simp [h, T]
    · simp [h]
  · rw [main]
    by_cases h : G (fun j => p2 (y j)) = 0
    · rw [h, GlobalTheory.ThK.Dbl.Dense.pureA_zero]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      simp only [A]
      rw [if_neg fun h' => (hφ₁ i).2 (h'.symm.trans h)]
      exact z0 _
    · let i₀ := hfin.toFinset.equivFin ⟨G fun j => p2 (y j), hfin.mem_toFinset.2 ⟨⟨_, hC' _ h, rfl⟩, h⟩⟩
      have hi : G (fun j => p2 (y j)) = φ₁ i₀ := by simp only [φ₁, i₀, Equiv.symm_apply_apply]
      rw [Finset.sum_eq_single i₀ (fun i _ hne => ?_) fun h => absurd (Finset.mem_univ _) h]
      · simp only [A]
        rw [if_pos hi, ← hi]
      · simp only [A]
        rw [if_neg fun h' => hne (hfin.toFinset.equivFin.symm.injective (Subtype.ext (h'.symm.trans hi)))]
        exact z0 _
  · obtain ⟨p, M, hp, hp'⟩ := grow (q.comp ei.toLinearMap) (hq.comp ei.continuous)
    obtain ⟨K, hK, hK'⟩ := exists_half_trace (F := F)
    let s : (Fin m → AF F) → ℝ := fun y => ∑ j, ∑ w : InfinitePlace F, normAtPlace w (qI F (y j))
    have hs0 : ∀ (y : Fin m → AF F) j, 0 ≤ ∑ w : InfinitePlace F, normAtPlace w (qI F (y j)) := fun y j =>
      Finset.sum_nonneg fun w _ => normAtPlace_nonneg _ _
    have hs : ∀ y, 0 ≤ s y := fun y => Finset.sum_nonneg fun j _ => hs0 y j
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∑ j, ‖ev2 (ζ j)‖ := ⟨_, rfl⟩
    obtain ⟨Cc, hCc⟩ : ∃ Z, Z = ∑ j, ‖ev2 (c j)‖ := ⟨_, rfl⟩
    have hCc0 : 0 ≤ Cc := hCc ▸ Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hZ0 : 0 ≤ Z := hZ ▸ Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hZ1 : ∀ j, ‖ev2 (ζ j)‖ ≤ Z := fun j =>
      hZ ▸ Finset.single_le_sum (f := fun j => ‖ev2 (ζ j)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    have hKC : 0 ≤ (1 + K₁ * Cc) ^ M := pow_nonneg (add_nonneg zero_le_one (mul_nonneg hK₁.le hCc0)) _
    refine (decay (Y := Fin hfin.toFinset.card × (Fin m → AF F)) (fun x => (A x.1 x.2).toLinearMap)
      (fun x => s x.2) (fun x => hs x.2) (K₁ * Z * (m * Fintype.card (InfinitePlace F)) * K) (fun x hy => ?_) q
      (sc ((1 + K₁ * Cc) ^ M) p) (sc_cont _ hp) M (fun x f => ?_) N).imp fun p' h => ⟨h.1, fun i y f => h.2 (i, y) f⟩
    · obtain ⟨i, y⟩ := x
      change 0 < s y at hy
      have hm : (Finset.univ : Finset (Fin m)).Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        simp only [s, h, Finset.sum_empty, lt_irrefl] at hy
      obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖qI F (y j)‖) hm
      have h1 : s y ≤ m * Fintype.card (InfinitePlace F) * ‖qI F (y j)‖ := by
        refine (Finset.sum_le_card_nsmul _ _ (Fintype.card (InfinitePlace F) * ‖qI F (y j)‖) fun i hi =>
          (sum_le_norm _).trans (mul_le_mul_of_nonneg_left (hj i hi) (Nat.cast_nonneg _))).trans (le_of_eq ?_)
        rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
      obtain ⟨α, hα, hα'⟩ := hK' (qI F (y j)) fun h => by
        rw [h, norm_zero, mul_zero] at h1
        exact absurd hy (not_lt.2 h1)
      refine ⟨aw0 F κ (α • ev2 (ζ j)), ?_, fun f => ?_⟩
      · have h2 : ‖aw0 F κ (α • ev2 (ζ j))‖ ≤ K₁ * (‖α‖ * Z) := (hK₁' _).trans (mul_le_mul_of_nonneg_left
          ((norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hZ1 j) (norm_nonneg _))) hK₁.le)
        calc _ ≤ K₁ * (‖α‖ * Z) * (m * Fintype.card (InfinitePlace F) * ‖qI F (y j)‖) :=
              mul_le_mul h2 h1 (hs y) (mul_nonneg hK₁.le (mul_nonneg (norm_nonneg _) hZ0))
          _ = K₁ * Z * (m * Fintype.card (InfinitePlace F)) * (‖α‖ * ‖qI F (y j)‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hα
            (mul_nonneg (mul_nonneg hK₁.le hZ0) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      · simp only [A]
        split_ifs with h
        · have h1 := key y j (pt α 0) _ (pureA_mem f hφ)
          rw [schr_pure hψ (pt α 0 • ζ j), pairEvaluation_smul, pairFunctional_smul, qI_pt, finite_projection_mixed_point, zero_smul, fw_zero, main, main,
            ← pureA_smul_left] at h1
          have h2 := pureA_cancel (h ▸ (hφ₁ i).2) h1
          have h3 : ψ (-(pt α 0 * y j)) = -1 := by
            rw [psi_eq hψ, map_neg, map_mul, qI_pt, map_neg, mul_comm α, hα', map_neg, map_mul, finite_projection_mixed_point, zero_mul, neg_zero,
              AddChar.map_zero_eq_one, mul_one, ← Complex.exp_pi_mul_I]
            congr 1
            push_cast
            ring
          rw [h3, neg_one_smul] at h2
          exact h2
        · simp
    · obtain ⟨i, y⟩ := x
      rw [sc_apply hKC]
      have h1 : ‖wy y‖ ≤ K₁ * (s y * Cc) := (hK₁' _).trans (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (by
        rw [hCc, Finset.mul_sum]
        refine Finset.sum_le_sum fun j hj => (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        exact (norm_le_sum _).trans (Finset.single_le_sum (fun j _ => hs0 y j) hj))) hK₁.le)
      have h2 := hs y
      have h3 := apply_nonneg p f
      simp only [A]
      split_ifs with h
      · refine (hp' (wy y) f).trans ?_
        rw [← mul_assoc, ← mul_pow]
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg _)) ?_ _) h3
        have h4 := mul_nonneg hK₁.le hCc0
        change 1 + ‖wy y‖ ≤ (1 + s y) * (1 + K₁ * Cc)
        generalize ‖wy y‖ = a, s y = b at h1 h2 ⊢
        nlinarith
      · simp only [ContinuousLinearMap.toLinearMap_zero, LinearMap.zero_apply, map_zero]
        exact mul_nonneg (pow_nonneg (add_nonneg zero_le_one h2) _) (mul_nonneg hKC h3)

end Ad

theorem slice_of : Slice := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hD φ hφ
  obtain ⟨ei, ef, h0, h⟩ := ev_pure hM hM₁ he
  obtain ⟨r, φ₁, C, A, h1, h2, h3, h4, h5⟩ := slice_core hB.std e ei ef h0 h (fun j => M.co.e (incM F (u j)))
    (fun j => M.co.e (incM F (z j))) (fun j a Φ hΦ => by rw [← map_smul]; exact he.inv _ (hD.mem j a) Φ hΦ)
    (fun i j => by rw [← M.co.form]; convert hD.pair i j) hφ
  refine ⟨r, φ₁, C, A, h1, h2, h3, fun y f => ?_, h5⟩
  rw [← h4, Darboux.rho, lin, map_sum]
  simp only [map_smul]

theorem evAdm_of : EvAdm := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁
  refine ⟨exists_adm_eq_thetaSum_of_locallyCompact F _, fun u Φ hΦ => schr_mem_schA _ hB.std _ Φ hΦ, fun ι ι' I e he u l hl => ?_⟩
  obtain ⟨ei, ef, -, h⟩ := ev_pure hM hM₁ he
  let R : Fn F n d →ₗ[ℂ] Fn F n d :=
    { toFun := M.co.rho B.ψ u
      map_add' := fun φ φ' => funext fun x => by simp only [Darboux.rho, schr, Pi.add_apply]; ring
      map_smul' := fun a φ => funext fun x => by
        simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  refine ⟨l ∘ₗ e ∘ₗ R, fun g hg => ?_, fun Φ _ => rfl⟩
  obtain ⟨h1, h2⟩ := h _ (fw_mem hB.std (fn2 (M.co.e u)) hg)
  obtain ⟨T, hT⟩ := hl _ h1
  refine ⟨T.comp (ei.comp (S (aw0 F _ (ev2 (M.co.e u))))), fun f => ?_⟩
  change l (e (schr B.ψ (M.co.e u) (pureA F f g))) = _
  rw [schr_pure hB.std, h2, hT]
  rfl

end PositivityTheory.ThKCT

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.NormPiInfSmul
section
noncomputable section

namespace PositivityTheory.ThKCT.Line

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField.mixedEmbedding
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.HeisSchA PositivityTheory.ThKCT.Ad PositivityTheory.ThKEst
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}

theorem cA_cA (h : IsCMExt F E σ) (a : AE F E) : cA σ (cA σ a) = a := by
  obtain ⟨t⟩ : Nonempty (E →+* ℂ) := inferInstance
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    change r ⊗ₜ[F] σ (σ x) = _
    rw [t.injective (show t (σ (σ x)) = t x by rw [h.2.2.2, h.2.2.2]; exact Complex.conj_conj _)]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem hTens_inc (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x y : Matrix (Fin n) (Fin d) E) :
    hTens (cA σ) (incM F J) (incM F J') (incM F x) (incM F y) = inclR (F := F) (AF F) (hTens σ J J' x y) := by
  simp only [hTens, incM, Matrix.map_apply, map_sum, map_mul]
  rfl

theorem hTens_smul (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin d) (Fin d) E) (x y : Matrix (Fin n) (Fin d) E) (a b : E) :
    hTens σ J J' (a • x) (b • y) = a * σ b * hTens σ J J' x y := by
  simp only [hTens, Matrix.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

theorem incM_smul (a : E) (x : Matrix (Fin n) (Fin d) E) : incM F (a • x) = inclR (F := F) (AF F) a • incM F x := by
  ext i j
  exact map_mul (inclR (F := F) (AF F)) _ _

theorem exists_dual (B : Base F E) {X : Spc F E n} {W : Spc F E d} {I : Set (Ten F E n d)} {v₀ z₀ : Matrix (Fin n) (Fin d) E}
    (hI : ∀ a : AE F E, a • incM F z₀ ∈ I) (hu : IsUnit (hTens (cA σ) (incM F X.J) (incM F W.J) (incM F z₀) (incM F v₀)))
    {m : ℕ} (b : Module.Basis (Fin m) F E) : ∃ z, Dual σ X W I (fun j => b j • v₀) z := by
  haveI : Module.Finite F E := Module.Finite.of_basis b
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h0 : hTens σ X.J W.J z₀ v₀ ≠ 0 := fun h => by
    rw [hTens_inc, h, map_zero] at hu
    exact (hu.map (piInf (B.emb w))).ne_zero (map_zero _)
  refine ⟨fun i => (-σ (b.traceDual i) / hTens σ X.J W.J z₀ v₀) • z₀, fun j a => ?_, fun i j => ?_⟩
  · rw [incM_smul, ← smul_assoc]
    exact hI _
  · rw [sy, symp, hTens_inc, hTens_smul, show -σ (b.traceDual i) / hTens σ X.J W.J z₀ v₀ * σ (b j) * hTens σ X.J W.J z₀ v₀ =
      -σ (b j * b.traceDual i) by rw [map_mul]; field_simp, map_neg, neg_one_mul, neg_neg]
    change Algebra.trace (AF F) _ ((1 : AF F) ⊗ₜ[F] _) = _
    rw [GlobalTheory.ThK.Dbl.Dense.trace_tmul, one_mul, show σ (b j * b.traceDual i) =
      AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ) (b j * b.traceDual i) from rfl,
      Algebra.trace_eq_of_algEquiv, Module.Basis.trace_mul_traceDual]
    simp only [eq_comm (a := i)]
    split_ifs <;> simp

theorem norm_piInf_smul (h : IsCMExt F E σ) {w : InfinitePlace F} (t : EmbOver E w) (y : AF F) (β : AE F E) :
    ‖piInf t (y • β)‖ = normAtPlace w (evI F y) * ‖piInf t β‖ := by
  haveI := h.1
  rw [Algebra.smul_def, map_mul, norm_mul, normAtPlace_apply_of_isReal (IsTotallyReal.isReal w)]
  congr 1
  change ‖infEmb t (evInf F w y ⊗ₜ[F] (1 : E))‖ = ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (y.1 w)‖
  rw [infEmb_tmul, map_one, mul_one, (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero (map_zero _)]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

def Nice {κ : Type} [Fintype κ] (μ : Measure (AE F E)ˣ) (z : ℕ) (v : AE F E → (κ → AF F) → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (φ : ι → (κ → Af F) → ℂ) (g : ι → AE F E → SInf F κ), (∀ i, φ i ∈ SB _) ∧ (∀ i, Continuous (g i)) ∧
    (∀ a, v a = ∑ i, pureA F (g i a) (φ i)) ∧
    ∀ q : Seminorm ℂ (SInf F κ), Continuous q → ∀ i, Integrable (fun l : (AE F E)ˣ => q (g i l) * (absE F E l : ℝ) ^ z) μ

set_option maxHeartbeats 800000 in
theorem nice (hS : Slice) (hT : TateAbs) {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) {ι ι' I e}
    (he : IsEv B M M₁ ι ι' I e) {v₀ z₀ : Matrix (Fin n) (Fin d) E} (hI : ∀ a : AE F E, a • incM F z₀ ∈ I)
    (hu : IsUnit (hTens (cA σ) (incM F X.J) (incM F W.J) (incM F z₀) (incM F v₀))) (τ : AE F E →ₐ[AF F] AE F E)
    (hτ : ∀ a, τ (τ a) = a) (μ : Measure (AE F E)ˣ) (hμ : μ.IsHaarMeasure) {z : ℕ} (hz : 2 ≤ z) {Ψ : Fn F n d}
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) : Nice μ z fun a => e (M.co.rho B.ψ (τ a • incM F v₀) Ψ) := by
  induction hΨ using Submodule.span_induction with
  | zero =>
    refine ⟨Empty, inferInstance, Empty.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim, fun a => ?_, fun _ _ i => i.elim⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty, ← map_zero e]
    exact congrArg e (funext fun x => mul_zero _)
  | add x y _ _ hx hy =>
    obtain ⟨ι₁, _, φ, g, h1, h2, h3, h4⟩ := hx
    obtain ⟨ι₂, _, φ', g', h1', h2', h3', h4'⟩ := hy
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim φ φ', Sum.elim g g', Sum.forall.2 ⟨h1, h1'⟩, Sum.forall.2 ⟨h2, h2'⟩, fun a => ?_,
      fun q hq => Sum.forall.2 ⟨h4 q hq, h4' q hq⟩⟩
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [← h3 a, ← h3' a, ← map_add]
    congr 1
    exact funext fun x => mul_add _ _ _
  | smul c x _ hx =>
    obtain ⟨ι₁, _, φ, g, h1, h2, h3, h4⟩ := hx
    refine ⟨ι₁, inferInstance, fun i => c • φ i, g, fun i => Submodule.smul_mem _ _ (h1 i), h2, fun a => ?_, h4⟩
    simp only [GlobalTheory.ThK.Dbl.Dense.pureA_smul]
    rw [← Finset.smul_sum, ← h3 a, ← map_smul]
    congr 1
    exact funext fun x => mul_left_comm _ _ _
  | mem x hx =>
    obtain ⟨f, φ, hφ, rfl⟩ := hx
    obtain ⟨⟨_, -⟩, -, _, -, -, _, -⟩ := ideleTop F E
    haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
    let b := Module.finBasis F E
    let Bt := Algebra.TensorProduct.basis (AF F) b
    obtain ⟨zz, hD⟩ := exists_dual B hI hu b
    obtain ⟨r, φ₁, C, A, h1, h2, h3, h4, h5, h6⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he _ _ _ hD φ hφ
    let y : AE F E → Fin (Module.finrank F E) → AF F := fun a => Bt.equivFun (τ a)
    have hy : Continuous y := IsModuleTopology.continuous_of_linearMap (Bt.equivFun.toLinearMap ∘ₗ τ.toLinearMap)
    have e1 : ∀ a, τ a = ∑ j, y a j • Bt j := fun a => (Bt.sum_equivFun _).symm
    have e2 : ∀ a, a = ∑ j, y a j • τ (Bt j) := fun a => by
      conv_lhs => rw [← hτ a, e1 a, map_sum]
      simp only [map_smul]
    refine ⟨Fin r, inferInstance, φ₁, fun i a => A i (y a) f, h1, fun i => (h3 i f).comp hy, fun a => ?_, fun q hq i => ?_⟩
    · beta_reduce
      rw [← h4, lin, e1 a, Finset.sum_smul]
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [incM_smul, smul_assoc, Algebra.TensorProduct.basis_apply]
      rfl
    obtain ⟨N, hN⟩ := hT F E σ B hB μ hμ z hz
    obtain ⟨p, -, hp⟩ := h6 q N hq
    have hN' := hN _ (h2.image (f := fun c => ∑ j, mk 0 (c j) • τ (Bt j)) (continuous_finsetSum _ fun j _ =>
      Continuous.smul (f := fun c : _ → Af F => mk 0 (c j)) (g := fun _ => τ (Bt j))
        (continuous_const.prodMk (continuous_apply j)) continuous_const))
    set K := ∑ j, ∑ w, ‖piInf (B.emb w) (τ (Bt j))‖ with hK
    have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
    refine ⟨((hq.comp ((h3 i f).comp (hy.comp Units.continuous_val))).mul
      ((NNReal.continuous_coe.comp GlobalTheory.Doubling.continuous_absE).pow z)).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun l => ?_) ((lintegral_indicator_le _ _).trans_lt
      ((lintegral_const_mul' (ENNReal.ofReal (p f * (1 + K) ^ N)) _ ENNReal.ofReal_ne_top).trans_lt
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN')))
    by_cases hl : (fun j => (y l j).2) ∈ C
    · rw [Set.indicator_of_mem, ← ENNReal.ofReal_mul (by positivity), Real.enorm_eq_ofReal (by positivity)]
      · refine ENNReal.ofReal_le_ofReal ?_
        rw [← mul_div_assoc, mul_div_right_comm]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [le_div_iff₀ (by positivity)]
        refine le_trans ?_ (mul_le_mul_of_nonneg_right (hp i (y l) f) (by positivity))
        rw [mul_assoc, ← mul_pow]
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (apply_nonneg _ _)
        set s := ∑ j, ∑ w : InfinitePlace F, normAtPlace w (evI F (y l j)) with hs
        have hs1 : ∀ j w, normAtPlace w (evI F (y l j)) ≤ s := fun j w =>
          (Finset.single_le_sum (fun w _ => normAtPlace_nonneg w _) (Finset.mem_univ w)).trans
            (Finset.single_le_sum (f := fun j => ∑ w : InfinitePlace F, normAtPlace w (evI F (y l j)))
              (fun j _ => Finset.sum_nonneg fun w _ => normAtPlace_nonneg w _) (Finset.mem_univ j))
        have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun w _ => normAtPlace_nonneg w _
        have : ∑ w, ‖piInf (B.emb w) (l : AE F E)‖ ≤ s * K := by
          rw [hK, Finset.sum_comm, Finset.mul_sum]
          refine Finset.sum_le_sum fun w _ => ?_
          conv_lhs => rw [e2 l, map_sum]
          rw [Finset.mul_sum]
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_piInf_smul hB.cm]
          exact mul_le_mul_of_nonneg_right (hs1 j w) (norm_nonneg _)
        nlinarith
      · refine ⟨_, ⟨_, hl, rfl⟩, fun u hu => ?_⟩
        beta_reduce
        rw [congrArg (· - ∑ j, mk 0 (y l j).2 • τ (Bt j)) (e2 l), ← Finset.sum_sub_distrib, Finset.smul_sum]
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [← sub_smul, ← smul_assoc, show y l j - mk 0 (y l j).2 = mk (y l j).1 0 from
          Prod.ext (sub_zero _) (sub_self _), at_mk _ u hu, zero_smul]
    · simp only [h5 i _ hl, ContinuousLinearMap.zero_apply, map_zero, zero_mul, enorm_zero, zero_le]

end PositivityTheory.ThKCT.Line

end
end

-- bundled from Development.WeilBound.ThetaLifts.SmallCones.SoStab
section
noncomputable section

namespace PositivityTheory.ThKCT.So

open NumberField GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem det_ne_of_map (B : Base F E) (w : InfinitePlace F) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (hJ : (J.map (B.emb w).1).det ≠ 0) : J.det ≠ 0 := fun h0 =>
  hJ (((RingHom.map_det _ J).symm.trans (congrArg _ h0)).trans (map_zero _))

theorem det_herm {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_ne_of_map B w _ (GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w))

theorem det_skew {B : Base F E} {n r s : ℕ} {X : Spc F E n} (h : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact det_ne_of_map B w _ fun h0 =>
    GlobalTheory.WeilSchrodingerHerm.det_ne_zero_of_hasSig (h.sig w) (by rw [Matrix.det_smul, h0, mul_zero])

theorem _root_.PositivityTheory.ThKCT.soStab_of : SoStab := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP x
  exact PositivityTheory.KCo.so_stable M hP.base.cm hP.base.std (det_herm hP.herm) (det_skew hP.skew) hP.good
    (IsUWeilPair.isUSplitting hP.weil).toIsSplitting B.τ₁ x

end PositivityTheory.ThKCT.So

end
end

