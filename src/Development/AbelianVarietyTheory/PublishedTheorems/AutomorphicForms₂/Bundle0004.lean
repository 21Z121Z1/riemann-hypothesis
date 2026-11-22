import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters GlobalTheory.RealPar Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.Published.CoverSeries

variable {p q n : ℕ}

def pull {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) : URep T where
  H := H
  π := { toFun := fun x => σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))
         map_one' := by simpa using hσ.1.1
         map_mul' := fun x y => by
           rw [ContinuousLinearMap.mul_def, ← hσ.1.2 _ (h.cov_mem T x) _ (h.cov_mem T y)]
           simp [Matrix.submatrix_mul_equiv] }
  isom x v := hσ.2.1 _ (h.cov_mem T x) v
  cont v := (hσ.2.2 v).comp_continuous
    ((Units.continuous_val.comp (continuous_fst.comp T.emb.continuous)).matrix_reindex e e) (h.cov_mem T)

theorem exists_of_isDSPar (T : GrpData p q)
    (hM : ∀ U : URep T, Formalism.MainNotions.SchurIrreducible.IrrU U → ∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] U.H), Formalism.MainNotions.SchurIrreducible.IsHCMod U M io)
    (P : SignedPar n) {e : Ix p q ≃ Fin n} (h : BlockOrd e P.sgn) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDSPar P σ) :
    ∃ R : DSRep T, HasParam R (blockPar P e) := by
  haveI : CompleteSpace H := hσ.1
  have hU := hσ.2.2.1
  have hirr : Formalism.MainNotions.SchurIrreducible.IrrU (pull h T hU) := ⟨hσ.2.1, fun S hS hst => hσ.2.2.2.1 S hS fun g hg v hv => by
    obtain ⟨x, rfl⟩ := h.cov_surj T hg
    exact hst x v hv⟩
  obtain ⟨M, io, m1, m2, m3⟩ := hM _ hirr
  haveI := SqInt.isHaarMeasure_map_covU h T
  have hμ := Measure.isMulLeftInvariant_eq_smul (T.haar.map (SqInt.covU h T)) (Formalism.REAL.muG P.sgn)
  obtain ⟨d, hd, hI⟩ := GlobalTheory.Mem.Vol.exists_isFdeg_smul_of_isDS n P.sgn P.lam H σ hσ _
    (Measure.haarScalarFactor_pos_of_isHaarMeasure (T.haar.map (SqInt.covU h T)) (Formalism.REAL.muG P.sgn))
  refine ⟨⟨pull h T hU, hirr.1, hirr.2, d, hd, fun x y => ?_, M, io, m1, m2, m3⟩, ?_⟩
  · change H at x y
    obtain ⟨i1, i2⟩ := hI x y x y
    rw [← ENNReal.smul_def, ← hμ] at i1 i2
    have hf : (fun g => coefOn (ε := P.sgn) σ x y g * star (coefOn (ε := P.sgn) σ x y g)) =
        fun g => ((‖coefOn (ε := P.sgn) σ x y g‖ ^ 2 : ℝ) : ℂ) := by
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hf] at i1 i2
    have hm := (SqInt.continuous_covU h T).measurable.aemeasurable (μ := T.haar)
    rw [integral_map hm i1.aestronglyMeasurable] at i2
    have i3 := (integrable_map_measure i1.aestronglyMeasurable hm).1 i1
    refine ⟨i3.re.congr (Filter.Eventually.of_forall fun g => Complex.ofReal_re _), ?_⟩
    rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at i2
    have i4 : ((∫ g, ‖coefOn (ε := P.sgn) σ x y (SqInt.covU h T g)‖ ^ 2 ∂T.haar : ℝ) : ℂ) =
        ((‖x‖ ^ 2 * ‖y‖ ^ 2 / d : ℝ) : ℂ) := by
      push_cast
      exact i2
    exact_mod_cast i4
  · exact (hasParam_iff_isDSPar _ P h (σ := σ) fun _ => rfl).2 hσ

theorem of_upq (hE : DiscreteSeriesUpqExists)
    (hM : ∀ p q : ℕ, 1 ≤ p + q → ∀ (T : GrpData p q) (U : URep T), Formalism.MainNotions.SchurIrreducible.IrrU U →
      ∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] U.H), Formalism.MainNotions.SchurIrreducible.IsHCMod U M io) :
    DiscreteSeriesCoverExists := by
  intro p q T lam hl
  rcases Nat.eq_zero_or_pos (p + q) with h0 | h0
  · obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.1 h0
    exact ⟨Cover.trivZero T, GlobalTheory.SignedParTest.hasParam_zero _ _⟩
  have key : ∀ lam : Ix p q → ℚ, IsParam lam → (∀ a, ∃ m : ℤ, lam a - (((p + q : ℕ) : ℚ) - 1) / 2 = m) →
      ∃ R : DSRep T, HasParam R lam := by
    intro lam hl hi
    obtain ⟨P, e, -, h, rfl⟩ := exists_blockPar hl hi
    obtain ⟨H, _, _, σ, hσ⟩ := hE _ P.sgn P.lam P.hc
    exact exists_of_isDSPar T (hM p q h0 T) P h hσ
  obtain ⟨P, e, -, h, rfl | rfl⟩ := isParam_cases hl
  · exact key _ hl fun a => ⟨(P.hc.2 (e a)).choose, by simp [blockPar, ratEntry]⟩
  · obtain ⟨R, hR⟩ := key (fun a => blockPar P e a + 1 / 2 + 1 / 2)
      ⟨fun x y e => hl.1 (add_left_injective _ e), fun x y e => by simpa using hl.2.1 x y e,
        fun x => by
          obtain ⟨k, hk⟩ := hl.2.2.1 x
          exact ⟨k + 1, by push_cast; linarith⟩,
        fun x y => by simpa using hl.2.2.2 x y⟩
      fun a => ⟨(P.hc.2 (e a)).choose + 1, by simp only [blockPar, ratEntry]; push_cast; ring⟩
    exact ⟨Cover.twist R, (Cover.hasParam_twist R _).2 hR⟩

end GlobalTheory.Published.CoverSeries

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LowestRankThree
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL

noncomputable section

namespace GlobalTheory.Published.DSExistsModel

def detPow (n : ℕ) (m : ℤ) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ →L[ℂ] ℂ :=
  (g.det ^ m) • ContinuousLinearMap.id ℂ ℂ

theorem detPow_apply (n : ℕ) (m : ℤ) (g : Matrix (Fin n) (Fin n) ℂ) (v : ℂ) :
    detPow n m g v = g.det ^ m * v := by simp [detPow]

theorem norm_det {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ‖g.det‖ = 1 := by
  have h : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  have h1 := congrArg Matrix.det h
  have h2 : (Formalism.REAL.Jm ε).det * (Formalism.REAL.Jm ε).det = 1 := by
    rw [← Matrix.det_mul, Formalism.REAL.Jm_mul_self, Matrix.det_one]
  have h3 : (Formalism.REAL.Jm ε).det ≠ 0 := left_ne_zero_of_mul_eq_one h2
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h1
  have h4 : star g.det * g.det = 1 := by
    apply mul_left_cancel₀ h3
    linear_combination h1
  have h5 := congrArg norm h4
  rw [norm_mul, norm_star, norm_one] at h5
  nlinarith [norm_nonneg g.det]

def lamDet (n : ℕ) (m : ℤ) : Fin n → ℝ := fun a => (m : ℝ) + Formalism.QuantumDeterminants.rhoStd n a

theorem lamDet_hc (n : ℕ) (m : ℤ) : Formalism.QuantumDeterminants.IsHCParam (lamDet n m) := by
  refine ⟨fun a b h => ?_, fun a => ⟨m - (a : ℕ), ?_⟩⟩
  · have : ((a : ℕ) : ℝ) < (b : ℕ) := by exact_mod_cast h
    simp only [lamDet, Formalism.QuantumDeterminants.rhoStd]; linarith
  · simp only [lamDet, Formalism.QuantumDeterminants.rhoStd]; push_cast; ring

theorem lowK_lamDet (n : ℕ) (s : Bool) (m : ℤ) :
    Formalism.QuantumDeterminants.lowK (fun _ : Fin n => s) (lamDet n m) = fun _ => (m : ℝ) := by
  funext a
  rw [GlobalTheory.DefiniteCheck.lowK_const]
  simp only [lamDet, Formalism.QuantumDeterminants.rhoStd]; ring

theorem detPow_diag (n : ℕ) (m : ℤ) (θ : Fin n → ℝ) (v : ℂ) :
    detPow n m (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) v =
      Complex.exp (((∑ a, (m : ℝ) * θ a : ℝ) : ℂ) * Complex.I) • v := by
  rw [detPow_apply, Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul, smul_eq_mul]
  congr 2
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem isDS_detPow (n : ℕ) (s : Bool) (m : ℤ) : IsDS (fun _ : Fin n => s) (lamDet n m) (detPow n m) := by
  rw [GlobalTheory.RealPar.isDS_const_iff]
  refine ⟨inferInstance, inferInstance, ⟨⟨?_, fun a _ b _ => ?_⟩, fun g hg v => ?_, fun v => ?_⟩,
    inferInstance, fun _ _ _ _ => trivial, fun S _ _ => eq_bot_or_eq_top S, ?_, ?_⟩
  · ext; simp [detPow_apply]
  · ext; simp [detPow_apply, mul_zpow]
  · rw [detPow_apply, norm_mul, norm_zpow, norm_det hg]; simp
  · simp only [detPow_apply]
    refine ContinuousOn.mul (ContinuousOn.zpow₀ (continuous_id.matrix_det.continuousOn) m fun g hg => Or.inl ?_)
      continuousOn_const
    intro h0
    have := norm_det hg
    simp only [id] at h0
    rw [h0] at this
    simp at this
  · refine ⟨1, trivial, one_ne_zero, fun θ _ => ?_⟩
    unfold allPos
    rw [lowK_lamDet]
    exact detPow_diag n m θ 1
  · intro μ v _ hv hw
    refine ⟨0, fun a b h => absurd rfl h, ?_⟩
    unfold allPos at *
    rw [lowK_lamDet]
    have hK : ∀ θ : Fin n → ℝ, Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈
        Formalism.REAL.Kset (fun _ : Fin n => true) := by
      intro θ
      refine ⟨?_, by simp [GlobalTheory.DefiniteCheck.jm_const]⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        Complex.norm_exp_ofReal_mul_I]
      simp
    funext a
    simp only [Pi.zero_apply, Nat.cast_zero, zero_smul, Finset.sum_const_zero, Pi.sub_apply]
    by_contra hne
    have h := hw (Pi.single a (Real.pi / ((m : ℝ) - μ a))) (hK _)
    rw [detPow_diag] at h
    have h2 := smul_left_injective ℂ hv h
    simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    have h3 : Complex.exp (Real.pi * Complex.I) = 1 := by
      have e : (Real.pi : ℂ) * Complex.I = (((m : ℝ) * (Real.pi / ((m : ℝ) - μ a)) : ℝ) : ℂ) * Complex.I -
          ((μ a * (Real.pi / ((m : ℝ) - μ a)) : ℝ) : ℂ) * Complex.I := by
        rw [← sub_mul, ← Complex.ofReal_sub, ← sub_mul, mul_div_cancel₀ _ hne]
      rw [e, Complex.exp_sub, h2, div_self (Complex.exp_ne_zero _)]
    rw [Complex.exp_pi_mul_I] at h3
    norm_num at h3

theorem holds_rank_le_one (N : ℕ) (hN : N ≤ 1) (ε : Fin N → Bool) (lam : Fin N → ℝ)
    (h : Formalism.QuantumDeterminants.IsHCParam lam) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ := by
  interval_cases N
  · have h1 : ε = fun _ => true := funext fun a => a.elim0
    have h2 : lam = lamDet 0 0 := funext fun a => a.elim0
    rw [h1, h2]
    exact ⟨ℂ, _, _, _, isDS_detPow 0 true 0⟩
  · obtain ⟨m, hm⟩ := h.2 0
    have h1 : ε = fun _ => ε 0 := funext fun a => by rw [Subsingleton.elim a 0]
    have h2 : lam = lamDet 1 m := funext fun a => by
      rw [Subsingleton.elim a 0]
      simp [lamDet, Formalism.QuantumDeterminants.rhoStd] at hm ⊢
      exact hm
    rw [h1, h2]
    exact ⟨ℂ, _, _, _, isDS_detPow 1 (ε 0) m⟩

theorem holds_det (N : ℕ) (s : Bool) (m : ℤ) :
    Formalism.QuantumDeterminants.IsHCParam (lamDet N m) ∧
    IsDS (fun _ : Fin N => s) (lamDet N m) (detPow N m) :=
  ⟨lamDet_hc N m, isDS_detPow N s m⟩

theorem card_split {N : ℕ} (ε : Fin N → Bool) (a : Fin N) :
    (((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ) + ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) +
    ((univ.filter fun b => a < b ∧ ε b ≠ ε a).card : ℝ) + ((univ.filter fun b => b < a ∧ ε b ≠ ε a).card : ℝ)) =
      (N : ℝ) - 1 := by
  have h : ∑ b : Fin N, ((if a < b ∧ ε b = ε a then (1 : ℝ) else 0) + (if b < a ∧ ε b = ε a then (1 : ℝ) else 0) +
      (if a < b ∧ ε b ≠ ε a then (1 : ℝ) else 0) + (if b < a ∧ ε b ≠ ε a then (1 : ℝ) else 0)) =
      ∑ b : Fin N, ((1 : ℝ) - if b = a then 1 else 0) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy a b with h | h | h
    · by_cases e : ε b = ε a <;> simp [h, h.ne', not_lt_of_gt h, e]
    · subst h; simp
    · by_cases e : ε b = ε a <;> simp [h, h.ne, not_lt_of_gt h, e]
  simpa [Finset.sum_add_distrib, Finset.sum_sub_distrib] using h

theorem lowest_integral {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ)
    (h : ∀ a, ∃ m : ℤ, lam a - ((N : ℝ) - 1) / 2 = (m : ℝ)) (a : Fin N) :
    ∃ m : ℤ, (lam + rhoN ε - rhoC ε) a = (m : ℝ) := by
  obtain ⟨m, hm⟩ := h a
  have := card_split ε a
  refine ⟨m + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b = ε a).card, ?_⟩
  simp only [Pi.sub_apply, Pi.add_apply, rhoN, rhoC]
  push_cast
  linarith

theorem lowest_rank_two :
    (![1 / 2, -1 / 2] : Fin 2 → ℝ) + rhoN ![true, false] - rhoC ![true, false] = ![1, -1] := by
  funext a
  simp only [rhoN, rhoC, Finset.card_filter, Pi.add_apply, Pi.sub_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases a <;> simp [Fin.lt_def] <;> norm_num

theorem lowest_rank_three :
    (![1, 0, -1] : Fin 3 → ℝ) + rhoN ![true, false, true] - rhoC ![true, false, true] = ![1, 0, -1] := by
  funext a
  simp only [rhoN, rhoC, Finset.card_filter, Pi.add_apply, Pi.sub_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases a <;> simp [Fin.lt_def] <;> norm_num

theorem lowest_rank_three' :
    (![1, 0, -1] : Fin 3 → ℝ) + rhoN ![true, true, false] - rhoC ![true, true, false] = ![1, 1, -2] := by
  funext a
  simp only [rhoN, rhoC, Finset.card_filter, Pi.add_apply, Pi.sub_apply, Fin.sum_univ_succ, Fin.sum_univ_zero]
  fin_cases a <;> simp [Fin.lt_def] <;> norm_num

theorem diag_mem {N : ℕ} (ε : Fin N → Bool) (θ : Fin N → ℝ) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  refine ⟨?_, by simp [Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rw [Pi.star_apply, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  simp

theorem integral_of_isDS {N : ℕ} (ε : Fin N → Bool) (lam : Fin N → ℝ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (h : IsDS ε lam σ) (a : Fin N) :
    ∃ m : ℤ, lam a - ((N : ℝ) - 1) / 2 = (m : ℝ) := by
  obtain ⟨S, -, -, -, ⟨v, -, hv, hw⟩, -⟩ := h.2.2.2.2.2.1
  have h1 := hw (Pi.single a (2 * Real.pi)) (diag_mem ε _)
  have e : Matrix.diagonal (fun b => Complex.exp (((Pi.single a (2 * Real.pi) : Fin N → ℝ) b : ℂ) * Complex.I)) = 1 := by
    rw [← Matrix.diagonal_one]; congr 1; funext b
    by_cases hb : b = a
    · subst hb; simp
    · simp [hb]
  rw [e, h.2.2.1.1.1] at h1
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    ContinuousLinearMap.one_apply] at h1
  have h2 : Complex.exp (((Formalism.QuantumDeterminants.lowK ε lam a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 :=
    smul_left_injective ℂ hv (h1.symm.trans (one_smul ℂ v).symm)
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h2
  have h3 : Formalism.QuantumDeterminants.lowK ε lam a = k := by
    have h4 : ((Formalism.QuantumDeterminants.lowK ε lam a : ℝ) : ℂ) * (2 * Real.pi * Complex.I) = k * (2 * Real.pi * Complex.I) := by
      rw [← hk]; push_cast; ring
    exact_mod_cast mul_right_cancel₀ Complex.two_pi_I_ne_zero h4
  have := card_split ε a
  refine ⟨k - (univ.filter fun b => a < b ∧ ε b ≠ ε a).card - (univ.filter fun b => b < a ∧ ε b = ε a).card, ?_⟩
  simp only [Formalism.QuantumDeterminants.lowK, Pi.sub_apply, Pi.add_apply, rhoN, rhoC] at h3
  push_cast
  linarith

theorem use_rank_two (h : DiscreteSeriesUpqExists) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin 2) (Fin 2) ℂ → (H →L[ℂ] H)), IsSqIntOn ![true, false] σ ∧
      ∃ S : Submodule ℂ H, IsKTypeOf ![true, false] σ ![1, -1] S := by
  obtain ⟨H, i1, i2, σ, -, -, -, -, h5, h6, -⟩ := h 2 ![true, false] ![1 / 2, -1 / 2]
    ⟨by intro a b hab; fin_cases a <;> fin_cases b <;> simp_all <;> norm_num,
     by intro a; fin_cases a
        · exact ⟨0, by norm_num⟩
        · exact ⟨-1, by norm_num⟩⟩
  rw [lowest_rank_two] at h6
  exact ⟨H, i1, i2, σ, h5, h6⟩

end GlobalTheory.Published.DSExistsModel
end
end

