import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0127
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0159
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0161
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0160
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DecGapOfFormula

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDualVectorNormInvNotMemLocal
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.LocNot

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_of_tmul_mem (v : HeightOneSpectrum (𝓞 F)) (t : v.adicCompletion F)
    (ht : (1 : E) ⊗ₜ[F] t ∈ intV E v) : t ∈ v.adicCompletionIntegers F := by
  classical
  let ι : v.adicCompletion F →ₐ[F] E ⊗[F] v.adicCompletion F := Algebra.TensorProduct.includeRight
  letI : Algebra (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) :=
    (ι.toRingHom.comp (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra
  let ιO : v.adicCompletion F →ₐ[v.adicCompletionIntegers F] E ⊗[F] v.adicCompletion F :=
    { ι.toRingHom with commutes' := fun _ => rfl }
  have hinj : Function.Injective ιO :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F E).injective
  have hle : intV E v ≤
      (integralClosure (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨⟨e, he⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · obtain ⟨a, rfl⟩ := he
      obtain ⟨p, hp, hpe⟩ := RingOfIntegers.isIntegral_coe a
      refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      let g : E →+* E ⊗[F] v.adicCompletion F := Algebra.TensorProduct.includeLeftRingHom
      have hc : (algebraMap (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F)).comp
          (Int.castRingHom _) = g.comp (algebraMap ℤ E) := RingHom.ext_int _ _
      have h3 := congrArg g hpe
      rw [Polynomial.hom_eval₂, map_zero] at h3
      rw [hc]
      exact h3
    · exact isIntegral_algebraMap (x := (⟨c, hc⟩ : v.adicCompletionIntegers F))
  have hi : IsIntegral (v.adicCompletionIntegers F) t := (isIntegral_algHom_iff ιO hinj).1 (hle ht)
  obtain ⟨b, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact b.2

end GlobalTheory.St.G.LocNot

namespace GlobalTheory.St.G

theorem dual_not_loc_of_norm_inv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), (∀ x ∈ L, x ∈ dualSet (cm.sig : E →+* E) J L) → ∀ (d : Fin n → E) (T : ℕ), 0 < T → d ∈ dualL cm.sig J L → Formalism.UG.hform (cm.sig : E →+* E) J d d - ((T : E))⁻¹ ∈ (algebraMap (𝓞 E) E).range → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∃ x ∈ loc v (dualL cm.sig J L), x ∉ loc v L := by
  intro F E _ _ _ _ _ _ cm n J L hL d T hT hd hdd v hv
  let x : Fin n → E ⊗[F] v.adicCompletion F := fun i => inclE (F := F) (v.adicCompletion F) (d i)
  refine ⟨x, Submodule.subset_span ⟨d, hd, rfl⟩, fun hx => ?_⟩
  have hLd : L ≤ dualL cm.sig J L := fun y hy => Submodule.subset_span (hL y hy)
  have hx' : x ∈ loc v (dualL cm.sig J L) := Submodule.span_mono (Set.image_mono hLd) hx
  have hxx := Dual.fwd cm.sig J (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring L x hx' x hx
  rw [Dual.hR_incl] at hxx
  obtain ⟨a, ha⟩ := hdd
  have h1 : inclE (F := F) (v.adicCompletion F) ((T : E)⁻¹) ∈ intV E v := by
    have he : Formalism.UG.hform (cm.sig : E →+* E) J d d = algebraMap (𝓞 E) E a + (T : E)⁻¹ := by
      rw [ha]; ring
    rw [he, map_add] at hxx
    have ha' : inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E a) ∈ intV E v :=
      Subring.subset_closure (Or.inl ⟨⟨_, a, rfl⟩, rfl⟩)
    have := sub_mem hxx ha'
    rwa [add_sub_cancel_left] at this
  have h2 : inclE (F := F) (v.adicCompletion F) ((T : E)⁻¹) =
      (1 : E) ⊗ₜ[F] ((T : v.adicCompletion F)⁻¹) := by
    have e1 : ((T : E))⁻¹ = ((T : F))⁻¹ • (1 : E) := by
      rw [Algebra.smul_def, mul_one, map_inv₀, map_natCast]
    have e2 : ((T : v.adicCompletion F))⁻¹ = ((T : F))⁻¹ • (1 : v.adicCompletion F) := by
      rw [Algebra.smul_def, mul_one, map_inv₀, map_natCast]
    rw [e1, e2]
    show ((T : F)⁻¹ • (1 : E)) ⊗ₜ[F] (1 : v.adicCompletion F) = _
    rw [TensorProduct.smul_tmul]
  rw [h2] at h1
  have h3 := LocNot.mem_of_tmul_mem v _ h1
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h3
  have hval : Valued.v (T : v.adicCompletion F) < 1 := by
    have hv1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (T : 𝓞 F)
    have hv2 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (T : 𝓞 F)).2 hv
    rw [← hv1] at hv2
    convert hv2 using 2
    simp
  have hne : (T : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F))]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hT.ne')
  rw [map_inv₀] at h3
  have hpos : 0 < Valued.v (T : v.adicCompletion F) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hne)
  have h4 : 1 ≤ Valued.v (T : v.adicCompletion F) := (inv_le_one₀ hpos).1 h3
  exact absurd hval (not_lt.2 h4)

end GlobalTheory.St.G
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsSaturatedIsotropicFlagOfAdaptedBasis
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.FlagBase.AdSat

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem isSatFlag_of_isAdapted (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (_hj : ∀ i, 1 ≤ j i) (h : IsAdapted I I₀ e xf j S Λ x₀ T T' T₀) :
    IsSatFlag I (lamX I (1, xf)) j S := by
  classical
  obtain ⟨-, -, hΛ, h1, h2, -, hL, hS⟩ := h
  have hJ : I.Jᴴ = I.J := I.J_herm
  let p : ∀ i, (Fin I.n → I.E) →ₗ[I.E] (Fin (j i) → I.E) := fun i => ((T' i)ᴴ * I.J).mulVecLin
  have hsw : ∀ i k, (T' i)ᴴ * I.J * T k = ((T k)ᴴ * I.J * T' i)ᴴ := fun i k => by
    simp [Matrix.conjTranspose_mul, hJ, Matrix.mul_assoc]
  have pT : ∀ i x, p i (T i *ᵥ x) = x := fun i x => by
    simp only [p, mulVecLin_apply, mulVec_mulVec]
    rw [hsw, (h2 i).1]; simp
  have pT' : ∀ i k x, k ≠ i → p i (T k *ᵥ x) = 0 := fun i k x hk => by
    simp only [p, mulVecLin_apply, mulVec_mulVec]
    rw [hsw, (h1 k i).2.2 hk]; simp
  have pS : ∀ i (u : ∀ i, Fin (j i) → I.E), p i (∑ k, T k *ᵥ u k) = u i := fun i u => by
    rw [map_sum, Finset.sum_eq_single i (fun k _ hk => pT' i k _ hk) (by simp), pT]
  have hsp : ∀ k z, z ∈ Submodule.span I.E (S k : Set (Fin I.n → I.E)) →
      z = ∑ i, T i *ᵥ p i z ∧ ∀ i : Fin a, ¬ i.castSucc < k → p i z = 0 := fun k z hz => by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨u, -, hu, rfl⟩ := (hS k z).1 hz
      simp only [pS]
      exact ⟨trivial, hu⟩
    | zero => simp
    | add x y _ _ hx hy =>
      refine ⟨?_, fun i hi => by rw [map_add, hx.2 i hi, hy.2 i hi, add_zero]⟩
      simp only [map_add, mulVec_add, Finset.sum_add_distrib]
      rw [← hx.1, ← hy.1]
    | smul c x _ hx =>
      refine ⟨?_, fun i hi => by rw [map_smul, hx.2 i hi, smul_zero]⟩
      simp only [map_smul, mulVec_smul, ← Finset.smul_sum]
      rw [← hx.1]
  have hmono : Monotone S := fun k l hkl z hz => by
    obtain ⟨u, hu, hu0, rfl⟩ := (hS k z).1 hz
    exact (hS l _).2 ⟨u, hu, fun i hi => hu0 i fun h => hi (h.trans_le hkl), rfl⟩
  refine ⟨?_, hmono, fun i => ?_, fun k y => ⟨fun hy => ⟨?_, Submodule.subset_span hy⟩, ?_⟩, ?_⟩
  · refine eq_bot_iff.2 fun z hz => ?_
    obtain ⟨u, -, hu0, rfl⟩ := (hS 0 z).1 hz
    have : ∀ i, u i = 0 := fun i => hu0 i (by simp)
    simp [this]
  · have hsup : Submodule.span I.E (S i.succ : Set (Fin I.n → I.E)) =
        Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)) ⊔ LinearMap.range (T i).mulVecLin := by
      apply le_antisymm
      · refine Submodule.span_le.2 fun z hz => ?_
        obtain ⟨u, hu, hu0, rfl⟩ := (hS _ z).1 hz
        have e1 : ∑ k, T k *ᵥ u k = ∑ k, T k *ᵥ Function.update u i 0 k + T i *ᵥ u i := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
            ← Finset.add_sum_erase _ (fun k => T k *ᵥ Function.update u i 0 k) (Finset.mem_univ i)]
          rw [Finset.sum_congr rfl (s₁ := univ.erase i) (f := fun k => T k *ᵥ Function.update u i 0 k)
            (g := fun k => T k *ᵥ u k)
            (fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)])]
          simp [add_comm]
        rw [e1]
        refine Submodule.add_mem_sup (Submodule.subset_span ((hS _ _).2 ⟨_, fun k => ?_, fun k hk => ?_, rfl⟩))
          ⟨u i, rfl⟩
        · by_cases hki : k = i
          · subst hki; simp
          · rw [Function.update_of_ne hki]; exact hu k
        · by_cases hki : k = i
          · subst hki; simp
          · rw [Function.update_of_ne hki]
            refine hu0 k fun h => hk ?_
            rw [Fin.castSucc_lt_succ_iff] at h
            exact Fin.castSucc_lt_castSucc_iff.2 (lt_of_le_of_ne h hki)
      · refine sup_le (Submodule.span_mono (hmono (Fin.castSucc_lt_succ).le)) ?_
        rw [LinearMap.range_eq_map, ← (hΛ i).span_eq_top, Submodule.map_span]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, hx, rfl⟩
        refine (hS _ _).2 ⟨Pi.single i x, fun k => ?_, fun k hk => ?_, ?_⟩
        · by_cases hki : k = i
          · subst hki; simpa using hx
          · rw [Pi.single_eq_of_ne hki]; exact zero_mem _
        · refine Pi.single_eq_of_ne ?_ _
          rintro rfl
          exact hk Fin.castSucc_lt_succ
        · rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, mulVec_zero]) (by simp)]
          simp
    have hinf : Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)) ⊓ LinearMap.range (T i).mulVecLin = ⊥ := by
      refine eq_bot_iff.2 ?_
      rintro _ ⟨hz, x, rfl⟩
      have : x = 0 := (pT i x).symm.trans ((hsp _ _ hz).2 i (lt_irrefl _))
      simp [this]
    have hinj : Function.Injective (T i).mulVecLin := fun x y hxy => by
      rw [← pT i x, ← pT i y]; exact congrArg (p i) hxy
    have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span I.E (S i.castSucc : Set (Fin I.n → I.E)))
      (LinearMap.range (T i).mulVecLin)
    rw [hinf, ← hsup, LinearMap.finrank_range_of_inj hinj] at this
    simpa [Formalism.HN.rkK] using this
  · obtain ⟨u, hu, -, rfl⟩ := (hS k y).1 hy
    refine (hL _).2 ⟨u, 0, 0, hu, fun i t _ => by simpa using zero_mem _, zero_mem _, ?_⟩
    have : (fun l => e ((0 : Fin I₀.n → I₀.E) l)) = 0 := by ext; simp
    rw [this]
    simp
  · rintro ⟨hy, hy'⟩
    obtain ⟨u, u', y₀, hu, -, -, hz⟩ := (hL y).1 hy
    have hp : ∀ i, p i y = u i := fun i => by
      have a1 : ∀ k, p i (T' k *ᵥ u' k) = 0 := fun k => by
        simp only [p, mulVecLin_apply, mulVec_mulVec]
        rw [(h1 i k).2.1]; simp
      have a2 : ∀ x, p i (T₀ *ᵥ x) = 0 := fun x => by
        simp only [p, mulVecLin_apply, mulVec_mulVec]
        rw [(h2 i).2.2]; simp
      rw [hz, map_add, map_add, pS, a2, map_sum]
      simp [a1]
    obtain ⟨b1, b2⟩ := hsp k y hy'
    exact (hS k y).2 ⟨fun i => p i y, fun i => by simpa only [hp] using hu i, b2, b1⟩
  · intro x hx y hy
    obtain ⟨u, -, -, rfl⟩ := (hS _ x).1 hx
    obtain ⟨v, -, -, rfl⟩ := (hS _ y).1 hy
    rw [hform_eq, star_sum, sum_dotProduct]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [mulVec_sum, dotProduct_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, (h1 i k).1]
    simp

end GlobalTheory.FlagBase.AdSat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsURepOnOfIsTau
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Dec.FormF
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.PsiBound

lemma det_exp_sq {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inP ε Y) :
    (NormedSpace.exp Y).det * (NormedSpace.exp Y).det = 1 := by
  have hJ := Jm_mul_self ε
  have h1 : Jm ε * Y * Jm ε = -Y := by
    rw [Matrix.mul_assoc, h.2, Matrix.mul_neg, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
  have h2 : NormedSpace.exp (Jm ε * Y * Jm ε) = Jm ε * NormedSpace.exp Y * Jm ε :=
    Matrix.exp_units_conj (⟨Jm ε, Jm ε, hJ, hJ⟩ : (Matrix (Fin n) (Fin n) ℂ)ˣ) Y
  have h3 : (Jm ε).det * (Jm ε).det = 1 := by rw [← det_mul, hJ, det_one]
  have h4 : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl Y).neg_left, neg_add_cancel,
      NormedSpace.exp_zero]
  have h5 := congrArg Matrix.det h4
  rw [← h1, h2, det_mul, det_mul, det_mul, det_one] at h5
  linear_combination h5 - (NormedSpace.exp Y).det * (NormedSpace.exp Y).det * h3

lemma muInt_cast {n : ℕ} {lam : Fin n → ℝ} (hlam : IsHCParam lam) (a : Fin n) :
    (muInt lam a : ℝ) = lam a + Formalism.QuantumDeterminants.rhoStd n a := by
  obtain ⟨m, hm⟩ := hlam.2 a
  have : lam a + Formalism.QuantumDeterminants.rhoStd n a = ((m + n - 1 - (a : ℕ) : ℤ) : ℝ) := by
    unfold Formalism.QuantumDeterminants.rhoStd; push_cast; linarith
  unfold muInt
  rw [this, Int.floor_intCast]

lemma norm_Phi_le {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {h : ℝ}
    {X km : Matrix (Fin n) (Fin n) ℂ} (hlam : IsHCParam lam) (hgap : GapAtLeast ε lam h)
    (hX : inP ε X) (hk : km ∈ Kset ε) :
    ‖Phi lam (km⁻¹ * NormedSpace.exp X * km)‖ ≤ decHS h (rkR ε) (Real.sqrt (hs X)) := by
  obtain ⟨hpos, hle⟩ := GlobalTheory.MinorDecay.prod_leadMinor_decay n ε lam h X km hlam hgap hX hk
  obtain ⟨hY, -, hexp⟩ := GlobalTheory.MinorDecay.conj_facts hX hk
  have hsq := det_exp_sq hY
  rw [← hexp] at hsq
  have hs0 : 0 ≤ hs X := by unfold hs; positivity
  unfold decHS rkR
  rw [Real.sq_sqrt hs0]
  refine le_trans (le_of_eq ?_) hle
  set z := km⁻¹ * NormedSpace.exp X * km with hz
  have hn : ∀ l hl, ‖leadMinor z l hl‖ = (leadMinor z l hl).re := fun l hl => by
    rw [← Complex.abs_re_eq_norm.2 (hpos l hl).2, abs_of_pos (hpos l hl).1]
  unfold Phi
  rw [norm_prod]
  cases n with
  | zero => simp
  | succ m =>
    rw [Fin.prod_univ_castSucc]
    have hdet : leadMinor z ((Fin.last m).val + 1) (Fin.last m).isLt = z.det := rfl
    have hone : ‖z.det‖ = 1 := by
      have h1 := congrArg norm hsq
      rw [norm_mul, norm_one] at h1
      nlinarith [norm_nonneg z.det]
    rw [norm_zpow, hdet, hone, _root_.one_zpow, mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_zpow, hn, ← Real.rpow_intCast]
    congr 1
    have hi : (Fin.castSucc i).val + 1 < m + 1 := by simp
    unfold sInt
    rw [dif_pos hi]
    push_cast
    rw [muInt_cast hlam, muInt_cast hlam]
    unfold Formalism.QuantumDeterminants.rhoStd
    simp only [Fin.val_castSucc]
    push_cast
    have : lam (Fin.castSucc i) = lam ⟨i.val, by omega⟩ := rfl
    rw [this]
    ring

lemma weighted_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) (d : ℕ) (φ a b : α → ℂ)
    (M U V : ℝ) (hM : 0 ≤ M) (hU : 0 ≤ U) (hV : 0 ≤ V) (hφ : ∀ x, ‖φ x‖ ≤ M)
    (i1 : Integrable (fun x => ‖a x‖ ^ 2) μ) (i2 : Integrable (fun x => ‖b x‖ ^ 2) μ)
    (ha : (d : ℝ) * ∫ x, ‖a x‖ ^ 2 ∂μ = V ^ 2) (hb : (d : ℝ) * ∫ x, ‖b x‖ ^ 2 ∂μ = U ^ 2) :
    ‖(d : ℂ) * ∫ x, φ x * (a x * b x) ∂μ‖ ≤ M * U * V := by
  have key : ∀ t : ℝ, 0 < t →
      ‖(d : ℂ) * ∫ x, φ x * (a x * b x) ∂μ‖ ≤ M * (t / 2) * V ^ 2 + M * (1 / (2 * t)) * U ^ 2 := by
    intro t ht
    have hbd := norm_integral_le_of_norm_le (μ := μ) (f := fun x => φ x * (a x * b x))
      (g := fun x => M * (t / 2) * ‖a x‖ ^ 2 + M * (1 / (2 * t)) * ‖b x‖ ^ 2)
      ((i1.const_mul _).add (i2.const_mul _)) (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, norm_mul]
        have hab : ‖a x‖ * ‖b x‖ ≤ t / 2 * ‖a x‖ ^ 2 + 1 / (2 * t) * ‖b x‖ ^ 2 := by
          have : t / 2 * ‖a x‖ ^ 2 + 1 / (2 * t) * ‖b x‖ ^ 2 - ‖a x‖ * ‖b x‖ =
              (t * ‖a x‖ - ‖b x‖) ^ 2 / (2 * t) := by
            field_simp; ring
          have h2 : 0 ≤ (t * ‖a x‖ - ‖b x‖) ^ 2 / (2 * t) := by positivity
          linarith
        calc _ ≤ M * (t / 2 * ‖a x‖ ^ 2 + 1 / (2 * t) * ‖b x‖ ^ 2) :=
              mul_le_mul (hφ x) hab (by positivity) hM
          _ = _ := by ring)
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul] at hbd
    rw [norm_mul, Complex.norm_natCast]
    refine (mul_le_mul_of_nonneg_left hbd (Nat.cast_nonneg d)).trans (le_of_eq ?_)
    rw [mul_add, mul_left_comm, ha, mul_left_comm (d : ℝ), hb]
  refine le_of_forall_pos_le_add fun e he => ?_
  obtain ⟨δ, hδ, hδe⟩ : ∃ δ : ℝ, 0 < δ ∧ M * (U + V) * δ ≤ e :=
    ⟨e / (M * (U + V) + 1), by positivity, by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith⟩
  refine (key ((U + δ) / (V + δ)) (by positivity)).trans ?_
  have h1 : (U + δ) / (V + δ) / 2 * V ^ 2 ≤ (U + δ) * V / 2 := by
    rw [div_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ (U + δ) * V * δ := by positivity
    nlinarith
  have h2 : 1 / (2 * ((U + δ) / (V + δ))) * U ^ 2 ≤ (V + δ) * U / 2 := by
    have : 1 / (2 * ((U + δ) / (V + δ))) * U ^ 2 = (V + δ) * U ^ 2 / (2 * (U + δ)) := by
      field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 ≤ (V + δ) * U * δ := by positivity
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hM
  have h4 : 0 ≤ M * (U + V) * δ := by positivity
  nlinarith

section Tau

variable {n : ℕ} {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

lemma isURepOn_of_isTau (h : IsTau ε abelian₂ τ w) : IsURepOn (Kset ε) τ := by
  obtain ⟨hW, hrep, hdiff, hadj, -⟩ := h
  refine ⟨⟨hrep.1, fun a ha b hb => hrep.2 a (K_KC ha) b (K_KC hb)⟩, fun g hg v => ?_, fun v => ?_⟩
  · have h1 := hadj g (K_KC hg) v (τ g v)
    have h2 : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hg.1
    rw [← ContinuousLinearMap.comp_apply, ← hrep.2 gᴴ (K_KC (Kset_star ε hg)) g (K_KC hg), h2, hrep.1,
      ContinuousLinearMap.one_apply] at h1
    rw [@norm_eq_sqrt_re_inner ℂ, h1, ← @norm_eq_sqrt_re_inner ℂ]
  · let b := stdOrthonormalBasis ℂ W
    have e : (fun k => τ k v) = fun k => ∑ i, ⟪b i, τ k v⟫_ℂ • b i :=
      funext fun k => (b.sum_repr' _).symm
    rw [e]
    refine continuousOn_finset_sum _ fun i _ => ContinuousOn.smul ?_ continuousOn_const
    exact (hdiff (b i) v).continuousOn.mono fun k hk => K_KC hk

lemma schur_norm (h : IsTau ε abelian₂ τ w) (x : W) :
    (Module.finrank ℂ W : ℝ) * ∫ k : KG ε, ‖⟪x, τ (toMK k) w⟫_ℂ‖ ^ 2 ∂(muK ε) = ‖x‖ ^ 2 := by
  have hU := isURepOn_of_isTau h
  obtain ⟨hW, -, -, -, hirr, hw, -⟩ := h
  haveI : IsProbabilityMeasure (muK ε) := (compact_haar_holds n ε).1
  obtain ⟨c, -, hc⟩ := avgSchur n ε W τ w hW hU hirr (by rintro rfl; simp at hw)
  have h1 : Continuous (fun k : KG ε => τ (toMK k) w) :=
    (hU.2.2 w).comp_continuous (toMK_cont ε) fun k => k.2
  have hc' : ∀ y : W, ∫ k : KG ε, ⟪τ (toMK k) w, y⟫_ℂ * ⟪y, τ (toMK k) w⟫_ℂ ∂(muK ε) = c * ⟪y, y⟫_ℂ :=
    fun y => hc y (innerSL ℂ y)
  let b := stdOrthonormalBasis ℂ W
  have hd : (Module.finrank ℂ W : ℂ) * c = 1 := by
    have h2 : ∑ i, ∫ k : KG ε, ⟪τ (toMK k) w, b i⟫_ℂ * ⟪b i, τ (toMK k) w⟫_ℂ ∂(muK ε) =
        (Module.finrank ℂ W : ℂ) * c := by
      simp only [hc', inner_self_eq_norm_sq_to_K, b.orthonormal.1]
      simp
    rw [← h2, ← integral_finset_sum _ fun i _ =>
      ((h1.inner continuous_const).mul (continuous_const.inner h1)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)]
    have h3 : ∀ k : KG ε, ‖τ (toMK k) w‖ = 1 := fun k => (hU.2.1 _ k.2 w).trans hw
    simp only [b.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K, h3]
    simp
  have e : ∀ k : KG ε, ⟪τ (toMK k) w, x⟫_ℂ * ⟪x, τ (toMK k) w⟫_ℂ =
      ((‖⟪x, τ (toMK k) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [← inner_conj_symm (τ (toMK k) w) x, Complex.conj_mul']; simp
  have h4 := hc' x
  simp only [e, integral_complex_ofReal] at h4
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, h4, Complex.ofReal_natCast, ← mul_assoc, hd, one_mul, Complex.ofReal_pow]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x

lemma ps_entry (h : IsTau ε abelian₂ τ w) (lam : Fin n → ℝ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef)
    (u y : W) :
    ⟪y, ps ε lam τ w x u⟫_ℂ = (Module.finrank ℂ W : ℂ) * ∫ k : KG ε, Phi lam ((toMK k)⁻¹ * x * toMK k) *
      (⟪y, τ (toMK k) w⟫_ℂ * ⟪τ (toMK k) w, u⟫_ℂ) ∂(muK ε) := by
  haveI := h.1
  haveI := FiniteDimensional.complete ℂ W
  have hk := toMK_cont ε
  have h1 : Continuous (fun k : KG ε => τ (toMK k) w) :=
    ((isURepOn_of_isTau h).2.2 w).comp_continuous hk fun k => k.2
  have h2 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k)) := by
    have e : ∀ k : KG ε, (toMK k)⁻¹ = (toMK k)ᴴ := fun k => K_inv k.2
    simp only [e]
    unfold Phi
    refine continuous_finset_prod _ fun i _ => Continuous.zpow₀ ?_ _ fun k => Or.inl ?_
    · unfold leadMinor
      exact (((hk.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hk).matrix_submatrix
        _ _).matrix_det
    · exact ((hx.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (K_KC k.2).1)).submatrix
        (Fin.castLE_injective _)).det_pos.ne'
  have h3 : Continuous (fun k : KG ε => Phi lam ((toMK k)⁻¹ * x * toMK k) •
      (innerSL ℂ (τ (toMK k) w)).smulRight (τ (toMK k) w)) :=
    h2.smul (((ContinuousLinearMap.smulRightL ℂ W W).continuous.comp
      ((innerSL ℂ).continuous.comp h1)).clm_apply h1)
  have h4 := h3.integrable_of_hasCompactSupport (μ := muK ε) (HasCompactSupport.of_compactSpace _)
  unfold ps
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply h4,
    ← integral_inner (h4.apply_continuousLinearMap u)]
  congr 2
  funext k
  simp [inner_smul_right, mul_comm]

end Tau

end GlobalTheory.PsiBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntriesStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebra_besselModel_middleUnitary_entries : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (GG k r) ↔ (unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → unrealify x i j = 0)) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) → NormedSpace.exp (unrealify x) ∈ Formalism.FourierDecayAlt.B2.UWb k r) := by
  first | exact @GlobalTheory.CellLieAlg.lie_entries | exact GlobalTheory.CellLieAlg.lie_entries | (intros; apply GlobalTheory.CellLieAlg.lie_entries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralRadicalEqTopSectionSplitStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_radical_eq_top_section_split : ∀ (k r j : ℕ) (f : Mat k r → ℝ≥0∞), Measurable (fun x : Mt k r => f (Matrix.of x)) → ∫⁻ q : PPar k r, f (pOf k r q) = ∫⁻ q' : PSec k r j, ∫⁻ q : PTop k r j, f (pTop k r j q * pSec k r j q') := by
  first | exact @GlobalTheory.Amp.PSplit.lintegral_split | exact GlobalTheory.Amp.PSplit.lintegral_split | (intros; apply GlobalTheory.Amp.PSplit.lintegral_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LogSingularValuesEuclidNormCartanPropertiesStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logSingularValuesEuclidNorm_cartan_properties : ∀ (n : ℕ) (ε : Fin n → Bool), Continuous (fun g : UJ ε => dHS (uMat g)) ∧ (∀ g : UJ ε, 0 ≤ dHS (uMat g) ∧ dOp (uMat g) ≤ dHS (uMat g)) ∧ (∀ g : UJ ε, ∃ k ∈ Kset ε, ∃ X, inP ε X ∧ uMat g = k * NormedSpace.exp X ∧ dHS (uMat g) = Real.sqrt (hs X)) ∧ (rkR ε = 0 → ∀ g : UJ ε, dHS (uMat g) = 0) := by
  first | exact @GlobalTheory.Count.CartanSize.cartan_size | exact GlobalTheory.Count.CartanSize.cartan_size | (intros; apply GlobalTheory.Count.CartanSize.cartan_size <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeDecayGapOfCompressionFormulaGap
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.DecGapBound

theorem decGap_of_formulaGap : FormulaGap → DecGap := by
  intro hF n ε lam H _ _ σ hlam hDS h hgap hh g hg u hu v hv
  have hU := hDS.2.2.1
  have h1 : ‖⟪v, σ g u⟫_ℂ‖ ≤ decHS h (rkR ε) (dHS g) * ‖u‖ * ‖v‖ := by
    obtain ⟨k, X, hk, hX, hgk⟩ := (polar_decomposition_holds n ε).1 g hg
    have hs' := GlobalTheory.LowKProj.mem_UJset_of_Kset (Kset_star ε hk)
    have hkk : star k * k = 1 := hk.1.1
    have e1 : σ (NormedSpace.exp X) u = σ (star k) (σ g u) := by
      have h := hU.1.2 (star k) hs' g hg
      rw [show star k * g = NormedSpace.exp X by rw [hgk, ← Matrix.mul_assoc, hkk, Matrix.one_mul]] at h
      exact congrArg (fun F : H →L[ℂ] H => F u) h
    let L : H →ₗᵢ[ℂ] H := ⟨(σ (star k) : H →ₗ[ℂ] H), hU.2.1 _ hs'⟩
    have e2 : ⟪σ (star k) v, σ (star k) (σ g u)⟫_ℂ = ⟪v, σ g u⟫_ℂ := L.inner_map_map v (σ g u)
    have hb := dec_exp hF n ε lam H σ hlam hDS h hgap hh X hX u hu (σ (star k) v)
      (GlobalTheory.LowKProj.lowKSub_stable ε lam σ _ (Kset_star ε hk) v hv)
    rw [e1, e2, hU.2.1 _ hs' v, ← (GlobalTheory.Count.Cartan.cartan_distances n ε).1 k X hk hX, ← hgk] at hb
    exact hb
  refine ⟨h1, h1.trans ?_⟩
  have h0 : 0 ≤ h := le_trans (by positivity) hh
  obtain ⟨h2, h3⟩ := dOp_facts hg
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (decHS_le_decE _ h0 h2 h3) (norm_nonneg u)) (norm_nonneg v)

end GlobalTheory.DecGapBound
end

