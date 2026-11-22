import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0884
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalRingCardinality.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0819
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0834
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0830
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogRootDiscSubLogHostPrimeLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.AllWt GlobalTheory.FlatLine

namespace GlobalTheory

theorem rootDiscr_le_of_intermediateField {E : Type} [Field E] [NumberField E]
    (K : IntermediateField ℚ E) : rootDiscr K ≤ rootDiscr E := by
  have hdisc := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) E (𝓞 E)
  have hN : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact differentIdeal_ne_bot
  have htow := Module.finrank_mul_finrank ℚ K E
  set k := Module.finrank ℚ K
  set m := Module.finrank K E
  have hk : 0 < k := Module.finrank_pos
  have hm : 0 < m := Module.finrank_pos
  have ha : 0 < (discr K).natAbs := Int.natAbs_pos.mpr (discr_ne_zero K)
  have hle : (discr K).natAbs ^ m ≤ (discr E).natAbs := by
    rw [hdisc]
    exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hN)
  have hleR : ((discr K).natAbs : ℝ) ^ m ≤ ((discr E).natAbs : ℝ) := by exact_mod_cast hle
  rw [rootDiscr_def, rootDiscr_def, ← htow]
  have e1 : (((|discr K| : ℤ)) : ℝ) = ((discr K).natAbs : ℝ) := by
    rw [Nat.cast_natAbs]
  have e2 : (((|discr E| : ℤ)) : ℝ) = ((discr E).natAbs : ℝ) := by
    rw [Nat.cast_natAbs]
  rw [e1, e2]
  change _ ^ ((k : ℝ))⁻¹ ≤ _
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc ((discr K).natAbs : ℝ) ^ (k : ℝ)⁻¹
      = (((discr K).natAbs : ℝ) ^ m) ^ (((k * m : ℕ) : ℝ))⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        field_simp
    _ ≤ ((discr E).natAbs : ℝ) ^ (((k * m : ℕ) : ℝ))⁻¹ :=
        Real.rpow_le_rpow (by positivity) hleR (by positivity)

end GlobalTheory

namespace GlobalTheory

theorem abs_lrd_sub_log_d_le_lrd :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
      |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E - Real.log H.d| ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
  intro E _ _ _ H
  have hK := (rootDiscr_and_different_quadField E H).1
  have hle := rootDiscr_le_of_intermediateField (GlobalTheory.IndefiniteRowSideFullHecke.AdelicDegreeTameRamification.quadField H)
  rw [hK] at hle
  have hd1 : (1 : ℝ) ≤ H.d := by exact_mod_cast H.d_prime.one_lt.le
  have hs : 0 < √(H.d : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hlog0 : 0 ≤ Real.log H.d := Real.log_nonneg hd1
  have hlogs : Real.log √(H.d : ℝ) = Real.log H.d / 2 := by
    rw [Real.log_sqrt (by linarith)]
  have h2 : Real.log H.d / 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by
    rw [← hlogs, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd]
    exact Real.log_le_log hs hle
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGenericUnipotentCharacterEqArchMulFinite
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff

namespace GlobalTheory.WhitBump

theorem adele_eq_sInf_add_sFin {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (x : Ad E) :
    x = sInf E (pInf E x) + sFin E (pFin E x) := by
  refine Prod.ext ?_ ?_
  · change x.1 = infEq E ((infEq E).symm x.1) + 0
    simp
  · change x.2 = 0 + x.2
    simp

theorem psiN_split : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (u : GA E n), GlobalTheory.JSW.psiN u = psiInf (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) * psiFin (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
  intro E _ _ _ n u
  have h : GlobalTheory.Whittaker.superDiag u = sInf E (sdM ((GeneralLinearGroup.map (pInf E) u : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E))) + sFin E (GlobalTheory.Whittaker.superDiag (GeneralLinearGroup.map (pFin E) u)) := by
    simp only [GlobalTheory.Whittaker.superDiag, sdM, map_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact adele_eq_sInf_add_sFin _
  unfold GlobalTheory.JSW.psiN psiInf psiFin
  rw [h, AddChar.map_add_eq_mul, Circle.coe_mul]

end GlobalTheory.WhitBump
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

namespace GlobalTheory.SchwartzDecay

open NumberField.InfinitePlace.Completion

variable {F : Type} [Field F] [NumberField F] {N : ℕ}

theorem continuous_mixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem norm_le_mixed (x : InfiniteAdeleRing F) (v : InfinitePlace F) :
    ‖x v‖ ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  rcases v.isReal_or_isComplex with hv | hv
  · calc ‖x v‖ = ‖(e x).1 ⟨v, hv⟩‖ :=
          ((isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) (x v)).symm
      _ ≤ ‖e x‖ := (norm_le_pi_norm (e x).1 ⟨v, hv⟩).trans (norm_fst_le (e x))
  · calc ‖x v‖ = ‖(e x).2 ⟨v, hv⟩‖ :=
          ((isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)).symm
      _ ≤ ‖e x‖ := (norm_le_pi_norm (e x).2 ⟨v, hv⟩).trans (norm_snd_le (e x))

theorem abs_re_le (x : Ainf F) (v : InfinitePlace F) :
    |re x v| ≤ ‖InfiniteAdeleRing.ringEquiv_mixedSpace F x‖ := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [(isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (x v)]
  exact norm_le_mixed x v

theorem sz_nonneg (u : Fin N → AF F) : 0 ≤ sz u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem sz_le (u : Fin N → AF F) :
    sz u ≤ (N * Fintype.card (InfinitePlace F) : ℝ) *
      ‖fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1‖ := by
  set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1
  calc sz u ≤ ∑ _l : Fin N, ∑ _w : InfinitePlace F, ‖t‖ :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun w _ =>
          (abs_re_le (inf u l) w).trans (norm_le_pi_norm t l)
    _ = _ := by simp [mul_assoc]

theorem decay_add {Φ Ψ : (Fin N → AF F) → ℂ} (h : Decay Φ) (h' : Decay Ψ) : Decay (Φ + Ψ) := by
  obtain ⟨hc, ⟨K, hK, hK0⟩, hd⟩ := h
  obtain ⟨hc', ⟨K', hK', hK0'⟩, hd'⟩ := h'
  refine ⟨hc.add hc', ⟨K ∪ K', hK.union hK', fun u hu => ?_⟩, fun k => ?_⟩
  · rw [Set.mem_union, not_or] at hu
    simp [hK0 u hu.1, hK0' u hu.2]
  · obtain ⟨C, hC⟩ := hd k
    obtain ⟨C', hC'⟩ := hd' k
    refine ⟨C + C', fun u => ?_⟩
    have h0 : 0 ≤ (1 + sz u) ^ k := pow_nonneg (by linarith [sz_nonneg u]) k
    calc ‖(Φ + Ψ) u‖ * (1 + sz u) ^ k ≤ (‖Φ u‖ + ‖Ψ u‖) * (1 + sz u) ^ k :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) h0
      _ ≤ C + C' := by rw [add_mul]; exact add_le_add (hC u) (hC' u)

theorem decay_smul (a : ℂ) {Φ : (Fin N → AF F) → ℂ} (h : Decay Φ) : Decay (a • Φ) := by
  obtain ⟨hc, ⟨K, hK, hK0⟩, hd⟩ := h
  refine ⟨hc.const_smul a, ⟨K, hK, fun u hu => by simp [hK0 u hu]⟩, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hd k
  refine ⟨‖a‖ * C, fun u => ?_⟩
  rw [Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hC u) (norm_nonneg a)

theorem schwartz_bound {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : SchwartzMap V ℂ) (k : ℕ) :
    ∃ C : ℝ, ∀ t, (1 + ‖t‖) ^ k * ‖f t‖ ≤ C := by
  have := fun t => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl f t
  simp only [norm_iteratedFDeriv_zero] at this
  exact ⟨_, this⟩

theorem decay_pure (f : SchwartzMap (Fin N → mixedEmbedding.mixedSpace F) ℂ) (g : (Fin N → Af F) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin N → Af F)) : Decay (GlobalTheory.WeilM.pureA F f g) := by
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ⟨tsupport g, hg2, fun u hu => ?_⟩, fun k => ?_⟩
  · refine Continuous.mul (f.continuous.comp (continuous_pi fun i => ?_))
      (hg1.continuous.comp (continuous_pi fun i => ?_))
    · exact continuous_mixed.comp (continuous_fst.comp (continuous_apply i))
    · exact continuous_snd.comp (continuous_apply i)
  · exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hu)
  · obtain ⟨B, hB⟩ := hg1.continuous.bounded_above_of_compact_support hg2
    obtain ⟨C, hC⟩ := schwartz_bound f k
    set c : ℝ := N * Fintype.card (InfinitePlace F)
    have hc : 0 ≤ c := by positivity
    refine ⟨(1 + c) ^ k * C * B, fun u => ?_⟩
    set t : Fin N → mixedEmbedding.mixedSpace F := fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (u i).1
    have h1 : 1 + sz u ≤ (1 + c) * (1 + ‖t‖) := by
      have : sz u ≤ c * ‖t‖ := sz_le u
      nlinarith [norm_nonneg t]
    have h2 : (1 + sz u) ^ k ≤ (1 + c) ^ k * (1 + ‖t‖) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith [sz_nonneg u]) h1 k
    have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
    calc ‖GlobalTheory.WeilM.pureA F f g u‖ * (1 + sz u) ^ k
        = ‖f t‖ * ‖g fun i => (u i).2‖ * (1 + sz u) ^ k := by rw [← norm_mul]; rfl
      _ ≤ ‖f t‖ * ‖g fun i => (u i).2‖ * ((1 + c) ^ k * (1 + ‖t‖) ^ k) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 + c) ^ k * ((1 + ‖t‖) ^ k * ‖f t‖) * ‖g fun i => (u i).2‖ := by ring
      _ ≤ (1 + c) ^ k * C * B :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hC t) (by positivity)) (hB _) (norm_nonneg _) (by positivity)

theorem decay_of_mem_schA (F : Type) [Field F] [NumberField F] (N : ℕ) :
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Decay Φ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact decay_pure f g hg
  | zero => exact decay_zero
  | add x y _ _ hx hy => exact decay_add hx hy
  | smul a x _ hx => exact decay_smul a hx

end GlobalTheory.SchwartzDecay
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSymplecticFormRealOneParamLineEqZero
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.ThetaTransform
open scoped Matrix Classical

noncomputable section

namespace GlobalTheory.ThetaTransform

theorem symV_realLine_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ), IsTotallyReal F →
    ∀ M : ℝ →+ VA F N, IsRealLine M → ∀ t s : ℝ, symV (M t) (M s) = 0 := by
  intro F _ _ N hF M hM t s

  let φ : InfinitePlace F → AF F →+* ℝ := fun w =>
    (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).comp
      ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp (fstA F).toRingHom)
  have hφ : ∀ w (x : AF F), φ w x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)
      (x.1 w) := fun _ _ => rfl
  have hcont : ∀ w (g : ℝ → AF F), Continuous g → Continuous fun r => φ w (g r) := by
    intro w g hg
    simp only [hφ]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (hF.isReal w)).continuous.comp
      ((continuous_apply w).comp (continuous_fst.comp hg))
  have lin : ∀ (p : VA F N →+ AF F), Continuous p → ∀ w r, φ w (p (M r)) = r * φ w (p (M 1)) := by
    intro p hp w r
    let f : ℝ →+ ℝ := ((φ w).toAddMonoidHom.comp p).comp M
    have hc : Continuous f := hcont w (fun r => p (M r)) (hp.comp hM.1)
    have := map_real_smul f hc r 1
    simpa [f] using this
  have p1 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.fst _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_fst
  have p2 : ∀ l : Fin N, Continuous ((LinearMap.proj l : (Fin N → AF F) →ₗ[ℤ] AF F).toAddMonoidHom.comp
      (AddMonoidHom.snd _ _) : VA F N →+ AF F) := fun l =>
    (continuous_apply l).comp continuous_snd
  have k1 : ∀ l w r, φ w ((M r).1 l) = r * φ w ((M 1).1 l) := fun l w r => lin _ (p1 l) w r
  have k2 : ∀ l w r, φ w ((M r).2 l) = r * φ w ((M 1).2 l) := fun l w r => lin _ (p2 l) w r
  have hfst : fstA F (symV (M t) (M s)) = 0 := by
    funext w
    apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal (hF.isReal w)).injective
    have h : φ w (symV (M t) (M s)) = 0 := by
      simp only [symV, dotProduct, map_sub, map_sum, map_mul]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [k1 l w t, k1 l w s, k2 l w t, k2 l w s]
      ring
    exact h.trans (map_zero _).symm
  have h0 : ∀ r l, sndA F ((M r).1 l) = 0 ∧ sndA F ((M r).2 l) = 0 := fun r l =>
    ⟨congrFun (hM.2 r).1 l, congrFun (hM.2 r).2 l⟩
  have hsnd : sndA F (symV (M t) (M s)) = 0 := by
    simp only [symV, dotProduct, map_sub, map_sum, map_mul, (h0 _ _).1, (h0 _ _).2, zero_mul,
      Finset.sum_const_zero, sub_zero]
  exact Prod.ext hfst hsnd

end GlobalTheory.ThetaTransform
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleComplementTwoAlongFamily
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

theorem familySecondComplementInputs_of_tuSize_of_dGamSize : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm →
    Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm := by
  intro eps Fm h0 h1 hT hG
  obtain ⟨Cdeg, xd, -, hdeg⟩ := GlobalTheory.T.exists_degreeCountBound_of_eps_lt_one_div_52 Fm h0 h1
  obtain ⟨Cg, xg, hCg, hsz⟩ := GlobalTheory.T.typePrime_sizes_le_budget_family Fm h0 h1 hG Cdeg
  obtain ⟨CT, xT, -, hoT⟩ := GlobalTheory.T.admissible_off_type_family_bound Fm h0 h1 hT
  obtain ⟨CG, xG, -, hoG⟩ := GlobalTheory.T.exists_const_stabiliserLog_bound_along_family Fm h0 h1 hT hG
  obtain ⟨Cd, xD, -, hoD⟩ := GlobalTheory.T.offDiagonalRamified_bound_along_family' Fm h0 h1
  obtain ⟨CI, xI, -, hoI⟩ := GlobalTheory.T.inertPrimeLossBound_eventually Fm h0 h1
  refine ⟨Cdeg, Cg, CT, CG, Cd, CI, max xd (max xg (max xT (max xG (max xD xI)))), hCg, ?_⟩
  intro x hx0 hx i
  have a1 : xd ≤ x := (le_max_left _ _).trans hx0
  have r1 := (le_max_right _ _).trans hx0
  have a2 : xg ≤ x := (le_max_left _ _).trans r1
  have r2 := (le_max_right _ _).trans r1
  have a3 : xT ≤ x := (le_max_left _ _).trans r2
  have r3 := (le_max_right _ _).trans r2
  have a4 : xG ≤ x := (le_max_left _ _).trans r3
  have r4 := (le_max_right _ _).trans r3
  have a5 : xD ≤ x := (le_max_left _ _).trans r4
  have a6 : xI ≤ x := (le_max_right _ _).trans r4
  exact ⟨fun u j h => (Fm.D x i).T_ne_g u j h.symm, GlobalTheory.T.normDecompositionCond_famP Fm x hx i, hdeg x a1 hx i, hsz x a2 hx i,
    hoT x a3 hx i, hoG x a4 hx i, hoD x a5 hx i, hoI x a6 hx i⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSmoothKernelRepresentation
section
noncomputable section

open Classical MeasureTheory NumberField Topology

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def unitOrOne (x : Lie E a) : GL (Fin a) (Cinf E) :=
  if h : IsUnit (Matrix.of x) then h.unit else 1

theorem unitOrOne_val (x : Lie E a) :
    (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E)) = (invSet E a).piecewise (fun y => Matrix.of y) (fun _ => 1) x := by
  by_cases hx : x ∈ invSet E a
  · rw [Set.piecewise_eq_of_mem _ _ _ hx, unitOrOne, dif_pos (show IsUnit (Matrix.of x) from hx)]; rfl
  · rw [Set.piecewise_eq_of_notMem _ _ _ hx, unitOrOne, dif_neg (show ¬ IsUnit (Matrix.of x) from hx)]; rfl

theorem measurable_unitOrOne : Measurable fun x : Lie E a => (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E)) := by
  have e : (fun x : Lie E a => (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E))) =
      (invSet E a).piecewise (fun y => Matrix.of y) (fun _ => 1) := funext unitOrOne_val
  rw [e]
  exact Measurable.piecewise isOpen_invSet.measurableSet measurable_id measurable_const

theorem continuousAt_height_unitOrOne {x : Lie E a} (hx : x ∈ invSet E a) :
    ContinuousAt (fun y : Lie E a => height (unitOrOne y)) x := by
  have hev : (fun y : Lie E a => height (unitOrOne y)) =ᶠ[𝓝 x]
      fun y => 1 + ‖y‖ + ‖toL ((Matrix.of y)⁻¹)‖ := by
    filter_upwards [isOpen_invSet.mem_nhds hx] with y hy
    have h1 : ((unitOrOne y : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = Matrix.of y := by
      rw [unitOrOne, dif_pos (show IsUnit (Matrix.of y) from hy)]; rfl
    have h2 : (((unitOrOne y)⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = (Matrix.of y)⁻¹ := by
      rw [Matrix.coe_units_inv, h1]
    simp only [height, h1, h2]
    rfl
  refine ContinuousAt.congr ?_ hev.symm
  have hinv : ContinuousAt (fun y : Matrix (Fin a) (Fin a) (Cinf E) => y⁻¹) (Matrix.of x) := by
    refine continuousAt_matrix_inv _ ?_
    have hu : IsUnit (Matrix.of x).det := (Matrix.isUnit_iff_isUnit_det _).1 hx
    rw [← hu.unit_spec]
    exact NormedRing.inverse_continuousAt hu.unit
  exact (continuousAt_const.add continuousAt_id.norm).add (hinv.comp (f := fun y : Lie E a => Matrix.of y)
    continuousAt_id).norm

theorem IsTestInf.isRapidInf {f : Lie E a → ℂ} (hf : IsTestInf f) :
    IsRapidInf (volume : Measure (Lie E a)) f unitOrOne := by
  refine ⟨hf.1.continuous.measurable, measurable_unitOrOne, fun N => ?_⟩
  have hc : Continuous fun x => ‖f x‖ * height (unitOrOne x) ^ N := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ tsupport f
    · exact hf.1.continuous.continuousAt.norm.mul ((continuousAt_height_unitOrOne (hf.2.2 hx)).pow N)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]
  have hs : HasCompactSupport fun x => ‖f x‖ * height (unitOrOne x) ^ N :=
    hf.2.1.norm.mul_right
  exact hc.integrable_of_hasCompactSupport hs

theorem isRapidInf_and_smoothInf_eq_kerInf :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (f : Lie E a → ℂ), IsTestInf f →
      IsRapidInf (volume : Measure (Lie E a)) f (fun x : Lie E a =>
        if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (Cinf E))) ∧
      ∀ F : GA E a → ℂ, smoothInf f F = kerInf (volume : Measure (Lie E a)) f (fun x : Lie E a =>
        if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (Cinf E))) F := by
  intro E _ _ _ a f hf
  refine ⟨hf.isRapidInf, fun F => funext fun g => ?_⟩
  simp only [smoothInf, kerInf]
  congr 1
  funext x
  by_cases hx : IsUnit (Matrix.of x)
  · rw [chart, dif_pos hx, dif_pos hx]
  · have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hf.2.2 h)
    simp [h0]

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSpecDecomp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.SpecBC

theorem baseChange_specDecomp : ∀ (g a m : ℕ) (O : Type) [CommRing O] (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (χ : Fin a → (O →+* ℂ)) (ω : O) (l l' : ℂ) (E : Fin a → Matrix (Fin g) (Fin g) ℂ), l ≠ l' → (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → (∀ i, E i * E i = E i) → (∀ i, (E i).trace = (m : ℂ)) → (∀ i c, ρ c * E i = χ i c • E i) → (∀ i c, E i * ρ c = χ i c • E i) → (l - l') • ∑ i, E i = ρ ω - l' • (1 : Matrix (Fin g) (Fin g) ℂ) → (∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'), (ρ ω).map j *ᵥ x = j l • x → ∃ y : Fin a → Fin g → R', (∀ i c, (ρ c).map j *ᵥ y i = j (χ i c) • y i) ∧ x = ∑ i, y i) ∧ ∀ (k : Type) [Field k] (j : ℂ →+* k) (i : Fin a), χ i ω = l → Module.finrank k (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) : Submodule k (Fin g → k)) = m := by
  intro g a m O _ ρ χ ω l l' E hll hsep hidem htr hrE hEr hsum
  have hsm : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (r : ℂ) (M : Matrix (Fin g) (Fin g) ℂ),
      (r • M).map j = j r • M.map j := by
    intro R' _ j r M; ext; simp
  have hmul : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (M N : Matrix (Fin g) (Fin g) ℂ),
      (M * N).map j = M.map j * N.map j := by
    intro R' _ j M N; exact Matrix.map_mul

  have hrel : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'),
      j (l - l') • ∑ i, (E i).map j *ᵥ x = (ρ ω).map j *ᵥ x - j l' • x := by
    intro R' _ j x
    have h := congrArg (fun M => (RingHom.mapMatrix j M) *ᵥ x) hsum
    simp only [RingHom.mapMatrix_apply] at h
    have hs : (∑ i, E i).map j = ∑ i, (E i).map j := by ext; simp [Matrix.sum_apply]
    rw [hsm, hs, Matrix.smul_mulVec, Matrix.sum_mulVec] at h
    rw [h, Matrix.map_sub _ (map_sub j), Matrix.sub_mulVec, hsm, Matrix.smul_mulVec, Matrix.map_one _ (map_zero j) (map_one j),
      Matrix.one_mulVec]
  refine ⟨fun R' _ j x hx => ?_, fun k _ j i hi => ?_⟩
  · refine ⟨fun i => (E i).map j *ᵥ x, fun i c => ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    · have hu : IsUnit (j (l - l')) := (sub_ne_zero.mpr hll).isUnit.map j
      have h := hrel R' j x
      rw [hx, ← sub_smul, ← map_sub] at h
      exact (hu.smul_left_cancel.mp h).symm
  · have hj : ∀ z : ℂ, z ≠ 0 → j z ≠ 0 := fun z hz => (hz.isUnit.map j).ne_zero
    have hK : (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) :
        Submodule k (Fin g → k)) = LinearMap.range (Matrix.mulVecLin ((E i).map j)) := by
      ext y
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range]
      constructor
      · intro hy
        refine ⟨y, ?_⟩
        have hz : ∀ i', i' ≠ i → (E i').map j *ᵥ y = 0 := by
          intro i' hne
          obtain ⟨c, hc⟩ := hsep i' i hne
          have h1 : (E i').map j *ᵥ ((ρ c).map j *ᵥ y) = j (χ i' c) • ((E i').map j *ᵥ y) := by
            rw [Matrix.mulVec_mulVec, ← hmul, hEr, hsm, Matrix.smul_mulVec]
          rw [hy c, Matrix.mulVec_smul] at h1
          have h2 : (j (χ i' c) - j (χ i c)) • ((E i').map j *ᵥ y) = 0 := by
            rw [sub_smul, ← h1, sub_self]
          rw [← map_sub] at h2
          exact (smul_eq_zero.mp h2).resolve_left (hj _ (sub_ne_zero.mpr hc))
        have h := hrel k j y
        rw [hy ω, hi, ← sub_smul, ← map_sub,
          Finset.sum_eq_single i (fun b _ hb => hz b hb) (by simp)] at h
        exact smul_right_injective _ (hj _ (sub_ne_zero.mpr hll)) h
      · rintro ⟨z, rfl⟩ c
        rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    rw [hK]
    have hPP : (E i).map j * (E i).map j = (E i).map j := by rw [← hmul, hidem]
    have he : IsIdempotentElem (Matrix.mulVecLin ((E i).map j)) := by
      unfold IsIdempotentElem
      rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hPP]
    have h1 := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
    rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin g)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at h1
    have htj : ((E i).map j).trace = j (E i).trace := by
      simp [Matrix.trace, map_sum]
    rw [htj, htr, map_natCast] at h1
    haveI : CharZero k := (RingHom.charZero_iff j.injective).1 inferInstance
    exact_mod_cast h1.symm

end GlobalTheory.SpecBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumMetricEqGramAtInfinitePlaceStatement
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSumMetric_eq_gram_at_infinitePlace : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] (T : Formalism.L2.Col.GSD K) (h : T.Ok), T.Rat → ∀ (v : InfinitePlace K) (φ : T.EqFun), T.ipAt h v φ.1 φ.1 = star (fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) ⬝ᵥ ((T.toCSD h).H.map v.embedding *ᵥ fun i => v.embedding ((T.toCSD h).basis.equivFun (T.res h φ) i)) := by
  first | exact @GlobalTheory.ClassSumCoord.ipAt_eq_gram | exact GlobalTheory.ClassSumCoord.ipAt_eq_gram | (intros; apply GlobalTheory.ClassSumCoord.ipAt_eq_gram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeUnitPhaseProdEqOneOfCongruentOneStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmType_unit_phase_prod_eq_one_of_congruent_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsCMField E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (q : ℕ), q.Prime → 2 < q → ¬ q ∣ Nat.card (Units.torsion E) → ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} → ∏ w : InfinitePlace F, ((emb w).1 ((u : 𝓞 E) : E) / ((‖(emb w).1 ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.weil_unit_phase_prod | exact GlobalTheory.weil_unit_phase_prod | (intros; apply GlobalTheory.weil_unit_phase_prod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocompactLatticeUnitCovolumeStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocompact_lattice_unit_covolume : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ : Γ, γ • g ∈ K) → ∃ (μ : Measure G) (𝓕 : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1 := by
  first | exact @GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one | exact GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one | (intros; apply GlobalTheory.HaarFundDom.exists_haar_fundDom_mass_one <;> assumption)
end

