import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
import Development.AbelianVarietyTheory.Definitions.Divisors.DividedWeightUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0800
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpArchimedeanFactorContDiffOnInvertib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolConjEqOneOfMassCNeZero
section
open GlobalTheory.LKCount

namespace GlobalTheory.LKCount

theorem vol_conj_eq_one_of_massC_ne_zero {G : Type} [Group G] (Γ' T C : Subgroup G) (t : G) (ht : t ∈ T)
    (hC : C ≤ T) (h1 : C.relIndex (C.map (MulAut.conj t).toMonoidHom) ≠ 0)
    (h2 : (C.map (MulAut.conj t).toMonoidHom).relIndex C ≠ 0)
    (hf : ∀ s ∈ T, ((Γ' ⊓ C.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G).Finite)
    (hf' : ∀ s ∈ T, ((Γ' ⊓ (C.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom :
      Subgroup G) : Set G).Finite)
    (hm : massC Γ' T C ≠ 0) :
    vol C (C.map (MulAut.conj t).toMonoidHom) = 1 := by
  have hC' : C.map (MulAut.conj t).toMonoidHom ≤ T := by
    rintro x ⟨c, hc, rfl⟩
    have hcT := hC hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact T.mul_mem (T.mul_mem ht hcT) (T.inv_mem ht)
  have hchange := GlobalTheory.T.mass_mul_volume_commensurable Γ' T C (C.map (MulAut.conj t).toMonoidHom) hC hC' h1 h2 hf hf'
  rw [GlobalTheory.T.twistedCentralizerMass_map_conj Γ' T C t ht hC] at hchange
  have := mul_left_cancel₀ hm (hchange.trans (mul_one _).symm)
  exact this

end GlobalTheory.LKCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolEqIndexMulMass
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VolIndex

open GlobalTheory.Mass GlobalTheory.Mass.Levels

theorem latLev_le_range {D : D7} (V : HSp D) : latLev V ≤ (Lev.finE V).range := by
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
  obtain ⟨g, rfl⟩ := hπ.surjective b
  refine ⟨g, ?_⟩
  change Lev.finE V g =
    ((swapPts (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram (π g) : UA D.sp.cm V.gram) : GL (Fin V.rank) (Lev.EAf D))
  rw [coe_swapPts, hπ g]
  rfl

theorem vol_eq_index_mul_mass : ∀ (D : D7) (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)), V.SigOK → V.IsPosDef → K ≤ GlobalTheory.Mass.Levels.latLev V → K.relIndex (GlobalTheory.Mass.Levels.latLev V) ≠ 0 → IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) → IsMeasDef V K ν 𝓕 → (ν 𝓕).toReal = (K.relIndex (GlobalTheory.Mass.Levels.latLev V) : ℝ) * GlobalTheory.Mass.unitaryMass D.sp.cm.sig V.gram (GlobalTheory.Mass.Levels.latStab V) := by
  intro D V K ν 𝓕 hW hs hK hi ho hν
  have hd : Formalism.UG.IsTotDef D.sp.cm.sig V.gram := GlobalTheory.DefiniteQuotient.isTotDef_of_posDef V fun τ => by
    have := hW (Formalism.BasicNotions.TH.tauE D τ)
    rw [hs] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  obtain ⟨π, hπ, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  obtain ⟨hc, hL⟩ := latStab_compact_open V
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have := hν.1.1
  have h1 : ν (K.comap (Lev.finE V)) = 1 := measure_comap_finE hν.1
  have hidx : (K.comap (Lev.finE V)).relIndex ((latLev V).comap (Lev.finE V)) = K.relIndex (latLev V) := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self (latLev_le_range V)]
  have : ((K.comap (Lev.finE V)).subgroupOf ((latLev V).comap (Lev.finE V))).FiniteIndex := ⟨hidx.trans_ne hi⟩
  have h2 := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure (K.comap (Lev.finE V)) ((latLev V).comap (Lev.finE V))
    (Subgroup.comap_mono hK) ho.measurableSet ν
  rw [hidx, h1, mul_one] at h2
  have hn0 : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hi
  have hnt : ((K.relIndex (latLev V) : ℕ) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcm := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm
  have h3 := hπ.measure_toReal hcm.1 (hcm.2 V) hd hc hL (((K.relIndex (latLev V) : ℕ) : ENNReal)⁻¹ • ν)
    (by
      rw [← toLev_latLev, comap_toLev V _ hπ, Measure.smul_apply, ← h2, smul_eq_mul]
      exact ENNReal.inv_mul_cancel hn0 hnt)
    (hν.2.mono (Measure.smul_absolutelyContinuous))
  rw [← h3, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_inv_cancel_left₀ (Nat.cast_ne_zero.2 hi)]

end GlobalTheory.VolIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassModelUnitDiscriminantAwayFromP
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem sqrtNegNat_im_ne_zero {p : ℕ} (hp : 0 < p) : (sqrtNegNat p).im ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp)
  simpa [sqrtNegNat] using this.ne'

theorem modelAt_one_of_sqProd_mem : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F →
    ∀ V : ValuationSubring ℂ, V.valuation (p : ℂ) = 1 → ModelAt V F (latticeCurve L) 1 := by
  intro p F L t hp hp4 hp3 hD hQ V hVp
  have hβ : (sqrtNegNat p).im ≠ 0 := sqrtNegNat_im_ne_zero hp.pos
  have hΔF : (latticeCurve L).Δ ∈ F := by
    rw [latticeCurve_Δ]
    exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem (by simpa using (algebraMap_mem F (27 : ℚ))) (pow_mem hD.g₃_mem 2))
  obtain ⟨A, hAF, hA0, hAv⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp hp4 hp3 hD V
  obtain ⟨u, huF, hu0, huv⟩ := GlobalTheory.T.exists_valuation_pow_twelve_mul_eq p V F (latticeCurve L).Δ A (sqProd p L t) hp4 hΔF hAF hQ
    (latticeCurve_Δ_ne_zero L) hA0 hAv (GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp hp4 hp3 hD)
  rw [hVp, one_pow, mul_one] at huv
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  by_cases h2 : V.valuation (2 : ℂ) = 1
  · by_cases h3 : V.valuation (3 : ℂ) = 1
    ·
      have h6 : V.valuation (6 : ℂ) = 1 := by
        rw [show (6 : ℂ) = 2 * 3 by norm_num, map_mul, h2, h3, one_mul]
      have hj : (latticeCurve L).j ∈ V :=
        ReciprocityTheory.Gal.mem_of_isIntegral_int V (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L (sqrtNegNat p) hD.mul hβ)
      exact GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F (-L.g₂ / 4) (-L.g₃ / 4) (latticeCurve L).j u 1 hj
        (GlobalTheory.j_mul_Δ (latticeCurve L)) h6 huF hu0 (one_mem V) (by rw [map_one, mul_one]; exact huv)
    ·
      obtain ⟨N, ι, hι, T, hNodd, hN3, hNv, hcard, hT, hTor⟩ := GlobalTheory.T.exists_galoisStable_torsion_family_ker p F L t hp hp4 hp3 hD V
      have hcop : Nat.Coprime (Fintype.card ι) 3 := by
        rw [hcard]
        exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
      have hc : V.valuation (Fintype.card ι : ℂ) = 1 := by
        rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
        · exact h
        · exact absurd (by simpa using h) h3
      exact GlobalTheory.T.exists_integralModel_of_galoisStable_torsion L (sqrtNegNat p) u V N hD.mul hβ huv hNv hNodd F ι T hD.g₂_mem hD.g₃_mem huF
        hT hTor hc
  ·
    obtain ⟨-, hodd'⟩ := GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp hp4
    have hcop : Nat.Coprime (Fintype.card (Sq p)) 2 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by rcases hodd' with ⟨k, hk⟩; omega))
    have hc : V.valuation (Fintype.card (Sq p) : ℂ) = 1 := by
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V _ _ hcop with h | h
      · exact h
      · exact absurd (by simpa using h) h2
    exact GlobalTheory.T.exists_integralModel_of_galoisStable_torsion L (sqrtNegNat p) u V p hD.mul hβ huv hVp hodd F (Sq p) (sqPt p t)
      hD.g₂_mem hD.g₃_mem huF ((GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable p F L t hp hp4 hp3 hD).2 hQ)
      (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp hp4 hp3 hD).1 hc

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightDegreeDefectLeOfDividedWeightStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightDegreeDefect_le_of_divided_weight : ∀ (ι : Type) [Fintype ι] (N : ℕ) (W : GlobalTheory.MeanTop.Wts ι N) (H : ℝ), W.Hyp → W.IsDiv → (∀ τ, StrictAnti (W.u1 τ)) → (∀ τ, 0 < W.w τ) → 4 * ((W.c0 : ℝ) + 2 * N + W.T + W.Dd + 1) ≤ H → 24 * (N : ℝ) * W.T ≤ H → (∀ τ (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) = W.p → H ≤ ((W.u τ a - W.u τ b : ℤ) : ℝ)) → GlobalTheory.CompHt.rhoOf W.u' W.u1 ≤ 3 * N * ∑ τ, ((N : ℝ) * N * (2 * ((W.T : ℝ) + W.Dd + 1)) / H + 2 * N * N * W.T / W.w τ) := by
  first | exact @GlobalTheory.MeanTop.rho_div_le | exact GlobalTheory.MeanTop.rho_div_le | (intros; apply GlobalTheory.MeanTop.rho_div_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLabelAtUnfoldingStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_label_at_unfolding : ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → AlgTie T → KapIs κ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ (e : D.what₂.Tau → ℤ), (∀ ρ, (e ρ : ℚ) = (D.hc (lab σ ρ)).e i) → ∀ k (ρ : D.what₂.Tau) (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin D.R.r, laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n k τ c = wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c + e ρ := by
  first | exact @GlobalTheory.HolRead.SecWt.laU_eq_wtCol | exact GlobalTheory.HolRead.SecWt.laU_eq_wtCol | (intros; apply GlobalTheory.HolRead.SecWt.laU_eq_wtCol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpArchimedeanFactorContDiffOnInvertibStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerBumpArchimedeanFactor_contDiffOn_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (f : Lie E n → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ invSet E n → ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := by
  first | exact @GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet | exact GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet | (intros; apply GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet <;> assumption)
end

