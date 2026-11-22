import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1844
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1778
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.PieriBlockIdeals.Bundle0004
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
import Formalism.LocalToGlobal.Divisibility.Bundle0002
import Formalism.LocalToGlobal.Columns.Bundle0014
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureVanishingLatticeEqRowLatticeMatrices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0802
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesAllOfCommutesRationalUnitaryPoints
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1823
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockVanishingLevelUnitBlockMulInvStabStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockVanishingLevel_unitBlock_mul_inv_stab : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → 𝔪 ⊔ D.host.conj • 𝔪 = ⊤ → ∀ (o a d : ℕ), o + a = d → ∀ j ∈ GlobalTheory.BotPairSmall.blockJ D 𝔪 o d, ∃ k ∈ intG D a, ∀ i l, (((j : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * (unitBlock D o a d).map (inc D) - (unitBlock D o a d).map (inc D) * (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D (D.host.conj • 𝔪) := by
  first | exact @GlobalTheory.BotPairSmall.BlockK.blockJ_unitBlock | exact GlobalTheory.BotPairSmall.BlockK.blockJ_unitBlock | (intros; apply GlobalTheory.BotPairSmall.BlockK.blockJ_unitBlock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingIntegralUpToExponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BrPairLocal

theorem finLocal : ∀ {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [StarRing K] [Fintype ι] (emb : ι → E →+* K) {n N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) →
    ∀ (M : Submodule (𝓞 E) (Fin n → E)) (L : Submodule (𝓞 E) (Fin N → E)), Submodule.IsLattice E M →
    (∀ v, v ∈ L ↔ (fun k => v (Formalism.L2.Col.Br.iC hN k)) ∈ M ∧ ∃ c : 𝓞 E, (c : E) = v (Formalism.L2.Col.Br.iL hN)) →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    u ∈ nabAtr emb Λ L → v ∈ nabAtr emb (fun τ => (σ τ).dual) M →
    GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0 ∨
      -Formalism.DivisionValues.vw w (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≤
        Formalism.DivisionValues.vw w (GlobalTheory.BrPairF.brPairF σ hN Λ u v) := by
  intro E K ι _ _ _ _ _ _ emb n N hN Λ σ hI hS M L hM hL w u v hu hv
  have hLlat : Submodule.IsLattice E L := GlobalTheory.T.isLattice_of_lastCoordinate_extension hN M L hM hL
  have h1 := GlobalTheory.OntoExponentsLat.exZ_sum_smul_mem_locP_delAtr E K ι N emb Λ L hLlat w u hu
  obtain ⟨s, hs, hsu⟩ := (Formalism.L2.DIV.lc_mem_locP w _ _).1 h1
  have hdel : delAtr emb Λ L = delK Λ (fun τ => Formalism.L2.Col.Br.sumLat hN (dualFr (tauLat emb τ M)) (1 : K)) := by
    unfold delAtr
    congr 1
    funext τ
    exact GlobalTheory.T.dualLattice_embedded_lastCoordinate_sum emb hN M L hL τ
  rw [hdel] at hsu
  have h2 := GlobalTheory.BranchFormula.integrality Formalism.L2.DIV.BrJ.branching_interlacing_pairs K ι N n hN Λ σ hI hS
    (fun τ => dualFr (tauLat emb τ M)) (fun _ => 1) (fun _ => one_ne_zero) _ hsu
  have hbr : Formalism.L2.Col.Br.brAt hN Λ σ (fun _ => (1 : K)) = Formalism.L2.Col.Br.brStd hN Λ σ := by
    simp [Formalism.L2.Col.Br.brAt]
  rw [hbr] at h2
  have hy := GlobalTheory.T.adjugateSubstLinearEquiv_symm_mem_nabla emb σ M hM v hv
  have h3 := ((Formalism.L2.DIV.pairBDual E K ι n emb σ M hM _).1.1 h2) _ hy
  obtain ⟨r, hr⟩ := Submodule.mem_one.1 h3
  have key : (s : K) * (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) *
      GlobalTheory.BrPairF.brPairF σ hN Λ u v = (r : K) := by
    have e1 : (r : K) = algebraMap (𝓞 K) K r := rfl
    rw [e1, hr, GlobalTheory.BrPairF.brPairF_apply, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
      LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, LinearMap.smul_apply, LinearMap.smul_apply,
      Algebra.smul_def, Algebra.smul_def, map_pow, map_natCast, mul_assoc]
  by_cases hP : GlobalTheory.BrPairF.brPairF σ hN Λ u v = 0
  · exact Or.inl hP
  right
  have hs0 : (s : K) ≠ 0 := by
    intro h0
    apply hs
    have : s = 0 := by exact_mod_cast h0
    rw [this]
    exact w.asIdeal.zero_mem
  have hp0 : (((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : K) ^ (∑ τ, Formalism.CohomologicalDescent.LA.exZ N N le_rfl (Λ τ).natW (Formalism.EigenvalueLevelCeiling.plc w))) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Formalism.EigenvalueLevelCeiling.plc_prime w).ne_zero)
  have h4 := Formalism.DivisionValues.ReductionFirst.vw_int_nonneg w r
  rw [← key, Formalism.DivisionValues.ReductionFirst.vw_mul w (mul_ne_zero hs0 hp0) hP, Formalism.DivisionValues.ReductionFirst.vw_mul w hs0 hp0,
    Formalism.DivisionValues.ReductionFirst.vw_unit w s hs] at h4
  linarith

end GlobalTheory.BrPairLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingPairingMapExtendScalarsEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branchingPairing_map_extendScalars_embedding : ∀ {K ι : Type} [Field K] [CharZero K] [Fintype ι] (φ : K →+* ℂ) {n N : ℕ} (hN : N = n + 1)
    (Λ : ι → DomWeight N) (σ : ι → DomWeight n) (u : VV K Λ) (v : VV K fun τ => (σ τ).dual),
    φ (GlobalTheory.BrPairF.brPairF σ hN Λ u v) =
      GlobalTheory.BrPairF.brPairF σ hN Λ (GlobalTheory.CoefModel.mapVV φ Λ u) (GlobalTheory.CoefModel.mapVV φ _ v) := by
  first | exact @GlobalTheory.BrPairF.brPairF_map_descent | exact GlobalTheory.BrPairF.brPairF_map_descent | (intros; apply GlobalTheory.BrPairF.brPairF_map_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeMulOfUnipotentCoverDiscreteSubgroup
section
open scoped TensorProduct NNReal ENNReal Matrix Pointwise
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem card_le_mul_of_unip_cover : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ Γ Q : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M) (μ : Measure G) (D V W : Set G), SemiLat N M Λ ν π DN DM → Λ ≤ Γ → Λ ≤ Q → IsClosed (Q : Set G) → (∀ q ∈ Q, ∃ u ∈ N, ∃ x ∈ M, q = u * x) → (∀ K : Set G, IsCompact K → (K ∩ Γ).Finite) → μ.IsHaarMeasure → IsFundamentalDomain Λ D μ → IsCompact V → IsCompact W → ∃ B : ℝ, 0 ≤ B ∧ ∀ (a : G) (Y T : Finset G), (∀ x ∈ M, a * x = x * a) → (∀ u, u ∈ N ↔ a⁻¹ * u * a ∈ N) → (∀ y ∈ Y, y ∈ N) → (∀ u ∈ N, ∃ γ ∈ Λ, γ ∈ N ∧ ∃ y ∈ Y, ∃ w ∈ V, γ * u = y * a * w * a⁻¹) → (∀ t ∈ T, t ∈ Γ) → (∀ t ∈ T, ∀ t' ∈ T, t' * t⁻¹ ∈ Λ → t = t') → (∀ t ∈ T, ∃ q ∈ Q, ∃ w ∈ W, t = q * a * w) → (T.card : ℝ) ≤ B * Y.card := by
  intro G _ _ _ _ _ _ _ _ N M Λ Γ Q _ ν π DN DM μ D V W H hΛΓ hΛQ hQ hQd hdisc hμ hD hV hW
  haveI := H.haarN
  obtain ⟨U, hUc, hU1⟩ := exists_compact_mem_nhds (1 : G)
  have hU0 : μ U ≠ 0 := (lt_of_lt_of_le (isOpen_interior.measure_pos μ ⟨1, mem_interior_iff_mem_nhds.2 hU1⟩) (measure_mono interior_subset)).ne'
  have hUt : μ U ≠ ⊤ := hUc.measure_ne_top
  obtain ⟨k, hk⟩ := GlobalTheory.T.packing_count_inequivalent_discreteSubgroup G Γ Λ μ D U hΛΓ hdisc hμ hD hUc
  obtain ⟨B₀, hB₀t, hB₀⟩ := GlobalTheory.T.measure_translate_shell_le_div_modulus G N M Λ ν π DN DM H μ D hμ hD (W * U) (hW.mul hUc)
  have hνV : ν {u : N | (u : G) ∈ V} ≠ ⊤ :=
    (H.closedN.isClosedEmbedding_subtypeVal.isCompact_preimage hV).measure_ne_top
  have hDN0 : ν DN ≠ 0 := GlobalTheory.ResLine.Inhab.semiLat_ne_zero H
  have hDNt : ν DN ≠ ⊤ := H.finN
  refine ⟨(ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U)).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro a Y T haM haN hY hcov hTΓ hTsep hTQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.lintegral_conj_normalizer_eq_const_mul_haar G N ν a⁻¹ H.closedN H.haarN (fun u => by rw [inv_inv]; exact haN u)
  let S : Set G := (Q : Set G) * (a • (W * U))
  have hSc : IsClosed S := hQ.mul_right_of_isCompact ((hW.mul hUc).smul a)
  have hSm : MeasurableSet S := hSc.measurableSet
  have hSinv : ∀ γ ∈ Λ, ∀ x ∈ S, γ * x ∈ S := by
    intro γ hγ x hx
    obtain ⟨q, hq, y, hy, rfl⟩ := Set.mem_mul.1 hx
    exact Set.mem_mul.2 ⟨γ * q, Q.mul_mem (hΛQ hγ) hq, y, hy, mul_assoc _ _ _⟩
  have hTS : ∀ t ∈ T, ∀ u ∈ U, t * u ∈ S := by
    intro t ht u hu
    obtain ⟨q, hq, w, hw, rfl⟩ := hTQ t ht
    have hm : a • (w * u) ∈ a • (W * U) := Set.smul_mem_smul_set (Set.mul_mem_mul hw hu)
    refine Set.mem_mul.2 ⟨q, hq, a • (w * u), hm, ?_⟩
    simp only [smul_eq_mul, mul_assoc]
  have hpack := hk T S hTΓ hTsep hSm hSinv hTS
  have hshell : κ * μ (S ∩ D) ≤ B₀ := by
    refine hB₀ a⁻¹ κ (fun m hm => (show Commute a m from haM m hm).inv_left) hκ S hSm fun x hx => ?_
    obtain ⟨q, hq, y, hy, rfl⟩ := Set.mem_mul.1 hx
    obtain ⟨c, hc, rfl⟩ := Set.mem_smul_set.1 hy
    obtain ⟨u, hu, m, hm, rfl⟩ := hQd q hq
    refine ⟨a⁻¹ * u * a, (haN u).1 hu, m, hm, c, hc, ?_⟩
    have e : m * a = a * m := (haM m hm).symm
    simp only [smul_eq_mul, mul_assoc]
    rw [← mul_assoc m a c, e, mul_assoc a m c]
  have hcover := GlobalTheory.T.haar_fundDomain_le_card_mul_of_translateCover G N Λ ν DN a⁻¹ κ V Y H.haarN H.domN hV hκ hY fun u hu => by
    obtain ⟨γ, hγ, hγN, y, hy, w, hw, e⟩ := hcov u hu
    exact ⟨γ, hγ, hγN, y, hy, w, hw, by rw [inv_inv]; exact e⟩
  have key : ν DN * (T.card * μ U) ≤ Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀) := calc
    ν DN * (T.card * μ U) ≤ (Y.card * (κ * ν {u : N | (u : G) ∈ V})) * (T.card * μ U) := by gcongr
    _ = Y.card * ν {u : N | (u : G) ∈ V} * (κ * (T.card * μ U)) := by ring
    _ ≤ Y.card * ν {u : N | (u : G) ∈ V} * (κ * (k * μ (S ∩ D))) := by gcongr
    _ = Y.card * ν {u : N | (u : G) ∈ V} * k * (κ * μ (S ∩ D)) := by ring
    _ ≤ Y.card * ν {u : N | (u : G) ∈ V} * k * B₀ := by gcongr
    _ = Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀) := by ring
  have hc0 : ν DN * μ U ≠ 0 := mul_ne_zero hDN0 hU0
  have hct : ν DN * μ U ≠ ⊤ := ENNReal.mul_ne_top hDNt hUt
  have hX : ν {u : N | (u : G) ∈ V} * k * B₀ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hνV (ENNReal.natCast_ne_top k)) hB₀t
  have h1 : (T.card : ℝ≥0∞) ≤ Y.card * (ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U)) := by
    rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)]
    calc (T.card : ℝ≥0∞) * (ν DN * μ U) = ν DN * (T.card * μ U) := by ring
      _ ≤ _ := key
  have hfin : ν {u : N | (u : G) ∈ V} * k * B₀ / (ν DN * μ U) ≠ ⊤ := (ENNReal.div_lt_top hX hc0).ne
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hfin) h1
  rw [mul_comm]
  simpa [ENNReal.toReal_mul] using h2

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainFrameSignatureData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

theorem GlobalTheory.RealQuotBot.tmul_ne_zero {Pr Pf : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf] {x : Pr} {y : Pf}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Pf, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ Pr).toLinearMap ∘ₗ LinearMap.lTensor Pr φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

theorem GlobalTheory.RealQuotBot.det_unitary_ne_zero {n : ℕ} (g : Matrix.unitaryGroup (Fin n) ℂ) :
    (g : Matrix (Fin n) (Fin n) ℂ).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 g.2)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at h1
  exact zero_ne_one h1

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.RealQuotBot.real_quot_inv_equiv : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    Nontrivial Pr ∧ ∃ (n₀ : D.what₂.Tau → ℕ) (σ : (D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ) → Module.End ℂ Pr),
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A.rank) ℂ) (P : PolF D WW.rank A.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) • q P) ∧
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ) (P : PolF D WW.rank A'.rank),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) • q' P) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A.rank WW.rank n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q P)) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A'.rank WW.rank n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q' P)) := by
  intro hH hP hK hLM D ψ θ hψ hθ A A' WW FA FA' FW a b had hsA hsA' hsW hex Pr q q' hq hq' hfac
  obtain ⟨α, β, hT, hE⟩ := hex
  obtain ⟨⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩, hfac2⟩ := hfac α β hT hE
  obtain ⟨Pf, r, r', e, hr, hr', hpA, hpB⟩ := hfac2 _ _ _ _ _ _ _ hm
  have hPi : Nontrivial Pi := hm.irred.1
  have hall : ¬ ∀ z : Pr ⊗[ℂ] Pf, z = 0 := by
    intro h
    obtain ⟨z, hz⟩ := exists_ne (0 : Pi)
    exact hz (by rw [← e.apply_symm_apply z, h (e.symm z), map_zero])
  have hPr : Nontrivial Pr := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hall fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
      | add u v hu hv => rw [hu, hv, add_zero]
  have hPf : Nontrivial Pf := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hall fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
      | add u v hu hv => rw [hu, hv, add_zero]
  obtain ⟨y, hy⟩ := exists_ne (0 : Pf)
  obtain ⟨f, hf, hfy⟩ := hr y
  obtain ⟨f', hf', hfy'⟩ := hr' y
  have hf0 : f ≠ 0 := by rintro rfl; exact hy (by rw [← hfy, map_zero])
  have canc : ∀ x x' : Pr, e (x ⊗ₜ y) = e (x' ⊗ₜ y) → x = x' := by
    intro x x' h
    by_contra hne
    have h2 : (x - x') ⊗ₜ[ℂ] y = 0 := by
      rw [TensorProduct.sub_tmul]; exact sub_eq_zero.2 (e.injective h)
    exact GlobalTheory.RealQuotBot.tmul_ne_zero (sub_ne_zero.2 hne) hy h2
  have sA := fun τ => GlobalTheory.T.diagonalHermitianFrame_signs_pos_of_definite D A FA τ (hsA τ)
  have sA' := fun τ => GlobalTheory.T.diagonalHermitianFrame_signs_pos_of_definite D A' FA' τ (hsA' τ)
  have sW := fun τ => GlobalTheory.T.diagonalHermitianFrame_signs_pos_of_definite D WW FW τ (hsW τ)
  obtain ⟨hTA, hcoA, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ true A WW FA FW β (β / α) ωA b (fun τ => b τ - a τ) hm.weilA
    (fun τ => ⟨(hE τ).2, GlobalTheory.RealQuot.hasInfExp_div D α β τ (a τ) (b τ) (hE τ).1 (hE τ).2⟩) Pi rf rl p hm.mapA
  obtain ⟨hTB, hcoB, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ false A' WW FA' FW α (α / β) ωB a (fun τ => a τ - b τ) hm.weilB
    (fun τ => ⟨(hE τ).1, GlobalTheory.RealQuot.hasInfExp_div D β α τ (b τ) (a τ) (hE τ).2 (hE τ).1⟩) Pi rf rl p' hm.mapB
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.T.definiteBottomTriple_weight_natural D ψ θ A A' WW FA FW a b α β ωA hθ hsA hsW hT hE hm.weilA ⟨f, hf, hf0⟩
  have kA : GlobalTheory.RealQuot.coinv true FA FW (fun τ => b τ - a τ) ≤ LinearMap.ker q := by
    intro P hP
    have h := hcoA f hf P hP
    rw [hpA f hf P, hfy] at h
    rw [LinearMap.mem_ker]
    refine canc _ _ ?_
    rw [h, TensorProduct.zero_tmul, map_zero]
  have kB : GlobalTheory.RealQuot.coinv false FA' FW (fun τ => a τ - b τ) ≤ LinearMap.ker q' := by
    intro P hP
    have h := hcoB f' hf' P hP
    rw [hpB f' hf' P, hfy'] at h
    rw [LinearMap.mem_ker]
    refine canc _ _ ?_
    rw [h, TensorProduct.zero_tmul, map_zero]
  have hrel : ∀ P P', q P = q' P' → ∀ τ, ∀ Y ∈ lieAt WW τ,
      q (GlobalTheory.RealQuot.actT true FA FW b τ Y P) = q' (GlobalTheory.RealQuot.actT false FA' FW a τ Y P') := by
    intro P P' hPP τ Y hY
    have h1 := hTA f hf τ Y hY P
    have h2 := hTB f' hf' τ Y hY P'
    rw [hpA f hf, hpA f hf, hfy] at h1
    rw [hpB f' hf', hpB f' hf', hfy'] at h2
    refine canc _ _ ?_
    rw [h1, h2, hPP]
  have hrow := GlobalTheory.T.definite_bottom_row_transport_contragredient D A A' WW FA FA' FW b a n₀ Pr q q' sA sA' sW
    (fun τ => by
      have hc : ((A.rank : ℚ) + (A'.rank : ℚ)) = (WW.rank : ℚ) := by exact_mod_cast had
      rw [hn₀ τ, hc]) hrel
  have hdet : ∀ κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ,
      GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) ≠ 0 := by
    intro κ
    unfold GlobalTheory.MinorFrame.detChar
    exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (GlobalTheory.RealQuotBot.det_unitary_ne_zero (κ τ))
  let σ : (D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ) → Module.End ℂ Pr := fun κ =>
    if h : LinearMap.ker q ≤ LinearMap.ker (q ∘ₗ (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ).map (starRingEnd ℂ))).toLinearMap) then
      (LinearMap.ker q).liftQ _ h ∘ₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap else 0
  have hσ : ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ) P,
      σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q P) =
        q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) P) := by
    intro κ P
    have hk : LinearMap.ker q ≤ LinearMap.ker (q ∘ₗ (GlobalTheory.MinorFrame.rowSub
        (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ))).toLinearMap) := by
      intro P₀ hP₀
      rw [LinearMap.mem_ker] at hP₀ ⊢
      have h := hrow κ P₀ 0 (by rw [hP₀, map_zero])
      rw [map_zero, map_zero] at h
      exact (smul_eq_zero.1 h.symm).resolve_left (hdet κ)
    have e1 : (q.quotKerEquivOfSurjective hq).symm (q P) = Submodule.Quotient.mk P := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [σ, dif_pos hk, LinearMap.comp_apply, LinearEquiv.coe_coe, e1, Submodule.liftQ_apply, AlgHom.toLinearMap_apply]
  refine ⟨hPr, n₀, σ, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.T.columnSubstitution_unitary_of_kills_lieCoinvariants D true A WW FA FW (fun τ => b τ - a τ) n₀ Pr q sA sW (fun τ => by simp only [if_true]; exact hn₀ τ) kA
  · exact GlobalTheory.T.columnSubstitution_unitary_of_kills_lieCoinvariants D false A' WW FA' FW (fun τ => a τ - b τ) n₀ Pr q' sA' sW
      (fun τ => by simp only [Bool.false_eq_true, if_false]; rw [hn₀ τ]; ring) kB
  · intro κ P _
    rw [hσ]
  · intro κ P' _
    obtain ⟨P, hP⟩ := hq (q' P')
    rw [hrow κ P P' hP, ← hP, hσ]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureVanishingLatticeEqRowLatticeMatricesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_vanishing_lattice_eq_row_lattice_matrices : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om') (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    IsOpen (closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)))) → IsCompact (closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁)))) →
    ∃ (P : GL (Fin a') (Fv D.host.F Bs.v₁)) (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin (a + a') → Fv D.host.F Bs.v₁)),
      ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁), Y ∈ closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁))) ↔ P.val * Y ∈ matLat (Fin a') Λ := by
  first | exact @GlobalTheory.VacShapeCl.closure_Sa_eq_matLat | exact GlobalTheory.VacShapeCl.closure_Sa_eq_matLat | (intros; apply GlobalTheory.VacShapeCl.closure_Sa_eq_matLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnsMemberRowsOfLogLevelLe
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRowsTopS

theorem rowsBody_colFace : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (N : NumDatum) (X : Fields) [IsTotallyComplex X.K] (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (hX : X.Ok) (Bs : DefBase X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs N.R.r → X.K)) (mu : Bs.Tup → Tup X.F X.E X.K Sg) (cst : ∀ t, LocCst X (rowSG Pr sel (mu t))) (I : ∀ t, ChIdx X Pr N.R (QE sel (mu t : Chr X.F X.E X.K))) (hL : ∀ t, (I t).Ok Ch sel (mu t) (cst t) G (N.R.m - 2)) (hP : ∀ t, (mtildeGSD W Ch sel (mu t) (rPsymF Ch)).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (I t).β (N.R.m - 2 + 1)) (hY : ∀ t x, YbHyp (R := N.R) sel (mu t) (cst t) (I t) (wd x) (N.R.m - 2) (b t x)) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (hK : ∀ t x, KerEquivC W Ch sel (mu t) (cst t) (I t) (ambOf s B χ cD) (wd x) (N.R.m - 2) (b t x) (hY t x) (rPsymF Ch)) (hF : ∀ t x j, (chF W sel (mu t) (I t) (wd x) j).Ok) (hE : ∀ x, (evGSD W Ch sel (mu Bs.μ0) (rPsymF Ch) (wd x)).Ok) (ev : ∀ t, (Fin (Df.nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg (rPsymF Ch)) (pl : RPl N.R ≃ X.Tau) (x : Mem) (δ : Code N) (eJ : Bs.J ≃ Fin N.R.m) (R : RecNums Bs.J (RPl N.R)), HostTie N s Pr → WeightTie N W pl (wd x) δ → CharTie N s W Ch G sel → AnalyticTie D dl χ cD → mu Bs.μ0 = 1 → (cst Bs.μ0).sharp = true → FieldOfDefinition W sel (mu Bs.μ0) (cst Bs.μ0) (wd x) (ambOf s B χ cD) → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T (wd x) : ℝ) ≤ CT * N.R.m * N.sc.L → Reads N eJ δ (Pr.T (wd x)) R → C0 ≤ R.Ch → (∀ v : InfinitePlace X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W Ch sel (mu Bs.μ0) (rPsymF Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg mu cst I hL hP Mem wd b hY (kerRec mu cst I wd b hY (ambOf s B χ cD) hK) hF ev) x (memQ (A := kerRec mu cst I wd b hY (ambOf s B χ cD) hK) (hF := hF) hE (x := x)) (colsIn W Ch hX sel (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) (hL Bs.μ0) (wd x)) R ∧ ∀ v, IsUnit ((MramH W Ch hX (wd x)).X v).det := by
  intro CY CT hCT
  obtain ⟨C, hC, hker⟩ := GlobalTheory.T.kernelHalf_chainNumbers_any_levelPrime CY
  refine ⟨max (2 * (16 + CT)) (max (6 * C + 1 + 2 * C * C) (4 * C * (CT + C))), ?_⟩
  intro D N X _ s Pr W Ch G sel Sg hX Bs Df Xg mu cst I hL hP Mem wd b hY dl B χ cD hK hF hE ev pl x δ eJ R
    hHost hWt hChar hAn hmu hsharp hFD hS hR hlogT hRd hC0 hpos hev
  have hPr : Pr.Ok := hHost.2.2.2.2.2.2.2.2.2.1
  have hT : 1 ≤ Pr.T (wd x) := (hPr.T_prime _).one_le
  have hk := hker D N X s Pr W Ch G sel Sg (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) dl B χ cD pl (wd x) δ (b Bs.μ0 x) (hY Bs.μ0 x)
    (hK Bs.μ0 x) (hF Bs.μ0 x) (hE x) Bs.J eJ R hHost hWt hChar hAn hmu hsharp (hL Bs.μ0) hFD hS hR hRd
  have hl := GlobalTheory.T.lastMapHalf_recNums_of_log_levelPrime_le CY CT N X Pr W pl (wd x) δ Bs.J eJ R hWt hS hR hlogT hT hRd
  obtain ⟨hn, hA, hsz⟩ := GlobalTheory.ColRows.exists_htNums_of_kerSide_lastSide Bs.J (RPl N.R) (InfinitePlace X.K) R C CT _ _ hC hCT
    ((le_max_left _ _).trans hC0) (((le_max_left _ _).trans (le_max_right _ _)).trans hC0)
    (((le_max_right _ _).trans (le_max_right _ _)).trans hC0) hk hl
  obtain ⟨X0, hX0⟩ := GlobalTheory.ColRows.exists_isFrames X.K Bs Df hpos
  obtain ⟨hdet, hiso⟩ := GlobalTheory.ColFirstIso.colsIn_isometry X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (cst Bs.μ0) (I Bs.μ0) G _ (hL Bs.μ0)
    (wd x) (hF Bs.μ0 x 0) hmu
  have hint : ∀ τ, Br.Interlace (N_m_succ N.R) (W.lamTrue (wd x) N.R.m τ) (W.sgTrue τ) :=
    fun τ => GlobalTheory.BranchMembers.interlace W hWt.1 (wd x) τ
  have hsh : ∀ τ, Br.SameShift (W.lamTrue (wd x) N.R.m τ) (W.sgTrue τ) :=
    fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.members_sameShift W hWt.1 (wd x) τ
  have hdat := GlobalTheory.ColRows.evGSD_datFramed X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (rPsymF Ch) (wd x) (hE x)
  refine ⟨GlobalTheory.T.kerChain_matrices_with_norm_bounds X.K Bs Df (colFace hX Df Xg mu cst I hL hP Mem wd b hY (kerRec mu cst I wd b hY (ambOf s B χ cD) hK) hF ev) x
    (memQ (A := kerRec mu cst I wd b hY (ambOf s B χ cD) hK) (hF := hF) hE (x := x)) _
    (colPerL (hP Bs.μ0) Xg (wd x) (ev Bs.μ0)) (RPl N.R) R hn (fun l => (eJ l).1) X0 hdet hiso
    (fun i => GlobalTheory.FamilyFrames.famFramed_chF X hX Pr N.R W Ch sel Sg (mu Bs.μ0) (I Bs.μ0) (wd x) i (hF Bs.μ0 x i)) hdat
    (fun φ F => colPer_eq hX (hP Bs.μ0) Xg _ (hF Bs.μ0 x) (hE x) (hL Bs.μ0) (ev Bs.μ0) φ F) hX0 hsz ?_, hdet⟩
  intro v ψ F
  have hb := GlobalTheory.ColRowsTop.period_le GlobalTheory.BranchNorm.lastMapNorm hX hPr W Ch sel (mu Bs.μ0) hmu (rPsymF Ch) (wd x) hint hsh
    (hP Bs.μ0) (hE x) v ψ.1 (ev Bs.μ0 F).1.1
  rw [hA]
  exact hb.trans (mul_le_mul_of_nonneg_left (hev X0 hX0 v F)
    (mul_nonneg (Real.exp_pos _).le (GlobalTheory.ColRowsTop.ipAt_nonneg_of_datFramed hdat v ψ)))

end GlobalTheory.ColRowsTopS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutesAllOfCommutesRationalUnitaryPointsStatement
section
set_option autoImplicit false
noncomputable section
open NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutes_all_of_commutes_rationalUnitaryPoints : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (tauL : D.what₂.Tau → (D.host.E →+* D.what₂.LL)),
    (∀ τ, D.what₂.embLL.comp (tauL τ) = Formalism.BasicNotions.TH.tauE D τ) →
    ∀ (lam : D.what₂.Tau → DomWeight V.rank) (g : Module.End D.what₂.LL (VV D.what₂.LL lam)),
    (∀ (γ : GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.IsRatMat V γ γE →
      ∀ v, g (rhoVr tauL lam γE v) = rhoVr tauL lam γE (g v)) →
    ∀ (h : D.what₂.Tau → GL (Fin V.rank) D.what₂.LL) v, g (rhoK lam h v) = rhoK lam h (g v) := by
  first | exact @GlobalTheory.RatDenseEnd.comm_all | exact GlobalTheory.RatDenseEnd.comm_all | (intros; apply GlobalTheory.RatDenseEnd.comm_all <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedColumnLatticeIntegralFrameCoordsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedColumnLattice_integral_frameCoords : ∀ {D : D7} {n : ℕ} (fr : GL (Fin n) D.host.E) (y : Fin n → Lev.EAf D), y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) → ∀ i, ((Formalism.UG.bc (GlobalTheory.FrameTransport.inclEAf D) fr)⁻¹.val *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.FrameTransport.hatL_colLat_coord_int | exact GlobalTheory.FrameTransport.hatL_colLat_coord_int | (intros; apply GlobalTheory.FrameTransport.hatL_colLat_coord_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefLineBundleNumericalTheoremsProofStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nefLineBundleNumericalTheorems_proof : GlobalTheory.Published.NefNumerics := by
  first | exact @GlobalTheory.nefNumerics_outright | exact GlobalTheory.nefNumerics_outright | (intros; apply GlobalTheory.nefNumerics_outright <;> assumption)
end

