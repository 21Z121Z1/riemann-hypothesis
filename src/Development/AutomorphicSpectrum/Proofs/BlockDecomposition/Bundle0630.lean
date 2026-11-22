import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0603
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0604
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensitiesProductConverges
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalScalingMeasureByUnit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0605
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0572

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFourierTransformIdentity
section
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFFour

open Ad3 Ad3.LFS Topology

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_ball_subset {ι : Type} [Fintype ι] {U : Set (ι → F)} (hU : U ∈ 𝓝 (0 : ι → F)) :
    ∃ n : ℤ, ∀ x : ι → F, (∀ i, x i ∈ valBall F n) → x ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, -, t, ht, hsub⟩ := hU
  have ht' : ∀ i, t i ∈ 𝓝 (0 : F) := fun i ↦ by simpa using ht i
  choose n hn using fun i ↦ (hasBasis_nhds_zero_valBall (K := F)).mem_iff.1 (ht' i)
  obtain ⟨N, hN⟩ := (Finset.univ.image n).exists_le
  refine ⟨N, fun x hx ↦ hsub fun i _ ↦ (hn i).2 ?_⟩
  exact valBall_antitone (hN _ (Finset.mem_image_of_mem n (Finset.mem_univ i))) (hx i)

def bx (ι : Type) (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℤ) : Set (ι → F) :=
  Set.pi Set.univ fun _ ↦ (valBall F n : Set F)

theorem mem_bx {ι : Type} {n : ℤ} {x : ι → F} : x ∈ bx ι F n ↔ ∀ i, x i ∈ valBall F n := by
  simp [bx, Set.mem_univ_pi]

theorem isOpen_bx {ι : Type} [Fintype ι] (n : ℤ) : IsOpen (bx ι F n) :=
  isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_valBall n

theorem exists_invariant {ι : Type} [Fintype ι] {Φ : (ι → F) → ℂ} (hlc : IsLocallyConstant Φ)
    (hcs : HasCompactSupport Φ) :
    ∃ N M : ℤ, (∀ x h, (∀ i, h i ∈ valBall F N) → Φ (x + h) = Φ x) ∧
      ∀ x, Φ x ≠ 0 → ∀ i, x i ∈ valBall F M := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, tsupport Φ ⊆ bx ι F (-(m : ℤ)) := by
    refine hcs.isCompact.elim_directed_cover (fun m : ℕ ↦ bx ι F (-(m : ℤ)))
      (fun m ↦ isOpen_bx _) ?_ ?_
    · intro x _
      simp only [Set.mem_iUnion]
      choose a ha using fun i ↦ exists_mem_valBall_neg_nat (x i)
      refine ⟨Finset.univ.sup a, mem_bx.2 fun i ↦ valBall_antitone ?_ (ha i)⟩
      have : a i ≤ Finset.univ.sup a := Finset.le_sup (Finset.mem_univ i)
      omega
    · exact Monotone.directed_le fun a b hab x hx ↦
        mem_bx.2 fun i ↦ valBall_antitone (by omega) (mem_bx.1 hx i)
  have hloc : ∀ x : ι → F, ∃ n : ℤ, ∀ h, (∀ i, h i ∈ valBall F n) → Φ (x + h) = Φ x := by
    intro x
    have ho : IsOpen {h : ι → F | Φ (x + h) = Φ x} :=
      (hlc.isOpen_fiber (Φ x)).preimage (continuous_const.add continuous_id)
    obtain ⟨n, hn⟩ := exists_ball_subset (ho.mem_nhds (by simp))
    exact ⟨n, fun h hh ↦ hn h hh⟩
  choose n hn using hloc
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover
    (fun x ↦ {z : ι → F | z - x ∈ bx ι F (n x)})
    (fun x _ ↦ ((isOpen_bx _).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp [mem_bx, zero_mem]))
  obtain ⟨N₀, hN⟩ := (t.image n).exists_le
  have hval : ∀ y ∈ tsupport Φ, ∀ h, (∀ i, h i ∈ valBall F N₀) → Φ (y + h) = Φ y := by
    intro y hy h hh
    have := ht hy
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hyx⟩ := this
    have hyx' := mem_bx.1 hyx
    have hN' : ∀ i, h i ∈ valBall F (n x) := fun i ↦
      valBall_antitone (hN _ (Finset.mem_image_of_mem n hxt)) (hh i)
    have e1 : Φ y = Φ x := by
      have := hn x (y - x) hyx'
      rwa [add_sub_cancel] at this
    have e2 : Φ (y + h) = Φ x := by
      have := hn x (y + h - x) (fun i ↦ by
        rw [show (y + h - x) i = (y - x) i + h i by simp; abel]
        exact add_mem (hyx' i) (hN' i))
      rwa [add_sub_cancel] at this
    rw [e1, e2]
  refine ⟨N₀, -(m : ℤ), fun y h hh ↦ ?_, fun x hx ↦ mem_bx.1 (hm (subset_tsupport Φ hx))⟩
  by_cases hy : y ∈ tsupport Φ
  · exact hval y hy h hh
  by_cases hyh : y + h ∈ tsupport Φ
  · have := hval (y + h) hyh (-h) (fun i ↦ by simpa using neg_mem (hh i))
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

def mh : (Fin 2 × Fin 3 → F) ≃ₜ Matrix (Fin 2) (Fin 3) F where
  toFun f := Matrix.of fun i j ↦ f (i, j)
  invFun X p := X p.1 p.2
  left_inv f := rfl
  right_inv X := rfl
  continuous_toFun := continuous_matrix fun i j ↦ continuous_apply (i, j)
  continuous_invFun := continuous_pi fun p ↦ continuous_id.matrix_elem p.1 p.2

theorem exists_invariant_matrix {Φ : Matrix (Fin 2) (Fin 3) F → ℂ}
    (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) :
    ∃ N M : ℤ, (∀ X Y : Matrix (Fin 2) (Fin 3) F, (∀ a b, Y a b ∈ valBall F N) → Φ (X + Y) = Φ X) ∧
      ∀ X, Φ X ≠ 0 → ∀ a b, X a b ∈ valBall F M := by
  obtain ⟨N, M, h1, h2⟩ := exists_invariant (Φ := Φ ∘ (mh (F := F)))
    (hlc.comp_continuous (mh (F := F)).continuous) (hcs.comp_homeomorph (mh (F := F)))
  refine ⟨N, M, fun X Y hY ↦ ?_, fun X hX a b ↦ ?_⟩
  · exact h1 (mh.symm X) (mh.symm Y) (fun p ↦ hY p.1 p.2)
  · exact h2 (mh.symm X) (by simpa using hX) (a, b)

theorem modulus_le_zpow_of_mem {M : ℤ} {x : F} (hx : x ∈ valBall F M) :
    (GroundTheory.LocalField.modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (-M) := by
  have hq : (1 : ℝ) ≤ residueCard F := by exact_mod_cast one_lt_residueCard.le
  by_cases h0 : x = 0
  · subst h0
    simp only [modulus_zero, NNReal.coe_zero]
    positivity
  rw [modulus_of_ne_zero h0, NNReal.coe_zpow, NNReal.coe_natCast]
  exact zpow_le_zpow_right₀ hq (by have := (mem_valBall_iff_le_ord h0).mp hx; omega)

theorem column_three_add (k : Matrix (Fin 2) (Fin 2) F) (y e : Fin 2 → F) :
    col3 k (y + e) = col3 k y + col3 0 e := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [col3]

theorem three_column_matrix_last (k : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) (a : Fin 2) :
    col3 k y a 2 = y a := by
  fin_cases a <;> simp [col3]

theorem three_column_matrix_left (k : Matrix (Fin 2) (Fin 2) F) (y : Fin 2 → F) (a b : Fin 2) :
    col3 k y a b.castSucc = k a b := by
  fin_cases a <;> fin_cases b <;> simp [col3]

theorem three_column_zero_mem_ball {N : ℤ} (e : Fin 2 → F) (he : ∀ a, e a ∈ valBall F N) (a : Fin 2) (b : Fin 3) :
    col3 (0 : Matrix (Fin 2) (Fin 2) F) e a b ∈ valBall F N := by
  have h0 : (0 : F) ∈ valBall F N := zero_mem _
  have h1 := he 0
  have h2 := he 1
  fin_cases a <;> fin_cases b <;> simpa [col3] using (by assumption)

variable [MeasurableSpace F] [BorelSpace F]

theorem pft_eq_mul (ψ : AddChar F Circle) {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} {N : ℤ}
    (hinv : ∀ X Y : Matrix (Fin 2) (Fin 3) F, (∀ a b, Y a b ∈ valBall F N) → Φ (X + Y) = Φ X)
    (k : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) (j : Fin 2) {c : F} (hc : c ∈ valBall F N) :
    pft ψ Φ k ξ = (ψ (-(ξ j * c)) : ℂ) * pft ψ Φ k ξ := by
  have hv : (vol2 ψ).IsAddHaarMeasure := by unfold vol2; infer_instance
  have hmem : ∀ a b, col3 (0 : Matrix (Fin 2) (Fin 2) F) (Pi.single j c) a b ∈ valBall F N :=
    three_column_zero_mem_ball _ fun a ↦ by
      rw [Pi.single_apply]
      split_ifs
      · exact hc
      · exact zero_mem _
  have h := integral_add_right_eq_self (μ := vol2 ψ)
    (fun y ↦ Φ (col3 k y) * (ψ (-(∑ j, ξ j * y j)) : ℂ)) (Pi.single j c)
  unfold pft
  rw [← integral_const_mul, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  have e1 : ∑ i, ξ i * (y + (Pi.single j c : Fin 2 → F)) i = ∑ i, ξ i * y i + ξ j * c := by
    simp [mul_add, Finset.sum_add_distrib, Pi.single_apply]
  show Φ (col3 k (y + (Pi.single j c : Fin 2 → F))) *
    (ψ (-(∑ i, ξ i * (y + (Pi.single j c : Fin 2 → F)) i)) : ℂ) = _
  rw [column_three_add, hinv _ _ hmem, e1, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  ring

theorem norm_pft_le (ψ : AddChar F Circle) {Φ : Matrix (Fin 2) (Fin 3) F → ℂ} {M : ℤ} {B : ℝ}
    (hB : ∀ X, ‖Φ X‖ ≤ B) (hs : ∀ X, Φ X ≠ 0 → ∀ a b, X a b ∈ valBall F M)
    (k : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F) :
    ‖pft ψ Φ k ξ‖ ≤ (vol2 ψ).real (bx (Fin 2) F M) * B := by
  have hv : (vol2 ψ).IsAddHaarMeasure := by unfold vol2; infer_instance
  have hS : MeasurableSet (bx (Fin 2) F M) :=
    MeasurableSet.univ_pi fun _ ↦ (isClosed_valBall M).measurableSet
  have hfin : vol2 ψ (bx (Fin 2) F M) ≠ ⊤ :=
    (IsCompact.measure_lt_top (isCompact_univ_pi fun _ ↦ isCompact_valBall M)).ne
  have hint : Integrable ((bx (Fin 2) F M).indicator fun _ ↦ B) (vol2 ψ) :=
    (integrable_indicator_iff hS).2 (integrableOn_const hfin)
  have := norm_integral_le_of_norm_le (μ := vol2 ψ)
    (f := fun y ↦ Φ (col3 k y) * (ψ (-(∑ j, ξ j * y j)) : ℂ)) hint
    (Filter.Eventually.of_forall fun y ↦ ?_)
  · rw [integral_indicator_const _ hS, smul_eq_mul] at this
    exact this
  · rw [norm_mul, Circle.norm_coe, mul_one]
    by_cases hy : y ∈ bx (Fin 2) F M
    · rw [Set.indicator_of_mem hy]
      exact hB _
    · rw [Set.indicator_of_notMem hy]
      by_cases h0 : Φ (col3 k y) = 0
      · simp [h0]
      · exact absurd (mem_bx.2 fun a ↦ by
          simpa [three_column_matrix_last] using hs _ h0 a 2) hy

end GlobalTheory.CompanionTheory.LFFour

open GlobalTheory.CompanionTheory.LFFour in

theorem GlobalTheory.CompanionTheory.LFFour.gFour : Ad3.LFS.GFour := by
  intro F _ _ _ _ _ _ ψ hψ Φ hΦ
  obtain ⟨N, M, hinv, hsupp⟩ := exists_invariant_matrix hΦ.1 hΦ.2
  obtain ⟨B, hB⟩ := hΦ.2.exists_bound_of_continuous hΦ.1.continuous
  obtain ⟨hc, h1, h0⟩ := hψ
  have hnot := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at hnot
  simp only [IsTrivialOn, not_forall] at hnot
  obtain ⟨y, hy, hy1⟩ := hnot
  have hy' : y ∈ valBall F (-1) := by simpa using hy
  refine ⟨(Ad3.LFS.vol2 ψ).real (bx (Fin 2) F M) * B,
    max ((residueCard F : ℝ) ^ (-M))
      (((residueCard F : NNReal) ^ (N + 1) : NNReal) : ℝ),
    fun k ξ ↦ ⟨norm_pft_le ψ hB hsupp k ξ, fun hne ↦ ⟨fun i j ↦ ?_, fun j ↦ ?_⟩⟩⟩
  · have hex : ∃ y, Φ (Ad3.LFS.col3 k y) ≠ 0 := by
      by_contra hno
      push_neg at hno
      exact hne (by simp [Ad3.LFS.pft, hno])
    obtain ⟨z, hz⟩ := hex
    have := hsupp _ hz i j.castSucc
    rw [three_column_matrix_left] at this
    exact (modulus_le_zpow_of_mem this).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    by_cases hξ : ξ j = 0
    · simp [hξ]
      positivity
    · refine NNReal.coe_le_coe.mpr
        (GlobalTheory.CompanionTheory.LFSupp.modulus_le_of_trivial hy' hy1 (Units.mk0 (ξ j) hξ) fun x hx ↦ ?_)
      have e := pft_eq_mul ψ hinv k ξ j (neg_mem hx)
      have e2 : (ψ (-(ξ j * -x)) : ℂ) = 1 :=
        mul_right_cancel₀ hne (by rw [← e, one_mul])
      have e3 := Circle.coe_eq_one.mp e2
      simpa using e3
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassThirdStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hermitian_class_third : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ (m : (w.adicCompletion E)[X]) (c : GL (Fin n) (w.adicCompletion E)), c.val * (γ₀.val.map (algebraMap E (w.adicCompletion E))) = (γ₀.val.map (algebraMap E (w.adicCompletion E))) * c.val → (H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m = cT (cj w) c.val * (H₀.map (algebraMap E (w.adicCompletion E))) * c.val → ∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → x ∈ norms Q (v.adicCompletion (maximalRealSubfield E)) := by
  first | exact @GlobalTheory.CompanionTheory.NormCongr.mem_norms_locPhi | exact GlobalTheory.CompanionTheory.NormCongr.mem_norms_locPhi | (intros; apply GlobalTheory.CompanionTheory.NormCongr.mem_norms_locPhi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeCharacterIntegralStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_character_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), 0 < n → ∀ p ∈ S, ∀ θ : ℝ≥0, (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (p.1 : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ j : ℕ, ∃ G : Finset (Fin n × (Fin n → (Fv F v ⊗[F] E))), ((G.card : ℝ≥0) ≤ n * (θ⁻¹) ^ (j * n)) ∧ (∀ q ∈ G, (∀ i, q.2 i ∈ O) ∧ q.2 q.1 = 1) ∧ ∀ X ∈ nearNF (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) (p.1 : (Fv F v ⊗[F] E)) j, ∃ q ∈ G, GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) q.1 q.2 * dMat (Fv F v) q.1 ((p.1 ^ j)⁻¹ : (Fv F v ⊗[F] E)ˣ)) ∈ tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.nearNF_cover | exact GlobalTheory.CompanionTheory.AvgFree.nearNF_cover | (intros; apply GlobalTheory.CompanionTheory.AvgFree.nearNF_cover <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeGaussSumEstimateStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_gauss_sum_estimate : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), Monotone (fun j => (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j)) ∧ ∀ j, (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.goodT_mono_free | exact GlobalTheory.CompanionTheory.AvgFree.goodT_mono_free | (intros; apply GlobalTheory.CompanionTheory.AvgFree.goodT_mono_free <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeQuadraticIntegralStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_quadratic_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M : ℕ), tupIn (Fv F v) (L : Set (Fv F v ⊗[F] E)) ∩ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ j, (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.free_tuple_mem_goodT | exact GlobalTheory.CompanionTheory.AvgFree.free_tuple_mem_goodT | (intros; apply GlobalTheory.CompanionTheory.AvgFree.free_tuple_mem_goodT <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLatticeVolumeOrderDataStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_volume_order_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (O : Subring (Fv F v ⊗[F] E)) (S : Finset ((Fv F v ⊗[F] E)ˣ × (Fv F v ⊗[F] E))), IsOrdData (Fv F v) σ b lv O S → ∀ L : Submodule O (Fv F v ⊗[F] E), IsCompact (L : Set (Fv F v ⊗[F] E)) → IsOpen (L : Set (Fv F v ⊗[F] E)) → ∀ (n M j : ℕ), IsCompact (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) ∧ IsOpen (goodT (M := M) (n := n) (Fv F v) (O : Set (Fv F v ⊗[F] E)) (L : Set (Fv F v ⊗[F] E)) S j) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.goodT_isClopen | exact GlobalTheory.CompanionTheory.AvgFree.goodT_isClopen | (intros; apply GlobalTheory.CompanionTheory.AvgFree.goodT_isClopen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderConjugationStableStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_conjugation_stable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n M : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → MeasurePreserving (fun X : (Fin n → Fin M → (Fv F v ⊗[F] E)) => GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (eMat (Fv F v) l a)) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.shear_measurePreserving | exact GlobalTheory.CompanionTheory.AvgFree.shear_measurePreserving | (intros; apply GlobalTheory.CompanionTheory.AvgFree.shear_measurePreserving <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderStableIntegralStructureStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_order_stable_integral_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ O : Subring (Fv F v ⊗[F] E), IsCompact (O : Set (Fv F v ⊗[F] E)) → IsOpen (O : Set (Fv F v ⊗[F] E)) → (∀ x ∈ O, HeckeCharacterZeroLocus.SiegelWeilU.sigR (Fv F v) σ x ∈ O) → ∀ (n : ℕ) (l : Fin n) (a : Fin n → (Fv F v ⊗[F] E)), (∀ i, a i ∈ O) → a l = 1 → ∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → MeasurableSet (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (cjPre (Fv F v) σ (eMat (Fv F v) l a) Y) = (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat | exact GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat | (intros; apply GlobalTheory.CompanionTheory.AvgFree.ElemHerm.coordHerm_cjPre_eMat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneZeroFibreVolume
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib

open scoped Pointwise in

theorem map_mul_fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    [lam.IsAddHaarMeasure] (x : Fv F v) (hx : x ≠ 0) (a : ℝ≥0) (ha : ‖x‖ = (a : ℝ)⁻¹) :
    lam.map (fun y => x * y) = a • lam := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu : IsUnit x := hx.isUnit
  have hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = (a : ℝ)⁻¹ := by
    have := GlobalTheory.GaugeProdFormula.modu_finite F v x hx
    rw [GlobalTheory.GaugeEx.modu, dif_pos hu] at this
    rw [this, ha]
  have hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = a := by
    rw [map_inv]
    apply NNReal.coe_injective
    push_cast
    rw [hc]
    simp
  have hm : Measurable fun y : Fv F v => x * y := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  have e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, hc']
  rfl

theorem mass_scalT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (c : Fv F v ⊗[F] E) (a : ℝ≥0) (t : Fv F v), IsUnit c → a ≠ 0 → (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = (a : ℝ)⁻¹ → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), MeasurableSet A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) {y | scalT c y ∈ A} = (a : ℝ≥0∞) ^ (M - 1) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) A := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₂ d b v lam hlam m hm c a t hcu ha hk hts hnorm A hA
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have ht : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact inv_ne_zero ha' hnorm.symm
  have hs := map_mul_fv v lam t ht a hnorm
  set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun y => c * y with hf
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk1 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk
  have hk2 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one] at hk2
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => c
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact hcu
  have hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) =
      fun X p i => f (X p i) := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf]
    rw [Subsingleton.elim p 0, mul_comm]
  obtain ⟨-, -, -, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Fv F v) 1
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S =>
    ⟨cT (sigR (Fv F v) σ) g * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) * g, hmem S g⟩
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g :=
    fun S => rfl
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := by
    intro S i j
    rw [hτ, hts]
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, g,
      Matrix.of_apply]
    ring
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
    have h1 : Continuous τ :=
      ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
    exact h1.measurable
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam t ht a hs τ hτm hτe
  have hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g := by
    rw [hrm]
    exact measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i =>
      hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hfree : IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm hfree g hg τ hτ _ _
    (by rw [hrm]; exact hk2) hc (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)
  have hτs : τ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) =
      hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ := by
    have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ = 0 := by
      apply Subtype.ext
      funext i j
      simp [hermOf]
    rw [h0]
    apply Subtype.ext
    rw [hτ]
    simp
  rw [hτs] at key
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' A) key
  simp only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2
  have e1 : a ^ M = a * a ^ (M - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hM]
  rw [e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc] at key2
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  have key3 := (ENNReal.mul_right_inj ha0 ENNReal.coe_ne_top).1 key2
  have hset : {y : Fin 1 → Fin M → Fv F v ⊗[F] E | scalT c y ∈ A} =
      (fun X => rmul (Fv F v) X g) ⁻¹' A := by
    rw [hrm]
    rfl
  rw [hset, ← key3]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalScalingMeasureByUnitStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_scaling_measure_by_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (s : (Fv F v ⊗[F] E)ˣ) (θ : ℝ≥0), (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (s : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ (n : ℕ) (l : Fin n) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y → MeasurableSet (cjPre (Fv F v) σ (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) Y) ∧ (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (cjPre (Fv F v) σ (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) Y) = ((θ : ℝ≥0∞) ^ n)⁻¹ * (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.cjPre_dMat_scale | exact GlobalTheory.CompanionTheory.AvgFree.cjPre_dMat_scale | (intros; apply GlobalTheory.CompanionTheory.AvgFree.cjPre_dMat_scale <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalScalingVolumeByUnitStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_scaling_volume_by_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (s : (Fv F v ⊗[F] E)ˣ) (θ : ℝ≥0), (∀ Y : Set (Fv F v ⊗[F] E), (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) ((fun x => (s : (Fv F v ⊗[F] E)) * x) '' Y) = θ * (GlobalTheory.CompanionTheory.SW.coordK (Fv F v) b lv) Y) → ∀ (n M : ℕ) (l : Fin n) (D : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), MeasurableSet D → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) {X | GlobalTheory.CompanionTheory.SW.rmul (Fv F v) X (dMat (Fv F v) l (s : (Fv F v ⊗[F] E))) ∈ D} = ((θ : ℝ≥0∞) ^ M)⁻¹ * (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) D := by
  first | exact @GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale | exact GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale | (intros; apply GlobalTheory.CompanionTheory.AvgFree.coordW_dMat_scale <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDensityFromBoxVolumeGrowthStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_box_radius_tail_lintegral_le_eps_mul : ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ) (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → Measurable q → (∀ r : Fin n → W → ℝ, MeasurableSet (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) → ∀ φ : (Fin n → Fin M → K) → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k) → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ R : ℝ, 1 ≤ R ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density <;> assumption)
end

