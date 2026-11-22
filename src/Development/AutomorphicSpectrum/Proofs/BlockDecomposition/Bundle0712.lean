import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SiegelOneDescent.Descend2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0562
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0702
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0703

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinIdele
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GroundTheory.Global GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal
open scoped TensorProduct NumberField.AdeleRing WithZero

noncomputable section
namespace GlobalTheory.CompanionTheory.CMDelta

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_delta (h : IsCMExt F E σ) :
    ∃ (δ : E) (d : F), δ ≠ 0 ∧ σ δ = -δ ∧ algebraMap F E d = δ ^ 2 := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have hσ := GlobalTheory.LFun.InertChart.conj_conj h
  have hne := GlobalTheory.LFun.InertChart.conj_ne h
  obtain ⟨e, he⟩ : ∃ e, σ e ≠ e := by
    by_contra hn
    push Not at hn
    exact hne hn
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs1 : s ≠ 1 := fun hs => he (congrArg (fun t : E ≃ₐ[F] E => t e) hs)
  have hfix : ∀ t : E ≃ₐ[F] E, t ((e - σ e) ^ 2) = (e - σ e) ^ 2 := fun t => by
    have hc : Nat.card (E ≃ₐ[F] E) = 2 := (IsGalois.card_aut_eq_finrank F E).trans h.2.2.1
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hc
    by_cases ht : t = 1
    · rw [ht]; rfl
    · rw [(hu t ht).trans (hu s hs1).symm]
      change σ _ = _
      rw [map_pow, map_sub, hσ]; ring
  obtain ⟨d, hd⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  exact ⟨e - σ e, d, sub_ne_zero.2 (Ne.symm he), by rw [map_sub, hσ]; ring, hd⟩

theorem val_square (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) {δ : E} {d : F} (hd : algebraMap F E d = δ ^ 2)
    (w : HeightOneSpectrum (𝓞 E)) :
    w.valuation E δ ^ 2 = (below F w).valuation F d := by
  have hram : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have h1 := valued_completionMap (below F w) w (algebraMap F _ d)
  rw [completionMap_algebraMap, hram, pow_one, IsScalarTower.algebraMap_apply F E (w.adicCompletion E),
    HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion] at h1
  simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self, RingHom.id_apply] at h1
  rw [← h1, hd, map_pow]

theorem valued_alg {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    Valued.v (algebraMap K (v.adicCompletion K) x) = v.valuation K x := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self, RingHom.id_apply]

theorem exists_finIdele {d : F} (hd0 : d ≠ 0) :
    ∃ (X : (FiniteAdeleRing (𝓞 F) F)ˣ), ∀ (v : HeightOneSpectrum (𝓞 F)) (k : ℤ),
      v.valuation F d = WithZero.exp (2 * k) → Valued.v ((X : FiniteAdeleRing (𝓞 F) F) v) = WithZero.exp k := by
  classical
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F) => v.valuation_exists_uniformizer F
  let n : HeightOneSpectrum (𝓞 F) → ℤ := fun v => WithZero.log (v.valuation F d) / 2
  have hev : ∀ᶠ v in Filter.cofinite, n v = 0 := by
    have h1 := (algebraMap F (FiniteAdeleRing (𝓞 F) F) d).2
    have h2 := (algebraMap F (FiniteAdeleRing (𝓞 F) F) d⁻¹).2
    filter_upwards [h1, h2] with v a b
    have a' : v.valuation F d ≤ 1 := by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 a
      exact (valued_alg v d).symm.le.trans this
    have b' : v.valuation F d⁻¹ ≤ 1 := by
      have := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 b
      exact (valued_alg v d⁻¹).symm.le.trans this
    have : v.valuation F d = 1 := by
      rw [map_inv₀] at b'
      exact le_antisymm a' ((inv_le_one₀ (zero_lt_iff.2 (by simpa using hd0))).1 b')
    simp [n, this]
  let f : ℤ → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F := fun s v =>
    (algebraMap F (v.adicCompletion F) (π v)) ^ (s * n v)
  have hfmem : ∀ s : ℤ, ∀ᶠ v in Filter.cofinite, f s v ∈ v.adicCompletionIntegers F := fun s => by
    filter_upwards [hev] with v hv
    simp [f, hv, one_mem]
  let X (s : ℤ) : FiniteAdeleRing (𝓞 F) F := ⟨f s, hfmem s⟩
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) (π v) ≠ 0 := fun v h => by
    have := valued_alg v (π v)
    rw [h, map_zero, hπ v] at this
    exact WithZero.exp_ne_zero this.symm
  refine ⟨⟨X (-1), X 1, ?_, ?_⟩, fun v k hk => ?_⟩
  · refine FiniteAdeleRing.ext (K := F) fun v => ?_
    change f (-1) v * f 1 v = 1
    simp only [f]
    rw [← zpow_add₀ (hne v)]
    simp
  · refine FiniteAdeleRing.ext (K := F) fun v => ?_
    change f 1 v * f (-1) v = 1
    simp only [f]
    rw [← zpow_add₀ (hne v)]
    simp
  · change Valued.v (f (-1) v) = _
    have hn : n v = k := by
      simp only [n]
      rw [hk, WithZero.log_exp]
      omega
    simp only [f, hn]
    rw [map_zpow₀, valued_alg, hπ]
    rw [← WithZero.exp_zsmul]
    simp

theorem exists_infIdele {d : F} (hd0 : d ≠ 0) (hr : NumberField.IsTotallyReal F) :
    ∃ T : (InfiniteAdeleRing F)ˣ, ∀ v : InfinitePlace F,
      (T : InfiniteAdeleRing F) v ^ 2 = algebraMap F (InfiniteAdeleRing F) d v ∨
      (T : InfiniteAdeleRing F) v ^ 2 = -algebraMap F (InfiniteAdeleRing F) d v := by
  have key : ∀ v : InfinitePlace F, ∃ t : v.Completion, t ≠ 0 ∧
      (t ^ 2 = algebraMap F (InfiniteAdeleRing F) d v ∨ t ^ 2 = -algebraMap F (InfiniteAdeleRing F) d v) := by
    intro v
    have hv : v.IsReal := NumberField.IsTotallyReal.isReal v
    let f := InfinitePlace.Completion.ringEquivRealOfIsReal hv
    have ha : algebraMap F (InfiniteAdeleRing F) d v ≠ 0 :=
      (map_ne_zero (algebraMap F v.Completion)).2 hd0
    set a := algebraMap F (InfiniteAdeleRing F) d v with hadef
    have hfa : f a ≠ 0 := (map_ne_zero f).2 ha
    refine ⟨f.symm (Real.sqrt |f a|), ?_, ?_⟩
    · exact (map_ne_zero f.symm).2 (Real.sqrt_ne_zero'.2 (abs_pos.2 hfa))
    · rw [← map_pow, Real.sq_sqrt (abs_nonneg _)]
      rcases abs_choice (f a) with h | h
      · left; rw [h]; simp
      · right; rw [h, map_neg]; simp
  choose t ht0 ht using key
  refine ⟨⟨t, fun v => (t v)⁻¹, ?_, ?_⟩, ht⟩
  · funext v; exact mul_inv_cancel₀ (ht0 v)
  · funext v; exact inv_mul_cancel₀ (ht0 v)

theorem bDel : PositivityTheory.RgEis.So.BDel := by
  intro F E _ _ _ _ _ σ χ c hcm hU _ _
  obtain ⟨δ, d, hδ0, hσ, hd⟩ := exists_delta hcm
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd
    exact hδ0 (pow_eq_zero_iff (two_ne_zero) |>.1 hd.symm)
  obtain ⟨X, hX⟩ := exists_finIdele hd0
  obtain ⟨T, hT⟩ := exists_infIdele hd0 hcm.1
  let α : IdeleGroup F := MulEquiv.prodUnits.symm (T, X)
  let δu : Eˣ := Units.mk0 δ hδ0
  let A := PositivityTheory.RgEis.adCM σ χ
  let ν := PositivityTheory.RgEis.So.nuCM F E
  let u := Units.map A.i.toMonoidHom δu * (Units.map ν.toMonoidHom α)⁻¹
  have hνe : ∀ z, PositivityTheory.RgEis.eqv F E (ν z) = adeleMap F E z := fun z => by
    change GroundTheory.BlockD.ThmBHecke.adeleEquiv F E (z ⊗ₜ 1) = _
    rw [GroundTheory.BlockD.ThmBHecke.adeleEquiv_tmul, map_one, one_mul]
  have hie : ∀ e, PositivityTheory.RgEis.eqv F E (A.i e) = algebraMap E 𝔸[E] e := fun e => by
    change GroundTheory.BlockD.ThmBHecke.adeleEquiv F E (1 ⊗ₜ e) = _
    rw [GroundTheory.BlockD.ThmBHecke.adeleEquiv_tmul, map_one, mul_one]
  have hdec : A.i δ = ν α * u := by
    change A.i δ = ν α * (A.i δ * ((Units.map ν.toMonoidHom α)⁻¹ : (_)ˣ).1)
    have : ν α * ((Units.map ν.toMonoidHom α)⁻¹ : (_)ˣ).1 = 1 := Units.mul_inv (Units.map ν.toMonoidHom α)
    rw [mul_left_comm, this, mul_one]
  set y := PositivityTheory.RgEis.eqv F E u with hy
  set y' := PositivityTheory.RgEis.eqv F E ((u⁻¹ : (_)ˣ) : _) with hy'
  have h1 : adeleMap F E α * y = algebraMap E 𝔸[E] δ := by
    rw [← hνe, hy, ← map_mul, ← hdec, hie]
  have h2 : y * y' = 1 := by
    rw [hy, hy', ← map_mul, Units.mul_inv, map_one]
  have hfin : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (y.2 w) = 1 := by
    intro w
    have hram : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
    have hw0 : w.valuation E δ ≠ 0 := by simpa using hδ0
    obtain ⟨k, hk⟩ : ∃ k : ℤ, w.valuation E δ = WithZero.exp k :=
      ⟨WithZero.log (w.valuation E δ), (WithZero.exp_log hw0).symm⟩
    have hsq := val_square hU hd w
    have hval : (below F w).valuation F d = WithZero.exp (2 * k) := by
      rw [← hsq, hk, ← WithZero.exp_nsmul]
      simp
    have hX' := hX (below F w) k hval
    have hA : Valued.v ((adeleMap F E α).2 w) = WithZero.exp k := by
      change Valued.v (completionMap (below F w) w ((X : FiniteAdeleRing (𝓞 F) F) (below F w))) = _
      rw [valued_completionMap, hram, pow_one, hX']
    have hc : (adeleMap F E α).2 w * y.2 w = algebraMap E (w.adicCompletion E) δ :=
      congrArg (fun z : 𝔸[E] => z.2 w) h1
    have hv := congrArg Valued.v hc
    rw [map_mul, hA, show Valued.v (algebraMap E (w.adicCompletion E) δ) = w.valuation E δ from valued_alg w δ, hk] at hv
    exact mul_left_cancel₀ (WithZero.exp_ne_zero (a := k)) (hv.trans (mul_one _).symm)
  have hfin' : ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (y'.2 w) = 1 := by
    intro w
    have hc : y.2 w * y'.2 w = 1 := congrArg (fun z : 𝔸[E] => z.2 w) h2
    have hv := congrArg Valued.v hc
    rwa [map_mul, hfin w, one_mul, map_one] at hv
  have hinf : ∀ w : InfinitePlace E, ‖y.1 w‖ = 1 := by
    intro w
    set D : w.Completion := algebraMap E (InfiniteAdeleRing E) δ w with hD
    have hD0 : D ≠ 0 := (map_ne_zero (algebraMap E w.Completion)).2 hδ0
    set v := w.comap (algebraMap F E) with hv
    set Aw : w.Completion := (adeleMap F E α).1 w with hAw
    have hAsq : Aw ^ 2 = D ^ 2 ∨ Aw ^ 2 = -D ^ 2 := by
      obtain ⟨g, hg⟩ : ∃ g : v.Completion →+* w.Completion, ∀ x : InfiniteAdeleRing F,
          GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) x w = g (x v) :=
        ⟨_, fun x => GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_apply x w⟩
      have hAw' : Aw = g ((T : InfiniteAdeleRing F) v) := hg _
      have hm : g (algebraMap F (InfiniteAdeleRing F) d v) = D ^ 2 := by
        have := congrFun (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap (K := F) (L := E) d) w
        rw [hg, hd, map_pow] at this
        exact this
      rcases hT v with h | h
      · left; rw [hAw', ← map_pow, h, hm]
      · right; rw [hAw', ← map_pow, h, map_neg, hm]
    have hnorm : ‖Aw‖ = ‖D‖ := by
      have : ‖Aw‖ ^ 2 = ‖D‖ ^ 2 := by
        rcases hAsq with h | h
        · rw [← norm_pow, h, norm_pow]
        · rw [← norm_pow, h, norm_neg, norm_pow]
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
    have hc : Aw * y.1 w = D := congrArg (fun z : 𝔸[E] => z.1 w) h1
    have hn := congrArg norm hc
    rw [norm_mul, hnorm] at hn
    exact mul_left_cancel₀ (norm_ne_zero_iff.2 hD0) (hn.trans (mul_one _).symm)
  have hint : ∀ z : 𝔸[E], (∀ w : HeightOneSpectrum (𝓞 E), Valued.v (z.2 w) = 1) → z ∈ PositivityTheory.RgEis.intAd E := by
    intro z hz
    refine (Subring.mem_iInf).2 fun w => ?_
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 (hz w).le
  have hφ : ∀ w : InfinitePlace E, ‖(InfinitePlace.Completion.extensionEmbedding w) (y.1 w)‖ = 1 := fun w => by
    rw [← hinf w]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _
  refine ⟨δu, α, u, hσ, hdec, hint y hfin, hint y' hfin', fun w => hφ w⟩

end GlobalTheory.CompanionTheory.CMDelta
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTestFunctionFixedSubspace
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep.Inj

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_infGL_alt : Continuous (infGL E a) := by
  have hs : Continuous (sInf E) := ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  exact Continuous.units_map (corner (matN a (sInf E))) (continuous_const.add (continuous_id.matrix_map hs))

theorem R_apply_eq {μ : Measure (GA E a)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {U : Subgroup (GL (Fin a) (Af E))}
    {v : L2 (latticeGL E a) μ} (hv : ∀ u ∈ U, R (latticeGL E a) μ (finGL E a u) v = v) {g : GA E a}
    (hu : GeneralLinearGroup.map (pFin E) g⁻¹ ∈ U) :
    R (latticeGL E a) μ g v = R (latticeGL E a) μ (infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹) v := by
  have e : g = infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹ * finGL E a (GeneralLinearGroup.map (pFin E) g⁻¹)⁻¹ := by
    rw [map_inv (infGL E a), map_inv (finGL E a), ← _root_.mul_inv_rev, ← infGL_comm, infGL_mul_finGL, inv_inv]
  conv_lhs => rw [e]
  rw [map_mul, ContinuousLinearMap.mul_apply, hv _ (U.inv_mem hu)]

theorem exists_isTest_Rop_injective : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (U : Subgroup (GL (Fin a) (Af E))), IsOpen (U : Set (GL (Fin a) (Af E))) → IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ X : Submodule ℂ (L2 (latticeGL E a) μ), FiniteDimensional ℂ X → (∀ u ∈ U, ∀ v ∈ X, R (latticeGL E a) μ (finGL E a u) v = v) → ∃ β : Lie E a → ℂ, IsTest β ∧ ConjInv β ∧ ∀ v ∈ X, Rop (latticeGL E a) μ (tst U β) v = 0 → v = 0 := by
  intro E _ _ _ a μ _ _ U hU hUc X hX hfix
  let Φ : GL (Fin a) (Cinf E) → (X →L[ℂ] L2 (latticeGL E a) μ) := fun y =>
    (R (latticeGL E a) μ (infGL E a y⁻¹) - ContinuousLinearMap.id ℂ _) ∘L X.subtypeL
  have hΦv : ∀ y (w : X), Φ y w = R (latticeGL E a) μ (infGL E a y⁻¹) w - w := fun _ _ => rfl
  have hΦ : Continuous Φ := by
    refine continuous_clm_apply.2 fun w => ?_
    simp only [hΦv]
    exact ((continuous_R (w : L2 (latticeGL E a) μ)).comp (continuous_infGL_alt.comp continuous_inv)).sub
      continuous_const
  have hΦ1 : Φ 1 = 0 := by
    ext w
    simp [hΦv]
  have hN : {y | ‖Φ y‖ ≤ 1 / 2} ∈ 𝓝 (1 : GL (Fin a) (Cinf E)) := by
    have h1 : Metric.closedBall (0 : X →L[ℂ] L2 (latticeGL E a) μ) (1 / 2) ∈ 𝓝 (Φ 1) := by
      rw [hΦ1]; exact Metric.closedBall_mem_nhds _ (by norm_num)
    have h2 := hΦ.continuousAt.preimage_mem_nhds h1
    simpa [Metric.closedBall, dist_zero_right] using h2
  obtain ⟨β₀, h0, hpos, htest, hconj, hsupp⟩ := GlobalTheory.T.exists_nonneg_test_function_near_one E a _ hN
  refine ⟨fun x => (β₀ x : ℂ), htest, hconj, fun v hv hRv => ?_⟩
  obtain ⟨hc, hcs⟩ := GlobalTheory.T.test_function_continuous_compact_support E a U hU hUc _ htest
  set f := tst U (fun x => (β₀ x : ℂ)) with hf
  set fr : GA E a → ℝ := fun g => (f g).re with hfr
  have hf_eq : ∀ g, f g = (fr g : ℂ) := by
    intro g
    simp only [hfr, hf, tst, ker]
    split_ifs <;> simp
  have hfr0 : ∀ g, 0 ≤ fr g := by
    intro g
    simp only [hfr, hf, tst, ker]
    split_ifs
    · simpa using h0 _
    · simp
  have hfrc : Continuous fr := Complex.continuous_re.comp hc
  have hfrs : HasCompactSupport fr := hcs.comp_left Complex.zero_re
  have hfr1 : fr 1 ≠ 0 := by
    have : fr 1 = β₀ (oneL E a) := by
      simp [hfr, hf, tst, ker, U.one_mem]
    rw [this]; exact hpos.ne'
  have hIpos : 0 < ∫ g, fr g ∂μ :=
    hfrc.integral_pos_of_hasCompactSupport_nonneg_nonzero hfrs hfr0 hfr1
  have hint : Integrable f μ := hc.integrable_of_hasCompactSupport hcs
  have hfrint : Integrable fr μ := hfrc.integrable_of_hasCompactSupport hfrs
  have hrep := (isRepOp_Rop (Γ := latticeGL E a) (μ := μ) hint) v
  have key : (∫ g, f g ∂μ) • v = ∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ := by
    calc (∫ g, f g ∂μ) • v = (∫ g, f g ∂μ) • v - ∫ g, f g • R (latticeGL E a) μ g v ∂μ := by
          have h2 := hrep.2.symm.trans hRv
          rw [show (∫ g, f g • R (latticeGL E a) μ g v ∂μ) = 0 from h2, sub_zero]
      _ = ∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ := by
          rw [← integral_smul_const, ← integral_sub (hint.smul_const v) hrep.1]
          simp_rw [smul_sub]
  have hI : (∫ g, f g ∂μ) = ((∫ g, fr g ∂μ : ℝ) : ℂ) := by
    simp_rw [hf_eq]; exact integral_ofReal
  have hpt : ∀ g, fr g ≠ 0 → ‖v - R (latticeGL E a) μ g v‖ ≤ ‖v‖ / 2 := by
    intro g hg
    have hfg : f g ≠ 0 := fun h => hg (by show (f g).re = 0; rw [h]; simp)
    simp only [hf, tst, ker] at hfg
    split_ifs at hfg with hu
    · have hb : β₀ (toL (GeneralLinearGroup.map (pInf E) g⁻¹).val) ≠ 0 := by
        intro h; apply hfg; simp only [Complex.ofReal_eq_zero]; convert h using 1
      obtain ⟨y, hyN, hy⟩ := hsupp _ hb
      have hy' : y = GeneralLinearGroup.map (pInf E) g⁻¹ := Units.ext (Matrix.of.symm.injective hy)
      rw [R_apply_eq (fun u hu' => hfix u hu' v hv) hu, norm_sub_rev]
      calc ‖R (latticeGL E a) μ (infGL E a (GeneralLinearGroup.map (pInf E) g⁻¹)⁻¹) v - v‖
          = ‖Φ y ⟨v, hv⟩‖ := by rw [hΦv, hy']
        _ ≤ ‖Φ y‖ * ‖(⟨v, hv⟩ : X)‖ := (Φ y).le_opNorm _
        _ ≤ 1 / 2 * ‖v‖ := mul_le_mul_of_nonneg_right hyN (norm_nonneg _)
        _ = ‖v‖ / 2 := by ring
    · exact absurd rfl hfg
  have hbound : ‖∫ g, f g • (v - R (latticeGL E a) μ g v) ∂μ‖ ≤ ∫ g, fr g * (‖v‖ / 2) ∂μ :=
    norm_integral_le_of_norm_le (hfrint.mul_const _) (Filter.Eventually.of_forall fun g => by
      rw [norm_smul, hf_eq, Complex.norm_real, Real.norm_of_nonneg (hfr0 g)]
      by_cases hg : fr g = 0
      · simp [hg]
      · exact mul_le_mul_of_nonneg_left (hpt g hg) (hfr0 g))
  rw [integral_mul_const, ← key, hI, norm_smul, Complex.norm_real, Real.norm_of_nonneg hIpos.le] at hbound
  have hle : ‖v‖ ≤ 0 := by nlinarith [norm_nonneg v]
  exact norm_le_zero_iff.1 hle

end GlobalTheory.CompanionTheory.SmoothRep.Inj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionEmbeddingAlgebraMapOfTotallyReal
section
noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing NumberField.LiesOver TensorProduct
open PositivityTheory.RgEis PositivityTheory.RgEis.So
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace GlobalTheory.CompanionTheory.RgEisSo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem embedding_algebraMap_of_totallyReal (hF : IsTotallyReal F) (w : InfinitePlace E) (x : F) :
    w.embedding (algebraMap F E x) = (w.comap (algebraMap F E)).embedding x := by
  have hreal : ComplexEmbedding.IsReal (w.comap (algebraMap F E)).embedding :=
    InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal _)
  have h : InfinitePlace.mk (w.embedding.comp (algebraMap F E)) =
      InfinitePlace.mk (w.comap (algebraMap F E)).embedding := by
    rw [InfinitePlace.mk_embedding, ← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  rcases InfinitePlace.mk_eq_iff.1 h with h | h
  · exact congrArg (fun f : F →+* ℂ => f x) h
  · have h' : w.embedding.comp (algebraMap F E) = (w.comap (algebraMap F E)).embedding := by
      have h2 : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate (w.embedding.comp (algebraMap F E))) =
          w.embedding.comp (algebraMap F E) := star_star _
      rw [← h2, h]
      exact ComplexEmbedding.isReal_iff.1 hreal
    exact congrArg (fun f : F →+* ℂ => f x) h'

theorem extensionEmbedding_algebraMap_of_totallyReal (hF : IsTotallyReal F) (w : InfinitePlace E)
    (z : (w.comap (algebraMap F E)).Completion) :
    extensionEmbedding w (algebraMap (w.comap (algebraMap F E)).Completion w.Completion z) =
      extensionEmbedding (w.comap (algebraMap F E)) z := by
  have h := (denseRange_coe (v := w.comap (algebraMap F E))).equalizer
    (g := fun z => extensionEmbedding w (algebraMap (w.comap (algebraMap F E)).Completion w.Completion z))
    (h := fun z => extensionEmbedding (w.comap (algebraMap F E)) z)
    ((isometry_extensionEmbedding w).continuous.comp LiesOver.continuous_completionMap)
    (isometry_extensionEmbedding _).continuous (funext fun k => ?_)
  · exact congrFun h z
  · have e := LiesOver.completionMap_coe (v := w.comap (algebraMap F E)) (w := w) k
    show extensionEmbedding w (LiesOver.completionMap (k : (w.comap (algebraMap F E)).Completion)) =
      extensionEmbedding (w.comap (algebraMap F E)) (k : (w.comap (algebraMap F E)).Completion)
    rw [e, extensionEmbedding_coe, extensionEmbedding_coe]
    exact embedding_algebraMap_of_totallyReal hF w _

theorem phi_nuCM (σ : E →ₐ[F] E) (χ : Chr F E) (hF : IsTotallyReal F) (w : InfinitePlace E) (x : 𝔸[F]) :
    (adCM σ χ).φ w (nuCM F E x) = (adStd F).φ (w.comap (algebraMap F E)) x := by
  have h : eqv F E (nuCM F E x) = GroundTheory.Global.AdeleBaseChange.adeleMap F E x :=
    GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap x
  show extensionEmbedding w (GroundTheory.Automorphic.Reduction.infEval w (eqv F E (nuCM F E x))) =
    extensionEmbedding _ (GroundTheory.Automorphic.Reduction.infEval _ x)
  rw [h]
  exact extensionEmbedding_algebraMap_of_totallyReal hF w _

end GlobalTheory.CompanionTheory.RgEisSo

namespace GlobalTheory.CompanionTheory.RgEisSo

theorem bInf : BInf := by
  intro F E _ _ _ _ _ σ χ c hcm _ _ _
  haveI : IsTotallyReal F := hcm.1
  refine ⟨fun w => ⟨w.comap (algebraMap F E), fun x => phi_nuCM σ χ hcm.1 w x⟩, fun v => ?_⟩
  obtain ⟨w, rfl⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  exact ⟨w, fun x => phi_nuCM σ χ hcm.1 w x⟩

end GlobalTheory.CompanionTheory.RgEisSo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodFunctionLineDerivativeStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_function_line_derivative : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (U : Subgroup (GAd σ J)) (A : ℕ) (φ : GAd σ J → ℂ) (γ : ℝ → GAd σ J), Good σ J U A φ → IsRealLine σ J γ → Good σ J U A (lineDer γ φ) := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.good_lineDer | exact GlobalTheory.CompanionTheory.RapidDecay.good_lineDer | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.good_lineDer <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIndicatorFormulaStatement
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_indicator_formula : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n k : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → k ≤ n → ∀ g : GL (Fin n) (w.adicCompletion E), Tj ℂ n (Ov E w) ϖ k g = if IsInt w g.val ∧ IsInt w (ϖ • (g⁻¹).val) ∧ ordL g.val.det = (k : ℤ) then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.CtS.Tj_eq_ite | exact GlobalTheory.CompanionTheory.CtS.Tj_eq_ite | (intros; apply GlobalTheory.CompanionTheory.CtS.Tj_eq_ite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeVectorLinearCombinationStatement
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_vector_linear_combination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → ℂ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : V), heckeVec ρ (K2 a b w) (fun g => ∑ p ∈ s, f p * (Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2)) x = ∑ p ∈ s, f p • heckeVec ρ (K2 a b w) (fun g => Tj ℂ a (Ov E w) ϖ p.1 g.1 * Tj ℂ b (Ov E w) ϖ p.2 g.2) x := by
  first | exact @GlobalTheory.CompanionTheory.CtS.HeckeSum.heckeVec_Tj_sum | exact GlobalTheory.CompanionTheory.CtS.HeckeSum.heckeVec_Tj_sum | (intros; apply GlobalTheory.CompanionTheory.CtS.HeckeSum.heckeVec_Tj_sum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicSmoothStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_pairing_mirabolic_smooth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n s : ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V'),
    IsSmooth T → IsSmooth T' → ∀ B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
      ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    ∃ B' : TwJacquet T (MirUin k (n + 1)) (mirChar k ψ n) →ₗ[ℂ]
        TwJacquet T' (MirUin k (n + 1)) (mirChar k ψ⁻¹ n) →ₗ[ℂ] ℂ,
      (∀ (p : Mir k n) w w', B' (phiMinus k ψ T p w) (phiMinus k ψ⁻¹ T' p w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.pairing_phi | exact GlobalTheory.CompanionTheory.MirPair.pairing_phi | (intros; apply GlobalTheory.CompanionTheory.MirPair.pairing_phi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIndexEqDiagonalStatement
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (i j : ℕ), i ≤ a → j ≤ b → ∀ m : GLw a w × GLw b w, Tj ℂ a (Ov E w) ϖ i m.1 ≠ 0 → Tj ℂ b (Ov E w) ϖ j m.2 ≠ 0 → (intSub a b w).relIndex (latM ϖ m) = (intSub a b w).relIndex (latD ϖ a b i j) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.Tr.latM_relIndex | exact GlobalTheory.CompanionTheory.CtS.Tr.latM_relIndex | (intros; apply GlobalTheory.CompanionTheory.CtS.Tr.latM_relIndex <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIndicatorIntegralIndexStatement
section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_indicator_integral_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (Λ : AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E))), intSub a b w ≤ Λ → hint (intMat a b w) (fun X => if Multiplicative.toAdd X ∈ Λ then (1 : ℂ) else 0) = (((intSub a b w).relIndex Λ : ℕ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.HintInd.hint_indicator_lattice | exact GlobalTheory.CompanionTheory.HintInd.hint_indicator_lattice | (intros; apply GlobalTheory.CompanionTheory.HintInd.hint_indicator_lattice <;> assumption)
end

