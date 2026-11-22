import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0190
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0188
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Formalism.FormalDegreeBessel.Bundle0002
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPos
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0191
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0192
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.DiscriminantKernelAutomorphisms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundSkew
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.SkewFund

open GlobalTheory.HomCovolume

theorem one_le_covolume {ι : Type} [Fintype ι] (A : Submodule ℤ (ι → ℝ)) [DiscreteTopology A] [IsZLattice ℝ A]
    (h : ∀ x ∈ A, x ≠ 0 → 1 ≤ ‖x‖) : 1 ≤ ZLattice.covolume A volume := by
  by_contra hlt
  rw [not_le] at hlt
  have : Countable A.toAddSubgroup := inferInstanceAs (Countable A)
  have hF : IsAddFundamentalDomain A.toAddSubgroup (latticeDomain A) volume :=
    isAddFundamentalDomain_latticeDomain A volume
  obtain ⟨x, hx0, hx⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF
    (s := Metric.ball 0 1) (fun x hx => by simpa using hx) (convex_ball _ _) (by
      rw [measure_latticeDomain, Real.volume_pi_ball _ one_pos, Module.finrank_fintype_fun_eq_card,
        mul_one, ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
      calc _ < 1 * 2 ^ Fintype.card ι :=
            ENNReal.mul_lt_mul_left (by simp) (by simp) (ENNReal.ofReal_lt_one.2 hlt)
        _ = _ := one_mul _)
  exact absurd (h x x.2 (fun h0 => hx0 (Subtype.ext h0))) (by simpa using hx)

theorem imag_covolume {ι : Type} [Fintype ι] (L : Submodule ℤ (ι → ℂ)) {c : ℝ} (hc : HasCov volume L c)
    (hs : ∀ z ∈ L, (fun v => starRingEnd ℂ (z v)) ∈ L) (hn : ∀ z ∈ L, z ≠ 0 → 1 ≤ ‖z‖) :
    ∃ B : Submodule ℤ (ι → ℝ), (∀ y, y ∈ B ↔ (fun v => (⟨0, y v⟩ : ℂ)) ∈ L) ∧
      ∃ b, HasCov volume B b ∧ 1 ≤ b ∧ b ≤ 2 ^ Fintype.card ι * c := by
  let e : ((ι → ℝ) × (ι → ℝ)) ≃L[ℝ] (ι → ℂ) := LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p v => ⟨p.1 v, p.2 v⟩
      invFun := fun z => (fun v => (z v).re, fun v => (z v).im)
      map_add' := fun p q => by ext v; apply Complex.ext <;> simp
      map_smul' := fun c p => by ext v; apply Complex.ext <;> simp
      left_inv := fun p => rfl
      right_inv := fun z => rfl }
  have he : ∀ p v, e p v = ⟨p.1 v, p.2 v⟩ := fun _ _ => rfl
  have hmp : MeasurePreserving e (Measure.prod volume volume) volume :=
    (volume_preserving_pi (ι := ι) fun _ => Complex.volume_preserving_equiv_real_prod.symm).comp
      (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι).symm
  let M : Submodule ℤ ((ι → ℝ) × (ι → ℝ)) := L.comap (e.toLinearMap.restrictScalars ℤ)
  have hM : ∀ p, p ∈ M ↔ e p ∈ L := fun _ => Iff.rfl
  have : ((volume : Measure (ι → ℝ)).prod (volume : Measure (ι → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  obtain ⟨_, _, hcM⟩ := HasCov.of_measurePreserving e hmp hM hc
  let A : Submodule ℤ (ι → ℝ) := M.comap (LinearMap.inl ℤ _ _)
  let B : Submodule ℤ (ι → ℝ) := M.comap (LinearMap.inr ℤ _ _)
  obtain ⟨⟨_, _⟩, ⟨_, _⟩, h⟩ := GlobalTheory.ReImLattice.reflection_stable volume M (fun p hp => by
    rw [hM] at hp ⊢
    convert hs _ hp using 1
    ext v; apply Complex.ext <;> simp [he]) A B (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have key : ∀ (x : ι → ℝ) (z : ι → ℂ), z ∈ L → (∀ v, ‖z v‖ = ‖x v‖) → x ≠ 0 → 1 ≤ ‖x‖ := by
    intro x z hz hzx hx
    have h1 : ‖z‖ = ‖x‖ := by
      refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_)
        ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun v => ?_)
      · rw [hzx]; exact norm_le_pi_norm x v
      · rw [← hzx]; exact norm_le_pi_norm z v
    rw [← h1]
    exact hn z hz (by rw [← norm_ne_zero_iff, h1]; exact norm_ne_zero_iff.2 hx)
  have hA : 1 ≤ ZLattice.covolume A volume := one_le_covolume A fun x hx =>
    key x (e (x, 0)) hx fun v => by
      have : e (x, 0) v = (x v : ℂ) := rfl
      rw [this, Complex.norm_real]
  have hB : 1 ≤ ZLattice.covolume B volume := one_le_covolume B fun x hx =>
    key x (e (0, x)) hx fun v => by
      have : e (0, x) v = (x v : ℂ) * Complex.I := by apply Complex.ext <;> simp [he]
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
  refine ⟨B, fun _ => Iff.rfl, _, ⟨inferInstance, inferInstance, rfl⟩, hB, ?_⟩
  rw [hcM, Module.finrank_fintype_fun_eq_card] at h
  exact (le_mul_of_one_le_left (zero_le_one.trans hB) hA).trans h

theorem prod_norm_sq (K : Type) [Field K] [NumberField K] (hK : IsTotallyComplex K) {ι : Type} [Fintype ι]
    (σ : ι → (K →+* ℂ)) (hσ : ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w) (t : K) :
    ∏ v, ‖σ v t‖ ^ 2 = ((|Algebra.norm ℚ t| : ℚ) : ℝ) := by
  rw [← InfinitePlace.prod_eq_abs_norm]
  refine Fintype.prod_bijective _ ((Function.bijective_iff_existsUnique _).2 hσ) _ _ fun v => ?_
  rw [InfinitePlace.mult_isComplex ⟨_, hK.isComplex _⟩, InfinitePlace.apply]

theorem exists_fund_skew : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)), IsPlaces σ → ∀ (𝔡 : Ideal (𝓞 K)) (n : ℕ), 𝔡 ≠ ⊥ → (∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) → (Ideal.absNorm 𝔡 : ℝ) = (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * Fintype.card ι) → 1 ≤ Formalism.HermitianLatticesTheory.vInv K → ∃ F : Set (ι → ℝ), MeasurableSet F ∧ (∀ a : ι → ℝ, ∃! t : K, (t ∈ ipow 𝔡 (-(2 * (n : ℤ))) ∧ t + star t = 0) ∧ ((fun v => (2 * Formalism.HermitianLatticesTheory.vInv K) ^ (2 * n) * (σ v t).im) + a) ∈ F) ∧ ENNReal.ofReal ((8 * Formalism.HermitianLatticesTheory.vInv K) ^ (-(Fintype.card ι : ℝ))) ≤ volume F ∧ volume F ≤ ENNReal.ofReal ((8 * Formalism.HermitianLatticesTheory.vInv K) ^ (Fintype.card ι : ℝ)) := by
  intro K _ _ _ hK ι _ σ hσ 𝔡 n h𝔡 hs hN hv
  set v₀ := Formalism.HermitianLatticesTheory.vInv K with hv₀
  set c : ℝ := (2 * v₀) ^ (2 * n) with hc
  have hc0 : 0 < c := by positivity
  have h0 : (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔡
  obtain ⟨L₀, hL₀, hcov⟩ := GlobalTheory.IdealFund.exists_lat K hK.1 ι σ hσ.2 _ (zpow_ne_zero (-(2 * (n : ℤ))) h0)
  have hNa : ((FractionalIdeal.absNorm ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ (-(2 * (n : ℤ)))) : ℚ) : ℝ) =
      c⁻¹ ^ (2 * Fintype.card ι) := by
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    rw [hN, _root_.zpow_neg, inv_pow, hc, show (2 * (n : ℤ)) = ((2 * n : ℕ) : ℤ) by push_cast; rfl, _root_.zpow_natCast,
      ← pow_mul, ← pow_mul, mul_comm (2 * n)]
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := c⁻¹ • LinearMap.id
  have hf : ∀ z v, f z v = (c : ℂ)⁻¹ * z v := fun _ _ => by simp [f]
  have hdet : LinearMap.det f = c⁻¹ ^ (2 * Fintype.card ι) := by
    rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_pi_fintype]
    simp [mul_comm]
  have hpos : 0 < c⁻¹ ^ (2 * Fintype.card ι) := by positivity
  let L : Submodule ℤ (ι → ℂ) := L₀.comap (f.restrictScalars ℤ)
  have h := HasCov.of_det f (L := L) (by rw [hdet]; exact hpos.ne') (fun _ => Iff.rfl) hcov
  rw [hNa, hdet, abs_of_pos hpos, mul_div_cancel_left₀ _ hpos.ne'] at h
  have hcc : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hL : ∀ z, z ∈ L ↔ ∃ t ∈ ipow 𝔡 (-(2 * (n : ℤ))), z = fun v => c * σ v t := by
    intro z
    change f z ∈ L₀ ↔ _
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h => funext fun v => ?_, fun h v => ?_⟩
    · rw [← h, hf, mul_inv_cancel_left₀ hcc]
    · rw [hf, h, inv_mul_cancel_left₀ hcc]
  obtain ⟨B, hB, b, ⟨_, _, hb⟩, hb1, hb2⟩ := imag_covolume L h (fun z hz => by
    obtain ⟨t, ht, rfl⟩ := (hL z).1 hz
    exact (hL _).2 ⟨star t, IdealPow.star_mem h𝔡 hs ht, funext fun v => by simp [hσ.1]⟩) (fun z hz hz0 => by
    obtain ⟨t, ht, rfl⟩ := (hL z).1 hz
    have ht0 : t ≠ 0 := by rintro rfl; exact hz0 (funext fun v => by simp)
    have h1 : c⁻¹ ^ (2 * Fintype.card ι) ≤ ∏ v, ‖σ v t‖ ^ 2 := by
      rw [← hNa, prod_norm_sq K hK.1 σ hσ.2]
      exact_mod_cast GlobalTheory.absNorm_le_abs_norm_of_mem ht ht0
    by_contra hlt
    rw [not_le, pi_norm_lt_iff one_pos] at hlt
    obtain ⟨u, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
    refine absurd h1 (not_le.2 ?_)
    rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const]
    refine Finset.prod_lt_prod_of_nonempty (fun v _ => pow_pos (norm_pos_iff.2 ((map_ne_zero _).2 ht0)) _)
      (fun v _ => pow_lt_pow_left₀ ?_ (norm_nonneg _) two_ne_zero) ⟨u, Finset.mem_univ _⟩
    have := hlt v
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le] at this
    rwa [← one_mul c⁻¹, lt_mul_inv_iff₀ hc0, mul_comm])
  obtain ⟨u, -⟩ := (hσ.2 (Classical.arbitrary _)).exists
  have hre : ∀ t : K, t + star t = 0 → ∀ v, (σ v t).re = 0 := fun t ht v => by
    have := congrArg (fun x => (σ v x).re) ht
    simp only [map_add, hσ.1, map_zero, Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    linarith
  have hB' : ∀ y, y ∈ B ↔ ∃ t : K, (t ∈ ipow 𝔡 (-(2 * (n : ℤ))) ∧ t + star t = 0) ∧
      y = fun v => c * (σ v t).im := by
    intro y
    rw [hB, hL]
    constructor
    · rintro ⟨t, ht, hy⟩
      refine ⟨t, ⟨ht, (σ u).injective ?_⟩, funext fun v => by simpa using congrArg Complex.im (congrFun hy v)⟩
      have h1 : (σ u t).re = 0 := by simpa [hc0.ne'] using congrArg Complex.re (congrFun hy u)
      rw [map_add, hσ.1, map_zero]
      apply Complex.ext <;> simp [h1]
    · rintro ⟨t, ⟨ht, ht'⟩, rfl⟩
      exact ⟨t, ht, funext fun v => by apply Complex.ext <;> simp [hre t ht']⟩
  refine ⟨latticeDomain B, measurableSet_latticeDomain B, fun a => ?_, ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := existsUnique_add_mem_latticeDomain B a
    obtain ⟨t, ht, hzt⟩ := (hB' z).1 z.2
    refine ⟨t, ⟨ht, by rw [← hzt, add_comm]; exact hz⟩, ?_⟩
    rintro t' ⟨ht', h'⟩
    have h1 := hu ⟨_, (hB' _).2 ⟨t', ht', rfl⟩⟩ (by rw [add_comm] at h'; exact h')
    have h2 := congrFun ((congrArg Subtype.val h1).trans hzt) u
    exact (σ u).injective (Complex.ext (by rw [hre t ht.2, hre t' ht'.2]) (mul_left_cancel₀ hc0.ne' h2))
  · rw [measure_latticeDomain, hb]
    exact ENNReal.ofReal_le_ofReal ((Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simp)).trans hb1)
  · rw [measure_latticeDomain, hb, Real.rpow_natCast]
    refine ENNReal.ofReal_le_ofReal (hb2.trans ?_)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) _

end GlobalTheory.SkewFund
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsChoiceAndIsChoiceOfCard
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.SplitChoice

theorem exists_int_sub_mem_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsMaximal) (hm : (p : 𝓞 E) ∈ P) (hN : Ideal.absNorm P = p) (h2 : (p : 𝓞 E) ∉ P ^ 2) (k : ℕ)
    (a : 𝓞 E) : ∃ m : ℤ, a - m ∈ P ^ k := by
  first
  | exact @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | (apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow ..)

theorem not_isConj_self (I : AutInst) {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 I.E))
    (hm : (p : 𝓞 I.E) ∈ v.asIdeal) (hN : Ideal.absNorm v.asIdeal = p) (h2 : (p : 𝓞 I.E) ∉ v.asIdeal ^ 2) :
    ¬ IsConj I v v := by
  intro h
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hmap : v.asIdeal.map st ≤ v.asIdeal :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (h a (st a) (hst a)).1 ha
  have hfix : ∀ a, st a = a := fun a => by
    have hall : ∀ k, st a - a ∈ v.asIdeal ^ k := fun k => by
      obtain ⟨m, hm'⟩ := exists_int_sub_mem_pow hp v.asIdeal v.isMaximal hm hN h2 k a
      have h3 : st (a - m) ∈ v.asIdeal ^ k := by
        have := Ideal.mem_map_of_mem st hm'
        rw [Ideal.map_pow] at this
        exact Ideal.pow_right_mono hmap k this
      rw [map_sub, map_intCast] at h3
      simpa using sub_mem h3 hm'
    have := Ideal.iInf_pow_eq_bot_of_isDomain v.asIdeal v.isPrime.ne_top
    have h4 : st a - a ∈ (⊥ : Ideal (𝓞 I.E)) := this ▸ Ideal.mem_iInf.2 hall
    exact sub_eq_zero.1 h4
  have hfixE : ∀ x : I.E, star x = x := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 I.E) x
    have ha : star (algebraMap (𝓞 I.E) I.E a) = algebraMap (𝓞 I.E) I.E a := by
      rw [← hst a, hfix]
    have hb : star (algebraMap (𝓞 I.E) I.E b) = algebraMap (𝓞 I.E) I.E b := by
      rw [← hst b, hfix]
    rw [star_div₀, ha, hb]
  have hsurj : Function.Surjective (algebraMap I.F I.E) := fun x => (I.cm.fixed x).1 (hfixE x)
  have h1 : Module.finrank I.F I.E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap I.F I.E).injective, hsurj⟩
  have := I.cm.deg2
  omega

theorem ncard_places_eq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}.ncard =
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  rw [← Set.ncard_image_of_injective _ (fun _ _ h => HeightOneSpectrum.ext h :
    Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _))]
  congr 1
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hv
  · rintro ⟨hP, hl⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩, ?_, rfl⟩
    have : (p : ℤ) ∈ P.under ℤ := hl.over ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at this
    exact this

theorem exists_isChoice_and_isChoice_of_card : ∀ (I : AutInst) (g : Fin 2 → ℕ), (∀ k, (g k).Prime) → g 0 ≠ g 1 → (∀ k (P : Ideal (𝓞 I.E)), P.IsMaximal → ((g k : ℕ) : 𝓞 I.E) ∈ P → Ideal.absNorm P = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ P ^ 2) → (∃ w : ∀ _ : Fin 2, Fin I.f → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin I.f) w) ∧ ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)), (∀ k, Fintype.card (Pl k) = I.f) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) → (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
  intro I g hg hne h
  have hdeg : Module.finrank ℚ I.E = 2 * I.f := by
    rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2, AutInst.f, mul_comm]
  refine GlobalTheory.Mem.RowsBundle.isChoice_of_card I g hg hne (fun k v hv => ?_) Module.finrank_pos fun k => ?_
  · obtain ⟨h1, h2⟩ := h k v.asIdeal v.isMaximal hv
    exact ⟨h1, h2, not_isConj_self I (hg k) v hv h1 h2⟩
  · rw [ncard_places_eq (hg k),
      GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq I.E (g k) (hg k) (h k), hdeg]

end GlobalTheory.SplitChoice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsQuotMeas
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgQuot

theorem isMatGroup_GG (k r : ℕ) : PI.IsMatGroup (GG k r) := by

  have hH : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det := by
    have h := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact ⟨⟨_, _, h, (mul_comm _ _).trans h⟩, rfl⟩
  obtain ⟨h1, hmul, hinv⟩ := Formalism.QuantumDeterminants.uHGroup _ _ hH
  refine ⟨?_, h1, hmul, fun a ha => ⟨(hinv a ha).2, Matrix.mul_nonsing_inv a (hinv a ha).1⟩⟩

  show IsClosed {g : Mat k r | gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r}
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem exists_isQuotMeas : ∀ (k r : ℕ) (S : Set (Mat k r)) (μG μS : Measure (Mt k r)), IsClosedSub k r S →
    IsHaarOn (GG k r) μG → IsHaarOn S μS → IsUnimod S μS → ∃ ν : Measure (Mt k r), IsQuotMeas μG μS ν := by
  intro k r S μG μS hS hG hSμ hU
  obtain ⟨hSG, hcl, h1, hmul, hinv⟩ := hS

  have hSm : PI.IsMatGroup S :=
    ⟨hcl, h1, hmul, fun a ha => ⟨hinv a ha, ((isMatGroup_GG k r).2.2.2 a (hSG ha)).2⟩⟩

  exact GlobalTheory.QuotWeil.exists_isQuotM (2 * r + k + 1) (GG k r) S μG μS (isMatGroup_GG k r) hSm hSG hG hSμ hU.1

end GlobalTheory.SgQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsQuotMeasSset
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem exists_isQuotMeas_Sset : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μG μS : Measure (Mt k r)), inWb k r z → 0 < Tz k r z → IsHaarOn (GG k r) μG → IsHaarOn (Sset k r z) μS → ∃ ν : Measure (Mt k r), IsQuotMeas μG μS ν := by
  intro k r z μG μS hz hT hG hS
  obtain ⟨μW, hW⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r z hz hT
  obtain ⟨μN, hN⟩ := Formalism.FourierDecayAlt.P.unipotent_haar_exists k r
  have conv : ∀ {U : Set (Mat k r)} {μ : Measure (Mt k r)}, Formalism.FourierDecayAlt.B.IsHaarOn U μ → IsHaarOn U μ := by
    intro U μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
    exact ⟨inferInstance, h.ne_zero, h.conc, h.left⟩
  obtain ⟨hSg, hsub, hH, hR⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT
    (conv hW) (conv hN)
  have hS' : PI.IsHaarOnM (Sset k r z) μS := hS
  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.MatHaar.haar_unique_locFinite_openPos _ _ _ hSg hH).1 μS hS'
  have hR' : PI.IsRightInvM (Sset k r z) μS := by
    intro s hs
    rw [hc, Measure.map_smul, hR s hs]
  obtain ⟨hGg, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  exact GlobalTheory.QuotWeil.exists_isQuotM _ _ _ μG μS hGg hSg hsub (hGH μG hG).1 hS' hR'

end GlobalTheory.SgInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableUnitaryLeviBlockMapStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_unitaryLeviBlockMap : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∃ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ ∧ ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
  first | exact @GlobalTheory.LeviIso.exists_measurable_levMap | exact GlobalTheory.LeviIso.exists_measurable_levMap | (intros; apply GlobalTheory.LeviIso.exists_measurable_levMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemKsetActsAsGLModSplitPrimeStatement
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_Kset_acts_as_GL_mod_splitPrime : ∀ (I : AutInst) (N p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)) (fr : PlFrame I N p w), I.n = N → p.Prime → Ideal.absNorm w.asIdeal = p → ¬ IsConj I w w → ∀ M : GL (Fin N) (ZMod p), ∃ x ∈ I.Kset, (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = (M : Matrix (Fin N) (Fin N) (ZMod p)) *ᵥ fr.c y) ∧ ∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ¬ IsConj I w u → ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I u.asIdeal • I.Lf := by
  first | exact @GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away | exact GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away | (intros; apply GlobalTheory.RowLev.exists_mem_Kset_actsAs_trivial_away <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBlockFrameOfComplexFlagStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_block_frame_of_complex_flag : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ), Monotone W → W 0 = ⊥ → (∀ b, m ≤ b → W b = ⊤) → (∀ b, Module.finrank ℂ (W (b + 1)) = Module.finrank ℂ (W b) + r b) → ∃ U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ, Biorth r m U (fun b => (U b)ᴴ) ∧ ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
  first | exact @GlobalTheory.RadCov.exists_orthonormal_block_frame | exact GlobalTheory.RadCov.exists_orthonormal_block_frame | (intros; apply GlobalTheory.RadCov.exists_orthonormal_block_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFlagBlockFixingLatticeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_flag_block_fixing_lattice : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ γ : ∀ i, GL (Fin (j i)) I.E, (∀ i y, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ i ↔ y ∈ Λ i) → ∀ g₀ ∈ latGroup I₀ x₀, ∃ g ∈ latGroup I xf, ∃ (Γ : Matrix (Fin I.n) (Fin I.n) I.E) (γ₀ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), (∀ v, uMat (g v) = (I.P v)⁻¹ * Γ.map (I.φ v) * I.P v) ∧ (∀ v, uMat (g₀ v) = (I₀.P v)⁻¹ * γ₀.map (I₀.φ v) * I₀.P v) ∧ (∀ i, Γ * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)) ∧ Γ * T₀ = T₀ * γ₀.map e := by
  first | exact @GlobalTheory.LeviRat.exists_rat_block | exact GlobalTheory.LeviRat.exists_rat_block | (intros; apply GlobalTheory.LeviRat.exists_rat_block <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRepsOfFinite
section
noncomputable section

open scoped Classical

namespace GlobalTheory.RowMassCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.IndefiniteRowSideFullHecke.DiscriminantKernelAutomorphisms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pieces

variable (D : D7) (u : D.what₂.Word)

def FixedFlagSetting (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) : Prop :=
  F0.e = D.sp.hypE ∧ F0.z = D.zmOf u ∧ (Tu D u).Prime ∧ SplitsCompletely (E := D.host.E) (Tu D u)

def RepsPart : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D), HidaSetting D u F0 Λ →
    ∀ s : Finset (LatV D), IsRowReps D F0 s →
      massRows D F0 s = massS D D.R.k * (((Tu D u : ℕ) : ℝ) ^ D.R.k - 1) ^ D.R.f ∧
      massFlagLatticeZero D F0 Λ = massRows D F0 s / (((Tu D u : ℕ) : ℝ) - 1) ^ D.R.f

def LatPart : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D), HidaSetting D u F0 Λ →
    massFlagLatticeZero D F0 Λ = massS D D.R.k * (∑ i ∈ Finset.range D.R.k, ((Tu D u : ℕ) : ℝ) ^ i) ^ D.R.f ∧
    massS D D.R.k * NT D u ^ (D.R.k - 1) ≤ massFlagLatticeZero D F0 Λ

def RowMassesAt : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D), HidaSetting D u F0 Λ →
    (∀ s : Finset (LatV D), IsRowReps D F0 s →
      massRows D F0 s = massS D D.R.k * (((Tu D u : ℕ) : ℝ) ^ D.R.k - 1) ^ D.R.f ∧
      massFlagLatticeZero D F0 Λ = massRows D F0 s / (((Tu D u : ℕ) : ℝ) - 1) ^ D.R.f) ∧
    massFlagLatticeZero D F0 Λ = massS D D.R.k * (∑ i ∈ Finset.range D.R.k, ((Tu D u : ℕ) : ℝ) ^ i) ^ D.R.f ∧
    massS D D.R.k * NT D u ^ (D.R.k - 1) ≤ massFlagLatticeZero D F0 Λ

def RowLatExistsAt : Prop :=
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), FixedFlagSetting D u F0 → ∃ Λ : LatV D, IsRowLat D F0 Λ

def RowRepsExistAt : Prop :=
  ∀ (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : LatV D), HidaSetting D u F0 Λ →
    ∃ s : Finset (LatV D), IsRowReps D F0 s

end Pieces

def RowLatExists : Prop := ∀ (D : D7) (u : D.what₂.Word), RowLatExistsAt D u

def RowDescent : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)), FixedFlagSetting D u F0 →
    ∀ Λ Λ' : LatV D, IsRowLat D F0 Λ → IsRowLat D F0 Λ' →
    ∀ γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
      Formalism.HermitianLatticesTheory.gmap (γ.prodCongr (LinearEquiv.refl D.host.E D.host.E)) (latL D F0 Λ') = latL D F0 Λ →
      ∃ δ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap δ Λ' = Λ

def PairsFinite : Prop :=
  ∀ (D : D7) (u : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)), FixedFlagSetting D u F0 →
    ∃ S : Finset (Submodule (𝓞 D.host.E) ((D.sp.X 0).V × D.host.E)),
      ∀ Λ : LatV D, IsRowLat D F0 Λ → ∃ M ∈ S, ∃ γ ∈ Formalism.HermitianLatticesTheory.isom (D.sp.X 0).hT,
        Formalism.HermitianLatticesTheory.gmap (γ.prodCongr (LinearEquiv.refl D.host.E D.host.E)) M = latL D F0 Λ

section Gmap

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_mul' (a b : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) M = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b M) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one' (M : Submodule (𝓞 K) V) : Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) M = M := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

end Gmap

section Stab

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem one_mem_stabF : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D F0 :=
  ⟨(Formalism.HermitianLatticesTheory.isom _).one_mem, fun j => Submodule.map_id _, rfl⟩

theorem mul_mem_stabF {a b : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ stabF D F0) (hb : b ∈ stabF D F0) :
    a * b ∈ stabF D F0 := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).mul_mem ha.1 hb.1, fun j => ?_, ?_⟩
  · have : ((a * b : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) =
        (a : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ (b : (VS D).V →ₗ[D.host.E] (VS D).V) := rfl
    rw [this, Submodule.map_comp, hb.2.1 j, ha.2.1 j]
  · show a (b F0.z) = F0.z
    rw [hb.2.2, ha.2.2]

theorem inv_mem_stabF {a : (VS D).V ≃ₗ[D.host.E] (VS D).V} (ha : a ∈ stabF D F0) : a⁻¹ ∈ stabF D F0 := by
  refine ⟨(Formalism.HermitianLatticesTheory.isom _).inv_mem ha.1, fun j => ?_, ?_⟩
  · conv_lhs => rw [← ha.2.1 j]
    rw [← Submodule.map_comp]
    have : ((a⁻¹ : (VS D).V ≃ₗ[D.host.E] (VS D).V) : (VS D).V →ₗ[D.host.E] (VS D).V) ∘ₗ
        (a : (VS D).V →ₗ[D.host.E] (VS D).V) = LinearMap.id := by
      ext x
      exact a.symm_apply_apply x
    rw [this, Submodule.map_id]
  · show a.symm F0.z = F0.z
    rw [LinearEquiv.symm_apply_eq, ha.2.2]

def rowSetoid : Setoid {Λ : LatV D // IsRowLat D F0 Λ} where
  r A B := ∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ A.1 = B.1
  iseqv :=
    ⟨fun A => ⟨1, one_mem_stabF D F0, gmap_one' _⟩,
      fun ⟨γ, hγ, h⟩ => ⟨γ⁻¹, inv_mem_stabF D F0 hγ, by rw [← h, ← gmap_mul', inv_mul_cancel, gmap_one']⟩,
      fun ⟨γ, hγ, h⟩ ⟨δ, hδ, h'⟩ => ⟨δ * γ, mul_mem_stabF D F0 hδ hγ, by rw [gmap_mul', h, h']⟩⟩

end Stab

end GlobalTheory.RowMassCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualFlagOfSaturatedIsotropicFlagStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_flag_of_saturated_isotropic_flag : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ (F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (r : ℕ → ℕ), IsDualFlag I.J F (2 * a + 1) ∧ F (2 * a + 1) = lamX I (1, xf) ∧ (∀ i : Fin (a + 1), F i = S i) ∧ (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) ∧ (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) ∧ r a = I.n - 2 * ∑ i, j i ∧ ∀ b, 2 * a + 1 ≤ b → r b = 0 := by
  first | exact @GlobalTheory.RadCov.FullFlag.main | exact GlobalTheory.RadCov.FullFlag.main | (intros; apply GlobalTheory.RadCov.FullFlag.main <;> assumption)
end

