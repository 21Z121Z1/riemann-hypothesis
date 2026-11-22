import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0109
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0866
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecaysOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0356
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1739
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1438
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
import Development.AbelianVarietyTheory.Definitions.Divisors.MemL2OfSmoothVector
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WordAppendSingle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0789

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProduct
section
open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.ZEul

open GlobalTheory.JSW

def partVec {n : ℕ} (l : {l : Fin n → ℕ // Antitone l}) : Fin n → ℤ := fun j => (l.1 j : ℤ)

theorem partVec_injective {n : ℕ} : Function.Injective (partVec (n := n)) := by
  intro a b h
  apply Subtype.ext; funext j
  have := congrFun h j
  simpa [partVec] using this

theorem partVec_valid {n : ℕ} (l : {l : Fin n → ℕ // Antitone l}) :
    (∀ i, 0 ≤ partVec l i) ∧ Antitone (partVec l) :=
  ⟨fun i => Int.natCast_nonneg _, fun a b h => Int.ofNat_le.2 (l.2 h)⟩

theorem mem_range_partVec {n : ℕ} {v : Fin n → ℤ} (hv : (∀ i, 0 ≤ v i) ∧ Antitone v) :
    v ∈ Set.range (partVec (n := n)) :=
  ⟨⟨fun i => (v i).toNat, fun a b h => Int.toNat_le_toNat (hv.2 h)⟩, by
    funext j; simp [partVec, Int.toNat_of_nonneg (hv.1 j)]⟩

theorem rsTerm_partVec (q : ℕ) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    rsTerm q α β x (partVec l) =
      schurAt l.1 α * conj (schurAt l.1 β) * ((q : ℂ) ^ (-(x : ℂ))) ^ (∑ i, l.1 i) := by
  rw [rsTerm, if_pos (partVec_valid l)]
  simp [partVec]

open Classical in

def sqTerm (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : ℝ :=
  if (∀ i, 0 ≤ v i) ∧ Antitone v then
    ‖schurAt (fun i => (v i).toNat) α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x))
  else 0

theorem sqTerm_nonneg (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) : 0 ≤ sqTerm q α x v := by
  unfold sqTerm
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · exact le_rfl

theorem sqTerm_zero (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : sqTerm q α x 0 = 1 := by
  have hs : schurAt (fun _ : Fin n => 0) α = 1 := by rw [schurAt, schur_zero]; simp
  rw [sqTerm, if_pos ⟨fun i => le_rfl, antitone_const⟩]
  simp [hs]

theorem sqTerm_partVec (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (l : {l : Fin n → ℕ // Antitone l}) :
    sqTerm q α x (partVec l) = ‖schurAt l.1 α‖ ^ 2 * (q : ℝ) ^ (-(((∑ i, l.1 i : ℕ) : ℝ) * x)) := by
  rw [sqTerm, if_pos (partVec_valid l)]
  simp [partVec]

theorem norm_cpow_pow (q : ℕ) (hq : 0 < q) (x : ℝ) (k : ℕ) :
    ‖((q : ℂ) ^ (-(x : ℂ))) ^ k‖ = (q : ℝ) ^ (-((k : ℝ) * x)) := by
  rw [norm_pow, Complex.norm_natCast_cpow_of_pos hq]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1; ring

theorem norm_rsTerm_le (q : ℕ) (hq : 0 < q) {n : ℕ} (α β : Fin n → ℂ) (x : ℝ) (v : Fin n → ℤ) :
    ‖rsTerm q α β x v‖ ≤ (sqTerm q α x v + sqTerm q β x v) / 2 := by
  by_cases hv : (∀ i, 0 ≤ v i) ∧ Antitone v
  · rw [rsTerm, if_pos hv, sqTerm, if_pos hv, sqTerm, if_pos hv, norm_mul, norm_mul, Complex.norm_conj,
      norm_cpow_pow q hq]
    have hw : 0 ≤ (q : ℝ) ^ (-(((∑ i, (v i).toNat : ℕ) : ℝ) * x)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [mul_nonneg (sq_nonneg (‖schurAt (fun i => (v i).toNat) α‖ - ‖schurAt (fun i => (v i).toNat) β‖)) hw]
  · rw [rsTerm, if_neg hv, sqTerm, if_neg hv, sqTerm, if_neg hv]; simp

end GlobalTheory.ZEul

namespace GlobalTheory.ZEul

open GlobalTheory.JSW

theorem summable_sqTerm {I : Type} (q : I → ℕ) {n : ℕ} (α : I → Fin n → ℂ) (x : ℝ)
    (h : GlobalTheory.RSPole.eulD q α x ≠ ⊤) :
    Summable fun p : I × {v : Fin n → ℤ // v ≠ 0} => sqTerm (q p.1) (α p.1) x p.2 := by
  set f : I → (Fin n → ℤ) → ℝ≥0∞ := fun i v => ENNReal.ofReal (sqTerm (q i) (α i) x v) with hf
  have hf0 : ∀ i, f i 0 = 1 := fun i => by simp [hf, sqTerm_zero]
  have hloc : ∀ i, ∑' v, f i v = GlobalTheory.RSPole.schurDir (q i) (α i) x := by
    intro i
    rw [← (partVec_injective (n := n)).tsum_eq]
    · rw [GlobalTheory.RSPole.schurDir]
      refine tsum_congr fun l => ?_
      simp only [hf, sqTerm_partVec]
    · intro v hv
      by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
      · exact mem_range_partVec hval
      · exact absurd (by simp [hf, sqTerm, if_neg hval]) hv
  have hE : ∑' l : I →₀ (Fin n → ℤ), l.prod f = GlobalTheory.RSPole.eulD q α x := by
    rw [(GlobalTheory.EulerSum.euler_product_intVec_ennreal n f hf0).2, GlobalTheory.RSPole.eulD]
    exact tprod_congr hloc
  have hinj : Function.Injective fun p : I × {v : Fin n → ℤ // v ≠ 0} => Finsupp.single p.1 p.2.1 := by
    intro p p' hp
    rcases (Finsupp.single_eq_single_iff _ _ _ _).1 hp with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Prod.ext h1 (Subtype.ext h2)
    · exact absurd h1 p.2.2
  have hle : ∑' p : I × {v : Fin n → ℤ // v ≠ 0}, f p.1 p.2 ≤ ∑' l : I →₀ (Fin n → ℤ), l.prod f := by
    have hc : (fun p : I × {v : Fin n → ℤ // v ≠ 0} => f p.1 p.2) =
        fun p => (fun l : I →₀ (Fin n → ℤ) => l.prod f) (Finsupp.single p.1 p.2.1) := by
      funext p; simp only; rw [Finsupp.prod_single_index (hf0 p.1)]
    rw [hc]
    exact ENNReal.tsum_comp_le_tsum_of_injective hinj _
  have hfin : ∑' p : I × {v : Fin n → ℤ // v ≠ 0}, f p.1 p.2 ≠ ⊤ := ne_top_of_le_ne_top (hE ▸ h) hle
  refine (ENNReal.summable_toReal hfin).congr fun p => ?_
  simp only [hf]
  exact ENNReal.toReal_ofReal (sqTerm_nonneg _ _ _ _)

theorem hasSum_rsTerm_local (q : ℕ) {n : ℕ} (α β : Fin n → ℂˣ) (x : ℝ)
    (hs : Summable fun v : Fin n → ℤ => ‖rsTerm q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v‖) :
    HasSum (fun v => rsTerm q (fun j => (α j : ℂ)) (fun j => (β j : ℂ)) x v)
      (locL q (Finset.univ.val.map α) ((Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom))
        (x : ℂ)) := by
  set β' : Fin n → ℂˣ := fun j => Units.map (starRingEnd ℂ).toMonoidHom (β j) with hβ'
  have hconj : ∀ l : Fin n → ℕ, schurAt l (fun j => (β' j : ℂ)) = conj (schurAt l fun j => (β j : ℂ)) := by
    intro l
    rw [schurAt, schurAt, MvPolynomial.eval₂_comp_left, RingHom.ext_int ((starRingEnd ℂ).comp (Int.castRingHom ℂ))
      (Int.castRingHom ℂ)]
    rfl
  have hm : (Finset.univ.val.map β).map (Units.map (starRingEnd ℂ).toMonoidHom) = Finset.univ.val.map β' :=
    Multiset.map_map _ _ _
  rw [hm]
  have hs' : Summable fun l : {l : Fin n → ℕ // Antitone l} =>
      ‖schurAt (padTo le_rfl l.1) (fun i => (α i : ℂ)) * schurAt l.1 (fun j => (β' j : ℂ))‖ *
        ‖(q : ℂ) ^ (-(x : ℂ))‖ ^ (∑ i, l.1 i) := by
    refine (hs.comp_injective partVec_injective).congr fun l => ?_
    simp only [Function.comp, rsTerm_partVec, padTo_self, hconj, norm_mul, norm_pow, Complex.norm_conj]
  have hc := cauchy_locL le_rfl α β' q (x : ℂ) hs'
  rw [← (partVec_injective (n := n)).hasSum_iff]
  · convert hc using 1
    funext l
    simp only [Function.comp, rsTerm_partVec, padTo_self, hconj]
  · intro v hv
    by_cases hval : (∀ j, 0 ≤ v j) ∧ Antitone v
    · exact absurd (mem_range_partVec hval) hv
    · rw [rsTerm, if_neg hval]

theorem hasSum_rsTerm_finsupp : ∀ {I : Type} (q : I → ℕ) {n : ℕ} (α β : I → Fin n → ℂˣ) (x : ℝ), 1 < x → (∀ i, 2 ≤ q i) →
    GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    HasSum (fun l : I →₀ (Fin n → ℤ) => l.prod fun i v => GlobalTheory.ZEul.rsTerm (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v)
      (∏' i, GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i)) ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) := by
  intro I q n α β x _ hq hα hβ
  set f : I → (Fin n → ℤ) → ℂ := fun i v => rsTerm (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v with hfdef
  have hf0 : ∀ i, f i 0 = 1 := fun i => rsTerm_zero _ _ _ _
  have hA := summable_sqTerm q (fun i j => (α i j : ℂ)) x hα
  have hB := summable_sqTerm q (fun i j => (β i j : ℂ)) x hβ
  have hsum : Summable fun p : I × {v : Fin n → ℤ // v ≠ 0} => ‖f p.1 p.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun p => by
        simpa only [hfdef] using norm_rsTerm_le (q p.1) (by have := hq p.1; omega) (fun j => (α p.1 j : ℂ)) (fun j => (β p.1 j : ℂ)) x p.2.1) ((hA.add hB).div_const 2)
  obtain ⟨hN, -, hE⟩ := GlobalTheory.EulerSum.euler_product_intVec n f hf0 hsum
  have hloc : ∀ i, ∑' v, f i v = locL (q i) (Finset.univ.val.map (α i))
      ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) :=
    fun i => (hasSum_rsTerm_local (q i) (α i) (β i) x (GlobalTheory.EulerSum.summable_norm_local f hsum i)).tsum_eq
  rw [← hE.trans (tprod_congr hloc)]
  exact hN.of_norm.hasSum

end GlobalTheory.ZEul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnAbsDetRpowLeOneFundamentalDomain
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open GlobalTheory.UnitaryBC GlobalTheory.ShortVecDecay
open scoped ComplexConjugate nonZeroDivisors ContDiff ENNReal

namespace GlobalTheory.RSThetaLow

theorem exists_tsum_zpow_le_low {T s : ℝ} (hT : 1 < T) (hs : 0 < s) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ u : ℝ, 0 < u →
    ∑' n : ℤ, (if T ^ n * u ≤ 1 then ENNReal.ofReal ((T ^ n * u) ^ s) else 0) ≤ B := by
  obtain ⟨B, hB, h⟩ := GlobalTheory.RSTheta.exists_tsum_zpow_le hT hs
  refine ⟨B, hB, fun u hu => ?_⟩
  have hT0 : 0 < T := one_pos.trans hT
  refine le_of_eq_of_le ?_ (h u⁻¹ (inv_pos.2 hu))
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply]
  have hp : 0 < T ^ n * u⁻¹ := by positivity
  have e : T ^ (-n) * u = (T ^ n * u⁻¹)⁻¹ := by
    rw [_root_.zpow_neg, mul_inv, inv_inv]
  rw [e, Real.inv_rpow hp.le, Real.rpow_neg hp.le]
  simp only [inv_le_one₀ hp]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem integrableOn_absDet_rpow (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ s)
      (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  set δ : GA E a → ℝ := fun g => (ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hm : MeasurableSet {g | δ g ≤ 1} := (isClosed_le hδc continuous_const).measurableSet
  have hc : Continuous fun g => δ g ^ s := hδc.rpow_const fun g => Or.inl (hδ0 g).ne'
  refine ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (.of_forall fun g => Real.rpow_nonneg (hδ0 g).le _)).2 ?_⟩
  rw [Set.inter_comm, ← Measure.restrict_restrict hm, ← lintegral_indicator hm]
  let φ : (ratGL E a).range × ℤ → latticeGL E a := fun p =>
    ⟨p.1 * splitCentre E a 1 ^ p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (zpow_mem_latticeGL _)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨_, γ, rfl⟩, n⟩ ⟨⟨_, γ', rfl⟩, n'⟩ h
      have h1 : ratGL E a γ * splitCentre E a 1 ^ n = ratGL E a γ' * splitCentre E a 1 ^ n' := congrArg Subtype.val h
      have h2 := congrArg (fun x => δ (x * 1)) h1
      simp only [mul_assoc, hδr, hδz] at h2
      obtain rfl : n = n' := zpow_right_injective₀ (one_pos.trans hT1) hT1.ne' (mul_right_cancel₀ (hδ0 1).ne' h2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h1)) rfl
    · rintro ⟨g, hg⟩
      obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
      exact ⟨⟨⟨_, γ, rfl⟩, n⟩, rfl⟩
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hd := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h1 : μ (GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E a)) ≠ ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hd]; exact measure_ne_top _ _
  rw [← GlobalTheory.ThetaUnfold.lintegral_unfold μ (latticeGL E a) (ratGL E a).range (fun n : ℤ => splitCentre E a 1 ^ n)
    (Equiv.ofBijective φ hφ) (fun _ => rfl) hd h𝓕 _
    (by rintro _ ⟨γ, rfl⟩ g; simp only [Set.indicator_apply, Set.mem_setOf_eq]; rw [show δ (ratGL E a γ * g) = δ g from hδr γ g])
    ((hc.measurable.ennreal_ofReal.indicator hm).aemeasurable)]
  obtain ⟨B, hB, h⟩ := exists_tsum_zpow_le_low hT1 hs
  refine (lintegral_mono (g := fun _ => B) fun g => ?_).trans_lt ?_
  · refine le_of_eq_of_le (tsum_congr fun n => ?_) (h _ (hδ0 g))
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [hδz]
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top hB.lt_top h1.lt_top

theorem integrableOn_absDet_rpow_low : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 0 < a →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ →
    ∀ s : ℝ, 0 < s → IntegrableOn (fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ s)
      (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ :=
  fun _ _ _ _ _ ha μ _ _ h𝓕 _ hs => integrableOn_absDet_rpow ha μ h𝓕 hs

end GlobalTheory.RSThetaLow

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableOnMinAbsDetInvFundamentalDomain
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal

noncomputable section

open GlobalTheory.UnitaryBC

namespace GlobalTheory.FinVolGL

theorem exists_tsum_min_le {T : ℝ} (hT : 1 < T) : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ u : ℝ, 0 < u →
    ∑' n : ℤ, ENNReal.ofReal (min (T ^ n * u) (T ^ n * u)⁻¹) ≤ B := by
  have hT0 : 0 < T := one_pos.trans hT
  have hq0 : 0 ≤ T⁻¹ := inv_nonneg.2 hT0.le
  have hq : T⁻¹ < 1 := inv_lt_one_of_one_lt₀ hT
  have hsum : Summable fun k : ℤ => T * T⁻¹ ^ k.natAbs :=
    (Summable.of_nat_of_neg (by simpa using summable_geometric_of_lt_one hq0 hq)
      (by simpa using summable_geometric_of_lt_one hq0 hq)).mul_left T
  refine ⟨∑' k : ℤ, ENNReal.ofReal (T * T⁻¹ ^ k.natAbs), hsum.tsum_ofReal_ne_top, fun u hu => ?_⟩
  obtain ⟨m, h1, h2⟩ := exists_mem_Ico_zpow hu hT
  rw [← (Equiv.subRight m).tsum_eq]
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  rw [Equiv.subRight_apply]
  have hp : 0 < T ^ (k - m) := zpow_pos hT0 _
  have e1 : T ^ (k - m) * T ^ m = T ^ k := by rw [← zpow_add₀ hT0.ne', sub_add_cancel]
  have e2 : T ^ (k - m) * T ^ (m + 1) = T ^ (k + 1) := by
    rw [← zpow_add₀ hT0.ne']; congr 1; ring
  have hv1 : T ^ k ≤ T ^ (k - m) * u := e1 ▸ mul_le_mul_of_nonneg_left h1 hp.le
  have hv2 : T ^ (k - m) * u < T ^ (k + 1) := e2 ▸ mul_lt_mul_of_pos_left h2 hp
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · refine (min_le_right _ _).trans ?_
    have h3 := inv_anti₀ (zpow_pos hT0 _) hv1
    rw [zpow_natCast, ← inv_pow] at h3
    rw [Int.natAbs_natCast]
    exact h3.trans (le_mul_of_one_le_left (pow_nonneg hq0 _) hT.le)
  · refine (min_le_left _ _).trans (hv2.le.trans (le_of_eq ?_))
    rw [zpow_add_one₀ hT0.ne', _root_.zpow_neg, zpow_natCast, Int.natAbs_neg, Int.natAbs_natCast, inv_pow, mul_comm]

theorem integrableOn_min_absDet : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ), 0 < m →
    ∀ (μ : Measure (GA E m)) [μ.IsHaarMeasure] (𝓕 : Set (GA E m)),
      IsFundamentalDomain (ratGL E m).range 𝓕 μ →
      IntegrableOn (fun h : GA E m => min (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)
        (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)⁻¹) 𝓕 μ := by
  intro E _ _ _ a ha μ _ 𝓕 h𝓕
  set δ : GA E a → ℝ := fun g => (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det g) : ℝ) with hδ
  have hδc : Continuous δ := GlobalTheory.RSTheta.continuous_absDet
  have hδ0 : ∀ g, 0 < δ g := fun g => (GroundTheory.Global.IdeleGroup.ideleModule E _).2
  have hδr : ∀ γ g, δ (ratGL E a γ * g) = δ g := fun γ g => by
    simp only [hδ, map_mul, GlobalTheory.ShortVecDecay.ideleModule_det_rat, one_mul]
  set T : ℝ := Real.exp 1 ^ (a * Module.finrank ℚ E) with hT
  have hT1 : 1 < T := one_lt_pow₀ (Real.one_lt_exp_iff.2 one_pos) (Nat.mul_pos ha Module.finrank_pos).ne'
  have hδz : ∀ (n : ℤ) g, δ (splitCentre E a 1 ^ n * g) = T ^ n * δ g := GlobalTheory.RSTheta.absDet_zpow_mul
  have hc : Continuous fun g => min (δ g) (δ g)⁻¹ := hδc.min (hδc.inv₀ fun g => (hδ0 g).ne')
  refine ⟨hc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (.of_forall fun g => le_min (hδ0 g).le (inv_nonneg.2 (hδ0 g).le))).2 ?_⟩
  let φ : (ratGL E a).range × ℤ → latticeGL E a := fun p =>
    ⟨p.1 * splitCentre E a 1 ^ p.2, mul_mem (Subgroup.mem_sup_left p.1.2) (zpow_mem_latticeGL _)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨⟨_, γ, rfl⟩, n⟩ ⟨⟨_, γ', rfl⟩, n'⟩ h
      have h1 : ratGL E a γ * splitCentre E a 1 ^ n = ratGL E a γ' * splitCentre E a 1 ^ n' := congrArg Subtype.val h
      have h2 := congrArg (fun x => δ (x * 1)) h1
      simp only [mul_assoc, hδr, hδz] at h2
      obtain rfl : n = n' := zpow_right_injective₀ (one_pos.trans hT1) hT1.ne' (mul_right_cancel₀ (hδ0 1).ne' h2)
      exact Prod.ext (Subtype.ext (mul_right_cancel h1)) rfl
    · rintro ⟨g, hg⟩
      obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hg
      exact ⟨⟨⟨_, γ, rfl⟩, n⟩, rfl⟩
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hd := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have h1 : μ (GlobalTheory.AutomorphicL2Unitary.stdDom (latticeGL E a)) ≠ ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hd]; exact measure_ne_top _ _
  rw [← GlobalTheory.ThetaUnfold.lintegral_unfold μ (latticeGL E a) (ratGL E a).range (fun n : ℤ => splitCentre E a 1 ^ n)
    (Equiv.ofBijective φ hφ) (fun _ => rfl) hd h𝓕 (fun g => ENNReal.ofReal (min (δ g) (δ g)⁻¹))
    (by rintro _ ⟨γ, rfl⟩ g; simp only [hδr])
    hc.measurable.ennreal_ofReal.aemeasurable]
  obtain ⟨B, hB, h⟩ := exists_tsum_min_le hT1
  refine (lintegral_mono (g := fun _ => B) fun g => ?_).trans_lt ?_
  · refine le_of_eq_of_le (tsum_congr fun n => ?_) (h _ (hδ0 g))
    simp only [hδz]
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top hB.lt_top h1.lt_top

example : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ), 0 < m →
    ∀ (μ : Measure (GA E m)) [μ.IsHaarMeasure] (𝓕 : Set (GA E m)),
      IsFundamentalDomain (ratGL E m).range 𝓕 μ →
      IntegrableOn (fun h : GA E m => min (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)
        (GroundTheory.Global.IdeleGroup.ideleModule E (GeneralLinearGroup.det h) : ℝ)⁻¹) 𝓕 μ := integrableOn_min_absDet

end GlobalTheory.FinVolGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocFacOfNeg
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.RSCell

def sphZ (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (ν : Fin n → ℤ) : ℂ :=
  if Antitone ν then GlobalTheory.JSW.sphW q α (fun i => (ν i).toNat) else 0

def locFac (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) (ν : Fin n → ℤ) : ℝ≥0∞ :=
  if Antitone ν ∧ ∀ i, 0 ≤ ν i then
    ENNReal.ofReal (‖GlobalTheory.JSW.schurAt (fun i => (ν i).toNat) α‖ ^ 2 *
      (q : ℝ) ^ (-(((∑ i, (ν i).toNat : ℕ) : ℝ) * x)))
  else 0

def cellProd {E : Type} [Field E] [NumberField E] {n : ℕ} (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ)
    (ν : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) : ℝ≥0∞ :=
  ∏ w ∈ ν.support, if h : w ∈ T then 1 else locFac (Ideal.absNorm w.asIdeal) (α ⟨w, h⟩) x (ν w)

def bInt {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (ℓ : Fin a) (F : GA E a → ℂ)
    (Φ : (Fin a → Cinf E) → ℂ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (x : ℝ) (g : GA E a) : ℝ≥0∞ :=
  ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit F) (GlobalTheory.JSW.whit F) Φ J η g (g.val ℓ)‖ₑ *
    ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x)

theorem locFac_zero (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) : locFac q α x 0 = 1 := by
  have h : (fun i : Fin n => ((0 : Fin n → ℤ) i).toNat) = fun _ => 0 := funext fun _ => rfl
  rw [locFac, if_pos (show Antitone (0 : Fin n → ℤ) ∧ ∀ i, (0 : ℤ) ≤ (0 : Fin n → ℤ) i from ⟨fun _ _ _ => le_rfl, fun _ => le_rfl⟩), h]
  simp [GlobalTheory.JSW.schurAt, GlobalTheory.JSW.schur_zero]

theorem locFac_of_neg (q : ℕ) {n : ℕ} (α : Fin n → ℂ) (x : ℝ) {ν : Fin n → ℤ} {i : Fin n} (h : ν i < 0) :
    locFac q α x ν = 0 := by
  rw [locFac, if_neg fun h' => absurd (h'.2 i) (not_le.2 h)]

example {E : Type} [Field E] [NumberField E] {n : ℕ} (T : Finset (HeightOneSpectrum (𝓞 E)))
    (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin n → ℂ) (x : ℝ) : cellProd T α x 0 = 1 := by
  simp [cellProd]

end GlobalTheory.RSCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModerateGrowthRapidKernelOperator
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped Pointwise

noncomputable section

namespace GlobalTheory.MSpanDecay

theorem growth_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F : GA E a → ℂ) (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.MSpanDecay.Growth F → GlobalTheory.MSpanDecay.Growth (fun g : GA E a => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) := by
  intro E _ _ _ a F X _ ν _ k γ hk hF g
  obtain ⟨C, N, hC⟩ := hF g
  set I := ∫ x, ‖k x‖ * height (γ x) ^ N ∂ν with hI
  refine ⟨|C| * ((a : ℝ) + 1) ^ N * I, N, fun y => ?_⟩
  have hint := (hk.2.2 N).const_mul (|C| * ((a : ℝ) + 1) ^ N * height y ^ N)
  have hb : ∀ x, ‖k x * F (g * infGL E a y * infGL E a (γ x))‖ ≤
      |C| * ((a : ℝ) + 1) ^ N * height y ^ N * (‖k x‖ * height (γ x) ^ N) := by
    intro x
    rw [mul_assoc g, ← map_mul, norm_mul]
    have h1 := hC (y * γ x)
    have hm := GlobalTheory.HCF.ModGrowth.height_mul_le y (γ x)
    have hy := one_le_height y
    have hg := one_le_height (γ x)
    have hz := one_le_height (y * γ x)
    have e1 : height (y * γ x) ^ N ≤ (((a : ℝ) + 1) * (height y * height (γ x))) ^ N :=
      pow_le_pow_left₀ (by linarith) hm N
    have e2 : ‖F (g * infGL E a (y * γ x))‖ ≤ |C| * ((((a : ℝ) + 1) * (height y * height (γ x))) ^ N) :=
      h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (by linarith) N)).trans
        (mul_le_mul_of_nonneg_left e1 (abs_nonneg C)))
    calc ‖k x‖ * ‖F (g * infGL E a (y * γ x))‖ ≤ ‖k x‖ * (|C| * ((((a : ℝ) + 1) * (height y * height (γ x))) ^ N)) :=
          mul_le_mul_of_nonneg_left e2 (norm_nonneg _)
      _ = |C| * ((a : ℝ) + 1) ^ N * height y ^ N * (‖k x‖ * height (γ x) ^ N) := by
          rw [mul_pow, mul_pow]; ring
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hb)).trans_eq ?_
  rw [integral_const_mul, hI]
  ring

end GlobalTheory.MSpanDecay
end
end

