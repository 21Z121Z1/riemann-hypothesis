import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0054
import Formalism.HermitianLattices.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermLevelZeroAndBoundedRepresentatives
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverRelationUniqueness
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0055
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0024
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0051
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0037
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0022
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumAbsNormRpowNegLeDedekindZetaBoundStatement
section
open MeasureTheory NumberField Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_absNorm_rpow_neg_le_dedekindZeta_bound : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ), 1 < s → ∀ (S : Finset (Ideal (𝓞 K))), (∀ I ∈ S, I ≠ ⊥) → ∑ I ∈ S, (Ideal.absNorm I : ℝ) ^ (-s) ≤ (s / (s - 1)) ^ Module.finrank ℚ K := by
  first | exact @GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le | exact GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le | (intros; apply GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBoundStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_exponents_nonneg_and_defect_group_bound : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → 0 ≤ S.a ∧ 0 ≤ S.vD ∧ (∀ l, S.D l ∈ L.O) ∧ (S.q : ℝ) ^ S.a ≤ S.Hp ∧ 1 ≤ S.Hp ∧ (∃ i : ℕ, (i : ℤ) ≤ S.a ∧ S.be d Λ = S.q ^ i) ∧ (S.BBzero d Λ ↔ S.be d Λ = 1) ∧ (¬ S.BBzero d Λ → (S.q : ℝ) ≤ S.Hp) ∧ (∀ y ∈ S.sat Λ, algebraMap F E ((S.ϖ : F) ^ S.a) • y ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, S.levC d Λ y = 0 ↔ y ∈ S.M d Λ) ∧ ∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔ ∃ y₁ ∈ S.spanTo S.f j ⊔ S.spanTo S.f' j, y - y₁ ∈ S.M d Λ := by
  first | exact @GlobalTheory.HL.Defect.exponents_and_defect | exact GlobalTheory.HL.Defect.exponents_and_defect | (intros; apply GlobalTheory.HL.Defect.exponents_and_defect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermFramesCongrModThetaUnitriangularStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_frames_congr_mod_theta_unitriangular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : GlobalTheory.HL.Frames L r k) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (y x : Fin (r + 1) → S.V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a, B a a = 1) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = 1) → (∀ b, y b = ∑ a, B a b • S.f a) → (∀ b, x b = ∑ a, B' a b • S.f' a) → (∀ a, y a ∈ Λ) → (∀ b, x b ∈ Λ) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, S.InTh Λ (x b - ∑ a, ξ a b • y a) := by
  first | exact @GlobalTheory.HL.FrameChange.frames_congr | exact GlobalTheory.HL.FrameChange.frames_congr | (intros; apply GlobalTheory.HL.FrameChange.frames_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermLevelZeroAndBoundedRepresentativesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termLevel_zero_and_bounded_representatives : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∀ y ∈ S.sat Λ, S.levC d Λ y = 0 ↔ y ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, ∀ j, S.levC d Λ y ≤ j ↔ ∃ y₁ ∈ (S.spanTo S.f j ⊔ S.spanTo S.f' j), y - y₁ ∈ S.M d Λ) ∧ (∀ y ∈ S.sat Λ, ∀ m ∈ S.M d Λ, S.levC d Λ (y + m) = S.levC d Λ y) ∧ ∀ (al al' : Fin (r + 1) → E) (j : ℕ), S.lev (S.fr d Λ) (S.fr' d Λ) (∑ i, al i • S.fr d Λ i + ∑ i, al' i • S.fr' d Λ i) ≤ j ↔ ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i) := by
  first | exact @GlobalTheory.HL.LevelRep.level_rep | exact GlobalTheory.HL.LevelRep.level_rep | (intros; apply GlobalTheory.HL.LevelRep.level_rep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverRelationUniquenessStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_over_relation_uniqueness : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d₁ d : LocNG.Datum P) (t₁ t : Term V M r), LocNG.IsTermOver P d₁ t₁ → LocNG.IsTermOver P d t → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat t₁.f t₁.f' ∈ c1 → (H.Zhat t.f t.f' ∈ c1 ↔ ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t.f j = ∑ i, A i j • s (t₁.f i)) ∧ ∀ j, t.f' j = ∑ i, A' i j • s (t₁.f' i)) := by
  first | exact @GlobalTheory.HL.PairingClass.mem_class_iff | exact GlobalTheory.HL.PairingClass.mem_class_iff | (intros; apply GlobalTheory.HL.PairingClass.mem_class_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TraceEqSumLocalTracesAbovePrime
section
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocalTraceSum

open Filter Topology TensorProduct

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem t2 : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

theorem isOpen_lt (γ : ValueGroupWithZero K) : IsOpen {x : K | valuation K x < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hγ : γ ≠ 0 := (lt_of_le_of_lt zero_le hx).ne'
  refine (IsValuativeTopology.hasBasis_nhds' x).mem_iff.2 ⟨γ, hγ, fun y hy => ?_⟩
  have := (valuation K).map_add_lt (x := y - x) (y := x) hy hx
  simpa using this

theorem tendsto_pow {x : K} (h : valuation K x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

variable {l : ℕ} [Fact l.Prime] [Algebra ℚ_[l] K]

theorem contSMul (hc : Continuous (algebraMap ℚ_[l] K)) : ContinuousSMul ℚ_[l] K :=
  continuousSMul_of_algebraMap _ _ hc

variable {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

theorem continuous_algHom [FiniteDimensional ℚ_[l] K] (hc : Continuous (algebraMap ℚ_[l] K))
    (τ : K →ₐ[ℚ_[l]] Ω) : Continuous τ := by
  have := contSMul hc
  have : T2Space K := t2
  exact τ.toLinearMap.continuous_of_finiteDimensional

theorem norm_lt_one [FiniteDimensional ℚ_[l] K] (hc : Continuous (algebraMap ℚ_[l] K))
    (τ : K →ₐ[ℚ_[l]] Ω) {x : K} (h : valuation K x < 1) : ‖τ x‖ < 1 := by
  have h1 := ((continuous_algHom hc τ).tendsto 0).comp (tendsto_pow h)
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  simpa [Function.comp_def] using h1

end Local

section Place

variable {F : Type} [Field F] [NumberField F] {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω]

theorem norm_int_le (σ : F →+* Ω) (a : 𝓞 F) : ‖σ a‖ ≤ 1 := by
  have h : IsIntegral ℤ (σ a) := a.isIntegral_coe.map σ.toIntAlgHom
  have h2 : IsIntegral (NormedField.valuation (K := Ω)).integer (σ a) := h.tower_top
  have := (Valuation.integer.integers _).mem_of_integral h2
  exact this

def ker (σ : F →+* Ω) : Ideal (𝓞 F) where
  carrier := {a | ‖σ a‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, RingOfIntegers.coe_eq_algebraMap, map_add] at *
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le σ c)) ha

theorem mem_ker (σ : F →+* Ω) (a : 𝓞 F) : a ∈ ker σ ↔ ‖σ a‖ < 1 := Iff.rfl

theorem ker_isPrime (σ : F →+* Ω) : (ker σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_ker]; simp
  · intro a b hab
    rw [mem_ker] at hab
    by_contra h
    rw [not_or, mem_ker, mem_ker, not_lt, not_lt] at h
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, norm_mul] at hab
    nlinarith [h.1, h.2]

theorem norm_le_one (σ : F →+* Ω) (p : HeightOneSpectrum (𝓞 F)) (hp : p.asIdeal = ker σ)
    {a : F} (ha : p.valuation F a ≤ 1) : ‖σ a‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := p.exists_primeCompl_mul_eq_of_integer a ha
  have hd : ¬ ‖σ (d : 𝓞 F)‖ < 1 := by
    rw [← mem_ker, ← hp]; exact d.2
  have h1 : ‖σ a‖ * ‖σ (d : 𝓞 F)‖ = ‖σ n‖ := by
    rw [← norm_mul, ← map_mul]; exact congrArg (fun x => ‖σ x‖) h
  have h2 := norm_int_le σ n
  nlinarith [norm_nonneg (σ a), not_lt.1 hd]

end Place

section Ext

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]
  {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[l] K] {Ω : Type} [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]

theorem norm_l_lt : ‖(l : Ω)‖ < 1 := by
  have : (l : Ω) = algebraMap ℚ_[l] Ω l := by simp
  rw [this, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem exists_ext (hc : Continuous (algebraMap ℚ_[l] K)) (ι : F →+* K) (hι : DenseRange ι)
    (σ : F →+* Ω) (h : ∀ a : F, valuation K (ι a) < 1 → ‖σ a‖ ≤ 1) :
    ∃ τ : K →ₐ[ℚ_[l]] Ω, ∀ a, τ (ι a) = σ a := by
  have := contSMul hc
  have : T2Space K := t2
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] _).injective
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ_[l] _).injective
  let φ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] K :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ι.toRatAlgHom (fun _ _ => .all _ _)
  let ψ : ℚ_[l] ⊗[ℚ] F →ₐ[ℚ_[l]] Ω :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) σ.toRatAlgHom (fun _ _ => .all _ _)
  have hφ : ∀ c a, φ (c ⊗ₜ a) = c • ι a := fun c a => by simp [φ, Algebra.smul_def]
  have hψ : ∀ c a, ψ (c ⊗ₜ a) = c • σ a := fun c a => by simp [ψ, Algebra.smul_def]
  have hsurj : Function.Surjective φ := by
    have hcl : IsClosed (LinearMap.range φ.toLinearMap : Set K) :=
      Submodule.closed_of_finiteDimensional _
    intro x
    have : x ∈ (LinearMap.range φ.toLinearMap : Set K) := by
      refine hι.induction_on x hcl fun a => ⟨1 ⊗ₜ a, ?_⟩
      simp [hφ]
    exact this
  let G : AddSubgroup (K × Ω) := ((ι.prod σ).toAddMonoidHom.range).topologicalClosure
  have hG : ∀ z, (φ z, ψ z) ∈ G := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact G.zero_mem
    | add x y hx hy => simpa using G.add_mem hx hy
    | tmul c a =>
      rw [hφ, hψ]
      refine (Padic.denseRange_ratCast l).induction_on c ?_ fun q => ?_
      · exact (AddSubgroup.isClosed_topologicalClosure _).preimage
          (f := fun c : ℚ_[l] => (c • ι a, c • σ a)) (by fun_prop)
      · refine AddSubgroup.le_topologicalClosure _ ⟨(q : F) * a, ?_⟩
        simp [Algebra.smul_def]
  have hl : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl' : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hker : ∀ z, φ z = 0 → ψ z = 0 := by
    intro z hz
    have hb : ∀ k : ℕ, ‖ψ z‖ ≤ ‖(l : Ω)‖ ^ k := by
      intro k
      have hcl : IsClosed ({w : K × Ω | valuation K w.1 < valuation K ((l : K) ^ k)}ᶜ ∪
          {w : K × Ω | ‖w.2‖ ≤ ‖(l : Ω)‖ ^ k}) :=
        (((isOpen_lt _).preimage continuous_fst).isClosed_compl).union
          (isClosed_le (by fun_prop) continuous_const)
      have hsub := closure_minimal (s := ((ι.prod σ).toAddMonoidHom.range : Set (K × Ω))) ?_ hcl
      · rcases hsub (hG z) with h1 | h1
        · exfalso
          apply h1
          simp only [Set.mem_setOf_eq, hz, map_zero]
          exact zero_lt_iff.2 (by simp [hl])
        · exact h1
      · rintro _ ⟨a, rfl⟩
        by_cases ha : valuation K (ι a) < valuation K ((l : K) ^ k)
        · right
          have h2 := h (a / (l : F) ^ k) (by
            rw [map_div₀, map_div₀, div_lt_one₀ (zero_lt_iff.2 (by simp [hl]))]
            simpa using ha)
          rw [map_div₀, norm_div, div_le_one (by simp [hl'])] at h2
          simpa using h2
        · left; exact ha
    have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (norm_l_lt (l := l) (Ω := Ω))) hb
    exact norm_le_zero_iff.1 this
  refine ⟨AlgHom.liftOfSurjective φ hsurj ψ (fun z hz => hker z hz), fun a => ?_⟩
  have h1 : ι a = φ (1 ⊗ₜ a) := by simp [hφ]
  rw [h1]
  exact (AlgHom.liftOfSurjective_apply φ hsurj ψ _ _).trans (by rw [hψ, one_smul])

end Ext

theorem sum_trace_eq : ∀ {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ p, p ∈ S ↔ (l : 𝓞 F) ∈ p.asIdeal) → ∀ (K : S → Type) [∀ p, Field (K p)] [∀ p, Algebra ℚ_[l] (K p)] [∀ p, FiniteDimensional ℚ_[l] (K p)] [∀ p, ValuativeRel (K p)] [∀ p, TopologicalSpace (K p)] (ι : ∀ p, F →+* K p), (∀ p, IsNonarchimedeanLocalField (K p)) → (∀ p, Continuous (algebraMap ℚ_[l] (K p))) → (∀ p, DenseRange (ι p)) → (∀ p (x y : F), (ι p x ≤ᵥ ι p y) ↔ p.1.valuation F x ≤ p.1.valuation F y) → ∀ a : F, ∑ p, Algebra.trace ℚ_[l] (K p) (ι p a) = ((Algebra.trace ℚ F a : ℚ) : ℚ_[l]) := by
  intro F _ _ l _ S hS K _ _ _ _ _ ι hK hc hι hv a
  classical
  let Ω := PadicAlgCl l
  have hv' : ∀ p (x : F), valuation (K p) (ι p x) < 1 ↔ p.1.valuation F x < 1 := by
    intro p x
    rw [← not_le, ← not_le, not_iff_not, ← map_one (valuation (K p)), ← map_one (ι p),
      ← Valuation.Compatible.vle_iff_le (v := valuation (K p)), hv, map_one]
  have hch : ∀ p, CharZero (K p) := fun p =>
    charZero_of_injective_algebraMap (algebraMap ℚ_[l] _).injective
  have hker : ∀ (p : S) (τ : K p →ₐ[ℚ_[l]] Ω), p.1.asIdeal = ker (τ.toRingHom.comp (ι p)) := by
    intro p τ
    refine p.1.isMaximal.eq_of_le (ker_isPrime _).ne_top fun x hx => ?_
    rw [mem_ker]
    exact norm_lt_one (hc p) τ ((hv' p x).2 ((p.1.valuation_lt_one_iff_mem x).2 hx))
  let e : (Σ p : S, (K p →ₐ[ℚ_[l]] Ω)) → (F →ₐ[ℚ] Ω) := fun t =>
    (t.2.toRingHom.comp (ι t.1)).toRatAlgHom
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨p, τ⟩ ⟨q, τ'⟩ h
      have h1 : τ.toRingHom.comp (ι p) = τ'.toRingHom.comp (ι q) :=
        RingHom.ext fun x => DFunLike.congr_fun h x
      have hpq : p = q := by
        apply Subtype.ext
        apply HeightOneSpectrum.ext
        rw [hker p τ, hker q τ', h1]
      subst hpq
      congr 1
      apply DFunLike.coe_injective
      exact (hι p).equalizer (continuous_algHom (hc p) τ) (continuous_algHom (hc p) τ')
        (funext fun x => DFunLike.congr_fun h1 x)
    · intro σ
      have hl : (l : 𝓞 F) ∈ ker σ.toRingHom := by
        rw [mem_ker]
        simpa using norm_l_lt (l := l) (Ω := Ω)
      let p : HeightOneSpectrum (𝓞 F) := ⟨ker σ.toRingHom, ker_isPrime _, fun h => by
        rw [h, Ideal.mem_bot] at hl
        exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hl)⟩
      have hp : p ∈ S := (hS p).2 hl
      obtain ⟨τ, hτ⟩ := exists_ext (hc ⟨p, hp⟩) (ι ⟨p, hp⟩) (hι _) σ.toRingHom
        (fun x hx => norm_le_one _ p rfl ((hv' ⟨p, hp⟩ x).1 hx).le)
      exact ⟨⟨⟨p, hp⟩, τ⟩, AlgHom.ext hτ⟩
  apply (algebraMap ℚ_[l] Ω).injective
  rw [map_sum, map_ratCast]
  have h1 := trace_eq_sum_embeddings (K := ℚ) Ω (x := a)
  rw [eq_ratCast] at h1
  rw [h1, ← he.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [trace_eq_sum_embeddings Ω]
  rfl

end GlobalTheory.LocalTraceSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TupleJacobianRightMulIsometryStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuple_jacobian_rightMul_isometry : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ m : ℕ, (∀ A : Matrix (Fin m) (Fin m) E, IsUnit A.det → ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x => rmul x A) '' T) ∧ cont (tupLat L Λ m) ((fun x => rmul x A) '' T) = (resQ ϖ : ℝ) ^ (-(vE L ϖ (A.det * L.cj A.det) * n)) * cont (tupLat L Λ m) T) ∧ ∀ g ∈ isomG L Hm, ∀ T, IsCO (tupLat L Λ m) T → IsCO (tupLat L Λ m) ((fun x a => g (x a)) '' T) ∧ cont (tupLat L Λ m) ((fun x a => g (x a)) '' T) = cont (tupLat L Λ m) T := by
  first | exact @GlobalTheory.HL.TupleJac.tuple_jacobian | exact GlobalTheory.HL.TupleJac.tuple_jacobian | (intros; apply GlobalTheory.HL.TupleJac.tuple_jacobian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupOrthogonalComplementUnimodular
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.Unimod

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_swap (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHerm L Hm)
    (x y : Fin n → E) : hf L Hm x y = L.cj (hf L Hm y x) := by
  have h : ∀ i j, L.cj (Hm j i) = Hm i j := fun i j => congrFun (congrFun hH i) j
  simp only [hf, map_sum, map_mul, L.cj_cj, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem qrefl_mem (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHerm L Hm)
    (Y : Submodule E (Fin n → E)) {a : Fin n → E} (ha : a ∈ perp L Hm Y)
    {g : (Fin n → E) ≃ₗ[E] (Fin n → E)} (hg : IsQRefl L Hm a g) : g ∈ fixG L Hm Y := by
  obtain ⟨_, hi, c, hc⟩ := hg
  have hfix : ∀ v ∈ Y, g v = v := fun v hv => by
    have h0 : hf L Hm a v = 0 := ha v hv
    rw [hc, hf_swap L hH v a, h0]; simp
  refine ⟨hi, fun v => ⟨fun hv => ?_, fun hv => by rw [hfix v hv]; exact hv⟩, fun v hv => ?_⟩
  · have : g v = v := g.injective (hfix _ hv)
    rwa [this] at hv
  · rw [hfix v hv]; simp

theorem conj_self {G : Type} [Group G] {H : Subgroup G} {h : G} (hh : h ∈ H) :
    MulAut.conj h • H = H := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [MulAut.smul_def, MulAut.inv_apply, MulAut.conj_symm_apply]
  constructor
  · intro hy
    have := H.mul_mem (H.mul_mem hh hy) (H.inv_mem hh)
    simpa [mul_assoc] using this
  · intro hy
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hy) hh

variable [IsNonarchimedeanLocalField F] [CharZero F]

theorem inf_stab_smul (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) {h} (hh : h ∈ H) :
    H ⊓ stabL L (h • Λ) = MulAut.conj h • (H ⊓ stabL L Λ) := by
  rw [((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ hΛ hΛ H).2 h).2, Subgroup.smul_inf, conj_self hh]

theorem comm_conj (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) : ∀ h ∈ H,
    (H ⊓ stabL L Λ).relIndex (MulAut.conj h • (H ⊓ stabL L Λ)) ≠ 0 ∧
      (MulAut.conj h • (H ⊓ stabL L Λ)).relIndex (H ⊓ stabL L Λ) ≠ 0 := by
  intro h hh
  have hl := ((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ hΛ hΛ H).2 h).1
  rw [← inf_stab_smul L H hΛ hh]
  exact ⟨(GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hl hΛ H).1, (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hΛ hl H).1⟩

theorem invVol_self {G : Type} [Group G] (K : Subgroup G) : invVol K K = 1 := by
  simp [invVol]

theorem delta_inv (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ : Submodule L.O (Fin n → E)} (hΛ : IsLat L Λ) {g} (hg : g ∈ H) :
    invVol (H ⊓ stabL L Λ) (MulAut.conj g • (H ⊓ stabL L Λ)) *
      invVol (H ⊓ stabL L Λ) (MulAut.conj g⁻¹ • (H ⊓ stabL L Λ)) = 1 := by
  rw [← (GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H hΛ)).1 g hg g⁻¹ (H.inv_mem hg)]
  simp [invVol_self]

theorem delta_indep (L : LocE F E) {n : ℕ} (H : Subgroup ((Fin n → E) ≃ₗ[E] (Fin n → E)))
    {Λ0 Λ : Submodule L.O (Fin n → E)} (h0 : IsLat L Λ0) (hΛ : IsLat L Λ) {g} (hg : g ∈ H)
    (h1 : invVol (H ⊓ stabL L Λ) (MulAut.conj g • (H ⊓ stabL L Λ)) = 1) :
    invVol (H ⊓ stabL L Λ0) (MulAut.conj g • (H ⊓ stabL L Λ0)) = 1 := by
  have a := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hΛ h0 H).1
  have b := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ h0 hΛ H).1
  have hl := ((GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L Λ Λ hΛ hΛ H).2 g).1
  have c := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hl h0 H).1
  have d := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ h0 hl H).1
  rw [inf_stab_smul L H hΛ hg] at c d
  have e1 := ((GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h0)).2.2.2 _ a b g hg).1
  have e2 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ _ _ a b c d).1
  have e3 := (GlobalTheory.HL.invVol_mul_pos_le_conj _ _ _ a b a b).2.1
  rw [e1, h1, mul_one] at e2
  exact mul_right_cancel₀ e3.ne' (by rw [e2, one_mul])

theorem unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ (m : ℕ) (x : Fin m → Fin n → E), IsUnit (gramT L Hm x).det → ∀ Λ0 Λ : Submodule L.O (Fin n → E), IsLat L Λ0 → IsLat L Λ → ∀ h ∈ fixG L Hm (Submodule.span E (Set.range x)), invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L (h • Λ)) = invVol (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ0) (fixG L Hm (Submodule.span E (Set.range x)) ⊓ stabL L Λ) := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH m x hx Λ0 Λ h0 hΛ h hh
  have hgen := GlobalTheory.T.isometriesFixingSubspace_le_quasiReflection_closure L Hm hH m x hx
  have hq := GlobalTheory.T.exists_lattice_and_inverting_automorphism_of_quasi_reflection L Hm hH m x hx
  have hmem := fun a ha g hg => qrefl_mem L hH.1 (Submodule.span E (Set.range x)) (a := a) ha (g := g) hg
  set H := fixG L Hm (Submodule.span E (Set.range x)) with hHdef
  have key : ∀ g ∈ Subgroup.closure
      {g | ∃ a ∈ perp L Hm (Submodule.span E (Set.range x)), IsQRefl L Hm a g},
      g ∈ H ∧ invVol (H ⊓ stabL L Λ0) (MulAut.conj g • (H ⊓ stabL L Λ0)) = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, hg⟩ := hg
      have hgH := hmem a ha g hg
      refine ⟨hgH, ?_⟩
      obtain ⟨Λ1, h1, α, hα, hαg⟩ := hq a ha g hg
      refine delta_indep L H h0 h1 hgH ?_
      have M := GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h1)
      have e1 := M.2.2.1 α hα g hgH
      have e2 := M.2.1 g hgH
      have e3 := delta_inv L H h1 hgH
      rw [hαg] at e1
      rw [e1] at e3
      nlinarith
    | one => exact ⟨H.one_mem, by simp [invVol_self]⟩
    | mul a b _ _ ha hb =>
      refine ⟨H.mul_mem ha.1 hb.1, ?_⟩
      rw [(GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h0)).1 a ha.1 b hb.1, ha.2, hb.2, one_mul]
    | inv a _ ha =>
      refine ⟨H.inv_mem ha.1, ?_⟩
      have := delta_inv L H h0 ha.1
      rwa [ha.2, one_mul] at this
  have a := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ hΛ h0 H).1
  have b := (GlobalTheory.T.latticeStabilizer_commensurable_unramified_hermitian L _ _ h0 hΛ H).1
  rw [inf_stab_smul L H hΛ hh,
    ((GlobalTheory.T.haarInvVolume_conj_modular_character H _ inf_le_left (comm_conj L H h0)).2.2.2 _ a b h hh).1, (key h (hgen hh)).2, one_mul]

end GlobalTheory.HL.Unimod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularCloseToOneInverseCloseStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitriangular_close_to_one_inverse_close : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (M : Matrix (Fin n) (Fin n) E) (t : E), t ∈ L.O → (∀ i j, j < i → M i j = 0) → (∀ i, M i i = 1) → (∀ i j, ∃ o ∈ L.O, (M - 1) i j = t * o) → ∃ Mi : Matrix (Fin n) (Fin n) E, Mi * M = 1 ∧ M * Mi = 1 ∧ ∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o := by
  first | exact @GlobalTheory.unitriangular_inv_close | exact GlobalTheory.unitriangular_inv_close | (intros; apply GlobalTheory.unitriangular_inv_close <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegrationFormulaOrbitStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_integration_formula_orbit : ∀ (G X : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] (x0 : X), Continuous (fun p : G × X => p.1 • p.2) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (ν : Measure X), ν {y | ¬ ∃ g : G, g • x0 = y} = 0 → (∀ (g : G) (s : Set X), MeasurableSet s → ν ((fun y => g • y) ⁻¹' s) = ν s) → (∀ K : Set G, IsCompact K → ν ((fun g => g • x0) '' K) < ⊤) → ν ≠ 0 → ∃ μ' : Measure (MulAction.stabilizer G x0), μ'.IsHaarMeasure ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∀ s : X → G, (∀ y, (∃ g : G, g • x0 = y) → s y • x0 = y) → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : G)) ∂μ' ∂ν := by
  first | exact @GlobalTheory.WeilOrbit.weil_formula | exact GlobalTheory.WeilOrbit.weil_formula | (intros; apply GlobalTheory.WeilOrbit.weil_formula <;> assumption)
end

