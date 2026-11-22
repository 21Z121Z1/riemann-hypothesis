import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0162
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0085
import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0163
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import GroundTheory.PAdicHodge.TiltValuation
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAndIsSemisimpleRingOfNoNilIdealsBoundedIde
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Formalism.CharacterColumnKernels.StatementRho
import ReciprocityTheory.Hypotheses.GalCohDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLargeCompactOpenSubgroupWithSmallDualStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_large_compactOpen_subgroup_with_small_dual : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ C : Set A.L, IsCompact C → ∀ V ∈ 𝓝 (0 : A.L), ∃ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) ∧ IsCompact (Λ : Set A.L) ∧ C ⊆ Λ ∧ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ ∧ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ V := by
  first | exact @GlobalTheory.JR.WeilQuad.LargeLattice.main | exact GlobalTheory.JR.WeilQuad.LargeLattice.main | (intros; apply GlobalTheory.JR.WeilQuad.LargeLattice.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIntegral
section
namespace GlobalTheory.IntegralPowerMultiple

theorem exists_pow_mul_integral {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (c : FractionRing O) :
    ∃ (n : ℕ) (a : O), algebraMap O (FractionRing O) (ϖ ^ n) * c = algebraMap O (FractionRing O) a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb

  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨n, ((u⁻¹ : Oˣ) : O) * a, ?_⟩
  have hbK : algebraMap O (FractionRing O) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hu' : algebraMap O (FractionRing O) (u : O) * algebraMap O (FractionRing O) ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [hu, map_mul] at hbK
  rw [hu, map_mul, map_mul]
  rw [mul_div_assoc', div_eq_iff hbK]
  linear_combination (-(algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) (ϖ ^ n))) * hu'

theorem exists_pow_smul_mem : ∀ {O : Type} [inst : CommRing O] [inst_1 : IsDomain O] [IsDiscreteValuationRing O] {V : Type} [inst_3 : AddCommGroup V] [inst_4 : Module O V] [inst_5 : Module (FractionRing O) V] [inst_6 : IsScalarTower O (FractionRing O) V] (T : Submodule O V), Formalism.RepresentationBoundsCohomology.LOC.IsLatticeIn T → ∀ (ϖ : O), Irreducible ϖ → ∀ (v : V), ∃ (m : ℕ), ϖ ^ m • v ∈ T := by
  intro O _ _ _ V _ _ _ _ T hT ϖ hϖ v
  have hv : v ∈ Submodule.span (FractionRing O) (T : Set V) := by rw [hT.2]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    refine ⟨m₁ + m₂, ?_⟩
    rw [smul_add, pow_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem _ h₁
    · rw [mul_smul]
      exact T.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx

    obtain ⟨n, a, ha⟩ := exists_pow_mul_integral hϖ c
    refine ⟨n + m, ?_⟩
    have key : ϖ ^ (n + m) • (c • x) = a • (ϖ ^ m • x) := by
      rw [← algebraMap_smul (FractionRing O) (ϖ ^ (n + m)) (c • x), smul_smul,
        ← algebraMap_smul (FractionRing O) a, ← algebraMap_smul (FractionRing O) (ϖ ^ m) x, smul_smul,
        ← ha, pow_add, map_mul]
      congr 1
      ring
    rw [key]
    exact T.smul_mem a hm

end GlobalTheory.IntegralPowerMultiple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemRangeOfFiniteLengthCoker
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem exists_pow_smul_eq_zero_of_isFiniteLength {R : Type} [CommRing R] (r : R)
    (hr : ∀ b : R, IsUnit (1 - b * r)) (M : Type) [AddCommGroup M] [Module R M]
    (h : IsFiniteLength R M) : ∃ n : ℕ, ∀ m : M, r ^ n • m = 0 := by
  induction h with
  | of_subsingleton => exact ⟨0, fun m => Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    have hS : ∀ q : M ⧸ N, r • q = 0 := by
      intro q
      by_contra hq
      have htop : (R ∙ (r • q)) = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top _).resolve_left
        (by rwa [Submodule.span_singleton_eq_bot])
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 (htop ▸ Submodule.mem_top : q ∈ R ∙ (r • q))
      have h1 : (1 - b * r) • q = 0 := by rw [sub_smul, one_smul, mul_smul, hb, sub_self]
      have h2 : q = 0 := (hr b).smul_eq_zero.1 h1
      exact hq (by rw [h2, smul_zero])
    refine ⟨n + 1, fun m => ?_⟩
    have hm : r • m ∈ N := by
      have := hS (N.mkQ m)
      rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    have := hn ⟨_, hm⟩
    rw [pow_succ, mul_smul]
    simpa using congrArg Subtype.val this

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem isUnit_one_sub_mul_l (b : A O K) : IsUnit (1 - b * (l : A O K)) := by
  set f : A O K := 1 - b * (l : A O K)
  set g := (equivA O K).symm f
  have hg : equivA O K g = f := AlgEquiv.apply_symm_apply _ _
  suffices IsUnit g by simpa [hg] using this.map (equivA O K)
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have h0 : algebraMap O K (constantCoeff g) = 1 - constantCoeff (b : K⟦X⟧) * l := by
    calc algebraMap O K (constantCoeff g) = constantCoeff ((equivA O K g : A O K) : K⟦X⟧) := by
          rw [coe_equivA, ← coeff_zero_eq_constantCoeff_apply (map _ g), coeff_map,
            coeff_zero_eq_constantCoeff_apply]
      _ = 1 - constantCoeff (b : K⟦X⟧) * l := by
          rw [hg]
          simp only [f, Subalgebra.coe_sub, Subalgebra.coe_one, Subalgebra.coe_mul,
            map_sub, map_one, map_mul]
          congr 2
  have hlt : ‖constantCoeff (b : K⟦X⟧) * (l : K)‖ < 1 := by
    rw [norm_mul]
    have hb : ‖constantCoeff (b : K⟦X⟧)‖ ≤ 1 := by
      simpa using (mem_A.1 b.2) 0
    calc _ ≤ 1 * ‖(l : K)‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      _ < 1 := by rw [one_mul]; exact norm_l_lt_one (K := K) l
  have hn : ‖algebraMap O K (constantCoeff g)‖ = 1 := by
    rw [h0, sub_eq_add_neg, add_comm, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg, norm_one]; exact hlt.ne), norm_neg, norm_one, max_eq_right hlt.le]
  have hne : algebraMap O K (constantCoeff g) ≠ 0 := by
    intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  obtain ⟨c, hc⟩ := (IsUnitBall.mem_range_iff (O := O) (algebraMap O K (constantCoeff g))⁻¹).2
    (by rw [norm_inv, hn, inv_one])
  refine IsUnit.of_mul_eq_one c (IsUnitBall.inj (K := K) ?_)
  rw [map_mul, hc, mul_inv_cancel₀ hne, map_one]

theorem exists_l_pow_smul_eq_app_of_isFiniteLength_coker (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ μ : Type) [Fintype κ]
    [DecidableEq κ] [Fintype μ] [DecidableEq μ] (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ)
    (G : GlobalTheory.BK.Hom Q T) :
    IsFiniteLength (A O K) G.coker → ∃ n : ℕ, ∀ y ∈ T.M, ∃ x ∈ Q.M, G.app x = (l : K) ^ n • y := by
  intro h
  obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_isFiniteLength (l : A O K)
    (isUnit_one_sub_mul_l l) _ h
  refine ⟨n, fun y hy => ?_⟩
  have h1 := hn (Submodule.Quotient.mk ⟨y, hy⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  change _ ∈ (G.imM).comap T.M.subtype at h1
  rw [Submodule.mem_comap, Hom.imM, Submodule.mem_map] at h1
  obtain ⟨x, hx, hxy⟩ := h1
  refine ⟨x, hx, ?_⟩
  rw [LinearMap.restrictScalars_apply] at hxy
  rw [hxy]
  ext τ i
  simp [Algebra.smul_def]

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulMemMMOfEqLphiUAdd
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
omit [IsUltrametricDist K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
private lemma coeff_eq_add_of_X_pow_succ_dvd_sub {f s g : K⟦X⟧} {c : K} {n : ℕ}
    (h : (X : K⟦X⟧) ^ (n + 1) ∣ f - (s + c • g)) :
    coeff n f = coeff n s + c * coeff n g := by
  have h0 := (PowerSeries.X_pow_dvd_iff.mp h) n (Nat.lt_succ_self n)
  rw [map_sub, map_add, PowerSeries.coeff_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
private lemma norm_add_mul_mul_le_max {x y c : K} {w : ℝ} (hw : 0 ≤ w) :
    ‖x + c * y‖ * w ≤ max (‖x‖ * w) (‖c‖ * (‖y‖ * w)) := by
  calc ‖x + c * y‖ * w ≤ max ‖x‖ ‖c * y‖ * w :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) hw
    _ = max (‖x‖ * w) (‖c‖ * (‖y‖ * w)) := by
        rw [max_mul_of_nonneg _ _ hw, norm_mul, mul_assoc]

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
omit [IsUltrametricDist K] in
private lemma norm_natCast_prime_lt_one_inertia_eigenvalues : ‖(l : K)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap']
  exact Padic.norm_p_lt_one

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in

theorem _root_.GlobalTheory.BK.mem_S_of_approx {f : K⟦X⟧}
    (h : ∀ k : ℕ, ∃ s ∈ _root_.GlobalTheory.BK.S O K e, ∀ m : ℕ,
      ∃ g ∈ _root_.GlobalTheory.BK.S O K e,
        (X : K⟦X⟧) ^ m ∣ f - (s + (l : K) ^ k • g)) : f ∈ _root_.GlobalTheory.BK.S O K e := by
  rw [_root_.GlobalTheory.BK.mem_S]
  have hw := _root_.GlobalTheory.BK.wS_nonneg (K := K) e
  refine ⟨fun n => ?_, ?_⟩
  · obtain ⟨s, hs, hm⟩ := h 0
    obtain ⟨g, hg, hdvd⟩ := hm (n + 1)
    rw [coeff_eq_add_of_X_pow_succ_dvd_sub hdvd]
    refine (norm_add_mul_mul_le_max (hw n)).trans (max_le ((_root_.GlobalTheory.BK.mem_S.mp hs).1 n) ?_)
    rw [pow_zero, norm_one, one_mul]
    exact (_root_.GlobalTheory.BK.mem_S.mp hg).1 n
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_prime_lt_one_inertia_eigenvalues (K := K) (l := l))
    obtain ⟨s, hs, hm⟩ := h k
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (_root_.GlobalTheory.BK.mem_S.mp hs).2 ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨g, hg, hdvd⟩ := hm (n + 1)
    have hsn := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hw n))] at hsn ⊢
    rw [coeff_eq_add_of_X_pow_succ_dvd_sub hdvd]
    refine (norm_add_mul_mul_le_max (hw n)).trans_lt (max_lt hsn ?_)
    calc ‖(l : K) ^ k‖ * (‖coeff n g‖ * _root_.GlobalTheory.BK.wS K e n)
        ≤ ‖(l : K) ^ k‖ * 1 :=
          mul_le_mul_of_nonneg_left ((_root_.GlobalTheory.BK.mem_S.mp hg).1 n)
            (norm_nonneg _)
      _ < ε := by rw [mul_one, norm_pow]; exact hk

namespace PhiMod

variable (P : PhiMod O K l e a ι)

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem _root_.GlobalTheory.BK.PhiMod.l_pow_smul_mem_MM (n : ℕ) {v : _root_.GlobalTheory.BK.Vec K a ι} (hv : v ∈ P.MM) :
    (l : K) ^ n • v ∈ P.MM := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hv _

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem _root_.GlobalTheory.BK.PhiMod.smul_mem_MM {f : K⟦X⟧}
    (hf : f ∈ _root_.GlobalTheory.BK.S O K e) {v : _root_.GlobalTheory.BK.Vec K a ι}
    (hv : v ∈ P.MM) : f • v ∈ P.MM :=
  Submodule.smul_mem _ (⟨f, hf⟩ : _root_.GlobalTheory.BK.S O K e) hv

variable [NeZero e]

open PowerSeries Filter Topology Matrix in
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [_root_.GlobalTheory.BK.IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
variable (P : _root_.GlobalTheory.BK.PhiMod O K l e a ι) in
variable [NeZero e] in

theorem _root_.GlobalTheory.BK.PhiMod.l_pow_smul_phi_mem_MM {k : ℕ} {v : _root_.GlobalTheory.BK.Vec K a ι}
    (hv : _root_.GlobalTheory.BK.E K l e ^ k • v ∈
      P.Mext (_root_.GlobalTheory.BK.S O K e)) :
    (l : K) ^ k • P.phi v ∈ P.MM := by
  obtain ⟨c, hc, hcE⟩ :=
    _root_.GlobalTheory.BK.exists_mul_frob_E (O := O) (K := K) l e
  set F := _root_.GlobalTheory.BK.frob K l with hF
  set E := _root_.GlobalTheory.BK.E K l e with hE
  have hw : ∀ τ i, (E ^ k • v) τ i ∈ _root_.GlobalTheory.BK.S O K e := by
    intro τ i
    unfold _root_.GlobalTheory.BK.PhiMod.Mext at hv
    rw [_root_.GlobalTheory.BK.mem_tot] at hv
    exact _root_.GlobalTheory.BK.mem_vecs.mp (hv τ) i
  have hmem : P.phi (E ^ k • v) ∈ P.MM := by
    unfold _root_.GlobalTheory.BK.PhiMod.MM
    rw [_root_.GlobalTheory.BK.PhiMod.ext, _root_.GlobalTheory.BK.mem_tot]
    intro τ
    rw [_root_.GlobalTheory.BK.PhiMod.mem_extc]
    refine ⟨_root_.GlobalTheory.BK.frobV l ((E ^ k • v) (τ - 1)), ?_, _root_.GlobalTheory.BK.PhiMod.phi_apply _ _ _⟩
    rw [_root_.GlobalTheory.BK.mem_vecs]
    intro i
    rw [_root_.GlobalTheory.BK.frobV_apply]
    exact _root_.GlobalTheory.BK.frob_mem_S l (hw _ i)
  have heq : (l : K) ^ k • P.phi v =
      ((⟨c, hc⟩ : _root_.GlobalTheory.BK.S O K e) ^ k) •
        P.phi (E ^ k • v) := by
    funext τ i
    have hvec : _root_.GlobalTheory.BK.frobV l ((E ^ k • v) (τ - 1)) =
        F E ^ k • _root_.GlobalTheory.BK.frobV l (v (τ - 1)) := by
      funext j
      simp only [Pi.smul_apply, _root_.GlobalTheory.BK.frobV_apply, smul_eq_mul, map_mul, map_pow, hF]
    change (l : K) ^ k • P.phi v τ i =
      (c ^ k) • P.phi (E ^ k • v) τ i
    rw [_root_.GlobalTheory.BK.PhiMod.phi_apply, _root_.GlobalTheory.BK.PhiMod.phi_apply, hvec, Matrix.mulVec_smul, Pi.smul_apply, smul_smul, ← mul_pow, hcE,
      ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [heq]
  exact Submodule.smul_mem _ _ hmem

def lphiU : Module.End K (Vec K a ι) := mulV K a ι (X ^ (l - 1)) * P.lphi

variable {η : ℕ} (hη : ∀ v ∈ P.MM, (l : K) ^ η • P.phi v ∈ P.MM)

include hη

end PhiMod

namespace BKDat

variable [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ} (D : BKDat O K l e a ι η H)

end BKDat

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSortedNormalizedOrthBasisComplexPAdicStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sorted_normalized_orthBasis_complexPAdic : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (μ : Fin h → ℂ_[l]), (∀ c : Fin h → ℚ_[l], ∑ j, algebraMap ℚ_[l] ℂ_[l] (c j) * μ j = 0 → c = 0) → ∃ (P : Matrix (Fin h) (Fin h) ℚ_[l]) (μ' : Fin h → ℂ_[l]), P.det ≠ 0 ∧ (∀ i, μ' i = ∑ j, algebraMap ℚ_[l] ℂ_[l] (P i j) * μ j) ∧ (∀ i, μ' i ≠ 0 ∧ ‖μ' i‖ ≤ 1) ∧ Antitone (fun i => ‖μ' i‖) ∧ (∀ i j, ‖μ' i‖ < l * ‖μ' j‖) ∧ ∀ (c : Fin h → ℚ_[l]) (j : Fin h), ‖c j‖ * ‖μ' j‖ ≤ ‖∑ i, algebraMap ℚ_[l] ℂ_[l] (c i) * μ' i‖ := by
  first | exact @GlobalTheory.PMonE.OrthBasis.exists_orthBasis | exact GlobalTheory.PMonE.OrthBasis.exists_orthBasis | (intros; apply GlobalTheory.PMonE.OrthBasis.exists_orthBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltIntegersCpEquivCompatibleUntilt
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

open GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

theorem oc_eq_normInteger : (𝓞_ℂ_[l]).toSubring = normInteger ℂ_[l] := by
  ext x
  rw [mem_normInteger, ← GlobalTheory.RingBasics.mem_OC]
  rfl

noncomputable def ocEquiv : OC l ≃+* normInteger ℂ_[l] := RingEquiv.subringCongr (oc_eq_normInteger l)

theorem coe_ocEquiv (x : OC l) : ((ocEquiv l x : normInteger ℂ_[l]) : ℂ_[l]) = (x : ℂ_[l]) := rfl

theorem span_map_ocEquiv :
    Ideal.span {(l : normInteger ℂ_[l])} = (Ideal.span {(l : OC l)}).map ((ocEquiv l : OC l →+* normInteger ℂ_[l])) := by
  rw [Ideal.map_span, Set.image_singleton]; simp

noncomputable def modEquiv : ModP (OC l) l ≃+* ModP (normInteger ℂ_[l]) l :=
  Ideal.quotientEquiv _ _ (ocEquiv l) (span_map_ocEquiv l)

noncomputable def flTo : Fl l →+* PreTilt (normInteger ℂ_[l]) l :=
  Perfection.map l (modEquiv l : ModP (OC l) l →+* ModP (normInteger ℂ_[l]) l)

noncomputable def flFrom : PreTilt (normInteger ℂ_[l]) l →+* Fl l :=
  Perfection.map l ((modEquiv l).symm : ModP (normInteger ℂ_[l]) l →+* ModP (OC l) l)

theorem coeff_flTo (x : Fl l) (n : ℕ) :
    Perfection.coeff _ l n (flTo l x) = modEquiv l (Perfection.coeff _ l n x) := rfl

theorem coeff_flFrom (x : PreTilt (normInteger ℂ_[l]) l) (n : ℕ) :
    Perfection.coeff _ l n (flFrom l x) = (modEquiv l).symm (Perfection.coeff _ l n x) := rfl

noncomputable def flEquiv : Fl l ≃+* PreTilt (normInteger ℂ_[l]) l :=
  RingEquiv.ofRingHom (flTo l) (flFrom l)
    (RingHom.ext fun x => Perfection.ext fun n => by
      change Perfection.coeff _ l n (flTo l (flFrom l x)) = Perfection.coeff _ l n x
      rw [coeff_flTo, coeff_flFrom, RingEquiv.apply_symm_apply])
    (RingHom.ext fun x => Perfection.ext fun n => by
      change Perfection.coeff _ l n (flFrom l (flTo l x)) = Perfection.coeff _ l n x
      rw [coeff_flFrom, coeff_flTo, RingEquiv.symm_apply_apply])

theorem flEquiv_apply (x : Fl l) : flEquiv l x = flTo l x := rfl

theorem untilt_flTo (x : Fl l) : (flTo l x).untilt = ocEquiv l x.untilt := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(l : normInteger ℂ_[l])}) fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (Perfection.coeff _ l n x)
  refine ⟨ocEquiv l y, ?_, ?_⟩
  · rw [coeff_flTo, ← hy]
    rfl
  · have := (Perfection.teichmuller_sModEq hy).symm
    rw [SModEq.sub_mem, GlobalTheory.RingBasics.mem_span_pow_OC] at this
    have hl : ((l : normInteger ℂ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by simp
    rw [SModEq.sub_mem, mem_span_singleton_pow_iff, ← map_pow, ← map_sub, coe_ocEquiv, hl]
    exact this

theorem exists_flEquiv_untilt : ∀ (l : ℕ) [Fact l.Prime], ∃ e : Fl l ≃+* PreTilt (GroundTheory.PAdicHodge.normInteger ℂ_[l]) l,
    ∀ x : Fl l, ((PreTilt.untilt (e x) : GroundTheory.PAdicHodge.normInteger ℂ_[l]) : ℂ_[l]) = sh x := by
  intro l _
  refine ⟨flEquiv l, fun x => ?_⟩
  rw [flEquiv_apply, untilt_flTo, coe_ocEquiv]
  rfl

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAndIsSemisimpleRingOfNoNilIdealsBoundedIdeStatement
section
open Formalism.MainNotions.N GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_and_isSemisimpleRing_of_no_nil_ideals_bounded_idempotents : ∀ (k R : Type) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] (d : ℕ), (∀ x : R, IsIntegral k x) → (∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) → (∀ (m : ℕ) (e : Fin m → R), OrthogonalIdempotents e → (∀ i, e i ≠ 0) → m ≤ d) → Module.Finite k R ∧ IsSemisimpleRing R := by
  first | exact @GlobalTheory.AlgRing.finite_and_isSemisimpleRing | exact GlobalTheory.AlgRing.finite_and_isSemisimpleRing | (intros; apply GlobalTheory.AlgRing.finite_and_isSemisimpleRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteInvariantsOfScalarNeOneTwistStatement
section
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_invariants_of_scalar_ne_one_twist : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) → ∀ {G : Type} [Group G]
    (ρ : Representation O G M) (g : G) (a : O), a ≠ 1 → (∀ m, ρ g m = a • m) → Finite ρ.invariants := by
  first | exact @GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one | exact GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one | (intros; apply GlobalTheory.ShapeNeg.finite_invariants_of_smul_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteUnitOrbitsStableLatticesSeparableStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_unit_orbits_stable_lattices_separable : ∀ (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A] [IsScalarTower O E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Finite (MulAction.orbitRel.Quotient Aˣ (stLat O E g)) := by
  first | exact @GlobalTheory.UnitLemma.finite_orbits_stLat_of_separable | exact GlobalTheory.UnitLemma.finite_orbits_stLat_of_separable | (intros; apply GlobalTheory.UnitLemma.finite_orbits_stLat_of_separable <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussIntegralOneMulGaussIntegralNegOneEqOneStatement
section
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussIntegral_one_mul_gaussIntegral_neg_one_eq_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) → IsCompact (Λ : Set A.L) → {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1} ⊆ Λ → (∀ y ∈ {y : A.L | ∀ w ∈ (Λ : Set A.L), A.kerL ψ x w y = 1}, A.psiK ψ ((x : A.K) * A.NL y) = 1) → gaussInt A ψ x μ 1 Λ * gaussInt A ψ x μ (-1) Λ = 1 := by
  first | exact @GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one | exact GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one | (intros; apply GlobalTheory.JR.WeilQuad.gaussInt_one_mul_neg_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianDualInvAlgBaseChangeUnramifiedIffStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDual_invAlgBaseChangeUnramified_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (x y : B.A), (∀ z ∈ L, (overExt φ B ψ hψ hσ).herm x y z ∈ (algebraMap K'.O K'.E).range) ↔ (∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) := by
  first | exact @GlobalTheory.UnitLemma.Unr.dual_iff | exact GlobalTheory.UnitLemma.Unr.dual_iff | (intros; apply GlobalTheory.UnitLemma.Unr.dual_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HighestWeightAtConjugateEmbeddingRevNeg
section
open NumberField

namespace GlobalTheory

theorem hwAt_conj_swap : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : Formalism.L2.NG.AlgWt L n) (τ : L →+* ℂ) (lam' : Fin n → ℤ), a.HWAt (ComplexEmbedding.conjugate τ) lam' → a.HWAt τ (fun i => -lam' (Fin.rev i)) :=
  PI.UnitaryGroupMassFormula.HwConjInf.conjugation_swap

end GlobalTheory
end

