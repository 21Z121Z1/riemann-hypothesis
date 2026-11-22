import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0277
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0024
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0018
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemClosureInducedCentralByPrimePower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0144
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0163
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0185
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0161
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgHomExtOfConstantCoeffZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem algHom_ext_of_constantCoeff_zero {O : Type} [CommRing O]
    (f g : PowerSeries O →ₐ[O] PowerSeries O) (h : f PowerSeries.X = g PowerSeries.X)
    (h0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0) : f = g := by
  have key : ∀ (n : ℕ) (a : PowerSeries O), PowerSeries.X ^ n ∣ f a - g a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      obtain ⟨b, hb⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
        rw [PowerSeries.X_dvd_iff]; simp
      have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
        rw [← hb, PowerSeries.algebraMap_eq]; ring
      have : f a - g a = f PowerSeries.X * (f b - g b) := by
        conv_lhs => rw [ha]
        rw [map_add, map_add, map_mul, map_mul, f.commutes, g.commutes, ← h]; ring
      rw [this, pow_succ']
      exact mul_dvd_mul (PowerSeries.X_dvd_iff.2 h0) (ih b)
  ext a n
  have := (PowerSeries.X_pow_dvd_iff.1 (key (n + 1) a)) n (Nat.lt_succ_self n)
  rw [map_sub] at this
  exact sub_eq_zero.1 this

theorem constantCoeff_algHom {O : Type} [CommRing O]
    (f : PowerSeries O →ₐ[O] PowerSeries O)
    (h0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0) (a : PowerSeries O) :
    PowerSeries.constantCoeff (f a) = PowerSeries.constantCoeff a := by
  obtain ⟨b, hb⟩ : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]; simp
  have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
    rw [← hb, PowerSeries.algebraMap_eq]; ring
  conv_lhs => rw [ha]
  rw [map_add, map_mul, f.commutes, map_add, map_mul, h0, PowerSeries.algebraMap_eq]
  simp

theorem eq_of_commute_pow {O : Type} [CommRing O] [IsDomain O] (l : ℕ) (hl0 : (l : O) ≠ 0)
    (hlu : ¬ IsUnit (l : O)) (φ f g : PowerSeries O →ₐ[O] PowerSeries O)
    (hφ : φ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1)
    (hf : φ (f PowerSeries.X) = f (φ PowerSeries.X))
    (hg : φ (g PowerSeries.X) = g (φ PowerSeries.X))
    (hf0 : PowerSeries.constantCoeff (f PowerSeries.X) = 0)
    (hg0 : PowerSeries.constantCoeff (g PowerSeries.X) = 0)
    (h1 : PowerSeries.coeff 1 (f PowerSeries.X) = PowerSeries.coeff 1 (g PowerSeries.X)) :
    f PowerSeries.X = g PowerSeries.X := by
  set F := f PowerSeries.X with hF
  set G := g PowerSeries.X with hG
  have hφ0 : PowerSeries.constantCoeff (φ PowerSeries.X) = 0 := by rw [hφ]; simp
  have hp : φ PowerSeries.X = PowerSeries.X *
      ∑ i ∈ Finset.range l, (1 + PowerSeries.X : PowerSeries O) ^ i := by
    rw [hφ, ← geom_sum_mul]; ring
  have hd : φ (F - G) = (F - G) * ∑ i ∈ Finset.range l, (1 + F) ^ i * (1 + G) ^ (l - 1 - i) := by
    rw [map_sub, hf, hg, hφ]
    have := (Commute.all (1 + F) (1 + G)).mul_geom_sum₂ l
    simp only [map_sub, map_pow, map_add, map_one, ← hF, ← hG]
    rw [show (1 + F) - (1 + G) = F - G by ring] at this
    rw [this]; ring
  have key : ∀ n : ℕ, PowerSeries.X ^ (n + 2) ∣ F - G := by
    intro n
    induction n with
    | zero =>
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      interval_cases m
      · simp [hf0, hg0]
      · rw [map_sub, h1, sub_self]
    | succ n ih =>
      obtain ⟨e, he⟩ := ih
      rw [he, map_mul, map_pow, hp, mul_pow, mul_assoc, mul_assoc] at hd
      have hc := congrArg PowerSeries.constantCoeff
        (mul_left_cancel₀ (pow_ne_zero _ PowerSeries.X_ne_zero) hd)
      simp only [map_mul, map_pow, map_sum, map_add, map_one, PowerSeries.constantCoeff_X, hf0, hg0,
        add_zero, one_pow, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        constantCoeff_algHom φ hφ0] at hc
      have he0 : PowerSeries.constantCoeff e = 0 := by
        by_contra hne
        have h2 : (l : O) * ((l : O) ^ (n + 1) - 1) * PowerSeries.constantCoeff e = 0 := by
          linear_combination hc
        rcases mul_eq_zero.1 h2 with h3 | h3
        · rcases mul_eq_zero.1 h3 with h4 | h4
          · exact hl0 h4
          · exact hlu (IsUnit.of_pow_eq_one (sub_eq_zero.1 h4) (Nat.succ_ne_zero n))
        · exact hne h3
      rw [he, show n + 1 + 2 = n + 2 + 1 from rfl, pow_succ]
      exact mul_dvd_mul_left _ (PowerSeries.X_dvd_iff.2 he0)
  ext n
  have := (PowerSeries.X_pow_dvd_iff.1 (key n)) n (by omega)
  rw [map_sub] at this
  exact sub_eq_zero.1 this

theorem act_unique : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (f : PowerSeries O →ₐ[O] PowerSeries O) (φ₀ : PowerSeries O →ₐ[O] PowerSeries O) (c : ℤ_[l]), φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 → (∀ a, φ₀ (f a) = f (φ₀ a)) → PowerSeries.constantCoeff (f PowerSeries.X) = 0 → PowerSeries.coeff 1 (f PowerSeries.X) = algebraMap ℤ_[l] O c → φ₀ = phi l O ∧ f = act l O c := by
  intro l _ O _ _ _ _ _ hl0 hlu f φ₀ c hφ hcomm hf0 hf1
  obtain ⟨hX, hmul, -, hnat, hlin, -⟩ := GlobalTheory.T.cyclotomicPowerSeriesAlgHom_action_laws l O
  have hφe : φ₀ = phi l O := by
    refine algHom_ext_of_constantCoeff_zero _ _ ?_ (by rw [hφ]; simp)
    rw [hφ, phi, hX, hnat]
  refine ⟨hφe, algHom_ext_of_constantCoeff_zero _ _ ?_ hf0⟩
  refine eq_of_commute_pow l hl0 hlu φ₀ f (act l O c) hφ (hcomm _) ?_ hf0 ?_ ?_
  · rw [hφe, phi, hmul, hmul, mul_comm]
  · rw [hX, cyc_const]
  · rw [hX, hlin, hf1]

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfFullGaloisLineUnitsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_regular_of_full_galois_line_units : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), (∀ b : Per.Bcris l, b ≠ 0 → (∀ g : GQ l, ∃ x : ℚ_[l], Per.σB g b = C.qB x * b) → IsUnit b) → C.Regular := by
  first | exact @GlobalTheory.MemLoc.regular_of_full | exact GlobalTheory.MemLoc.regular_of_full | (intros; apply GlobalTheory.MemLoc.regular_of_full <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterion
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ExtCrysCrit

theorem cocycle_of_ext {G LL V₀ V₁ : Type} [Group G] [TopologicalSpace G] [Field LL] [TopologicalSpace LL]
    [AddCommGroup V₀] [Module LL V₀] [TopologicalSpace V₀] [ContinuousAdd V₀] [ContinuousSMul LL V₀]
    [AddCommGroup V₁] [Module LL V₁] [TopologicalSpace V₁] [IsModuleTopology LL V₁]
    (ρ₀ : Representation LL G V₀) (ρ₁ : Representation LL G V₁) (ι : V₀ →ₗ[LL] V₁)
    (hι : Function.Injective ι) (hιρ : ∀ g y, ι (ρ₀ g y) = ρ₁ g (ι y)) (x : V₁)
    (hx : Continuous fun g => ρ₁ g x) (c : G → V₀) (hc : ∀ g, ι (c g) = ρ₁ g x - x) :
    Continuous c ∧ ∀ g h, c (g * h) = c g + ρ₀ g (c h) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.2 hι)
  have hrc : ∀ g, c g = r (ρ₁ g x) + (- r x) := by
    intro g
    rw [← sub_eq_add_neg, ← map_sub, ← hc, ← LinearMap.comp_apply, hr, LinearMap.id_apply]
  refine ⟨?_, fun g h => hι ?_⟩
  · have : c = fun g => r (ρ₁ g x) + (- r x) := funext hrc
    rw [this]
    exact ((IsModuleTopology.continuous_of_linearMap r).comp hx).add continuous_const
  · rw [map_add, hιρ, hc, hc, hc, map_mul, Module.End.mul_apply, map_sub]
    abel

theorem finrank_ext {LL V₀ V₁ V₂ : Type} [Field LL] [AddCommGroup V₀] [Module LL V₀] [AddCommGroup V₁]
    [Module LL V₁] [FiniteDimensional LL V₁] [AddCommGroup V₂] [Module LL V₂]
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂) (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hk : ∀ z, π z = 0 ↔ ∃ y, ι y = z) (h1 : Module.finrank LL V₂ = 1) :
    Module.finrank LL V₁ = Module.finrank LL V₀ + 1 := by
  have hk' : LinearMap.ker π = LinearMap.range ι := by
    ext z; rw [LinearMap.mem_ker, LinearMap.mem_range]; exact hk z
  have h := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.2 hπ, finrank_top, hk', LinearMap.finrank_range_of_inj hι, h1] at h
  omega

theorem not_mem_range {LL V₀ V₁ V₂ : Type} [Field LL] [AddCommGroup V₀] [Module LL V₀] [AddCommGroup V₁]
    [Module LL V₁] [AddCommGroup V₂] [Module LL V₂]
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂) (hk : ∀ z, π z = 0 ↔ ∃ y, ι y = z) (x : V₁) (hx : π x ≠ 0) :
    x ∉ LinearMap.range ι := by
  rintro ⟨y, rfl⟩
  exact hx ((hk _).2 ⟨y, rfl⟩)

theorem blochKato_ext_all : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm15 D := by
  intro D l _ K LL
  intro T Tp To ι π hses htriv hdim hcrys x hxT hπx c hc
  have key := GlobalTheory.CrysExtCrit.coboundary_iff_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ Tp.V Tp.ρ ι.f ι.equiv hses.1
    (finrank_ext ι.f π.f hses.1 hses.2.1 hses.2.2.2.1 hdim) hcrys x
    (not_mem_range ι.f π.f hses.2.2.2.1 x hπx) c hc
  obtain ⟨hcont, hcoc⟩ := cocycle_of_ext T.ρ Tp.ρ ι.f hses.1 ι.equiv x (Tp.cont x) c hc
  exact ⟨fun h => key.1 h.2, fun h => ⟨⟨hcont, hcoc⟩, key.2 h⟩⟩

end GlobalTheory.ExtCrysCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAndEventuallySubMemLatStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ b ∈ FilB P 0, ∀ M n : ℕ, (∃ k : ℕ, (l : P.R.BdR) ^ k * b ∈ Lat AI M n) ∧ ∀ᶠ σ in nhds (1 : GQ l), P.actQdR σ b - b ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat | exact GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat | (intros; apply GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BrauerDegreeZero
section
noncomputable section
open GlobalTheory.BI

namespace GlobalTheory.BrauerZero

theorem step_ind_ind {G : Type} [Group G] [Finite G] (K A : Subgroup G) (hKA : K ≤ A) (ψ : K → ℂ) :
    ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ :=
  GlobalTheory.T.inducedClassFunctionFromSubgroup_trans K A hKA ψ

theorem inducedClassFunction_mem_degreeOneCharacterDiff {G : Type} [Group G] [Finite G] (E : Subgroup G) (f : E → ℂ) (hf : f ∈ D0 E) :
    ind E f ∈ D0 G :=
  GlobalTheory.T.inducedClassFunction_mem_inducedDegreeOneCharDiff E f hf

theorem step_ind_one_sub_index_of_comm {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) :
    ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G :=
  GlobalTheory.T.induced_one_sub_index_mem_degreeOneCharacterDiff K hc

theorem step_exists_gt_commutators_le {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] (K : Subgroup G)
    (hK : K ≠ ⊤) : ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K :=
  GlobalTheory.T.exists_gt_commutator_mem_of_ne_whole K hK

theorem ind_one_sub_index_mem_degreeOneDiff_nilpotent {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] :
    ∀ (n : ℕ) (K : Subgroup G), K.index ≤ n →
      ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by
  intro n
  induction n with
  | zero => intro K hK; have := K.index_ne_zero_of_finite; omega
  | succ n ih =>
    intro K hK
    by_cases hKt : K = ⊤
    · subst hKt
      have e : ind (⊤ : Subgroup G) (fun _ => (1 : ℂ)) = fun _ => 1 :=
        ind_top (fun _ => (1 : ℂ)) (fun _ _ => rfl)
      rw [e, Subgroup.index_top]
      simp
    · obtain ⟨A, hKA, hc⟩ := step_exists_gt_commutators_le K hKt
      have h1 : ind (K.subgroupOf A) (fun _ => (1 : ℂ)) - (fun _ => ((K.subgroupOf A).index : ℂ)) ∈ D0 A :=
        step_ind_one_sub_index_of_comm (K.subgroupOf A) (fun a b => by
          rw [Subgroup.mem_subgroupOf]; simpa using hc a a.2 b b.2)
      have h2 := inducedClassFunction_mem_degreeOneCharacterDiff A _ h1
      have hrel := Subgroup.relIndex_mul_index hKA.le
      have hlt : 1 < K.relIndex A := by
        have h0 : (K.subgroupOf A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have h1' : (K.subgroupOf A).index ≠ 1 := fun h =>
          hKA.not_ge (Subgroup.subgroupOf_eq_top.1 (Subgroup.index_eq_one.1 h))
        unfold Subgroup.relIndex; omega
      have hA0 : A.index ≠ 0 := A.index_ne_zero_of_finite
      have h3 := ih A (by nlinarith)
      have t := step_ind_ind K A hKA.le (fun _ => (1 : ℂ))
      have key : ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) =
          ind A (ind (K.subgroupOf A) (fun _ => (1 : ℂ)) - (fun _ => ((K.subgroupOf A).index : ℂ))) +
            ((K.subgroupOf A).index : ℤ) • (ind A (fun _ => (1 : ℂ)) - (fun _ => (A.index : ℂ))) := by
        rw [ind_sub, ← t, ← hrel]
        funext g
        have hc1 := ind_const A (((K.subgroupOf A).index : ℕ) : ℂ) g
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hc1, zsmul_eq_mul]
        simp only [Pi.mul_apply, Pi.sub_apply, Pi.intCast_apply, Pi.natCast_apply, Int.cast_natCast]
        simp only [Subgroup.relIndex]
        push_cast
        ring
      rw [key]
      exact add_mem h2 (zsmul_mem h3 _)

theorem mem_degreeOneDiff_of_forall_centralByPrime (G : Type) [Group G] [Finite G] (f : G → ℂ)
    (hf : ∀ g x : G, f (x⁻¹ * g * x) = f g)
    (h : ∀ E : Subgroup G, (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) →
      ∀ ψ ∈ Virt ℂ ℂ E, ind E (fun e => ψ e * f e) ∈ D0 G) : f ∈ D0 G := by
  have key : ∀ φ ∈ AddSubgroup.closure {φ : G → ℂ | ∃ (E : Subgroup G) (ψ : E → ℂ),
      (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧
        ψ ∈ Virt ℂ ℂ E ∧ φ = ind E ψ}, φ * f ∈ D0 G := by
    intro φ hφ
    induction hφ using AddSubgroup.closure_induction with
    | mem φ hφ =>
      obtain ⟨E, ψ, hl, hψ, rfl⟩ := hφ
      rw [ind_mul_classFun_eq_ind_mul_restrict G E ψ f hf]
      exact h E hl ψ hψ
    | zero => rw [zero_mul]; exact zero_mem _
    | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
    | neg a _ ha => rw [neg_mul]; exact neg_mem ha
  simpa using key 1 (one_mem_closure_ind_centralByPrime G)

theorem central_case (G : Type) [Group G] [Finite G]
    (hG : ∃ l : ℕ, l.Prime ∧ ∀ y : G, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center G)
    (IH : ∀ T : Subgroup G, T ≠ ⊤ → ∀ f ∈ Virt ℂ ℂ T, f 1 = 0 → f ∈ D0 T) :
    ∀ f ∈ Virt ℂ ℂ G, f 1 = 0 → f ∈ D0 G := by
  classical
  obtain ⟨l, hl, hc⟩ := hG
  have : Fact l.Prime := ⟨hl⟩
  have hq : IsPGroup l (G ⧸ Subgroup.center G) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨j, hj⟩ := hc y
    exact ⟨j, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hj⟩
  have := hq.isNilpotent
  haveI : Group.IsNilpotent G :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (Subgroup.center G)) (by simp)
  have hab : AbByP G := ⟨l, hl, Subgroup.center G, inferInstance,
    fun a _ b hb => Subgroup.mem_center_iff.1 hb a, fun g => hc g⟩
  have C : ∀ χ : G → ℂ, IsChar ℂ ℂ χ → χ - (fun _ => χ 1) ∈ D0 G := by
    refine isChar_induction ℂ ℂ G (fun χ => χ - (fun _ => χ 1) ∈ D0 G) ?_ ?_
    · have e : (0 : G → ℂ) - (fun _ => (0 : G → ℂ) 1) = 0 := by funext g; simp
      rw [e]; exact zero_mem _
    · intro φ c hφ _ hQ
      have e : (φ + c) - (fun _ => (φ + c) 1) = (φ - fun _ => φ 1) + (c - fun _ => c 1) := by
        funext g; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [e]
      refine add_mem ?_ hQ
      rcases irrChar_linear_or_induced ℂ G φ hab hφ with ⟨lam, hlam⟩ | ⟨T, hT, ψ, hψ, rfl⟩
      · have hφc : IsChar ℂ ℂ φ := by obtain ⟨n, ρ, -, h⟩ := hφ; exact ⟨n, ρ, h⟩
        have hcl := (isChar_restrict_conj_one ℂ ℂ G φ hφc).2.1
        refine AddSubgroup.subset_closure ⟨⊤, lam.comp (⊤ : Subgroup G).subtype, ?_⟩
        have e1 : (fun h : (⊤ : Subgroup G) => ((lam.comp (⊤ : Subgroup G).subtype h : ℂˣ) : ℂ)) =
            fun h : (⊤ : Subgroup G) => φ (h : G) := by
          funext h; simp [hlam]
        rw [e1, ind_top φ hcl, ind_top (fun _ : G => (1 : ℂ)) (fun _ _ => rfl)]
        funext g; simp [hlam]
      · obtain ⟨n, hn, -⟩ := (isChar_restrict_conj_one ℂ ℂ T ψ hψ).2.2
        have hψV : ψ - (fun _ => ψ 1) ∈ Virt ℂ ℂ T := by
          refine sub_mem (isChar_mem_virt_complex hψ) ?_
          have e2 : (fun _ : T => ψ 1) = n • (fun _ : T => (1 : ℂ)) := by funext; simp [hn]
          rw [e2]; exact nsmul_mem (isChar_mem_virt_complex (isChar_one ℂ ℂ T)) n
        have h1 := inducedClassFunction_mem_degreeOneCharacterDiff T _ (IH T hT _ hψV (by simp))
        have h2 := ind_one_sub_index_mem_degreeOneDiff_nilpotent T.index T le_rfl
        have key : ind T ψ - (fun _ => ind T ψ 1) = ind T (ψ - fun _ => ψ 1) +
            (n : ℤ) • (ind T (fun _ => (1 : ℂ)) - fun _ => (T.index : ℂ)) := by
          rw [ind_sub]; funext g
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, ind_apply_one, hn, ind_const T (n : ℂ) g,
            zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Pi.natCast_apply]
          push_cast; ring
        rw [key]; exact add_mem h1 (zsmul_mem h2 _)
  intro f hf hf1
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_virt_iff_sub ℂ ℂ G f).1 hf
  have hab1 : a 1 = b 1 := by simpa [sub_eq_zero] using hf1
  have e : a - b = (a - fun _ => a 1) - (b - fun _ => b 1) := by funext g; simp [hab1]
  rw [e]; exact sub_mem (C a ha) (C b hb)

theorem virtualCharacter_degreeZero_mem_degreeOneDiff : ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G ≤ n →
    ∀ f ∈ Virt ℂ ℂ G, f 1 = 0 → f ∈ D0 G := by
  intro n
  induction n with
  | zero => intro G _ _ hG; have := Nat.card_pos (α := G); omega
  | succ n ih =>
    intro G _ _ hG f hf hf1
    have hcl : ∀ g x : G, f (x⁻¹ * g * x) = f g := (virt_mul_comap_conj_ind_linear G).2.2.1 f hf
    refine mem_degreeOneDiff_of_forall_centralByPrime G f hcl ?_
    intro E hE ψ hψ
    have hV : (fun e : E => ψ e * f e) ∈ Virt ℂ ℂ E :=
      (virt_mul_comap_conj_ind_linear E).1 ψ hψ _
        ((virt_mul_comap_conj_ind_linear G).2.1 f hf E E.subtype)
    have h1 : (fun e : E => ψ e * f e) 1 = 0 := by simp [hf1]
    by_cases hlt : Nat.card E < Nat.card G
    · exact inducedClassFunction_mem_degreeOneCharacterDiff E _ (ih E (by omega) _ hV h1)
    · have htop : E = ⊤ := (Subgroup.card_eq_iff_eq_top E).1
        (le_antisymm (Subgroup.card_le_card_group E) (not_lt.1 hlt))
      have hVG : ind E (fun e => ψ e * f e) ∈ Virt ℂ ℂ G :=
        (virt_mul_comap_conj_ind_linear G).2.2.2.1 E _ hV
      have hG1 : ind E (fun e => ψ e * f e) 1 = 0 := by rw [ind_apply_one]; simp [hf1]
      subst htop
      obtain ⟨l, hl, hc⟩ := hE
      have hG' : ∃ l : ℕ, l.Prime ∧ ∀ y : G, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center G := by
        refine ⟨l, hl, fun y => ?_⟩
        obtain ⟨j, hj⟩ := hc ⟨y, Subgroup.mem_top y⟩
        refine ⟨j, Subgroup.mem_center_iff.2 fun z => ?_⟩
        have := Subgroup.mem_center_iff.1 hj ⟨z, Subgroup.mem_top z⟩
        simpa using congrArg Subtype.val this
      refine central_case G hG' (fun T hT g hg hg1 => ih T ?_ g hg hg1) _ hVG hG1
      have := Subgroup.card_le_card_group T
      have hne : Nat.card T ≠ Nat.card G := fun h => hT ((Subgroup.card_eq_iff_eq_top T).1 h)
      omega

theorem exists_sum_induced_characters_of_mem_degreeOneDiff {G : Type} [Group G] [Fintype G] {f : G → ℂ} (hf : f ∈ D0 G) :
    ∃ (r : ℕ) (H : Fin r → Subgroup G) (χ : ∀ i, H i →* ℂˣ) (c : Fin r → ℤ), ∀ g : G,
      f g = ∑ i, (c i : ℂ) * (GlobalTheory.Published.indFun (H i) (fun x => (χ i x : ℂ)) g -
        GlobalTheory.Published.indFun (H i) (fun _ => 1) g) := by
  rw [D0, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_set'] at hf
  obtain ⟨n, c, s, hs⟩ := hf
  choose H χ hHχ using fun i => (s i).2
  refine ⟨n, H, χ, c, fun g => ?_⟩
  rw [← hs, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, hHχ i, zsmul_eq_mul, indFun_eq_ind, indFun_eq_ind]
  rfl

theorem brauerDegreeZero : GlobalTheory.Published.BrauerDegreeZero := by
  intro G _ _ V _ _ _ ρ
  classical
  have hchar := (isChar_and_isIrrChar_of_rep ℂ ℂ G V ρ).1
  have hV : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) ∈ Virt ℂ ℂ G := by
    have e : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) =
        (fun g => algebraMap ℂ ℂ (ρ.character g)) - (Module.finrank ℂ V) • (fun _ => (1 : ℂ)) := by
      funext g; simp [Representation.character]
    rw [e]
    exact sub_mem (isChar_mem_virt_complex hchar)
      (nsmul_mem (isChar_mem_virt_complex (isChar_one ℂ ℂ G)) _)
  have h1 : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) 1 = 0 := by simp
  exact exists_sum_induced_characters_of_mem_degreeOneDiff (virtualCharacter_degreeZero_mem_degreeOneDiff _ G le_rfl _ hV h1)

end GlobalTheory.BrauerZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffEmbeddingIntegersResCharUnitStatement
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffEmbedding_integers_resChar_unit : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (w : D.what₂.places.Pl), (∀ a : 𝓞 D.what₂.LL, B.ec j w (a : D.what₂.LL) ∈ (algebraMap (B.Oc j w) (FractionRing (B.Oc j w))).range) ∧ ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal ∧ ∀ (a : 𝓞 D.what₂.LL) (z : B.Oc j w), algebraMap (B.Oc j w) (FractionRing (B.Oc j w)) z = B.ec j w (a : D.what₂.LL) → (a ∈ (D.plEq w).asIdeal ↔ ¬ IsUnit z) := by
  first | exact @GlobalTheory.NLocPlace.ec_int_resChar_unit | exact GlobalTheory.NLocPlace.ec_int_resChar_unit | (intros; apply GlobalTheory.NLocPlace.ec_int_resChar_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactSpaceATopStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactSpace_aTop' : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)), letI := aTop (K := K) bO; CompactSpace (AA K LL) := by
  first | exact @GlobalTheory.WeakClosed.compactSpace_aTop | exact GlobalTheory.WeakClosed.compactSpace_aTop | (intros; apply GlobalTheory.WeakClosed.compactSpace_aTop <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionComparisonAdmissibleEveryPlaceOver
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BridgeTie

theorem localCoefficientCompatibility : ∀ (D : D7) (i : D.nd.Loc), TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i :=
  fun D i => coefficient_compatibility_of D i (fun w hw => GlobalTheory.bridge_degW D.nbr i w hw)

end GlobalTheory.BridgeTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcretePeriodDeRhamModuleFinrankLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedDdR

theorem ddR_finrank_le : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
      FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) ∧
        Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) ≤ Module.finrank ℚ_[l] ↥K.1 * Module.finrank ↥LL.1 V := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ
  haveI := LL.2
  exact GlobalTheory.Per.FontaineBound.ddR_finite_le (P.PD K) (GlobalTheory.Per.FontaineBound.isField_of_tied T) ρ

end GlobalTheory.Per.TiedDdR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfTailStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_of_tail_small_of_monomial_continuous : ∀ {O : Type} [CommRing O] [TopologicalSpace O] {n : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] (Φ : LetA O n →+ M), (∀ U ∈ 𝓝 (0 : M), ∃ k : ℕ, ∀ r : LetA O n, Φ (letπ ^ k * r) ∈ U) → (∀ j : ℕ, Continuous fun c : ZMod n → O => Φ (fun i => PowerSeries.C (c i) * PowerSeries.X ^ j)) → Continuous Φ := by
  first | exact @GlobalTheory.WeakClosed.continuous_of_tail | exact GlobalTheory.WeakClosed.continuous_of_tail | (intros; apply GlobalTheory.WeakClosed.continuous_of_tail <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOneTmulStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_one_tmul_latB : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d), letI := twTop T b; Continuous fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t := by
  first | exact @GlobalTheory.WeakClosed.continuous_one_tmul | exact GlobalTheory.WeakClosed.continuous_one_tmul | (intros; apply GlobalTheory.WeakClosed.continuous_one_tmul <;> assumption)
end

