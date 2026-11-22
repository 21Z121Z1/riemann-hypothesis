import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0161
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrowthGaloisInvariantsModPrimePowerLattice

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc

namespace ParamRing

variable {R : Type} [CommRing R] {σ : R⟦X⟧ →ₐ[R] R⟦X⟧} {w : R⟦X⟧} {s : ℕ}

theorem X_pow_dvd_map (h : σ X = w * X ^ s) {j : ℕ} {G : R⟦X⟧} (hG : X ^ j ∣ G) :
    X ^ (s * j) ∣ σ G := by
  obtain ⟨H, rfl⟩ := hG
  exact ⟨w ^ j * σ H, by rw [map_mul, map_pow, h, pow_mul]; ring⟩

theorem coeff_map_lead (h : σ X = w * X ^ s) (hs : 0 < s) {j : ℕ} {G : R⟦X⟧} (hG : X ^ j ∣ G) :
    coeff (s * j) (σ G) = constantCoeff w ^ j * coeff j G := by
  obtain ⟨H, rfl⟩ := hG
  have h0 : constantCoeff (σ H) = constantCoeff H := by
    conv_lhs => rw [eq_X_mul_shift_add_const H]
    rw [map_add, map_mul, h, show σ (C (constantCoeff H)) = C (constantCoeff H) from σ.commutes _]
    simp [hs.ne']
  have h1 : σ (X ^ j * H) = X ^ (s * j) * (w ^ j * σ H) := by
    rw [map_mul, map_pow, h, pow_mul]; ring
  have h2 := coeff_X_pow_mul (w ^ j * σ H) (s * j) 0
  have h3 := coeff_X_pow_mul H j 0
  rw [zero_add] at h2 h3
  rw [h1, h2, h3]
  simp [h0]

theorem lead_sum (h : σ X = w * X ^ s) (hs : 0 < s) (G : Fin s → R⟦X⟧) (n : ℕ)
    (hG : ∀ (k : Fin s) (j : ℕ), k + s * j < n → coeff j (G k) = 0) :
    X ^ n ∣ ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) ∧
      coeff n (∑ k : Fin s, X ^ (k : ℕ) * σ (G k)) =
        constantCoeff w ^ (n / s) * coeff (n / s) (G ⟨n % s, Nat.mod_lt _ hs⟩) := by
  have hn := Nat.mod_add_div n s
  have key : ∀ k : Fin s, (k : ℕ) ≠ n % s → X ^ (n + 1) ∣ X ^ (k : ℕ) * σ (G k) := by
    intro k hk
    have hk' := k.2
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · have h1 : X ^ (n / s + 1) ∣ G k := X_pow_dvd_iff.2 fun m hm => hG k m (by
        have := Nat.mul_le_mul_left s (Nat.lt_succ_iff.1 hm)
        omega)
      refine (pow_dvd_pow X ?_).trans ((X_pow_dvd_map h h1).mul_left _)
      have := Nat.mod_lt n hs
      rw [mul_add]; omega
    · have h1 : X ^ (n / s) ∣ G k := X_pow_dvd_iff.2 fun m hm => hG k m (by
        have := Nat.mul_le_mul_left s (Nat.succ_le_of_lt hm)
        rw [Nat.mul_succ] at this
        omega)
      refine (pow_dvd_pow X (show n + 1 ≤ k + s * (n / s) by omega)).trans ?_
      rw [pow_add]
      exact mul_dvd_mul_left _ (X_pow_dvd_map h h1)
  have h1 : X ^ (n / s) ∣ G ⟨n % s, Nat.mod_lt _ hs⟩ := X_pow_dvd_iff.2 fun m hm => hG _ m (by
    have := Nat.mul_lt_mul_of_pos_left hm hs
    simp only
    omega)
  constructor
  · refine Finset.dvd_sum fun k _ => ?_
    by_cases hk : (k : ℕ) = n % s
    · obtain rfl : k = ⟨n % s, Nat.mod_lt _ hs⟩ := Fin.ext hk
      conv_lhs => rw [← hn, pow_add]
      exact mul_dvd_mul_left _ (X_pow_dvd_map h h1)
    · exact (pow_dvd_pow X n.le_succ).trans (key k hk)
  · rw [map_sum, Finset.sum_eq_single ⟨n % s, Nat.mod_lt _ hs⟩]
    · rw [← coeff_map_lead h hs h1, ← coeff_X_pow_mul (σ _) (n % s) (s * (n / s)), add_comm, hn]
    · intro k _ hk
      exact X_pow_dvd_iff.1 (key k fun e => hk (Fin.ext e)) n n.lt_succ_self
    · simp

theorem eq_zero_of_lead (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (G : Fin s → R⟦X⟧)
    (hG : ∀ n, X ^ n ∣ ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) →
      coeff n (∑ k : Fin s, X ^ (k : ℕ) * σ (G k)) = 0 ∨ G ⟨n % s, Nat.mod_lt _ hs⟩ = 0) : G = 0 := by
  have key : ∀ n, ∀ (k : Fin s) (j : ℕ), k + s * j < n → coeff j (G k) = 0 := by
    intro n
    induction n with
    | zero => intro k j hj; omega
    | succ n ih =>
      intro k j hj
      rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj | hj
      · exact ih k j hj
      obtain ⟨h1, h2⟩ := lead_sum h hs G n ih
      have e1 : n % s = k := by rw [← hj, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.2]
      have e2 : n / s = j := by rw [← hj, Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt k.2, zero_add]
      have e3 : (⟨n % s, Nat.mod_lt _ hs⟩ : Fin s) = k := Fin.ext e1
      have h3 := hG n h1
      rw [h2, e3, e2] at h3
      rcases h3 with h3 | h3
      · exact ((hw.map constantCoeff).pow j).mul_right_eq_zero.1 h3
      · rw [h3, map_zero]
  ext k j
  exact key _ k j (Nat.lt_succ_self _)

theorem exists_sum (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (b : R⟦X⟧) :
    ∃ G : Fin s → R⟦X⟧, b = ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) := by
  obtain ⟨v, hv⟩ := hw.exists_right_inv
  let T : R⟦X⟧ → R⟦X⟧ := fun b => v * mk fun i => coeff (i + s) b
  let G : R⟦X⟧ → Fin s → R⟦X⟧ := fun b k => mk fun j => coeff k (T^[j] b)
  have hT : ∀ b : R⟦X⟧, b = σ X * T b + ∑ k : Fin s, X ^ (k : ℕ) * C (coeff k b) := by
    intro b
    have h1 : σ X * T b = X ^ s * mk fun i => coeff (i + s) b := by
      simp only [h, T]
      linear_combination (X ^ s * mk fun i => coeff (i + s) b) * hv
    rw [h1]
    ext n
    rw [map_add, coeff_X_pow_mul', map_sum]
    simp only [coeff_mul_C, coeff_X_pow, coeff_mk]
    split_ifs with hn
    · rw [Nat.sub_add_cancel hn, Finset.sum_eq_zero, add_zero]
      intro k _
      have := k.2
      rw [if_neg (by omega), zero_mul]
    · rw [zero_add, Finset.sum_eq_single ⟨n, by omega⟩]
      · simp
      · intro k _ hk
        rw [if_neg (fun e => hk (Fin.ext e.symm)), zero_mul]
      · simp
  have hG : ∀ b k, σ (G b k) = σ X * σ (G (T b) k) + C (coeff k b) := by
    intro b k
    have : G b k = X * G (T b) k + C (coeff k b) := by
      conv_lhs => rw [eq_X_mul_shift_add_const (G b k)]
      simp [G]
    rw [this, map_add, map_mul]
    congr 1
    exact σ.commutes _
  have key : ∀ n, ∀ b : R⟦X⟧, X ^ n ∣ b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G b k) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro b
      have : b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G b k) =
          σ X * (T b - ∑ k : Fin s, X ^ (k : ℕ) * σ (G (T b) k)) := by
        have h1 := hT b
        simp only [hG b, mul_add, Finset.sum_add_distrib, mul_sub, Finset.mul_sum, mul_left_comm (σ X)]
        linear_combination h1
      rw [this, pow_succ']
      refine mul_dvd_mul ?_ (ih _)
      rw [h]
      exact (dvd_pow_self X hs.ne').mul_left w
  refine ⟨G b, sub_eq_zero.1 ?_⟩
  ext n
  exact X_pow_dvd_iff.1 (key (n + 1) b) n n.lt_succ_self

theorem existsUnique_sum (h : σ X = w * X ^ s) (hs : 0 < s) (hw : IsUnit w) (b : R⟦X⟧) :
    ∃! G : Fin s → R⟦X⟧, b = ∑ k : Fin s, X ^ (k : ℕ) * σ (G k) := by
  obtain ⟨G, hG⟩ := exists_sum h hs hw b
  refine ⟨G, hG, fun G' hG' => sub_eq_zero.1 (eq_zero_of_lead h hs hw _ fun n _ => Or.inl ?_)⟩
  simp only [Pi.sub_apply, map_sub σ, mul_sub, Finset.sum_sub_distrib, ← hG, ← hG', sub_self, map_zero]

theorem algebraMap_injective (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    [Algebra ℤ_[l] O] (hl : (l : O) ≠ 0) : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h0
  rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
  exact mul_ne_zero ((Units.isUnit _).map _).ne_zero (pow_ne_zero _ hl) hx

end ParamRing

open ParamRing

theorem invariants_param : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ (Δ : Subgroup ℤ_[l]ˣ) [Fintype ↥Δ] (π' w : PowerSeries O), IsUnit w → π' = w * PowerSeries.X ^ Fintype.card ↥Δ → (∀ d : ↥Δ, act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) π' = π') → (∀ b : PowerSeries O, ∃! G : Fin (Fintype.card ↥Δ) → PowerSeries O, b = ∑ k : Fin (Fintype.card ↥Δ), PowerSeries.X ^ (k : ℕ) * PowerSeries.subst π' (G k)) ∧ ∀ b : PowerSeries O, (∀ d : ↥Δ, act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) b = b) ↔ ∃ g : PowerSeries O, b = PowerSeries.subst π' g := by
  intro l _ O _ _ _ _ _ hl _ Δ _ π' w hw hπ hinv
  have hs : 0 < Fintype.card ↥Δ := Fintype.card_pos
  have hsub : HasSubst π' := HasSubst.of_constantCoeff_zero' (by simp [hπ, hs.ne'])
  set σ : O⟦X⟧ →ₐ[O] O⟦X⟧ := substAlgHom hsub with hσ
  have hσa : ∀ g, subst π' g = σ g := fun g => (congrFun (coe_substAlgHom hsub) g).symm
  have hσX : σ X = w * X ^ Fintype.card ↥Δ := (substAlgHom_X hsub).trans hπ
  have hfix : ∀ (d : ↥Δ) (g : O⟦X⟧), act l O ((d : ℤ_[l]ˣ) : ℤ_[l]) (σ g) = σ g := by
    intro d g
    have := hinv d
    rw [act_apply] at this
    rw [← hσa, act_apply, subst_comp_subst_apply hsub
      (HasSubst.of_constantCoeff_zero' (cyc_const l O _)), this]
  simp only [hσa]
  refine ⟨existsUnique_sum hσX hs hw, fun b => ⟨fun hb => ?_, ?_⟩⟩
  swap
  · rintro ⟨g, rfl⟩ d
    exact hfix d g
  obtain ⟨G, hG⟩ := exists_sum hσX hs hw b
  refine ⟨G ⟨0, hs⟩, ?_⟩
  have hG' : b - σ (G ⟨0, hs⟩) =
      ∑ k : Fin (Fintype.card ↥Δ), X ^ (k : ℕ) * σ (Function.update G ⟨0, hs⟩ 0 k) := by
    rw [hG, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hs⟩),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, hs⟩)]
    simp only [pow_zero, one_mul, Function.update_self, map_zero, zero_add, add_sub_cancel_left]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have h0 : Function.update G ⟨0, hs⟩ 0 = 0 := by
    refine eq_zero_of_lead hσX hs hw _ fun n hn => ?_
    rw [← hG'] at hn ⊢
    by_cases hd : Fintype.card ↥Δ ∣ n
    · right
      have : (⟨n % _, Nat.mod_lt _ hs⟩ : Fin (Fintype.card ↥Δ)) = ⟨0, hs⟩ :=
        Fin.ext (Nat.mod_eq_zero_of_dvd hd)
      rw [this, Function.update_self]
    left
    by_contra hc
    apply hd
    haveI : IsCyclic ↥Δ := isCyclic_of_injective_ringHom ((Units.coeHom ℤ_[l]).comp Δ.subtype)
      (Units.val_injective.comp Subtype.val_injective)
    obtain ⟨d, hd⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Δ)
    rw [← Nat.card_eq_fintype_card, ← hd, orderOf_dvd_iff_pow_eq_one]
    obtain ⟨u, hu⟩ : (X : O⟦X⟧) ∣ cyc l O ((d : ℤ_[l]ˣ) : ℤ_[l]) := X_dvd_iff.2 (cyc_const l O _)
    have hu0 : constantCoeff u = algebraMap ℤ_[l] O ((d : ℤ_[l]ˣ) : ℤ_[l]) := by
      rw [← coeff_one_cyc, hu, coeff_succ_X_mul, coeff_zero_eq_constantCoeff]
    have h1 := coeff_map_lead (σ := act l O ((d : ℤ_[l]ˣ) : ℤ_[l])) (w := u) (s := 1)
      (by rw [act_X, hu, pow_one, mul_comm]) one_pos hn
    rw [map_sub (act l O _), hb, hfix, one_mul, hu0, ← map_pow, eq_comm, mul_eq_right₀ hc,
      ← map_one (algebraMap ℤ_[l] O)] at h1
    have h2 := algebraMap_injective l O hl h1
    ext
    simpa using h2
  rw [← sub_eq_zero, hG', h0]
  simp

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLatticeCocyclesModUniformizerPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CocycleModPow

theorem cocycles_finite (hT : Formalism.GaloisCohomology.LocalTateDualityK) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : ↥(GK K) → M →+ M) (h1 : ∀ m, a 1 m = m)
    (hmul : ∀ g h m, a (g * h) m = a g (a h m)) (hr : ∀ m : M, l ^ r • m = 0)
    (hlc : ∀ m, IsLocallyConstant fun g => a g m) :
    {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hr, smul_zero]
  have _ : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ (r + 1))) M) := ⟨AddCommGroup.zmodModule hr'⟩
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ (r + 1))) (Formalism.GaloisCohomology.GK l K.1) M :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => a (φ.symm g)) (fun m => by rw [map_one, h1])
      (fun g h m => by rw [map_mul, hmul])
  have ha : ∀ (g : Formalism.GaloisCohomology.GK l K.1) (m : M), (rho g : M →ₗ[ZMod (l ^ (r + 1))] M) m = a (φ.symm g) m := fun _ _ => rfl
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  have hH := (GlobalTheory.T.finite_H1_H2_local hT l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho).1
  have hZ := GlobalTheory.CocycleCount.card_cocycles_mul_invariants_discrete _ _ M rho hrho
  have hH1 : 0 < Nat.card (ReciprocityTheory.Gal.H1 rho) := Nat.card_pos
  have hM : 0 < Nat.card M := Nat.card_pos
  have hfin : Finite (ReciprocityTheory.Gal.Z1 rho) := by
    refine Nat.finite_of_card_ne_zero fun h0 => ?_
    rw [h0, zero_mul] at hZ
    exact (Nat.mul_pos hH1 hM).ne hZ
  let E : ↥{c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} →
      ↥(ReciprocityTheory.Gal.Z1 rho) :=
    fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, c.2.2]⟩
  refine Set.finite_coe_iff.1 (Finite.of_injective E fun c c' h => Subtype.ext (funext fun g => ?_))
  have := congrFun (congrArg Subtype.val h) (φ g)
  simpa only [E, φ.symm_apply_apply] using this

theorem dvd_and_finite (l : ℕ) [Fact l.Prime] (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (hO : GoodO (Qp := ℚ_[l]) LL O)
    (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) :
    ϖ ^ n ∣ ((l : ℕ) : O) ^ n ∧ Finite (O ⧸ Ideal.span {ϖ ^ n}) := by
  obtain ⟨-, -, hfin, hcomp⟩ := GlobalTheory.T.coefficient_ring_integers_compact_adic_properties l LL O hO
  obtain ⟨⟨hdom, hdvr, -⟩, -⟩ := hO
  have hnu : ¬ IsUnit ((l : ℕ) : O) := fun hu => by
    have htop : Ideal.span {((l : ℕ) : O)} = ⊤ := Ideal.span_singleton_eq_top.2 hu
    have hH : IsHausdorff (Ideal.span {((l : ℕ) : O)}) O := hcomp.toIsHausdorff
    have h1 : (1 : O) = 0 := hH.haus 1 fun k => by
      rw [htop, SModEq.zero]
      simp [Ideal.top_pow]
    exact one_ne_zero h1
  have hdvd : ϖ ∣ ((l : ℕ) : O) := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hnu
  have hd : ϖ ^ n ∣ ((l : ℕ) : O) ^ n := pow_dvd_pow_of_dvd hdvd n
  refine ⟨hd, ?_⟩
  have := hfin n
  exact Finite.of_surjective _
    (Ideal.Quotient.factor_surjective (Ideal.span_singleton_le_span_singleton.2 hd))

theorem finite_Z1Q : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (n : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)), (quotientCocycles LA _ hI : Set (↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T))).Finite := by
  intro hT l _ K LL _ _ _ O _ _ hO A LA ϖ hϖ n hI
  obtain ⟨hd, hfin⟩ := dvd_and_finite l LL O hO ϖ hϖ n
  have hring : IsTopologicalRing LL := hO.2.2.2.1
  have hopen : IsOpen (LA.T : Set A.V) :=
    GlobalTheory.Cyc.isOpen_of_fg_of_span_eq_top hO.2.2.2.2 LA.T LA.fg LA.span
  obtain ⟨⟨hdom, hdvr, hfrac⟩, -⟩ := hO
  have hTfin : Module.Finite O ↥LA.T := Module.Finite.iff_fg.2 LA.fg
  have hQ : Finite (↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) := by
    have : Module.Finite (O ⧸ Ideal.span {ϖ ^ n})
        (↥LA.T ⧸ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T)) :=
      Module.Finite.of_restrictScalars_finite O _ _
    exact Module.finite_of_finite (O ⧸ Ideal.span {ϖ ^ n})
  have hmem : ∀ t : ↥LA.T, ϖ ^ n • t ∈ (Ideal.span {ϖ ^ n} • ⊤ : Submodule O ↥LA.T) := fun t =>
    Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have hc : algebraMap O LL (ϖ ^ n) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact pow_ne_zero _ hϖ.ne_zero
  haveI := IsModuleTopology.topologicalAddGroup LL A.V
  refine cocycles_finite hT l K n _ (fun g => (actQ LA _ hI g).toAddMonoidHom) ?_ ?_ ?_ ?_
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (actT LA 1 x) = _
      congr 1
      apply Subtype.ext
      change A.ρ 1 x = x
      simp
  · intro g h m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      change Submodule.Quotient.mk (actT LA (g * h) x) =
        Submodule.Quotient.mk (actT LA g (actT LA h x))
      congr 1
      apply Subtype.ext
      change A.ρ (g * h) x = A.ρ g (A.ρ h x)
      simp
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨b, hb⟩ := hd
      rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Nat.cast_pow, hb, mul_smul]
      exact hmem _
  · intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      rw [IsLocallyConstant.iff_eventually_eq]
      intro g₀
      have hcont : Continuous fun g : ↥(GK K) =>
          (algebraMap O LL (ϖ ^ n))⁻¹ • (A.ρ g x - A.ρ g₀ x) :=
        ((A.cont x).sub continuous_const).const_smul _
      have hev := (hopen.preimage hcont).mem_nhds (x := g₀) (by simp)
      filter_upwards [hev] with g hg
      change Submodule.Quotient.mk (actT LA g x) = Submodule.Quotient.mk (actT LA g₀ x)
      rw [Submodule.Quotient.eq]
      convert hmem ⟨_, hg⟩ using 1
      apply Subtype.ext
      change A.ρ g x - A.ρ g₀ x = ϖ ^ n • ((algebraMap O LL (ϖ ^ n))⁻¹ • (A.ρ g x - A.ρ g₀ x))
      rw [← algebraMap_smul LL (ϖ ^ n), smul_smul, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.CocycleModPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpansLeContinuousCocycles
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.CocN

open GlobalTheory.Cut.Coc

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (S : IdempotentChoiceData D.nd i)

theorem blocks (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) (g : GE D.nd) :
    S.ψρ (tw i r S g) = WpO D.nd i ρ π g ∧
    ∀ c : Fin D.R.t, S.ψχ c (tw i r S g) =
      (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have key : ∀ w : (Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i),
      (((S.ψρ (tw i r S g)).map (toK D.nd i)).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i (S.ψχ c (tw i r S g)) * w.2 c) =
      toK D.nd i (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * w.2 c) := by
    intro w
    obtain ⟨u, rfl⟩ := S.e.surjective w
    rw [← h2 _ (tw_mem i r S g) u, ← h1 g u, ← map_smul, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [tw, hp, mapM]
  have hinj : Function.Injective (toK D.nd i) := IsFractionRing.injective _ _
  constructor
  · ext p q
    apply hinj
    have := congrFun (congrArg Prod.fst (key (Pi.single q 1, 0))) p
    simpa [mapM, WpO, twistM] using this
  · intro c
    apply hinj
    have := congrFun (congrArg Prod.snd (key (0, 1))) c
    simpa using this

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  intro D i r ρ π Xs S hr hS _
  refine ⟨cocW_le i r S hr Xs _ _ fun g => (blocks i r S ρ π hS g).1, fun c =>
    cocW_le i r S hr Xs _ _ fun g => ?_⟩
  rw [(blocks i r S ρ π hS g).2 c, mul_comm]
  rfl

end GlobalTheory.Cut.CocN

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineThetaNatural
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.Per

theorem untilt_natural {O : Type} [CommRing O] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (σ : O →+* O) (τ : PreTilt O p →+* PreTilt O p)
    (h : ∀ (x : PreTilt O p) (n : ℕ) (y : O),
      PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {(p : O)}) y →
        PreTilt.coeff n (τ x) = Ideal.Quotient.mk (Ideal.span {(p : O)}) (σ y))
    (x : PreTilt O p) : (τ x).untilt = σ x.untilt := by
  refine Perfection.teichmuller_spec (I := Ideal.span {(p : O)}) fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : O)}) (PreTilt.coeff n x)
  refine ⟨σ y, (h x n y hy.symm).symm, ?_⟩
  have h1 := (Perfection.teichmuller_sModEq (I := Ideal.span {(p : O)}) (x := x) hy).symm
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1 ⊢
  have h2 := map_dvd σ h1
  rw [map_pow, map_natCast, map_sub, map_pow] at h2
  exact h2

theorem fontaineTheta_natural {O : Type} [CommRing O] {p : ℕ} [Fact p.Prime] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (σ : O →+* O) (τ : PreTilt O p →+* PreTilt O p)
    (h : ∀ (x : PreTilt O p) (n : ℕ) (y : O),
      PreTilt.coeff n x = Ideal.Quotient.mk (Ideal.span {(p : O)}) y →
        PreTilt.coeff n (τ x) = Ideal.Quotient.mk (Ideal.span {(p : O)}) (σ y))
    (a : WittVector p (PreTilt O p)) :
    WittVector.fontaineTheta O p (WittVector.map τ a) = σ (WittVector.fontaineTheta O p a) := by
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : O)})).2 fun n => ?_
  rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, ← Ideal.Quotient.eq]
  have key := WittVector.eq_of_apply_teichmuller_eq
    ((Ideal.Quotient.mk (Ideal.span {(p : O)} ^ n)).comp
      ((WittVector.fontaineTheta O p).comp (WittVector.map τ)))
    ((Ideal.Quotient.mk (Ideal.span {(p : O)} ^ n)).comp (σ.comp (WittVector.fontaineTheta O p)))
    ⟨n, by
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : O)} ^ n)), ← map_pow,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n⟩
    (fun x => by
      simp only [RingHom.comp_apply, WittVector.map_teichmuller,
        WittVector.fontaineTheta_teichmuller, untilt_natural σ τ h])
  exact RingHom.congr_fun key a

end GlobalTheory.Per
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_sub_one_wittTensorLattice_surjective_fixed : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∀ y : TW (RW LL) T, ∃ b, TWmap (φRW LL) T b - b = y) ∧ (∀ b : TW (RW LL) T, TWmap (φRW LL) T b = b ↔ ∃ t : ↥T.L.T, b = (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ Function.Injective (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) := by
  first | exact @GlobalTheory.WittTensorFixed.main | exact GlobalTheory.WittTensorFixed.main | (intros; apply GlobalTheory.WittTensorFixed.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisFixedSubringTensorWittSaturatedCompleteStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisFixedSubringTensorWitt_saturated_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (LL : FinExt l) (H : Set (GQ l)), (∀ x, (l : RW LL) * x ∈ fixSub AI LL H → x ∈ fixSub AI LL H) ∧ (∀ x ∈ fixSub AI LL H, φRW LL x ∈ fixSub AI LL H) ∧ ∀ x : ℕ → RW LL, (∀ i, x i ∈ fixSub AI LL H) → ∃ y ∈ fixSub AI LL H, ∀ k : ℕ, ∃ r, y - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r := by
  first | exact @GlobalTheory.Decompl.FixL.fixSub_ladic | exact GlobalTheory.Decompl.FixL.fixSub_ladic | (intros; apply GlobalTheory.Decompl.FixL.fixSub_ladic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GrowthGaloisInvariantsModPrimePowerLatticeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.growth_galois_invariants_mod_prime_power_lattice : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∃ C : ℕ, 0 < C ∧ ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL ↥(H0V A.ρ)) ≤ Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ∧ Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} ≤ C * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * finrank LL ↥(H0V A.ρ)) := by
  first | exact @GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt | exact GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt | (intros; apply GlobalTheory.GrowthOfInvariants.growth_galois_invariants_mod_prime_power_lattice_alt <;> assumption)
end

