import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSpanEigenOfBaseChangeEigen
section
open scoped TensorProduct

namespace GlobalTheory

theorem mem_span_eigen_of_baseChange_eigen (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M]
    [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
    (g : S → Module.End ℤ_[l] M) (χ : S → ℤ_[l]) (hB : ∀ s, ∀ b ∈ B, g s b ∈ B)
    (x : PadicAlgCl l ⊗[ℤ_[l]] M)
    (hx : x ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype))
    (he : ∀ s, LinearMap.baseChange (PadicAlgCl l) (g s) x
      = algebraMap ℤ_[l] (PadicAlgCl l) (χ s) • x) :
    x ∈ Submodule.span (PadicAlgCl l)
      {y | ∃ b ∈ B, (∀ s, g s b = χ s • b) ∧ y = (1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] b} := by
  classical
  obtain ⟨x', rfl⟩ := hx
  have hinj0 : Function.Injective (algebraMap ℤ_[l] (PadicAlgCl l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (PadicAlgCl l), RingHom.coe_comp]
    exact (algebraMap ℚ_[l] (PadicAlgCl l)).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  haveI : FaithfulSMul ℤ_[l] (PadicAlgCl l) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj0
  haveI : Module.IsTorsionFree ℤ_[l] (PadicAlgCl l) := inferInstance
  haveI : Module.Flat ℤ_[l] (PadicAlgCl l) := inferInstance
  obtain ⟨P, hP, z, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_subtype x'
  haveI : Module.Finite ℤ_[l] P := Module.Finite.iff_fg.2 hP
  haveI : Module.Free ℤ_[l] P := inferInstance
  let ω := Module.Free.chooseBasis ℤ_[l] P
  let Φ : P ⊗[ℤ_[l]] B →ₗ[ℤ_[l]] PadicAlgCl l ⊗[ℤ_[l]] M :=
    (B.subtype.lTensor (PadicAlgCl l)) ∘ₗ (P.subtype.rTensor B)
  have hΦ : Function.Injective Φ :=
    (Module.Flat.lTensor_preserves_injective_linearMap _ B.injective_subtype).comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ P.injective_subtype)
  have hΦz : ∀ w, LinearMap.baseChange (PadicAlgCl l) B.subtype (P.subtype.rTensor B w) = Φ w :=
    fun w => rfl
  have hΦt : ∀ (a : P) (b : B), Φ (a ⊗ₜ b) = (a : PadicAlgCl l) ⊗ₜ (b : M) := fun a b => rfl
  rw [hΦz] at he ⊢
  let h : S → Module.End ℤ_[l] B := fun s => (g s).restrict (hB s) - χ s • LinearMap.id
  have hcomm : ∀ s w, Φ ((h s).lTensor P w)
      = LinearMap.baseChange (PadicAlgCl l) (g s) (Φ w) - χ s • Φ w := by
    intro s w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [LinearMap.lTensor_tmul, hΦt, hΦt, LinearMap.baseChange_tmul, ← TensorProduct.tmul_smul,
        ← TensorProduct.tmul_sub]
      rfl
    | add u v hu hv => simp only [map_add, hu, hv, smul_add]; abel
  have hz : ∀ s, (h s).lTensor P z = 0 := by
    intro s
    apply hΦ
    rw [hcomm, he s, algebraMap_smul, sub_self, map_zero]
  obtain ⟨c, rfl⟩ := (TensorProduct.equivFinsuppOfBasisLeft (N := B) ω).symm.surjective z
  have hc : ∀ s i, h s (c i) = 0 := by
    intro s i
    have e : (h s).lTensor P ((TensorProduct.equivFinsuppOfBasisLeft (N := B) ω).symm c)
        = (TensorProduct.equivFinsuppOfBasisLeft (N := B) ω).symm
          (c.mapRange (h s) (map_zero _)) := by
      rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
        TensorProduct.equivFinsuppOfBasisLeft_symm_apply,
        Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _), map_finsuppSum]
      rfl
    have e2 := hz s
    rw [e, LinearEquiv.map_eq_zero_iff] at e2
    simpa using DFunLike.congr_fun e2 i
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, map_finsuppSum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have e : Φ (ω i ⊗ₜ c i) = (ω i : PadicAlgCl l) • ((1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] (c i : M)) := by
    rw [hΦt, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  change Φ (ω i ⊗ₜ c i) ∈ _
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨c i, (c i).2, fun s => ?_, rfl⟩)
  have := congrArg Subtype.val (hc s i)
  exact sub_eq_zero.1 this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicFactorCoeffNatDegreeLe
section
open Polynomial

namespace GlobalTheory.MonicFactorDegree

variable {κ : Type} [Field κ]

noncomputable def subst (D : ℕ) : Polynomial (Polynomial κ) →+* Polynomial (Polynomial κ) :=
  eval₂RingHom (mapRingHom (C : κ →+* Polynomial κ)) (C X * X ^ D)

lemma term_coeff (D j m i : ℕ) (p : Polynomial κ) :
    (((mapRingHom (C : κ →+* Polynomial κ)) p * (C X * X ^ D) ^ j).coeff m).coeff i =
      if D * j ≤ m then (if i = j then p.coeff (m - D * j) else 0) else 0 := by
  have hC : (C (X : Polynomial κ) : Polynomial (Polynomial κ)) ^ j = C (X ^ j) := (C_pow ..).symm
  rw [mul_pow, hC, ← pow_mul, ← mul_assoc, coeff_mul_X_pow']
  split_ifs with h1 h2
  · subst h2; rw [coeff_mul_C, coe_mapRingHom, coeff_map, coeff_C_mul_X_pow]; simp
  · rw [coeff_mul_C, coe_mapRingHom, coeff_map, coeff_C_mul_X_pow]; simp [h2]
  · simp

lemma subst_coeff_coeff (D : ℕ) (P : Polynomial (Polynomial κ)) (i k : ℕ) :
    ((subst D P).coeff (k + D * i)).coeff i = (P.coeff i).coeff k := by
  simp only [subst, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum, finset_sum_coeff, term_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro hi; simp [notMem_support_iff.mp hi]

theorem monic_factor_coeff_natDegree_le : ∀ {κ : Type} [Field κ] (Φ A B : Polynomial (Polynomial κ))
    (D : ℕ), Φ.Monic → A.Monic → B.Monic → Φ = A * B → (∀ i, (Φ.coeff i).natDegree ≤ D) →
    ∀ i, (A.coeff i).natDegree ≤ Φ.natDegree * D := by
  intro κ _ Φ A B D hΦ _ hB hAB hD i
  by_cases hi : A.coeff i = 0
  · simp [hi]
  have key : ∀ P : Polynomial (Polynomial κ), ∀ j, P.coeff j ≠ 0 →
      (P.coeff j).natDegree + D * j ≤ (subst D P).natDegree ∧ subst D P ≠ 0 := by
    intro P j hj
    have h := subst_coeff_coeff D P j (P.coeff j).natDegree
    have hne : (subst D P).coeff ((P.coeff j).natDegree + D * j) ≠ 0 := by
      intro h0
      rw [h0, coeff_zero] at h
      exact hj (leadingCoeff_eq_zero.mp h.symm)
    exact ⟨le_natDegree_of_ne_zero hne, fun h0 => hne (by simp [h0])⟩
  have hAi := key A i hi
  have hB0 := (key B B.natDegree (by rw [hB.coeff_natDegree]; exact one_ne_zero)).2
  have hmul : (subst D Φ).natDegree = (subst D A).natDegree + (subst D B).natDegree := by
    rw [hAB, map_mul, natDegree_mul hAi.2 hB0]
  have hup : (subst D Φ).natDegree ≤ Φ.natDegree * D := by
    simp only [subst, coe_eval₂RingHom, eval₂_eq_sum, Polynomial.sum]
    apply natDegree_sum_le_of_forall_le
    intro j hj
    have hjd : j ≤ Φ.natDegree := le_natDegree_of_mem_supp j hj
    have h1 : (mapRingHom (C : κ →+* Polynomial κ) (Φ.coeff j)).natDegree ≤ (Φ.coeff j).natDegree := by
      rw [coe_mapRingHom]; exact natDegree_map_le
    have h2 : ((C X * X ^ D : Polynomial (Polynomial κ)) ^ j).natDegree ≤ j * D := by
      calc _ ≤ j * (C X * X ^ D : Polynomial (Polynomial κ)).natDegree := natDegree_pow_le
        _ ≤ j * D := by
          apply Nat.mul_le_mul_left
          calc _ ≤ (C X : Polynomial (Polynomial κ)).natDegree + (X ^ D : Polynomial (Polynomial κ)).natDegree :=
                natDegree_mul_le
            _ = D := by simp
    have h3 : (Φ.coeff j).natDegree + j * D ≤ Φ.natDegree * D := by
      rcases hjd.lt_or_eq with h | h
      · have h4 := hD j
        have h5 : (j + 1) * D ≤ Φ.natDegree * D := Nat.mul_le_mul_right _ h
        rw [add_mul, one_mul] at h5
        omega
      · rw [h, hΦ.coeff_natDegree, natDegree_one, zero_add]
    exact (natDegree_mul_le).trans (by omega)
  have := hAi.1
  have h6 : (A.coeff i).natDegree ≤ (subst D A).natDegree := by omega
  omega

end GlobalTheory.MonicFactorDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MvPowerSeriesThreeEqZeroOfSubstLines
section
namespace GlobalTheory

theorem mvPowerSeries_three_eq_zero_of_subst_lines :
    ∀ (K : Type) [Field K] [Infinite K] (Φ : MvPowerSeries (Fin 3) K),
      (∀ t : Fin 3 → K, (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ : PowerSeries K) = 0) →
      Φ = 0 := by
  intro K _ _ Φ h
  ext d
  set n := ∑ i, d i with hn
  let S : Finset (Fin 3 →₀ ℕ) :=
    (Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => n)).filter (fun e => ∑ i, e i = n)
  have hS : ∀ e, e ∈ S ↔ ∑ i, e i = n := by
    intro e
    simp only [S, Finset.mem_filter, Finset.mem_Iic, and_iff_right_iff_imp]
    intro he i
    change e i ≤ n
    rw [← he]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  let P : MvPolynomial (Fin 3) K := ∑ e ∈ S, MvPolynomial.monomial e (MvPowerSeries.coeff e Φ)
  have hcoef : ∀ t : Fin 3 → K, PowerSeries.coeff n (MvPowerSeries.subst
      (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) = MvPolynomial.eval t P := by
    intro t
    have ha : MvPowerSeries.HasSubst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
        rw [map_mul]; exact mul_eq_zero_of_right _ (MvPowerSeries.constantCoeff_X ()))
    have hprod : ∀ e : Fin 3 →₀ ℕ,
        (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) =
          PowerSeries.C (∏ s, t s ^ e s) * PowerSeries.X ^ (∑ s, e s) := by
      intro e
      rw [Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_prod, map_pow]
    have h1 : PowerSeries.coeff n (MvPowerSeries.subst
        (fun i => (PowerSeries.C (t i) * PowerSeries.X : PowerSeries K)) Φ) =
        ∑ᶠ e : Fin 3 →₀ ℕ, MvPowerSeries.coeff e Φ • PowerSeries.coeff n
          (e.prod fun s k => (PowerSeries.C (t s) * PowerSeries.X : PowerSeries K) ^ k) :=
      MvPowerSeries.coeff_subst ha Φ (Finsupp.single () n)
    rw [h1]
    simp only [hprod, PowerSeries.coeff_C_mul_X_pow, smul_eq_mul]
    rw [finsum_eq_sum_of_support_subset _ (s := S) ?_]
    · simp only [P, map_sum, MvPolynomial.eval_monomial]
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [if_pos ((hS e).1 he).symm, Finsupp.prod_fintype _ _ (fun s => pow_zero _)]
    · intro e he
      rw [Function.mem_support] at he
      rw [Finset.mem_coe, hS]
      by_contra hne
      exact he (by rw [if_neg (Ne.symm hne), mul_zero])
  have hP : P = 0 := MvPolynomial.funext (fun t => by rw [← hcoef, h t, map_zero, map_zero])
  have hd := congrArg (MvPolynomial.coeff d) hP
  simp only [P, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial,
    Finset.sum_ite_eq', Finset.sum_ite_eq, if_pos ((hS d).2 rfl)] at hd
  simpa using hd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NewtonPowerSeriesSurjectiveLinearizationSolution
section
open Polynomial

namespace GlobalTheory

theorem newton_powerSeries_of_surjective_linearisation (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ]
    (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k))
    (hL : Function.Surjective L)
    (h0 : ∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0)
    (hG : ∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
      (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e -
        PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) :
    ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 := by
  classical
  let r := Function.surjInv hL
  have hLr : ∀ v, L (r v) = v := Function.surjInv_eq hL
  let step : ℕ → (ι → PowerSeries k) → (ι → PowerSeries k) := fun m x i =>
    x i + PowerSeries.X ^ m * PowerSeries.C (r (fun e => -PowerSeries.coeff m (G x e)) i)
  let sq : ℕ → (ι → PowerSeries k) := fun n =>
    Nat.rec (motive := fun _ => ι → PowerSeries k) (fun i => PowerSeries.C (x₀ i)) (fun n x => step (n + 1) x) n
  have sq_zero : sq 0 = fun i => PowerSeries.C (x₀ i) := rfl
  have sq_succ : ∀ n, sq (n + 1) = step (n + 1) (sq n) := fun n => rfl
  have coeffXC : ∀ (m j : ℕ) (c : k),
      PowerSeries.coeff j ((PowerSeries.X : PowerSeries k) ^ m * PowerSeries.C c) = if j = m then c else 0 := by
    intro m j c
    rw [mul_comm, PowerSeries.coeff_C_mul_X_pow]
  have inv : ∀ n, (∀ i, PowerSeries.constantCoeff (sq n i) = x₀ i) ∧
      ∀ e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G (sq n) e := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i => by simp [sq_zero], fun e => ?_⟩
      rw [zero_add, pow_one, PowerSeries.X_dvd_iff, sq_zero]
      exact h0 e
    | succ n ih =>
      have hc : ∀ i, PowerSeries.constantCoeff (sq (n + 1) i) = x₀ i := by
        intro i
        simp [sq_succ, step, ih.1 i]
      refine ⟨hc, fun e => ?_⟩
      set x := sq n with hx
      set v : κ → k := fun e => -PowerSeries.coeff (n + 1) (G x e) with hv
      have key := hG x (fun i => PowerSeries.C (r v i)) (n + 1) (by omega) ih.1 e
      have hcv : (fun i => PowerSeries.constantCoeff (PowerSeries.C (r v i))) = r v := by
        funext i; simp
      rw [hcv, hLr] at key
      have hs : sq (n + 1) = fun i => x i + PowerSeries.X ^ (n + 1) * PowerSeries.C (r v i) := by
        rw [sq_succ]
      have h2 : (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) ∣
          G x e + PowerSeries.X ^ (n + 1) * PowerSeries.C (v e) := by
        rw [PowerSeries.X_pow_dvd_iff]
        intro j hj
        rw [map_add, coeffXC]
        rcases Nat.lt_or_ge j (n + 1) with hj' | hj'
        · have := (PowerSeries.X_pow_dvd_iff.mp (ih.2 e)) j hj'
          rw [this, if_neg (by omega), add_zero]
        · have hjn : j = n + 1 := by omega
          subst hjn
          simp [hv]
      have := dvd_add key h2
      rw [hs]
      convert this using 1
      ring
  have stab : ∀ i j n, j ≤ n → PowerSeries.coeff j (sq n i) = PowerSeries.coeff j (sq j i) := by
    intro i j n hjn
    induction n, hjn using Nat.le_induction with
    | base => rfl
    | succ n hjn ihn =>
      rw [← ihn, sq_succ]
      simp only [step, map_add]
      rw [coeffXC, if_neg (by omega), add_zero]
  let xl : ι → PowerSeries k := fun i => PowerSeries.mk (fun j => PowerSeries.coeff j (sq j i))
  have hdiff : ∀ n i, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ xl i - sq n i := by
    intro n i
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    simp only [xl, map_sub, PowerSeries.coeff_mk]
    rw [stab i j n (by omega), sub_self]
  have hlim : ∀ n e, (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e := by
    intro n e
    choose d hd using hdiff n
    have hx : xl = fun i => sq n i + PowerSeries.X ^ (n + 1) * d i := by
      funext i; rw [← hd i]; ring
    have key := hG (sq n) d (n + 1) (by omega) (inv n).1 e
    rw [← hx] at key
    have k1 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ G xl e - G (sq n) e := by
      have h3 : (PowerSeries.X : PowerSeries k) ^ (n + 1) ∣ (PowerSeries.X : PowerSeries k) ^ (n + 1 + 1) :=
        pow_dvd_pow _ (by omega)
      have := dvd_add (h3.trans key) (dvd_mul_right ((PowerSeries.X : PowerSeries k) ^ (n + 1))
        (PowerSeries.C (L (fun i => PowerSeries.constantCoeff (d i)) e)))
      simpa using this
    have := dvd_add k1 ((inv n).2 e)
    simpa using this
  refine ⟨xl, fun i => ?_, fun e => ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [xl, PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (inv 0).1 i
  · ext j
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.mp (hlim j e) j (by omega)

theorem newton_powerSeries_target : ∀ (k ι κ : Type) [Field k] [Fintype ι] [Fintype κ] (G : (ι → PowerSeries k) → κ → PowerSeries k) (x₀ : ι → k) (L : (ι → k) →ₗ[k] (κ → k)), Function.Surjective L →
 (∀ e, PowerSeries.constantCoeff (G (fun i => PowerSeries.C (x₀ i)) e) = 0) →
 (∀ (x h : ι → PowerSeries k) (m : ℕ), 1 ≤ m → (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) → ∀ e,
   (PowerSeries.X : PowerSeries k) ^ (m + 1) ∣ G (fun i => x i + PowerSeries.X ^ m * h i) e - G x e - PowerSeries.X ^ m * PowerSeries.C (L (fun i => PowerSeries.constantCoeff (h i)) e)) →
 ∃ x : ι → PowerSeries k, (∀ i, PowerSeries.constantCoeff (x i) = x₀ i) ∧ ∀ e, G x e = 0 :=
  fun k ι κ _ _ _ G x₀ L hL h0 hG => newton_powerSeries_of_surjective_linearisation k ι κ G x₀ L hL h0 hG

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAlgebraMapLeOne
section
namespace GlobalTheory.IntegralAlgebraMapNormBound

open Polynomial

lemma norm_algebraMap_le_one {l : ℕ} [Fact (Nat.Prime l)] (c : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) c‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  have h1 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] c)‖
      = ‖algebraMap ℤ_[l] ℚ_[l] c‖ := PadicAlgCl.norm_extends l _
  rw [h1]
  exact PadicInt.norm_le_one c

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨p, hmon, hp⟩ := hx
  set n := p.natDegree with hn
  have hx0 : 0 < ‖x‖ := lt_trans one_pos hlt
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, ← hn] at hp
  have hlead : p.coeff n = 1 := hmon
  rw [hlead, map_one, one_mul] at hp
  have heq : x ^ n = -∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hp
  have hbound : ‖∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i) * x ^ i‖
      ≤ ‖x‖ ^ n / ‖x‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [Finset.mem_range] at hi
    rw [norm_mul, norm_pow, le_div_iff₀ hx0]
    calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ * ‖x‖ ^ i * ‖x‖
        ≤ 1 * ‖x‖ ^ i * ‖x‖ := by
          gcongr
          exact norm_algebraMap_le_one _
      _ = ‖x‖ ^ (i + 1) := by ring
      _ ≤ ‖x‖ ^ n := pow_le_pow_right₀ hlt.le (by omega)
  have hxn : ‖x‖ ^ n ≤ ‖x‖ ^ n / ‖x‖ := by
    calc ‖x‖ ^ n = ‖x ^ n‖ := (norm_pow x n).symm
      _ = _ := by rw [heq, norm_neg]
      _ ≤ _ := hbound
  have hpos : 0 < ‖x‖ ^ n := pow_pos hx0 n
  have : ‖x‖ ^ n / ‖x‖ < ‖x‖ ^ n := div_lt_self hpos hlt
  linarith

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l),
    IsIntegral ℤ_[l] x → ‖x‖ ≤ (1 : ℝ) :=
  fun x hx => norm_le_one_of_isIntegral x hx

end GlobalTheory.IntegralAlgebraMapNormBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAlgebraMapLeOneBis
section
namespace GlobalTheory.AlgebraMapNormLeOne

open Polynomial

theorem norm_algebraMap_le_one (l : ℕ) [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  calc ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖
      = ‖algebraMap ℚ_[l] (PadicAlgCl l) (algebraMap ℤ_[l] ℚ_[l] a)‖ := by
        rw [← IsScalarTower.algebraMap_apply]
    _ = ‖algebraMap ℤ_[l] ℚ_[l] a‖ := PadicAlgCl.norm_extends l _
    _ ≤ 1 := PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral (l : ℕ) [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  let v : Valuation (PadicAlgCl l) NNReal := Valued.v
  have hle : ∀ y : PadicAlgCl l, v y ≤ 1 ↔ ‖y‖ ≤ 1 := by
    intro y
    rw [← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  let f : ℤ_[l] →+* v.integer := (algebraMap ℤ_[l] (PadicAlgCl l)).codRestrict v.integer
    fun a => (hle _).mpr (norm_algebraMap_le_one l a)
  let _ : Algebra ℤ_[l] v.integer := f.toAlgebra
  have : IsScalarTower ℤ_[l] v.integer (PadicAlgCl l) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxO : IsIntegral v.integer x := hx.tower_top
  exact (hle x).mp ((Valuation.Integers.isIntegral_iff_v_le_one (Valuation.integer.integers v)).mp hxO)

end GlobalTheory.AlgebraMapNormLeOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAlgebraMapPadicIntLeOne
section
namespace GlobalTheory.PadicIntegralNormLeOne

open Polynomial

theorem norm_algebraMap_padicInt_le_one {l : ℕ} [Fact (Nat.Prime l)] (a : ℤ_[l]) :
    ‖algebraMap ℤ_[l] (PadicAlgCl l) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l),
    PadicAlgCl.norm_extends]
  exact PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral {l : ℕ} [Fact (Nat.Prime l)] (x : PadicAlgCl l)
    (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ (1 : ℝ) := by
  obtain ⟨f, hmon, hf⟩ := hx
  by_contra h
  push_neg at h
  have hsum := hf
  rw [eval₂_eq_sum_range, Finset.sum_range_succ, Polynomial.coeff_natDegree, hmon.leadingCoeff,
    map_one, one_mul] at hsum
  set n := f.natDegree
  set S := ∑ i ∈ Finset.range n, algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i) * x ^ i
  have hxn : x ^ n = -S := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have : S = 0 := by simp [S, hn]
    rw [this, hn, pow_zero, neg_zero] at hxn
    exact one_ne_zero hxn
  · have hx1 : (1 : ℝ) ≤ ‖x‖ := h.le
    have hS : ‖S‖ ≤ ‖x‖ ^ (n - 1) := by
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
      intro i hi
      rw [Finset.mem_range] at hi
      rw [norm_mul, norm_pow]
      calc ‖algebraMap ℤ_[l] (PadicAlgCl l) (f.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ i := by
            gcongr; exact norm_algebraMap_padicInt_le_one _
        _ = ‖x‖ ^ i := one_mul _
        _ ≤ ‖x‖ ^ (n - 1) := pow_le_pow_right₀ hx1 (by omega)
    have hlt : ‖x‖ ^ (n - 1) < ‖x‖ ^ n := pow_lt_pow_right₀ h (by omega)
    have : ‖x ^ n‖ = ‖S‖ := by rw [hxn, norm_neg]
    rw [norm_pow] at this
    linarith

end GlobalTheory.PadicIntegralNormLeOne

example : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (x : PadicAlgCl l), IsIntegral ℤ_[l] x → ‖x‖ ≤ (1 : ℝ) :=
  fun x hx => GlobalTheory.PadicIntegralNormLeOne.norm_le_one_of_isIntegral x hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOfMemSpan
section
namespace GlobalTheory.NormBoundOfSpan

theorem norm_le_of_mem_span {K E ι : Type} [NormedField K] [AddCommGroup E] [Module K E]
    (φ : ι → E →ₗ[K] K) :
    ∀ f ∈ Submodule.span K (Set.range φ), ∃ (C : ℝ), (0 : ℝ) ≤ C ∧ ∀ (p : E) (r : ℝ),
      (0 : ℝ) ≤ r → (∀ (j : ι), ‖(φ j : E → K) p‖ ≤ r) → ‖(f : E → K) p‖ ≤ C * r := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨1, zero_le_one, fun p r _ h => by simpa using h j⟩
  | zero => exact ⟨0, le_rfl, fun p r _ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨C, hC, h1⟩ := hx
    obtain ⟨D, hD, h2⟩ := hy
    refine ⟨C + D, add_nonneg hC hD, fun p r hr h => ?_⟩
    rw [LinearMap.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h1 p r hr h) (h2 p r hr h))
  | smul a x _ hx =>
    obtain ⟨C, hC, h1⟩ := hx
    refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg a) hC, fun p r hr h => ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h1 p r hr h) (norm_nonneg a)

end GlobalTheory.NormBoundOfSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PosDefExistsFrame
section
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem posDef_exists_frame :
    ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℂ), G.PosDef →
      ∃ X : Matrix (Fin d) (Fin d) ℂ, IsUnit X.det ∧ (X⁻¹)ᴴ * X⁻¹ = G := by
  intro d G hG
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg
  have hu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hBu : IsUnit B.det := by
    rw [hB, Matrix.det_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det B hBu, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv B hBu, hB, Matrix.star_eq_conjTranspose]

end GlobalTheory
end

