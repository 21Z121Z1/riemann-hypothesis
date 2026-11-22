import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaBaseChange
section
open scoped TensorProduct
open Function

namespace GlobalTheory
open TensorProduct MulOpposite

variable (A S Λ : Type) [CommRing A] [CommRing S] [Algebra A S] [Ring Λ] [Algebra A Λ]

noncomputable def endBaseChangeMap :
    S ⊗[A] Module.End A Λ →ₗ[S] Module.End S (S ⊗[A] Λ) :=
  (LinearMap.baseChangeHom A S Λ Λ).liftBaseChange S

lemma endBaseChangeMap_tmul (s : S) (f : Module.End A Λ) :
    endBaseChangeMap A S Λ (s ⊗ₜ f) = s • f.baseChange S := by
  simp [endBaseChangeMap]

lemma endBaseChangeMap_bijective [Module.Free A Λ] [Module.Finite A Λ] :
    Bijective (endBaseChangeMap A S Λ) := by
  classical
  let ι := Module.Free.ChooseBasisIndex A Λ
  let b := Module.Free.chooseBasis A Λ
  let bS := Algebra.TensorProduct.basis S b
  let e₁ : S ⊗[A] Module.End A Λ ≃ₗ[S] S ⊗[A] Matrix ι ι A :=
    (LinearMap.toMatrix b b).baseChange A S _ _
  let e₂ := (matrixEquivTensor ι A S).symm
  let e₃ := LinearMap.toMatrix bS bS
  have h : ∀ x, e₃ (endBaseChangeMap A S Λ x) = e₂ (e₁ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s f =>
      simp [e₁, e₂, e₃, bS, endBaseChangeMap_tmul, matrixEquivTensor_apply_symm]
    | add x y hx hy => simp only [map_add, hx, hy]
  have : (endBaseChangeMap A S Λ : _ → _) = e₃.symm ∘ e₂ ∘ e₁ := by
    funext x; simp [← h x]
  rw [this]
  exact e₃.symm.bijective.comp (e₂.bijective.comp e₁.bijective)

noncomputable def opBaseChange : S ⊗[A] Λᵐᵒᵖ ≃ₗ[S] (S ⊗[A] Λ)ᵐᵒᵖ :=
  ((opLinearEquiv A (M := Λ)).symm.baseChange A S _ _).trans (opLinearEquiv S)

noncomputable def envBaseChange :
    S ⊗[A] (Λ ⊗[A] Λᵐᵒᵖ) ≃ₗ[S] (S ⊗[A] Λ) ⊗[S] (S ⊗[A] Λ)ᵐᵒᵖ :=
  (AlgebraTensorModule.distribBaseChange A S Λ Λᵐᵒᵖ).trans
    (TensorProduct.congr (LinearEquiv.refl S _) (opBaseChange A S Λ))

lemma mulLeftRight_envBaseChange (x : S ⊗[A] (Λ ⊗[A] Λᵐᵒᵖ)) :
    AlgHom.mulLeftRight S (S ⊗[A] Λ) (envBaseChange A S Λ x) =
      endBaseChangeMap A S Λ ((AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
    | tmul a b =>
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z w hz hw => simp only [map_add, hz, hw]
      | tmul t y =>
        simp [envBaseChange, opBaseChange, endBaseChangeMap_tmul,
          AlgebraTensorModule.distribBaseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          smul_tmul', mul_comm, mul_left_comm]

theorem isAzumaya_baseChange [IsAzumaya A Λ] [Module.Free A Λ] :
    IsAzumaya S (S ⊗[A] Λ) := by
  classical
  haveI : Module.Finite A Λ := inferInstance
  refine { toProjective := inferInstance, toFinite := inferInstance,
           toFaithfulSMul := ?_, bij := ?_ }
  · rcases subsingleton_or_nontrivial S with hS | hS
    · exact ⟨fun _ => Subsingleton.elim _ _⟩
    · haveI : Nontrivial A := (algebraMap A S).domain_nontrivial
      haveI : Nontrivial Λ := by
        by_contra hΛ
        rw [not_nontrivial_iff_subsingleton] at hΛ
        have : (0 : A) = 1 :=
          FaithfulSMul.eq_of_smul_eq_smul (α := Λ) fun _ => Subsingleton.elim _ _
        exact zero_ne_one this
      let b := Module.Free.chooseBasis A Λ
      let bS := Algebra.TensorProduct.basis S b
      obtain ⟨i⟩ := b.index_nonempty
      refine ⟨fun {s₁ s₂} h => ?_⟩
      have := congrArg (fun x => bS.repr x i) (h (bS i))
      simpa using this
  · have hφ : Bijective ((AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S) := by
      let e := LinearEquiv.ofBijective (AlgHom.mulLeftRight A Λ).toLinearMap IsAzumaya.bij
      have : (AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S = (e.lTensor S : _ →ₗ[A] _) := rfl
      rw [this]; exact (e.lTensor S).bijective
    have hc : (AlgHom.mulLeftRight S (S ⊗[A] Λ) : _ → _) =
        (endBaseChangeMap A S Λ ∘ (AlgHom.mulLeftRight A Λ).toLinearMap.lTensor S) ∘
          (envBaseChange A S Λ).symm := by
      funext y
      simp [← mulLeftRight_envBaseChange]
    rw [hc]
    exact ((endBaseChangeMap_bijective A S Λ).comp hφ).comp (envBaseChange A S Λ).symm.bijective

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BarGapParameterInequality
section
namespace GlobalTheory

theorem _root_.GlobalTheory.bar_gap_param_ineq : ∀ (T D c0 h0 N f m k PP : ℝ), 4 * D + 4 ≤ T → 4 * T ^ 2 ≤ h0 → PP * T * N * f ^ 2 * m ^ 2 * k * D ≤ h0 →
    4 * (c0 + 2 * N + T + D + 1) ≤ h0 → 0 ≤ c0 → c0 ≤ 22 * f ^ 2 * N ^ 4 → D = f * (N * (N - 1) / 2) → 40 ≤ PP →
    N + 4 ≤ 2 * k → 2 ≤ m → 6 ≤ N → 8 ≤ f →
    (T + c0) * (T + D + 1) + c0 + 2 * N - 2 ≤ h0 ∧ 2 * N + D ≤ T := by
  intro T D c0 h0 N f m k PP hTD hT2 hP h4 hc0 hc0u hD hPP hk hm hN hf
  have hNN : 5 * N ≤ N * (N - 1) := by nlinarith
  have hD1 : 4 * (N * (N - 1)) ≤ D := by
    rw [hD]; nlinarith [mul_nonneg (sub_nonneg.2 hf) (by nlinarith : (0:ℝ) ≤ N * (N - 1))]
  have hD0 : 0 ≤ D := by nlinarith
  have hgap : 2 * N + D ≤ T := by nlinarith
  refine ⟨?_, hgap⟩
  have hT0 : 0 ≤ T := by linarith
  have hm2 : 4 ≤ m ^ 2 := by nlinarith
  have hk0 : 0 ≤ k := by linarith
  have hA : 160 ≤ PP * m ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.2 hPP) (sq_nonneg m)]
  have hB : 80 * N ≤ PP * m ^ 2 * k := by
    nlinarith [mul_nonneg (sub_nonneg.2 hA) hk0]
  have hC : 320 * (N ^ 2 * (N - 1)) ≤ PP * m ^ 2 * k * D := by
    nlinarith [mul_nonneg (sub_nonneg.2 hB) hD0, mul_nonneg (by linarith : (0:ℝ) ≤ 80 * N) (sub_nonneg.2 hD1)]
  have hE : 264 * N ^ 3 ≤ PP * m ^ 2 * k * D := by
    nlinarith [mul_nonneg (sq_nonneg N) (by linarith : (0:ℝ) ≤ 56 * N - 320)]
  have hX : 0 ≤ T * N * f ^ 2 := by
    have : 0 ≤ N := by linarith
    positivity
  have hF : 264 * N ^ 3 * (T * N * f ^ 2) ≤ PP * T * N * f ^ 2 * m ^ 2 * k * D := by
    have := mul_le_mul_of_nonneg_right hE hX
    calc 264 * N ^ 3 * (T * N * f ^ 2) ≤ PP * m ^ 2 * k * D * (T * N * f ^ 2) := this
      _ = PP * T * N * f ^ 2 * m ^ 2 * k * D := by ring
  have hcT : 12 * (c0 * T) ≤ h0 := by
    have h1 : c0 * T ≤ 22 * f ^ 2 * N ^ 4 * T := mul_le_mul_of_nonneg_right hc0u hT0
    nlinarith
  have hcD : c0 * (4 * (D + 1)) ≤ c0 * T := mul_le_mul_of_nonneg_left (by linarith) hc0
  have hTT : T * (4 * (D + 1)) ≤ T * T := mul_le_mul_of_nonneg_left (by linarith) hT0
  have hexp : (T + c0) * (T + D + 1) + c0 + 2 * N - 2
      = T ^ 2 + T * (D + 1) + c0 * T + c0 * (D + 1) + c0 + 2 * N - 2 := by ring
  rw [hexp]
  nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTensorModuleCompat
section
open TensorProduct

namespace GlobalTheory

set_option maxHeartbeats 1000000 in

theorem baseChange_tensor_int_field_equiv :
    ∀ (K L O : Type) [Field K] [Field L] [Algebra K L] [CommRing O] (M : Type) [AddCommGroup M]
    [Module K M] [Module O M] [SMulCommClass K O M] (N : Type) [AddCommGroup N] [Module L N] [Module O N]
    [SMulCommClass L O N] (e : L ⊗[K] M ≃ₗ[L] N), (∀ (a : O) (m : M), e (1 ⊗ₜ (a • m)) = a • e (1 ⊗ₜ m)) →
    letI : Module (K ⊗[ℤ] O) M := TensorProduct.Algebra.module
    letI : Module (L ⊗[ℤ] O) N := TensorProduct.Algebra.module
    ∃ _ : Algebra (K ⊗[ℤ] O) (L ⊗[ℤ] O), Module.FaithfullyFlat (K ⊗[ℤ] O) (L ⊗[ℤ] O) ∧
      Nonempty ((L ⊗[ℤ] O) ⊗[K ⊗[ℤ] O] M ≃ₗ[L ⊗[ℤ] O] N) := by
  intro R R' O _ _ _ _ M _ _ _ _ N _ _ _ _ e he
  letI : Module (R ⊗[ℤ] O) M := TensorProduct.Algebra.module
  letI : Module (R' ⊗[ℤ] O) N := TensorProduct.Algebra.module
  let f : R ⊗[ℤ] O →ₐ[ℤ] R' ⊗[ℤ] O :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom ℤ R R') (AlgHom.id ℤ O)
  letI : Algebra (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := f.toRingHom.toAlgebra
  letI : Module (R ⊗[ℤ] O) N := Module.compHom N f.toRingHom
  haveI : IsScalarTower (R ⊗[ℤ] O) (R' ⊗[ℤ] O) N := ⟨fun a x n => mul_smul (f a) x n⟩
  have hf : ∀ (r : R) (o : O), f (r ⊗ₜ o) = algebraMap R R' r ⊗ₜ o := fun r o => rfl

  haveI : Module.FaithfullyFlat R R' := inferInstance
  haveI : IsScalarTower R (R ⊗[ℤ] O) (R' ⊗[ℤ] O) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  let l : R' →ₗ[R] R' ⊗[ℤ] O :=
    { toFun := fun r' => r' ⊗ₜ 1
      map_add' := fun x y => add_tmul x y 1
      map_smul' := fun r r' => rfl }
  let u : (R ⊗[ℤ] O) ⊗[R] R' →ₗ[R ⊗[ℤ] O] R' ⊗[ℤ] O := LinearMap.liftBaseChange _ l
  have hu : ∀ (r : R) (o : O) (r' : R'), u ((r ⊗ₜ o) ⊗ₜ r') = (algebraMap R R' r * r') ⊗ₜ o := by
    intro r o r'
    change f (r ⊗ₜ o) * (r' ⊗ₜ 1) = _
    rw [hf, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  let w : R' →ₗ[ℤ] O →ₗ[ℤ] (R ⊗[ℤ] O) ⊗[R] R' :=
    LinearMap.mk₂ ℤ (fun r' o => ((1 : R) ⊗ₜ[ℤ] o) ⊗ₜ[R] r')
      (fun x y o => by simp [tmul_add])
      (fun n x o => map_zsmul (TensorProduct.mk R (R ⊗[ℤ] O) R' ((1 : R) ⊗ₜ[ℤ] o)) n x)
      (fun x o o' => by simp [tmul_add, add_tmul])
      (fun n x o => by
        change (TensorProduct.mk R (R ⊗[ℤ] O) R').flip x (TensorProduct.mk ℤ R O 1 (n • o)) =
          n • (TensorProduct.mk R (R ⊗[ℤ] O) R').flip x (TensorProduct.mk ℤ R O 1 o)
        rw [map_zsmul, map_zsmul])
  let v : R' ⊗[ℤ] O →ₗ[ℤ] (R ⊗[ℤ] O) ⊗[R] R' := TensorProduct.lift w
  have hv : ∀ (r' : R') (o : O), v (r' ⊗ₜ o) = ((1 : R) ⊗ₜ[ℤ] o) ⊗ₜ[R] r' := fun r' o => rfl
  have huv : ∀ y, u (v y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' o =>
      rw [hv, hu, map_one, _root_.one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hvu : ∀ x, v (u x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a r' =>
      induction a using TensorProduct.induction_on with
      | zero => simp
      | tmul r o =>
        rw [hu, ← Algebra.smul_def, hv, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul,
          _root_.mul_one]
      | add a b ha hb => rw [add_tmul, map_add, map_add, ha, hb]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hubij : Function.Bijective u :=
    ⟨fun a b hab => by rw [← hvu a, ← hvu b, hab], fun y => ⟨v y, huv y⟩⟩
  have hFF : Module.FaithfullyFlat (R ⊗[ℤ] O) (R' ⊗[ℤ] O) :=
    Module.FaithfullyFlat.of_linearEquiv (R ⊗[ℤ] O) ((R ⊗[ℤ] O) ⊗[R] R')
      (LinearEquiv.ofBijective u hubij).symm

  have hj : ∀ (a : R ⊗[ℤ] O) (m : M), e (1 ⊗ₜ (a • m)) = f a • e (1 ⊗ₜ m) := by
    intro a m
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r o =>
      rw [hf, TensorProduct.Algebra.smul_def, TensorProduct.Algebra.smul_def, ← he,
        TensorProduct.tmul_smul, ← algebraMap_smul R', map_smul]
    | add a b ha hb => rw [add_smul, tmul_add, map_add, ha, hb, map_add, add_smul]
  let j : M →ₗ[R ⊗[ℤ] O] N :=
    { toFun := fun m => e (1 ⊗ₜ m)
      map_add' := fun x y => by simp [tmul_add]
      map_smul' := fun a m => hj a m }
  let Φ : (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M →ₗ[R' ⊗[ℤ] O] N := LinearMap.liftBaseChange _ j
  let g : R' →+ M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M :=
    AddMonoidHom.mk' (fun r' => (TensorProduct.mk (R ⊗[ℤ] O) (R' ⊗[ℤ] O) M
      (r' ⊗ₜ[ℤ] (1 : O))).toAddMonoidHom) (by intro a b; ext m; simp [add_tmul])
  let ψ : R' ⊗[R] M →+ (R' ⊗[ℤ] O) ⊗[R ⊗[ℤ] O] M := TensorProduct.liftAddHom g (by
    intro r r' m
    have hr : r • m = ((r ⊗ₜ[ℤ] (1 : O)) : R ⊗[ℤ] O) • m := by
      rw [TensorProduct.Algebra.smul_def, one_smul]
    simp only [g, AddMonoidHom.mk'_apply, LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
    rw [hr, ← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    change _ = f (r ⊗ₜ 1) * _
    simp only [hf, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, Algebra.smul_def])
  have h1 : ∀ y, Φ (ψ y) = e y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r' m =>
      simp only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply,
        LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply, Φ, LinearMap.liftBaseChange_tmul]
      change (r' ⊗ₜ[ℤ] (1 : O)) • e (1 ⊗ₜ m) = _
      rw [TensorProduct.Algebra.smul_def, one_smul, ← map_smul, TensorProduct.smul_tmul',
        smul_eq_mul, _root_.mul_one]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have h2 : ∀ z, ψ (e.symm (Φ z)) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x m =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r' o =>
        have hΦ : Φ ((r' ⊗ₜ[ℤ] o) ⊗ₜ m) = e (r' ⊗ₜ (o • m)) := by
          simp only [Φ, LinearMap.liftBaseChange_tmul]
          change (r' ⊗ₜ[ℤ] o) • e (1 ⊗ₜ m) = _
          rw [TensorProduct.Algebra.smul_def, ← he, ← map_smul, TensorProduct.smul_tmul',
            smul_eq_mul, _root_.mul_one]
        rw [hΦ, LinearEquiv.symm_apply_apply]
        simp only [ψ, TensorProduct.liftAddHom_tmul, g, AddMonoidHom.mk'_apply,
          LinearMap.toAddMonoidHom_coe, TensorProduct.mk_apply]
        have ho : o • m = (((1 : R) ⊗ₜ[ℤ] o) : R ⊗[ℤ] O) • m := by
          rw [TensorProduct.Algebra.smul_def, one_smul]
        rw [ho, ← TensorProduct.smul_tmul, Algebra.smul_def]
        congr 1
        change f (1 ⊗ₜ o) * _ = _
        rw [hf, map_one, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
      | add x y hx hy => rw [add_tmul, map_add, map_add, map_add, hx, hy]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hinj : Function.Injective Φ := fun a b hab => by rw [← h2 a, ← h2 b, hab]
  have hsurj : Function.Surjective Φ := fun n =>
    ⟨ψ (e.symm n), by rw [h1, LinearEquiv.apply_symm_apply]⟩
  exact ⟨f.toRingHom.toAlgebra, hFF, ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩⟩⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharDerivContDiff
section
open scoped ContDiff

namespace GlobalTheory

open intervalIntegral Filter Topology

theorem bichar_deriv_contDiff (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ)
    (hQ : Continuous (Function.uncurry Q))
    (hs : ∀ t s s', Q t (s + s') = Q t s * Q t s')
    (ht : ∀ t t' s, Q (t + t') s = Q t s * Q t' s)
    (h0 : ∀ t, Q t 0 = 1) :
    ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := by
  have hQt : ∀ t, Continuous (Q t) := fun t =>
    hQ.comp (continuous_const.prodMk continuous_id : Continuous fun s : ℝ => (t, s))
  set g : (Fin k → ℝ) → ℝ → ℂ := fun t δ => ∫ r in (0:ℝ)..δ, Q t r with hgdef
  have hg : ∀ t x, HasDerivAt (g t) (Q t x) x := fun t x =>
    ((hQt t).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hid : ∀ t s δ, Q t s * g t δ = g t (s + δ) - g t s := by
    intro t s δ
    have hint : ∀ a b : ℝ, IntervalIntegrable (Q t) MeasureTheory.volume a b :=
      fun a b => (hQt t).intervalIntegrable a b
    simp only [hgdef]
    rw [integral_interval_sub_left (hint _ _) (hint _ _)]
    have h1 : ∫ x in (0:ℝ)..δ, Q t (x + s) = ∫ x in s..s + δ, Q t x := by
      rw [intervalIntegral.integral_comp_add_right (fun x => Q t x) s]
      simp [add_comm]
    rw [← h1]
    simp_rw [hs, intervalIntegral.integral_mul_const]
    ring
  have hder : ∀ t δ, g t δ ≠ 0 → ∀ s,
      HasDerivAt (Q t) ((Q t (s + δ) - Q t s) / g t δ) s := by
    intro t δ hδ s
    have heq : Q t = fun u => (g t (u + δ) - g t u) / g t δ := by
      funext u; rw [← hid t u δ, mul_div_cancel_right₀ _ hδ]
    have ha : HasDerivAt (fun u => g t (u + δ)) (Q t (s + δ)) s :=
      HasDerivAt.comp_add_const s δ (hg t (s + δ))
    have h1 : HasDerivAt (fun u => (g t (u + δ) - g t u) / g t δ)
        ((Q t (s + δ) - Q t s) / g t δ) s := (ha.sub (hg t s)).div_const _
    rwa [← heq] at h1
  have hex : ∀ t, ∃ δ, g t δ ≠ 0 := by
    intro t
    have h := (hg t 0).eventually_ne (c := 0) (by rw [h0]; exact one_ne_zero)
    obtain ⟨z, hz⟩ := h.exists
    refine ⟨z, ?_⟩
    simpa [hgdef] using hz
  have hd : ∀ t, HasDerivAt (Q t) (deriv (Q t) 0) 0 := by
    intro t
    obtain ⟨δ, hδ⟩ := hex t
    exact (hder t δ hδ 0).differentiableAt.hasDerivAt
  have hadd : ∀ t t', deriv (Q (t + t')) 0 = deriv (Q t) 0 + deriv (Q t') 0 := by
    intro t t'
    have e : Q (t + t') = Q t * Q t' := funext fun s => by rw [Pi.mul_apply, ht]
    have hm := (hd t).mul (hd t')
    rw [← e] at hm
    rw [hm.deriv, h0, h0]; ring
  let c : (Fin k → ℝ) →+ ℂ := AddMonoidHom.mk' (fun t => deriv (Q t) 0) hadd
  have hQ0 : ∀ s, Q 0 s = 1 := by
    intro s
    have h1 : Q 0 s = Q 0 s * Q 0 s := by simpa using ht 0 0 s
    have h2 : Q 0 s * Q 0 (-s) = 1 := by rw [← hs, add_neg_cancel, h0]
    have hne : Q 0 s ≠ 0 := left_ne_zero_of_mul_eq_one h2
    have := mul_left_cancel₀ hne (h1.symm.trans (mul_one _).symm)
    exact this
  have hgc : Continuous fun t => g t 1 :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hQ 0 1
  have hg01 : g 0 1 = 1 := by simp [hgdef, hQ0]
  have hne : ∀ᶠ t in 𝓝 (0 : Fin k → ℝ), g t 1 ≠ 0 :=
    hgc.continuousAt.eventually_ne (by rw [hg01]; exact one_ne_zero)
  have hc0 : ContinuousAt c 0 := by
    have hQ1 : Continuous fun t => Q t 1 :=
      hQ.comp (continuous_id.prodMk continuous_const : Continuous fun t => (t, (1:ℝ)))
    have hf : ContinuousAt (fun t => (Q t 1 - 1) / g t 1) 0 :=
      ((hQ1.sub continuous_const).continuousAt).div hgc.continuousAt (by rw [hg01]; exact one_ne_zero)
    refine hf.congr ?_
    filter_upwards [hne] with t htne
    have := (hder t 1 htne 0).deriv
    simp only [zero_add, h0] at this
    simp [c, this]
  have hcc : Continuous c := continuous_of_continuousAt_zero c hc0
  have : (fun t => deriv (Q t) 0) = ⇑(c.toRealLinearMap hcc) := by
    funext t; simp [c]
  rw [this]
  exact (c.toRealLinearMap hcc).contDiff

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveIffIsUnitDet
section
noncomputable section
open scoped TensorProduct
open Module

namespace GlobalTheory.LocAzumaya

variable {A Λ : Type*} [CommRing A] [Ring Λ] [Algebra A Λ] {ι : Type*} [Fintype ι] [DecidableEq ι]

def structMat (b : Basis ι A Λ) : Matrix (ι × ι) (ι × ι) A :=
  LinearMap.toMatrix (b.tensorProduct b.mulOpposite) b.end (AlgHom.mulLeftRight A Λ).toLinearMap

theorem stdBasis_repr_apply' (M : Matrix ι ι A) (k l : ι) :
    (Matrix.stdBasis A ι ι).repr M (k, l) = M k l := rfl

theorem repr_equiv_apply {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    {κ : Type*} (b₁ : Basis κ A M) (b₂ : Basis κ A N) (x : M) :
    b₂.repr (b₁.equiv b₂ (Equiv.refl κ) x) = b₁.repr x := by
  simp [Basis.equiv]

theorem structMat_apply (b : Basis ι A Λ) (k l i j : ι) :
    structMat b (k, l) (i, j) = b.repr (b i * b l * b j) k := by
  rw [structMat, LinearMap.toMatrix_apply]
  simp [Basis.end_repr_apply, Basis.tensorProduct_apply, LinearMap.toMatrix_apply, stdBasis_repr_apply']

theorem bijective_iff_isUnit_det (b : Basis ι A Λ) :
    Function.Bijective (AlgHom.mulLeftRight A Λ) ↔ IsUnit (structMat b).det := by
  set c := b.tensorProduct b.mulOpposite
  set f := (AlgHom.mulLeftRight A Λ).toLinearMap
  haveI := Module.Free.of_basis c
  haveI := Module.Finite.of_basis c
  let e : Module.End A Λ ≃ₗ[A] Λ ⊗[A] Λᵐᵒᵖ := b.end.equiv c (Equiv.refl _)
  have hM : structMat b = LinearMap.toMatrix c c (e.toLinearMap ∘ₗ f) := by
    ext p q
    rw [structMat, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, repr_equiv_apply]
  rw [hM, LinearMap.det_toMatrix, ← LinearMap.isUnit_iff_isUnit_det, Module.End.isUnit_iff]
  constructor
  · intro h; exact e.bijective.comp h
  · intro h
    have := e.symm.bijective.comp h
    simpa [Function.comp_def, f] using this

end GlobalTheory.LocAzumaya
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveLinearCombinationOfRankAtStalk
section
namespace GlobalTheory

open Module in

theorem bijective_linearCombination_of_rankAtStalk :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (r : ℕ),
      (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) → ∀ s : Fin r → M,
      Module.support R (M ⧸ Submodule.span R (Set.range s)) = ∅ →
      Function.Bijective (Fintype.linearCombination R s) := by
  intro R M _ _ _ _ _ r hr s hs
  have hspan : Submodule.span R (Set.range s) = ⊤ := by
    have : Subsingleton (M ⧸ Submodule.span R (Set.range s)) := Module.support_eq_empty_iff.1 hs
    exact Submodule.Quotient.subsingleton_iff.1 this
  refine ⟨?_, ?_⟩
  · rw [← linearIndependent_iff_injective_fintypeLinearCombination]
    refine LinearIndependent.of_isLocalized_maximal (fun P _ => Localization.AtPrime P)
      (fun P _ => LocalizedModule P.primeCompl M) (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M)
      s fun P hP => ?_
    have hfree : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
      Module.free_of_flat_of_isLocalRing
    have hrk : Module.finrank (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = r :=
      hr ⟨P, hP.isPrime⟩
    have hsp : Submodule.span (Localization.AtPrime P)
        (Set.range (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) = ⊤ := by
      rw [Set.range_comp]
      exact span_eq_top_of_isLocalizedModule (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl M) hspan
    have hsurj : Function.Surjective (Fintype.linearCombination (Localization.AtPrime P)
        (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hsp]
    let b := Module.finBasisOfFinrankEq (Localization.AtPrime P) (LocalizedModule P.primeCompl M) hrk
    have hinj := OrzechProperty.injective_of_surjective_endomorphism
      (b.equivFun.toLinearMap ∘ₗ Fintype.linearCombination (Localization.AtPrime P)
        (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) (b.equivFun.surjective.comp hsurj)
    rw [linearIndependent_iff_injective_fintypeLinearCombination]
    exact Function.Injective.of_comp (f := ⇑b.equivFun) hinj
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardDvdSumOfInvariantOfCardStabilizerDvd
section
namespace GlobalTheory

theorem card_dvd_sum_of_invariant_of_card_stabilizer_dvd (G X : Type) [AddGroup G] [Finite G]
    [Fintype X] [AddAction G X] (h : X → ℤ) (hinv : ∀ (g : G) (x : X), h (g +ᵥ x) = h x)
    (hdvd : ∀ x, (Nat.card (AddAction.stabilizer G x) : ℤ) ∣ h x) :
    (Nat.card G : ℤ) ∣ ∑ x, h x := by
  classical
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun x : X => (Quotient.mk (AddAction.orbitRel G X) x)) (f := h)]
  refine Finset.dvd_sum fun q _ => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  have hconst : ∀ y ∈ Finset.univ.filter
      (fun y : X => Quotient.mk (AddAction.orbitRel G X) y = Quotient.mk (AddAction.orbitRel G X) x),
      h y = h x := by
    intro y hy
    have hy' := Quotient.exact (Finset.mem_filter.mp hy).2
    obtain ⟨g, rfl⟩ : y ∈ AddAction.orbit G x := AddAction.orbitRel_apply.mp hy'
    exact hinv g x
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter
      (fun y : X => Quotient.mk (AddAction.orbitRel G X) y
        = Quotient.mk (AddAction.orbitRel G X) x)).card = Nat.card (AddAction.orbit G x) := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Quotient.eq]
    exact AddAction.orbitRel_apply
  have hG : Nat.card G = Nat.card (AddAction.orbit G x) * Nat.card (AddAction.stabilizer G x) := by
    rw [Nat.card_congr (AddAction.orbitEquivQuotientStabilizer G x)]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  rw [hcard, hG, Nat.cast_mul]
  exact mul_dvd_mul_left _ (hdvd x)

end GlobalTheory
end

