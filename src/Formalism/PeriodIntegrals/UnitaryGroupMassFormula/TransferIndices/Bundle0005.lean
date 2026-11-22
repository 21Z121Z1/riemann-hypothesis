import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.Bundle0004
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0021

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.BlockHyp
section
noncomputable section

namespace PI.Dv.TIW

open Formalism.BasicNotions NumberField IsDedekindDomain PI.Dv

section Cut

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_smul_mem (M : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ M :=
  _root_.UpperTheory.Reformulated.B.ExistsSmulMemTer.exists_smul_mem M x hx

theorem cut_span (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) (X : Submodule K V) :
    Submodule.span K ((M ⊓ X.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = X := by
  apply le_antisymm
  · rw [Submodule.span_le]; intro x hx; exact hx.2
  · intro x hx
    obtain ⟨a, ha, hax⟩ := exists_smul_mem M x (by rw [hM]; exact Submodule.mem_top)
    have haK : algebraMap (𝓞 K) K a ≠ 0 := by simpa using ha
    have hmem : a • x ∈ (M ⊓ X.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) := by
      refine Submodule.mem_inf.mpr ⟨hax, ?_⟩
      rw [Submodule.restrictScalars_mem, ← algebraMap_smul K]
      exact X.smul_mem _ hx
    have : x = (algebraMap (𝓞 K) K a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul K a x, smul_smul, inv_mul_cancel₀ haK, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem rk_cut (M : Submodule (𝓞 K) V) (hM : Submodule.span K (M : Set V) = ⊤) (X : Submodule K V) :
    Formalism.HN.rkK (M ⊓ X.restrictScalars (𝓞 K)) = Module.finrank K X := by
  rw [Formalism.HN.rkK, cut_span M hM X]

theorem fg_cut (M : Submodule (𝓞 K) V) (hM : M.FG) (X : Submodule K V) : (M ⊓ X.restrictScalars (𝓞 K)).FG :=
  Submodule.FG.of_le hM inf_le_left

end Cut

section Block

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {n : ℕ}

def Φt (Φ : Fin n → V →ₗ[K] V) : (Fin n → V) →ₗ[K] V := ∑ i, Φ i ∘ₗ LinearMap.proj i

theorem Φt_apply (Φ : Fin n → V →ₗ[K] V) (x : Fin n → V) : Φt Φ x = ∑ i, Φ i (x i) := by
  simp [Φt, LinearMap.sum_apply]

theorem Ψt_apply (Ψ : Fin n → V →ₗ[K] V) (y : V) (j : Fin n) : (LinearMap.pi Ψ) y j = Ψ j y := rfl

structure BlockHyp (X Y : Submodule K V) (Φ Ψ : Fin n → V →ₗ[K] V) (Γ : Matrix (Fin n) (Fin n) K) : Prop where
  det : Γ.det ≠ 0
  h1 : ∀ i j, ∀ x ∈ X, Ψ j (Φ i x) = Γ j i • x
  h2 : ∀ i, ∀ x ∈ X, Φ i x ∈ Y
  h3 : ∀ j, ∀ y ∈ Y, Ψ j y ∈ X
  h4 : ∀ y ∈ Y, ∃ x : Fin n → V, (∀ i, x i ∈ X) ∧ y = ∑ i, Φ i (x i)

variable {X Y : Submodule K V} {Φ Ψ : Fin n → V →ₗ[K] V} {Γ : Matrix (Fin n) (Fin n) K}

theorem BlockHyp.psiPhi (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X) :
    LinearMap.pi Ψ (Φt Φ x) = matV Γ x := by
  funext j
  rw [Ψt_apply, Φt_apply, map_sum, matV_apply]
  exact Finset.sum_congr rfl fun i _ => H.h1 i j (x i) (hx i (Set.mem_univ i))

theorem BlockHyp.phi_mem (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X) :
    Φt Φ x ∈ Y := by
  rw [Φt_apply]
  exact Y.sum_mem fun i _ => H.h2 i _ (hx i (Set.mem_univ i))

theorem BlockHyp.psi_mem (H : BlockHyp X Y Φ Ψ Γ) (y : V) (hy : y ∈ Y) :
    LinearMap.pi Ψ y ∈ Submodule.pi Set.univ fun _ : Fin n => X :=
  fun j _ => H.h3 j y hy

theorem BlockHyp.phi_inj (H : BlockHyp X Y Φ Ψ Γ) (x : Fin n → V) (hx : x ∈ Submodule.pi Set.univ fun _ => X)
    (h0 : Φt Φ x = 0) : x = 0 := by
  have := H.psiPhi x hx
  rw [h0, map_zero] at this
  rw [← matV_inv_cancel' Γ H.det x, ← this, map_zero]

theorem BlockHyp.psi_inj (H : BlockHyp X Y Φ Ψ Γ) (y : V) (hy : y ∈ Y) (h0 : LinearMap.pi Ψ y = 0) : y = 0 := by
  obtain ⟨x, hx, rfl⟩ := H.h4 y hy
  have hx' : x ∈ Submodule.pi Set.univ fun _ : Fin n => X := fun i _ => hx i
  have := H.psiPhi x hx'
  rw [Φt_apply] at this
  rw [h0] at this
  have hx0 : x = 0 := by rw [← matV_inv_cancel' Γ H.det x, ← this, map_zero]
  simp [hx0]

theorem BlockHyp.map_phi (H : BlockHyp X Y Φ Ψ Γ) :
    (Submodule.pi Set.univ fun _ : Fin n => X).map (Φt Φ) = Y := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact H.phi_mem x hx
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := H.h4 y hy
    exact ⟨x, fun i _ => hx i, by rw [Φt_apply]⟩

theorem BlockHyp.map_psi (H : BlockHyp X Y Φ Ψ Γ) :
    Y.map (LinearMap.pi Ψ) = Submodule.pi Set.univ fun _ : Fin n => X := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩; exact H.psi_mem y hy
  · intro x hx
    have hx' : matV Γ⁻¹ x ∈ Submodule.pi Set.univ fun _ : Fin n => X := by
      intro k _
      rw [matV_apply]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hx l (Set.mem_univ l))
    refine ⟨Φt Φ (matV Γ⁻¹ x), H.phi_mem _ hx', ?_⟩
    rw [H.psiPhi _ hx', matV_inv_cancel Γ H.det]

theorem BlockHyp.finrank [FiniteDimensional K V] (H : BlockHyp X Y Φ Ψ Γ) : Module.finrank K Y = n * Module.finrank K X := by
  let f : (Fin n → X) →ₗ[K] Y := LinearMap.codRestrict Y
    (Φt Φ ∘ₗ LinearMap.pi (fun i => X.subtype ∘ₗ LinearMap.proj i))
    (fun x => H.phi_mem _ (fun i _ => (x i).2))
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      simp only [f, LinearMap.codRestrict_apply, LinearMap.comp_apply] at h
      rw [← sub_eq_zero, ← map_sub] at h
      have := H.phi_inj _ (Submodule.sub_mem _ (fun i _ => (x i).2) (fun i _ => (y i).2)) h
      funext i
      apply Subtype.ext
      have := congrFun this i
      simpa [sub_eq_zero] using this
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := H.h4 y hy
      refine ⟨fun i => ⟨x i, hx i⟩, ?_⟩
      apply Subtype.ext
      simp [f, Φt_apply]
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_pi_fintype]
  simp

end Block

end PI.Dv.TIW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.GroupDataExists
section
noncomputable section

namespace PI.Dv.TIW

open PI.Dv NumberField

section Bound

variable {K : Type} [Field K] [NumberField K] {G : Type} [Group G] [Fintype G]

theorem norm_chiT_le (P : Pair K G) (x : G) (σ : K →+* ℂ) : ‖σ (chiT P x)‖ ≤ 1 := by
  by_cases hx : x ∈ P.H
  · rw [chiT_of_mem P x hx]
    have h := chi_inv_pow P ⟨x, hx⟩
    have h2 : (σ (((P.chi ⟨x, hx⟩)⁻¹ : Kˣ) : K)) ^ (Nat.card P.H) = 1 := by rw [← map_pow, h, map_one]
    exact (Complex.norm_eq_one_of_pow_eq_one h2 (card_H_pos P).ne').le
  · rw [chiT_of_not_mem P x hx, map_zero, norm_zero]; exact zero_le_one

theorem prod_expand (c c' : G → K) (g' g : G) :
    (∑ x : G, c x • MonoidAlgebra.of K G x) * MonoidAlgebra.of K G g' *
        ((∑ y : G, c' y • MonoidAlgebra.of K G y) * MonoidAlgebra.of K G g) =
      ∑ x : G, ∑ y : G, (c x * c' y) • MonoidAlgebra.of K G (x * g' * (y * g)) := by
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hof : MonoidAlgebra.of K G x * MonoidAlgebra.of K G g' * (MonoidAlgebra.of K G y * MonoidAlgebra.of K G g) =
      MonoidAlgebra.of K G (x * g' * (y * g)) := by simp only [map_mul]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hof, mul_comm (c' y) (c x)]

theorem entry_bound (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (g' g : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
      (epsS P0 * MonoidAlgebra.of K G g' * (epsS P * MonoidAlgebra.of K G g))))‖ ≤
      ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
  have hd : (Module.finrank K (T.W s) : ℝ) ≤ (Fintype.card G : ℝ) := by
    exact_mod_cast finrank_le_card (T.tau s) (T.irr s)
  rw [epsS, epsS, prod_expand, map_sum, map_sum, map_sum]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ x y : G, ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
      ((chiT P0 x * chiT P y) • MonoidAlgebra.of K G (x * g' * (y * g)))))‖ ≤ (Fintype.card G : ℝ) := by
    intro x y
    rw [map_smul, map_smul, Representation.asAlgebraHom_of, smul_eq_mul, map_mul, map_mul, norm_mul, norm_mul]
    have h1 := norm_chiT_le P0 x σ
    have h2 := norm_chiT_le P y σ
    have h3 := norm_trace_tau_le (T.tau s) (x * g' * (y * g)) σ
    calc ‖σ (chiT P0 x)‖ * ‖σ (chiT P y)‖ * ‖σ (LinearMap.trace K (T.W s) ((T.tau s) (x * g' * (y * g))))‖
        ≤ 1 * 1 * (Module.finrank K (T.W s) : ℝ) := by
          gcongr
      _ ≤ _ := by rw [one_mul, one_mul]; exact hd
  calc ∑ x : G, ‖σ (LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom
        (∑ y : G, (chiT P0 x * chiT P y) • MonoidAlgebra.of K G (x * g' * (y * g)))))‖
      ≤ ∑ x : G, ∑ y : G, (Fintype.card G : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [map_sum, map_sum, map_sum]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ => hterm x y)
    _ = ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end Bound

theorem group_data_exists : GrpData := by
  intro K _ _ G _ _ T P0 P hM1
  refine ⟨eS_mul_eS T, fun s z => eS_central T s z, eps_idem P, fun s => intEl_of_intR _ (intR_card_eS T s),
    fun s => ?_⟩
  obtain ⟨g, g', Γ, hΓ, hdet, b', hb'1, hb'2⟩ := perS T P0 P hM1 s
  refine ⟨fun k => epsS P * MonoidAlgebra.of K G (g k), fun j => epsS P0 * MonoidAlgebra.of K G (g' j), Γ, hdet,
    ?_, fun i => intEl_of_intR _ (intR_mul (intR_epsS P) (intR_of _)),
    fun j => intEl_of_intR _ (intR_mul (intR_epsS P0) (intR_of _)), ?_,
    fun i => (absorb_eps T s P P0 _).symm, fun j => (absorb_eps T s P0 P _).symm, b', hb'1, hb'2⟩
  ·
    intro σ
    set ΓK := Γ.map (algebraMap (𝓞 K) K) with hΓK
    have hdetK : algebraMap (𝓞 K) K Γ.det = ΓK.det := RingHom.map_det _ _
    have hentry : ∀ j k, (InfinitePlace.mk σ).1 (ΓK j k) ≤ ((Fintype.card G : ℕ) : ℝ) ^ 3 := by
      intro j k
      show ‖σ (ΓK j k)‖ ≤ _
      rw [hΓK, Matrix.map_apply, hΓ j k]
      exact entry_bound T s P0 P (g' j) (g k) σ
    have hdl := Matrix.det_le hentry
    rw [Fintype.card_fin] at hdl
    rw [hdetK]
    refine (show ‖σ ΓK.det‖ ≤ _ from hdl).trans ?_
    have hnG : nS T P s ≤ Fintype.card G :=
      (Submodule.finrank_le _).trans (finrank_le_card (T.tau s) (T.irr s))
    have hN : ((nS T P s).factorial * (Fintype.card G ^ 3) ^ (nS T P s) : ℕ) ≤
        Fintype.card G ^ (4 * nS T P s) := by
      calc (nS T P s).factorial * (Fintype.card G ^ 3) ^ (nS T P s)
          ≤ (nS T P s) ^ (nS T P s) * (Fintype.card G ^ 3) ^ (nS T P s) :=
            Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
        _ ≤ (Fintype.card G) ^ (nS T P s) * (Fintype.card G ^ 3) ^ (nS T P s) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hnG _)
        _ = Fintype.card G ^ (4 * nS T P s) := by ring
    rw [nsmul_eq_mul]
    exact_mod_cast hN
  ·
    intro i j
    have hmul : epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * eps P0 =
        epsS P0 * (MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i))) * eps P0 := by
      simp only [mul_assoc]
    have hτ : (T.tau s).asAlgebraHom
        (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * eps P0) =
        (T.tau s).asAlgebraHom (algebraMap (𝓞 K) K (Γ j i) • eps P0) := by
      rw [hmul, sandwich (T.tau s) P0 (hM1 s), map_smul, ← mul_assoc, ← hΓ j i]
    calc epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * (eps P0 * eS T s)
        = (epsS P0 * MonoidAlgebra.of K G (g' j) * (epsS P * MonoidAlgebra.of K G (g i)) * eps P0) * eS T s := by
          simp only [mul_assoc]
      _ = (algebraMap (𝓞 K) K (Γ j i) • eps P0) * eS T s := mul_eS_eq T s _ _ hτ
      _ = algebraMap (𝓞 K) K (Γ j i) • (eps P0 * eS T s) := smul_mul_assoc _ _ _

end PI.Dv.TIW
end
end

