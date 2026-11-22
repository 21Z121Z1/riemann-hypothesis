import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisAlt
section
namespace GlobalTheory.ProofStatement

theorem main : ∀ (l : ℕ) [hl : Fact (Nat.Prime l)] (a : AlgebraicClosure (ZMod l)), a ≠ (0 : AlgebraicClosure (ZMod l)) → ∃ (m : ℕ), (0 : ℕ) < m ∧ ¬l ∣ m ∧ a ^ m = (1 : AlgebraicClosure (ZMod l)) := by
  intro l hl a ha
  set K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l))) with hK
  haveI : FiniteDimensional (ZMod l) K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  haveI : Finite K := Module.finite_of_finite (ZMod l)
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K l := charP_of_injective_algebraMap (algebraMap (ZMod l) K).injective l
  obtain ⟨n, _, hcard⟩ := FiniteField.card K l
  have ha' : (⟨a, IntermediateField.mem_adjoin_simple_self (ZMod l) a⟩ : K) ≠ 0 := by
    intro h; apply ha; exact congrArg Subtype.val h
  have hpow := FiniteField.pow_card_sub_one_eq_one _ ha'
  have hl1 : 2 ≤ l := hl.out.two_le
  have hn : 1 ≤ (n : ℕ) := n.pos
  have hq : l ≤ l ^ (n : ℕ) := Nat.le_self_pow (by omega) l
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · rw [hcard]
    intro hd
    have h2 : l ∣ l ^ (n : ℕ) := dvd_pow_self l (by omega)
    have h3 : l ∣ l ^ (n : ℕ) - (l ^ (n : ℕ) - 1) := Nat.dvd_sub h2 hd
    rw [Nat.sub_sub_self (by omega)] at h3
    exact hl.out.one_lt.ne' (Nat.dvd_one.mp h3)
  · have := congrArg Subtype.val hpow
    simpa using this

end GlobalTheory.ProofStatement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisBis
section
namespace GlobalTheory.PowerMembershipInertiaEigenvalues

theorem pow_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (Q : Submodule k U) (hT : ∀ y ∈ Q, (T : U → U) y ∈ Q) (n : ℕ) :
    ∀ y ∈ Q, ((T ^ n : Module.End k U) : U → U) y ∈ Q := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hT y hy)

theorem main : ∀ {k U : Type} [inst : Field k] [inst_1 : AddCommGroup U] [inst_2 : Module k U] (T : Module.End k U) (Q : Submodule k U), (∀ y ∈ Q, (T : U → U) y ∈ Q) → ∀ (p : Polynomial k), ∀ y ∈ Q, ((Polynomial.aeval T : Polynomial k → Module.End k U) p : U → U) y ∈ Q := by
  intro k U _ _ _ T Q hT p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y hy
    simp only [map_add, LinearMap.add_apply]
    exact Q.add_mem (hp y hy) (hq y hy)
  | monomial n a =>
    intro y hy
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Q.smul_mem a (pow_mem T Q hT n y hy)

end GlobalTheory.PowerMembershipInertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisFurther
section
namespace GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues

open Module

theorem exists_common_eigenvector {k ι V : Type} [Field k] [IsAlgClosed k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (f : ι → Module.End k V)
    (hcomm : ∀ i j, f i * f j = f j * f i) :
    ∀ (d : ℕ) (W : Submodule k V), Module.finrank k W = d → W ≠ ⊥ →
      (∀ i, ∀ w ∈ W, (f i : V → V) w ∈ W) →
        ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ i, ∃ c : k, (f i : V → V) x = c • x := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro W hd hW hinv
  by_cases hs : ∀ i, ∃ c : k, ∀ w ∈ W, f i w = c • w
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    exact ⟨x, hx, hx0, fun i => let ⟨c, hc⟩ := hs i; ⟨c, hc x hx⟩⟩
  · push_neg at hs
    obtain ⟨i, hi⟩ := hs
    let g : Module.End k W := (f i).restrict (fun w hw => hinv i w hw)
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
    obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue g
    obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
    have hgv : g v = c • v := hv.apply_eq_smul
    have hv0 : v ≠ 0 := hv.2
    set W' : Submodule k V := W ⊓ Module.End.eigenspace (f i) c with hW'
    have hvW' : (v : V) ∈ W' := by
      refine ⟨v.2, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have := congrArg Subtype.val hgv
      simpa [g] using this
    have hW'ne : W' ≠ ⊥ := by
      intro h
      rw [h, Submodule.mem_bot] at hvW'
      exact hv0 (Subtype.ext hvW')
    have hlt : W' < W := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro h
      obtain ⟨w, hw, hne⟩ := hi c
      have : w ∈ W' := h ▸ hw
      exact hne ((Module.End.mem_eigenspace_iff).mp this.2)
    have hdlt : Module.finrank k W' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hlt
    have hinv' : ∀ j, ∀ w ∈ W', (f j : V → V) w ∈ W' := by
      intro j w hw
      refine ⟨hinv j w hw.1, ?_⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      have h1 : f i w = c • w := (Module.End.mem_eigenspace_iff).mp hw.2
      have h2 := congrArg (fun F : Module.End k V => F w) (hcomm i j)
      simp only [Module.End.mul_apply] at h2
      rw [h2, h1, map_smul]
    obtain ⟨x, hx, hx0, hxe⟩ := ih _ hdlt W' rfl hW'ne hinv'
    exact ⟨x, hx.1, hx0, hxe⟩

theorem target : ∀ {k ι V : Type} [inst : Field k] [IsAlgClosed k] [inst_2 : AddCommGroup V] [inst_3 : Module k V] [FiniteDimensional k V] (f : ι → Module.End k V), (∀ (i j : ι), f i * f j = f j * f i) → ∀ (d : ℕ) (W : Submodule k V), Module.finrank k ↥W = d → W ≠ ⊥ → (∀ (i : ι), ∀ w ∈ W, (f i : V → V) w ∈ W) → ∃ x ∈ W, x ≠ (0 : V) ∧ ∀ (i : ι), ∃ (c : k), (f i : V → V) x = c • x :=
  fun f hc => exists_common_eigenvector f hc

end GlobalTheory.CommonEigenvectorExistenceInertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsExtra
section
namespace GlobalTheory.SimpStatement

open Finset

theorem main {K B W G ι : Type} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [AddCommGroup W] [Module B W] [Module K W] [IsScalarTower K B W] [Module.IsTorsionFree B W]
    (a : G → B → B) (σ : G → W →+ W)
    (hσ : ∀ (g : G) (b : B) (w : W), (σ g : W → W) (b • w) = a g b • (σ g : W → W) w)
    (ha : ∀ (b b' : B), b ≠ (0 : B) → (∀ (g : G), b * a g b' = a g b * b') →
      ∃ (c : K), b' = (Algebra.algebraMap K B : K → B) c * b)
    (v : ι → W) (hv : ∀ (g : G) (i : ι), (σ g : W → W) (v i) = v i)
    (s : Finset ι) (hK : LinearIndepOn K v (↑s : Set ι)) :
    LinearIndepOn B v (↑s : Set ι) := by
  classical

  have key : ∀ T : Finset ι, T ⊆ s → ∀ f : ι → B, ∑ i ∈ T, f i • v i = 0 → ∀ i ∈ T, f i = 0 := by
    intro T
    induction T using Finset.strongInduction with
    | H T ih =>
      intro hTs f hf
      by_contra hne
      push_neg at hne
      obtain ⟨i₀, hi₀, hfi₀⟩ := hne

      have hrel : ∀ j ∈ T, ∀ g : G, f i₀ * a g (f j) = a g (f i₀) * f j := by
        intro j hj g
        set f' : ι → B := fun i => f i₀ * a g (f i) - a g (f i₀) * f i with hf'
        have hsum : ∑ i ∈ T, f' i • v i = 0 := by
          have h1 : ∑ i ∈ T, a g (f i) • v i = 0 := by
            have := congrArg (σ g : W → W) hf
            rw [map_sum, map_zero] at this
            rw [← this]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hσ, hv]
          simp only [hf', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, h1, hf,
            smul_zero, sub_zero]
        have hf'i₀ : f' i₀ = 0 := by simp only [hf']; ring
        have hsum' : ∑ i ∈ T.erase i₀, f' i • v i = 0 := by
          rw [← Finset.add_sum_erase T _ hi₀, hf'i₀, zero_smul, zero_add] at hsum
          exact hsum
        by_cases hj0 : j = i₀
        · subst hj0; ring
        · have := ih (T.erase i₀) (Finset.erase_ssubset hi₀)
            ((Finset.erase_subset _ _).trans hTs) f' hsum' j (Finset.mem_erase.2 ⟨hj0, hj⟩)
          simp only [hf'] at this
          exact sub_eq_zero.1 this
      have hc : ∀ j ∈ T, ∃ c : K, f j = (Algebra.algebraMap K B : K → B) c * f i₀ :=
        fun j hj => ha (f i₀) (f j) hfi₀ (hrel j hj)
      choose! c hc using hc
      have hsumK : ∑ i ∈ T, c i • v i = 0 := by
        have : f i₀ • ∑ i ∈ T, c i • v i = 0 := by
          rw [← hf, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hc i hi, mul_comm, mul_smul, smul_comm]
          rw [algebraMap_smul]
          exact smul_comm (c i) (f i₀) (v i)
        exact (smul_eq_zero_iff_right hfi₀).1 this
      have hKT : LinearIndepOn K v (↑T : Set ι) := hK.mono (by exact_mod_cast hTs)
      have hci₀ := (linearIndepOn_finset_iff.1 hKT) c hsumK i₀ hi₀
      apply hfi₀
      rw [hc i₀ hi₀, hci₀, map_zero, zero_mul]
  exact linearIndepOn_finset_iff.2 (key s subset_rfl)

end GlobalTheory.SimpStatement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsMore
section
namespace GlobalTheory.AbelianStatement

open Module

theorem main {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module (LaurentSeries k) V]
    [Module (PowerSeries k) V] [IsScalarTower (PowerSeries k) (LaurentSeries k) V]
    {W : Type} [AddCommGroup W] [Module (LaurentSeries k) W] [Module (PowerSeries k) W]
    [IsScalarTower (PowerSeries k) (LaurentSeries k) W]
    (f : W →ₗ[LaurentSeries k] V) {N : Submodule (PowerSeries k) V} (hN : N.FG) :
    ∃ (m : ℕ) (b : Fin m → V),
      LinearIndependent (LaurentSeries k)
        ((⇑(Submodule.mkQ (LinearMap.range f)) : V → V ⧸ LinearMap.range f) ∘ b) ∧
      ∀ y ∈ N, ∃ (a : Fin m → PowerSeries k) (x : W),
        (f : W → V) x ∈ N ∧ y = ∑ j : Fin m, a j • b j + (f : W → V) x := by
  classical
  let π : V →ₗ[PowerSeries k] (V ⧸ LinearMap.range f) :=
    (LinearMap.range f).mkQ.restrictScalars (PowerSeries k)
  let P : Submodule (PowerSeries k) (V ⧸ LinearMap.range f) := N.map π
  haveI : Module.Finite (PowerSeries k) P := Module.Finite.iff_fg.mpr (hN.map π)
  haveI : FaithfulSMul (PowerSeries k) (LaurentSeries k) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  haveI : IsTorsionFree (PowerSeries k) (V ⧸ LinearMap.range f) :=
    IsTorsionFree.trans_faithfulSMul (PowerSeries k) (LaurentSeries k) _
  haveI : IsTorsionFree (PowerSeries k) P := inferInstance
  let B := Module.finBasis (PowerSeries k) P
  have hB : ∀ j, ∃ v ∈ N, π v = (B j : V ⧸ LinearMap.range f) := fun j => (B j).2
  choose b hbN hb using hB
  refine ⟨_, b, ?_, ?_⟩
  · have e : ((LinearMap.range f).mkQ : V → V ⧸ LinearMap.range f) ∘ b
        = (Subtype.val : P → V ⧸ LinearMap.range f) ∘ B := by
      funext j; exact hb j
    rw [e, ← LinearIndependent.iff_fractionRing (PowerSeries k) (LaurentSeries k)]
    exact B.linearIndependent.map' P.subtype (Submodule.ker_subtype _)
  · intro y hy
    have hyP : π y ∈ P := Submodule.mem_map_of_mem hy
    set c := B.repr ⟨π y, hyP⟩ with hc
    have hsum := congrArg Subtype.val (B.sum_repr ⟨π y, hyP⟩)
    have h0 : π (y - ∑ j, c j • b j) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul, hb]
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
      rw [hsum, sub_self]
    have hz : y - ∑ j, c j • b j ∈ LinearMap.range f := (Submodule.Quotient.mk_eq_zero _).mp h0
    obtain ⟨x, hx⟩ := hz
    refine ⟨c, x, ?_, ?_⟩
    · rw [hx]; exact N.sub_mem hy (N.sum_mem fun j _ => N.smul_mem _ (hbN j))
    · rw [hx]; abel

end GlobalTheory.AbelianStatement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsRest
section
universe u_1 u_2

namespace GlobalTheory.PermutationExistence

theorem exists_perm {G : Type u_1} {C : Type u_2} [Group G] [AddCommMonoid C]
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (hT : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (h : G) (hh : h ∈ H) :
    ∃ σ : G → G, (∀ s ∈ S, σ s ∈ S ∧ (σ s)⁻¹ * (h * s) ∈ V) ∧
      ∀ f : G → C, ∑ s ∈ S, f (σ s) = ∑ s ∈ S, f s := by
  classical
  have key : ∀ s ∈ S, ∃ s' : G, s' ∈ S ∧ s'⁻¹ * (h * s) ∈ V := fun s hs =>
    (hT (h * s) (H.mul_mem hh (hS s hs))).exists
  choose! σ hσS hσV using key
  refine ⟨σ, fun s hs => ⟨hσS s hs, hσV s hs⟩, fun f => ?_⟩

  have hinj : Set.InjOn σ S := by
    intro s₁ hs₁ s₂ hs₂ heq
    have h1 := hσV s₁ hs₁
    rw [heq] at h1
    have h12 : s₁⁻¹ * s₂ ∈ V := by
      have e : ((σ s₂)⁻¹ * (h * s₁))⁻¹ * ((σ s₂)⁻¹ * (h * s₂)) = s₁⁻¹ * s₂ := by group
      rw [← e]
      exact V.mul_mem (V.inv_mem h1) (hσV s₂ hs₂)
    obtain ⟨u, _, hu⟩ := hT s₂ (hS s₂ hs₂)
    have e1 : s₁ = u := hu s₁ ⟨hs₁, h12⟩
    have e2 : s₂ = u := hu s₂ ⟨hs₂, by rw [inv_mul_cancel]; exact V.one_mem⟩
    rw [e1, e2]
  have himg : S.image σ = S := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
      exact hσS s hs
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ s ∈ S, f (σ s) = ∑ x ∈ S.image σ, f x := (Finset.sum_image hinj).symm
    _ = ∑ s ∈ S, f s := by rw [himg]

theorem main {G : Type u_1} {C : Type u_2} [Group G] [NormedField C] [IsUltrametricDist C]
    (act : G →* C ≃+* C) (hn : ∀ (g : G) (y : C), ‖act g y‖ = ‖y‖)
    (H V : Subgroup G) (S : Finset G) (hS : ∀ s ∈ S, s ∈ H)
    (hT : ∀ h ∈ H, ∃! s : G, s ∈ S ∧ s⁻¹ * h ∈ V) (a b : C) (hb : ‖b‖ ≤ (1 : ℝ))
    (hV : ∀ g ∈ V, act g b = b) (ha : ∑ s ∈ S, act s b = a) (c : G → C)
    (hc : ∀ g ∈ H, ∀ h ∈ H, c (g * h) = c g + act g (c h)) (t ε : ℝ) (ht : (0 : ℝ) ≤ t)
    (hε : (0 : ℝ) ≤ ε) (hct : ∀ g ∈ H, ‖c g‖ ≤ t) (hcε : ∀ g ∈ H, g ∈ V → ‖c g‖ ≤ ε) :
    ∃ x : C, ‖x‖ ≤ t ∧ ∀ h ∈ H, ‖a * c h - (act h x - x)‖ ≤ ε := by
  classical
  refine ⟨-∑ s ∈ S, act s b * c s, ?_, ?_⟩
  · rw [norm_neg]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg ht
    intro s hs
    rw [norm_mul, hn]
    calc ‖b‖ * ‖c s‖ ≤ 1 * t := mul_le_mul hb (hct s (hS s hs)) (norm_nonneg _) zero_le_one
      _ = t := one_mul t
  · intro h hh
    obtain ⟨σ, hσ, hsum⟩ := exists_perm (C := C) H V S hS hT h hh
    have hmul : ∀ (g k : G) (y : C), act (g * k) y = act g (act k y) := by
      intro g k y
      rw [map_mul]
      rfl

    have hterm : ∀ s ∈ S, act h (act s b * c s) = act (σ s) b * c (σ s)
        + act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - act (σ s) b * c h := by
      intro s hs
      have hsH := hS s hs
      have hσH := hS (σ s) (hσ s hs).1
      have hvV := (hσ s hs).2
      have hhs : h * s = σ s * ((σ s)⁻¹ * (h * s)) := (mul_inv_cancel_left _ _).symm
      have hvH : (σ s)⁻¹ * (h * s) ∈ H := H.mul_mem (H.inv_mem hσH) (H.mul_mem hh hsH)
      have h1 : act h (act s b) = act (σ s) b := by
        rw [← hmul, hhs, hmul, hV _ hvV]
      have h2 : act h (c s) = c (σ s) + act (σ s) (c ((σ s)⁻¹ * (h * s))) - c h := by
        have e1 := hc h hh s hsH
        have e2 := hc (σ s) hσH _ hvH
        rw [← hhs] at e2
        linear_combination e2 - e1
      rw [map_mul, h1, h2, map_mul (act (σ s)) b (c ((σ s)⁻¹ * (h * s)))]
      ring
    have hsumA : ∑ s ∈ S, act (σ s) b = a := by
      rw [← ha]
      exact hsum (fun g => act g b)
    have hsumT : ∑ s ∈ S, act (σ s) b * c (σ s) = ∑ s ∈ S, act s b * c s :=
      hsum (fun g => act g b * c g)
    have hact : act h (-∑ s ∈ S, act s b * c s) = -(∑ s ∈ S, act s b * c s
        + ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - a * c h) := by
      rw [map_neg, map_sum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, hsumT, ← Finset.sum_mul, hsumA]
    rw [hact]
    have hE : a * c h - (-(∑ s ∈ S, act s b * c s
        + ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) - a * c h)
        - -∑ s ∈ S, act s b * c s) = ∑ s ∈ S, act (σ s) (b * c ((σ s)⁻¹ * (h * s))) := by
      ring
    rw [hE]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε
    intro s hs
    rw [hn, norm_mul]
    have hvH : (σ s)⁻¹ * (h * s) ∈ H :=
      H.mul_mem (H.inv_mem (hS _ (hσ s hs).1)) (H.mul_mem hh (hS s hs))
    calc ‖b‖ * ‖c ((σ s)⁻¹ * (h * s))‖ ≤ 1 * ε :=
          mul_le_mul hb (hcε _ hvH (hσ s hs).2) (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

end GlobalTheory.PermutationExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsSide
section
namespace GlobalTheory.BasisMatrixExistence

theorem exists_basis {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {r : ℕ}
    (d : O) (hd : d ≠ 0) (N : Submodule O (Fin r → O)) (hN : ∀ x : Fin r → O, d • x ∈ N) :
    Nonempty (Module.Basis (Fin r) O N) := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin r)) N
  have : Module.Finite O N := Module.Finite.of_basis b
  have hfin : Module.finrank O N = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hle : n ≤ r := by
    have h := Submodule.finrank_le N
    rw [Module.finrank_fin_fun] at h
    omega

  let f : (Fin r → O) →ₗ[O] N :=
    { toFun := fun x => ⟨d • x, hN x⟩
      map_add' := fun x y => by ext1; simp [smul_add]
      map_smul' := fun c x => by ext1; simp [smul_comm d c x] }
  have hf : Function.Injective f := by
    intro x y hxy
    have h' : d • x = d • y := congrArg Subtype.val hxy
    exact smul_right_injective (Fin r → O) hd h'
  have hge : r ≤ n := by
    have h := LinearMap.finrank_le_finrank_of_injective hf
    rw [Module.finrank_fin_fun, hfin] at h
    exact h
  exact ⟨b.reindex (finCongr (le_antisymm hle hge))⟩

theorem exists_matrix {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {r : ℕ}
    (d : O) (hd : d ≠ 0) (N : Submodule O (Fin r → O)) (hN : ∀ x : Fin r → O, d • x ∈ N) :
    ∃ (G C : Matrix (Fin r) (Fin r) O), C * G = d • (1 : Matrix (Fin r) (Fin r) O) ∧
      ∀ v : Fin r → O, v ∈ N ↔ ∃ w : Fin r → O, v = Matrix.vecMul w G := by
  classical
  obtain ⟨b⟩ := exists_basis d hd N hN
  refine ⟨Matrix.of fun i j => (b i : Fin r → O) j,
    Matrix.of fun j i => b.repr ⟨d • Pi.single j 1, hN _⟩ i, ?_, ?_⟩
  · ext j k
    have hsum := congrArg (fun x : N => (x : Fin r → O) k) (b.sum_repr ⟨d • Pi.single j 1, hN _⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hsum
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply]
    rw [hsum]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [Ne.symm hjk, hjk]
  · intro v
    constructor
    · intro hv
      refine ⟨fun i => b.repr ⟨v, hv⟩ i, ?_⟩
      have hsum := congrArg (fun x : N => (x : Fin r → O)) (b.sum_repr ⟨v, hv⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hsum
      ext k
      have hk := congrFun hsum k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hk
      rw [Matrix.vecMul, dotProduct]
      simp only [Matrix.of_apply]
      exact hk.symm
    · rintro ⟨w, rfl⟩
      have : Matrix.vecMul w (Matrix.of fun i j => (b i : Fin r → O) j) =
          ∑ i, w i • (b i : Fin r → O) := by
        ext k
        simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2

theorem main : (let d1 : {O : Type} → [inst : CommRing O] → (I : Ideal O) → (r : ℕ) → (Fin r → O) →ₗ[O] Fin r → O ⧸ I := @(fun {O : Type} [CommRing O] (I : Ideal O) (r : ℕ) ↦ LinearMap.compLeft (AlgHom.toLinearMap (Ideal.Quotient.mkₐ O I)) (Fin r)); ∀ {O : Type} [inst : CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {r : ℕ} (d : O), d ≠ (0 : O) → ∀ (l : Submodule O (Fin r → O ⧸ Ideal.span {d})), ∃ (G : Matrix (Fin r) (Fin r) O) (C : Matrix (Fin r) (Fin r) O), C * G = d • (1 : Matrix (Fin r) (Fin r) O) ∧ ∀ (v : Fin r → O), (d1 (Ideal.span {d}) r : (Fin r → O) → Fin r → O ⧸ Ideal.span {d}) v ∈ l ↔ ∃ (w : Fin r → O), v = Matrix.vecMul w G) := by
  intro d1 O _ _ _ r d hd l
  let N : Submodule O (Fin r → O) := l.comap (d1 (Ideal.span {d}) r)
  have hN : ∀ x : Fin r → O, d • x ∈ N := by
    intro x
    show d1 (Ideal.span {d}) r (d • x) ∈ l
    have h0 : d1 (Ideal.span {d}) r (d • x) = 0 := by
      ext i
      change Ideal.Quotient.mk (Ideal.span {d}) (d * x i) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self d)
    rw [h0]
    exact l.zero_mem
  obtain ⟨G, C, hCG, hG⟩ := exists_matrix d hd N hN
  exact ⟨G, C, hCG, fun v => hG v⟩

end GlobalTheory.BasisMatrixExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsTail
section
namespace GlobalTheory.NonzeroScalarMembership

theorem exists_ne_zero_smul_mem {O LL V : Type} [CommRing O] [IsDomain O] [Field LL]
    [Algebra O LL] [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V]
    [IsScalarTower O LL V] (T : Submodule O V)
    (hT : Submodule.span LL (↑T : Set V) = ⊤) (x : V) :
    ∃ d : O, d ≠ 0 ∧ d • x ∈ T := by
  have hx : x ∈ Submodule.span LL (↑T : Set V) := hT ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact T.smul_mem b hay
    · rw [mul_smul]
      exact T.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors O) c
    have hq : (q : O) ≠ 0 := nonZeroDivisors.coe_ne_zero q
    refine ⟨q * a, mul_ne_zero hq ha, ?_⟩
    have h : ((q : O) * a) • c • y = p • a • y := by
      have h1 : (q : O) • c • y = p • y := by
        rw [← algebraMap_smul LL (q : O), smul_smul, mul_comm, hpq, algebraMap_smul]
      rw [mul_comm, mul_smul, h1, smul_comm]
    rw [h]
    exact T.smul_mem p hay

end GlobalTheory.NonzeroScalarMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralPi
section
namespace GlobalTheory.IntegralPi

open Polynomial

theorem isIntegral_pi {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i)
    (hx : ∀ i, IsIntegral O (x i)) : IsIntegral O x := by
  classical
  haveI := Fintype.ofFinite ι
  choose p hpm hp using hx
  refine ⟨∏ i, p i, monic_prod_of_monic _ _ (fun i _ => hpm i), ?_⟩
  rw [← aeval_def]
  funext j
  have key : (aeval x (∏ i, p i)) j = aeval (x j) (∏ i, p i) := by
    have := (aeval_algHom_apply (Pi.evalAlgHom O R j) x (∏ i, p i)).symm
    simpa using this
  rw [key, map_prod, Pi.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [aeval_def]; exact hp j)

theorem main : ∀ {O : Type} [inst : CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [inst_2 : (i : ι) → CommRing (R i)] [inst_3 : (i : ι) → Algebra O (R i)] (x : (i : ι) → R i),
    (∀ (i : ι), IsIntegral O (x i)) → IsIntegral O x :=
  fun x hx => isIntegral_pi x hx

end GlobalTheory.IntegralPi
end

