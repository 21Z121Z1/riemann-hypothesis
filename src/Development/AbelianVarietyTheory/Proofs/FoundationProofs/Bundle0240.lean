import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InjAndRatOfLi
section
set_option autoImplicit false

noncomputable section

open Formalism.IndefR.Bridge Formalism.L2.DIV NumberField GlobalTheory.PresBasic

namespace GlobalTheory.TraceIncl

section Scalar

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] {σ : K →+* ℂ}

theorem exists_int_smul (f : V →ₛₗ[σ] W) (hinj : Function.Injective f)
    (hs : ∀ x y (c : ℂ), f x = c • f y → y = 0 ∨ ∃ a, σ a = c) {x y : V} {c : ℂˣ} (hc : IsOfFinOrder c)
    (h : f x = (c : ℂ) • f y) : ∃ a : 𝓞 K, x = (a : K) • y := by
  rcases hs x y c h with rfl | ⟨a, ha⟩
  · exact ⟨0, hinj (by rw [h]; simp)⟩
  · obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
    have h1 : a ^ n = 1 := σ.injective (by rw [map_pow, ha, ← Units.val_pow_eq_pow_val, e, Units.val_one, map_one])
    refine ⟨⟨a, IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)⟩, hinj ?_⟩
    rw [h, map_smulₛₗ, ← ha]
    rfl

theorem inj_and_rat_of_li (f : V →ₛₗ[σ] W)
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent ℂ fun k => f (b k)) :
    Function.Injective f ∧ ∀ x y (c : ℂ), f x = c • f y → y = 0 ∨ ∃ a, σ a = c := by
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    by_contra h0
    have := (hli 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)).ne_zero 0
    exact this hx
  refine ⟨hinj, fun x y c h => ?_⟩
  by_cases hy : y = 0
  · exact Or.inl hy
  have hy' : f y ≠ 0 := fun h0 => hy (hinj (by rw [h0, map_zero]))
  by_cases hl : LinearIndependent K ![y, x]
  · have h2 : LinearIndependent ℂ ![f y, f x] := by
      convert hli 2 _ hl using 1
      funext k
      fin_cases k <;> rfl
    exact absurd h.symm ((LinearIndependent.pair_iff' hy').1 h2 c)
  · rw [LinearIndependent.pair_iff' hy] at hl
    push Not at hl
    obtain ⟨a, rfl⟩ := hl
    rw [map_smulₛₗ] at h
    exact Or.inr ⟨a, smul_left_injective ℂ hy' h⟩

end Scalar

variable {G Γ W K X : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] [AddCommGroup X] [Module ℂ X] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ) (k : G → W →ₗ[ℂ] X)

theorem coef_rat (x y : S.V) (c : ℂ) (h : P.coef x = c • P.coef y) : y = 0 ∨ ∃ a, σ a = c := by
  by_cases hy : y = 0
  · exact Or.inl hy
  obtain ⟨j, hj⟩ : ∃ j, S.bV.repr y j ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hy (S.bV.repr.injective (by ext j; simp [hn j]))
  have e := congrArg (fun w => (bW P).repr w j) h
  simp only [map_smul, Finsupp.smul_apply, repr_coef, smul_eq_mul] at e
  refine Or.inr ⟨S.bV.repr x j / S.bV.repr y j, ?_⟩
  rw [map_div₀, e, mul_div_cancel_right₀ _ ((map_ne_zero σ).2 hj)]

theorem card_stab (γ : Γ) (y : G) (j : J) : Nat.card (stab ι J (ι γ * y * j)) = Nat.card (stab ι J y) := by
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj γ⁻¹).toEquiv fun δ => ?_)
  rw [mem_stab, mem_stab]
  have e : (ι γ * y * j)⁻¹ * ι δ * (ι γ * y * j) = (j : G)⁻¹ * (y⁻¹ * ι ((MulAut.conj γ⁻¹).toEquiv δ) * y) * j := by
    simp [mul_assoc]
  rw [e, J.mul_mem_cancel_right j.2, J.mul_mem_cancel_left (J.inv_mem j.2)]

theorem sum_translate (κ : G) (h1 : ∀ j ∈ J, κ * j * κ⁻¹ ∈ J) (h2 : ∀ j ∈ J, κ⁻¹ * j * κ ∈ J) (Φ : G → X)
    (hΦ : ∀ γ h (j : J), Φ (ι γ * h * j) = Φ h) :
    ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • Φ (P.y c * κ) = ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • Φ (P.y c) := by
  have hinj : Function.Injective fun c => P.decC (P.y c * κ) := by
    intro c c' e
    have e1 := P.dec_spec (P.y c * κ)
    have e2 := P.dec_spec (P.y c' * κ)
    simp only at e
    rw [← e] at e2
    generalize P.decC (P.y c * κ) = d at e1 e2
    generalize P.decG (P.y c * κ) = γ at e1
    generalize P.decK (P.y c * κ) = j at e1
    generalize P.decG (P.y c' * κ) = γ' at e2
    generalize P.decK (P.y c' * κ) = j' at e2
    refine (P.reps (P.y c')).unique ⟨γ' * γ⁻¹, ⟨_, h1 _ (j⁻¹ * j').2⟩, ?_⟩ ⟨1, 1, by simp⟩
    rw [eq_mul_inv_of_mul_eq e1, eq_mul_inv_of_mul_eq e2]
    simp [mul_assoc]
  refine Fintype.sum_bijective _ (Finite.injective_iff_bijective.1 hinj) _ _ fun c => ?_
  have e1 := P.dec_spec (P.y c * κ)
  have e2 : stab ι J (P.y c * κ) = stab ι J (P.y c) := by
    ext δ
    rw [mem_stab, mem_stab]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · convert h1 _ h using 1
      group
    · convert h2 _ h using 1
      group
  rw [← e2]
  conv_lhs => rw [e1, card_stab, hΦ]

def clSum : S.Forms →ₛₗ[σ] X where
  toFun f := ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • k (P.y c) (P.extL f (P.y c))
  map_add' f f' := by simp [Finset.sum_add_distrib]
  map_smul' a f := by
    simp only [map_smulₛₗ, Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]
    exact Finset.sum_congr rfl fun c _ => smul_comm _ _ _

theorem clSum_apply (f : S.Forms) :
    clSum P k f = ∑ c, (Nat.card (stab ι J (P.y c)) : ℂ)⁻¹ • k (P.y c) (P.coef ((f : S.Cl → S.V) c)) :=
  Finset.sum_congr rfl fun c _ => by rw [ClassPres.extL_apply, ext_y]

structure KernelLaws (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) {J : Subgroup G} (χ : J →* ℂˣ) (k : G → W →ₗ[ℂ] X) : Prop where
  aut : ∀ γ h w, k (ι γ * h) (ρ γ w) = k h w
  typ : ∀ h (j : J) w, k (h * j) w = (((χ j)⁻¹ : ℂˣ) : ℂ) • k h w

variable {k}

theorem KernelLaws.dec (hk : KernelLaws ι ρ χ k) (γ : Γ) (h : G) (j : J) (w : W) :
    (χ j : ℂ) • k (ι γ * h * j) (ρ γ w) = k h w := by
  rw [hk.typ, hk.aut, smul_smul, Units.mul_inv, one_smul]

theorem KernelLaws.form (hk : KernelLaws ι ρ χ k) {F : G → W} (hF : F ∈ AdForms ι ρ J χ) (γ : Γ) (h : G) (j : J) :
    k (ι γ * h * j) (F (ι γ * h * j)) = k h (F h) := by
  rw [hF γ h j, map_smul, hk.dec]

theorem clSum_avgForm (hk : KernelLaws ι ρ χ k) (c : S.Cl) (x : S.V) :
    clSum P k (avgForm S c x) = k (P.y c) (P.coef x) := by
  classical
  rw [clSum_apply, Finset.sum_eq_single c]
  · have hg : ∀ g : S.Gam c, k (P.y c) (P.coef (S.ρ c g x)) = k (P.y c) (P.coef x) := fun g => by
      have := hk.dec (P.stabI c g : Γ) (P.y c) (stabK ι (P.stabI c g)) (P.coef x)
      rwa [stabK_spec, ← map_smul, ← P.coef_act] at this
    simp only [avgForm, Pi.single_eq_same, map_sum, hg, Finset.sum_const, Finset.card_univ]
    rw [← Nat.card_congr (P.stabI c).toEquiv, Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
  · intro c' _ hc
    simp [avgForm, Pi.single_eq_of_ne hc]
  · simp

theorem clSum_act (hk : KernelLaws ι ρ χ k) {Q : Subgroup G} {ch : Q →* ℂˣ} {G0 : Type} [Group G0]
    {act : Representation K G0 S.Forms} (T : ActTie ι P Q ch act) (hJ : J ≤ Q) (a : G0 → X →ₗ[ℂ] X)
    (ha : ∀ (q : Q) h w, a (T.red q) (k (h * q) w) = (((ch q)⁻¹ : ℂˣ) : ℂ) • k h w) (g : G0) (f : S.Forms) :
    clSum P k (act g f) = a g (clSum P k f) := by
  obtain ⟨q, rfl⟩ := T.red_surj g
  have hn : ∀ (q : Q), ∀ j ∈ J, (q : G) * j * (q : G)⁻¹ ∈ J := fun q j hj =>
    (T.red_ker (q * ⟨j, hJ hj⟩ * q⁻¹)).1 (by
      rw [map_mul, map_mul, (T.red_ker ⟨j, hJ hj⟩).2 hj, mul_one, ← map_mul, mul_inv_cancel, map_one])
  have key := sum_translate P (q : G) (hn q) (fun j hj => by simpa using hn q⁻¹ j hj)
    (fun h => k h (P.ext f h)) (hk.form (extMem P f))
  change ∑ c, _ • k (P.y c) (P.ext _ (P.y c)) = a _ (∑ c, _ • k (P.y c) (P.ext _ (P.y c)))
  rw [← key, map_sum, T.act_eq _ q rfl]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, ha, g0Act, map_smul]

structure LatSys (r : Γ → S.V →ₗ[K] S.V) (L : G → Submodule (𝓞 K) S.V) : Prop where
  coef : ∀ γ x, P.coef (r γ x) = ρ γ (P.coef x)
  move : ∀ γ h (j : J), ∀ x ∈ L h, r γ x ∈ L (ι γ * h * j)
  nab : ∀ c, L (P.y c) = S.Nab c

variable {P} {r : Γ → S.V →ₗ[K] S.V} {L : G → Submodule (𝓞 K) S.V}

theorem LatSys.avg_mem (hL : LatSys P r L) (hχ : ∀ j, IsOfFinOrder (χ j)) {c : S.Cl} {x : S.V} (hx : x ∈ S.Nab c) (c' : S.Cl) :
    (avgForm S c x : S.Cl → S.V) c' ∈ S.Nab c' := by
  classical
  by_cases h : c' = c
  · subst h
    simp only [avgForm, Pi.single_eq_same]
    refine Submodule.sum_mem _ fun g _ => ?_
    have h1 := hL.move (P.stabI c' g : Γ) (P.y c') (stabK ι (P.stabI c' g)) x (hL.nab c' ▸ hx)
    rw [stabK_spec, hL.nab] at h1
    obtain ⟨a, ha⟩ := exists_int_smul P.coef (coef_injective P) (coef_rat P) (hχ _)
      ((P.coef_act c' g x).trans (by rw [← hL.coef]))
    rw [ha]
    have h2 := Submodule.smul_mem _ a h1
    rwa [← algebraMap_smul K a] at h2
  · simp [avgForm, Pi.single_eq_of_ne h]

theorem LatSys.exists_trace (hL : LatSys P r L) (hχ : ∀ j, IsOfFinOrder (χ j)) (hk : KernelLaws ι ρ χ k) {h : G} {x : S.V}
    (hx : x ∈ L h) : ∃ f : S.Forms, (∀ c, (f : S.Cl → S.V) c ∈ S.Nab c) ∧
      ∃ j : J, k h (P.coef x) = (((χ j)⁻¹ : ℂˣ) : ℂ) • clSum P k f := by
  obtain ⟨c, ⟨γ, j, rfl⟩, -⟩ := P.reps h
  have h1 := hL.move γ⁻¹ _ j⁻¹ x hx
  rw [show ι γ⁻¹ * (ι γ * P.y c * j) * (j⁻¹ : J) = P.y c by simp [mul_assoc], hL.nab] at h1
  refine ⟨avgForm S c (r γ⁻¹ x), hL.avg_mem hχ h1, j, ?_⟩
  rw [clSum_avgForm P hk, ← hk.dec γ (P.y c) j, smul_smul, Units.inv_mul, one_smul, hL.coef, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

end GlobalTheory.TraceIncl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralLeOfDisjointTranslates
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaSupBall

open MeasureTheory Filter Set
open scoped Pointwise

theorem integral_le_of_disjoint_translates {ι : Type} [Fintype ι]
    (A : AddSubgroup (EuclideanSpace ℂ ι)) [Countable A]
    (D t : Set (EuclideanSpace ℂ ι)) (hD : IsAddFundamentalDomain A D volume)
    (ht : MeasurableSet t)
    (hd : ∀ y₁ y₂ : A, y₁ ≠ y₂ → Disjoint (y₁ +ᵥ t) (y₂ +ᵥ t))
    (f : EuclideanSpace ℂ ι → ℝ) (hf0 : ∀ u, 0 ≤ f u) (hfc : Continuous f)
    (hf : ∀ (y : A) u, f (y +ᵥ u) = f u) (hi : IntegrableOn f D) :
    ∫ u in t, f u ≤ ∫ u in D, f u := by
  haveI : VAddInvariantMeasure A (EuclideanSpace ℂ ι) volume :=
    ⟨fun g s _ => measure_preimage_add volume (g : EuclideanSpace ℂ ι) s⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfc.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfc.aestronglyMeasurable]
  refine ENNReal.toReal_mono (Integrable.lintegral_lt_top hi).ne ?_
  calc ∫⁻ u in t, ENNReal.ofReal (f u)
      = ∑' y : A, ∫⁻ u in (y +ᵥ t) ∩ D, ENNReal.ofReal (f (-y +ᵥ u)) :=
        hD.setLIntegral_eq_tsum' (fun u => ENNReal.ofReal (f u)) t
    _ = ∑' y : A, ∫⁻ u in (y +ᵥ t) ∩ D, ENNReal.ofReal (f u) := by simp_rw [hf]
    _ = ∫⁻ u in ⋃ y : A, (y +ᵥ t) ∩ D, ENNReal.ofReal (f u) := by
        refine (lintegral_iUnion₀ (fun y => ?_) ?_ _).symm
        · exact (ht.const_vadd y).nullMeasurableSet.inter hD.nullMeasurableSet
        · intro y₁ y₂ h
          exact (((hd y₁ y₂ h).inf_left _).inf_right _).aedisjoint
    _ ≤ ∫⁻ u in D, ENNReal.ofReal (f u) :=
        lintegral_mono_set (iUnion_subset fun _ => inter_subset_right)

theorem factorial_div_le (g : ℕ) {v r : ℝ} (hv : 1 ≤ v) (hr : r ^ 2 = 1 / (4 * v)) :
    (g.factorial : ℝ) / (Real.pi ^ g * r ^ (2 * g)) ≤ (2 * (g : ℝ) * v + 1) ^ g := by
  have hv0 : 0 < v := by linarith
  have hpi := Real.pi_gt_three
  rw [pow_mul, hr, ← mul_pow]
  have h1 : (g.factorial : ℝ) ≤ (g : ℝ) ^ g := by exact_mod_cast Nat.factorial_le_pow g
  calc (g.factorial : ℝ) / (Real.pi * (1 / (4 * v))) ^ g
      ≤ (g : ℝ) ^ g / (Real.pi * (1 / (4 * v))) ^ g := by gcongr
    _ = ((g : ℝ) / (Real.pi * (1 / (4 * v)))) ^ g := by rw [div_pow]
    _ ≤ _ := by
        refine pow_le_pow_left₀ (by positivity) ?_ g
        rw [div_le_iff₀ (by positivity)]
        have h2 : (2 * (g : ℝ) * v + 1) * (Real.pi * (1 / (4 * v)))
            = Real.pi / 2 * g + Real.pi / (4 * v) := by field_simp; ring
        rw [h2]
        have h3 : 0 ≤ Real.pi / (4 * v) := by positivity
        have h4 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
        nlinarith

theorem sup_le_mean_square : ∀ (ι : Type) [Fintype ι] (A : AddSubgroup (EuclideanSpace ℂ ι)) (v : ℝ) (Fd : Set (EuclideanSpace ℂ ι)) (G : EuclideanSpace ℂ ι → ℂ), 1 ≤ v → (∀ x ∈ A, x ≠ 0 → 1 / v ≤ ‖x‖ ^ 2) → MeasureTheory.IsAddFundamentalDomain A Fd MeasureTheory.volume → MeasureTheory.volume Fd = 1 → Differentiable ℂ G → (∀ x ∈ A, ∀ z, ‖G (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2) = ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) → MeasureTheory.IntegrableOn (fun z => ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)) Fd → ∀ z, ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) ≤ 3 * (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι * ∫ w in Fd, ‖G w‖ ^ 2 * Real.exp (-Real.pi * ‖w‖ ^ 2) := by
  intro ι _ A v Fd G hv hA hD _ hG hinv hint z
  have hv0 : 0 < v := by linarith
  set r : ℝ := Real.sqrt (1 / (4 * v)) with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 1 / (4 * v) := Real.sq_sqrt (by positivity)
  set N : EuclideanSpace ℂ ι → ℝ := fun u => ‖G u‖ ^ 2 * Real.exp (-Real.pi * ‖u‖ ^ 2) with hN
  have hN0 : ∀ u, 0 ≤ N u := fun u => by positivity
  have hGc := hG.continuous
  have hNc : Continuous N := by simp only [hN]; fun_prop
  have hdisj : ∀ y₁ y₂ : A, y₁ ≠ y₂ →
      Disjoint (y₁ +ᵥ Metric.ball z r) (y₂ +ᵥ Metric.ball z r) := by
    intro y₁ y₂ hne
    rw [Set.disjoint_left]
    rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
    have hpq' : (y₂ : EuclideanSpace ℂ ι) + q = (y₁ : EuclideanSpace ℂ ι) + p := hpq
    have hy : ((y₁ - y₂ : A) : EuclideanSpace ℂ ι) = q - p := by
      rw [AddSubgroup.coe_sub, sub_eq_sub_iff_add_eq_add, ← hpq', add_comm]
    have hne' : ((y₁ - y₂ : A) : EuclideanSpace ℂ ι) ≠ 0 := fun h0 =>
      hne (sub_eq_zero.mp (Subtype.ext h0))
    have h1 := hA _ (y₁ - y₂ : A).2 hne'
    rw [hy] at h1
    have h2 : ‖q - p‖ < 2 * r := by
      have hp' : dist p z < r := hp
      have hq' : dist q z < r := hq
      rw [← dist_eq_norm]
      calc dist q p ≤ dist q z + dist z p := dist_triangle _ _ _
        _ < 2 * r := by rw [dist_comm z p]; linarith
    have h3 : ‖q - p‖ ^ 2 < (2 * r) ^ 2 := by gcongr
    have h4 : (2 * r) ^ 2 = 1 / v := by rw [mul_pow, hr2]; field_simp; norm_num
    linarith
  haveI : Countable A := by
    rw [← Set.countable_univ_iff]
    refine Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun y : A => y +ᵥ Metric.ball z r) (fun a _ b _ h => hdisj a b h) ?_ ?_
    · intro y _
      exact Metric.isOpen_ball.vadd (y : EuclideanSpace ℂ ι)
    · intro y _
      exact ⟨y +ᵥ z, z, Metric.mem_ball_self hr0, rfl⟩
  have hpk : ∫ u in Metric.ball z r, N u ≤ ∫ u in Fd, N u := by
    refine integral_le_of_disjoint_translates A Fd _ hD measurableSet_ball hdisj N hN0 hNc ?_ hint
    intro y u
    have e : y +ᵥ u = u + (y : EuclideanSpace ℂ ι) := by
      rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm]
    rw [e]
    exact hinv y y.2 u
  set φ : EuclideanSpace ℂ ι → ℂ :=
    fun u => G u * Complex.exp (-(Real.pi : ℂ) * innerSL ℂ z (u - z)) with hφ
  have hφd : Differentiable ℂ φ := by
    refine hG.mul (Differentiable.cexp (Differentiable.const_mul ?_ _))
    exact (innerSL ℂ z).differentiable.comp (differentiable_id.sub_const z)
  have hφi : IntegrableOn (fun u => ‖φ u‖ ^ 2) (Metric.ball z r) :=
    GlobalTheory.integrableOn_norm_pow_ball volume hφd.continuous.continuousOn 2
  have hsub := GlobalTheory.norm_pow_le_factorial_div_mul_integral_ball hr0 hφd.differentiableOn 2 hφi
  rw [finrank_euclideanSpace] at hsub
  have hφz : φ z = G z := by simp [hφ]
  rw [hφz] at hsub
  have hpt : ∀ u ∈ Metric.ball z r,
      ‖φ u‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2) ≤ 3 * N u := by
    intro u hu
    have hu' : ‖u - z‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hu
    have h1 : ‖u - z‖ ^ 2 ≤ 1 / 4 := by
      have : ‖u - z‖ ^ 2 ≤ r ^ 2 := by gcongr
      refine this.trans ?_
      rw [hr2]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : ‖u‖ ^ 2 = ‖z‖ ^ 2 + 2 * (inner ℂ z (u - z)).re + ‖u - z‖ ^ 2 := by
      have := norm_add_sq (𝕜 := ℂ) z (u - z)
      rwa [add_sub_cancel] at this
    have h3 : Real.exp (Real.pi * ‖u - z‖ ^ 2) ≤ 3 := by
      have hpi := Real.pi_le_four
      have hpi0 := Real.pi_pos
      calc Real.exp (Real.pi * ‖u - z‖ ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖u - z‖])
        _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
    have h4 : ‖φ u‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)
        = Real.exp (Real.pi * ‖u - z‖ ^ 2) * N u := by
      simp only [hφ, hN]
      rw [norm_mul, Complex.norm_exp, mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add,
        mul_left_comm, ← Real.exp_add, h2]
      congr 2
      simp only [innerSL_apply_apply, neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
      push_cast
      ring
    rw [h4]
    exact mul_le_mul_of_nonneg_right h3 (hN0 u)
  have hNi : IntegrableOn N (Metric.ball z r) :=
    (hNc.continuousOn.integrableOn_compact (isCompact_closedBall z r)).mono_set
      Metric.ball_subset_closedBall
  have hb : (∫ u in Metric.ball z r, ‖φ u‖ ^ 2) * Real.exp (-Real.pi * ‖z‖ ^ 2)
      ≤ 3 * ∫ u in Metric.ball z r, N u := by
    rw [← integral_mul_const, ← integral_const_mul]
    exact setIntegral_mono_on (hφi.mul_const _) (hNi.const_mul _) measurableSet_ball hpt
  have hnum := factorial_div_le (Fintype.card ι) hv hr2
  have hI0 : 0 ≤ ∫ u in Fd, N u := integral_nonneg hN0
  set c : ℝ := ((Fintype.card ι).factorial : ℝ) /
    (Real.pi ^ Fintype.card ι * r ^ (2 * Fintype.card ι)) with hc
  have hc0 : 0 ≤ c := by positivity
  calc ‖G z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2)
      ≤ (c * ∫ u in Metric.ball z r, ‖φ u‖ ^ 2) * Real.exp (-Real.pi * ‖z‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hsub (Real.exp_pos _).le
    _ ≤ c * (3 * ∫ u in Metric.ball z r, N u) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb hc0
    _ ≤ c * (3 * ∫ u in Fd, N u) := by gcongr
    _ ≤ (2 * (Fintype.card ι : ℝ) * v + 1) ^ Fintype.card ι * (3 * ∫ u in Fd, N u) := by gcongr
    _ = _ := by ring

end GlobalTheory.ThetaSupBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Complex
open scoped BigOperators ComplexConjugate Real

noncomputable section

namespace GlobalTheory.UnitaryTheta

section General

abbrev Sesq (V : Type) [AddCommGroup V] [Module ℂ V] : Type := V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def IsPosHerm (H : Sesq V) : Prop :=
  (∀ z w, H z w = conj (H w z)) ∧ ∀ z, z ≠ 0 → 0 < (H z z).re

def Heisenberg₂ (H : Sesq V) (x : V) (G : V → ℂ) : V → ℂ :=
  fun z => G (z + x) * cexp (-(π : ℂ) * H z x - (π : ℂ) * H x x / 2)

def kerTerm (H : Sesq V) (x w z : V) : ℂ :=
  cexp ((π : ℂ) * H (w + x) z - (π : ℂ) * H w x - (π : ℂ) * H x x / 2)

def kerSum (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) (z : V) : V → ℂ :=
  fun w => ∑' x : Λ, α x * kerTerm H x w z

def IsSemichar (H : Sesq V) (Λ : AddSubgroup V) (α : V → ℂ) : Prop :=
  (∀ x ∈ Λ, α x = 1 ∨ α x = -1) ∧ (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ m : ℤ, (H x y).im = m) ∧
    ∀ x ∈ Λ, ∀ y ∈ Λ, α (x + y) = α x * α y * cexp (-((π : ℂ) * I) * ((H x y).im : ℂ))

end General

def formV (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (fun z z' w => by simp [Hf, add_mul, Finset.sum_add_distrib, add_div])
    (fun c z w => by simp [Hf, Finset.mul_sum, mul_assoc, mul_div_assoc'])
    (fun z w w' => by simp [Hf, mul_add, Finset.sum_add_distrib, add_div])
    (fun c z w => by simp [Hf, Finset.mul_sum, mul_left_comm, mul_div_assoc'])

@[simp] theorem formV_apply (D : D7) (T : Tor D) {N N' : ℕ} (z w : VC D N N') :
    formV D T N N' z w = Hf D T z w := rfl

theorem heis_formV (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (G : VC D N N' → ℂ) :
    Heisenberg₂ (formV D T N N') x G = U D T x G := rfl

open NumberField Classical in
open Complex in
open scoped BigOperators ComplexConjugate Real in
theorem _root_.GlobalTheory.UnitaryTheta.isPosHerm_formV (D : _root_.Formalism.BasicNotions.D7) (T : _root_.Formalism.MainNotions.TaylorLogMetric.Tor D)
    (N N' : ℕ) (h : 0 < _root_.Formalism.MainNotions.TaylorLogMetric.area T.abelian₂) :
    _root_.GlobalTheory.UnitaryTheta.IsPosHerm (_root_.GlobalTheory.UnitaryTheta.formV D T N N') := by
  refine ⟨fun z w => ?_, fun z hz => ?_⟩
  · simp only [_root_.GlobalTheory.UnitaryTheta.formV_apply, _root_.Formalism.MainNotions.TaylorLogMetric.Hf, map_div₀, map_sum, map_mul,
      Complex.conj_conj, Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => mul_comm _ _
  · have hsum : ∀ τ i j, z τ i j * conj (z τ i j) = ((Complex.normSq (z τ i j) : ℝ) : ℂ) :=
      fun τ i j => Complex.mul_conj _
    simp only [_root_.GlobalTheory.UnitaryTheta.formV_apply, _root_.Formalism.MainNotions.TaylorLogMetric.Hf, hsum]
    simp only [← Complex.ofReal_sum, ← Complex.ofReal_div, Complex.ofReal_re]
    refine div_pos ?_ h
    obtain ⟨τ, i, j, hz⟩ : ∃ τ i j, z τ i j ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hz (funext fun τ => funext fun i => funext fun j => hne τ i j)
    refine Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) ⟨τ, Finset.mem_univ _, ?_⟩
    refine Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, ?_⟩
    exact Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
      ⟨j, Finset.mem_univ _, Complex.normSq_pos.2 hz⟩

end GlobalTheory.UnitaryTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrthoProductThetaMemThetaSpaceOfLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ProdTheta

theorem coordB_add (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (z x : VC D N N') : coordB D T b k (z + x) = coordB D T b k z + coordB D T b k x := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem coordB_differentiable (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (k : Fin r) : Differentiable ℂ (coordB D T b k) := by
  unfold coordB
  fun_prop

theorem neg_one_zpow_sum {ι : Type} (s : Finset ι) (m : ι → ℤ) :
    (-1 : ℂ) ^ (∑ k ∈ s, m k) = ∏ k ∈ s, (-1 : ℂ) ^ m k := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ (by norm_num), ih]

theorem pullB_mem_ThSp : ∀ (D : D7) (T : Tor D) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ), (∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) = ∑ k, coordB D T b k z * (starRingEnd ℂ) (coordB D T b k w)) → (∀ x : VC D N N', x ∈ LaB D T b ↔ ∀ k, coordB D T b k x ∈ T.abelian₂) → Differentiable ℂ g → (∀ ω ∈ T.abelian₂, ∃ m : ℤ, q1 D T.abelian₂ ω = m ∧ ∀ z, (-1 : ℂ) ^ m * U1 T.abelian₂ ω g z = g z) → pullB D T b g ∈ ThSp D T (LaB D T b) := by
  intro D T N N' r b g hP hL hg hq
  refine ⟨?_, ?_⟩
  · unfold pullB
    have hc := coordB_differentiable D T b
    fun_prop
  · intro x hx z
    have hx' := (hL x).1 hx
    choose m hm hU using fun k => hq _ (hx' k)
    have hre : Real.sqrt D.host.d / 2 * (Hf D T x x).re = ((∑ k, m k : ℤ) : ℝ) := by
      unfold Hf
      rw [hP, Complex.div_ofReal_re, Complex.re_sum, Int.cast_sum, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hm k, q1, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hal : al D T x = ∏ k, (-1 : ℂ) ^ m k := by
      unfold al
      rw [hre, round_intCast, neg_one_zpow_sum]
    have hUU : U D T x (pullB D T b g) z = ∏ k, U1 T.abelian₂ (coordB D T b k x) g (coordB D T b k z) := by
      unfold U U1 pullB Hf
      rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
      simp only [coordB_add]
      congr 2
      rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hal, hUU, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => hU k _

end GlobalTheory.ProdTheta
end

