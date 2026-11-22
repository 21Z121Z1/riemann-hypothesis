import Development.DiscreteGroups.GlobalIrreducibility.MulMemBall
import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0019
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.ExistsBallMem
section
noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.SplitWeil ValuativeRel

namespace DiscreteGroups.sglob.LConvGenF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem psi_triv {ψ : AddChar k Circle} {c : kˣ} (hc : HasConductor ψ c) {s : kˣ} {ξ : k}
    (hξ : ξ ∈ ball (c * s⁻¹)) : ∀ h ∈ ball s, ψ (ξ * h) = 1 := by
  intro h hh
  have := mul_mem_ball hξ hh
  rw [inv_mul_cancel_right] at this
  exact hc.eq_one this

theorem psi_neg_triv {ψ : AddChar k Circle} {c : kˣ} (hc : HasConductor ψ c) {s : kˣ} {ξ : k}
    (hξ : ξ ∈ ball (c * s⁻¹)) {h : k} (hh : h ∈ ball s) : ψ (-(ξ * h)) = 1 := by
  have := mul_mem_ball hξ hh
  rw [inv_mul_cancel_right] at this
  exact hc.eq_one (neg_mem this)

theorem card_ne_zero (s t : kˣ) : ((Fintype.card (Q (k := k) s t) : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem exists_ball_mem (a : k) : ∃ t : kˣ, a ∈ ball t := by
  by_cases h : a = 0
  · exact ⟨1, by rw [h]; exact (ball 1).zero_mem⟩
  · exact ⟨Units.mk0 a h, mem_ball.2 le_rfl⟩

theorem exists_min (s1 s2 : kˣ) : ∃ s : kˣ, valuation k (s : k) ≤ valuation k (s1 : k) ∧
    valuation k (s : k) ≤ valuation k (s2 : k) := by
  rcases le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h
  · exact ⟨s1, le_rfl, h⟩
  · exact ⟨s2, h, le_rfl⟩

theorem exists_max (s1 s2 : kˣ) : ∃ s : kˣ, valuation k (s1 : k) ≤ valuation k (s : k) ∧
    valuation k (s2 : k) ≤ valuation k (s : k) := by
  rcases le_total (valuation k (s1 : k)) (valuation k (s2 : k)) with h | h
  · exact ⟨s2, h, le_rfl⟩
  · exact ⟨s1, le_rfl, h⟩

section Fourier

variable (ψ : AddChar k Circle) (σ : k → V →ₗ[ℂ] V) (hadd : ∀ a b, σ (a + b) = σ a * σ b)

theorem avg_of_eigen {s t : kˣ} {ξ : k} {z : V}
    (hz : ∀ b ∈ ball t, σ b z = ((ψ (ξ * b) : Circle) : ℂ) • z) :
    avg ψ σ s t ξ z = ((Fintype.card (Q s t) : ℕ) : ℂ) • z := by
  have h1 : ∀ q : Q s t, ((ψ (-(ξ * ((Quotient.out q : ↥(ball t)) : k))) : Circle) : ℂ) •
      σ ((Quotient.out q : ↥(ball t)) : k) z = z := fun q => by
    rw [hz _ (out_mem q), smul_smul, ch_neg_mul, one_smul]
  simp only [avg, LinearMap.sum_apply, LinearMap.smul_apply, h1, Finset.sum_const, Finset.card_univ]
  exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm

include hadd

theorem avg_level {s s0 t : kˣ} {ξ : k} (hss0 : valuation k (s : k) ≤ valuation k (s0 : k))
    (hξ : ∀ h ∈ ball s0, ψ (ξ * h) = 1) {x : V} (hx : ∀ h ∈ ball s0, σ h x = x) :
    ((Fintype.card (Q s0 t) : ℕ) : ℂ) • avg ψ σ s t ξ x = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s0 t ξ x := by
  have hξs : ∀ h ∈ ball s, ψ (ξ * h) = 1 := fun h hh => hξ h (ball_mono hss0 hh)
  have hxs : ∀ h ∈ ball s, σ h x = x := fun h hh => hx h (ball_mono hss0 hh)
  have e1 : avg ψ σ s0 t ξ (avg ψ σ s t ξ x) = ((Fintype.card (Q s0 t) : ℕ) : ℂ) • avg ψ σ s t ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξs hxs hb)
  have e2 : avg ψ σ s t ξ (avg ψ σ s0 t ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s0 t ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx hb)
  rw [← e1, ← e2, ← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]

theorem avg_mono_mem (W : Submodule ℂ V) (hW : ∀ a, ∀ w ∈ W, σ a w ∈ W) {s t t' : kˣ}
    (htt' : valuation k (t : k) ≤ valuation k (t' : k)) {ξ : k} (hξ : ∀ h ∈ ball s, ψ (ξ * h) = 1)
    {x : V} (hx : ∀ h ∈ ball s, σ h x = x) (h : avg ψ σ s t ξ x ∈ W) : avg ψ σ s t' ξ x ∈ W := by
  have e : avg ψ σ s t ξ (avg ψ σ s t' ξ x) = ((Fintype.card (Q s t) : ℕ) : ℂ) • avg ψ σ s t' ξ x :=
    avg_of_eigen ψ σ (fun b hb => avg_eigen ψ σ hadd hξ hx (ball_mono htt' hb))
  have hm : avg ψ σ s t ξ (avg ψ σ s t' ξ x) ∈ W := by
    rw [← Module.End.mul_apply, avg_comm_avg ψ σ hadd, Module.End.mul_apply]
    exact avg_mem ψ σ W hW _ _ _ h
  rw [e] at hm
  exact (W.smul_mem_iff (card_ne_zero s t)).1 hm

end Fourier

end DiscreteGroups.sglob.LConvGenF
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.KmatMulKinv
section
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands ValuativeRel Filter Topology

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] {m : ℕ}

def Kmat (jj : Fin (m + 1)) (a : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Matrix.of fun p q => if p = jj then a q else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q

def Kinv2 (jj : Fin (m + 1)) (z : (Fin (m + 1) → k) × k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Matrix.of fun p q => if p = jj then (if q = jj then z.2 else -(z.1 q) * z.2)
    else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q

def Kinv (jj : Fin (m + 1)) (a : Fin (m + 1) → k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
  Kinv2 jj (a, (a jj)⁻¹)

theorem Kmat_mul_Kinv (jj : Fin (m + 1)) (a : Fin (m + 1) → k) (ha : a jj ≠ 0) :
    Kmat jj a * Kinv jj a = 1 := by
  ext p q
  rw [Matrix.mul_apply]
  by_cases hp : p = jj
  · subst hp
    have hs : ∀ r, Kmat p a p r * Kinv p a r q = a r * (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r q +
        (if r = p then a p * (Kinv p a p q - (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) p q) else 0) := by
      intro r
      by_cases hr : r = p
      · rw [hr, if_pos rfl]; simp only [Kmat, Matrix.of_apply, ↓reduceIte]; ring
      · rw [if_neg hr, add_zero]
        simp only [Kmat, Kinv, Kinv2, Matrix.of_apply, ↓reduceIte, if_neg hr]
    rw [Finset.sum_congr rfl (fun r _ => hs r), Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hq : q = p
    · subst hq
      simp only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte]
      field_simp
      ring
    · simp only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte, if_neg hq, if_neg (Ne.symm hq)]
      field_simp
      ring
  · rw [Finset.sum_eq_single p]
    · simp only [Kmat, Kinv, Kinv2, Matrix.of_apply, if_neg hp, Matrix.one_apply_eq, one_mul]
    · intro r _ hr
      simp only [Kmat, Matrix.of_apply, if_neg hp, Matrix.one_apply_ne (Ne.symm hr), zero_mul]
    · intro h; exact absurd (Finset.mem_univ p) h

theorem Kinv_mul_Kmat (jj : Fin (m + 1)) (a : Fin (m + 1) → k) (ha : a jj ≠ 0) :
    Kinv jj a * Kmat jj a = 1 :=
  mul_eq_one_comm.1 (Kmat_mul_Kinv jj a ha)

theorem Kmat_single (jj : Fin (m + 1)) : Kmat jj (Pi.single jj (1 : k)) = 1 := by
  ext p q
  by_cases hp : p = jj
  · subst hp; simp [Kmat, Matrix.one_apply, Pi.single_apply, eq_comm]
  · simp [Kmat, hp]

theorem Kinv_single (jj : Fin (m + 1)) : Kinv jj (Pi.single jj (1 : k)) = 1 := by
  ext p q
  by_cases hp : p = jj
  · subst hp
    by_cases hq : q = p
    · subst hq; simp [Kinv, Kinv2]
    · simp [Kinv, Kinv2, hq, Matrix.one_apply, Pi.single_apply, Ne.symm hq]
  · simp [Kinv, Kinv2, hp]

end DiscreteGroups.sglob.LConvKir
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvBigD
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Filter Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁}
  {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂} {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

theorem small_fix (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) (v₁ : V₁) (v₂ : V₂) (i j : Fin (m + 1)) (h : i ≠ j) :
    {t : k | π₁ (tv i j h (-t)) v₁ = v₁ ∧ π₂ (tv i j h (-t)) v₂ = v₂} ∈ 𝓝 (0 : k) := by
  have hc : Continuous fun t : k => tv i j h (-t) := (continuous_tv i j h).comp continuous_neg
  refine IsOpen.mem_nhds (((hs₁ v₁).preimage hc).inter ((hs₂ v₂).preimage hc)) ?_
  simp [tv_zero]

theorem last_ne_zero (hm : 0 < m) : Fin.last m ≠ (0 : Fin (m + 1)) := fun e => by
  have := congrArg Fin.val e
  simp at this
  omega

theorem transvection_apply_same (i j : Fin (m + 1)) (h : i ≠ j) (t : k) : Matrix.transvection i j t i j = t := by
  simp [Matrix.transvection, Matrix.one_apply_ne h]

theorem centralChar_eq (hm : 0 < m) (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) {ω₁ ω₂ : kˣ →* ℂˣ}
    (h₁ : HasCentralChar π₁ ω₁) (h₂ : HasCentralChar π₂ ω₂) (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (h0 : l₁ v₁ ≠ 0) : ω₁ = ω₂ := by
  have hc : l₁ v₁ = l₂ v₂ := by
    have := hX 1
    rwa [corner_one, map_one, map_one, Module.End.one_apply, Module.End.one_apply] at this
  have hL := last_ne_zero hm
  have hO := small_fix hs₁ hs₂ v₁ v₂ _ _ hL
  have key : ∀ t : k, ∀ ht : t ≠ 0, t ∈ {t : k | π₁ (tv _ _ hL (-t)) v₁ = v₁ ∧ π₂ (tv _ _ hL (-t)) v₂ = v₂} →
      ω₁ (Units.mk0 t ht) = ω₂ (Units.mk0 t ht) := by
    intro t ht hmem
    have hent : (((tv _ _ hL (-t))⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 =
        (Units.mk0 t ht : k) := by
      rw [val_tv_inv, neg_neg, transvection_apply_same _ _ hL, Units.val_mk0]
    have := agree_scalar h₁ h₂ hl₁ hl₂ hW hX _ _ hent
    rw [hmem.1, hmem.2, ← hc] at this
    exact Units.ext (mul_right_cancel₀ h0 this)
  refine MonoidHom.ext fun a => ?_
  obtain ⟨t, ht, htO, hatO⟩ := exists_small hO (a : k)
  have hat : (a : k) * t ≠ 0 := mul_ne_zero a.ne_zero ht
  have e : Units.mk0 ((a : k) * t) hat = a * Units.mk0 t ht := Units.ext (by simp)
  have h1 := key _ hat hatO
  rw [e, map_mul, map_mul, key _ ht htO] at h1
  exact mul_right_cancel h1

theorem agree_all (hm : 0 < m) (hs₁ : IsSmooth π₁) (hs₂ : IsSmooth π₂) {ω : kˣ →* ℂˣ}
    (h₁ : HasCentralChar π₁ ω) (h₂ : HasCentralChar π₂ ω) (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k) :
    l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
  have step : ∀ g : GL (Fin (m + 1)) k,
      ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 ≠ 0 →
      l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
    intro g hg
    have := agree_scalar h₁ h₂ hl₁ hl₂ hW hX g (Units.mk0 _ hg) rfl
    exact mul_left_cancel₀ (ω (Units.mk0 _ hg)).ne_zero this
  by_cases hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 0
  swap
  · exact step g hg
  obtain ⟨j, hj⟩ : ∃ j, ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) j 0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h1 := congrFun (congrFun g.mul_inv 0) 0
    rw [Matrix.mul_apply] at h1
    simp [hall] at h1
  have hjL : Fin.last m ≠ j := fun e => hj (e ▸ hg)
  obtain ⟨t, ht, htO, -⟩ := exists_small (small_fix hs₁ hs₂ v₁ v₂ _ _ hjL) 1
  have hent : (((g * tv _ _ hjL (-t))⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k)
      (Fin.last m) 0 ≠ 0 := by
    rw [mul_inv_rev, Units.val_mul, val_tv_inv, neg_neg, Matrix.transvection_mul_apply_same, hg, zero_add]
    exact mul_ne_zero ht hj
  have := step _ hent
  rwa [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, htO.1, htO.2] at this

end DiscreteGroups.sglob.LConv

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvIrr
section
noncomputable section

open scoped InnerProductSpace
open UniformSpace GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv.IrreduciblePresentation

variable {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (hB : IsPsd B)
variable {G : Type} [Group G] (ρ : Representation ℂ G M) (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)

include hinv in
theorem closure_top (hext : IsExtremeForm ρ B) (Z : Submodule ℂ M) (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z)
    (z₀ : M) (hz₀ : z₀ ∈ Z) (hne : B z₀ z₀ ≠ 0) (y : Hs B hB) :
    y ∈ (Z.map (iota B hB)).topologicalClosure := by
  set W := (Z.map (iota B hB)).topologicalClosure with hW
  have : CompleteSpace W := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hWinv : ∀ g, ∀ w ∈ W, pi B hB ρ hinv g w ∈ W := by
    intro g w hw
    rw [← SetLike.mem_coe, hW, Submodule.topologicalClosure_coe] at hw ⊢
    refine map_mem_closure (pi B hB ρ hinv g).continuous hw fun v hv => ?_
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hv
    exact Submodule.mem_map.2 ⟨ρ g z, hZ g z hz, (pi_iota B hB ρ hinv g z).symm⟩
  have hP : ∀ g, W.starProjection * pi B hB ρ hinv g = pi B hB ρ hinv g * W.starProjection := by
    intro g
    refine ContinuousLinearMap.ext fun v => ?_
    show W.starProjection (pi B hB ρ hinv g v) = pi B hB ρ hinv g (W.starProjection v)
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact hWinv g _ (W.starProjection_apply_mem v)
    · intro w hw
      rw [← map_sub, inner_left]
      exact W.starProjection_inner_eq_zero v _ (hWinv _ _ hw)
  obtain ⟨c, hc⟩ := commutant B hB ρ hinv hext _ hP
  have hι0 : iota B hB z₀ ≠ 0 := fun h => hne (by rw [← inner_iota B hB, h, inner_zero_left])
  have hmem : iota B hB z₀ ∈ W := Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hz₀)
  have h1 : W.starProjection (iota B hB z₀) = iota B hB z₀ := Submodule.starProjection_eq_self_iff.2 hmem
  rw [hc] at h1
  have hc1 : c = 1 := by
    have e : (c - 1) • iota B hB z₀ = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]; simpa using h1
    rcases smul_eq_zero.1 e with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hι0
  apply Submodule.starProjection_eq_self_iff.1
  rw [hc, hc1, one_smul]; rfl

end DiscreteGroups.sglob.LConv.IrreduciblePresentation

namespace DiscreteGroups.sglob.LConv

open IrreduciblePresentation in
theorem extremeIrred : ExtremeIrred := by
  intro G M _ _ _ _ _ ρ hsm hK hAdm B hext Z hZ
  by_cases h0 : ∀ z ∈ Z, B z z = 0
  · exact Or.inl h0
  right
  simp only [not_forall, exists_prop] at h0
  obtain ⟨z₀, hz₀, hne⟩ := h0
  have hB : IsPsd B := ⟨hext.1.1, hext.1.2.1⟩
  have hinv := hext.1.2.2
  intro x
  obtain ⟨K, hKo, hKc, hxK⟩ := hK x
  obtain ⟨s, hs⟩ := hAdm K hKo hKc (Hs B hB) (pi B hB ρ hinv) (norm_pi B hB ρ hinv)
    (commutant B hB ρ hinv hext)
  set L : Submodule ℂ (Hs B hB) := (Z ⊓ fixSub ρ K).map (iota B hB) with hL
  have hle : L ≤ Submodule.span ℂ (s : Set (Hs B hB)) := by
    intro v hv
    obtain ⟨a, ⟨_, haK⟩, rfl⟩ := Submodule.mem_map.1 hv
    exact hs _ fun κ hκ => by rw [pi_iota, haK κ hκ]
  have : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hle
  have hcl : IsClosed (L : Set (Hs B hB)) := L.closed_of_finiteDimensional
  have hxL : iota B hB x ∈ L := by
    rw [← SetLike.mem_coe, ← hcl.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    have hxW := closure_top B hB ρ hinv hext Z hZ z₀ hz₀ hne (iota B hB x)
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hxW
    obtain ⟨_, hb, hd⟩ := hxW ε hε
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hb
    obtain ⟨a, haZ, haK, hda⟩ := avg_exists B hB ρ hinv hsm Z hZ K hKc x hxK z hz
    exact ⟨iota B hB a, Submodule.mem_map_of_mem ⟨haZ, haK⟩, lt_of_le_of_lt hda hd⟩
  obtain ⟨a, ⟨haZ, _⟩, ha⟩ := Submodule.mem_map.1 hxL
  refine ⟨a, haZ, ?_⟩
  rw [← inner_iota B hB, map_sub, ha, sub_self, inner_zero_left]

end DiscreteGroups.sglob.LConv
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LConvSepB
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker Topology

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}
  {ψ : AddChar k Circle}

def PosInt (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  IsInvIntegral I ∧ (∀ f, IsTestFun f → I (fun g => (starRingEnd ℂ) (f g)) = (starRingEnd ℂ) (I f)) ∧
    ∀ f, IsTestFun f → (∀ g, 0 ≤ (f g).re) → 0 ≤ (I f).re ∧ ((I f).re = 0 → ∀ g, (f g).re = 0)

theorem isTestFun_pair (x y : WT (m := m) ψ) :
    IsTestFun fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g := by
  have h := isTestFun_mul y (fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g))
    (fun u hu g => by
      show (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) (u * g)) =
        ((ψ⁻¹ (superDiag u) : Circle) : ℂ) * (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g)
      rw [WT.left x hu, map_mul, conj_psi]) (x.2.2.1.comp _)
  have e : (fun g => (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (y : GL (Fin m) k → ℂ) g) =
      fun g => (y : GL (Fin m) k → ℂ) g * (starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) :=
    funext fun g => mul_comm _ _
  rw [e]
  exact h

theorem isInvForm_formI {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I) :
    IsInvForm (rhoW ψ) (formI ψ I) := by
  refine ⟨fun x y => ?_, fun x => ?_, fun g x y => ?_⟩
  · rw [formI_apply, formI_apply, ← hI.2.1 _ (isTestFun_pair x y)]
    congr 1
    funext g
    simp only [map_mul, Complex.conj_conj]
    ring
  · exact (hI.2.2 _ (isTestFun_pair x x) fun g => by rw [conj_mul_self_re]; exact Complex.normSq_nonneg _).1
  · rw [formI_apply, formI_apply]
    simp only [rhoW_apply]
    exact hI.1 _ (isTestFun_pair x y) g

theorem formI_self_ne_zero {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I) {x : WT (m := m) ψ} (hx : x ≠ 0) :
    formI ψ I x x ≠ 0 := by
  intro h0
  apply hx
  have hn : ∀ g, 0 ≤ ((starRingEnd ℂ) ((x : GL (Fin m) k → ℂ) g) * (x : GL (Fin m) k → ℂ) g).re := fun g => by
    rw [conj_mul_self_re]; exact Complex.normSq_nonneg _
  have h := (hI.2.2 _ (isTestFun_pair x x) hn).2 (by rw [← formI_apply, h0, Complex.zero_re])
  refine Subtype.ext (funext fun g => ?_)
  have := h g
  rw [conj_mul_self_re] at this
  exact Complex.normSq_eq_zero.1 this

variable (ψ) in

def cK (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (K : Subgroup (GL (Fin m) k)) : ℂ :=
  formI ψ I (delta ψ K) (delta ψ K)

theorem cK_ne_zero {I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ} (hI : PosInt I) {K : Subgroup (GL (Fin m) k)}
    (hK : Good ψ K) : cK ψ I K ≠ 0 :=
  formI_self_ne_zero hI (delta_ne_zero hK)

theorem formI_delta_le (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) {K K' : Subgroup (GL (Fin m) k)} (hK : Good ψ K)
    (hK' : Good ψ K') (hle : K' ≤ K) : formI ψ I (delta ψ K) (delta ψ K') = cK ψ I K' := by
  rw [cK, formI_apply, formI_apply]
  congr 1
  funext g
  by_cases h : (delta ψ K' : GL (Fin m) k → ℂ) g = 0
  · simp [h]
  · rw [delta_eq_of_le hK hK' hle g h]

theorem rhoW_inv_delta_conj {K : Subgroup (GL (Fin m) k)} (hK : Good ψ K) {u : GL (Fin m) k}
    (hu : u ∈ unipB k (Fin m)) :
    rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)) =
      ((ψ⁻¹ (superDiag u) : Circle) : ℂ) • delta ψ K := by
  have hK' := good_conj hK hu
  have hfix : ∀ κ ∈ K, rhoW ψ κ (rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom))) =
      rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)) := by
    intro κ hκ
    rw [← Module.End.mul_apply, ← map_mul]
    have e1 : κ * u⁻¹ = u⁻¹ * (u * κ * u⁻¹) := by group
    have e2 : u⁻¹ * (u * κ * u⁻¹) * u = κ := by group
    rw [e1, map_mul, Module.End.mul_apply, rhoW_delta (mem_conj.2 (by rw [e2]; exact hκ))]
  have hs : ∀ g, (rhoW ψ u⁻¹ (delta ψ (K.map (MulAut.conj u).toMonoidHom)) : GL (Fin m) k → ℂ) g ≠ 0 →
      ∃ n ∈ unipB k (Fin m), ∃ κ ∈ K, g = n * κ := by
    intro g hg
    rw [rhoW_apply] at hg
    obtain ⟨n, hn, κ', hκ', he⟩ : ∃ n ∈ unipB k (Fin m), ∃ κ' ∈ K.map (MulAut.conj u).toMonoidHom,
        g * u⁻¹ = n * κ' := by
      by_contra h
      exact hg (delta_eq_zero h)
    refine ⟨n * u, (unipB k (Fin m)).mul_mem hn hu, u⁻¹ * κ' * u, mem_conj.1 hκ', ?_⟩
    calc g = g * u⁻¹ * u := by group
      _ = n * κ' * u := by rw [he]
      _ = n * u * (u⁻¹ * κ' * u) := by group
  rw [eq_smul_delta hK _ hfix hs, rhoW_apply, one_mul]
  congr 1
  have := delta_mul hK' ((unipB k (Fin m)).inv_mem hu) (K.map (MulAut.conj u).toMonoidHom).one_mem
  rw [mul_one] at this
  rw [this, superDiag_inv hu, AddChar.inv_apply]

end DiscreteGroups.sglob.LConv

end
end

