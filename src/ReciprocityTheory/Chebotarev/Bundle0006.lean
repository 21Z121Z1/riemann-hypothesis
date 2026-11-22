import ReciprocityTheory.Chebotarev.Bundle0005
import ReciprocityTheory.Chebotarev.UnitPart
import ReciprocityTheory.Chebotarev.DiscreteTopologyLatOf
import ReciprocityTheory.Chebotarev.Bundle0002

-- bundled from ReciprocityTheory.Chebotarev.EulerLim
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem exists_smooth {E : Type} [Field E] [NumberField E] (a : NZIdeal E) : ∃ S : Finset (Prm E), Smooth S a.1 := by
  have hfin := Ideal.finite_factors (R := 𝓞 E) (I := a.1) a.2
  exact ⟨hfin.toFinset, fun q hq => hfin.mem_toFinset.mpr hq⟩

theorem Smooth.mono {E : Type} [Field E] [NumberField E] {S T : Finset (Prm E)} {a : Ideal (𝓞 E)}
    (h : Smooth S a) (hST : S ⊆ T) : Smooth T a := fun q hq => hST (h q hq)

theorem euler_hasProd {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1) :
    HasProd (fun q : Prm E => (1 - f q.asIdeal)⁻¹) (∑' a : NZIdeal E, f a.1) := by
  unfold HasProd
  simp only [SummationFilter.unconditional_filter]
  have key : (fun S : Finset (Prm E) => ∏ q ∈ S, (1 - f q.asIdeal)⁻¹) =
      fun S => ∑' a : NZIdeal E, Set.indicator {a : NZIdeal E | Smooth S a.1} (fun a => f a.1) a := by
    funext S
    exact (euler_finite f hf1 hmul hsum hlt S).tsum_eq.symm
  rw [key]
  refine tendsto_tsum_of_dominated_convergence (bound := fun a : NZIdeal E => ‖f a.1‖) hsum ?_ ?_
  · intro a
    obtain ⟨S0, hS0⟩ := exists_smooth a
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop S0] with S hS
    have : a ∈ {a : NZIdeal E | Smooth S a.1} := Smooth.mono hS0 hS
    rw [Set.indicator_of_mem this]
  · exact Eventually.of_forall fun S a => norm_indicator_le_norm_self _ _

theorem euler_exp_log {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1) :
    Complex.exp (∑' q : Prm E, -Complex.log (1 - f q.asIdeal)) = ∑' a : NZIdeal E, f a.1 := by
  have hinj : Function.Injective (fun q : Prm E => (⟨q.asIdeal, q.ne_bot⟩ : NZIdeal E)) := by
    intro q q' h
    exact IsDedekindDomain.HeightOneSpectrum.ext (congrArg Subtype.val h)
  have hs1 : Summable (fun q : Prm E => ‖f q.asIdeal‖) := by
    have h := hsum.comp_injective hinj
    exact h
  have hs2 : Summable (fun q : Prm E => -f q.asIdeal) := (Summable.of_norm hs1).neg
  have hs3 : Summable (fun q : Prm E => -Complex.log (1 - f q.asIdeal)) := by
    have := (Complex.summable_log_one_add_of_summable hs2).neg
    simp only [← sub_eq_add_neg] at this
    exact this
  have hP := hs3.hasSum.cexp
  have hne : ∀ q : Prm E, 1 - f q.asIdeal ≠ 0 := by
    intro q h
    have h1 : f q.asIdeal = 1 := (sub_eq_zero.mp h).symm
    have := hlt q
    rw [h1, norm_one] at this
    exact lt_irrefl _ this
  have hP' : HasProd (fun q : Prm E => (1 - f q.asIdeal)⁻¹)
      (Complex.exp (∑' q : Prm E, -Complex.log (1 - f q.asIdeal))) := by
    have e : (Complex.exp ∘ fun q : Prm E => -Complex.log (1 - f q.asIdeal)) =
        fun q : Prm E => (1 - f q.asIdeal)⁻¹ := by
      funext q
      rw [Function.comp_apply, Complex.exp_neg, Complex.exp_log (hne q)]
    rw [e] at hP
    exact hP
  exact hP'.unique (euler_hasProd f hf1 hmul hsum hlt)

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.IdealLat
section
open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

theorem nzIdeal_ne_zero (a : NZIdeal E) : a.1 ≠ 0 := by
  intro h; exact a.2 (by rw [h]; rfl)

theorem cls_mul_eq_one_iff (a b : NZIdeal E) :
    cls a * cls b = 1 ↔ Submodule.IsPrincipal (a.1 * b.1) := by
  have hab : a.1 * b.1 ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (nzIdeal_ne_zero a) (nzIdeal_ne_zero b))
  rw [← ClassGroup.mk0_eq_one_iff hab]
  unfold cls
  rw [← map_mul]
  rfl

theorem norm_embZ_ne_zero {g : 𝓞 E} (hg : g ≠ 0) : mixedEmbedding.norm (embZ g) ≠ 0 := by
  rw [norm_embZ]
  have : Algebra.norm ℤ g ≠ 0 := Algebra.norm_ne_zero_iff.2 hg
  exact abs_ne_zero.2 (Int.cast_ne_zero.2 this)

theorem uphi_embZ_zero : uphi (embZ (0 : 𝓞 E)) = 0 := by
  apply uphi_of_norm_eq_zero
  rw [norm_embZ]; simp

theorem tsum_class_eq_latSum (b : NZIdeal E) (H : Ideal (𝓞 E) → ℂ)
    (hH : Summable fun a : NZIdeal E => H (a.1 * b.1)) :
    ∑' a : NZIdeal E, (if cls a * cls b = 1 then H (a.1 * b.1) else 0) =
      ((torsionOrder E : ℕ) : ℂ)⁻¹ *
        ∑' α : b.1, ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * H (Ideal.span {(α : 𝓞 E)}) := by
  set S : Set (NZIdeal E) := {a | cls a * cls b = 1} with hS
  have hP : ∀ a : S, ∃ g : 𝓞 E, Ideal.span {g} = a.1.1 * b.1 := by
    intro a
    rcases ((cls_mul_eq_one_iff a.1 b).1 a.2) with ⟨g, hg⟩
    exact ⟨g, hg.symm⟩
  choose gen hgen using hP
  have gen_mem : ∀ a, gen a ∈ b.1 := fun a => by
    rw [← Ideal.span_singleton_le_iff_mem, hgen]; exact Ideal.mul_le_inf.trans inf_le_right
  have gen_ne : ∀ a, gen a ≠ 0 := fun a h => by
    have := hgen a
    rw [h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact mul_ne_zero (nzIdeal_ne_zero a.1) (nzIdeal_ne_zero b) (by rw [← this]; rfl)
  have hb0 : b.1 ≠ 0 := nzIdeal_ne_zero b
  let Ψ : S × (𝓞 E)ˣ → b.1 := fun p => ⟨(p.2 : 𝓞 E) * gen p.1, b.1.mul_mem_left _ (gen_mem p.1)⟩
  have hspan : ∀ p : S × (𝓞 E)ˣ, Ideal.span {((Ψ p : b.1) : 𝓞 E)} = p.1.1.1 * b.1 := fun p => by
    show Ideal.span {(p.2 : 𝓞 E) * gen p.1} = _
    rw [Ideal.span_singleton_mul_left_unit p.2.isUnit, hgen]
  have hinj : Function.Injective Ψ := by
    rintro ⟨a, u⟩ ⟨a', u'⟩ h
    have h1 : a.1.1 * b.1 = a'.1.1 * b.1 := by
      rw [← hspan (a, u), ← hspan (a', u'), h]
    have h2 : a = a' := Subtype.ext (Subtype.ext (mul_right_cancel₀ hb0 h1))
    subst h2
    have h3 : (u : 𝓞 E) * gen a = u' * gen a := congrArg Subtype.val h
    rw [Units.ext (mul_right_cancel₀ (gen_ne a) h3)]
  let F : b.1 → ℂ := fun α => ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * H (Ideal.span {(α : 𝓞 E)})
  have hsupp : Function.support F ⊆ Set.range Ψ := by
    intro α hα
    have hα0 : (α : 𝓞 E) ≠ 0 := by
      intro h0; apply hα; simp only [F, h0, uphi_embZ_zero]; simp
    have hle : Ideal.span {(α : 𝓞 E)} ≤ b.1 := (Ideal.span_singleton_le_iff_mem _).2 α.2
    obtain ⟨c, hc⟩ := Ideal.dvd_iff_le.2 hle
    have hcne : c ≠ ⊥ := by
      rintro rfl
      rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hc
      exact hα0 hc
    have hcS : (⟨c, hcne⟩ : NZIdeal E) ∈ S := by
      show cls _ * cls b = 1
      rw [cls_mul_eq_one_iff]
      exact ⟨⟨α, by rw [mul_comm, ← hc]⟩⟩
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.1
      ((hgen ⟨_, hcS⟩).trans (by rw [mul_comm, ← hc]) : Ideal.span {gen ⟨_, hcS⟩} = Ideal.span {(α : 𝓞 E)})
    refine ⟨(⟨_, hcS⟩, u), Subtype.ext ?_⟩
    show (u : 𝓞 E) * gen _ = α
    rw [mul_comm]; exact hu
  rw [← hinj.tsum_eq hsupp]
  let f : S × (𝓞 E)ˣ → ℂ := fun p => ((uphi (p.2 • embZ (gen p.1)) : ℝ) : ℂ) * H (p.1.1.1 * b.1)
  have hFf : ∀ p, F (Ψ p) = f p := fun p => by
    simp only [F, f]
    rw [hspan p]
    show ((uphi (embZ ((p.2 : 𝓞 E) * gen p.1)) : ℝ) : ℂ) * _ = _
    rw [unit_smul_embZ]
  simp only [hFf]
  have hw : ∀ a : S, HasSum (fun u : (𝓞 E)ˣ => uphi (u • embZ (gen a))) (torsionOrder E : ℝ) :=
    fun a => hasSum_uphi_unit_smul _ (norm_embZ_ne_zero (gen_ne a))
  have hfib : ∀ a : S, HasSum (fun u => f (a, u)) (((torsionOrder E : ℕ) : ℂ) * H (a.1.1 * b.1)) := by
    intro a
    have := (Complex.hasSum_ofReal.2 (hw a)).mul_right (H (a.1.1 * b.1))
    simpa [f] using this
  have hnfib : ∀ a : S, HasSum (fun u => ‖f (a, u)‖) ((torsionOrder E : ℝ) * ‖H (a.1.1 * b.1)‖) := by
    intro a
    have := (hw a).mul_right ‖H (a.1.1 * b.1)‖
    have e : (fun u => ‖f (a, u)‖) = fun i => uphi (i • embZ (gen a)) * ‖H (a.1.1 * b.1)‖ := by
      funext u
      simp only [f, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (uphi_nonneg _)]
    rw [e]; exact this
  have hHn : Summable fun a : S => (torsionOrder E : ℝ) * ‖H (a.1.1 * b.1)‖ :=
    ((summable_norm_iff.2 hH).subtype S).mul_left _
  have hfs : Summable f := by
    apply Summable.of_norm
    rw [summable_prod_of_nonneg (fun p => norm_nonneg _)]
    refine ⟨fun a => (hnfib a).summable, ?_⟩
    simpa only [(hnfib _).tsum_eq] using hHn
  have hsum := hfs.hasSum.prod_fiberwise hfib
  rw [← hsum.tsum_eq, tsum_mul_left, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast torsionOrder_ne_zero E), one_mul,
    tsum_subtype S (fun a => H (a.1 * b.1))]
  congr 1

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.MeanZero
section
open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

theorem isCoprime_span_mul_of_coprime_absNorm {l : ℕ} (B C : Ideal (𝓞 E))
    (hcop : Nat.Coprime (Ideal.absNorm C) (l * Ideal.absNorm B)) :
    IsCoprime (Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B) C := by
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  have h2 : Nat.Coprime (Ideal.absNorm C) ((l * Ideal.absNorm B) * Ideal.absNorm B) :=
    Nat.Coprime.mul_right hcop (Nat.Coprime.coprime_dvd_right (dvd_mul_left _ _) hcop)
  obtain ⟨u, v, huv⟩ : IsCoprime (Ideal.absNorm C : ℤ)
      (((l * Ideal.absNorm B) * Ideal.absNorm B : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr h2
  have hmem1 : ((l * Ideal.absNorm B : ℕ) : 𝓞 E) * ((Ideal.absNorm B : ℕ) : 𝓞 E) ∈
      Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B :=
    Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.absNorm_mem B)
  have hmem2 : ((Ideal.absNorm C : ℕ) : 𝓞 E) ∈ C := Ideal.absNorm_mem C
  have h1 : (1 : 𝓞 E) = (v : 𝓞 E) * (((l * Ideal.absNorm B : ℕ) : 𝓞 E) * ((Ideal.absNorm B : ℕ) : 𝓞 E))
      + (u : 𝓞 E) * ((Ideal.absNorm C : ℕ) : 𝓞 E) := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) huv
    push_cast at this ⊢
    linear_combination -this
  rw [h1]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hmem1))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ hmem2))

theorem sum_crt_weight_eq_zero {R : Type*} [CommRing R] (I C : Ideal R) (hIC : IsCoprime I C)
    [Fintype (R ⧸ I * C)] [Fintype (R ⧸ I)] [Fintype (R ⧸ C)] (f : R → ℂ)
    (hf : ∀ a b, a - b ∈ I → f a = f b) (σ : R ⧸ I * C → R)
    (hσ : ∀ y, Ideal.Quotient.mk _ (σ y) = y) :
    ∑ y, f (σ y) * (1 - (Fintype.card (R ⧸ C) : ℂ) * if σ y ∈ C then 1 else 0) = 0 := by
  set e := Ideal.quotientMulEquivQuotientProd I C hIC
  have hfst : ∀ p, Ideal.Quotient.mk I (σ (e.symm p)) = p.1 := by
    intro p
    have := congrArg Prod.fst (e.apply_symm_apply p)
    rw [← hσ (e.symm p), Ideal.quotientMulEquivQuotientProd_fst, Ideal.Quotient.factor_mk] at this
    exact this
  have hsnd : ∀ p, Ideal.Quotient.mk C (σ (e.symm p)) = p.2 := by
    intro p
    have := congrArg Prod.snd (e.apply_symm_apply p)
    rw [← hσ (e.symm p), Ideal.quotientMulEquivQuotientProd_snd, Ideal.Quotient.factor_mk] at this
    exact this
  rw [← (e.symm.toEquiv).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun u _ => ?_
  have hfe : ∀ v, f (σ (e.symm (u, v))) = f (σ (e.symm (u, 0))) := by
    intro v
    apply hf
    rw [← Ideal.Quotient.eq, hfst, hfst]
  have hC : ∀ v, σ (e.symm (u, v)) ∈ C ↔ v = 0 := by
    intro v
    rw [← Ideal.Quotient.eq_zero_iff_mem, hsnd]
  calc ∑ v, f (σ (e.symm.toEquiv (u, v))) *
        (1 - (Fintype.card (R ⧸ C) : ℂ) * if σ (e.symm.toEquiv (u, v)) ∈ C then 1 else 0)
      = ∑ v : R ⧸ C, f (σ (e.symm (u, 0))) *
        (1 - (Fintype.card (R ⧸ C) : ℂ) * if v = 0 then 1 else 0) :=
        Finset.sum_congr rfl fun v _ => by
          simp only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv]
          rw [hfe v]
          simp only [hC v]
    _ = f (σ (e.symm (u, 0))) * ∑ v : R ⧸ C, (1 - (Fintype.card (R ⧸ C) : ℂ) * if v = 0 then 1 else 0) := by
        rw [Finset.mul_sum]
    _ = 0 := by
        simp [Finset.sum_sub_distrib]

theorem exists_reps_meanZero {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    latOf (mbc l b.1 c.1) ≤ latOf b.1 ∧
    ∃ reps : Finset (mixedSpace E), (∀ β ∈ reps, β ∈ latOf b.1) ∧
      (∀ α ∈ latOf b.1, ∃ l' ∈ latOf (mbc l b.1 c.1), ∃ β ∈ reps, α = l' + β) ∧
      (∀ β₁ ∈ reps, ∀ β₂ ∈ reps, β₁ - β₂ ∈ latOf (mbc l b.1 c.1) → β₁ = β₂) ∧
      (∀ l' ∈ latOf (mbc l b.1 c.1), ∀ β ∈ reps, cfun χ b.1 c.1 (l' + β) = cfun χ b.1 c.1 β) ∧
      ∑ β ∈ reps, cfun χ b.1 c.1 β = 0 := by
  have hM : mbc l b.1 c.1 = Ideal.span {((l * Ideal.absNorm b.1 : ℕ) : 𝓞 E)} * b.1 * c.1 := rfl
  rw [hM]
  obtain ⟨B, hB0⟩ := b
  obtain ⟨C, hC0⟩ := c
  simp only at hcop ⊢
  set I : Ideal (𝓞 E) := Ideal.span {((l * Ideal.absNorm B : ℕ) : 𝓞 E)} * B with hI
  have hIC : IsCoprime I C := isCoprime_span_mul_of_coprime_absNorm B C hcop
  have hIB : I ≤ B := Ideal.mul_le_right
  have hIspan : I ≤ Ideal.span {((((l : ℤ) * (Ideal.absNorm B : ℤ) : ℤ)) : 𝓞 E)} := by
    have : ((((l : ℤ) * (Ideal.absNorm B : ℤ) : ℤ)) : 𝓞 E) = ((l * Ideal.absNorm B : ℕ) : 𝓞 E) := by
      push_cast; rfl
    rw [this]; exact Ideal.mul_le_left
  have hMB : I * C ≤ B := le_trans Ideal.mul_le_left hIB
  have hMBC : I * C ≤ B * C := Ideal.mul_mono_left hIB
  have hBC : B * C = B ⊓ C := Ideal.mul_eq_inf_of_coprime
    (Ideal.isCoprime_iff_sup_eq.mp (hIC.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hIB)))
  have hl0 : (l * Ideal.absNorm B : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (Fact.out : l.Prime).ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨by exact_mod_cast hl0, hB0⟩
  have hM0 : I * C ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]; exact ⟨hI0, hC0⟩
  have := Ideal.finiteQuotientOfFreeOfNeBot (I * C) hM0
  have := Ideal.finiteQuotientOfFreeOfNeBot I hI0
  have := Ideal.finiteQuotientOfFreeOfNeBot C hC0
  let : Fintype (𝓞 E ⧸ I * C) := Fintype.ofFinite _
  let : Fintype (𝓞 E ⧸ I) := Fintype.ofFinite _
  let : Fintype (𝓞 E ⧸ C) := Fintype.ofFinite _
  have hsurj : Function.Surjective (Ideal.Quotient.mk (I * C)) := Ideal.Quotient.mk_surjective
  obtain ⟨σ, hσ⟩ : ∃ σ : 𝓞 E ⧸ I * C → 𝓞 E, ∀ y, Ideal.Quotient.mk (I * C) (σ y) = y :=
    ⟨_, Function.surjInv_eq hsurj⟩
  have hσinj : Function.Injective σ := fun y₁ y₂ h => by rw [← hσ y₁, ← hσ y₂, h]
  have hkey : ∀ y₁ y₂, σ y₁ - σ y₂ ∈ I * C → y₁ = y₂ := by
    intro y₁ y₂ h
    rw [← hσ y₁, ← hσ y₂]; exact Ideal.Quotient.eq.mpr h

  set F : 𝓞 E → ℂ := fun α => χ (((Algebra.norm ℤ α / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) *
    (1 - (Ideal.absNorm C : ℂ) * (if α ∈ B * C then 1 else 0)) with hF
  have hcf : ∀ α, cfun χ B C (embZ α) = F α := by
    intro α; simp only [cfun, preZ_embZ, hF]
  have hchi : ∀ a a', a ∈ B → a' ∈ B → a - a' ∈ I →
      χ (((Algebra.norm ℤ a / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) =
      χ (((Algebra.norm ℤ a' / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) := by
    intro a a' ha ha' h
    congr 1
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mpr (norm_div_absNorm_modEq (l : ℤ) ha ha' (hIspan h))
  have hper : ∀ μ ∈ I * C, ∀ a ∈ B, F (μ + a) = F a := by
    intro μ hμ a ha
    simp only [hF]
    rw [hchi (μ + a) a (B.add_mem (hMB hμ) ha) ha (by rw [add_sub_cancel_right]; exact Ideal.mul_le_left hμ)]
    simp only [Ideal.add_mem_iff_right _ (hMBC hμ)]
  set reps : Finset (mixedSpace E) :=
    (Finset.univ.filter fun y => σ y ∈ B).image (fun y => embZ (σ y)) with hreps
  have hmemreps : ∀ β ∈ reps, ∃ y, σ y ∈ B ∧ embZ (σ y) = β := by
    intro β hβ
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hβ
    exact ⟨y, (Finset.mem_filter.mp hy).2, rfl⟩
  refine ⟨latOf_mono hMB, reps, ?_, ?_, ?_, ?_, ?_⟩
  · intro β hβ
    obtain ⟨y, hy, rfl⟩ := hmemreps β hβ
    exact mem_latOf.mpr ⟨_, hy, rfl⟩
  · intro α hα
    obtain ⟨a, ha, rfl⟩ := mem_latOf.mp hα
    have hya : σ (Ideal.Quotient.mk _ a) - a ∈ I * C := Ideal.Quotient.eq.mp (hσ _)
    have hyB : σ (Ideal.Quotient.mk _ a) ∈ B := by
      have := B.add_mem (hMB hya) ha
      rwa [sub_add_cancel] at this
    refine ⟨embZ (a - σ (Ideal.Quotient.mk _ a)), mem_latOf.mpr ⟨_, ?_, rfl⟩,
      embZ (σ (Ideal.Quotient.mk _ a)), ?_, ?_⟩
    · have := (I * C).neg_mem hya
      rwa [neg_sub] at this
    · exact Finset.mem_image.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyB⟩, rfl⟩
    · rw [map_sub, sub_add_cancel]
  · intro β₁ h₁ β₂ h₂ hd
    obtain ⟨y₁, -, rfl⟩ := hmemreps β₁ h₁
    obtain ⟨y₂, -, rfl⟩ := hmemreps β₂ h₂
    obtain ⟨μ, hμ, hμe⟩ := mem_latOf.mp hd
    have : μ = σ y₁ - σ y₂ := embZ_injective (by rw [hμe, map_sub])
    rw [hkey y₁ y₂ (this ▸ hμ)]
  · intro l' hl' β hβ
    obtain ⟨y, hy, rfl⟩ := hmemreps β hβ
    obtain ⟨μ, hμ, rfl⟩ := mem_latOf.mp hl'
    rw [← map_add, hcf, hcf, hper μ hμ _ hy]
  · rw [hreps, Finset.sum_image (fun y₁ _ y₂ _ h => hσinj (embZ_injective h))]
    simp only [hcf]
    rw [Finset.sum_filter]
    set f : 𝓞 E → ℂ := fun a => if a ∈ B then
      χ (((Algebra.norm ℤ a / (Ideal.absNorm B : ℤ) : ℤ)) : ZMod l) else 0 with hf
    have hfper : ∀ a a', a - a' ∈ I → f a = f a' := by
      intro a a' h
      have hiff : a ∈ B ↔ a' ∈ B := by
        have h' := hIB h
        constructor
        · intro ha; have := B.sub_mem ha h'; rwa [sub_sub_cancel] at this
        · intro ha'; have := B.add_mem h' ha'; rwa [sub_add_cancel] at this
      simp only [hf]
      by_cases ha : a ∈ B
      · rw [if_pos ha, if_pos (hiff.mp ha), hchi a a' ha (hiff.mp ha) h]
      · rw [if_neg ha, if_neg (fun h' => ha (hiff.mpr h'))]
    have hcard : (Ideal.absNorm C : ℂ) = (Fintype.card (𝓞 E ⧸ C) : ℂ) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    refine (Finset.sum_congr rfl fun y _ => ?_).trans (sum_crt_weight_eq_zero I C hIC f hfper σ hσ)
    by_cases hy : σ y ∈ B
    · simp only [hf, hF, ← hcard, if_pos hy, hBC, Ideal.mem_inf, hy, true_and, if_true]
    · simp only [hf, if_neg hy, zero_mul]

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.Support
section
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

theorem exists_logMap_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ x : mixedSpace E, (∀ i, |ucoord x i| < 1) →
    ∀ w : {w : InfinitePlace E // w ≠ w₀}, |logMap x w| ≤ B := by
  set b := (basisUnitLattice E).ofZLatticeBasis ℝ (unitLattice E) with hb
  refine ⟨∑ i, ‖b i‖, Finset.sum_nonneg fun i _ => norm_nonneg _, fun x hx w => ?_⟩
  have hsum : (∑ i, ucoord x i • b i) = logMap x := by
    simpa [ucoord, hb] using b.sum_repr (logMap x)
  calc |logMap x w| = ‖logMap x w‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖logMap x‖ := norm_le_pi_norm (logMap x) w
    _ = ‖∑ i, ucoord x i • b i‖ := by rw [hsum]
    _ ≤ ∑ i, ‖ucoord x i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖b i‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [_root_.norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _) (hx i).le

theorem sum_mult_logDev {x : mixedSpace E} (hx : mixedEmbedding.norm x ≠ 0) :
    ∑ w : InfinitePlace E, (w.mult : ℝ) * (Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ E : ℝ)⁻¹) = 0 := by
  have hne := mixedEmbedding.norm_ne_zero_iff.mp hx
  have hlog : Real.log (mixedEmbedding.norm x) =
      ∑ w : InfinitePlace E, (w.mult : ℝ) * Real.log (normAtPlace w x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod (fun w _ => pow_ne_zero _ (hne w))]
    simp [Real.log_pow]
  have hd : (Module.finrank ℚ E : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := E)).ne'
  have hm : (∑ w : InfinitePlace E, (w.mult : ℝ)) = Module.finrank ℚ E := by
    exact_mod_cast InfinitePlace.sum_mult_eq
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← hlog, ← Finset.sum_mul, hm]
  field_simp
  ring

theorem exists_logDev_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : mixedSpace E, uphi x ≠ 0 →
    mixedEmbedding.norm x ≠ 0 ∧ ∀ w : InfinitePlace E, |Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ E : ℝ)⁻¹| ≤ C := by
  obtain ⟨B, hB0, hB⟩ := exists_logMap_bound (E := E)
  refine ⟨Fintype.card (InfinitePlace E) * B, by positivity, fun x hx => ?_⟩
  have hN : mixedEmbedding.norm x ≠ 0 := fun h => hx (by simp [uphi, h])
  have hT : Tent (ucoord x) ≠ 0 := by simpa [uphi, hN] using hx
  have hc : ∀ i, |ucoord x i| < 1 := abs_lt_one_of_Tent_ne_zero hT
  refine ⟨hN, fun w => ?_⟩
  set D : InfinitePlace E → ℝ := fun w => Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ E : ℝ)⁻¹ with hD
  have hlm : ∀ v : {w : InfinitePlace E // w ≠ w₀}, logMap x v = (v.1.mult : ℝ) * D v.1 := fun v => rfl
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace E) := by
    exact_mod_cast Fintype.card_pos

  have key : |(w.mult : ℝ) * D w| ≤ Fintype.card (InfinitePlace E) * B := by
    by_cases hw : w = w₀
    · rw [hw]
      have h0 := sum_mult_logDev hN
      rw [Fintype.sum_eq_add_sum_subtype_ne _ (w₀ : InfinitePlace E)] at h0
      have h1 : ((w₀ : InfinitePlace E).mult : ℝ) * D w₀ = -∑ v : {w : InfinitePlace E // w ≠ w₀}, logMap x v := by
        simp only [hlm]; linarith
      rw [h1, abs_neg]
      calc |∑ v : {w : InfinitePlace E // w ≠ w₀}, logMap x v|
          ≤ ∑ v : {w : InfinitePlace E // w ≠ w₀}, |logMap x v| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _v : {w : InfinitePlace E // w ≠ w₀}, B := Finset.sum_le_sum fun v _ => hB x hc v
        _ = Fintype.card {w : InfinitePlace E // w ≠ w₀} * B := by simp
        _ ≤ Fintype.card (InfinitePlace E) * B := by
          gcongr
          exact_mod_cast Fintype.card_subtype_le _
    · have := hB x hc ⟨w, hw⟩
      rw [hlm] at this
      exact this.trans (le_mul_of_one_le_left hB0 hcard)
  have hm : (1 : ℝ) ≤ w.mult := InfinitePlace.one_le_mult
  rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < w.mult)] at key
  calc |D w| ≤ (w.mult : ℝ) * |D w| := le_mul_of_one_le_left (abs_nonneg _) hm
    _ ≤ _ := key

theorem exists_support_bound : ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ 1 ∧ ∀ x : mixedSpace E, uphi x ≠ 0 →
    (∀ w : InfinitePlace E, c₀ * ‖x‖ ≤ normAtPlace w x) ∧
      c₀ ^ Module.finrank ℚ E * ‖x‖ ^ Module.finrank ℚ E ≤ mixedEmbedding.norm x := by
  obtain ⟨C, hC0, hC⟩ := exists_logDev_bound (E := E)
  refine ⟨Real.exp (-(2 * C)), Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), fun x hx => ?_⟩
  obtain ⟨hN, hD⟩ := hC x hx
  have hpos : ∀ w, 0 < normAtPlace w x := fun w =>
    lt_of_le_of_ne (normAtPlace_nonneg w x) (mixedEmbedding.norm_ne_zero_iff.mp hN w).symm
  have h1 : ∀ w, Real.exp (-(2 * C)) * ‖x‖ ≤ normAtPlace w x := by
    intro w
    obtain ⟨w', -, hw'⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun w => normAtPlace w x)
    rw [norm_eq_sup'_normAtPlace, hw']
    have a := hD w
    have b := hD w'
    rw [abs_le] at a b
    have hl : Real.log (normAtPlace w' x) - 2 * C ≤ Real.log (normAtPlace w x) := by linarith
    calc Real.exp (-(2 * C)) * normAtPlace w' x
        = Real.exp (Real.log (normAtPlace w' x) - 2 * C) := by
          rw [Real.exp_sub, Real.exp_log (hpos w'), Real.exp_neg]; ring
      _ ≤ Real.exp (Real.log (normAtPlace w x)) := Real.exp_le_exp.mpr hl
      _ = normAtPlace w x := Real.exp_log (hpos w)
  refine ⟨h1, ?_⟩
  rw [← mul_pow, mixedEmbedding.norm_apply, ← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
  exact pow_le_pow_left₀ (by positivity) (h1 w) _

end ReciprocityTheory.Cheb
end

