import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3452
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3007
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0838
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3455
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturated
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3456
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3439

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjInvariantTraceGeneratorLocal
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.RealTheta

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem bar_algebraMap (H : Host E) (r : 𝓞 (maximalRealSubfield E)) :
    H.bar (algebraMap _ (𝓞 E) r) = algebraMap _ (𝓞 E) r := by
  apply RingOfIntegers.ext
  rw [H.bar_eq]
  have h1 : ((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) r : 𝓞 E) : E) =
      algebraMap (maximalRealSubfield E) E (algebraMap (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) r) := by
    rw [← IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) E]
    exact (IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (𝓞 E) E r).symm
  rw [h1]
  exact (IsCMField.complexConj E).commutes _

theorem sub_bar_mem_pow_succ (H : Host E) (𝔭 : Ideal (𝓞 E)) (n : ℕ) (hn : 1 ≤ n)
    (h : ∀ c, c - H.bar c ∈ 𝔭 ^ n) (c : 𝓞 E) : c - H.bar c ∈ 𝔭 ^ (n + 1) := by
  haveI := H.unram
  let L : 𝓞 E →ₗ[𝓞 (maximalRealSubfield E)] (𝓞 E ⧸ 𝔭 ^ (n + 1)) :=
    { toFun := fun c => Ideal.Quotient.mk _ (c - H.bar c)
      map_add' := fun a b => by rw [← map_add, map_add H.bar]; congr 1; ring
      map_smul' := fun r a => by
        rw [Algebra.smul_def, map_mul, bar_algebraMap, ← mul_sub, RingHom.id_apply, Algebra.smul_def, map_mul,
          Ideal.Quotient.mk_algebraMap] }
  let D : Derivation (𝓞 (maximalRealSubfield E)) (𝓞 E) (𝓞 E ⧸ 𝔭 ^ (n + 1)) :=
    Derivation.mk' L fun a b => by
      show Ideal.Quotient.mk _ (a * b - H.bar (a * b)) =
        a • Ideal.Quotient.mk _ (b - H.bar b) + b • Ideal.Quotient.mk _ (a - H.bar a)
      rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, ← map_mul, ← map_add,
        Ideal.Quotient.eq]
      have hab : (a - H.bar a) * (b - H.bar b) ∈ 𝔭 ^ (n + 1) :=
        Ideal.pow_le_pow_right (by omega : n + 1 ≤ n + n) (by rw [pow_add]; exact Ideal.mul_mem_mul (h a) (h b))
      have : a * b - H.bar (a * b) - (a * (b - H.bar b) + b * (a - H.bar a)) = -((a - H.bar a) * (b - H.bar b)) := by
        rw [map_mul]; ring
      rw [this]; exact neg_mem hab
  have hD : D c = 0 := by
    rw [← Derivation.liftKaehlerDifferential_comp_D, Subsingleton.elim (KaehlerDifferential.D _ _ c) 0, map_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.1 hD

theorem exists_sub_bar_notMem (H : Host E) {𝔭 : Ideal (𝓞 E)} (h𝔭 : 𝔭 ≠ ⊤) : ∃ c, c - H.bar c ∉ 𝔭 := by
  by_contra! h
  have key : ∀ n : ℕ, ∀ c, c - H.bar c ∈ 𝔭 ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih => exact sub_bar_mem_pow_succ H 𝔭 (n + 1) (by omega) ih
  have h0 : H.rt - H.bar H.rt = 0 := by
    have hm : H.rt - H.bar H.rt ∈ ⨅ i, 𝔭 ^ i :=
      Ideal.mem_iInf.2 fun i => Ideal.pow_le_pow_right (Nat.le_succ i) (key i _)
    rwa [Ideal.iInf_pow_eq_bot_of_isDomain 𝔭 h𝔭, Ideal.mem_bot] at hm
  rw [GlobalTheory.CharRank.bar_rt_neg, sub_neg_eq_add, ← two_mul] at h0
  have hrt : H.rt = 0 := (mul_eq_zero.1 h0).resolve_left two_ne_zero
  have hd := H.rt_sq
  rw [hrt, zero_pow two_ne_zero, zero_eq_neg, Nat.cast_eq_zero] at hd
  exact H.d_prime.ne_zero hd

end GlobalTheory.RealTheta

namespace GlobalTheory.RealTheta

open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_trace_eq (ψ : 𝓞 E →+ ℤ) : ∃ δ : E, ∀ u : 𝓞 E, ((ψ u : ℤ) : ℚ) = Algebra.trace ℚ E (δ * u) := by
  let f : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => (ψ (RingOfIntegers.basis E i) : ℚ))
  obtain ⟨δ, hδ⟩ := ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).surjective f
  refine ⟨δ, fun u => ?_⟩
  have h1 : Algebra.trace ℚ E (δ * u) = f u := by
    rw [← hδ, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply]
  rw [h1]
  have h2 : ((Int.castAddHom ℚ).comp ψ).toIntLinearMap =
      (f.toAddMonoidHom.comp (algebraMap (𝓞 E) E).toAddMonoidHom).toIntLinearMap := by
    refine (RingOfIntegers.basis E).ext fun i => ?_
    simp [f, ← integralBasis_apply]
  exact (LinearMap.congr_fun h2 u)

open FractionalIdeal in

theorem exists_local_gen {M : FractionalIdeal (𝓞 E)⁰ E} (hM : M ≠ 0) {𝔭 : Ideal (𝓞 E)} {δ : E} (hδ : δ ∈ M)
    (hδ' : δ ∉ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M) :
    ∃ s : 𝓞 E, s ∉ 𝔭 ∧ ∀ x ∈ M, ∃ t : 𝓞 E, (s : E) * x = δ * t := by
  set I := spanSingleton (𝓞 E)⁰ δ * M⁻¹ with hI
  have hIM : I * M = spanSingleton (𝓞 E)⁰ δ := by
    rw [hI, mul_assoc, inv_mul_cancel₀ hM, mul_one]
  have hI1 : I ≤ 1 := by
    rw [← mul_inv_cancel₀ hM, hI]
    exact mul_le_mul_left (spanSingleton_le_iff_mem.2 hδ) _
  have hnot : ¬ I ≤ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) := by
    intro h
    apply hδ'
    have : spanSingleton (𝓞 E)⁰ δ ≤ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := hIM ▸ mul_le_mul_left h M
    exact spanSingleton_le_iff_mem.1 this
  obtain ⟨y, hyI, hy𝔭⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨s, rfl⟩ := (mem_one_iff _).1 (hI1 hyI)
  refine ⟨s, fun hs => hy𝔭 ((mem_coeIdeal _).2 ⟨s, hs, rfl⟩), fun x hx => ?_⟩
  have : algebraMap (𝓞 E) E s * x ∈ spanSingleton (𝓞 E)⁰ δ := hIM ▸ mul_mem_mul hyI hx
  obtain ⟨t, ht⟩ := (mem_spanSingleton _).1 this
  exact ⟨t, by rw [← ht, Algebra.smul_def, mul_comm]⟩

open FractionalIdeal in

theorem exists_mem_notMem_mul {M : FractionalIdeal (𝓞 E)⁰ E} (hM : M ≠ 0) {𝔭 : Ideal (𝓞 E)} (h𝔭 : 𝔭 ≠ ⊤) :
    ∃ x ∈ M, x ∉ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := by
  by_contra! h
  have hle : M ≤ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := fun x hx => h x hx
  have h1 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ 𝔭 := by
    have := mul_le_mul_left hle M⁻¹
    rwa [mul_assoc, mul_inv_cancel₀ hM, mul_one] at this
  rw [← coeIdeal_top, coeIdeal_le_coeIdeal E] at h1
  exact h𝔭 (top_le_iff.1 h1)

theorem fi_add_mem (N : FractionalIdeal (𝓞 E)⁰ E) {x y : E} (hx : x ∈ N) (hy : y ∈ N) : x + y ∈ N :=
  FractionalIdeal.mem_coe.1 (Submodule.add_mem _ (FractionalIdeal.mem_coe.2 hx) (FractionalIdeal.mem_coe.2 hy))

theorem fi_sub_mem (N : FractionalIdeal (𝓞 E)⁰ E) {x y : E} (hx : x ∈ N) (hy : y ∈ N) : x - y ∈ N :=
  FractionalIdeal.mem_coe.1 (Submodule.sub_mem _ (FractionalIdeal.mem_coe.2 hx) (FractionalIdeal.mem_coe.2 hy))

theorem fi_mul_mem (N : FractionalIdeal (𝓞 E)⁰ E) (a : 𝓞 E) {y : E} (hy : y ∈ N) : (a : E) * y ∈ N := by
  have := Submodule.smul_mem (N : Submodule (𝓞 E) E) a (FractionalIdeal.mem_coe.2 hy)
  rw [Algebra.smul_def] at this
  exact FractionalIdeal.mem_coe.1 this

theorem exists_real_notMem (H : Host E) {M : FractionalIdeal (𝓞 E)⁰ E} (hM : M ≠ 0)
    (hconj : ∀ x ∈ M, IsCMField.complexConj E x ∈ M) {𝔭 : Ideal (𝓞 E)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ δ ∈ M, IsCMField.complexConj E δ = δ ∧ δ ∉ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := by
  obtain ⟨x, hx, hx'⟩ := exists_mem_notMem_mul hM h𝔭.ne_top
  obtain ⟨c, hc⟩ := exists_sub_bar_notMem H h𝔭.ne_top
  have hcc : ∀ y, IsCMField.complexConj E (IsCMField.complexConj E y) = y := IsCMField.complexConj_apply_apply E
  have hbar : IsCMField.complexConj E (c : E) = (H.bar c : E) := (H.bar_eq c).symm
  by_cases h1 : x + IsCMField.complexConj E x ∈ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M
  · refine ⟨(c : E) * x + IsCMField.complexConj E ((c : E) * x), fi_add_mem _ (fi_mul_mem M c hx)
      (hconj _ (fi_mul_mem M c hx)), by rw [map_add, hcc, add_comm], fun h2 => hx' ?_⟩
    have h3 : ((c - H.bar c : 𝓞 E) : E) * x ∈ (𝔭 : FractionalIdeal (𝓞 E)⁰ E) * M := by
      have := fi_sub_mem _ h2 (fi_mul_mem _ (H.bar c) h1)
      convert this using 1
      rw [map_mul, hbar]; push_cast; ring
    obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv hc
    have hyi' := congrArg (fun z : 𝓞 E => (z : E)) hyi
    push_cast at hyi'
    have : x = (y : E) * (((c - H.bar c : 𝓞 E) : E) * x) + (i : E) * x := by
      push_cast; linear_combination (-x) * hyi'
    rw [this]
    exact fi_add_mem _ (fi_mul_mem _ y h3)
      (FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨i, hi, rfl⟩) hx)
  · exact ⟨x + IsCMField.complexConj E x, fi_add_mem _ hx (hconj x hx), by rw [map_add, hcc, add_comm], h1⟩

theorem trace_conj (y : E) : Algebra.trace ℚ E (IsCMField.complexConj E y) = Algebra.trace ℚ E y :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) y

theorem conj_mem_dual (H : Host E) {x : E} (hx : x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    IsCMField.complexConj E x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_dual (one_ne_zero : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0)] at hx ⊢
  intro a ha
  obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
  have := hx _ ((FractionalIdeal.mem_one_iff _).2 ⟨H.bar b, rfl⟩)
  rw [Algebra.traceForm_apply] at this ⊢
  convert this using 1
  rw [← trace_conj, map_mul, IsCMField.complexConj_apply_apply]
  exact congrArg (fun y => Algebra.trace ℚ E (x * y)) (H.bar_eq b).symm

end GlobalTheory.RealTheta

namespace GlobalTheory.RealTheta

open scoped nonZeroDivisors

theorem exists_bar_inv_trace_gen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ θ : 𝓞 E →+ ℤ, (∀ t, θ (H.bar t) = θ t) ∧ ∃ s : 𝓞 E, s ∉ 𝔭 ∧ H.bar s ∉ 𝔭 ∧
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) := by
  intro E _ _ _ H 𝔭 h𝔭
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  set M : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.dual ℤ ℚ 1 with hMdef
  have hM : M ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ h10
  obtain ⟨δ, hδM, hδc, hδ⟩ := exists_real_notMem H hM (fun x hx => conj_mem_dual H hx) h𝔭
  have hint : ∀ x ∈ M, ∀ u : 𝓞 E, ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ E (x * u) := by
    intro x hx u
    rw [hMdef, FractionalIdeal.mem_dual h10] at hx
    obtain ⟨z, hz⟩ := hx _ ((FractionalIdeal.mem_one_iff _).2 ⟨u, rfl⟩)
    exact ⟨z, by rw [← Algebra.traceForm_apply, ← hz]; simp⟩
  choose z hz using hint δ hδM
  let θ : 𝓞 E →+ ℤ := AddMonoidHom.mk' z fun a b => Int.cast_injective (α := ℚ) (by
    push_cast; rw [hz, hz, hz]; push_cast; rw [mul_add, map_add])
  have hθ : ∀ u, ((θ u : ℤ) : ℚ) = Algebra.trace ℚ E (δ * u) := hz
  have hmemψ : ∀ ψ : 𝓞 E →+ ℤ, ∃ x ∈ M, ∀ u : 𝓞 E, ((ψ u : ℤ) : ℚ) = Algebra.trace ℚ E (x * u) := by
    intro ψ
    obtain ⟨x, hx⟩ := exists_trace_eq ψ
    refine ⟨x, (FractionalIdeal.mem_dual h10).2 fun a ha => ?_, hx⟩
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    exact ⟨ψ b, by rw [Algebra.traceForm_apply]; simpa using (hx b)⟩
  obtain ⟨s, hs, hsM⟩ := exists_local_gen hM hδM hδ
  have hθbar : ∀ t, θ (H.bar t) = θ t := by
    intro t
    apply Int.cast_injective (α := ℚ)
    rw [hθ, hθ, H.bar_eq, ← hδc, ← map_mul, trace_conj, hδc]
  have hPs : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) := by
    intro ψ
    obtain ⟨x, hx, hψ⟩ := hmemψ ψ
    obtain ⟨t, ht⟩ := hsM x hx
    refine ⟨t, fun u => Int.cast_injective (α := ℚ) ?_⟩
    rw [hψ, hθ]
    push_cast
    rw [← mul_assoc, mul_comm x, ht, mul_assoc]
  have hPbar : ∀ s : 𝓞 E, (∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u)) →
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (H.bar s * u) = θ (t * u) := by
    intro s hs ψ
    obtain ⟨t, ht⟩ := hs (ψ.comp (H.bar : 𝓞 E →+* 𝓞 E).toAddMonoidHom)
    refine ⟨H.bar t, fun u => ?_⟩
    have := ht (H.bar u)
    simp only [AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, RingHom.coe_coe,
      map_mul, bar_bar] at this
    rw [this, ← hθbar (t * H.bar u), map_mul, bar_bar]
  refine ⟨θ, hθbar, ?_⟩
  by_cases hb : H.bar s ∈ 𝔭
  · have hsb : s + H.bar s ∉ 𝔭 := fun h => hs (by have := sub_mem h hb; rwa [add_sub_cancel_right] at this)
    refine ⟨s + H.bar s, hsb, by rwa [map_add, bar_bar, add_comm], fun ψ => ?_⟩
    obtain ⟨t, ht⟩ := hPs ψ
    obtain ⟨t', ht'⟩ := hPbar s hPs ψ
    exact ⟨t + t', fun u => by rw [add_mul, map_add, ht, ht', add_mul, map_add]⟩
  · exact ⟨s, hs, hb, hPs⟩

end GlobalTheory.RealTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogSwapSymmetric
section
open GlobalTheory.Published GlobalTheory.CovTest

theorem GlobalTheory.CovTest.homog_swap_exists_of_ar_calc : ArCalc → RegularAlteration → ∃ G, Homog G ∧ Swap2 G := fun hC hR =>
  let ⟨G, hG, hS⟩ := GlobalTheory.T.exists_homogeneous_swap_regular hC
  ⟨G, hG, GlobalTheory.T.swap_identity_from_regular_base hC hR GlobalTheory.T.generic_degree_pullback_formula G hS⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntLogOfIsLiePSmul
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem GlobalTheory.QLog.exists_int_log_of_isLie_p_smul : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E) (l : G.dual.Lie), QL c.μ ⊤ f → c.IsLie f ((p : O) • l) → ∃ (s : MvPowerSeries (Fin d) O) (g : MvPowerSeries (Fin d) E), cob1 (up E c.μ) g = 0 ∧ QL c.μ (Ideal.span {(p : O)}) (f - map (algebraMap O E) s - g) := by
  intro p _ O E _ _ _ hF G d c f l hf hl
  obtain ⟨s₁, hs₁, hl₁⟩ := (c.isLie_iff hF.inj f _).1 hl 1
  rw [pow_one] at hs₁
  have hdiv : ∀ (w : G.dual.omega) (φ : CartierDual O (G.A 1)), dUnit O φ = w.1 1 →
      (p : O) ∣ φ (c.ev 1 s₁) := by
    intro w φ hφ
    have h1 := hl₁ w φ hφ
    rw [pow_one, LinearMap.smul_apply, smul_eq_mul] at h1
    exact (dvd_sub_right (dvd_mul_right _ _)).1 h1
  obtain ⟨⟨z, hz⟩, -⟩ := GlobalTheory.T.dvd_of_forall_invariantDifferential_dvd p O G 1 (p : O) (c.ev 1 s₁) hdiv
  obtain ⟨t, ht0, ht⟩ := GlobalTheory.T.exists_integral_coboundary_divisible_of_quasiLog_defect p O E hF G d c f s₁ z hf hs₁ hz
  obtain ⟨hf0, hflin, -⟩ := hf
  choose b _ hb using hflin
  obtain ⟨g, hg0, hglin, hgcob⟩ := GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart p O E hF d c.μ c.isLaw (fun i => b i - lin t i)
  have hμ : ∀ i, constantCoeff (up E c.μ i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      c.isLaw.const i, map_zero]
  refine ⟨t, g, hgcob, ?_, ?_, ?_⟩
  · rw [map_sub, map_sub, hf0, hg0, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, ht0, map_zero]
    simp
  · intro i
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    have : lin (f - map (algebraMap O E) t - g) i = lin f i - algebraMap O E (lin t i) - lin g i := by
      simp [lin, coeff_map]
    rw [this, hb i, hglin i, map_sub, map_zero]
    simp
  · have hsub : f - map (algebraMap O E) t - g = (f - map (algebraMap O E) t) + (-1 : E) • g := by
      rw [neg_one_smul, ← sub_eq_add_neg]
    rw [hsub, formalCoboundary_add hμ, formalCoboundary_smul hμ, hgcob, smul_zero, add_zero]
    exact ht
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantTangentBasisRaynaudExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_tangent_basis_raynaudExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), ∃ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), ∀ a, IsInv Y.H (v a) (dd a) := by
  first | exact @GlobalTheory.RayTan.exists_basis_isInv | exact GlobalTheory.RayTan.exists_basis_isInv | (intros; apply GlobalTheory.RayTan.exists_basis_isInv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedSubmoduleOfFinrankLe
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.IsoSat

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_isotropic_vector (D : Datum H) (hp : 1 ≤ D.p) (hq : 1 ≤ D.q) :
    ∃ x : D.La, x ≠ 0 ∧ ∀ a : 𝓞 E, D.EF (a • x) x = 0 := by
  by_cases h3 : 3 ≤ D.p + D.q
  · have hξ := GlobalTheory.OneSpace.cc_rt H
    have hξ0 := GlobalTheory.OneSpace.rt_ne H
    obtain ⟨G, φ, hM⟩ := GlobalTheory.exists_herm_coord_of_datum E H D (H.rt : E) hξ hξ0 (D.p + D.q) rfl
    have hind := GlobalTheory.SplitGenus.indefinite D hp hq G φ hM
    obtain ⟨inj, span, hG, hdet, hEF⟩ := hM
    have hh : GlobalTheory.UTrans.IsHerm (IsCMField.complexConj E : E →+* E) G := by
      refine ⟨fun a => IsCMField.complexConj_apply_apply E a, ⟨(H.rt : E), fun h => hξ0 ?_⟩, hG, hdet⟩
      have h2 : (H.rt : E) = -(H.rt : E) := h.symm.trans hξ
      linear_combination (1 / 2 : E) * h2
    obtain ⟨z, hz0, hz⟩ := GlobalTheory.UTrans.exists_isotropic_of_indefinite E _ _ G (fun _ => rfl) hh h3 hind
    have hz' : FD.herm G z z = 0 := hz
    obtain ⟨N, g, hN, hg⟩ := GlobalTheory.SplitGenus.exists_scaled_map (LinearMap.toSpanSingleton (𝓞 E) _ z) φ inj span
    have h1 : φ (g 1) = (N : E) • z := by rw [hg, LinearMap.toSpanSingleton_apply, one_smul]
    refine ⟨g 1, fun h => ?_, fun a => ?_⟩
    · rw [h, map_zero, eq_comm, smul_eq_zero] at h1
      exact h1.elim (Nat.cast_ne_zero.2 hN.ne') hz0
    · have h2 := hEF (a • g 1) (g 1)
      rw [map_smul φ, h1, show a • (N : E) • z = (a : E) • (N : E) • z from rfl, GlobalTheory.HermModel.herm_smul_left,
        GlobalTheory.HermModel.herm_smul_left, GlobalTheory.HermModel.herm_smul_right, hz'] at h2
      simp only [zero_mul, mul_zero, map_zero] at h2
      exact_mod_cast h2
  · obtain ⟨k, f, hk, hf⟩ := GlobalTheory.LocalIsomAt.exists_coprime_scaled_isometry E H (GlobalTheory.HostModel.hypDatum H) D
      (by change D.p = 1; omega) (by change D.q = 1; omega) 2 two_pos
    have hk0 : (k : ℤ) ^ 2 ≠ 0 := by
      have : k ≠ 0 := by
        rintro rfl
        simp at hk
      positivity
    refine ⟨f (1, 0), fun h => ?_, fun a => ?_⟩
    · have : ((1, 0) : (GlobalTheory.HostModel.hypDatum H).La) = 0 := (GlobalTheory.HostModel.hypDatum H).unimod.1 (LinearMap.ext fun y => by
        have := hf (1, 0) y
        rw [h, map_zero, LinearMap.zero_apply] at this
        rw [map_zero, LinearMap.zero_apply]
        exact (mul_eq_zero.1 this.symm).resolve_left hk0)
      exact one_ne_zero (congrArg Prod.fst this)
    · rw [← map_smul, hf, GlobalTheory.HostModel.hypDatum_smul, smul_zero, GlobalTheory.HostModel.hypDatum_EF_inl_inl, mul_zero]

theorem exists_saturation (D : Datum H) (W : Submodule (𝓞 E) D.La) (hW : W ≤ perp D W) :
    ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) W := by
  have := D.fin
  let Z : Submodule (𝓞 E) D.La :=
    { carrier := {x | ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ W}
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨n, hn, hx⟩ ⟨m, hm, hy⟩
        refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
        rw [smul_add]
        refine add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact nsmul_mem hx m
        · rw [mul_smul]; exact nsmul_mem hy n
      smul_mem' := by
        rintro a x ⟨n, hn, hx⟩
        exact ⟨n, hn, by rw [smul_comm]; exact W.smul_mem a hx⟩ }
  have hle : W ≤ Z := fun x hx => ⟨1, one_ne_zero, by rwa [one_smul]⟩
  refine ⟨Z, ⟨?_, ?_⟩, ?_⟩
  · rintro x ⟨n, hn, hx⟩ y ⟨m, hm, hy⟩
    have := hW hx _ hy
    simpa [hn, hm] using this
  · rintro n x hn ⟨m, hm, hx⟩
    exact ⟨m * n, mul_ne_zero hm hn, by rwa [mul_smul]⟩
  · have h1 := Submodule.finrank_quotient_add_finrank (W.comap Z.subtype)
    have h2 : Module.finrank (𝓞 E) (Z ⧸ W.comap Z.subtype) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro x
      obtain ⟨⟨x, n, hn, hx⟩, rfl⟩ := Submodule.mkQ_surjective _ x
      refine ⟨(n : 𝓞 E), Nat.cast_ne_zero.2 hn, ?_⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Nat.cast_smul_eq_nsmul]
      exact hx
    rw [← h1, h2, zero_add, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq]

theorem exists_succ (D : Datum H) (Z : Submodule (𝓞 E) D.La) (hZ : IsIsoSat D Z)
    (hr : Module.finrank (𝓞 E) Z + 1 ≤ min D.p D.q) :
    ∃ Z' : Submodule (𝓞 E) D.La, IsIsoSat D Z' ∧ Module.finrank (𝓞 E) Z' = Module.finrank (𝓞 E) Z + 1 := by
  have := D.fin
  obtain ⟨D', f, ⟨hs, hk, hE⟩, hp, hq⟩ := exists_lowerDatum D Z hZ
  obtain ⟨x', hx0, hx⟩ := exists_isotropic_vector D' (by omega) (by omega)
  obtain ⟨x, rfl⟩ := hs x'
  have := D'.proj
  have hnot : ∀ a : 𝓞 E, a • (x : D.La) ∈ Z → a = 0 := fun a ha => by
    have h := (hk (a • x)).2 ha
    rw [map_smul, smul_eq_zero] at h
    exact h.resolve_right hx0
  let g : (Z × 𝓞 E) →ₗ[𝓞 E] D.La := Z.subtype.coprod (LinearMap.toSpanSingleton (𝓞 E) _ (x : D.La))
  have hg : ∀ u, g u = u.1 + u.2 • (x : D.La) := fun u => rfl
  have hinj : Function.Injective g := (injective_iff_map_eq_zero g).2 fun u hu => by
    rw [hg] at hu
    have h2 : u.2 = 0 := hnot _ (by rw [eq_neg_of_add_eq_zero_right hu]; exact neg_mem u.1.2)
    rw [h2, zero_smul, add_zero] at hu
    exact Prod.ext (Subtype.ext hu) h2
  obtain ⟨Z', h1, h2⟩ := exists_saturation D (LinearMap.range g) (by
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    have e1 : D.EF u.1 v.1 = 0 := hZ.1 u.1.2 _ v.1.2
    have e2 : ∀ (a : 𝓞 E) (z : Z), D.EF (a • (x : D.La)) z = 0 := fun a z => (a • x).2 _ z.2
    have e3 : D.EF (u.2 • (x : D.La)) (v.2 • (x : D.La)) = 0 := by
      have h := hx (H.bar v.2 * u.2)
      rw [← map_smul, hE, Submodule.coe_smul, mul_smul, D.adj, bar_bar] at h
      exact h
    rw [hg, hg]
    simp only [map_add, LinearMap.add_apply]
    rw [e1, e2, e3, ef_swap, e2]
    simp)
  refine ⟨Z', h1, ?_⟩
  rw [h2, ← (LinearEquiv.ofInjective g hinj).finrank_eq]
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.ker (LinearMap.snd (𝓞 E) Z (𝓞 E)))
  rw [((LinearMap.snd (𝓞 E) Z (𝓞 E)).quotKerEquivOfSurjective LinearMap.snd_surjective).finrank_eq,
    Module.finrank_self, ← LinearMap.range_inl,
    ← (LinearEquiv.ofInjective _ LinearMap.inl_injective).finrank_eq] at h3
  omega

end GlobalTheory.LowFilt.IsoSat

namespace GlobalTheory.LowFilt

theorem exists_isIsoSat_finrank : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (r : ℕ),
    r ≤ min D.p D.q → ∃ Z : Submodule (𝓞 E) D.La, IsIsoSat D Z ∧ Module.finrank (𝓞 E) Z = r := by
  intro E _ _ _ H D r
  induction r with
  | zero => exact fun _ => ⟨⊥, (isOpp_bot D).isIsoSat, finrank_bot _ _⟩
  | succ r ih =>
    intro hr
    obtain ⟨Z, hZ, rfl⟩ := ih (by omega)
    exact IsoSat.exists_succ D Z hZ hr

end GlobalTheory.LowFilt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPulledBackTraitStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_uniformisation_pulled_back_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : UTrait Xo c) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ h : T.V →+* W, Function.Injective h → IsLocalHom h → ∃ (tW : SAB H (Sp W)) (_ : SABMap tW T.t (spMap h)) (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X), ∀ y, 0 ≤ T.be (e y) (e y) ∧ ∃ r, PsiCoord PW.D.toPre y r ∧ Associated (r ^ 2) (h T.ϖ ^ (T.be (e y) (e y)).toNat) := by
  first | exact @GlobalTheory.UPoinc.TraitPull.exists_pull_unif | exact GlobalTheory.UPoinc.TraitPull.exists_pull_unif | (intros; apply GlobalTheory.UPoinc.TraitPull.exists_pull_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSpreadUniversalAbelianSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_spread_universal_abelian_scheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (o₁ Ω : Type) [CommRing o₁] [Field Ω] [Algebra o₁ Ω] [ArithBase o₁ Ω] (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (uη : Sp Ω ⟶ Xo.XF c), GlobalTheory.IsNormalScheme M.Z → M.pt ≫ π = uη ≫ C.i → ∀ (A₁ : PolAV (Sp Ω)) (m : ℕ) (ze : o₁ˣ), IsUnit (m : o₁) → UOver Xo c A₁ (RingHom.id Ω) uη → Out.Level A₁ m (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze)) → ∀ (K : Type) [Field K] (yM : Sp K ⟶ M.Z) (y : Sp K ⟶ Xo.XF c), yM ≫ π = y ≫ C.i → ∃ (R : Subalgebra o₁ Ω) (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c) (𝔭 : Ideal R), R.FG ∧ (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ P.g = A₁.g ∧ HypS P.A P.L ∧ Nonempty (Out.Level P m (unitOn (Units.map (algebraMap o₁ R).toMonoidHom ze))) ∧ (∀ a, IsMonHom (act a)) ∧ GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u ∧ spMap (ratHull R).val.toRingHom ≫ u = uη ∧ 𝔭.IsPrime ∧ ∀ a b : R, b ∉ 𝔭 → (a : Ω) / (b : Ω) ∈ M.O (yM (closedPoint K)) := by
  first | exact @GlobalTheory.UCovSep.LocalSpread.exists_local_spread | exact GlobalTheory.UCovSep.LocalSpread.exists_local_spread | (intros; apply GlobalTheory.UCovSep.LocalSpread.exists_local_spread <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerDatumOfIsotropicSaturatedStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lower_datum_of_isotropic_saturated : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) (Z : Submodule (𝓞 E) Dw.La),
  GlobalTheory.LowDat.IsIsoSat Dw Z → ∃ (D' : Datum H) (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f ∧
    D'.p = Dw.p - Module.finrank (𝓞 E) Z ∧ D'.q = Dw.q - Module.finrank (𝓞 E) Z := by
  first | exact @GlobalTheory.LowDat.exists_lowerDatum | exact GlobalTheory.LowDat.exists_lowerDatum | (intros; apply GlobalTheory.LowDat.exists_lowerDatum <;> assumption)
end
end

