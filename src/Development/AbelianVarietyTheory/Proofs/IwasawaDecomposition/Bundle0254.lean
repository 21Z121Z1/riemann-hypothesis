import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0039
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
import Formalism.LocalToGlobal.IndefiniteReal.HeckeNonvanishing.Imports
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0249
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
section
noncomputable section

open ValuativeRel
open scoped Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.LocLanglands

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_iff_ord {x y : kˣ} : valuation k (x : k) ≤ valuation k (y : k) ↔ ord k y ≤ ord k x := by
  rw [ord, ord, neg_le_neg_iff, WithZero.log_le_log (by simp) (by simp)]
  exact (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k)).symm

theorem valuation_eq_iff_ord {x y : kˣ} : valuation k (x : k) = valuation k (y : k) ↔ ord k x = ord k y := by
  rw [le_antisymm_iff, valuation_le_iff_ord, valuation_le_iff_ord]; omega

variable (k) in
theorem exists_unit_pow (a : ℕ) : ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧ ord k p = a := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (R := k) (by simpa using hy.symm)
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hy
  refine ⟨Units.mk0 y hy0 ^ a, by simp [hy], ?_⟩
  induction a with
  | zero => simpa using ord_eq_zero (k := k) (x := 1) (by simp)
  | succ n ih => rw [pow_succ, ord_mul, ih, h1]; simp

theorem valuation_of_shell {c r : kˣ} {a : ℕ} (hr : ord k r = ord k c - a) :
    valuation k (c : k) = uniformizer k ^ a * valuation k (r : k) := by
  obtain ⟨p, hp, hp'⟩ := exists_unit_pow k a
  rw [← hp, ← map_mul, ← Units.val_mul, valuation_eq_iff_ord, ord_mul]; omega

theorem exists_shell (c : kˣ) (a : ℕ) : ∃ d : kˣ, ord k d = ord k c - a := by
  obtain ⟨p, -, hp'⟩ := exists_unit_pow k a
  refine ⟨c * p⁻¹, ?_⟩
  have := ord_mul k (c * p⁻¹) p
  rw [inv_mul_cancel_right] at this
  omega

theorem exists_hasExponent {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) : ∃ a, HasExponent χ a := by
  classical
  have h : ∃ a, ∀ x ∈ unitFilt k a, χ x = 1 := by
    obtain ⟨V, hV, hV'⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.1 hχ
    have h1 : (1 : k) ∈ V := by
      have : (1 : kˣ) ∈ Units.val ⁻¹' V := by rw [hV']; exact χ.ker.one_mem
      simpa using this
    have h2 : (fun z : k => z + 1) ⁻¹' V ∈ 𝓝 (0 : k) :=
      (hV.preimage (by fun_prop)).mem_nhds (by simpa using h1)
    obtain ⟨s, hs⟩ := exists_cball_subset h2
    obtain ⟨p, hp, hp'⟩ := exists_unit_pow k (ord k s).toNat
    refine ⟨(ord k s).toNat, fun x hx => ?_⟩
    have h3 : (x : k) - 1 ∈ cball s :=
      hx.2.trans (show _ ≤ valuation k (s : k) by rw [← hp, valuation_le_iff_ord]; omega)
    have h4 : x ∈ Units.val ⁻¹' V := by simpa using hs h3
    rw [hV'] at h4
    exact h4
  refine ⟨Nat.find h, Nat.find_spec h, fun b hb => ?_⟩
  have := Nat.find_min h hb
  push Not at this
  exact this

theorem exists_isShellReps (c : kˣ) (a : ℕ) : ∃ R, IsShellReps c a R := by
  classical
  obtain ⟨d, hd⟩ := exists_shell c a
  let B : AddSubgroup k :=
    { carrier := cball c
      add_mem' := add_mem_cball
      zero_mem' := by simp [cball]
      neg_mem' := neg_mem_cball }
  have : DiscreteTopology (k ⧸ B) := QuotientAddGroup.discreteTopology (isOpen_cball c)
  let S : Set kˣ := {y | ord k y = ord k c - a}
  let q : kˣ → k ⧸ B := fun y => QuotientAddGroup.mk (y : k)
  have hq : ∀ y r : kˣ, q r = q y ↔ valuation k ((y : k) - r) ≤ valuation k (c : k) := fun y r => by
    simp only [q]
    rw [QuotientAddGroup.eq, neg_add_eq_sub]; rfl
  have hfin : (q '' S).Finite := by
    refine (((isCompact_cball d).image QuotientAddGroup.continuous_mk).finite_of_discrete).subset ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, (valuation_eq_iff_ord.2 (hy.trans hd.symm)).le, rfl⟩
  obtain ⟨T, hTS, hT⟩ := Set.exists_subset_bijOn S q
  have hTfin : T.Finite := Set.Finite.of_finite_image (hT.image_eq ▸ hfin) hT.injOn
  refine ⟨hTfin.toFinset, fun r hr => hTS (by simpa using hr), fun y hy => ?_⟩
  obtain ⟨r, hr, hry⟩ := hT.surjOn ⟨y, hy, rfl⟩
  refine ⟨r, ⟨by simpa using hr, (hq y r).1 hry⟩, fun r' hr' => ?_⟩
  exact hT.injOn (by simpa using hr'.1) hr (((hq y r').2 hr'.2).trans hry.symm)

theorem IsShellReps.sum_eq {c : kˣ} {a : ℕ} {R R' : Finset kˣ} (h : IsShellReps c a R) (h' : IsShellReps c a R')
    {g : kˣ → ℂ} (hg : ∀ y r : kˣ, ord k y = ord k c - a → ord k r = ord k c - a →
      valuation k ((y : k) - r) ≤ valuation k (c : k) → g y = g r) :
    ∑ r ∈ R, g r = ∑ r ∈ R', g r := by
  choose i hi hi' using fun r hr => h'.2 r (h.1 r hr)
  refine Finset.sum_bij i (fun r hr => (hi r hr).1) (fun r₁ h₁ r₂ h₂ e => ?_) (fun r' hr' => ?_)
    (fun r hr => hg _ _ (h.1 r hr) (h'.1 _ (hi r hr).1) (hi r hr).2)
  · refine (h.2 _ (h'.1 _ (hi r₁ h₁).1)).unique ⟨h₁, ?_⟩ ⟨h₂, ?_⟩
    · rw [Valuation.map_sub_swap]; exact (hi r₁ h₁).2
    · rw [Valuation.map_sub_swap, e]; exact (hi r₂ h₂).2
  · obtain ⟨r, hr, -⟩ := h.2 r' (h'.1 r' hr')
    exact ⟨r, hr.1, (hi' r hr.1 r' ⟨hr', by rw [Valuation.map_sub_swap]; exact hr.2⟩).symm⟩

open Classical in

theorem IsShellReps.image_mul {c : kˣ} {a : ℕ} {R : Finset kˣ} (h : IsShellReps c a R) {u : kˣ}
    (hu : valuation k (u : k) = 1) : IsShellReps c a (R.image (u * ·)) := by
  have h0 := ord_eq_zero hu
  refine ⟨fun r hr => ?_, fun y hy => ?_⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hr
    rw [ord_mul, h0, zero_add, h.1 s hs]
  · have h1 : ord k (u⁻¹ * y) = ord k c - a := by
      have := ord_mul k u (u⁻¹ * y)
      rw [mul_inv_cancel_left] at this
      omega
    have h2 : ∀ r : kˣ, valuation k ((y : k) - (u * r : kˣ)) = valuation k (((u⁻¹ * y : kˣ) : k) - r) := fun r => by
      have : (y : k) - (u * r : kˣ) = u * (((u⁻¹ * y : kˣ) : k) - r) := by simp [mul_sub]
      rw [this, map_mul, hu, one_mul]
    obtain ⟨r, hr, hr'⟩ := h.2 _ h1
    refine ⟨u * r, ⟨Finset.mem_image_of_mem _ hr.1, (h2 r).trans_le hr.2⟩, ?_⟩
    rintro _ ⟨hm, hv⟩
    obtain ⟨r', hm', rfl⟩ := Finset.mem_image.1 hm
    rw [hr' r' ⟨hm', (h2 r').symm.trans_le hv⟩]

variable {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {c : kˣ} {a : ℕ} {R R' : Finset kˣ}

theorem addChar_eq_of_sub (hψ : HasConductor ψ c) {y z : k} (h : valuation k (y - z) ≤ valuation k (c : k)) :
    ψ y = ψ z := by
  have : y = z + (y - z) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.eq_one h, mul_one]

theorem gaussTerm_eq (hψ : HasConductor ψ c) (hχ : HasExponent χ a) {x : k} (hx : valuation k x ≤ 1) (y r : kˣ)
    (hy : ord k y = ord k c - a) (hr : ord k r = ord k c - a)
    (h : valuation k ((y : k) - r) ≤ valuation k (c : k)) :
    (((χ y)⁻¹ : ℂˣ) : ℂ) * (ψ (x * y) : ℂ) = (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) := by
  have h1 : ψ (x * y) = ψ (x * r) := addChar_eq_of_sub hψ (by
    rw [← mul_sub, map_mul]
    exact (mul_le_mul' hx h).trans_eq (one_mul _))
  have hr0 : 0 < valuation k (r : k) := by simp [zero_lt_iff]
  have h2 : χ (y * r⁻¹) = 1 := hχ.1 _ ⟨by
    rw [Units.val_mul, map_mul, valuation_eq_iff_ord.2 (hy.trans hr.symm), ← map_mul]; simp, by
    have : ((y * r⁻¹ : kˣ) : k) - 1 = ((y : k) - r) * (r : k)⁻¹ := by simp [sub_mul]
    rw [this, map_mul, map_inv₀, mul_inv_le_iff₀ hr0, ← valuation_of_shell hr]
    exact h⟩
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [h1, h2]

theorem gaussSum_mul_unit (hψ : HasConductor ψ c) (hχ : HasExponent χ a) (h : IsShellReps c a R) {x : k}
    (hx : valuation k x ≤ 1) {u : kˣ} (hu : valuation k (u : k) = 1) :
    ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * u * r) : ℂ) =
      χ u * ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) := by
  classical
  rw [h.sum_eq (h.image_mul hu) (gaussTerm_eq hψ hχ hx),
    Finset.sum_image (fun _ _ _ _ e => mul_left_cancel e), Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [map_mul, mul_inv, Units.val_mul, mul_assoc, Units.mul_inv_cancel_left]

theorem gaussSum_eq_zero (hψ : HasConductor ψ c) (hχ : HasExponent χ (a + 1)) (h : IsShellReps c (a + 1) R) {x : k}
    (hx : valuation k x < 1) : ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) = 0 := by
  obtain ⟨u, hu, hu'⟩ := hχ.2 a (Nat.lt_succ_self a)
  have h1 := gaussSum_mul_unit hψ hχ h hx.le hu.1
  have h2 : ∀ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * u * r) : ℂ) = (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) := by
    intro r hr
    rw [addChar_eq_of_sub hψ (y := x * u * r) (z := x * r)]
    have : x * u * r - x * r = ((u : k) - 1) * x * r := by ring
    rw [this, map_mul, map_mul, valuation_of_shell (h.1 r hr), pow_succ]
    exact mul_le_mul' (mul_le_mul' hu.2 (le_uniformizer_iff.2 hx)) le_rfl
  rw [Finset.sum_congr rfl h2] at h1
  by_contra h0
  exact hu' (Units.ext (by simpa using ((mul_eq_right₀ h0).1 h1.symm)))

theorem gaussSum_ne_zero_of_ramified (hψ : HasConductor ψ c) (hχ : HasExponent χ (a + 1))
    (h : IsShellReps c (a + 1) R) : ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (r : k) : ℂ) ≠ 0 := by
  intro h0
  have h1 : ∀ x : k, valuation k x ≤ 1 → ∑ r ∈ R, (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) = 0 := by
    intro x hx
    rcases hx.lt_or_eq with hx | hx
    · exact gaussSum_eq_zero hψ hχ h hx
    · have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have := gaussSum_mul_unit hψ hχ h (x := 1) (by simp) (u := Units.mk0 x hx0) hx
      simp only [one_mul, Units.val_mk0] at this
      rw [this, h0, mul_zero]
  let φ : R → Multiplicative 𝒪[k] →* ℂ := fun r =>
    { toFun := fun x => ψ ((x.toAdd : k) * (r.1 : k))
      map_one' := by simp
      map_mul' := fun x y => by simp [add_mul, AddChar.map_add_eq_mul] }
  have hφ : Function.Injective φ := by
    intro r r' e
    refine Subtype.ext ((h.2 r (h.1 r r.2)).unique ⟨r.2, by simp⟩ ⟨r'.2, ?_⟩)
    refine (hψ _).1 fun y hy => ?_
    by_cases h2 : (r.1 : k) - r'.1 = 0
    · rw [h2, map_zero, le_zero_iff, map_eq_zero] at hy
      simp [hy]
    have h3 : valuation k (y / ((r.1 : k) - r'.1)) ≤ 1 := by
      rw [map_div₀]; exact div_le_one_of_le₀ hy zero_le
    have h4 : ψ (y / ((r.1 : k) - r'.1) * r.1) = ψ (y / ((r.1 : k) - r'.1) * r'.1) :=
      Circle.ext (DFunLike.congr_fun e (Multiplicative.ofAdd (⟨y / ((r.1 : k) - r'.1), h3⟩ : 𝒪[k])))
    rw [← div_mul_cancel₀ y h2, mul_sub, AddChar.map_sub_eq_div, h4, div_self']
  have hli := (linearIndependent_monoidHom (Multiplicative 𝒪[k]) ℂ).comp φ hφ
  obtain ⟨d, hd⟩ := exists_shell c (a + 1)
  obtain ⟨r, hr, -⟩ := h.2 d hd
  refine Units.ne_zero (χ r)⁻¹ (Fintype.linearIndependent_iff.1 hli (fun r => (((χ r)⁻¹ : ℂˣ) : ℂ)) ?_ ⟨r, hr.1⟩)
  funext x
  rw [Finset.sum_apply, Pi.zero_apply, ← h1 x.toAdd x.toAdd.2, ← Finset.sum_coe_sort R]
  rfl

theorem IsTateEps.unique {e e' : ℂ} (h : IsTateEps ψ χ e) (h' : IsTateEps ψ χ e') : e = e' := by
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := h
  obtain ⟨c', a', R', hc', ha', hR', rfl⟩ := h'
  obtain rfl := ha.unique ha'
  have h1 : valuation k (c' : k) = valuation k (c : k) :=
    le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl))
  rw [IsShellReps, valuation_eq_iff_ord.1 h1, h1] at hR'
  have := hR.sum_eq hR' (gaussTerm_eq hc ha (x := 1) (by simp))
  simp only [one_mul] at this
  rw [this]

theorem IsTateEps.ne_zero {e : ℂ} (h : IsTateEps ψ χ e) : e ≠ 0 := by
  obtain ⟨c, a, R, hc, ha, hR, he⟩ := id h
  cases a with
  | zero =>
    rw [h.unique (isTateEps_of_isUnram hc (hasExponent_zero_iff.1 ha))]
    exact Units.ne_zero _
  | succ a =>
    rw [he]
    refine mul_ne_zero ?_ (gaussSum_ne_zero_of_ramified hc ha hR)
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne')

theorem existsUnique_isTateEps (ψ : AddChar k Circle) (hψ : Continuous ψ) (h1 : ψ ≠ 1) (χ : kˣ →* ℂˣ)
    (hχ : IsSmoothChar χ) : (∃! e : ℂ, IsTateEps ψ χ e) ∧ ∀ e : ℂ, IsTateEps ψ χ e → e ≠ 0 := by
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
  obtain ⟨a, ha⟩ := exists_hasExponent hχ
  obtain ⟨R, hR⟩ := exists_isShellReps c a
  exact ⟨existsUnique_of_exists_of_unique ⟨_, c, a, R, hc, ha, hR, rfl⟩ fun _ _ => IsTateEps.unique,
    fun _ => IsTateEps.ne_zero⟩

end GlobalTheory.LocLanglands
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasCompactSupportDescend
section
noncomputable section

open MeasureTheory Topology
open scoped Pointwise

namespace GlobalTheory.LocLanglands.InvInt

section General

variable {G : Type} [Group G] (H : Subgroup G)

def descend : (G → ℂ) →ₗ[ℂ] (G ⧸ H → ℂ) where
  toFun f q := f (q.out)⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {H}

theorem descend_mk {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (g : G) :
    descend H f (g : G ⧸ H) = f g⁻¹ := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  show f ((g : G ⧸ H).out)⁻¹ = _
  rw [hh, mul_inv_rev]
  exact hf _ (H.inv_mem h.2) _

theorem descend_mul_right {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (x : G) :
    descend H (fun g => f (g * x)) = fun q => descend H f (x⁻¹ • q) := by
  funext q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk (fun u hu g => by rw [mul_assoc, hf u hu]), MulAction.Quotient.smul_mk, descend_mk hf]
  simp

theorem indicator_mul_left {K : Set G} : ∀ u ∈ H, ∀ g, ((H : Set G) * K).indicator (fun _ => (1 : ℂ)) (u * g) =
    ((H : Set G) * K).indicator (fun _ => (1 : ℂ)) g := by
  intro u hu g
  classical
  simp only [Set.indicator_apply]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨v, hv, c, hc, e⟩
    exact ⟨u⁻¹ * v, H.mul_mem (H.inv_mem hu) hv, c, hc, by simp only at e; simp [mul_assoc, e]⟩
  · rintro ⟨v, hv, c, hc, rfl⟩
    exact ⟨u * v, H.mul_mem hu hv, c, hc, mul_assoc _ _ _⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_descend {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g) (hc : Continuous f) :
    Continuous (descend H f) := by
  refine (QuotientGroup.isQuotientMap_mk H).continuous_iff.mpr ?_
  have : descend H f ∘ QuotientGroup.mk = fun g => f g⁻¹ := funext (descend_mk hf)
  rw [this]
  exact hc.comp continuous_inv

theorem hasCompactSupport_descend [T2Space (G ⧸ H)] {f : G → ℂ} (hf : ∀ u ∈ H, ∀ g, f (u * g) = f g)
    {C : Set G} (hC : IsCompact C) (hs : ∀ g, f g ≠ 0 → ∃ u ∈ H, ∃ c ∈ C, g = u * c) :
    HasCompactSupport (descend H f) := by
  refine HasCompactSupport.intro (hC.inv.image QuotientGroup.continuous_mk) fun q hq => ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  rw [descend_mk hf]
  by_contra h
  obtain ⟨u, hu, c, hc, e⟩ := hs _ h
  refine hq ⟨c⁻¹, by simpa using hc, QuotientGroup.eq.2 ?_⟩
  have : g = c⁻¹ * u⁻¹ := by rw [← mul_inv_rev, ← e, inv_inv]
  rw [this]
  simpa using hu

theorem exists_invariant_form [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (hH : IsClosed (H : Set G))
    (uG : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsUnimodular G) (uH : GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre.IsUnimodular H)
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) :
    ∃ I : (G → ℂ) →ₗ[ℂ] ℂ,
      (∀ f : G → ℂ, (∀ u ∈ H, ∀ g, f (u * g) = f g) → Continuous f →
        (∃ C : Set G, IsCompact C ∧ ∀ g, f g ≠ 0 → ∃ u ∈ H, ∃ c ∈ C, g = u * c) →
        ∀ x, I (fun g => f (g * x)) = I f) ∧
      I (((H : Set G) * (K : Set G)).indicator fun _ => 1) ≠ 0 := by
  borelize (G ⧸ H)
  obtain ⟨⟨μ, hμ⟩, -⟩ := GlobalTheory.Proof.quotientInvariantMeasure_exists_unique_unimodular.invariantMeasureClause G H hH uG uH
  have := hμ.finiteOnCompacts
  have := hμ.invariant
  have := hμ.regular
  let S : Submodule ℂ (G → ℂ) :=
    { carrier := {f | Integrable (descend H f) μ}
      zero_mem' := by simp
      add_mem' := fun {f g} hf hg => by
        simp only [Set.mem_ofPred_eq, map_add] at *
        exact hf.add hg
      smul_mem' := fun c f hf => by
        simp only [Set.mem_ofPred_eq, map_smul] at *
        exact hf.smul c }
  let J : S →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ q, descend H f q ∂μ
      map_add' := fun f g => integral_add f.2 g.2
      map_smul' := fun c f => integral_smul c (descend H f) }
  obtain ⟨I, hI⟩ := J.exists_extend
  have hIJ : ∀ f, Integrable (descend H f) μ → I f = ∫ q, descend H f q ∂μ := fun f hf =>
    LinearMap.congr_fun hI ⟨f, hf⟩
  refine ⟨I, fun f hf hc ⟨C, hC, hs⟩ x => ?_, ?_⟩
  · have h1 : Integrable (descend H f) μ :=
      (continuous_descend hf hc).integrable_of_hasCompactSupport (hasCompactSupport_descend hf hC hs)
    have h2 : Integrable (descend H fun g => f (g * x)) μ := by
      rw [descend_mul_right hf]
      exact (measurePreserving_smul x⁻¹ μ).integrable_comp_of_integrable h1
    rw [hIJ _ h1, hIJ _ h2, descend_mul_right hf]
    exact integral_smul_eq_self (descend H f)
  · set U : Set (G ⧸ H) := QuotientGroup.mk '' (K : Set G)
    have hUo : IsOpen U := QuotientGroup.isOpenMap_coe _ hKo
    have hUc : IsCompact U := hKc.image QuotientGroup.continuous_mk
    have e : descend H (((H : Set G) * (K : Set G)).indicator fun _ => 1) = U.indicator fun _ => 1 := by
      funext q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      rw [descend_mk indicator_mul_left]
      classical
      simp only [Set.indicator_apply]
      refine if_congr ⟨?_, ?_⟩ rfl rfl
      · rintro ⟨u, hu, c, hc, e⟩
        refine ⟨c⁻¹, K.inv_mem hc, QuotientGroup.eq.2 ?_⟩
        have : g = c⁻¹ * u⁻¹ := by rw [← mul_inv_rev, show u * c = g⁻¹ from e, inv_inv]
        rw [this]
        simpa using hu
      · rintro ⟨c, hc, e⟩
        exact ⟨_, H.inv_mem (QuotientGroup.eq.1 e), _, K.inv_mem hc, by simp⟩
    have hpos : 0 < μ U :=
      measure_isOpen_pos_of_smulInvariant_of_ne_zero G hμ.ne_zero hUo ⟨_, 1, K.one_mem, rfl⟩
    rw [hIJ _ (e ▸ (integrable_indicator_iff hUo.measurableSet).2
      (integrableOn_const hUc.measure_lt_top.ne)), e, integral_indicator_const _ hUo.measurableSet]
    simpa [Measure.real, ENNReal.toReal_eq_zero_iff] using ⟨hpos.ne', hUc.measure_lt_top.ne⟩

end General

open GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem isClosed_unipB : IsClosed (unipB k (Fin m) : Set (GL (Fin m) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have hc : ∀ i j, Continuous fun g : GL (Fin m) k => g.val i j := fun i j =>
    Units.continuous_val.matrix_elem i j
  have : (unipB k (Fin m) : Set (GL (Fin m) k)) =
      (⋂ i, ⋂ j, ⋂ _ : j < i, {g : GL (Fin m) k | g.val i j = 0}) ∩ ⋂ i, {g : GL (Fin m) k | g.val i i = 1} := by
    ext g
    simp only [SetLike.mem_coe, mem_unipB, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [this]
  exact (isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    isClosed_eq (hc _ _) continuous_const).inter (isClosed_iInter fun _ => isClosed_eq (hc _ _) continuous_const)

theorem isTestFun_indicator :
    IsTestFun (((unipB k (Fin m) : Set (GL (Fin m) k)) * (KO k (Fin m) : Set (GL (Fin m) k))).indicator
      fun _ => (1 : ℂ)) := by
  refine ⟨indicator_mul_left, ?_, _, isCompact_KO, fun g hg => ?_⟩
  · exact (LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ))
      ⟨isClosed_unipB.mul_right_of_isCompact isCompact_KO, isOpen_KO.mul_left⟩).isLocallyConstant
  · obtain ⟨u, hu, c, hc, e⟩ := Set.mem_of_indicator_ne_zero hg
    exact ⟨u, hu, c, hc, e.symm⟩

theorem exists_isInvIntegral (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m : ℕ) :
    ∃ (I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ) (f : GL (Fin m) k → ℂ), IsInvIntegral I ∧ IsTestFun f ∧ I f ≠ 0 := by
  borelize k
  obtain ⟨I, h1, h2⟩ := exists_invariant_form (H := unipB k (Fin m)) isClosed_unipB
    (fun μ _ => inferInstance)
    (fun μ hμ => @UnipHaar.haar_isMulRightInvariant k _ _ _ _ (Fin m) (Fin m) (fun _ => Unit) _ _ _ _ _ _
      (points (Fin m)) (inferInstance : MeasurableSpace (unipB k (Fin m)))
      (inferInstance : BorelSpace (unipB k (Fin m))) μ hμ)
    (KO k (Fin m)) isOpen_KO isCompact_KO
  exact ⟨I, _, fun f hf => h1 f hf.1 hf.2.1.continuous hf.2.2, isTestFun_indicator, h2⟩

end GlobalTheory.LocLanglands.InvInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeepPuVolAR
section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe.KeepD

variable {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X)

set_option maxHeartbeats 4000000 in

theorem toTerm_eTT (u u' : D.what₂.Word) (s : TT Y u u') : (eTT Z Y u u' s).toTerm = eRT Z Y u u' s.toTerm := (by with_unfolding_all exact (Eq.refl (eRT Z Y u u' s.toTerm) :))

set_option maxHeartbeats 4000000 in

def eFib (u u' : D.what₂.Word) (t : RT Y u u') : fib Y t ≃ fib (reY Z Y) (eRT Z Y u u' t) :=
  Equiv.subtypeEquiv (eTT Z Y u u') fun s => by
    rw [toTerm_eTT]
    exact (eRT Z Y u u').injective.eq_iff.symm

set_option maxHeartbeats 4000000 in

theorem aT_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u u' : D.what₂.Word) (s : TT Y u u') (x : ColT (h.shInj u')) :
    eCure Z h h' u (aT h u u' s x) = aT h' (wd Z u) (wd Z u') (eTT Z Y u u' s) (eCure Z h h' u' x) := (by with_unfolding_all exact (
  Eq.refl (aT h u u' s x) :))

set_option maxHeartbeats 4000000 in

theorem aR_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u u' : D.what₂.Word) (t : RT Y u u') (x : ColT (h.shInj u')) :
    eCure Z h h' u (aR h u u' t x) = aR h' (wd Z u) (wd Z u') (eRT Z Y u u' t) (eCure Z h h' u' x) := by
  letI := h.fibFT t
  letI := h'.fibFT (eRT Z Y u u' t)
  unfold aR
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply, map_sum]
  exact Fintype.sum_equiv (eFib Z Y u u' t) _ _ fun s => aT_keep Z Y u u' s.1 x

set_option maxHeartbeats 4000000 in

theorem pu_keep {h : FinX Y} {h' : FinX (reY Z Y)} (u : D.what₂.Word) (x : ColT (h.shInj u)) :
    eHHre Z X (puC h u x) = puC h' (wd Z u) (eCure Z h h' u x) := (by with_unfolding_all exact (Eq.refl (puC h u x) :))

set_option maxHeartbeats 4000000 in

theorem vol_keep (u : D.what₂.Word) : Y.volN u = (reY Z Y).volN u ∧ Y.volH u = (reY Z Y).volH u := by
  constructor
  · exact (by with_unfolding_all exact (Eq.refl (Y.volN u) :))
  · exact (by with_unfolding_all exact (Eq.refl (Y.volH u) :))

end GlobalTheory.Mem.SRe.KeepD

namespace GlobalTheory.Mem.SRe

set_option maxHeartbeats 4000000 in

theorem keep_pu_vol_aR : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y)), (∀ u x, eHHre Z X (puC h u x) = puC h' (wd Z u) (eCure Z h h' u x)) ∧ (∀ u, Y.volN u = (reY Z Y).volN u ∧ Y.volH u = (reY Z Y).volH u) ∧ ∀ u u' (t : RT Y u u') x, eCure Z h h' u (aR h u u' t x) = aR h' (wd Z u) (wd Z u') (eRT Z Y u u' t) (eCure Z h h' u' x) :=
  fun _ Z _ Y _ _ => ⟨fun u x => KeepD.pu_keep Z Y u x, fun u => KeepD.vol_keep Z Y u,
    fun u u' t x => KeepD.aR_keep Z Y u u' t x⟩

end GlobalTheory.Mem.SRe
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestKTypeCoefficientWeightEqMinorWeightsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), σ = D.what₂.embLL → ∀ M : DSModel (Wc D i) (parAt (Wc D i) σ), (∀ τ a, M.ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) → ∃ x₁ x₂ x₃ : D.what₂.Tau → ℤ, ∀ τ, (x₁ τ : ℚ) = -(D.hc τ).e i + ((Vc D i).rank : ℚ) / 2 ∧ (x₂ τ : ℚ) = -(D.hc τ).e i - ((Vc D i).rank : ℚ) / 2 ∧ (x₃ τ : ℚ) = -(((((Wc D i).sig (tauE D τ)).1 : ℚ) - ((Wc D i).sig (tauE D τ)).2) / 2 + (-(D.hc τ).e i - 1 / 2)) ∧ (∀ a, Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) a = (wtK ((Wc D i).sig (tauE D τ)).1 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₁ τ) (x₂ τ) a : ℝ)) ∧ ∀ j : Fin (Vc D i).rank, wtU ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 (aPl D i ((Wc D i).sig (tauE D τ)).1 τ) (aMi D i ((Wc D i).sig (tauE D τ)).1 ((Wc D i).sig (tauE D τ)).2 τ) (x₃ τ) j = -(Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w j := by
  first | exact @GlobalTheory.JointHarm.weights_of_minors | exact GlobalTheory.JointHarm.weights_of_minors | (intros; apply GlobalTheory.JointHarm.weights_of_minors <;> assumption)
end

