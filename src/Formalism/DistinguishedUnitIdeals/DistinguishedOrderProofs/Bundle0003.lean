import Mathlib
import Formalism.DistinguishedUnitIdeals.StatementE
import Formalism.DistinguishedUnitIdeals.Bundle0001
import Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.Bundle0001

-- bundled from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.BaseGamC
section
noncomputable section

namespace Formalism.ExponentWindows.E

open PowerSeries

namespace PhiGammaCoboundaries

section
variable {O : Type} [CommRing O] {B : Base O} {n : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O) V]

theorem base_phi_C (B : Base O) (m : O) : B.φ (C m) = C m := by
  rw [← PowerSeries.algebraMap_eq]
  exact B.φ.commutes m

theorem base_gam_C (B : Base O) (m : O) : B.γ (C m) = C m := by
  rw [← PowerSeries.algebraMap_eq]
  exact B.γ.commutes m

theorem cob_zero (L : Lat B n V) : L.IsCobound 0 0 := by
  exact ⟨0, by funext i; simp [Lat.dφ], by funext i; simp [Lat.dγ]⟩

theorem cob_add (L : Lat B n V) {y z y' z' : ZMod n → V} (h : L.IsCobound y z)
    (h' : L.IsCobound y' z') : L.IsCobound (y + y') (z + z') := by
  obtain ⟨m, rfl, rfl⟩ := h
  obtain ⟨m', rfl, rfl⟩ := h'
  refine ⟨m + m', ?_, ?_⟩ <;> funext i <;> simp only [Lat.dφ, Lat.dγ, Pi.add_apply, map_add] <;> abel

theorem cob_neg (L : Lat B n V) {y z : ZMod n → V} (h : L.IsCobound y z) :
    L.IsCobound (-y) (-z) := by
  obtain ⟨m, rfl, rfl⟩ := h
  refine ⟨-m, ?_, ?_⟩ <;> funext i <;> simp only [Lat.dφ, Lat.dγ, Pi.neg_apply, map_neg] <;> abel

theorem cob_sub (L : Lat B n V) {y z y' z' : ZMod n → V} (h : L.IsCobound y z)
    (h' : L.IsCobound y' z') : L.IsCobound (y - y') (z - z') := by
  simpa [sub_eq_add_neg] using cob_add L h (cob_neg L h')

theorem cob_smul (L : Lat B n V) (a : O) {y z : ZMod n → V} (h : L.IsCobound y z) :
    L.IsCobound (C a • y) (C a • z) := by
  obtain ⟨m, rfl, rfl⟩ := h
  refine ⟨C a • m, ?_, ?_⟩ <;> funext i <;>
    simp only [Lat.dφ, Lat.dγ, Pi.smul_apply, L.φ_semi, L.γ_semi, base_phi_C, base_gam_C, smul_sub]

theorem cob_sum (L : Lat B n V) {ι : Type} (s : Finset ι) (y z : ι → ZMod n → V)
    (h : ∀ c ∈ s, L.IsCobound (y c) (z c)) :
    L.IsCobound (∑ c ∈ s, y c) (∑ c ∈ s, z c) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simpa using cob_zero L) ?_
  intro c s hc ih h
  rw [Finset.sum_insert hc, Finset.sum_insert hc]
  exact cob_add L (h c (Finset.mem_insert_self c s))
    (ih fun c' hc' => h c' (Finset.mem_insert_of_mem hc'))

theorem lc_pow (B : Base O) (k : ℕ) : B.lc ^ k = C ((B.ℓ : O) ^ k) := by
  unfold Base.lc
  rw [map_pow]

end

theorem combine {O : Type} [CommRing O] {n : ℕ} {V₁ V₂ : Type} [AddCommGroup V₁]
    [Module (PowerSeries O) V₁] [AddCommGroup V₂] [Module (PowerSeries O) V₂]
    (f : V₁ →ₗ[PowerSeries O] V₂) (s : Finset (ZMod n)) (l : O) (e e₁ e₂ : ℕ) (he : e = e₂ + e₁)
    (a m : ZMod n → O) (ham : ∀ c ∈ s, a c * m c = l ^ e₂)
    (y₀ : ZMod n → V₂) (yc : ZMod n → ZMod n → V₂) (y1 : ZMod n → ZMod n → V₁) :
    (C (l ^ e) • y₀ - fun i => f ((∑ c ∈ s, C (a c) • y1 c) i)) =
      C (l ^ e₂) • (C (l ^ e₁) • y₀ - ∑ c ∈ s, yc c) -
        ∑ c ∈ s, C (a c) • ((fun i => f (y1 c i)) - C (m c) • yc c) := by
  subst he
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, map_sum, map_smul, smul_sub,
    Finset.smul_sum, Finset.sum_sub_distrib, smul_smul]
  have h1 : ∑ c ∈ s, (C (a c) * C (m c)) • yc c i = ∑ c ∈ s, C (l ^ e₂) • yc c i :=
    Finset.sum_congr rfl fun c hc => by rw [← map_mul, ham c hc]
  rw [h1, pow_add, map_mul]
  abel

end PhiGammaCoboundaries

open PhiGammaCoboundaries in
theorem thmE_of (h1 : RhoExists) (h2 : RhoLin) (h3 : RhoFun) (h4 : Step1) : ThmEAssembly := by
  intro O _ B n _ Cu abelian₂ j M g sig rr a₀ kap V₁ V₂ V₀ _ _ _ _ _ _ L₁ L₂ L₀ e₀ h Zf₁ Zf₂
    hM hB hG1 hG2 hell he1 he2 hZsmul hZrho hZext hW κ hκ
  obtain ⟨Y, hYrep, hYgood⟩ := hZext κ hκ
  obtain ⟨w, yc, zc, hwc, hcob⟩ := h4 O B n Cu abelian₂ j M g sig rr V₂ V₀ L₂ L₀ e₀ Y κ.1 κ.2 hM hB
    hG2 hell he1 he2 hYrep hYgood
  have H : ∀ c ∈ Cu.cuts, ∃ (w' : V₁) (k : ℕ) (ε : Oˣ), k ≤ 2 * kap ∧ L₁.Wc Cu abelian₂ c w' ∧
      h.f w' - C ((ε : O) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + k)) • w c ∈ sm X (L₂.N c) :=
    fun c hc => hW c hc (w c) (hwc c hc).1
  choose! W1 K E hK hW1 hD using H
  have H2 : ∀ c ∈ Cu.cuts, ∃ y z : ZMod n → V₁, L₁.IsRho c j M g sig (W1 c) y z :=
    fun c hc => h1 O B n Cu j M g sig V₁ L₁ hB hG1 c hc (W1 c) (hW1 c hc).1
  choose! Y1 Z1 hR using H2
  let mc : ZMod n → O := fun c => (E c : O) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + K c)
  let ac : ZMod n → O := fun c => (((E c)⁻¹ : Oˣ) : O) * (B.ℓ : O) ^ (2 * kap - K c)
  have ham : ∀ c ∈ Cu.cuts, ac c * mc c = (B.ℓ : O) ^ (rr + 2 * sig + 2 * a₀ + 2 * kap) := by
    intro c hc
    have hk := hK c hc
    calc ac c * mc c = ((((E c)⁻¹ : Oˣ) : O) * (E c : O)) *
          ((B.ℓ : O) ^ (2 * kap - K c) * (B.ℓ : O) ^ (2 * sig + 2 * a₀ + rr + K c)) := by
          simp only [ac, mc]; ring
      _ = _ := by
          rw [Units.inv_mul, one_mul, ← pow_add]
          congr 1
          omega
  have hlin : ∀ c ∈ Cu.cuts, L₂.IsCobound ((fun i => h.f (Y1 c i)) - C (mc c) • yc c)
      ((fun i => h.f (Z1 c i)) - C (mc c) • zc c) := fun c hc =>
    h2 O B n Cu j M g sig V₂ L₂ hB hG2 c hc (mc c) (w c) (h.f (W1 c)) (yc c) (zc c) _ _
      (hwc c hc).2 (h3 O B n j M g sig V₁ V₂ L₁ L₂ h c (W1 c) (Y1 c) (Z1 c) (hR c hc)) (hD c hc)
  refine ⟨∑ c ∈ Cu.cuts, (C (ac c) • Y1 c, C (ac c) • Z1 c), ?_, ?_⟩
  · exact AddSubgroup.sum_mem _ fun c hc =>
      hZsmul (ac c) (Y1 c, Z1 c) (hZrho c hc (W1 c) (hW1 c hc) (Y1 c) (Z1 c) (hR c hc))
  · have e : 2 * rr + 4 * sig + 2 * a₀ + 2 * kap =
        (rr + 2 * sig + 2 * a₀ + 2 * kap) + (rr + 2 * sig) := by ring
    simp only [lc_pow] at hcob ⊢
    simp only [Prod.fst_sum, Prod.snd_sum]
    rw [e, combine h.f Cu.cuts (B.ℓ : O) _ (rr + 2 * sig) (rr + 2 * sig + 2 * a₀ + 2 * kap) rfl
        ac mc ham κ.1 yc Y1,
      combine h.f Cu.cuts (B.ℓ : O) _ (rr + 2 * sig) (rr + 2 * sig + 2 * a₀ + 2 * kap) rfl
        ac mc ham κ.2 zc Z1]
    exact cob_sub L₂ (cob_smul L₂ _ hcob)
      (cob_sum L₂ Cu.cuts _ _ fun c hc => cob_smul L₂ (ac c) (hlin c hc))

end Formalism.ExponentWindows.E
end
end

-- bundled from Formalism.DistinguishedUnitIdeals.DistinguishedOrderProofs.DUConst
section
noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

section Helpers

variable {O : Type} [CommRing O] [IsDomain O]

theorem map_distinguished_eq_X_pow (ϖ : O) (E : Polynomial O)
    (hE : E.IsDistinguishedAt (Ideal.span {ϖ})) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (E : PowerSeries O) =
      X ^ E.natDegree := by
  ext n
  rw [coeff_map, Polynomial.coeff_coe, coeff_X_pow]
  rcases lt_trichotomy n E.natDegree with h | h | h
  · rw [if_neg h.ne]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hE.mem h)
  · rw [if_pos h, h, hE.monic.coeff_natDegree, map_one]
  · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, map_zero]

theorem map_unitDist (ϖ : O) (d : ℕ) (p : PowerSeries O) (hp : UnitDist ϖ d p) :
    ∃ U : PowerSeries (O ⧸ Ideal.span {ϖ}), IsUnit U ∧
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) p = U * X ^ d := by
  obtain ⟨u, E, hu, hE, hd, rfl⟩ := hp
  refine ⟨PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) u, hu.map _, ?_⟩
  rw [map_mul, map_distinguished_eq_X_pow ϖ E hE, hd]

theorem map_prod_unitDist (ϖ : O) (p : ℕ → PowerSeries O) (dg b : ℕ → ℕ) (I : Finset ℕ)
    (hp : ∀ s ∈ I, UnitDist ϖ (dg s) (p s)) :
    ∃ U : PowerSeries (O ⧸ Ideal.span {ϖ}), IsUnit U ∧
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (∏ s ∈ I, p s ^ b s) =
        U * X ^ (∑ s ∈ I, b s * dg s) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, isUnit_one, by simp⟩
  | insert t I ht ih =>
    obtain ⟨U, hU, hUe⟩ := ih (fun s hs => hp s (Finset.mem_insert_of_mem hs))
    obtain ⟨V, hV, hVe⟩ := map_unitDist ϖ (dg t) (p t) (hp t (Finset.mem_insert_self t I))
    refine ⟨V ^ b t * U, (hV.pow _).mul hU, ?_⟩
    rw [Finset.prod_insert ht, Finset.sum_insert ht, map_mul, hUe, map_pow, hVe, pow_add,
      mul_pow, ← pow_mul, mul_comm (dg t) (b t)]
    ring

end Helpers

theorem unit_constant_holds : DUConst := by
  intro O _ _ _ ϖ hϖ ℓ p I b g B y N c a hp hD h
  have hmax : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  have : IsDomain (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.isDomain _
  by_cases hc : c = 0
  · rw [hc]; exact dvd_zero _
  obtain ⟨v, w, hc'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  by_contra hy
  have hvy : v < y := by
    by_contra hvy
    apply hy
    rw [hc']
    exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (not_lt.mp hvy)) _
  set P := ∏ s ∈ I, p s ^ b s with hP
  set z := C (w : O) * P - C (ϖ ^ (y - v)) * a with hz
  have hz' : C (ϖ ^ (N + v)) * z ∈ Ideal.span {p g ^ B} := by
    have heq : C (ϖ ^ N) * (C c * P - C (ϖ ^ y) * a) = C (ϖ ^ (N + v)) * z := by
      rw [hz, hc']
      have hy' : y = v + (y - v) := by omega
      conv_lhs => rw [hy']
      simp only [map_mul, map_pow, pow_add]
      ring
    rw [← heq]; exact h
  have hzmem := mem_span_pow_of_uniformizer_mul O ϖ hϖ (ℓ ^ g) (p g) (hp g (Finset.mem_insert_self g I)) B (N + v)
    z hz'
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hzmem
  obtain ⟨U, hU, hUe⟩ := map_prod_unitDist ϖ p (fun s => ℓ ^ s) b I
    (fun s hs => hp s (Finset.mem_insert_of_mem hs))
  obtain ⟨V, -, hVe⟩ := map_unitDist ϖ (ℓ ^ g) (p g) (hp g (Finset.mem_insert_self g I))
  have hmap := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ}))) hq
  have hzero : Ideal.Quotient.mk (Ideal.span {ϖ}) (ϖ ^ (y - v)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr (dvd_pow_self ϖ (by omega))
  rw [hz, map_sub, map_mul, map_mul, PowerSeries.map_C, PowerSeries.map_C, hzero, map_zero,
    zero_mul, sub_zero, hUe, map_mul, map_pow, hVe, mul_pow, ← pow_mul] at hmap
  have hW : IsUnit (C (Ideal.Quotient.mk (Ideal.span {ϖ}) (w : O)) * U) :=
    ((w.isUnit.map (Ideal.Quotient.mk (Ideal.span {ϖ}))).map C).mul hU
  set D := ∑ s ∈ I, b s * ℓ ^ s
  have hc1 := congrArg (coeff D) hmap
  have hlhs : coeff D (C (Ideal.Quotient.mk (Ideal.span {ϖ}) (w : O)) * (U * X ^ D)) =
      constantCoeff (C (Ideal.Quotient.mk (Ideal.span {ϖ}) (w : O)) * U) := by
    rw [← mul_assoc, coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self,
      coeff_zero_eq_constantCoeff]
  have hrhs : coeff D (V ^ B * X ^ (ℓ ^ g * B) *
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) q) = 0 := by
    have : V ^ B * X ^ (ℓ ^ g * B) * PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) q =
        X ^ (ℓ ^ g * B) * (V ^ B * PowerSeries.map (Ideal.Quotient.mk (Ideal.span {ϖ})) q) := by
      ring
    rw [this, coeff_X_pow_mul', if_neg (by rw [mul_comm]; omega)]
  rw [hlhs, hrhs] at hc1
  exact (isUnit_constantCoeff _ hW).ne_zero hc1

end Formalism.ExponentWindows
end
end

