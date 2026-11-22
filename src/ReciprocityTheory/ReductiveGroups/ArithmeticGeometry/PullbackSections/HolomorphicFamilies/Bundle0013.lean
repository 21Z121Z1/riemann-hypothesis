import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.PlaceBoundOwnPrimeOf
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

theorem not_both_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : (a : 𝓞 K) ∈ la.asIdeal) (hb : (b : 𝓞 K) ∈ la.asIdeal) : False := by
  have hg := Nat.gcd_eq_gcd_ab a b
  have h1 : ((Nat.gcd a b : ℕ) : ℤ) = 1 := by rw [hab]; rfl
  have e : (1 : 𝓞 K) = (a : 𝓞 K) * ((Nat.gcdA a b : ℤ) : 𝓞 K) + (b : 𝓞 K) * ((Nat.gcdB a b : ℤ) : 𝓞 K) := by
    have : ((1 : ℤ) : 𝓞 K) = (((a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b : ℤ) : 𝓞 K) := by
      rw [← hg, h1]
    push_cast at this
    exact this
  have hone : (1 : 𝓞 K) ∈ la.asIdeal := by
    rw [e]
    exact la.asIdeal.add_mem (la.asIdeal.mul_mem_right _ ha) (la.asIdeal.mul_mem_right _ hb)
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hone)

theorem vLa_nat_nonneg {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) :
    0 ≤ vLa la (p : K) := by
  by_cases hp : (p : K) = 0
  · simp [vLa, hp]
  unfold vLa
  have e : (p : K) = ((p : 𝓞 K) : K) := by simp
  rw [e] at hp ⊢
  have h1 := la.valuation_le_one (K := K) (p : 𝓞 K)
  have h2 : (la.valuation K) ((p : 𝓞 K) : K) ≠ 0 := (Valuation.ne_zero_iff _).mpr hp
  have h3 := (WithZero.log_le_log h2 one_ne_zero).mpr h1
  rw [WithZero.log_one] at h3
  omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightAssemblyClause
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj

theorem nonneg_add_of_neg_le (c : ℝ) (x : EReal) (h : ((-c : ℝ) : EReal) ≤ x) : 0 ≤ (c : EReal) + x := by
  induction x using EReal.rec with
  | bot => simp at h
  | coe y =>
      have hy : -c ≤ y := EReal.coe_le_coe_iff.mp h
      rw [← EReal.coe_add]
      exact EReal.coe_nonneg.mpr (by linarith)
  | top => simp

theorem le_val_of_mem_span {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
    [Algebra (𝓞 K) R] [IsScalarTower (𝓞 K) K R] {la : HeightOneSpectrum (𝓞 K)} {v : R → EReal} (hv : IsVal la v)
    {s : Set R} {c : EReal} (hc : ∀ g ∈ s, c ≤ v g) : ∀ g ∈ Submodule.span (𝓞 K) s, c ≤ v g := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem x hx => exact hc x hx
  | zero => rw [hv.zero]; exact le_top
  | add x y _ _ hx hy => exact (le_min hx hy).trans (hv.add x y)
  | smul a x _ hx =>
      rw [← algebraMap_smul K a x]
      by_cases ha : (algebraMap (𝓞 K) K a) = 0
      · rw [ha, zero_smul, hv.zero]; exact le_top
      · rw [hv.smul _ _ ha]
        have h1 : (0 : EReal) ≤ (((vAdd la (algebraMap (𝓞 K) K a) : ℤ) : ℝ) : EReal) := by
          have h0 : 0 ≤ vAdd la (algebraMap (𝓞 K) K a) := by
            unfold vAdd
            have hle : la.valuation K (algebraMap (𝓞 K) K a) ≤ 1 := la.valuation_le_one (K := K) a
            have hne : la.valuation K (algebraMap (𝓞 K) K a) ≠ 0 := by simpa using ha
            obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.mp hne
            have hu1 : u ≤ 1 := by rw [← hu] at hle; exact_mod_cast hle
            rw [← hu, show ((u : WithZero (Multiplicative ℤ))) = WithZero.exp (Multiplicative.toAdd u) from rfl,
              WithZero.log_exp]
            have h3 : Multiplicative.toAdd u ≤ 0 := Multiplicative.toAdd_le.mpr hu1
            linarith
          exact_mod_cast h0
        calc c ≤ v x := hx
          _ = 0 + v x := (zero_add _).symm
          _ ≤ _ := add_le_add h1 le_rfl

theorem WWc_le_Mlat {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (s : 𝓞 B.KO)
    (hs : s ≠ 0) (w : WeightFamilies.Wt D j)
    (hb : ∀ G ∈ X.thAll w, ∀ la (y : X.Pt la),
      (((-(((vAdd la (s : B.KO) : ℤ) : ℝ))) : ℝ) : EReal) ≤ X.vAt la y (X.inc w G)) :
    X.WWc s w ≤ B.Mlat j w := by
  unfold WeightAlgebra.PJ.WWc
  intro F hF
  obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hF
  rw [X.Mlat_eq]
  intro la y
  have hsK : ((s : B.KO)) ≠ 0 := by exact_mod_cast hs
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [← algebraMap_smul B.KO s G, map_smul, X.vAt_smul la y _ _ hsK]
  exact nonneg_add_of_neg_le _ _ (hb G hG la y)

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
end
end

