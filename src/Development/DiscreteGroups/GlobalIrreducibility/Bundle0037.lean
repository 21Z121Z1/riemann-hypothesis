import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0036
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0033
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0032
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0013
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0031
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0034

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzFeIter
section
noncomputable section

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL GlobalTheory.LocLanglands Matrix

namespace DiscreteGroups.sglob.DzFe

theorem lFE_of_fe : FunctionalEquationAtIndex → DzType.LFE := by
  intro hfe g _ m ψ₀ hψ τ hτ γ hγ l hl x hx
  have hfix : ∀ k, ∀ h : Gn g (m + 1),
      (∃ b : GL (Fin m) (ZMod g), (∀ i j : Fin m, i < j → (b : Matrix (Fin m) (Fin m) (ZMod g)) i j = 0) ∧
        corner b = cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹) →
      τ.ρ h (τ.ρ (cyc g (m + 1) ^ k)⁻¹ x) = τ.ρ (cyc g (m + 1) ^ k)⁻¹ x := by
    rintro k h ⟨b, hb, hcb⟩
    have e : h * (cyc g (m + 1) ^ k)⁻¹ =
        (cyc g (m + 1) ^ k)⁻¹ * (cyc g (m + 1) ^ k * h * (cyc g (m + 1) ^ k)⁻¹) := by group
    calc τ.ρ h (τ.ρ (cyc g (m + 1) ^ k)⁻¹ x) = τ.ρ (h * (cyc g (m + 1) ^ k)⁻¹) x := by rw [map_mul]; rfl
      _ = τ.ρ ((cyc g (m + 1) ^ k)⁻¹ * corner b) x := by rw [e, ← hcb]
      _ = τ.ρ (cyc g (m + 1) ^ k)⁻¹ (τ.ρ (corner b) x) := by rw [map_mul]; rfl
      _ = τ.ρ (cyc g (m + 1) ^ k)⁻¹ x := by rw [hx b hb]
  have step : ∀ t, t < m → γ * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x) =
      (g : ℂ) ^ ((m + 1) * m / 2 + (t + 1)) * l (τ.ρ (cyc g (m + 1) ^ (t + 1))⁻¹ x) := by
    intro t ht
    have hv : τ.ρ (cyc g (m + 1))⁻¹ (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x) = τ.ρ (cyc g (m + 1) ^ (t + 1))⁻¹ x := by
      rw [pow_succ, _root_.mul_inv_rev, map_mul]; rfl
    have := hfe g m ψ₀ hψ τ hτ γ hγ l hl (m - 1 - t) (by omega) (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x)
      (fun h hh => hfix t h (colFix_conj ht h hh)) (fun h hh => hfix t h (rowFix_conj ht h hh))
    rw [this, hv, show (m + 1) * m / 2 + m - (m - 1 - t) = (m + 1) * m / 2 + (t + 1) by omega]
  have key : ∀ t, t ≤ m → γ ^ t * l x =
      (g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x) := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
      have ih := ih (by omega)
      have h2 : (t + 1) * (t + 1 + 1) / 2 = t * (t + 1) / 2 + (t + 1) := by
        rw [show (t + 1) * (t + 1 + 1) = t * (t + 1) + 2 * (t + 1) by ring,
          Nat.add_mul_div_left _ _ (by norm_num)]
      have hE : t * ((m + 1) * m / 2) + t * (t + 1) / 2 + ((m + 1) * m / 2 + (t + 1)) =
          (t + 1) * ((m + 1) * m / 2) + (t + 1) * (t + 1 + 1) / 2 := by
        rw [h2]; ring
      calc γ ^ (t + 1) * l x = γ * (γ ^ t * l x) := by ring
        _ = γ * ((g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x)) := by
            rw [ih]
        _ = (g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) * (γ * l (τ.ρ (cyc g (m + 1) ^ t)⁻¹ x)) := by
            ring
        _ = (g : ℂ) ^ (t * ((m + 1) * m / 2) + t * (t + 1) / 2) *
            ((g : ℂ) ^ ((m + 1) * m / 2 + (t + 1)) * l (τ.ρ (cyc g (m + 1) ^ (t + 1))⁻¹ x)) := by
            rw [step t (by omega)]
        _ = _ := by rw [← mul_assoc, ← pow_add, hE]
  have hcm : (cyc g (m + 1) ^ m)⁻¹ = cyc g (m + 1) := by
    have h1 := cyc_pow_eq_one (g := g) m
    rw [pow_succ] at h1
    exact inv_eq_of_mul_eq_one_right h1
  have hfin := key m le_rfl
  rw [hcm] at hfin
  have hexp : m * (m + 1) ^ 2 / 2 = m * ((m + 1) * m / 2) + m * (m + 1) / 2 := by
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self m
    have h1 : (m + 1) * m / 2 = r := by rw [mul_comm, hr]; omega
    have h2 : m * (m + 1) / 2 = r := by rw [hr]; omega
    have h3 : m * (m + 1) ^ 2 / 2 = r * (m + 1) := by
      rw [show m * (m + 1) ^ 2 = 2 * (r * (m + 1)) by
        rw [show m * (m + 1) ^ 2 = m * (m + 1) * (m + 1) by ring, hr]; ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [h1, h2, h3]; ring
  rw [longElt_corner_eq_cyc, hfin, hexp]

end DiscreteGroups.sglob.DzFe
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalEig
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_H_eigen {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
    [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (g : ℕ) [Fact g.Prime]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) (n : ℕ) (hn : 0 < n)
    (hg : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2) (hN : normV w' = g ^ n)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (K : Type) [Field K] [Algebra (ZMod g) K] (red : 𝓞 E' →+* K) (hr : Function.Surjective red)
    (hk : RingHom.ker red = w'.asIdeal)
    (m : ℕ) (b : WDRep h (Fin m → ℂ)) (hb : b.ρ.IsIrreducible)
    (htame : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → b.ρ σ = 1) (hm : finrank ℂ (Fin m → ℂ) = n)
    (ξ : Kˣ →* ℂˣ)
    (hξf : ∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        (WD.mk b).inePol (AlgEquiv.restrictScalars E (t : G E' Ω)) =
          ∏ j ∈ Finset.range n, (X - C ((ξ (z ^ g ^ j) : ℂˣ) : ℂ))) :
    ∃ (v₀ : Fin m → ℂ) (χH : Weil h → ℂ), v₀ ≠ 0 ∧
      (∀ σ : Weil h, (n : ℤ) ∣ deg σ → b.ρ σ v₀ = χH σ • v₀) ∧
      (∀ (t : Ine (F := E') A) (x : 𝓞 E') (z : Kˣ), red x = z →
        Valued.v ((a' (ineIncl h' t) : w'.adicCompletion E') - algebraMap E' (w'.adicCompletion E') (x : E')) < 1 →
        χH (ineIncl h (resI t)) = ((ξ z : ℂˣ) : ℂ)) ∧
      Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) = ⊤ := by
  classical
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hq' : normV w' = normV w ^ n := by rw [hq, hN]
  let I : Subgroup (Weil h) := (Ine (F := E) A).comap (Weil h).subtype
  haveI hInorm : I.Normal := ⟨fun t ht g0 => by
    show ((g0 * t * g0⁻¹ : Weil h) : G E Ω) ∈ Ine (F := E) A
    exact conj_mem_Ine (Weil_le_Dec h g0.2) ht⟩
  have hgen : ∀ σ : Weil h, ∃ k : ℤ, ∃ t ∈ I, σ = frob h ^ k * t := fun σ => by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    exact ⟨deg σ, ineIncl h τ, τ.2, hτ⟩
  have hcomm : ∀ s ∈ I, ∀ t ∈ I, b.ρ s * b.ρ t = b.ρ t * b.ρ s := by
    intro s hs t ht
    let s' : Ine (F := E) A := ⟨s, hs⟩
    let t' : Ine (F := E) A := ⟨t, ht⟩
    have h1 : b.ρ (ineIncl h (s' * t' * s'⁻¹ * t'⁻¹)) = 1 := htame _ (isWild_commutator s' t')
    have h2 : ineIncl h (s' * t' * s'⁻¹ * t'⁻¹) = s * t * s⁻¹ * t⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  have hfrob : ∀ t ∈ I, b.ρ (frob h * t * (frob h)⁻¹) = b.ρ t ^ normV w := by
    intro t ht
    let t' : Ine (F := E) A := ⟨t, ht⟩
    let c' : Ine (F := E) A :=
      ⟨(frob h : G E Ω) * t' * (frob h : G E Ω)⁻¹, conj_mem_Ine (isFrob_frob (h := h)).1 t'.2⟩
    have h1 : b.ρ (ineIncl h (c' * (t' ^ normV w)⁻¹)) = 1 :=
      htame _ (isWild_frob (isFrob_frob (h := h)) t')
    have h2 : ineIncl h (c' * (t' ^ normV w)⁻¹) = frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : frob h * t * (frob h)⁻¹ = (frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹) * t ^ normV w := by group
    rw [e, map_mul, h1, one_mul, map_pow]
  obtain ⟨η, u, c, hu, huI, hφn, hchar, hper, hmin⟩ :=
    DzCliff.clifford b.ρ hb I (frob h) (normV w) n hm hn hgen hcomm hfrob
  rw [hq] at hchar hper
  have hc0 : c ≠ 0 := fun h0 => DzCliff.rho_ne_zero b.ρ (frob h ^ n) hu (by rw [hφn, h0, zero_smul])
  have hcinv : b.ρ (frob h ^ n)⁻¹ u = c⁻¹ • u := by
    have h1 := DzCliff.rho_inv_apply b.ρ (frob h ^ n) u
    rw [hφn, map_smul] at h1
    calc b.ρ (frob h ^ n)⁻¹ u = c⁻¹ • (c • b.ρ (frob h ^ n)⁻¹ u) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • u := by rw [h1]
  have hz : ∀ k : ℤ, b.ρ ((frob h ^ n) ^ k) u = c ^ k • u := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, Module.End.mul_apply, hφn, map_smul, ih, smul_smul, zpow_add_one₀ hc0, mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, Module.End.mul_apply, hcinv, map_smul, ih, smul_smul, zpow_sub_one₀ hc0,
        mul_comm]
  have huH : ∀ σ : Weil h, (n : ℤ) ∣ deg σ → ∃ e : ℂ, b.ρ σ u = e • u := by
    intro σ hσ
    obtain ⟨k, hk'⟩ := hσ
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    rw [hτ, hk', map_mul, Module.End.mul_apply, huI (ineIncl h τ) τ.2, map_smul,
      show frob h ^ ((n : ℤ) * k) = (frob h ^ n) ^ k by rw [zpow_mul, zpow_natCast], hz, smul_smul]
    exact ⟨_, rfl⟩
  obtain ⟨R, hR⟩ := exists_resHom (A := A) ha' hk
  obtain ⟨β, hβ⟩ := exists_eigenChar b.ρ ((ineIncl h).comp (resI (E := E) (E' := E') (Ω := Ω) (A := A))) hu
    (fun t => ⟨_, huI (ineIncl h (resI t)) (resI t).2⟩)
  have hβη : ∀ t : Ine (F := E') A, ((β t : ℂˣ) : ℂ) = η (ineIncl h (resI t)) := fun t =>
    DzCliff.eig_unique hu (hβ t) (huI (ineIncl h (resI t)) (resI t).2)
  have hpos : 0 < g ^ n := pow_pos (Fact.out : g.Prime).pos n
  have hzK : ∀ z : Kˣ, z ^ g ^ n = z := pow_card_units w' g n hN K red hr hk hpos
  have hα : ∀ t, ((ξ.comp R) t) ^ (g ^ n - 1) = 1 := by
    intro t
    rw [MonoidHom.comp_apply, ← map_pow]
    have : R t ^ (g ^ n - 1) = 1 := by
      have h1 := hzK (R t)
      have h2 : R t ^ (g ^ n - 1) * R t = 1 * R t := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos), h1, one_mul]
      exact mul_right_cancel h2
    rw [this, map_one]
  have h1 : ∀ t, ∃ j : ℕ, β t = (ξ.comp R) t ^ g ^ j := by
    intro t
    obtain ⟨x, hx⟩ := exists_int_approx_compl w' _ (val_artin_ine ha' t).le
    have hRx : R t = Units.mk0 (red x) (red_ne_zero_of_approx ha' hk hx) := Units.ext (hR t x hx)
    have hp := hξf t x (R t) (hR t x hx).symm hx
    rw [WD.inePol_of_mem_Ine _ (res_mem_Ine t.2), WD.charPol_mk,
      show ineIncl h ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩ = ineIncl h (resI t) from rfl,
      hchar _ (resI t).2] at hp
    have hroot := congrArg (Polynomial.eval (η (ineIncl h (resI t)))) hp
    rw [Polynomial.eval_prod, Polynomial.eval_prod] at hroot
    have hl : ∏ j ∈ Finset.range n, Polynomial.eval (η (ineIncl h (resI t)))
        (X - C (η (ineIncl h (resI t)) ^ g ^ j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr hn) (by simp)
    rw [hl, eq_comm, Finset.prod_eq_zero_iff] at hroot
    obtain ⟨j, -, hj⟩ := hroot
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hj
    refine ⟨j, Units.ext ?_⟩
    rw [hβη, hj, MonoidHom.comp_apply, map_pow, Units.val_pow_eq_pow_val]
  obtain ⟨j₀, hj₀⟩ := char_orbit (ξ.comp R) β (g ^ n - 1) (Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne'
    (Fact.out : g.Prime).one_lt)) hα g h1
  have hαn : ∀ k t, ((ξ.comp R) t) ^ g ^ (k * n) = (ξ.comp R) t := by
    intro k t
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, pow_add, pow_mul, ih, MonoidHom.comp_apply, ← map_pow, hzK]
  set j : ℕ := n - j₀ % n with hj
  have hjn : j₀ + j = n * (j₀ / n + 1) := by
    have := Nat.div_add_mod j₀ n
    have := Nat.mod_lt j₀ hn
    rw [hj]; rw [Nat.mul_add, Nat.mul_one]; omega
  set v₀ := b.ρ (frob h ^ j)⁻¹ u with hv₀
  have hv₀0 : v₀ ≠ 0 := DzCliff.rho_ne_zero b.ρ _ hu
  have hv₀I : ∀ t ∈ I, b.ρ t v₀ = η t ^ g ^ j • v₀ :=
    DzCliff.eig_translate b.ρ I (frob h) g (by rw [← hq]; exact hfrob) huI j
  have hv₀H : ∀ σ : Weil h, ∃ e : ℂ, (n : ℤ) ∣ deg σ → b.ρ σ v₀ = e • v₀ := by
    intro σ
    by_cases hσ : (n : ℤ) ∣ deg σ
    · have hdeg : (n : ℤ) ∣ deg (frob h ^ j * σ * (frob h ^ j)⁻¹) := by simpa using hσ
      obtain ⟨e, he⟩ := huH _ hdeg
      refine ⟨e, fun _ => ?_⟩
      have e1 : σ * (frob h ^ j)⁻¹ = (frob h ^ j)⁻¹ * (frob h ^ j * σ * (frob h ^ j)⁻¹) := by group
      rw [hv₀, ← Module.End.mul_apply, ← map_mul, e1, map_mul, Module.End.mul_apply, he, map_smul]
    · exact ⟨0, fun h0 => absurd h0 hσ⟩
  choose χH hχH using hv₀H
  refine ⟨v₀, χH, hv₀0, fun σ hσ => hχH σ hσ, fun t x z hxz hx => ?_, ?_⟩
  · have hRz : R t = z := Units.ext (by rw [hR t x hx, hxz])
    have e1 := hχH (ineIncl h (resI t)) (by simp)
    have e2 := hv₀I (ineIncl h (resI t)) (resI t).2
    rw [DzCliff.eig_unique hv₀0 e1 e2, ← hβη]
    have h3 := hj₀ t
    have h4 : β t ^ g ^ j = (ξ.comp R) t := by
      rw [h3, ← pow_mul, ← pow_add, hjn, mul_comm, hαn]
    have h5 := congrArg Units.val h4
    rw [Units.val_pow_eq_pow_val] at h5
    rw [h5, MonoidHom.comp_apply, hRz]
  · apply DzCliff.eq_top_of_stable b.ρ hb
    · intro h0
      have hmem : b.ρ 1 v₀ ∈ Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) := Submodule.subset_span ⟨1, rfl⟩
      rw [h0, map_one, Module.End.one_apply, Submodule.mem_bot] at hmem
      exact hv₀0 hmem
    · intro τ v hv
      have hle : Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) ≤
          (Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀)).comap (b.ρ τ) := by
        rw [Submodule.span_le]
        rintro _ ⟨σ, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
        exact Submodule.subset_span ⟨τ * σ, rfl⟩
      exact hle hv

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalInd
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem eps_ind_step {E L Ω : Type} [Field E] [NumberField E] [Field L] [NumberField L] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra E L] [IsScalarTower E L Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {v : HeightOneSpectrum (𝓞 L)}
    (hv : IsPlaceOver A v) (hL : IsLocalExt L h) {ε : EpsFamily A} (hε : IsDeligneEps ε)
    {ψ : AddChar (w.adicCompletion E) Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1)
    {ψL : AddChar (v.adicCompletion L) Circle} (hcL : Continuous ψL)
    (hψL : ∀ z : L, ψL (algebraMap L _ z) = ψ (algebraMap E _ (Algebra.trace E L z)))
    (r : Weil hv →* Weil h) (hr : ∀ (σ : Weil hv) (z : Ω), (r σ : G E Ω) z = (σ : G L Ω) z)
    (hrs : ∀ (M : Type) [Monoid M] (f : Weil h →* M), IsSmooth f → IsSmooth (f.comp r))
    {m : ℕ} (hm : m = Module.finrank E L) (b : WDRep h (Fin m → ℂ)) (v₀ : Fin m → ℂ)
    (hsp : Submodule.span ℂ (Set.range fun σ => b.ρ σ v₀) = ⊤)
    (ξL₀ : Weil hv →* ℂˣ) (hξ : ∀ σ, b.ρ (r σ) v₀ = (ξL₀ σ : ℂ) • v₀)
    (ν₁ ν₂ : Weil h →* ℂˣ) (hν₁ : IsSmooth ν₁) (hν₂ : IsSmooth ν₂) :
    ∃ (hs₁ : IsSmooth (ξL₀ * ν₁.comp r)) (hs₂ : IsSmooth (ξL₀ * ν₂.comp r)),
      ε E w h ψ (WD.mk (b.twist ν₁ hν₁)) * ε L v hv ψL (WD.lpOfChar hv (ξL₀ * ν₂.comp r) hs₂) =
        ε E w h ψ (WD.mk (b.twist ν₂ hν₂)) * ε L v hv ψL (WD.lpOfChar hv (ξL₀ * ν₁.comp r) hs₁) := by
  have key : ∀ (ν : Weil h →* ℂˣ) (hν : IsSmooth ν), ∃ hs : IsSmooth (ξL₀ * ν.comp r),
      Induces (WD.lpOfChar hv (ξL₀ * ν.comp r) hs) (WD.mk (b.twist ν hν)) := by
    intro ν hν
    refine EpsUnique.induces_of_eigenvector E L Ω A w v h hv r hr hrs m (b.twist ν hν) v₀ (ξL₀ * ν.comp r) hm
      (fun σ => ?_) ?_
    · rw [WDRep.twist_ρ, LinearMap.smul_apply, hξ, smul_smul, MonoidHom.mul_apply, Units.val_mul,
        MonoidHom.comp_apply, mul_comm]
    · rw [eq_top_iff, ← hsp]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨σ, rfl⟩
      have e : b.ρ σ v₀ = ((ν σ)⁻¹ : ℂˣ) • ((b.twist ν hν).ρ σ v₀) := by
        rw [WDRep.twist_ρ, LinearMap.smul_apply, Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, one_smul]
      show b.ρ σ v₀ ∈ Submodule.span ℂ (Set.range fun σ => (b.twist ν hν).ρ σ v₀)
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)
  obtain ⟨hs₁, i₁⟩ := key ν₁ hν₁
  obtain ⟨hs₂, i₂⟩ := key ν₂ hν₂
  refine ⟨hs₁, hs₂, ?_⟩
  have d : (WD.lpOfChar hv (ξL₀ * ν₁.comp r) hs₁).lpDim = (WD.lpOfChar hv (ξL₀ * ν₂.comp r) hs₂).lpDim := by
    simp [WD.lpOfChar]
  exact hε.ind E L w v h hv hL ψ ψL hc h1 hcL hψL _ _ _ _ i₁ i₂ d

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalTR
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem tr_match (hTR : TameRec) {L E' Ω : Type} [Field L] [NumberField L] [IsTotallyComplex L] [Field E'] [NumberField E']
    [IsTotallyComplex E'] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (n : ℕ) (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 L)) (hv : IsPlaceOver A v) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (hgv : ((g : ℕ) : 𝓞 L) ∈ v.asIdeal) (hgv2 : ((g : ℕ) : 𝓞 L) ∉ v.asIdeal ^ 2)
    (hgw : ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal) (hgw2 : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2)
    (hvN : normV v = g ^ n) (hwN : normV w' = g ^ n)
    (aL : Weil hv →* (v.adicCompletion L)ˣ) (haL : IsLocalArtin hv aL)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (π : Ω) (hπ : π ^ (g ^ n - 1) = (g : Ω))
    (t : Ine (F := L) A) (t' : Ine (F := E') A) (htt : ∀ z : Ω, (t : G L Ω) z = (t' : G E' Ω) z)
    (y : 𝓞 L) (hy : Valued.v ((aL (ineIncl hv t) : v.adicCompletion L) - algebraMap L (v.adicCompletion L) (y : L)) < 1)
    (x : 𝓞 E') (hx : Valued.v ((a' (ineIncl h' t') : w'.adicCompletion E') -
      algebraMap E' (w'.adicCompletion E') (x : E')) < 1) :
    A.valuation (algebraMap L Ω (y : L) - algebraMap E' Ω (x : E')) < 1 := by
  have h1 := hTR L Ω g A v hv hgv hgv2 aL haL π (by rw [hvN]; exact hπ) t y hy
  have h2 := hTR E' Ω g A w' h' hgw hgw2 a' ha' π (by rw [hwN]; exact hπ) t' x hx
  rw [htt] at h1
  have e : algebraMap L Ω (y : L) - algebraMap E' Ω (x : E') =
      ((t' : G E' Ω) π / π - algebraMap E' Ω (x : E')) - ((t' : G E' Ω) π / π - algebraMap L Ω (y : L)) := by ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h2 h1)

theorem tr_base (hTR : TameRec) {E E' Ω : Type} [Field E] [NumberField E] [IsTotallyComplex E] [Field E'] [NumberField E']
    [IsTotallyComplex E'] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (n : ℕ) (hn : 0 < n) (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (hgv : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (hgv2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2)
    (hgw : ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal) (hgw2 : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2)
    (hvN : normV w = g) (hwN : normV w' = g ^ n)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (π : Ω) (hπ : π ^ (g ^ n - 1) = (g : Ω))
    (s : Ine (F := E) A) (t' : Ine (F := E') A) (htt : ∀ z : Ω, (s : G E Ω) z = (t' : G E' Ω) z)
    (y : 𝓞 E) (hy : Valued.v ((a (ineIncl h s) : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (y : E)) < 1)
    (x : 𝓞 E') (hx : Valued.v ((a' (ineIncl h' t') : w'.adicCompletion E') -
      algebraMap E' (w'.adicCompletion E') (x : E')) < 1) :
    A.valuation (algebraMap E Ω (y : E) - algebraMap E' Ω (x : E') ^ ((g ^ n - 1) / (g - 1))) < 1 := by
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hdvd : (g - 1) ∣ (g ^ n - 1) := by
    simpa using Nat.sub_dvd_pow_sub_pow g 1 n
  set e := (g ^ n - 1) / (g - 1) with he
  have hπE : (π ^ e) ^ (normV w - 1) = (g : Ω) := by
    rw [hvN, ← pow_mul, he, Nat.div_mul_cancel hdvd, hπ]
  have h1 := hTR E Ω g A w h hgv hgv2 a ha (π ^ e) hπE s y hy
  have h2 := hTR E' Ω g A w' h' hgw hgw2 a' ha' π (by rw [hwN]; exact hπ) t' x hx
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by have := Nat.one_lt_pow hn.ne' hg1; omega)] at hπ
    exact (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero) hπ.symm
  have e1 : (s : G E Ω) (π ^ e) / π ^ e = ((t' : G E' Ω) π / π) ^ e := by
    rw [map_pow, htt, div_pow]
  rw [e1] at h1
  have hr1 : A.valuation ((t' : G E' Ω) π / π) ≤ 1 := by
    have hd : ((t' : G E' Ω) : G E' Ω) ∈ Dec (F := E') A := Ine_le_Dec A t'.2
    exact (val_ratio hd hπ0).le
  have hx1 : A.valuation (algebraMap E' Ω (x : E')) ≤ 1 := by
    rw [A.valuation_le_one_iff]
    have h3 : IsIntegral ℤ (algebraMap E' Ω (x : E')) := x.2.map (algebraMap E' Ω).toIntAlgHom
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h3.tower_top (A := A))
    exact hz ▸ z.2
  have h3 := cong_pow hr1 hx1 h2 e
  have e2 : algebraMap E Ω (y : E) - algebraMap E' Ω (x : E') ^ e =
      (((t' : G E' Ω) π / π) ^ e - algebraMap E' Ω (x : E') ^ e) - (((t' : G E' Ω) π / π) ^ e - algebraMap E Ω (y : E)) := by
    ring
  rw [e2]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h3 h1)

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.LTw
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands
  GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem lTw : LTw := by
  intro E _ _ w g _ i hi n K _ _ hK hn χ₀
  obtain ⟨χ, hχs, hχl⟩ := DzTw.exists_liftsChar i hi χ₀
  have hdet : ∀ k : GL (Fin n) ℤ_[g],
      χ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k))) =
        χ₀ (Matrix.GeneralLinearGroup.det (red g n k)) := by
    intro k
    rw [hχl.1 (Matrix.GeneralLinearGroup.det k) _ ?_]
    · congr 1
      refine Units.ext ?_
      show PadicInt.toZMod ((k : Matrix (Fin n) (Fin n) ℤ_[g]).det) =
        ((red g n k : Matrix (Fin n) (Fin n) (ZMod g))).det
      exact RingHom.map_det _ _
    · show (i.toRingHom.mapMatrix ((algebraMap ℤ_[g] ℚ_[g]).mapMatrix (k : Matrix (Fin n) (Fin n) ℤ_[g]))).det =
        i.toRingHom ((algebraMap ℤ_[g] ℚ_[g]) (k : Matrix (Fin n) (Fin n) ℤ_[g]).det)
      rw [RingHom.map_det, RingHom.map_det]
  refine ⟨χ, hχs, hχl, fun θ hθ τ hτ hθτ σ hσ => ?_⟩
  refine ⟨DzTw.twFD τ χ₀, irrTwist σ (detChar (Fin n) χ) (hχs.detChar (n := Fin n)),
    DzTw.isRegularChar_mul K χ₀ hθ, DzTw.isCusp_twFD τ χ₀ hτ, DzTw.char_twFD K hK hn χ₀ θ τ hθτ, ?_,
    Sigma.ext rfl (heq_of_eq (clTwist_cl σ _ _).symm)⟩
  obtain ⟨φ, hφ0, hφ⟩ := hσ
  refine ⟨φ, hφ0, fun k v => ?_⟩
  show φ ((((detChar (Fin n) χ₀ (red g n k)) : ℂˣ) : ℂ) • τ.ρ (red g n k) v) =
    (((detChar (Fin n) χ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k))) : ℂˣ) : ℂ) •
      σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k)) (φ v)
  rw [map_smul, hφ k v, detChar_apply, detChar_apply, hdet k, MonoidHom.comp_apply]

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.StepUp
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)
  {ψ₀ : AddChar (ZMod g) Circle} {ψ : AddChar (w.adicCompletion E) Circle}

include hi in
theorem step_up (hψ : ∀ x : ℤ_[g], ψ (i (x : ℚ_[g])) = ψ₀ (PadicInt.toZMod x)) (h0 : ψ₀ ≠ 1) {n : ℕ}
    (τ : FDRep ℂ (Gn g n)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (φ : τ →ₗ[ℂ] V)
    (hφ : ∀ (κ : GL (Fin n) ℤ_[g]) (x : τ),
      φ (τ.ρ (red g n κ) x) = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n κ)) (φ x))
    (L : Module.Dual ℂ V) (hL : IsFunctional ψ π L) (x : τ) (d : Fin n → ℤ) (a b : Fin n)
    (hb : b.val = a.val + 1) (hd : d a < d b) :
    L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) = 0 := by
  obtain ⟨x0, hx0⟩ := exists_psi_ne_one i hψ h0
  have hab : a ≠ b := fun h => by rw [h] at hb; omega
  have hlt : a < b := by rw [Fin.lt_def]; omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d b = d a + ((k + 1 : ℕ) : ℤ) := ⟨(d b - d a - 1).toNat, by omega⟩
  have hyv : valuation (w.adicCompletion E) (i (x0 : ℚ_[g])) ≤ 1 := (DzIso.valuation_le_iff i hi _).2 x0.2
  set c : w.adicCompletion E := (GLnLocal.uniformizer (w.adicCompletion E) : w.adicCompletion E) ^ (k + 1) *
    i (x0 : ℚ_[g]) with hc_def
  have hcv : valuation (w.adicCompletion E) c < 1 := val_uniformizer_pow_lt k hyv
  have hmem : tv a b hab c ∈ KOne (w.adicCompletion E) (Fin n) := by
    rw [GlobalTheory.StepData.mem_KOne]
    intro p q
    show valuation (w.adicCompletion E) (((tv a b hab c : Matrix (Fin n) (Fin n) (w.adicCompletion E)) - 1) p q) < 1
    rw [Matrix.sub_apply, tv_apply, add_sub_cancel_left]
    split_ifs
    · exact hcv
    · simp
  have hconj : Iwasawa.torusPow (w.adicCompletion E) n d * tv a b hab c *
      (Iwasawa.torusPow (w.adicCompletion E) n d)⁻¹ = tv a b hab (i (x0 : ℚ_[g])) := by
    rw [Iwasawa.torusPow, conj_tv, hc_def, torus_entry d a b k hk]
  have key := hL _ (tv_mem_unipB a b hlt (i (x0 : ℚ_[g]))) (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x))
  rw [superDiag_tv a b hb] at key
  rw [← hconj, rep_conj, fix_of_mem_KOne i hi τ π φ hφ hmem] at key
  have hne : (ψ (i (x0 : ℚ_[g])) : ℂ) ≠ 1 := fun h => hx0 (Circle.ext (by simpa using h))
  have h2 : (1 - (ψ (i (x0 : ℚ_[g])) : ℂ)) * L (π (Iwasawa.torusPow (w.adicCompletion E) n d) (φ x)) = 0 := by
    rw [sub_mul, one_mul]; exact sub_eq_zero.2 key
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hne.symm)

end DiscreteGroups.sglob.DzRed
end
end

