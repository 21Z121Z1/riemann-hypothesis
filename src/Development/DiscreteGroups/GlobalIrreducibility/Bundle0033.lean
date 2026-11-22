import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0031
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0009
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0011
import Development.DiscreteGroups.GlobalIrreducibility.OrbitOfAgree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0014
import Development.DiscreteGroups.GlobalIrreducibility.DzMatchCut
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0029
import Development.DiscreteGroups.GlobalIrreducibility.EigTranslate
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0013
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0012
import Development.DiscreteGroups.GlobalIrreducibility.ExistsIneOfVEqOne
import Development.DiscreteGroups.GlobalIrreducibility.DzIneEq
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0030
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0008
import Development.DiscreteGroups.GlobalIrreducibility.Bundle0001

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzGalW
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual

set_option linter.all false

noncomputable section

namespace DiscreteGroups.sglob.DzType

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (g : ℕ) [hg : Fact g.Prime]

theorem g_not_mem_sq (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) :
    ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro hg2
  have hvF : ∀ y : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.intValuation y := fun y => by
    have e : Valued.v (algebraMap E (w.adicCompletion E) (y : E)) = w.valuation E (y : E) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E) w (y : E)
    rw [e]; exact HeightOneSpectrum.valuation_of_algebraMap w y
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  have hg2' : w.intValuation ((g : ℕ) : 𝓞 E) ≤ WithZero.exp (-(2 : ℕ) : ℤ) :=
    (w.intValuation_le_pow_iff_mem _ 2).mpr hg2
  set x := i.symm (algebraMap E (w.adicCompletion E) (π : E)) with hx
  have hxπ : i x = algebraMap E (w.adicCompletion E) (π : E) := by rw [hx, RingEquiv.apply_symm_apply]
  have hπ1 : Valued.v (algebraMap E (w.adicCompletion E) (π : E)) < 1 := by
    rw [hvF, hπ]
    have h0 : WithZero.exp (-1 : ℤ) < WithZero.exp 0 := WithZero.exp_lt_exp.mpr (by norm_num)
    simpa using h0
  have hxn : ‖x‖ < 1 := by
    rw [← DiscreteGroups.sglob.DzIso.norm_lt_iff i hi, hxπ, Valued.toNormedField.norm_lt_one_iff]
    exact hπ1
  have hxg : ‖x / (g : ℚ_[g])‖ ≤ 1 := by
    have h1 : ‖x‖ ≤ (g : ℝ) ^ (-1 : ℤ) := by
      rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]; simpa using hxn
    rw [norm_div, Padic.norm_p, div_le_one (inv_pos.mpr (by exact_mod_cast hg.out.pos))]
    simpa [zpow_neg, zpow_one] using h1
  have h2 := DiscreteGroups.sglob.DzIso.norm_le_of_le i hi hxg
  rw [Valued.toNormedField.norm_le_one_iff] at h2
  have e : algebraMap E (w.adicCompletion E) (π : E) = ((g : ℕ) : w.adicCompletion E) * i (x / (g : ℚ_[g])) := by
    rw [← hxπ, ← map_natCast i g, ← map_mul, mul_div_cancel₀]
    exact_mod_cast hg.out.ne_zero
  have h3 : Valued.v (algebraMap E (w.adicCompletion E) (π : E)) ≤ WithZero.exp (-(2 : ℕ) : ℤ) := by
    rw [e, map_mul]
    have hgv : Valued.v ((g : ℕ) : w.adicCompletion E) = w.intValuation ((g : ℕ) : 𝓞 E) := by
      rw [← hvF]; simp
    rw [hgv]
    calc w.intValuation ((g : ℕ) : 𝓞 E) * Valued.v (i (x / (g : ℚ_[g])))
        ≤ w.intValuation ((g : ℕ) : 𝓞 E) * 1 := mul_le_mul_right h2 _
      _ ≤ _ := by rw [mul_one]; exact hg2'
  rw [hvF, hπ, WithZero.exp_le_exp] at h3
  norm_num at h3

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzKondo
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.GLq GlobalTheory.Published

noncomputable section

namespace DiscreteGroups.sglob.DzType

open Kon

set_option linter.style.haveILetI false

theorem lKondo : LKondo := by
  intro g _ n hn2 hbig K _ _ hK ψ₀ hψ₀
  classical
  have hgp : g.Prime := Fact.out
  have hn0 : 0 < n := by omega
  have hKpos : 0 < Nat.card K := by rw [hK]; exact pow_pos hgp.pos _
  have : Finite K := Nat.finite_of_card_ne_zero hKpos.ne'
  let _ : Fintype K := Fintype.ofFinite K
  have : FiniteDimensional (ZMod g) K := Module.Finite.of_finite
  have hcard : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hK]
  have hfr : Module.finrank (ZMod g) K = n := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod g) (V := K)
    rw [ZMod.card, hcard] at h1
    exact (Nat.pow_right_injective hgp.two_le h1).symm
  obtain ⟨θ₀, hθ₀, ι, kOf, hlink, τE, hτe, hτ1, hτ2, hex⟩ := named_family g n hn0 K hfr
  have hN : 0 < g ^ n - 1 := by have := Nat.one_lt_pow hn0.ne' hgp.one_lt; omega
  have hD0 : (∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have hi1 := (Finset.mem_Ico.1 hi).1
    have h1 : ((g ^ i : ℕ) : ℂ) ≠ 1 := by
      rw [Ne, Nat.cast_eq_one]; exact (Nat.one_lt_pow (by omega) hgp.one_lt).ne'
    rw [sub_ne_zero]; exact_mod_cast h1
  have hGL : glCard (ZMod g) n ≠ 0 := by unfold glCard; exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hNc : ((g ^ n - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hε : ((-1 : ℂ) ^ (n - 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  refine ⟨(-1) ^ (n - 1) * glCard (ZMod g) n / (((g ^ n - 1 : ℕ) : ℂ) * ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)),
    div_ne_zero (mul_ne_zero hε hGL) (mul_ne_zero hNc hD0), ?_⟩
  intro θ hθ τ hτ hf
  have hname : ∀ x, τ.character x = τE θ x := by
    obtain ⟨θ', hθ', heq⟩ := hex τ.character hτ
    obtain ⟨i, hi, hii⟩ := orbit_of_agree hn2 hbig hK θ θ' hθ (fun z hz => by
      obtain ⟨y, hy, hzy⟩ := hz
      have e1 := hf y hy z hzy
      have e2 := (hτ1 θ' hθ').2.2 y hy z hzy
      rw [heq] at e1
      show fo g n θ z = fo g n θ' z
      exact mul_left_cancel₀ hε (e1.symm.trans e2))
    have h3 : τE θ = τE θ' := (hτ2 θ θ' hθ hθ').2 ⟨i, hi, hii⟩
    intro x; rw [heq, ← h3]
  have hsimple := simple_of_isIrr τ hτ.2.1
  let fψ : Gn g n → ℂ := fun y => ((ψ₀ (Matrix.trace (y : Mt g n)) : Circle) : ℂ)
  have hfcl : ∀ x y : Gn g n, fψ (y * x * y⁻¹) = fψ x := by
    intro x y
    simp only [fψ, Units.val_mul]
    rw [Matrix.trace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨c, hc1, hc2⟩ := central_scalar τ fψ hfcl
  have hdim : (Module.finrank ℂ τ : ℂ) = ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1) := by
    rw [← FDRep.char_one, hname, (hτ1 θ hθ).2.1]
  have hip := ipGL_psi_trace (F := ZMod g) (Fin n → ZMod g) (by rw [Module.finrank_fin_fun]; exact hn0) θ₀ hθ₀
    (kOf θ) (fun a => ((ψ₀ a : Circle) : ℂ))
  rw [Module.finrank_fin_fun] at hip
  rw [(GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties (ZMod g) n (fun _ => 0)).2.2.1, finsum_eq_sum_of_fintype] at hip
  have e : ∀ y : Gn g n, fψ y * τ.character y⁻¹ =
      star (psi (rootSum θ₀ (kOf θ)) (Fin n → ZMod g) (Matrix.toLin' (y : Mt g n)) *
        star ((ψ₀ (-(LinearMap.charpoly (Matrix.toLin' (y : Mt g n))).nextCoeff) : Circle) : ℂ)) * (-1) ^ (n - 1) := by
    intro y
    rw [GlobalTheory.BadShare.ZCalc.character_inv, hname, hτe, ← trace_eq_nextCoeff hn0]
    simp only [fψ, starRingEnd_apply, star_mul', star_pow, star_neg, star_one, star_star]
    ring
  have hsum : ∑ y : Gn g n, fψ y * τ.character y⁻¹ =
      (-1) ^ (n - 1) * glCard (ZMod g) n * aC n θ₀ (hT n fun a => ((ψ₀ a : Circle) : ℂ)) (kOf θ) := by
    rw [Finset.sum_congr rfl (fun y _ => e y), ← Finset.sum_mul, ← star_sum]
    rw [show (∑ y : Gn g n, psi (rootSum θ₀ (kOf θ)) (Fin n → ZMod g) (Matrix.toLin' (y : Mt g n)) *
        star ((ψ₀ (-(LinearMap.charpoly (Matrix.toLin' (y : Mt g n))).nextCoeff) : Circle) : ℂ)) =
        glCard (ZMod g) n * star (aC n θ₀ (hT n fun a => ((ψ₀ a : Circle) : ℂ)) (kOf θ)) from hip]
    rw [star_mul', star_star, glCard, star_natCast]
    ring
  have hgs := aC_eq_gs hn0 hK θ₀ ι θ (kOf θ) (hlink θ) ψ₀
  rw [hdim, hsum, hgs] at hc2
  have hcval : c = (-1) ^ (n - 1) * glCard (ZMod g) n /
      (((g ^ n - 1 : ℕ) : ℂ) * ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)) * gs ψ₀ θ⁻¹ := by
    unfold gs
    have h4 : c = (c * ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1)) / ∏ i ∈ Finset.Ico 1 n, ((g : ℂ) ^ i - 1) := by
      field_simp
    rw [h4, hc2]
    field_simp
  intro v
  rw [finsum_eq_sum_of_fintype]
  exact (hc1 v).trans (by rw [hcval])

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzLTame
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module

set_option linter.all false

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_eigenChar {H W V : Type*} [Group H] [Group W] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ W V) (f : H →* W) {u : V} (hu : u ≠ 0) (hex : ∀ s, ∃ e : ℂ, ρ (f s) u = e • u) :
    ∃ χ : H →* ℂˣ, ∀ s, ρ (f s) u = ((χ s : ℂˣ) : ℂ) • u := by
  choose e he using hex
  have hne : ∀ s, e s ≠ 0 := fun s h0 => DzCliff.rho_ne_zero ρ (f s) hu (by rw [he s, h0, zero_smul])
  refine ⟨{ toFun := fun s => Units.mk0 (e s) (hne s), map_one' := ?_, map_mul' := ?_ }, fun s => he s⟩
  · ext
    simp only [Units.val_mk0, Units.val_one]
    exact DzCliff.eig_unique hu (he 1) (by rw [map_one, map_one, Module.End.one_apply, one_smul])
  · intro s t
    ext
    simp only [Units.val_mk0, Units.val_mul]
    exact DzCliff.eig_unique hu (he (s * t))
      (by rw [map_mul, map_mul, Module.End.mul_apply, he t, map_smul, he s, smul_smul, mul_comm])

theorem lTame : LTame := by
  intro E E' Ω _ _ _ _ _ _ _ _ _ _ _ g _ A w h w' h' i hi n hn hg hN a' ha' K _ _ red hr hk y hirr htame hdim
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hq' : normV w' = normV w ^ n := by rw [hq, hN]
  obtain ⟨m, a, hya, hirr_a⟩ := hirr
  obtain ⟨m2, a2, hya2, htame2⟩ := htame
  have hiso : a2.Iso a := WD.mk_eq_mk.mp (hya2.trans hya.symm)
  have htame_a : ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → a.ρ σ = 1 :=
    fun σ hσ => hiso.ρ_eq_one (htame2 σ hσ)
  have hdim_a : finrank ℂ (Fin m → ℂ) = n := by rw [← hdim, ← hya, WD.lpDim_mk]
  let I : Subgroup (Weil h) := (Ine (F := E) A).comap (Weil h).subtype
  haveI hInorm : I.Normal := ⟨fun t ht g0 => by
    show ((g0 * t * g0⁻¹ : Weil h) : G E Ω) ∈ Ine (F := E) A
    exact conj_mem_Ine (Weil_le_Dec h g0.2) ht⟩
  have hgen : ∀ σ : Weil h, ∃ k : ℤ, ∃ t ∈ I, σ = frob h ^ k * t := fun σ => by
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) σ
    exact ⟨deg σ, ineIncl h τ, τ.2, hτ⟩
  have hcomm : ∀ s ∈ I, ∀ t ∈ I, a.ρ s * a.ρ t = a.ρ t * a.ρ s := by
    intro s hs t ht
    let s' : Ine (F := E) A := ⟨s, hs⟩
    let t' : Ine (F := E) A := ⟨t, ht⟩
    have h1 : a.ρ (ineIncl h (s' * t' * s'⁻¹ * t'⁻¹)) = 1 := htame_a _ (isWild_commutator s' t')
    have h2 : ineIncl h (s' * t' * s'⁻¹ * t'⁻¹) = s * t * s⁻¹ * t⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : s * t = (s * t * s⁻¹ * t⁻¹) * (t * s) := by group
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  have hfrob : ∀ t ∈ I, a.ρ (frob h * t * (frob h)⁻¹) = a.ρ t ^ normV w := by
    intro t ht
    let t' : Ine (F := E) A := ⟨t, ht⟩
    let c' : Ine (F := E) A :=
      ⟨(frob h : G E Ω) * t' * (frob h : G E Ω)⁻¹, conj_mem_Ine (isFrob_frob (h := h)).1 t'.2⟩
    have h1 : a.ρ (ineIncl h (c' * (t' ^ normV w)⁻¹)) = 1 :=
      htame_a _ (isWild_frob (isFrob_frob (h := h)) t')
    have h2 : ineIncl h (c' * (t' ^ normV w)⁻¹) = frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹ := Subtype.ext rfl
    rw [h2] at h1
    have e : frob h * t * (frob h)⁻¹ = (frob h * t * (frob h)⁻¹ * (t ^ normV w)⁻¹) * t ^ normV w := by group
    rw [e, map_mul, h1, one_mul, map_pow]
  obtain ⟨η, u, c, hu, huI, hφn, hchar, hper, hmin⟩ :=
    DzCliff.clifford a.ρ hirr_a I (frob h) (normV w) n hdim_a hn hgen hcomm hfrob
  have hc0 : c ≠ 0 := fun h0 => DzCliff.rho_ne_zero a.ρ (frob h ^ n) hu (by rw [hφn, h0, zero_smul])
  have hcinv : a.ρ (frob h ^ n)⁻¹ u = c⁻¹ • u := by
    have h1 := DzCliff.rho_inv_apply a.ρ (frob h ^ n) u
    rw [hφn, map_smul] at h1
    calc a.ρ (frob h ^ n)⁻¹ u = c⁻¹ • (c • a.ρ (frob h ^ n)⁻¹ u) := by
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      _ = c⁻¹ • u := by rw [h1]
  have hz : ∀ k : ℤ, a.ρ ((frob h ^ n) ^ k) u = c ^ k • u := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, map_mul, Module.End.mul_apply, hφn, map_smul, ih, smul_smul, zpow_add_one₀ hc0, mul_comm]
    | pred k ih =>
      rw [zpow_sub_one, map_mul, Module.End.mul_apply, hcinv, map_smul, ih, smul_smul, zpow_sub_one₀ hc0,
        mul_comm]
  have hex : ∀ σ : Weil h', ∃ e : ℂ, a.ρ (resW h h' hq' σ) u = e • u := by
    intro σ
    obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) (resW h h' hq' σ)
    rw [hτ, deg_resW, map_mul, Module.End.mul_apply, huI (ineIncl h τ) τ.2, map_smul,
      show frob h ^ ((n : ℤ) * deg σ) = (frob h ^ n) ^ deg σ by rw [zpow_mul, zpow_natCast], hz, smul_smul]
    exact ⟨_, rfl⟩
  obtain ⟨η', hη'⟩ := exists_eigenChar a.ρ (resW h h' hq') hu hex
  have hval : ∀ t : Ine (F := E') A, ((η' (ineIncl h' t) : ℂˣ) : ℂ) = η (ineIncl h (resI t)) := fun t =>
    DzCliff.eig_unique hu (hη' _) (by rw [resW_ineIncl]; exact huI (ineIncl h (resI t)) (resI t).2)
  have hsm : IsSmooth η' := by
    refine IsSmooth.of_open (U := resI ⁻¹' {s : Ine (F := E) A | a.ρ (ineIncl h s) = 1})
      (IsOpen.preimage continuous_resI a.smooth) (by simp) ?_
    intro t ht
    have h1 : a.ρ (resW h h' hq' (ineIncl h' t)) u = (1 : ℂ) • u := by
      rw [resW_ineIncl, ht, Module.End.one_apply, one_smul]
    exact Units.ext (DzCliff.eig_unique hu (hη' _) h1)
  have hηN : ∀ t : Ine (F := E') A, η' (ineIncl h' t) ^ (g ^ n - 1) = 1 := by
    intro t
    have hp := hper (ineIncl h (resI t)) (resI t).2
    rw [hq] at hp
    have hs0 : η (ineIncl h (resI t)) ≠ 0 := by rw [← hval]; exact Units.ne_zero _
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hval, Units.val_one]
    have h1 : η (ineIncl h (resI t)) ^ (g ^ n - 1) * η (ineIncl h (resI t)) = 1 * η (ineIncl h (resI t)) := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos), hp, one_mul]
    exact mul_right_cancel₀ hs0 h1
  obtain ⟨ξ, hξ⟩ := exists_resChar g A w' h' n hn hN a' ha' K red hr hk η' hsm hηN
  refine ⟨ξ, ?_, ?_⟩
  · intro i0 j0 hi0 hj0 hij
    by_contra hne
    wlog hlt : i0 < j0 generalizing i0 j0
    · exact this j0 i0 hj0 hi0 hij.symm (Ne.symm hne) (by omega)
    obtain ⟨s, hsI, hs⟩ := hmin (j0 - i0) (by omega) (by omega)
    obtain ⟨t0, ht0, hres⟩ := ine_lift g A w h w' h' n hn hg hN (s : G E Ω) hsI
    let t : Ine (F := E') A := ⟨t0, ht0⟩
    have hts : ineIncl h (resI t) = s := Subtype.ext hres
    have hunit : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1 := by
      have h1 := ha'.ord_eq (ineIncl h' t)
      rw [GlobalTheory.SmGL.SphCompletion.ord_completion, deg_ineIncl] at h1
      have hv0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0 := by
        rw [Ne, Valuation.zero_iff]; exact Units.ne_zero _
      have hl : WithZero.log (Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E')) = 0 := by
        simpa using h1
      rw [← WithZero.exp_log hv0, hl, WithZero.exp_zero]
    obtain ⟨x, hx⟩ := exists_int_approx_compl w' _ hunit.le
    have hxw : red x ≠ 0 := by
      intro h0
      have hxm : x ∈ w'.asIdeal := by rw [← hk, RingHom.mem_ker]; exact h0
      have hvx : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) < 1 := by
        have e : Valued.v (algebraMap E' (w'.adicCompletion E') (x : E')) = w'.valuation E' (x : E') :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 E') w' (x : E')
        rw [e]
        exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E') w' x).mpr hxm
      have hlt1 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') < 1 := by
        have e : ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') =
            (((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') -
              algebraMap E' (w'.adicCompletion E') (x : E')) + algebraMap E' (w'.adicCompletion E') (x : E') := by ring
        rw [e]
        exact Valuation.map_add_lt _ hx hvx
      rw [hunit] at hlt1
      exact lt_irrefl _ hlt1
    have hξz := hξ t x (Units.mk0 (red x) hxw) rfl hx
    have h1 : (ξ (Units.mk0 (red x) hxw)) ^ g ^ i0 = (ξ (Units.mk0 (red x) hxw)) ^ g ^ j0 := by
      have := congrArg (fun χ : Kˣ →* ℂˣ => χ (Units.mk0 (red x) hxw)) hij
      simpa using this
    rw [hξz] at h1
    have h2 : ((η' (ineIncl h' t) : ℂˣ) : ℂ) ^ g ^ i0 = ((η' (ineIncl h' t) : ℂˣ) : ℂ) ^ g ^ j0 := by
      have := congrArg Units.val h1
      simpa only [Units.val_pow_eq_pow_val] using this
    rw [hval, hts] at h2
    have hp := hper s hsI
    rw [hq] at hp hs
    apply hs
    calc η s ^ g ^ (j0 - i0) = (η s ^ g ^ n) ^ g ^ (j0 - i0) := by rw [hp]
      _ = η s ^ (g ^ n * g ^ (j0 - i0)) := by rw [← pow_mul]
      _ = η s ^ (g ^ j0 * g ^ (n - i0)) := by
          rw [← pow_add, ← pow_add]; congr 2; omega
      _ = (η s ^ g ^ j0) ^ g ^ (n - i0) := by rw [pow_mul]
      _ = (η s ^ g ^ i0) ^ g ^ (n - i0) := by rw [h2]
      _ = η s ^ (g ^ i0 * g ^ (n - i0)) := by rw [← pow_mul]
      _ = η s ^ g ^ n := by rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hi0)]
      _ = η s := hp
  · intro t x z hxz hv
    have hξz := hξ t x z hxz hv
    rw [WD.inePol_of_mem_Ine y (res_mem_Ine t.2), ← hya, WD.charPol_mk]
    rw [show ineIncl h ⟨AlgEquiv.restrictScalars E (t : G E' Ω), res_mem_Ine t.2⟩ = ineIncl h (resI t) from rfl,
      hchar (ineIncl h (resI t)) (resI t).2, hq]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow ξ, Units.val_pow_eq_pow_val, hξz, hval]

end DiscreteGroups.sglob.DzType

end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzPinFinal
section
noncomputable section

set_option linter.style.haveILetI false

namespace DiscreteGroups.sglob.DzType

open NumberField IsDedekindDomain

theorem lPin_of_dig (hD : Dig) : LPin := by
  intro g _ n hn2 hbig K _ _ hcard ψ₀ hψ₀ θ ξ hθ hξ hH
  classical
  have hgp : g.Prime := Fact.out
  have hg2 := hgp.two_le
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  letI : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = g ^ n := by rw [← Nat.card_eq_fintype_card, hcard]
  have hg2n : g ^ 2 ≤ g ^ n := Nat.pow_le_pow_right (by omega) hn2
  have hg4 : 4 ≤ g ^ 2 := by nlinarith
  set N := g ^ n - 1 with hNdef
  have hN1 : N + 1 = g ^ n := by omega
  have hN0 : 0 < N := by omega
  have hN1lt : 1 < N := by omega
  obtain ⟨Q, ω, Ω, hΩi, hdat⟩ := DzPin.exists_setup g n (by omega) K hK ψ₀ hψ₀
  obtain ⟨k, hk⟩ := DzPin.exists_eq_pow_of_injective Ω θ hΩi
  obtain ⟨k', hk'⟩ := DzPin.exists_eq_pow_of_injective Ω ξ hΩi
  have hΩN : Ω ^ N = 1 := by
    refine MonoidHom.ext fun z => ?_
    have hz : z ^ N = 1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one, hNdef, ← hK]
      exact FiniteField.pow_card_sub_one_eq_one _ z.ne_zero)
    rw [MonoidHom.pow_apply, ← map_pow, hz, map_one, MonoidHom.one_apply]
  have hreg : ∀ {η : Kˣ →* ℂˣ} {m : ℕ}, η = Ω ^ m → GlobalTheory.Published.IsRegularChar g n η →
      ∀ i j, i < n → j < n → m * g ^ i ≡ m * g ^ j [MOD g ^ n - 1] → i = j := by
    intro η m hηm hr i j hi hj hm
    refine hr i j hi hj ?_
    rw [hηm, ← pow_mul, ← pow_mul]
    exact DzPin.pow_eq_pow_of_modEq hΩN hm
  have hmain : ∀ u b : ℕ, u.Coprime (g ^ n - 1) →
      (Nat.digits g ((u * k + b * ((g ^ n - 1) / (g - 1))) % (g ^ n - 1))).sum +
          (Nat.digits g (u * k' % (g ^ n - 1))).sum =
        (Nat.digits g ((u * k' + b * ((g ^ n - 1) / (g - 1))) % (g ^ n - 1))).sum +
          (Nat.digits g (u * k % (g ^ n - 1))).sum := by
    intro u b hu
    haveI : NeZero N := ⟨by omega⟩
    set t0 := ((ZMod.unitOfCoprime u hu)⁻¹ : (ZMod N)ˣ).val.val with ht0def
    have h0 : u * t0 ≡ 1 [MOD N] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      push_cast
      rw [ht0def, ZMod.natCast_zmod_val, ← ZMod.coe_unitOfCoprime u hu, Units.mul_inv]
    set t := t0 + N * (t0 + 1) with htdef
    have htu : t * u ≡ 1 [MOD N] := by
      have e : t * u = u * t0 + N * ((t0 + 1) * u) := by rw [htdef]; ring
      unfold Nat.ModEq
      rw [e, Nat.add_mul_mod_self_left]
      exact h0
    have htN : t.Coprime N := Nat.coprime_of_mul_modEq_one u htu
    have htg : t.Coprime g := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hgp]
      intro hdt
      have h1 : g ∣ t + 1 := by
        have e : t + 1 = g ^ n * (t0 + 1) := by rw [← hN1, htdef]; ring
        rw [e]
        exact Dvd.dvd.mul_right (dvd_pow_self g (by omega)) _
      have h2 : g ∣ 1 := (Nat.dvd_add_right hdt).mp h1
      exact hgp.one_lt.ne' (Nat.dvd_one.mp h2)
    obtain ⟨Φ, D, hΦi, hDω, hΦζ, hΦω⟩ := hdat t (Nat.Coprime.mul_right htg htN)
    have hG : ∀ (η : Kˣ →* ℂˣ) (a : ℕ), η = Ω ^ (t * a) → gs ψ₀ η⁻¹ = Φ (D.g a) := by
      intro η a hη
      exact DzPin.gs_eq ψ₀ Φ D.ω D.ζ D.prim.pow_eq_one hΦζ η a (fun z => by
        rw [hη, hDω, hΦω, MonoidHom.pow_apply, Units.val_pow_eq_pow_val, pow_mul])
    set e := (g ^ n - 1) / (g - 1) with hedef
    let χ₀ : (ZMod g)ˣ →* ℂˣ := (Ω.comp (Units.map (algebraMap (ZMod g) K).toMonoidHom)) ^ (t * b)
    have hnm : nmChar K χ₀ = Ω ^ (e * (t * b)) := DzPin.nm_eq hK Ω (t * b)
    obtain ⟨r, hr, hrr⟩ := hH χ₀
    have h1 : θ * nmChar K χ₀ = Ω ^ (t * ((u * k + b * e) % N)) := by
      rw [hnm, hk, ← pow_add]
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist htu)).symm
    have h2 : ξ = Ω ^ (t * (u * k' % N)) := by
      rw [hk']
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist0 htu)).symm
    have h3 : ξ * nmChar K χ₀ = Ω ^ (t * ((u * k' + b * e) % N)) := by
      rw [hnm, hk', ← pow_add]
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist htu)).symm
    have h4 : θ = Ω ^ (t * (u * k % N)) := by
      rw [hk]
      exact (DzPin.pow_eq_pow_of_modEq hΩN (DzPin.modEq_twist0 htu)).symm
    rw [hG _ _ h1, hG _ _ h2, hG _ _ h3, hG _ _ h4, ← map_mul, ← map_mul, ← map_pow,
      ← map_pow] at hrr
    exact DzPin.dsum_eq_of_pow_eq D (Nat.mod_lt _ hN0) (Nat.mod_lt _ hN0) (Nat.mod_lt _ hN0)
      (Nat.mod_lt _ hN0) hr (hΦi hrr)
  obtain ⟨i, hi⟩ := hD g n hgp hn2 hbig k k' (hreg hk hθ) (hreg hk' hξ) hmain
  refine ⟨i, fun z => ?_⟩
  rw [hk', hk, DzPin.pow_eq_pow_of_modEq hΩN hi, MonoidHom.pow_apply, MonoidHom.pow_apply, map_pow,
    ← pow_mul, mul_comm]

end DiscreteGroups.sglob.DzType
end
end

-- bundled from Development.DiscreteGroups.GlobalIrreducibility.DzRedMat
section
noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem corner_torusPow {m : ℕ} (d : Fin m → ℤ) :
    corner (Iwasawa.torusPow K m d) = Iwasawa.torusPow K (m + 1) (Fin.snoc d 0) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  · rw [corner_last_last]; simp [Iwasawa.torusPow]
  · rw [corner_last_cs]; simp [Iwasawa.torusPow, Matrix.diagonal_apply, (Fin.castSucc_lt_last _).ne']
  · rw [corner_cs_last]; simp [Iwasawa.torusPow, Matrix.diagonal_apply, (Fin.castSucc_lt_last _).ne]
  · rw [corner_cs_cs]; simp [Iwasawa.torusPow, Matrix.diagonal_apply]

theorem longElt_mul_invT_torusPow {n : ℕ} (D : Fin n → ℤ) :
    longElt n K * GlobalTheory.CuspRep.invT n K (Iwasawa.torusPow K n D) =
      Iwasawa.torusPow K n (fun j => -D j.rev) * longElt n K := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  rw [Units.val_mul, Units.val_mul, longElt_mul_apply, mul_longElt_apply, val_invT, ← Iwasawa.torusPow_neg]
  simp only [Matrix.transpose_apply, Iwasawa.torusPow, Iwasawa.coe_diagGL, Matrix.diagonal_apply, Pi.neg_apply]
  by_cases h : b = a.rev
  · subst h; simp
  · have h' : a ≠ b.rev := fun h' => h (by rw [h', Fin.rev_rev])
    simp [h, h']

theorem torusPow_const_comm {n : ℕ} (c : ℤ) (y : GL (Fin n) K) :
    Iwasawa.torusPow K n (fun _ => c) * y = y * Iwasawa.torusPow K n (fun _ => c) := by
  refine Units.ext (Matrix.ext fun a b => ?_)
  simp [Iwasawa.torusPow, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

theorem torusPow_zero' {n : ℕ} : Iwasawa.torusPow K n 0 = 1 := by
  show Iwasawa.diagGL K n (fun _ => _ ^ (0 : ℤ)) = 1
  simp only [zpow_zero]
  exact map_one _

theorem unipotent_le_unipB {n : ℕ} {u : GL (Fin n) K} (hu : u ∈ Iwasawa.unipotent K n) : u ∈ unipB K (Fin n) := by
  rw [Iwasawa.mem_unipotent] at hu
  exact (mem_unipB K).2 ⟨fun i j h => hu.1 h, hu.2⟩

end DiscreteGroups.sglob.DzRed
end
end

