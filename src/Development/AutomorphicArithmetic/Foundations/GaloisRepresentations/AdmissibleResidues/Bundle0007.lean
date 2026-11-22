import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0001
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.MonodromyFreeOfEigenvalueRatio
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0310
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.GenericUnitaryDual.GenericUnitaryDualGLHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLatticeComplement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.FrobeniusTraceCountBoundOfCmEigensystemCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0028
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CongNum

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.PurLocSW
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.GalN.V
open private ex_elt algPow_const flag_cont cyc_cont from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst

private theorem map_zpow_eq_intCast_mul_of_map_mul_eq_add {Γ R : Type} [Group Γ] [Ring R] (f : Γ → R) (hf : ∀ a b, f (a * b) = f a + f b)
    (g : Γ) (m : ℤ) : f (g ^ m) = (m : R) * f g := by
  let D : Γ →* Multiplicative R := MonoidHom.mk' (fun x => Multiplicative.ofAdd (f x)) (by
    intro a b
    rw [hf]
    rfl)
  have h := congrArg Multiplicative.toAdd (map_zpow D g m)
  simp only [toAdd_zpow] at h
  rw [zsmul_eq_mul] at h
  exact h

private theorem int_zero {Γ : Type} [Group Γ] (d : Γ → ℤ) (L : Γ → ℝ) (hd : ∀ a b, d (a * b) = d a + d b)
    (hL : ∀ a b, L (a * b) = L a + L b) (φ : Γ) (hφ : d φ = 1) {c : ℝ} (hc : 0 < c) (hw : ∀ g, d g = 1 → |L g| < c)
    (s : Γ) (hs : d s ≠ 0) (k : ℤ) (hk : L s = k * d s * c) : k = 0 := by
  have hD := map_zpow_eq_intCast_mul_of_map_mul_eq_add d hd
  have hLz := map_zpow_eq_intCast_mul_of_map_mul_eq_add L hL
  have key : ∀ m : ℤ, |(m : ℝ) * (d s : ℝ) * (k * c - L φ) + L φ| < c := by
    intro m
    have h1 : d (s ^ m * φ ^ (1 - m * d s)) = 1 := by
      rw [hd, hD, hD, hφ]
      push_cast
      ring
    have h2 := hw _ h1
    rw [hL, hLz, hLz, hk] at h2
    convert h2 using 2
    push_cast
    ring
  have hδ : k * c - L φ = 0 := by
    by_contra hne
    have hpos : 0 < |k * c - L φ| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * c / |k * c - L φ|)
    have h1 := key n
    have h0 := key 0
    simp only [Int.cast_zero, zero_mul, zero_add] at h0
    have hds : (1 : ℝ) ≤ |(d s : ℝ)| := by
      have : (1 : ℤ) ≤ |d s| := Int.one_le_abs hs
      exact_mod_cast this
    have h3 : |(n : ℝ) * (d s : ℝ) * (k * c - L φ)| < 2 * c := by
      have := abs_sub (((n : ℤ) : ℝ) * (d s : ℝ) * (k * c - L φ) + L φ) (L φ)
      simp only [add_sub_cancel_right, Int.cast_natCast] at this
      simp only [Int.cast_natCast] at h1
      linarith
    rw [abs_mul, abs_mul, Nat.abs_cast] at h3
    rw [div_lt_iff₀ hpos] at hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hds (mul_nonneg hn0 hpos.le)]
  have hLφ : L φ = k * c := by linarith
  have h := hw φ hφ
  rw [hLφ, abs_mul, abs_of_pos hc] at h
  have hk1 : |(k : ℝ)| < 1 := by
    by_contra hh
    push_neg at hh
    nlinarith
  have : |k| < 1 := by exact_mod_cast hk1
  exact Int.abs_lt_one_iff.mp this

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}

private theorem mono0_of_charPol_eq_prod_of_ne_normV_pow_mul {n : ℕ} (x : WD h) (μ : Fin n → Weil h →* ℂˣ) (hμ : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (μ i))
    (hx : ∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ)))
    (hne : ∀ i j, ∃ s, (μ i s : ℂ) ≠ ((normV w : ℕ) : ℂ) ^ deg s * μ j s) : x.mono0 := by
  obtain ⟨na, a, rfl⟩ := x.exists_rep
  rw [WD.monodromyZero_ofWeilDeligneRepClass_iff]
  let b := WDRep.ofChars h μ hμ
  have hc : ∀ σ, (a.ρ σ).charpoly = (b.ρ σ).charpoly := by
    intro σ
    rw [← WD.charPol_mk, hx, WDRep.ofChars_ρ, charpoly_diagEnd]
  obtain ⟨e, he⟩ := GlobalTheory.T.weilRep_equiv_of_charpoly_eq F Ω A w h na n a b hc
  have hes : ∀ σ z, e.symm (b.ρ σ z) = a.ρ σ (e.symm z) := by
    intro σ z
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let N' : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := e.toLinearMap ∘ₗ a.N ∘ₗ e.symm.toLinearMap
  have hN' : ∀ σ z, b.ρ σ (N' z) = ((normV w : ℕ) : ℂ) ^ deg σ • N' (b.ρ σ z) := by
    intro σ z
    simp only [N', LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he, WDRep.comm_apply, hes, LinearEquiv.map_smul]
  have hsingle : ∀ σ j, b.ρ σ (Pi.single j 1) = (μ j σ : ℂ) • Pi.single j 1 := by
    intro σ j
    funext i
    rw [WDRep.ofChars_ρ, diagEnd_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_apply, hij]
  have hM : ∀ i j, N' (Pi.single j 1) i = 0 := by
    intro i j
    obtain ⟨σ, hσ⟩ := hne i j
    have h1 := congrFun (hN' σ (Pi.single j 1)) i
    rw [hsingle, LinearMap.map_smul, WDRep.ofChars_ρ, diagEnd_apply, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul] at h1
    have h2 : ((μ i σ : ℂ) - ((normV w : ℕ) : ℂ) ^ deg σ * μ j σ) * N' (Pi.single j 1) i = 0 := by
      rw [sub_mul, h1]
      ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3) hσ
    · exact h3
  have hN0 : N' = 0 := by
    apply LinearMap.pi_ext'
    intro j
    apply LinearMap.ext_ring
    funext i
    simp only [LinearMap.comp_apply, LinearMap.coe_single, LinearMap.zero_comp, LinearMap.zero_apply, Pi.zero_apply]
    exact hM i j
  apply LinearMap.ext
  intro v
  have h4 := LinearMap.congr_fun hN0 (e v)
  simp only [N', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.zero_apply] at h4
  rw [LinearMap.zero_apply]
  exact (LinearEquiv.map_eq_zero_iff e).mp h4

private theorem ratio_lt {n : ℕ} (x : WD h) (μ : Fin n → Weil h →* ℂˣ) (hμ : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (μ i))
    (hx : ∀ s, x.charPol s = ∏ i, (X - C (μ i s : ℂ))) (ht : x.mono0 → RatioW x)
    (hor : (∀ i j, ∃ s, (μ i s : ℂ) ≠ ((normV w : ℕ) : ℂ) ^ deg s * μ j s) ∨ x.mono0) (i j : Fin n) (s : Weil h) (hs : deg s ≠ 0) (k : ℤ)
    (hk : ‖(μ i s : ℂ)‖ = ((normV w : ℕ) : ℝ) ^ (k * deg s) * ‖(μ j s : ℂ)‖) : k = 0 := by
  have hm : x.mono0 := by
    rcases hor with h1 | h1
    · exact mono0_of_charPol_eq_prod_of_ne_normV_pow_mul x μ hμ hx h1
    · exact h1
  have hR := ht hm
  have hq1 : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hq0 : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by linarith
  have hpos : ∀ l g, 0 < ‖(μ l g : ℂ)‖ := fun l g => norm_pos_iff.mpr (Units.ne_zero _)
  have hmem : ∀ g l, (μ l g : ℂ) ∈ x.eig g := by
    intro g l
    show (μ l g : ℂ) ∈ (x.charPol g).roots
    rw [hx]
    have hmon : (∏ k, (X - C (μ k g : ℂ))).Monic := monic_prod_of_monic _ _ (fun k _ => monic_X_sub_C _)
    rw [mem_roots hmon.ne_zero, IsRoot, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (by simp)
  refine int_zero (Γ := Weil h) deg (fun g => Real.log ‖(μ i g : ℂ)‖ - Real.log ‖(μ j g : ℂ)‖) deg_mul ?_ (frob h)
    deg_frob (Real.log_pos hq1) ?_ s hs k ?_
  · intro a b
    simp only [map_mul, Units.val_mul, norm_mul]
    rw [Real.log_mul (hpos i a).ne' (hpos i b).ne', Real.log_mul (hpos j a).ne' (hpos j b).ne']
    ring
  · intro g hg
    have h1 := hR g hg _ (hmem g i) _ (hmem g j)
    have h2 := hR g hg _ (hmem g j) _ (hmem g i)
    have l1 := Real.log_lt_log (hpos i g) h1
    have l2 := Real.log_lt_log (hpos j g) h2
    rw [Real.log_mul hq0.ne' (hpos j g).ne'] at l1
    rw [Real.log_mul hq0.ne' (hpos i g).ne'] at l2
    rw [abs_lt]
    constructor <;> linarith
  · beta_reduce
    rw [hk, Real.log_mul (zpow_pos hq0 _).ne' (hpos j s).ne', Real.log_zpow]
    push_cast
    ring

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RW
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne UpperTheory.V.Af

namespace UpperTheory.GalN.V

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def RW (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    ∀ s : G F Ω, IsFrob A (normV w) s → ∀ α β : Qbar l, (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot α →
      (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot β → ‖ι α‖ < ((normV w : ℕ) : ℝ) * ‖ι β‖

theorem RW.iso {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} (h : RW ι r)
    (e : ∀ s, (r' s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly) : RW ι r' :=
  fun w hw A hA s hs α β hα hβ => h w hw A hA s hs α β (e s ▸ hα) (e s ▸ hβ)

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SAdIso
section
open UpperTheory.GalN.V

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.Ga.AutomorphyInvariantUnderRepIso

section Rep

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}

private theorem act_conj (g : GL (Fin n) k) (hg : ∀ s, r' s = g * r s * g⁻¹) (s : Γ) (v : Fin n → k) :
    (r' s : Matrix (Fin n) (Fin n) k) *ᵥ ((g : Matrix (Fin n) (Fin n) k) *ᵥ v) =
      (g : Matrix (Fin n) (Fin n) k) *ᵥ ((r s : Matrix (Fin n) (Fin n) k) *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hg]
  congr 2
  group

private theorem ss_iso (h : RepIso r r') (hr : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Units.mul_inv g) (fun s => ?_) hr
  rw [hg s, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group

private theorem irr_iso (h : RepIso r r') (hr : IsIrr r) : IsIrr r' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨hr.1, fun _ _ _ => Submodule.mem_top, fun W _ hW => ?_⟩
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv
  have he : ∀ v, e v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := fun _ => rfl
  have hinv := hr.2.2 (W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) le_top (fun s v hv => by
    change e _ ∈ W
    have h1 : e v ∈ W := hv
    rw [he] at h1 ⊢
    rw [← act_conj g hg]
    exact hW s _ h1)
  have hW' : W = (W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))).map (e : (Fin n → k) →ₗ[k] (Fin n → k)) :=
    (Submodule.map_comap_eq_of_surjective e.surjective W).symm
  rcases hinv with h0 | h0
  · left
    rw [hW', h0, Submodule.map_bot]
  · right
    rw [hW', h0, Submodule.map_top, LinearEquiv.range]

private theorem tw_iso (χ : Γ →* kˣ) (h : RepIso r r') : RepIso (tw r χ) (tw r' χ) := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => Units.ext ?_⟩
  simp only [Units.val_mul, tw_val, hg s, Matrix.mul_smul, Matrix.smul_mul]

private theorem comp_iso {Γ' : Type} [Group Γ'] (φ : Γ' →* Γ) (h : RepIso r r') : RepIso (r.comp φ) (r'.comp φ) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, fun s => hg (φ s)⟩

end Rep

private theorem att_iso {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    (h : RepIso r r') (H : AttachedSys ι r sat) : AttachedSys ι r' sat :=
  ⟨ss_iso h H.1, H.2.mono fun _ ⟨B, hB, hB'⟩ => ⟨B, hB, hB'.of_iso h⟩⟩

end UpperTheory.V.Z.Sym.Ga.AutomorphyInvariantUnderRepIso
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WinNumN
section
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

namespace UpperTheory.GalN.V.Win.N

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V.CongNum

section

private theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    normV w = p := by
  have h : normV w = Ideal.absNorm w.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hN : Ideal.absNorm (Ideal.span {((p : ℕ) : 𝓞 ℚ)}) = p := by
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank]
    simp
  have hd : Ideal.absNorm w.asIdeal ∣ p :=
    hN ▸ Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hw)
  rw [h]
  refine ((Nat.dvd_prime hp).1 hd).resolve_left ?_
  rw [Ideal.absNorm_eq_one_iff]
  exact w.isPrime.ne_top

private theorem est {p e : ℕ} (hp : 5 ≤ p) (he : 2 ≤ e) {t z₁ z₂ z₃ : ℂ} (h1 : ‖z₁‖ = 1) (h2 : ‖z₂‖ = 1) (h3 : ‖z₃‖ = 1)
    (ht : ‖t‖ ≤ 3 * (Real.sqrt p * (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) + (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2)) :
    t - eis4 p e z₁ z₂ z₃ ≠ 0 ∧ ‖t - eis4 p e z₁ z₂ z₃‖ ≤ (p : ℝ) ^ (2 * (e + 1)) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  set x : ℝ := (p : ℝ) ^ ((((e : ℤ) + 1 : ℤ) : ℝ) / 2) with hx
  set y : ℝ := (p : ℝ) ^ e with hy
  have hx0 : 0 ≤ x := by positivity
  have hxx : x * x = p * y := by
    rw [hx, ← Real.rpow_add (by linarith), hy, ← pow_succ', ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hy2 : (p : ℝ) ^ 2 ≤ y := pow_le_pow_right₀ (by linarith) he
  have hy0 : 0 ≤ y := by positivity
  have hxy : 2 * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0, mul_nonneg (show (0:ℝ) ≤ p - 4 by linarith) (mul_nonneg (show (0:ℝ) ≤ p by linarith) hy0)]
  have hsx : Real.sqrt p * x ≤ y := by
    refine abs_le_of_sq_le_sq' ?_ hy0 |>.2
    rw [mul_pow, Real.sq_sqrt (by linarith), pow_two x, hxx]
    nlinarith [mul_le_mul_of_nonneg_right hy2 hy0]
  replace ht : ‖t‖ ≤ 7 / 2 * y := by linarith
  have n1 : ‖(p : ℂ) ^ (e + 1) * z₁‖ = p * y := by simp [h1, hy, pow_succ']
  have n2 : ‖(p : ℂ) ^ e * z₂‖ = y := by simp [h2, hy]
  have n3 : ‖(p : ℂ) * z₃‖ = p := by simp [h3]
  have hr : ‖t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)‖ ≤ 7 / 2 * y + (y + p + 1) := by
    refine (norm_sub_le _ _).trans (add_le_add ht ?_)
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, ← n2, ← n3]
    have := norm_add_le ((p : ℂ) ^ e * z₂) ((p : ℂ) * z₃)
    simpa using this
  have hE : t - eis4 p e z₁ z₂ z₃ = (t - ((p : ℂ) ^ e * z₂ + (p : ℂ) * z₃ + 1)) - (p : ℂ) ^ (e + 1) * z₁ := by
    rw [eis4]; ring
  have hlt : 7 / 2 * y + (y + p + 1) < p * y := by nlinarith
  constructor
  · intro h0
    rw [hE, sub_eq_zero] at h0
    rw [h0, n1] at hr
    linarith
  · rw [hE]
    refine (norm_sub_le _ _).trans ?_
    rw [n1, mul_comm 2, pow_mul, pow_succ' (p : ℝ) e, ← hy]
    have : (2 : ℝ) ≤ p * y := by nlinarith
    nlinarith

private theorem size {c A M e N d p : ℕ} (hN : N ≤ c * (M * (e + 1 + 1)) ^ A) (hM : 1 ≤ M) (hp : 5 ≤ p) :
    ((N * d : ℕ) : ℝ) * Real.log ((p : ℝ) ^ (2 * (e + 1))) ≤
      ((c * 2 ^ A * 2 : ℕ) : ℝ) * d * ((M : ℝ) * (e + 1)) ^ (A + 1) * Real.log p := by
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have h1 : N * d * (2 * (e + 1)) ≤ c * 2 ^ A * 2 * d * (M * (e + 1)) ^ (A + 1) := by
    have a1 : (M * (e + 1 + 1)) ^ A ≤ 2 ^ A * (M * (e + 1)) ^ A := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by nlinarith) _
    have a2 : e + 1 ≤ M * (e + 1) := Nat.le_mul_of_pos_left _ hM
    calc N * d * (2 * (e + 1)) ≤ c * (2 ^ A * (M * (e + 1)) ^ A) * d * (2 * (M * (e + 1))) := by
          gcongr
          exact hN.trans (by gcongr)
      _ = _ := by ring
  rw [Real.log_pow, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hl
  exact_mod_cast h1

end

end

end UpperTheory.GalN.V.Win.N
end

