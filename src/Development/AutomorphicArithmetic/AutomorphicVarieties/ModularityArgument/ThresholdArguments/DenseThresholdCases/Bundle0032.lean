import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.BaseChangeNorms.PropMHol
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0029
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.ExistsCharsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTypeVLoc

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.MPropMHol
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Base UpperTheory.V.Sd
section SlopeTestRemainingChoices
variable {l : ℕ} [Fact l.Prime]
private theorem sm_add {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)
private theorem sm_sub {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]; exact sm_add hx (by rwa [norm_neg])
private theorem sm_mul {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ < 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans_lt hy
private theorem le_of_cong {x y : Qbar l} (h : ‖x - y‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x‖ ≤ 1 := by
  have := IsUltrametricDist.norm_add_le_max (x - y) y
  rw [sub_add_cancel] at this
  exact this.trans (max_le h.le hy)
private theorem eq_of_cong {x y : Qbar l} (h : ‖x - y‖ < 1) (hy : ‖y‖ = 1) : ‖x‖ = 1 := by
  refine le_antisymm (le_of_cong h hy.le) (not_lt.1 fun hx => ?_)
  have := sm_sub hx h
  rw [sub_sub_cancel, hy] at this
  exact lt_irrefl _ this
private theorem inv_cong {x : Qbar l} (h : ‖x⁻¹ - 1‖ < 1) : ‖x - 1‖ < 1 := by
  have h1 := eq_of_cong h norm_one
  rw [norm_inv, inv_eq_one] at h1
  have h0 : x ≠ 0 := by rintro rfl; simp at h1
  have := sm_mul h1.le h
  rw [mul_sub, mul_inv_cancel₀ h0, mul_one, norm_sub_rev] at this
  exact this
private theorem norm_nat_lt {n : ℕ} (h : l ∣ n) : ‖(n : Qbar l)‖ < 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm]
  refine sm_mul (IsUltrametricDist.norm_natCast_le_one _ _) ?_
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one
private theorem pow_cong {n k : ℕ} (h : ¬ l ∣ n) (hk : l - 1 ∣ k) : ‖(n : Qbar l) ^ k - 1‖ < 1 := by
  obtain ⟨m, rfl⟩ := hk
  have hp : l.Prime := Fact.out
  have h1 : n ^ (l - 1) ≡ 1 [MOD l] := by
    rw [← Nat.totient_prime hp]
    exact Nat.ModEq.pow_totient ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  have h2 : n ^ ((l - 1) * m) ≡ 1 [MOD l] := by
    rw [pow_mul]; simpa using h1.pow m
  have h0 : 1 ≤ n ^ ((l - 1) * m) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h))
  have := norm_nat_lt ((Nat.modEq_iff_dvd' h0).1 h2.symm)
  rwa [Nat.cast_sub h0, Nat.cast_pow, Nat.cast_one] at this
variable {F : Type} [Field F] [NumberField F]
private theorem dvd_normV (w : Pl F) : l ∣ normV w ↔ ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  rw [normV, Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast,
    ringChar.spec]
  have hq : (ringChar (𝓞 F ⧸ w.asIdeal)).Prime := CharP.prime_ringChar _
  rw [Nat.prime_dvd_prime_iff_eq Fact.out hq, Nat.prime_dvd_prime_iff_eq hq Fact.out, eq_comm]
private theorem norm_val (ι : Qbar l ≃+* ℂ) {η : HChar F} (h : IsOfFinOrder η) (x : Ideles F) :
    ‖ι.symm (η.1 x : ℂˣ)‖ = 1 := by
  obtain ⟨m, hm, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : η.1 x ^ m = 1 := DFunLike.congr_fun (congrArg Subtype.val e) x
  have e2 : ‖ι.symm (η.1 x : ℂˣ)‖ ^ m = 1 := by
    rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, e1, Units.val_one, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e2
private theorem chiI_prime (ω : HChar F) (c : Pl F → ℕ) (w : Pl F) :
    chiI ω c w.asIdeal = if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0 := by
  classical
  rw [chiI, finprod_eq_single _ w]
  · rw [ordI, Associates.count_self w.associates_irreducible, pow_one]
  · intro v hv
    rw [ordI, Associates.count_eq_zero_of_ne v.associates_irreducible w.associates_irreducible, pow_zero]
    intro e
    exact hv (HeightOneSpectrum.ext (associated_iff_eq.1 (Associates.mk_eq_mk_iff_associated.1 e)))
private theorem gal_of (hA : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {η₁ η₂ : HChar F} (h₁ : IsOfFinOrder η₁)
    (h₂ : IsOfFinOrder η₂) {S : Set (Pl F)} (hS : S.Finite)
    (h : ∀ w ∉ S, η₁.UnrAt w ∧ η₂.UnrAt w ∧ (‖ι.symm (η₁.val w : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.val w : ℂˣ) - 1‖ < 1))
    (x : Ideles F) : ‖ι.symm (η₁.1 x : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.1 x : ℂˣ) - 1‖ < 1 := by
  obtain ⟨art, ha⟩ := hA F (AlgebraicClosure F)
  obtain ⟨m₁, hm₁, e₁⟩ := isOfFinOrder_iff_pow_eq_one.1 h₁
  obtain ⟨m₂, hm₂, e₂⟩ := isOfFinOrder_iff_pow_eq_one.1 h₂
  obtain ⟨δ₁, c₁, L₁⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₁) hm₁ e₁)
  obtain ⟨δ₂, c₂, L₂⟩ := ha.exists_isLAdicOf ι (isAlgPos_zero_of_orderDvd (χ := η₂) hm₂ e₂)
  have hcl : IsClosed ((fun σ => (δ₁ σ : Qbar l)) ⁻¹' Metric.ball 1 1 ∪ (fun σ => (δ₂ σ : Qbar l)) ⁻¹' Metric.ball 1 1) :=
    ((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₁)).union
      ((IsUltrametricDist.isClosed_ball _ _).preimage (Units.continuous_val.comp c₂))
  obtain ⟨σ, hσ⟩ := toAb_surjective (art x)
  have hd := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := F) (Ω := AlgebraicClosure F) GlobalTheory.Published.chebotarevDegreeOne' hS
  have hm := hcl.closure_subset_iff.2 ?_ (hd σ)
  · have f₁ := L₁ x σ hσ.symm
    have f₂ := L₂ x σ hσ.symm
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one] at f₁ f₂
    simpa only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, f₁, f₂] using hm
  · rintro τ ⟨v, hv, -, B, hB, hτ⟩
    obtain ⟨u₁, u₂, hh⟩ := h v hv
    simp only [Set.mem_union, Set.mem_preimage, mem_ball_iff_norm, L₁.frob_unr ha (Or.inr rfl) u₁ hB hτ,
      L₂.frob_unr ha (Or.inr rfl) u₂ hB hτ]
    exact hh.imp (fun t => inv_cong (by rwa [inv_inv])) fun t => inv_cong (by rwa [inv_inv])
end SlopeTestRemainingChoices
theorem UpperTheory.V.Z.Bc.propMHolZ_alt :
    _root_.UpperTheory.V.Z.Bc.Hypotheses4Z' → UpperTheory.V.Sd.PropMHol := by
  intro PP F _ _ _ l _ hl ι ω c hω hodd hc hne hcl P hP hQ B
  have hp : l.Prime := Fact.out
  obtain ⟨v, hvP, hvl, hv⟩ := hP
  obtain ⟨v', hvQ, hvl', hv'⟩ := hQ
  obtain ⟨φ, a, hφ, eφ, a1, aint, aeig⟩ := emix PP.eis F l ι ω c hω hodd hc hne hcl P ⟨v, hvP, hvl⟩
  have hl1 : 0 < l - 1 := Nat.sub_pos_of_lt hp.one_lt
  obtain ⟨k, hkB, hk0, hkd', ψ, d₀, b, hψ, eψ, hd, hb⟩ := PP.one F l hl ι B
  obtain ⟨χ, a', hχ, eχ, ha'⟩ := holMul F l ι 1 k (levL l c) ω hω φ ψ a d₀ b hφ hψ eφ eψ aint hd hb
  rw [add_comm 1 k] at hχ eχ
  simp only [map_sub] at ha'
  have hfin : {w | levL l c w ≠ 0}.Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
    refine ((Ideal.finite_factors h0).union (GlobalTheory.Mem.UnrAe.unr_ae_and_level F ω).1).subset fun w hw => ?_
    by_cases h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · exact Or.inl (Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 h))
    · refine Or.inr fun hu => hw ?_
      rw [levL, if_neg h]
      exact Nat.le_zero.1 ((hc w).2 fun x hx _ => hu x hx)
  have hL0 : ∀ w, levL l c w = 0 → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ∧ c w = 0 := fun w hw => by
    by_cases h : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [levL, if_pos h] at hw; exact absurd hw one_ne_zero
    · rw [levL, if_neg h] at hw; exact ⟨h, hw⟩
  have nval : ∀ {η : HChar F}, IsOfFinOrder η → ∀ w, ‖ι.symm (η.val w : ℂˣ)‖ = 1 := fun h w => norm_val ι h _
  have hpow : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖(normV w : Qbar l) ^ k - 1‖ < 1 := fun w hw =>
    pow_cong (mt (dvd_normV w).1 hw) hkd'
  have ht : ∀ w, ‖ι.symm (eisT l ω c P w)‖ ≤ 1 := fun w => by
    rw [eisT]
    split_ifs
    · exact (nval hω w).le
    · simp
    · rw [map_add, map_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le norm_one.le (nval hω w).le)
    · simp
  obtain ⟨g, lam, hg, hlam⟩ := _root_.UpperTheory.V.Sd.holLift_alt PP.h F l ι (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω χ 0 a'
    (eisT l ω c P) hχ eχ (fun 𝔪 h => le_of_cong (ha' 𝔪 h) (aint 𝔪 h))
    (eq_of_cong (ha' ⊤ top_ne_bot) (by rw [a1, map_one, norm_one])) ht (fun w 𝔪 h𝔪 => by
      have e := aeig w 𝔪 h𝔪
      have h1 := ha' _ (mul_ne_zero w.ne_bot h𝔪)
      have h2 := sm_mul (ht w) (ha' 𝔪 h𝔪)
      have h3 : ‖ι.symm (coefDiv a w.asIdeal 𝔪)‖ ≤ 1 ∧
          ‖ι.symm (coefDiv a' w.asIdeal 𝔪) - ι.symm (coefDiv a w.asIdeal 𝔪)‖ < 1 := by
        unfold coefDiv
        split_ifs with h
        · have h0 : h.choose ≠ ⊥ := fun h0 => h𝔪 (by rw [h.choose_spec, h0, Ideal.mul_bot])
          exact ⟨aint _ h0, ha' _ h0⟩
        · simp
      rw [hkCoef, chiI_prime, Nat.sub_self, pow_zero, mul_one] at e
      have e' := congrArg ι.symm e
      rw [hkCoef, chiI_prime, Nat.add_sub_cancel]
      split_ifs at e' ⊢ with h0
      · have h4 := sm_mul (nval hω w).le (sm_add (sm_mul (le_of_cong (hpow w (hL0 w h0).1) norm_one.le) h3.2)
          (sm_mul h3.1 (hpow w (hL0 w h0).1)))
        convert sm_add (sm_sub h1 h2) h4 using 2
        simp only [map_add, map_sub, map_mul, map_pow, map_natCast] at e' ⊢
        linear_combination e'
      · convert sm_sub h1 h2 using 2
        simp only [map_add, map_sub, map_mul, map_pow, map_natCast, map_zero] at e' ⊢
        linear_combination e')
  refine ⟨k, hkB, hkd', g, lam, hg, ?_, hlam⟩
  by_contra hcusp
  obtain ⟨η₁, η₂, f₁, f₂, rfl, hu, hr⟩ := holEis F (k + 1) (Nat.le_add_left _ _) (levL l c) hfin ω hω g lam hg hcusp
  simp only [map_sub, Nat.add_sub_cancel] at hlam hu hr
  have key := gal_of PP.h.litN.aut.art ι f₁ f₂ hfin fun w hw => by
    have h0 : levL l c w = 0 := not_not.1 hw
    obtain ⟨u₁, u₂, e⟩ := hu w h0
    refine ⟨u₁, u₂, ?_⟩
    have h1 := hlam w
    rw [e, eisT, if_neg (hL0 w h0).1, if_pos (hL0 w h0).2, HChar.val_mul] at h1
    have h2 := sm_sub (sm_mul (nval f₂ w).le (hpow w (hL0 w h0).1)) h1
    have h3 : ‖ι.symm (η₁.val w : ℂˣ) - 1‖ * ‖ι.symm (η₂.val w : ℂˣ) - 1‖ < 1 := by
      rw [← norm_mul]
      convert h2 using 2
      simp only [map_add, map_mul, map_pow, map_natCast, map_one, Units.val_mul]
      ring
    by_contra hn
    rw [not_or, not_lt, not_lt] at hn
    exact h3.not_ge (one_le_mul_of_one_le_of_one_le hn.1 hn.2)
  have hab : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l (η₁ * η₂) c P w)‖ = 1 →
      ‖ι.symm (η₁.val w : ℂˣ) - ι.symm (eisT l (η₁ * η₂) c P w)‖ < 1 := fun w hw h1 => by
    have h2 := eq_of_cong (hlam w) h1
    rcases hr w (fun h0 => (hL0 w h0).1 hw) with e | ⟨-, e⟩ | ⟨-, e⟩
    · simp [e] at h2
    · exact e ▸ hlam w
    · rw [e, map_mul, map_pow, map_natCast, ← Nat.cast_pow] at h2
      exact absurd h2 (sm_mul (nval f₂ w).le (norm_nat_lt (dvd_pow ((dvd_normV w).2 hw) hk0.ne'))).ne
  have e₁ : eisT l (η₁ * η₂) c P v = ((η₁ * η₂).val v : ℂˣ) := by rw [eisT, if_pos hvl, if_pos hvP]
  have e₂ : eisT l (η₁ * η₂) c P v' = 1 := by rw [eisT, if_pos hvl', if_neg hvQ]
  have a₁ := hab v hvl (by rw [e₁]; exact nval hω v)
  have a₂ := hab v' hvl' (by rw [e₂, map_one, norm_one])
  rw [e₁] at a₁
  rw [e₂, map_one] at a₂
  have kk : ‖ι.symm (η₁.val v * η₁.val v' : ℂˣ) - 1‖ < 1 ∨ ‖ι.symm (η₂.val v * η₂.val v' : ℂˣ) - 1‖ < 1 := by
    have := key (localIdele F v (atFin v (unif v)) * localIdele F v' (atFin v' (unif v')))
    rw [map_mul η₁.1, map_mul η₂.1] at this
    exact this
  simp only [HChar.val_mul, Units.val_mul, map_mul] at kk a₁ hv hv'
  have n₁ := nval f₁ v
  have n₂ := nval f₂ v
  have n₃ := nval f₁ v'
  have n₄ := nval f₂ v'
  generalize ι.symm (η₁.val v : ℂˣ) = x at *
  generalize ι.symm (η₂.val v : ℂˣ) = y at *
  generalize ι.symm (η₁.val v' : ℂˣ) = x' at *
  generalize ι.symm (η₂.val v' : ℂˣ) = y' at *
  have hy : ‖y - 1‖ < 1 := by
    rwa [← mul_one_sub, norm_mul, n₁, one_mul, norm_sub_rev] at a₁
  rcases kk with h | h
  · refine hv ?_
    convert sm_sub (sm_sub h (sm_mul n₁.le a₂)) a₁ using 2
    ring
  · refine hv' ?_
    convert sm_add (sm_sub h (sm_mul n₄.le hy)) (sm_mul n₄.le a₂) using 2
    ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAIsoTwOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HeckeGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
private theorem semisimple_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (H : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Units.mul_inv g) (fun s => ?_) H
  rw [hg s, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group
private theorem attC_conj {F Ω : Type} [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {π : CuspSub F n} (h : RepIso r r')
    (H : AttC ι r π) : AttC ι r' π :=
  ⟨semisimple_conj h H.1, H.2.mono fun _ ⟨B, hB, hE⟩ => ⟨B, hB, hE.of_iso h⟩⟩
private theorem tw_tw_inv {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (μ : Γ →* kˣ) :
    tw (tw r μ) μ⁻¹ = r := by
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [tw_val, tw_val, smul_smul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    inv_mul_cancel₀ (Units.ne_zero _), one_smul]
private theorem algPos_inv {K : Type} [Field K] [NumberField K] {χ : HChar K} {a : (K →+* ℂ) → ℤ} (h : IsAlgPos χ a) :
    IsAlgPos χ⁻¹ (-a) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
private theorem regAlg_tw {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {a : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ a) : (CG.mk (P.twist κ)).IsRegAlg := by
  have halg : κ.IsAlg a := fun k => hκ k fun φ => absurd
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_ofReal (φ x))))
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (Complex.ofRealHom.comp φ))))
  refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
  replace h := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).1 h
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 a halg τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + a τ, by push_cast; ring⟩
theorem aIsoTwOf_alt : _root_.UpperTheory.V.Z.Win.AIsoTwOfAlt := by
  intro FL WT _ F Ω _ _ _ _ _ _ l _ ι n r hW
  refine ⟨fun r' hi => ⟨fun v hv h => ?_, fun π hreg ha => ?_⟩, fun μ hμ => ?_⟩
  · exact (((FL F Ω l n r).1 r' hi).2.2 v).2 (hW.1 v hv ((((FL F Ω l n r').1 r hi.symm').2.2 v).1 h))
  · obtain ⟨t, ht⟩ := hW.2 π hreg (attC_conj hi.symm' ha)
    exact ⟨t, fun v hv => ht v (hv.imp id (((FL F Ω l n r').1 r hi.symm').2.2 v).2)⟩
  · obtain ⟨χ, -, art, a, hart, hpos, hL⟩ := hμ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have e : tw r μ = r := MonoidHom.ext fun s => Units.ext (by ext i; exact i.elim0)
      rw [e]
      exact hW
    have hv : ∀ v, (Unl1 (tw r μ) v → Unl1 r v) ∧ (PotUnl r v → PotUnl (tw r μ) v) ∧ (PotUnl (tw r μ) v → PotUnl r v) := fun v =>
      have h := ((FL F Ω l n r).2.1 μ).2.2 v
      ⟨h.1.2, h.2.1, h.2.2⟩
    refine ⟨fun v hl h => (hv v).2.1 (hW.1 v hl ((hv v).1 h)), fun π' hreg ha => ?_⟩
    have hatt : AttC ι r (π'.twist χ⁻¹) := by
      have h := UpperTheory.V.Af.Cq.attTwist F Ω l ι n (tw r μ) π' ha art χ⁻¹ (-a) μ⁻¹ hart hL.inv
      rwa [tw_tw_inv] at h
    obtain ⟨t, ht⟩ := hW.2 _ (regAlg_tw hreg (algPos_inv hpos)) hatt
    obtain ⟨b, hb⟩ := WT F χ
    refine ⟨t + b, fun v h => ?_⟩
    have h1 := hb n hn _ t v (ht v (h.imp id (hv v).2.2))
    rwa [← CuspSub.twist_mul, inv_mul_cancel, CuspSub.twist_one] at h1
end UpperTheory.V.Z.Win
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTypeV
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
open GlobalTheory.PRep GlobalTheory.TypeTwo.PowIrrProof
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped commutatorElement
namespace UpperTheory.V.Z.J.D.TypeVAux
private theorem exists_chars {Γ : Type} [Group Γ] {n : ℕ} (ρ : Representation ℂ Γ (Fin n → ℂ))
    (hs : ∀ g, Module.End.IsSemisimple (ρ g)) (hc : ∀ s t, ρ s * ρ t = ρ t * ρ s) :
    ∃ η : Fin n → Γ →* ℂˣ, (∀ g, (ρ g).charpoly = ∏ j, (X - C (η j g : ℂ))) ∧
      ∀ j g, ρ g = 1 → η j g = 1 := by
  obtain ⟨B, hB⟩ := GlobalTheory.TameInertiaChars.exists_basis_eigen (fun g => ρ g) hs fun g k => hc g k
  choose d hd using hB
  have hne : ∀ j, B j ≠ 0 := fun j => B.ne_zero j
  have canc : ∀ j {a b : ℂ}, a • B j = b • B j → a = b := fun j a b e =>
    smul_left_injective ℂ (hne j) e
  let c : Fin n → Γ →* ℂ := fun j =>
    { toFun := d j
      map_one' := canc j (by rw [← hd j 1, map_one, one_smul]; rfl)
      map_mul' := fun s t => canc j (by
        rw [← hd j (s * t), map_mul, Module.End.mul_apply, hd j t, map_smul, hd j s, smul_smul, mul_comm]) }
  refine ⟨fun j => (c j).toHomUnits, fun g => ?_, fun j g hg => ?_⟩
  · exact GlobalTheory.TameInertiaChars.charpoly_of_basis _ B _ fun j => hd j g
  · refine Units.ext (canc j ?_)
    show d j g • B j = (1 : ℂ) • B j
    rw [← hd j g, hg, one_smul]
    rfl
private theorem exists_perm {H : Type} [Monoid H] {n : ℕ} (a c : Fin n → H →* ℂ)
    (h : ∀ g, ∑ j, a j g = ∑ i, c i g) : ∃ e : Equiv.Perm (Fin n), ∀ i, a (e i) = c i := by
  classical
  have key : ∀ ψ : H →* ℂ, Nonempty ({i // c i = ψ} ≃ {j // a j = ψ}) := fun ψ =>
    ⟨Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      exact (GlobalTheory.CommSemisimpleChars.card_eq_of_sum_eq a c h ψ).symm)⟩
  let E := Equiv.ofFiberEquiv (f := c) (g := a) fun ψ => (key ψ).some
  exact ⟨E, fun i => Equiv.ofFiberEquiv_map _ i⟩
private theorem sum_of_prod {n : ℕ} (u v : Fin n → ℂ) (h : ∏ j, (X - C (u j)) = ∏ j, (X - C (v j))) :
    ∑ j, u j = ∑ j, v j := by
  have key : ∀ u : Fin n → ℂ, (∏ j, (X - C (u j)) : ℂ[X]).roots = Finset.univ.val.map u := fun u => by
    rw [Finset.prod_eq_multiset_prod]
    have := roots_multiset_prod_X_sub_C (Finset.univ.val.map u)
    rwa [Multiset.map_map] at this
  exact congrArg Multiset.sum (((key u).symm.trans (congrArg roots h)).trans (key v))
end UpperTheory.V.Z.J.D.TypeVAux
set_option synthInstance.maxHeartbeats 200000 in
open UpperTheory.V.Z.J.D UpperTheory.V.Z.J.D.TypeVAux in
theorem UpperTheory.V.Z.J.D.type_v_statement :
    _root_.UpperTheory.V.Z.J.D.TypeVAlt := by
  intro P L Ω _ _ _ _ _ _ n hn π w A h τ hτ χ hχ rc hrc hT
  obtain ⟨a, ha, ε, H⟩ := hrc
  have hart : a = artOf h := by
    have ha' : IsLocalArtin h (artOf h) := Classical.epsilon_spec (p := IsLocalArtin h) ⟨a, ha⟩
    obtain ⟨art, hart⟩ := P.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha.glob art hart _).trans (ha'.glob art hart _).symm)
  obtain ⟨b, hb, hN, hI⟩ := hT
  choose ψ hψ using hχ
  have hcomm : ∀ s t, b.ρ s * b.ρ t = b.ρ t * b.ρ s := by
    intro s t
    have hd : deg (⁅s, t⁆ : Weil h) = 0 := by
      have h0 : degHom h ⁅s, t⁆ = 1 := by
        rw [map_commutatorElement]
        exact (Commute.all _ _).commutator_eq
      rwa [degHom_apply, ofAdd_eq_one] at h0
    let c : Ine (F := L) A := ⟨_, deg_eq_zero_iff.1 hd⟩
    have hcc : ineIncl h c = ⁅s, t⁆ := Subtype.ext rfl
    have h1 : b.ρ ⁅s, t⁆ = 1 := by
      have h2 : ∀ i, (χ i c : ℂ) = 1 := fun i => by
        rw [← hψ i c, hcc, map_commutatorElement, (Commute.all _ _).commutator_eq]
        rfl
      rw [← hcc, hI c]
      simp [h2]
      rfl
    have e : s * t = ⁅s, t⁆ * (t * s) := by
      rw [commutatorElement_def]
      group
    rw [← map_mul, ← map_mul, e, map_mul, h1, one_mul]
  obtain ⟨η, hcp, hone⟩ := exists_chars b.ρ b.semisimple hcomm
  have hsum : ∀ s : Ine (F := L) A, ∑ j, ((Units.coeHom ℂ).comp ((η j).comp (ineIncl h))) s =
      ∑ i, ((Units.coeHom ℂ).comp (χ i)) s := by
    intro s
    refine sum_of_prod _ _ ?_
    have h1 := hcp (ineIncl h s)
    rw [hI s, ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin n)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin', Matrix.charpoly_diagonal] at h1
    exact h1.symm
  obtain ⟨e, he⟩ := exists_perm _ _ hsum
  have hηχ : ∀ i (g : Ine (F := L) A), η (e i) (ineIncl h g) = χ i g := fun i g =>
    Units.ext (DFunLike.congr_fun (he i) g)
  have hsm : ∀ j, GlobalTheory.WeilDeligne.IsSmooth (η j) := fun j => b.smooth.of_le fun σ hσ => hone j σ hσ
  choose ω hωs hωe using fun i => ha.factor (η (e i)) (hsm _)
  refine ⟨ω, hωs, ?_, fun i g => ?_⟩
  · refine _root_.UpperTheory.V.Z.J.D.TypeVAux.nonempty_equiv_principal_series_of_char_poly_of_generic P.loc H _ ω hωs (fun s => ?_) ⟨b, hb, hN⟩
      (GlobalTheory.ThK.DetProd.exists_isGeneric_of_isLocComp hτ)
    rw [← hb, WD.charPol_mk, hcp s, ← Equiv.prod_comp e]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hωe i]
    rfl
  · rw [← hart, ← hηχ i g, hωe i]
    rfl
end
end
end

