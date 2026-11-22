import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0002
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.OfTempered
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.EventuallyNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0228
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConjSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0035
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ThetaSatakeParametersInverse
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0008
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharPolCharCongr
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}

theorem charPol_char_congr {x y z : WD h} (hz : z.lpDim = 1) (g : ↥(Weil h)) (e : x.charPol g = y.charPol g) :
    (x.lpChar z).charPol g = (y.lpChar z).charPol g := by
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.1 ((WD.card_eig z g).trans hz)
  rw [WD.charPol_eq_prod, WD.charPol_eq_prod (y.lpChar z), GlobalTheory.RowTie.EigTwist.eig_lpChar x z g hz c hc,
    GlobalTheory.RowTie.EigTwist.eig_lpChar y z g hz c hc, WD.eig, WD.eig, e]

theorem AwV.char {x y z : WD h} (k : AwV x y) (hz : z.lpDim = 1) : AwV (x.lpChar z) (y.lpChar z) :=
  ⟨fun g => charPol_char_congr hz g (k.pol g), fun m => by rw [k.n0 ((WD.monomial_char_iff _ _ hz).1 m)]⟩

theorem WDN.charpoly (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (k : WDN ι r y) (g : ↥(Weil h)) :
    (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = y.charPol g := by
  obtain ⟨x, hx, k⟩ := k
  have e := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  rw [← hN.charPol_wdOf hl ht ι g, e, k.pol]

theorem wn' (k : WDN ι r y) : WDN ι r y := k
theorem woOf' (k : IsWDOf ι r y) : WDN ι r y := .of_isWDOf k
theorem woConj' (k : WDN ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : G E Ω →* GL (Fin n) (Qbar l)}
    (P : GL (Fin n) (Qbar l)) (hP : ∀ g : ↥(Weil h), P * r g = r' g * P) : WDN ι r' y := k.of_conj hl P hP
theorem woSum' (hA : Gu.SumAway) {m : ℕ} {r' : G E Ω →* GL (Fin m) (Qbar l)} (hc : Continuous r) (hc' : Continuous r')
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {y' : WD h} (k : WDN ι r y) (k' : WDN ι r' y') :
    WDN ι (Formalism.MainNotions.SumRepresentations.At.sumRep r r') (y.lpSum y') := by
  obtain ⟨x, hx, k⟩ := k
  obtain ⟨x', hx', k'⟩ := k'
  exact ⟨_, hA E Ω l ι n m r r' hc hc' w hl A h _ _ hx hx', k.sum k'⟩
theorem woChar' (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : G E Ω →* GL (Fin n) (Qbar l)} {z : WD h} (hz : z.lpDim = 1)
    (e : IsWDOf ι r' ((wdOf h hl ι r).lpChar z)) (k : WDN ι r y) : WDN ι r' (y.lpChar z) := ⟨_, e, (k.awV hl).char hz⟩
theorem galEx' (H : CuspU) (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (ha : 1 ≤ a) (π : CuspSub E a) (χ : HChar (maximalRealSubfield E))
    (hr : (CG.mk π).IsRegAlg) (hp : IsPolarized π χ) :
    ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), IsGalU π χ ι r wt HT ∧
      ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
        (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → WDN ι r (rc (algNorm σ)) := by
  obtain ⟨r, wt, HT, k⟩ := H E Ω l ι a ha π χ hr hp
  exact ⟨r, wt, HT, k, fun w hl A h rc hrc σ hσ => .of_aw hl k.cont (.of_aw (k.away w hl A h rc hrc σ hσ))⟩

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ClassicalityIrreducibleArith
section
noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.W
open UpperTheory.V.HV (Coef)

namespace UpperTheory.GalN.V

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ) (J : Ideal B.B)

def ClassicalityIrreducibleArith : Prop := r.V0ok →
  ∀ (x : B.Pt) (h : s.Wt n) (ρ : G L Ω →* GL (Fin n) (Qbar l)), J ≤ RingHom.ker x → x.Arith h → x.IsRep ρ → Af.IsIrr ρ →
    IsAutCsdN ι ρ

variable {B ι J}

end UpperTheory.GalN.V
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.EventuallyNotMem
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published

private theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {m : Fin n → ℤ}
    (hm : StrictAnti m) {π : CuspSub K n} (h : ∀ τ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (h τ)]
  refine ⟨Multiset.Nodup.map (fun i j e => hm.injective ?_) Finset.univ.nodup, fun z hz => ?_⟩
  · exact_mod_cast add_left_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, add_comm _ _⟩

private theorem eventually_notMem {K : Type} [Field K] [NumberField K] {M : ℕ} (hM : 1 ≤ M) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (M : 𝓞 K) ∉ w.asIdeal := by
  have h0 : Ideal.span {(M : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 (by omega)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  exact Ideal.dvd_span_singleton.2 (not_not.1 hw)

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (cPl w) = normV w := by
  have e : (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv) :=
    (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)
  show Ideal.absNorm (cPl w).asIdeal = Ideal.absNorm w.asIdeal
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).symm ?_).toEquiv).symm
  rw [e]
  exact (Ideal.map_symm _).symm

private theorem eventually_unr {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] (χ : HChar F) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, χ.UnrAt (w.under (𝓞 F)) := by
  rw [Filter.eventually_cofinite]
  refine ((GlobalTheory.Mem.UnrAe.finite_ramified χ).preimage' (f := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 F))
    fun v _ => ?_).subset fun w hw => hw
  haveI := v.isMaximal
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage
    (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) fun _ _ _ _ e => HeightOneSpectrum.ext e).subset fun w hw => ?_
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩

private theorem dual_conj {n q : ℕ} (hn : 1 ≤ n) (hq : q ≠ 0) (σ : ℂ ≃+* ℂ) {B B₁ B' B₁' : Multiset ℂˣ} {z z' : ℂˣ}
    (hz : (z' : ℂ) = σ z) (h : B₁.map (·⁻¹) = B.map (· * z⁻¹)) (e : algSat n q B' = (algSat n q B).map σ)
    (e₁ : algSat n q B₁' = (algSat n q B₁).map σ) : B₁'.map (·⁻¹) = B'.map (· * z'⁻¹) := by
  have hc : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (n - 1) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity), add_halves, ← Nat.cast_one (R := ℝ), ← Nat.cast_sub hn,
      Real.rpow_natCast]
    push_cast
    rfl
  have h0 : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (by positivity) _).ne'
  have ae : ∀ B : Multiset ℂˣ, algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) :=
    fun B => by simp [algSat]
  simp only [ae] at e e₁
  clear ae
  generalize (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = c at *
  have hs : σ c * σ c = c * c := by rw [← map_mul, hc, map_pow, map_natCast]
  have h1 : σ c ≠ 0 := (map_ne_zero σ).2 h0
  apply Multiset.map_injective (f := fun x : ℂˣ => c⁻¹ * (x : ℂ))
    (fun x y hxy => Units.ext (mul_left_cancel₀ (inv_ne_zero h0) hxy))
  have k1 := congrArg (Multiset.map fun x : ℂ => x⁻¹) e₁
  have k2 := congrArg (Multiset.map fun x : ℂ => (c * c)⁻¹ * x * (σ z)⁻¹) e
  have k3 := congrArg (Multiset.map fun x : ℂˣ => σ (c⁻¹ * (x : ℂ))) h
  simp only [Multiset.map_map, Function.comp_def] at k1 k2 k3 ⊢
  refine (Multiset.map_congr rfl fun x _ => ?_).trans (k1.trans ((Multiset.map_congr rfl fun x _ => ?_).trans (k3.trans
    ((Multiset.map_congr rfl fun x _ => ?_).trans (k2.symm.trans (Multiset.map_congr rfl fun x _ => ?_))))))
  · simp [mul_comm]
  · simp [mul_comm]
  · rw [← hs]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    field_simp
  · simp only [Units.val_mul, Units.val_inv_eq_inv_val, hz]
    field_simp

theorem UpperTheory.GalN.V.conjPrime₂ :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.ConjP := by
  intro P K _ _ _ hK n hn m hm M hM σ π ⟨hinf, ⟨χ, hpol⟩, hfix⟩
  have hreg := regAlg_of_infOf hm hinf
  obtain ⟨π', τ, τ', h1, h2, h3, h4⟩ := P.conjC K n (by omega) π hreg σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  have hsat : ∀ w B, (CG.mk π).HasSat w B →
      ∃ B', (CG.mk π').HasSat w B' ∧ algSat n (normV w) B' = (algSat n (normV w) B).map σ :=
    fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB
  refine ⟨π', ⟨fun φ => ?_, ?_, hs.hasFixed hfix⟩, hsat⟩
  · have e : σ.toRingHom.comp (σ.symm.toRingHom.comp φ) = φ := RingHom.ext fun x => σ.apply_symm_apply _
    exact e ▸ h4 _ _ (hinf _)
  obtain ⟨a, ha⟩ := GlobalTheory.T.isAlgebraicHeckeChar_of_regularAlgebraic_polarizedPair K n (by omega) π χ hreg hpol
  have hF : Module.finrank ℚ (maximalRealSubfield K) = 1 := by
    have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield K) K
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield K) K] at h1
    omega
  obtain ⟨χ', hsg, hv⟩ := UpperTheory.V.Br.charConj _ hF χ a ha σ
  refine ⟨χ', fun v => (hsg v).trans (hpol.sign v),
    UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse P.litN.aut.js.1 P.litN.aut.gk K n (by omega) π' _ ?_⟩
  have hM1 := eventually_notMem (K := K) hM
  filter_upwards [eventually_unr (K := K) χ, hM1,
    (conjSrc_injective (IsCMField.complexConj K).toRingEquiv).tendsto_cofinite.eventually hM1] with w hw a1 a2
  obtain ⟨B, hB⟩ := satK P K n M π hfix w a1
  obtain ⟨B₁, hB₁⟩ := satK P K n M π hfix (cPl w) a2
  obtain ⟨B', hB', e⟩ := hsat w B hB
  obtain ⟨B₁', hB₁', e₁⟩ := hsat _ B₁ hB₁
  rw [normV_cPl] at e₁
  obtain ⟨e3, e4⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ w _ (normV_under w) hw
  obtain ⟨e5, e6⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ' w _ (normV_under w) (hv _ hw).1
  refine ⟨e5, B', B₁', hB', hB₁', dual_conj (by omega) (GlobalTheory.WeilDeligne.one_lt_normV w).ne_bot σ ?_
    (UpperTheory.V.Br.satOfPol K n π _ hpol.dual w e3 B B₁ hB hB₁) e e₁⟩
  rw [e4, e6, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, (hv _ hw).2]

example : type_of% @UpperTheory.V.Br.conjPrime₂ := @UpperTheory.GalN.V.conjPrime₂
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ExistenceOfGaloisRepresentationsOfHyp
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalN.V
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.ExLib

def ExCN : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (π : CuspSub F n) (χ : HChar (maximalRealSubfield F)), (CG.mk π).IsRegAlg →
    (∀ v v' : InfinitePlace (maximalRealSubfield F), χ.locInf v (-1) = χ.locInf v' (-1)) →
    GlobalTheory.ContraPair.DualIsConjBy π (compNorm F χ) →
    ∃ (χ' : HChar (maximalRealSubfield F)) (r : G F Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (HT : (F →+* Qbar l) → Multiset ℤ),
      compNorm F χ' = compNorm F χ ∧ IsGalU π χ' ι r wt HT ∧ AttC ι r π ∧
      ∀ r' : G F Ω →* GL (Fin n) (Qbar l), Continuous r' → AttC ι r' π → IsGalU π χ' ι r' wt HT

end UpperTheory.GalN.V

namespace UpperTheory.V.Af

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}

private theorem exists_sign (χ : HChar (maximalRealSubfield K))
    (h : ∀ v v' : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = χ.locInf v' (-1)) :
    ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have h2 : χ.locInf v (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e
  · exact ⟨0, fun u => (h u v).trans (Units.ext (by simpa using e))⟩
  · exact ⟨1, fun u => (h u v).trans (Units.ext (by simpa using e))⟩

end UpperTheory.V.Af

end
end

