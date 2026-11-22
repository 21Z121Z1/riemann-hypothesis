import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.MonoOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CompatPSOf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lev

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

private theorem compatK (P : Hypotheses₂) (hS : CsdSs) {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} (hn : 2 ≤ n) {r : G K Ω →* GL (Fin n) (Qbar l)}
    {π : CuspSub K n} (hr : Continuous r) (hreg : (CG.mk π).IsRegAlg) (hd : GlobalTheory.ContraPair.DualIsConj π) (ha : AttC ι r π)
    {w : HeightOneSpectrum (𝓞 K)} {A : ValuationSubring Ω} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : Induces Bw) :
    IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := K) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
      SsCmp (wdAt (Loc.PP l) ι Bw h hj (r.comp (Dec (F := K) A).subtype)) (rc (algNorm σ)) := by
  obtain ⟨R, hc, hs, Haw, Hab⟩ := hS K Ω l ι n hn π hd (P.litN.aut.coh K n (by omega) π hreg)
  obtain ⟨p, hp⟩ : RepIso R r := by
    refine isoOfFrob P K Ω l ι n R r hc hr hs ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem K l] with w ⟨B, hB, hf⟩ hw
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    exact ⟨_, satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => Haw w hw A h rc hrc σ hσ, hf⟩
  have h1 := Hab _ _ (Loc.tiedP l) w A h O Bw hj
  have h3 := GlobalTheory.PstConj.main K Ω l ι n _ _ (Loc.tiedP l) w A h O Bw hj (R.comp (Dec (F := K) A).subtype)
    (r.comp (Dec (F := K) A).subtype) p (fun g => hp g.1) h1.1
  exact ⟨h3.1, fun σ hσ rc hrc => h3.2 ▸ h1.2 σ hσ rc hrc⟩

end UpperTheory.V.Lev

open UpperTheory.V.Lev in
theorem UpperTheory.V.Lev.compatPSOf :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Lev.CsdSs → UpperTheory.V.Lev.CompatPS := by
  intro P hS K _ _ _ hK n hn l _ Ω _ _ _ ι r π hr hreg hpol hatt w A h O _ _ _ Bw hj
  obtain ⟨χ₀, hχ₀⟩ := hpol
  obtain ⟨χ, -, wt, HT, hN, -, -, hall⟩ := galoisExistence_from_published P K Ω l ι n (by omega) π χ₀ hreg
    (fun v v' => (hχ₀.sign v).trans (hχ₀.sign v').symm) hχ₀.dual
  have hG := hall r hr hatt
  have hpst : IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := K) A).subtype) := by
    obtain ⟨T⟩ := Loc.tiedP l
    exact P.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hr.comp continuous_subtype_val))
      (hG.above _ _ ⟨T⟩ w A h O Bw hj).1
  refine ⟨hpst, fun σ hσ rc hrc hab => ?_⟩
  obtain ⟨μ₀, ⟨-, -, a, -, hχa, -⟩, -⟩ := hG.pol
  have hχa' : IsAlgPos χ⁻¹ (-a) := fun k hk => by
    rw [HChar.inf_inv, Units.val_inv_eq_inv_val, hχa k hk, ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
  obtain ⟨k, b, hb⟩ := Cq.signFix K hK χ⁻¹ (-a) hχa'
  obtain ⟨κ, mκ, hκ, hκχ⟩ := Cq.extReal K _ b hb
  have hcsd : GlobalTheory.ContraPair.DualIsConj (π.twist κ) := Cq.csdTwist K n π _ κ hχ₀.dual (by
    rw [hκχ, map_mul, map_pow, compNorm_quadChar, one_pow, mul_one, map_inv, hN])
  obtain ⟨artK, hartK, hμ⟩ := (GlobalTheory.Published.GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt P.litN.aut.art).1 K Ω
  obtain ⟨μ, ⟨hμc, hμ⟩, -⟩ := hμ l ι κ mκ (isAlgPos_of_isAlg hκ)
  obtain ⟨c1, c2⟩ := compatK P hS hn (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ n _ μ hr hμc) (regAlg_twist hreg hκ) hcsd
    (Cq.attTwist K Ω l ι n _ π hatt artK κ mκ μ hartK hμ) h Bw hj
  obtain ⟨ν, hν⟩ := hab
  exact Lev.untwistS P.litN.aut.chA P.litN.aut.chW P.litN.aut.berger K Ω l ι n _ hr artK κ mκ μ hartK
    (isAlgPos_of_isAlg hκ) hμc hμ w A h O Bw hj hpst c1 σ rc hrc (c2 _ (hσ.twist κ) rc hrc)
    (Or.inl ((Lev.ssCalc K Ω A w h).1 n _ ν hν))

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedAll
section
theorem UpperTheory.V.Lev.fixedAll (P : UpperTheory.V.Af.Hypotheses₂) : UpperTheory.V.Lev.FixedSs :=
  UpperTheory.V.Lev.fixedSs UpperTheory.V.Lev.flagPol (UpperTheory.V.Lev.fixedDvd P) (UpperTheory.V.Lev.fixedUnr P)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelFRes
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc
open scoped Pointwise

private theorem move {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω] [Algebra F K]
    [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F))) :
    ∃ (B : ValuationSubring Ω) (g : G F Ω), IsPlaceOver B w ∧ (∀ x, x ∈ B ↔ g x ∈ A) ∧
      (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  obtain ⟨B, hB⟩ := (exists_isPlaceOver Ω w : ∃ B : ValuationSubring Ω, IsPlaceOver B w)
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hm : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hv : ∀ y, (g • B).valuation (g y) < 1 ↔ B.valuation y < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, ← hm, ← hm, map_eq_zero_iff _ g.injective]
  have hD : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  refine ⟨B, g, hB, hm, hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, hv]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))

private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

private theorem char_conj {Γ C : Type} [Group Γ] [CommGroup C] (χ : Γ →* C) (g s : Γ) : χ (g * s * g⁻¹) = χ s := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

private theorem rep_conj {Γ C : Type} [Group Γ] [Group C] (r : Γ →* C) (P : C) (g s : Γ) :
    P * r g * r s * (P * r g)⁻¹ = P * r (g * s * g⁻¹) * P⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  group

theorem UpperTheory.V.Lev.levelFRes :
    UpperTheory.V.Lev.LevelFRes := by
  intro F K Ω _ _ _ _ _ _ _ _ _ _ _ l _ n M m r H
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  have hres : Continuous (res F Ω K : G K Ω →* G F Ω) := continuous_restrictScalarsHom F K Ω
  have hK : ∀ χ : G F Ω →* (Qbar l)ˣ, KillsMu M χ → KillsMu M (χ.comp (res F Ω K)) :=
    fun χ h s hs => h _ hs
  refine ⟨H.cont.comp hres, fun w hw => ?_, fun w hw => ?_⟩
  · obtain ⟨A, hA, χ, hχ, P, hP⟩ := H.away (w.under (𝓞 F)) (fun h => hw ((nat_mem_under l w).1 h))
    obtain ⟨B, g, hB, -, -, hI⟩ := move w hA
    refine ⟨B, hB, fun i => (χ i).comp (res F Ω K), fun i => hK _ (hχ i), P * r g, fun s hs => ?_⟩
    have h := hP _ (hI s hs)
    simp only [char_conj] at h
    rw [MonoidHom.comp_apply, rep_conj]
    exact h
  · obtain ⟨A, hA, κ, χ, hχ, ⟨P, hP⟩, hκ⟩ := H.above (w.under (𝓞 F)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, g, hB, -, hD, hI⟩ := move w hA
    let d : ↥(Dec (F := K) B) →* ↥(Dec (F := F) A) :=
      (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (Dec (F := K) B).subtype).codRestrict _
        fun s => hD s s.2
    have hd : ∀ s, (d s : G F Ω) = g * res F Ω K s * g⁻¹ := fun _ => rfl
    refine ⟨B, hB, fun i => (κ i).comp d, fun i => (χ i).comp (res F Ω K), fun i => hK _ (hχ i),
      ⟨P * r g, fun s => ?_⟩, fun i s hs => ?_⟩
    · rw [MonoidHom.comp_apply, rep_conj]
      exact hP (d s)
    · have h := hκ i (d s) (hI s hs)
      rw [hd, char_conj, char_conj] at h
      exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.LevelKO
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lev

open UpperTheory.V.Af

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}

private theorem frob_of_away (P : Hypotheses₂) (hc : Continuous R)
    (H : ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion K) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ)))
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal) (B : Multiset ℂˣ) (hB : (CG.mk π).HasSat w B) :
    FrobEig ι R w (algSat n (normV w) B) := by
  obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
  exact satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
    fun A h rc hrc => H w hw A h rc hrc σ hσ

private theorem iso_of_away (P : Hypotheses₂) (hr : Continuous r) (ha : AttC ι r π) (hc : Continuous R) (hs : IsSSRep R)
    (H : ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion K) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ))) :
    RepIso r R := by
  refine isoOfFrob P K Ω l ι n r R hr hc ha.1 hs ((ha.2.and (eventually_not_mem K l)).mono ?_)
  rintro w ⟨⟨B, h1, h2⟩, hw⟩
  exact ⟨_, h2, frob_of_away P hc H w hw B h1⟩

private theorem infOf_of_weights {m : Fin n → ℤ} {x : Multiset ℂ}
    (h : (Finset.univ.val.map fun i => -m i).map (fun k : ℤ => (k : ℂ)) = x.map fun z => ((n : ℂ) - 1) / 2 - z) :
    x = infOf m := by
  have h2 := congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) h
  simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id'] at h2
  rw [← h2, infOf]
  exact Multiset.map_congr rfl fun i _ => by push_cast; ring

private theorem not_mem_of_not_dvd {F : Type} [Field F] [NumberField F] {M : ℕ} {w : HeightOneSpectrum (𝓞 F)}
    (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (hM : ¬ l ∣ M) : (M : 𝓞 F) ∉ w.asIdeal := fun h => by
  obtain ⟨a, b, e⟩ : IsCoprime ((l : ℕ) : 𝓞 F) (M : 𝓞 F) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hM)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left a hw) (w.asIdeal.mul_mem_left b h)))

private theorem sph_of {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {n : ℕ}
    {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion F) → WD h} (hrc : IsRec h rc) (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (h0 : (rc (algNorm σ)).mono0) (d : ℕ)
    (hI : ∀ s : ↥(Ine (F := F) A), (rc (algNorm σ)).charPol (ineIncl h s) = (X - 1) ^ d) : GlobalTheory.SmGL.IsSpherical σ.ρ := by
  obtain ⟨a, ha, ε, -, H⟩ := hrc
  have hu : (rc (algNorm σ)).unr := by
    obtain ⟨k, b, e⟩ := WD.exists_rep (rc (algNorm σ))
    rw [← e] at h0 hI ⊢
    rw [WD.unr_mk]
    refine ⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff b).1 h0, fun s => ?_⟩
    have h1 := LinearMap.aeval_self_charpoly (b.ρ (ineIncl h s))
    have h2 := hI s
    rw [WD.charPol_mk] at h2
    rw [h2, map_pow, map_sub, aeval_X, map_one] at h1
    have hs : Module.End.IsSemisimple (b.ρ (ineIncl h s) - algebraMap ℂ (Module.End ℂ (Fin k → ℂ)) 1) :=
      Module.End.isSemisimple_sub_algebraMap_iff.2 (b.semisimple _)
    rw [map_one] at hs
    exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h1⟩ hs)
  obtain ⟨v, hv0, hv⟩ := UpperTheory.hasFixed_of_algNorm_fixed_ne_bot F w n σ _ le_rfl ((H.sph _).2 hu)
  exact (Submodule.ne_bot_iff _).2 ⟨v, fun g => by simpa using hv g.1 g.2, hv0⟩

def LevelKO : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
    ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n), Level l M m r → Odd n → (CG.mk π).IsRegAlg →
      GlobalTheory.ContraPair.DualIsConj π → AttC ι r π →
      π ∈ SigK K m M ∧ ∀ w : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∉ w.asIdeal → ∀ B, (CG.mk π).HasSat w B →
        FrobEig ι r w (algSat n (normV w) B)

end UpperTheory.V.Lev

open UpperTheory.V.Af UpperTheory.V.Lev in
theorem UpperTheory.V.Lev.levelKO :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Lev.CsdSs → UpperTheory.V.Lev.MonoOdd → UpperTheory.V.Lev.FixedSs → UpperTheory.V.Lev.LevelKO := by
  intro P hC hO hF K _ _ _ n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hodd hreg hd ha
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (quadChar K ^ n) :=
    ⟨fun v => by rw [locInf_pow, quadChar_locInf], by
      rw [map_pow, compNorm_quadChar, one_pow]; exact (GlobalTheory.ContraPair.dualIsConjBy_one π).2 hd⟩
  obtain ⟨R₁, wt, HT, H₁⟩ := P.litN.aut.gal K Ω l ι n (by omega) π _ hreg hpol
  obtain ⟨R, hc, hs, Haw, Hab⟩ := hC K Ω l ι n hn π hd (P.litN.aut.coh K n (by omega) π hreg)
  have hiso₁ := iso_of_away P hL.cont ha H₁.cont H₁.ss H₁.away
  have L₁ := hL.of_iso hiso₁
  have hiso := iso_of_away P hL.cont ha hc hs Haw
  have L := hL.of_iso hiso
  refine ⟨⟨fun φ => ?_, hd, ?_⟩, fun w hw B hB => (frob_of_away P hc Haw w hw B hB).of_iso hiso.symm'⟩
  · let τ : K →+* Qbar l := ι.symm.toRingHom.comp φ
    have hφ : ι.toRingHom.comp τ = φ := RingHom.ext fun x => ι.apply_symm_apply _
    obtain ⟨w, hw, hτ⟩ := GlobalTheory.GalFirstClause.existsIsInduced l K Ω τ
    obtain ⟨A, hA, χ, κ, h1, h2, h3, -⟩ := L₁.above w hw
    obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
    obtain ⟨τ', hτ'⟩ := hτ A hA O Bw hj
    have hJ := jumpsAbove P K Ω l hl n M hM m R₁ H₁.cont w A hA O Bw hj κ ⟨χ, h1, h2, h3⟩ τ _
      ((H₁.above _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj).jumps τ _ τ' hτ')
    have hw := H₁.weights τ
    rw [hJ, hφ] at hw
    rw [← infOf_of_weights hw]
    exact ParLaws.hasInfChar_infChar (CG.mk π) φ
  · refine globFixed P K n M hM _ π.finPart π.isSmooth_finPart fun w => ?_
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    refine ⟨σ, hi σ hσ, ?_⟩
    by_cases hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal
    · obtain ⟨A, hA, χ, κ, h1, h2, h3, h4⟩ := hL.above w hw
      obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
      obtain ⟨rc, hrc⟩ := P.exists_rec hA
      obtain ⟨hp, he⟩ := Hab _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj
      have hS := fun hor => hF K Ω l ι n M hM m R hc w A hA O Bw hj κ ⟨χ, h1, h2.of_iso hiso, h3⟩ hp rc hrc σ
        (fun ⟨μ, hμ⟩ => he σ hσ rc hrc (Or.inl ((ssCalc K Ω A w hA).1 n _ μ hμ))) hor
      rcases h4 with h4 | h4
      · exact hS (Or.inr (Or.inl h4))
      · by_cases hlM : l ∣ M
        · exact hS (Or.inl hlM)
        refine hS (Or.inr (Or.inr fun _ => ?_))
        obtain ⟨μ, m1, m2, -⟩ := flagPol K Ω l ι n M hM m R hc w A hA O Bw hj κ ⟨χ, h1, h2.of_iso hiso, h3⟩ hp
        have e := he σ hσ rc hrc (Or.inl ((ssCalc K Ω A w hA).1 n _ μ m1))
        refine sph_of hrc σ (hO K n hodd l Ω ι r π hL.cont hreg hd ha w A hA h4 σ hσ rc hrc) n fun s => ?_
        rw [← e, m1]
        simp [fun i => m2 i s (UpperTheory.inertia_fixes_roots_of_unity_prime_to_residue_char K Ω w A hA M (not_mem_of_not_dvd hw hlM) s s.2)]
    · obtain ⟨A, hA, χ, h1, h2⟩ := L.away w hw
      obtain ⟨rc, hrc⟩ := P.exists_rec hA
      exact locFixed P K Ω n M hM w A hA rc hrc σ
        (wdAway P K Ω l ι n M hM R hc w hw A hA χ h1 h2 _ (Haw w hw A hA rc hrc σ hσ))

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.MonoOddOf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lev

private theorem monodromy_zero_of_dim_one {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A w} (x : WD h) (hx : x.lpDim = 1) : x.mono0 := by
  obtain ⟨n, b, rfl⟩ := WD.exists_rep x
  obtain rfl : n = 1 := by simpa using hx
  refine (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 ?_
  have h1 := (LinearMap.isNilpotent_iff_charpoly b.N).1 b.nilpotent
  have h2 := LinearMap.aeval_self_charpoly b.N
  rw [h1] at h2
  simpa using h2

theorem monoOddOf : UpperTheory.V.Af.Hypotheses₂ → CsdMonoOdd → MonoOdd := by
  intro P hS K _ _ _ n hodd l _ Ω _ _ _ ι r π hr hreg hd ha w A h ⟨O, _, _, _, Bw, hj, hpc⟩ σ hσ rc hrc
  rcases (show n = 1 ∨ 2 ≤ n by obtain ⟨k, rfl⟩ := hodd; omega) with rfl | hn
  · refine monodromy_zero_of_dim_one _ ?_
    rw [rec_algNorm hrc, WD.lpDim_tw]
    obtain ⟨a, ha, ε, -, H⟩ := hrc
    exact H.dim _
  obtain ⟨R, hc, hs, Haw, Hab⟩ := hS K Ω l ι n hn hodd π hd (P.litN.aut.coh K n (by omega) π hreg)
  obtain ⟨p, hp⟩ : RepIso R r := by
    refine isoOfFrob P K Ω l ι n R r hc hr hs ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem K l] with w ⟨B, hB, hf⟩ hw
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    exact ⟨_, satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => Haw w hw A h rc hrc σ hσ, hf⟩
  have h1 := Hab _ _ (Loc.tiedP l) w A h O Bw hj
  have h3 := GlobalTheory.PstConj.main K Ω l ι n _ _ (Loc.tiedP l) w A h O Bw hj (R.comp (Dec (F := K) A).subtype)
    (r.comp (Dec (F := K) A).subtype) p (fun g => hp g.1) h1.1
  refine h1.2 σ hσ rc hrc ?_
  rw [← h3.2]
  exact (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj _ ι _ h3.1).2 hpc

theorem monoOdd (P : UpperTheory.V.Af.Hypotheses₂) : MonoOdd := monoOddOf P P.mono

end UpperTheory.V.Lev

end
end

