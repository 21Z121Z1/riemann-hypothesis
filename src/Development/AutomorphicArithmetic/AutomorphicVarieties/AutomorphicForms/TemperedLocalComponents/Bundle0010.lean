import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0056
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0059
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0055
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0057
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0054
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0060
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistedDualFrobeniusCompatibility
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0058
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0678
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1357
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0724
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExistsIdele
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0006
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CsdOf
section
open NumberField Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp GlobalTheory.HeckeGal

theorem UpperTheory.V.Af.csdOf :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.CsdOf := by
  intro hP F₀ F Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n hn r c P hc haut hpair
  obtain ⟨π, hreg, hatt⟩ := ((UpperTheory.V.Af.autBridge hP F Ω l ι n r).2.1).1 haut
  haveI : IsAlgClosure (maximalRealSubfield F) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans (maximalRealSubfield F) F Ω⟩
  obtain ⟨art, hart⟩ : ∃ art : Neutral.B1.Ideles (maximalRealSubfield F) →* Gab (maximalRealSubfield F) Ω,
      IsGlobalArtin art := hP.toClassicalTheorems.litN.aut.art _ Ω
  have h1 : IsLAdicCharOf (E := F) (Ω := Ω) ι 1 1 := by
    refine ⟨continuous_const, art, 0, hart, fun k _ => ?_, fun x σ _ => ?_⟩
    · simp [HChar.inf]
    · rw [infPow_zero, lPow_zero]
      change (1 : Qbar l) = ι.symm (1 * 1⁻¹) * 1
      simp
  obtain ⟨j, hj⟩ := hc
  let c' : G (maximalRealSubfield F) Ω := AlgEquiv.ofRingEquiv (f := c.toRingEquiv) fun x => by
    apply j.injective
    refine (hj _).trans ?_
    exact (mem_maximalRealSubfield_iff x.1).1 x.2 (j.comp (algebraMap F Ω))
  have hd := UpperTheory.V.Af.selfDualC hP F Ω l ι n hn r π hatt 1 1 h1 c' P ⟨j, hj⟩ (by
    intro s s' hs
    rw [MonoidHom.one_comp, mul_one]
    refine hpair s s' (AlgEquiv.ext fun x => ?_)
    exact DFunLike.congr_fun hs x)
  rw [map_one, GlobalTheory.ContraPair.dualIsConjBy_one] at hd
  exact ⟨π, hreg, hd, hatt⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GalUnitary
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Gu

private theorem ev_notMem {K : Type} [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ((l : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr (not_not.1 hv)

private theorem assemble (H : HypothesesH) (hFam : SumFam) (hHalf : Half) (hStr : Strings) (hUni : CompUnique) (hRec : RecTot)
    (hFrob : FrobTot) (hPol : PolOfFrob) (hLink : SatLink) (hConj : SatConj) (hIrr : IrrCase) : GalUnitary := by
  intro E Ω _ _ _ _ _ _ hE l _ _ ι n hn π hπ
  obtain ⟨c, a, d, hsum, P, ρ, m, σ, hP, hS, hsplit⟩ :=
    GlobalTheory.BcSpeh.bcSpeh_of_baseChange (GlobalTheory.BaseChangeBridge.main H.litN.aut.bc H.litN.loc.bern)
      (GlobalTheory.SpehInfChar.discreteSpectrumGL_of_residual H.litN.aut.mw) E hE n hn π hπ
  have hc : 1 ≤ c := by
    rcases c with _ | c
    · simp at hsum; omega
    · omega
  have hint : ∀ i (k : Fin (d i)) τ, (m i τ).Nodup ∧ ∀ z ∈ m i τ, ∃ j : ℤ, z + (ex n (d i) k : ℂ) / 2 = j := fun i k τ => by
    obtain ⟨lam, hl⟩ := GlobalTheory.T.exists_algebraicWeight_of_automorphic_definiteUnitary E n hn π hπ τ
    exact (hStr n c d (m · τ) lam (hP.weight τ lam hl)).1 i k
  choose r₀ HT₀ h₀ hw₀ using fun i (k : Fin (d i)) =>
    hHalf E Ω l ι (a i) (hP.pos i).1 (P i) (hP.csd i) (ρ i) (hP.loc i) (m i) (hP.inf i) (ex n (d i) k) (hint i k)
  choose r₁ h₁ hi₁ using fun i => hFam E Ω l ι (d i) (hP.pos i).2 (fun _ => a i) (fun _ => (hP.pos i).1) (d i * a i) (by simp)
    (r₀ i) _ (HT₀ i) (h₀ i)
  obtain ⟨r, hr, hi⟩ := hFam E Ω l ι c hc (fun i => d i * a i) (fun i => Nat.mul_pos (hP.pos i).2 (hP.pos i).1) n hsum r₁ _ _ h₁
  have hpar : ∀ w, ParAt ι r w (totPar n d (ρ · w)) := hr.par
  have hF : ∀ w : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ S : Fin c → Multiset ℂˣ,
      (∀ i, (CG.mk (P i)).HasSat w (S i)) → FrobEig ι r w (algSat n (normV w) (satTot w d S)) := fun w hw S hS =>
    hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S (fun i => ((hLink E _ (P i)).1 w _ (hP.loc i w) _).1 (hS i)) (hpar w)
  have hev : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧
      ∃ S : Fin c → Multiset ℂˣ, ∀ i, (CG.mk (P i)).HasSat w (S i) := by
    filter_upwards [ev_notMem (K := E) l, Filter.eventually_all.2 fun i => (hLink E _ (P i)).2] with w h1 h2
    exact ⟨h1, Classical.skolem.1 h2⟩
  refine ⟨r, _, hr.cont, hr.ss, fun w hw hu A hA => ?_, hr.ht, fun τ lam hl => ?_, fun w hw τ hτ => ?_, ?_, fun hirr => ?_⟩
  · choose S hSat using fun i => (satLoc H.toClassicalTheorems E (a i) w (ρ i w)).1 (by
      obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1
        (GlobalTheory.SphBC.isSpherical_of_isUnramU E hE n π hπ c a d hsum P ρ m σ hP hS hsplit w hu i (ρ i w) (hP.loc i w))
      exact ⟨x, h0, GlobalTheory.LGrp.mem_fixed.1 hx⟩)
    exact (hFrob E Ω l ι n c a d r hr.cont w hw (ρ · w) S hSat (hpar w) A hA).1
  · rw [← (hStr n c d (m · (ι.toRingHom.comp τ)) lam (hP.weight _ lam hl)).2]
    simp only [← hw₀]
    simp only [← Multiset.coe_mapAddMonoidHom, map_sum]
  · exact (locGlob_iff ι r w τ).2 ((hpar w).congr (hRec E Ω n c a d hsum P w (ρ · w) (σ · w) hP.pos (hP.loc · w) (hS · w) τ
      (hUni E n π hπ w hw _ _ _ _ hτ (hsplit w hw))))
  · refine hPol E Ω l ι n r hr.cont hr.ss ?_
    filter_upwards [hev, (conjSrc_injective (IsCMField.complexConj E).toRingEquiv).tendsto_cofinite.eventually hev]
      with w ⟨hw, _⟩ ⟨hw', S, hS'⟩
    refine ⟨satTot (Bc.cPl w) d S, ?_, hF _ hw' S hS'⟩
    rw [← (hConj E w).2 c d S]
    exact hF w hw _ fun i => (hConj E w).1 _ (P i) (hP.csd i) _ (hS' i)
  · refine hIrr E Ω l ι n hn π hπ c a d hsum P ρ m hP (hi hirr).1 (fun i => (hi₁ i ((hi hirr).2 i)).1) r hr.ss ?_
    filter_upwards [hev] with w ⟨hw, S, hS'⟩
    exact ⟨S, hS', hF w hw S hS'⟩

theorem UpperTheory.V.Af.galUnitary :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.GalUnitary := fun H =>
  assemble H (UpperTheory.sum_family_of_reductions (UpperTheory.sum_two_of_hodge_tate H UpperTheory.galoisRep_direct_sum_away_from_places UpperTheory.sum_hodge_tate) UpperTheory.finiteSum_reduction)
    (UpperTheory.half_of_compatible_polarization H UpperTheory.eta_condition UpperTheory.twist_local_components_compatible (UpperTheory.compatible_polarization_of_link H (compatCsd H) (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H)))
    UpperTheory.speh_parameter_strings UpperTheory.building_component_uniqueness (UpperTheory.total_reciprocity H) (UpperTheory.total_frobenius_compatibility H) (UpperTheory.twistedDual_frobenius_compatibility (isoOfFrob H.toClassicalTheorems))
    (UpperTheory.satake_galois_compatibility_of_hecke_eigensystem H) UpperTheory.satake_parameters_complex_conjugate (UpperTheory.irreducible_case H)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LevelQ
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

section Conj

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}

end Conj

private theorem infOf_of_weights {n : ℕ} (m : Fin n → ℤ) (μ : Multiset ℂ)
    (h : (Finset.univ.val.map fun i => -m i).map (fun n : ℤ => (n : ℂ)) = μ.map fun z => ((n : ℂ) - 1) / 2 - z) :
    μ = infOf m := by
  have h2 := congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) h
  simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id', Int.cast_neg, sub_neg_eq_add] at h2
  exact h2.symm

private theorem exists_over (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] :
    ∃ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hl : (l : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hu : ¬ IsUnit (l : 𝓞 F) := fun hu => by
    have h := hu.map (Algebra.norm ℤ)
    rw [← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne'] at h
    exact (Nat.prime_iff_prime_int.1 Fact.out).not_unit h
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(l : 𝓞 F)}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : (l : 𝓞 F) ∈ P := hle (Ideal.mem_span_singleton_self _)
  exact ⟨⟨P, hP.isPrime, fun h0 => hl (by rw [h0] at hmem; exact hmem)⟩, hmem⟩

end UpperTheory.V.Af
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformAut
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp
open UpperTheory.V.Af
open scoped Matrix

namespace UpperTheory.V.Af.NewformAutomorphy

private theorem ss_of_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep (tw r χ)) : IsSSRep r := by
  have key : ∀ W, IsInv (tw r χ) W ↔ IsInv r W := fun W => by
    constructor
    · intro h g v hv
      have := W.smul_mem ((χ g : k)⁻¹) (h g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
    · intro h g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (h g v hv)
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W ((key W).2 hW)
  exact ⟨W', (key W').1 hW', hc⟩

private theorem ev_not_mem (N : ℕ) (hN : N ≠ 0) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, ((N : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := by
  have h0 : Ideal.span {((N : ℕ) : 𝓞 ℚ)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors h0).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq, not_not] at hw
  exact Ideal.dvd_span_singleton.2 hw

private theorem normV_eq (w : HeightOneSpectrum (𝓞 ℚ)) : normV w = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

private theorem scale_charpoly {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod) :
    M.charpoly.map φ = (B.map fun b => X - C b).prod := by
  have hc' : φ c ≠ 0 := by simpa using hc
  have hcard : B.card = 2 := by
    have h1 := congrArg natDegree h
    rw [natDegree_map, Matrix.charpoly_natDegree_eq_dim] at h1
    have h2 := natDegree_multiset_prod_X_sub_C_eq_card (B.map (φ c * ·))
    rw [Multiset.map_map] at h2
    simp only [Function.comp_def, Multiset.card_map] at h2
    rw [h2] at h1
    simpa using h1.symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_X,
    map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have e0 := congrArg (eval 0) h
  have e1 := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at e0 e1
  have hd : φ M.det = x * y := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hc')
    linear_combination e0
  have ht : φ M.trace = x + y := by
    apply mul_left_cancel₀ hc'
    linear_combination e0 - e1
  rw [hd, ht, C_add, C_mul]
  ring

end UpperTheory.V.Af.NewformAutomorphy

open UpperTheory.V.Af.NewformAutomorphy in
theorem UpperTheory.V.Af.newformAutR :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.NewformAutR := by
  intro P k hk f l hl Ω _ _ _ ι W j hf
  obtain ⟨π, hinf, hsat⟩ := P.newform k hk f (-j)
  refine ⟨π, fun v => ⟨_, hinf v, ?_, ?_⟩, ss_of_tw _ _ hf.1, ?_⟩
  · simp only [Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_singleton, Multiset.nodup_singleton, and_true]
    intro h
    have h1 : (k : ℂ) = 1 := by linear_combination h
    have h2 : k = 1 := by exact_mod_cast h1
    omega
  · intro z hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ⟨-j, by push_cast; ring⟩
    · exact ⟨1 - k - j, by push_cast; ring⟩
  · filter_upwards [hf.2, ev_not_mem l hl.out.ne_zero, ev_not_mem f.M f.pos.ne'] with w hw hwl hwM
    have hM : ¬ normV w ∣ f.M := by
      rintro ⟨c, hc⟩
      apply hwM
      rw [hc, Nat.cast_mul, normV_eq]
      exact w.asIdeal.mul_mem_right _ (Ideal.absNorm_mem _)
    obtain ⟨B, hB, hpoly⟩ := hsat w hM
    refine ⟨B, hB, fun A hA => ⟨fun s hs => ?_, fun σ hσ => ?_⟩⟩
    · have h1 := (hw A hA).1 s hs
      have h2 : cycZ ℚ Ω l s = 1 := by
        refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
        rw [cycZ_toZModPow_eq (v := w) hwl hA (q := 1) (fun x hx => by simpa using hs.2 x hx) n]
        simp
      have h3 : (cycBar ℚ Ω l ^ j) s = 1 := by
        rw [MonoidHom.zpow_apply, cycBar, MonoidHom.comp_apply, h2, map_one, one_zpow]
      apply Units.ext
      have h4 := congrArg Units.val h1
      rwa [tw_val, h3, Units.val_one, one_smul] at h4
    · have h1 := (hw A hA).2 σ hσ
      rw [tw_val, ← hpoly] at h1
      refine scale_charpoly ι.toRingHom _ _ (Units.ne_zero ((cycBar ℚ Ω l ^ j) σ⁻¹)) _ ?_
      rw [h1]
      have h2 : ((cycBar ℚ Ω l σ : (Qbar l)ˣ) : Qbar l) = (normV w : ℕ) := by
        change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])) = _
        rw [cycZ_of_isFrob hwl hA hσ, map_natCast, map_natCast]
      have h3 : ι.toRingHom (((cycBar ℚ Ω l ^ j) σ⁻¹ : (Qbar l)ˣ) : Qbar l) = (normV w : ℂ) ^ (-j) := by
        rw [MonoidHom.zpow_apply, map_inv, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, h2, map_zpow₀,
          map_inv₀, map_natCast, inv_zpow']
      rw [h3]

theorem UpperTheory.V.Af.newformAut :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.NewformAut := by
  intro P k hk f l hl Ω _ _ _ ι W j hf hW K _ _ _ _ _ _ hK hirr
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  exact UpperTheory.V.Sd.upQuad P ℚ K Ω l ι hK 2 one_le_two W hW (UpperTheory.V.Af.newformAutR P k hk f l Ω ι W j hf) hirr
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.NewformRepOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Af.Nf

private theorem liftHol : LiftHol := by
  intro k M hM χ ω hω f hf
  obtain ⟨φ₀, hφ⟩ := liftEx k M hM f fun δ hδ => SlashInvariantForm.slash_action_eqn f δ ⟨δ, hδ, rfl⟩
  obtain ⟨hl, hr, hs⟩ := liftSm k M hM f φ₀ hφ
  let φ : TR.Sm ℚ 2 := ⟨φ₀, hs f.holo'⟩
  have hfix : ∀ u ∈ K1G M, TR.finRep ℚ 2 u φ = φ := fun u hu => Subtype.ext (funext (hr u hu))
  have hlev : IsOpen {u | TR.finRep ℚ 2 u φ = φ} :=
    isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset ((kOpen M hM).1.mem_nhds (one_mem _)) hfix)
  have hc := liftCent k M hM χ ω hω f hf φ₀ hφ
  have hlie := liftLie k M hM f f.holo' φ hφ
  obtain ⟨C, hC⟩ := archBd k M hM f
  have haut : TR.IsAutForm φ := ⟨hl, hlev, liftK k M hM f φ hφ,
    zFin ℚ k ω (charVal M hM χ ω hω).1 φ hc (fun v => (hlie v).1) (fun v => (hlie v).2), fun g => ⟨C, 0, fun y => by
      obtain ⟨γ, h, u, hu, e⟩ := decomp M hM (g * TR.infGL ℚ 2 y)
      rw [pow_zero, mul_one, e]
      change ‖φ₀ _‖ ≤ C
      rw [hφ γ h u hu]
      exact hC _ h.det_ne_zero⟩⟩
  exact ⟨φ, hφ, ⟨haut, fun w u hu => hfix _ (kLocal M hM w u hu), hc, fun v => (hlie v).1, fun v => (hlie v).2⟩,
    haut, cuspCrit φ hl hlev (liftCT k M hM f φ₀ hφ)⟩

private theorem repOf (hS : Published.CuspSemisimpleReal) (hA : Published.AdmissibleReal) : RepOf := by
  intro F _ _ _ k hk1 c ω hω φ hφ h0 hcusp j
  obtain ⟨h1, hcap⟩ := holCap F k c ω hω φ hφ
  obtain ⟨π, ψ, W, hψ, hW, hd, hm⟩ := split F 2 φ h0 (hS F 2 φ hcusp ⟨0, by rw [h1, zero_smul]⟩)
  set s : ℝ := 1 - (k : ℝ) / 2 + j with hs
  let χ := GlobalTheory.HeckeGal.Model.absPow F s
  have hE := GlobalTheory.HeckeGal.Model.absPow_isAbsPow F s
  refine ⟨π.twist χ, fun v => ?_, fun w lam hc he => ?_⟩
  · have hi : π.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)} := by
      refine ⟨rfl, fun u x hx => ?_⟩
      obtain ⟨d, hd'⟩ := TR.Cen.exists_cap_scalar π
      have h2 : TR.cap v u (φ - ψ.1) ∈ W := TR.Zalg_stable (fun X => hW (.lie X)) (Algebra.subset_adjoin ⟨v, u, rfl⟩) _ hm
      set t := (u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)
      have h3 : (t - d v u) • ψ.1 ∈ W := by
        have := W.sub_mem h2 (W.smul_mem t hm)
        rw [map_sub, hcap v u, hd' v u ψ ψ.2] at this
        convert this using 1
        module
      have h4 := (Submodule.disjoint_def.1 hd) _ (π.V.smul_mem _ ψ.2) h3
      have h5 : t = d v u := sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_right fun e => hψ (Subtype.ext e))
      rw [hd' v u x hx, ← h5]
      simp [t, sub_eq_add_neg]
    have := hi.twist χ
    rw [absExpo F s v] at this
    convert this using 1
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, hs]
    exact congrArg₂ (fun a b : ℂ => a ::ₘ {b}) (by push_cast; ring) (by push_cast; ring)
  · obtain ⟨α, β, hv, hsum, hprod⟩ := satHol F k c ω φ hφ h0 w lam hc he
    refine ⟨_, (satOfVec hA F 2 π w ψ _ (satComp F φ π ψ W hψ hW hd hm w _ hv)).twist (χ := χ) (hE.1 w), ?_⟩
    have hq : Ideal.absNorm w.asIdeal = normV w := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    have hq0 : (0 : ℝ) < normV w := by
      rw [← hq]; exact_mod_cast Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot)
    have hval : ((χ.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [hE.2.1 w, hq, Complex.ofReal_cpow hq0.le]; simp
    set r : ℂ := (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr
    have key : ∀ a : ℂˣ, (normV w : ℂ) ^ j * ((((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * ((a * χ.val w : ℂˣ) : ℂ)) =
        r * a := fun a => by
      have : ((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) =
          (normV w : ℝ) ^ j * ((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV w : ℝ) ^ (-s)) := by
        rw [← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
        congr 1
        rw [hs]; push_cast; ring
      rw [hr, this, Units.val_mul, hval]; push_cast; ring
    have hrr : r * r = (normV w : ℂ) ^ (k - 1) := by
      rw [hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]
      push_cast; rfl
    simp only [algSat, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton, Multiset.pure_def, Multiset.bind_def, Multiset.cons_bind, Multiset.singleton_bind,
      Multiset.singleton_add, key]
    rw [← hsum, ← hprod, ← hrr]
    simp only [Units.val_mul, C_mul, C_add]
    ring

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.newformRepOf :
    UpperTheory.V.Published.CuspSemisimpleReal → UpperTheory.V.Published.AdmissibleReal → UpperTheory.V.Published.NewformRep := by
  intro hS hA k hk2 f j
  have hM : 1 ≤ f.M := f.pos
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ω, hω⟩ := dirChar f.M hM f.χ
  obtain ⟨hfin, hval⟩ := charVal f.M hM f.χ ω hω
  obtain ⟨φ, hL, hH, hC⟩ := liftHol k f.M hM f.χ ω hω f.f f.char
  have hE := liftExp k f.M hM f.f φ.1 hL
  obtain ⟨-, hz, hl1, hl2, -⟩ := holLin ℚ k (lev f.M) ω
  have h0 : φ ≠ 0 := by
    rintro rfl
    have := (expUnique ℚ _ k _ _ _ _ hE hz).2 ⊤ top_ne_bot
    rw [icoef, Ideal.absNorm_top, f.one] at this
    exact one_ne_zero this
  obtain ⟨π, hi, hs⟩ := repOf hS hA ℚ k hk1 _ ω hfin φ hH h0 hC j
  refine ⟨π, hi, fun w hw => ?_⟩
  have hc := (places w).2.2.2 f.M hM hw
  obtain ⟨h1, -, h2⟩ := holHk ℚ k hk1 _ ω hfin φ hH w
  obtain ⟨c₀, h3⟩ := h2 _ _ hE
  have h4 := expInj ℚ k hk1 _ ω hfin _ (hl1 _ _ (-f.a (normV w)) h1 hH) _ _ (hl2 _ _ (-f.a (normV w)) _ _ _ _ h3 hE)
    fun 𝔪 h𝔪 => by simp [hkCoef k f ω w hw (hval w hw) 𝔪 h𝔪]
  rw [hc, neg_smul, add_neg_eq_zero] at h4
  obtain ⟨B, hB, e⟩ := hs w _ hc h4
  exact ⟨B, hB, by rw [e, hval w hw, Newform.heckePoly]⟩
end

