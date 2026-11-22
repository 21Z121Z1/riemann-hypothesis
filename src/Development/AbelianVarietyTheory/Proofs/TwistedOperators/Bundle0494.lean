import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0487
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
import GroundTheory.GlobalFields.TateThesis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0488
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0456
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftLowestKTypeCompatibility
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaProjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem eq_zero_of_no_lift (R : RealDat D A Ks) (hW : R.models_HW) (hg : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ)
    (g : G) (hn : ¬ ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ) (x : (R.HW i σ).H) : x = 0 := by
  have hL : actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) = 0 := by
    ext F h
    show actG0 _ _ _ _ F h = 0
    rw [GlobalTheory.ProjComm.levelGroupAction_eq_zero_of_no_lift hn F]
    rfl
  have h1 : (R.HW i σ).e (R.gW i σ g x) = 0 := by
    rw [hg i σ g x, hL]
    ext v h
    rfl
  have h2 : R.gW i σ g x = 0 := (hW i σ).1 (by rw [h1, map_zero])
  have h3 := congrArg (R.gW i σ g⁻¹) h2
  rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at h3

theorem realDatum_coeffFlagLevelCharacter_eq_one (R : RealDat D A Ks) (i : Fin D.R.m) (κ : GA D (Wc D i)) :
    levChi (Wc D i) (R.βW i) (flagL (R.datWp i R.triv)) κ = 1 := by
  classical
  unfold levChi Formalism.L2.DIV.levFn
  simp [flagL, withP, LevCh.datWp, datY, Formalism.L2.DIV.ext1, Formalism.L2.DIV.LevelP.full]
  exact dite_eq_right_iff.mpr fun _ => rfl

theorem left_abs {H Gf W : Type} [Group H] [Group Gf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (Γ : Subgroup H)
    (p : H →* Gf) (ρ : H →* Module.End ℂ W) (f : Gf → W) (J : Subgroup Gf) (χ : J →* ℂˣ)
    (hy : f ∈ Bridge.AdForms (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) (γ : H) (hγ : γ ∈ Γ) (h : H) :
    ρ (γ * h)⁻¹ (f (p (γ * h))) = ρ h⁻¹ (f (p h)) := by
  have h1 : f (p γ * p h) = ρ γ (f (p h)) := by
    have h0 : f (p γ * p h * 1) = ((χ 1 : ℂˣ) : ℂ) • ρ γ (f (p h)) := hy ⟨γ, hγ⟩ (p h) 1
    simpa using h0
  rw [map_mul p, h1, mul_inv_rev, map_mul ρ, Module.End.mul_apply, ← Module.End.mul_apply (ρ γ⁻¹), ← map_mul ρ,
    inv_mul_cancel, map_one, Module.End.one_apply]

theorem shift_abs {H Gf W : Type} [Group H] [Group Gf] [AddCommGroup W] [Module ℂ W]
    (p : H →* Gf) (ρ : H →* Module.End ℂ W) (κ : H) (hκ : ρ κ⁻¹ = 1) (a : ℂ) (ha : a ≠ 0) (f f' : Gf → W)
    (hy : ∀ h, f' h = a⁻¹ • f (h * p κ)) (h : H) :
    ρ h⁻¹ ((a • f') (p h)) = ρ (h * κ)⁻¹ (f (p (h * κ))) := by
  rw [Pi.smul_apply, hy, smul_smul, mul_inv_cancel₀ ha, one_smul, map_mul p, mul_inv_rev, map_mul ρ,
    Module.End.mul_apply, hκ, Module.End.one_apply]

theorem ext_left {V : HSp D} (c : CoefA V) (f : Bridge.Gf V → c.W) (J : Subgroup (Bridge.Gf V)) (χ : J →* ℂˣ)
    (hy : f ∈ Bridge.AdForms (W := c.W) (Bridge.ratF V) (c.ρ.comp (GQ V).subtype) J χ)
    (γ : GA D V) (hγ : γ ∈ GQ V) (h : GA D V) : c.ext f (γ * h) = c.ext f h := by
  show c.ρ (γ * h)⁻¹ (f ((finHom V).rangeRestrict (γ * h))) = c.ρ h⁻¹ (f ((finHom V).rangeRestrict h))
  exact left_abs (GQ V) (finHom V).rangeRestrict c.ρ f J χ hy γ hγ h

theorem ext_shift {V : HSp D} (c : CoefA V) (hc : c.Is) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0)
    (f f' : Bridge.Gf V → c.W) (hy : ∀ h, f' h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (h : GA D V) :
    c.ext (a • f') h = c.ext f (h * κ) := by
  show c.ρ h⁻¹ ((a • f') ((finHom V).rangeRestrict h)) = c.ρ (h * κ)⁻¹ (f ((finHom V).rangeRestrict (h * κ)))
  exact shift_abs (finHom V).rangeRestrict c.ρ κ (hc.1 _ (inv_mem hκ)) a ha f f' hy h

theorem extV_left (R : RealDat D A Ks) (hV : R.models_HV) (i : Fin D.R.m) (t : T0) (y : (R.HV i t).H)
    (γ : GA D (Vc D i)) (hγ : γ ∈ GQ (Vc D i)) (h : GA D (Vc D i)) : R.extV i t y (γ * h) = R.extV i t y h := by
  have h3 := LinearMap.mem_range_self (R.HV i t).e y
  rw [(hV i t).2.1] at h3
  show (R.cV i).ext ((R.HV i t).e y) (γ * h) = (R.cV i).ext ((R.HV i t).e y) h
  exact ext_left (R.cV i) _ _ _ h3 γ hγ h

theorem extV_shift (R : RealDat D A Ks) (hc : R.models_cV) (i : Fin D.R.m) (t : T0) (κ : GA D (Vc D i))
    (hκ : κ ∈ GfC (Vc D i)) (c : ℂ) (hc0 : c ≠ 0) (y y' : (R.HV i t).H)
    (hy : ∀ h, (R.HV i t).e y' h = c⁻¹ • (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ)) (h : GA D (Vc D i)) :
    R.extV i t (c • y') h = R.extV i t y (h * κ) := by
  show (R.cV i).ext ((R.HV i t).e (c • y')) h = (R.cV i).ext ((R.HV i t).e y) (h * κ)
  rw [map_smul]
  exact ext_shift (R.cV i) (hc i) κ hκ c hc0 _ _ hy h

theorem integral_shift (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (g0 : G0 L.Pg L.r)
    (κ : GA D V) (hκ : IsLevelLift V β L g0 κ) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (𝓕 : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) 𝓕 ν) (f : GA D V → ℂ) (hf : ∀ γ ∈ GQ V, ∀ h, f (γ * h) = f h)
    (hi : IntegrableOn f 𝓕 ν) : ∫ h in 𝓕, f (h * κ) ∂ν = ∫ h in 𝓕, f h ∂ν := by
  obtain ⟨htg, hlc, hsc, -, hbo, -⟩ := GlobalTheory.Ker.CongTop.adelicUnitary_top_cong D V
  obtain ⟨-, -, -, hct⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable V
  obtain ⟨hK, hlift⟩ := GlobalTheory.ParahoricCompact.isCompact_flag_and_lift V β L
  haveI := htg
  haveI := hlc
  haveI := hsc
  haveI := hbo
  haveI := hct
  haveI := hν
  have hmap := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup ν _ hK κ (hlift g0 κ hκ)
  exact (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) ν 𝓕 hfd κ hmap f hf hi).2

theorem thetaLift_shift {G' H' S' Sinf TK Tau : Type} [Group G'] [Group H'] [MeasurableSpace H']
    [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
    {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Sinf → S'} {io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf}
    {B : Submodule ℂ (H' → Tau)} {thP : B →ₗ[ℂ] (TK →ₗ[ℂ] (G' → ℂ))} (hP : Lift.IsThetaP ν 𝓕 th pt io B thP)
    (Γ : Subgroup H') (k : H') (k' : G') (c : ℂ) (hc : c ≠ 0)
    (hsh : ∀ f : H' → ℂ, (∀ γ ∈ Γ, ∀ h, f (γ * h) = f h) → IntegrableOn f 𝓕 ν →
      ∫ h in 𝓕, f (h * k) ∂ν = ∫ h in 𝓕, f h ∂ν)
    (hl : ∀ P, ∀ γ ∈ Γ, ∀ g h, th g (γ * h) (pt P) = th g h (pt P))
    (hr : ∀ P g h, th (g * k') (h * k) (pt P) = c⁻¹ * th g h (pt P))
    (f f' : B) (hf : ∀ γ ∈ Γ, ∀ h, (f : H' → Tau) (γ * h) = (f : H' → Tau) h)
    (hf' : ∀ h, ((c • f' : B) : H' → Tau) h = (f : H' → Tau) (h * k)) (e : TK) (g : G') :
    thP f' e g = thP f e (g * k') := by
  have hA : thP f e (g * k') = ∫ h in 𝓕, th (g * k') h (pt (io e ((f : H' → Tau) h))) ∂ν :=
    hP.eq f e (g * k')
  have hB : thP (c • f') e g = ∫ h in 𝓕, th g h (pt (io e (((c • f' : B) : H' → Tau) h))) ∂ν :=
    hP.eq (c • f') e g
  have hF := hsh (fun h => th (g * k') h (pt (io e ((f : H' → Tau) h))))
    (fun γ hγ h => by
      rw [hf γ hγ h]
      exact hl _ γ hγ _ _)
    (hP.integ f e (g * k'))
  rw [hA, ← hF]
  simp only [hr]
  rw [integral_const_mul]
  have hfk : ∀ h, (f : H' → Tau) (h * k) = ((c • f' : B) : H' → Tau) h := fun h => (hf' h).symm
  simp only [hfk]
  rw [← hB, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem thF_type (R : RealDat D A Ks) (hm : R.thP_thF_mem) (i : Fin D.R.m) (t : T0) (y : (R.HV i t).H)
    (v : (R.MW i (sg0 D A)).Vec) : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) (R.thF i t y v) := by
  intro κ hκ h
  have hmem : R.thF i t y ∈ Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) := hm i t y
  exact (GlobalTheory.mult_value_left_cont_level R.θ _ _ _ _ hmem v).2.2 κ hκ h

theorem finiteGroup_acts_by_lift_translation_principalType (R : RealDat D A Ks) (i : Fin D.R.m) (g0 : G0 R.Pg D.R.r) (κ' : GA D (Wc D i))
    (hκ' : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ') (f : GA D (Wc D i) → ℂ)
    (hT : HasType (Wc D i) (R.βW i) (R.datWp i R.triv) f) (x : GA D (Wc D i)) :
    actL (Wc D i) (R.βW i) (R.datWp i R.triv) g0 f x = f (x * κ') := by
  have hex : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) g0 κ := ⟨κ', hκ'⟩
  have hchi : ∀ k, levChi (Wc D i) (R.βW i) (R.datWp i R.triv) k = 1 := by
    intro k
    classical
    unfold levChi Formalism.L2.DIV.levFn
    simp [LevCh.datWp, datY, Formalism.L2.DIV.ext1, Formalism.L2.DIV.LevelP.triv]
    exact dite_eq_right_iff.mpr fun _ => rfl
  have hmem := lift_div_mem hκ' hex.choose_spec
  have hfl : flag1L (R.datWp i R.triv) = R.datWp i R.triv := rfl
  rw [hfl] at hmem
  have hx := hT _ hmem (x * κ')
  rw [hchi, one_mul, ← mul_assoc, mul_inv_cancel_right] at hx
  show actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) g0 f x = f (x * κ')
  unfold actG0
  rw [dif_pos hex, realDatum_coeffFlagLevelCharacter_eq_one, inv_one, one_mul]
  exact hx

end GlobalTheory.ThetaProjEquiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerTowerLiftsVanishOnFock
section
noncomputable section

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowerMembersRule

section Local

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin)
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix GlobalTheory.Chain.RealIt.LocalFromCover

theorem nodup_of_isParam {p q : ℕ} {l₁ l₂ : List ℚ} (h1 : l₁.length = p) (h2 : l₂.length = q)
    (h : IsParam (ofBlocks l₁ l₂ : Ix p q → ℚ)) : l₁.Nodup ∧ l₂.Nodup := by
  subst h1 h2
  refine ⟨List.nodup_iff_injective_get.2 fun i j hij => ?_, List.nodup_iff_injective_get.2 fun i j hij => ?_⟩
  · have := @h.1 (.inl i) (.inl j) (by simpa [ofBlocks, List.getD_eq_getElem] using hij)
    simpa using this
  · have := @h.1 (.inr i) (.inr j) (by simpa [ofBlocks, List.getD_eq_getElem] using hij)
    simpa using this

theorem pairing_eq_zero : ∀ (X : ProvA) (p q r s : ℕ) (lam' : Ix r s → ℚ), Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s lam').HK →
    GlobalTheory.PairLift.NoLow X p q lam' → ∀ i : ℕ, 1 ≤ i → i ≤ p → i ≤ q →
    ∀ (D : D7) (V W : HSp D) (S' : D.what₂.Tau → SPar) (M' : DSModel W S') (τ : D.what₂.Tau) (ε : Fin V.rank → Bool)
    (e : Ix (p - i) (q - i) ≃ Fin V.rank) (e' : Ix r s ≃ Fin W.rank) (m' : ℤ) (aS : ℚ)
    (U' : M'.H τ ≃ₗᵢ⋆[ℂ] (X.ds r s lam').U.H) (a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ))
    (b : LPol W.rank V.rank →ₗ[ℂ] kFin M' τ →ₗ[ℂ] ℂ), SignCompat ε e → SignCompat (M'.ε τ) e' → (m' : ℚ) = 2 * aS →
    Matches (X.ds r s lam') M' τ (plainMat e') m' U' → GlobalTheory.Chain.IoLift.IsKAct M' τ a' →
    (∀ Y ∈ lieAt W τ, ∀ P y, b (locT ε (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) P + ((aS : ℂ) * Y.trace) • P) y +
      b P (a' Y y) = 0) → b = 0 := by
  intro X p q r s lam' hadm hlow i hi hip hiq D V W S' M' τ ε e e' m' aS U' a' b he he' hm' h₂ ha hb
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_fockPolynomialIso_unitaryPair _ _ _ _ _ _ ε (M'.ε τ) e e' he he'
  have hmC' : (m' : ℂ) = 2 * (aS : ℂ) := by exact_mod_cast hm'
  have hmem : ∀ v, U'.symm ((X.ds r s lam').ι v) ∈ kFin M' τ := fun v =>
    (h₂.kfin _).2 ⟨v, (U'.apply_symm_apply _).symm⟩
  let j : (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] kFin M' τ :=
    { toFun := fun v => ⟨U'.symm ((X.ds r s lam').ι v), hmem v⟩
      map_add' := fun v w => Subtype.ext (by simp)
      map_smul' := fun c v => Subtype.ext (by simp [LinearIsometryEquiv.map_smulₛₗ]) }
  have hj : ∀ v, U' (j v : M'.H τ) = (X.ds r s lam').ι v := fun v => U'.apply_symm_apply _
  have hsurj : Function.Surjective j := fun y => by
    obtain ⟨v, hv⟩ := (h₂.kfin y).1 y.2
    exact ⟨v, Subtype.ext (U'.injective (by rw [hj, hv]))⟩
  let B' : Pol _ _ _ _ →ₗ[ℂ] (X.ds r s lam').HK.V →ₛₗ[starRingEnd ℂ] ℂ :=
    { toFun := fun P => (b (κ.symm P)).comp j
      map_add' := fun P Q => by ext v; simp
      map_smul' := fun c P => by ext v; simp }
  have hB' : ∀ P v, B' (κ P) v = b P (j v) := fun P v => by simp [B']
  have h0 : B' = 0 := GlobalTheory.T.no_invariant_pairing_smaller_fock_discreteSeries X p q r s lam' hadm hlow i hi hip hiq B' (fun Y hY P y => by
    obtain ⟨P, rfl⟩ := κ.surjective P
    have hY' : toFrame M' τ (plainMat e' Y) ∈ lieAt W τ := h₂.lie ▸ ⟨Y, hY, rfl⟩
    have h4 : (plainMat e' Y).trace = Y.trace := trace_reindex' e' Y
    have h6 : a' (toFrame M' τ (plainMat e' Y)) (j y) = j ((X.ds r s lam').HK.act Y y) -
        ((aS : ℂ) * Y.trace) • j y := by
      have h7 : a' (toFrame M' τ (plainMat e' Y)) (j y) =
          j ((X.ds r s lam').HK.act Y y + ((m' : ℂ) / 2 * Y.trace) • y) := by
        refine Subtype.ext (U'.injective ?_)
        rw [hj, ← h₂.der Y hY y _ (hj y), dRep, (ha.der _ hY' (j y)).deriv]
      rw [h7, map_add, LinearMap.map_smulₛₗ, map_mul, map_div₀, map_intCast, map_ofNat, trace_conj hY, hmC',
        sub_eq_add_neg, ← neg_smul]
      congr 2
      ring
    have h := hb _ hY' P (j y)
    rw [h6, fr_toFrame, trace_toFrame, h4] at h
    rw [← hκ.2, hB', hB', ← h]
    simp [plainMat])
  refine LinearMap.ext fun P => LinearMap.ext fun z => ?_
  obtain ⟨v, rfl⟩ := hsurj z
  rw [← hB', h0]
  rfl

end Local

section Global

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.ChainFr GlobalTheory.Chain.IoLift GlobalTheory.Chain.IoLift.FockOrbit GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension (kFin KVec maxCpt)
open GlobalTheory.LowerMembers (frame_fock_orbit signCard_signed ptF_zero)
open scoped TensorProduct InnerProductSpace

set_option maxHeartbeats 1000000 in

theorem lowFock : ∀ (D : D7) (X : ProvA), GlobalTheory.PairLift.Inputs D X → GlobalTheory.PairLift.LowFock D X := by
  classical
  intro D X hIn
  have hTB := hIn.bridge.2
  intro S S' aS aT hP i V' W M' θ ψ hθ hi hs ω' hω ν 𝓕 hν h𝓕 F hF v A f₀ hf P
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  by_cases f0 : f₀ = 0
  · subst f0
    funext g
    simp [Lift.liftInt, thetaKO, ptF_zero]

  have tgt : ∀ τ, ∃ a' : Matrix (Fin W.rank) (Fin W.rank) ℂ → Module.End ℂ (kFin M' τ),
      kFin M' τ ≤ M'.sm τ ∧ IsKAct M' τ a' := fun τ => by
    obtain ⟨p, q, r, s, l₁, l₂, l₁', l₂', -, -, h3, h4, hR, -, e2⟩ := hP τ
    obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W S' M' τ r s l₁' l₂' (aS τ)
      ⟨hR.pos', h3, h4, hR.par', hIn.chosen _ _ _ hR.par', e2⟩
    obtain ⟨U', hU'⟩ := hU' e' he'
    obtain ⟨hsm, a', ha'⟩ := GlobalTheory.Chain.IoLift.kFin_smooth_isKAct D W _ M' τ _ _ _ _ _ _ _ hU'
    exact ⟨a', hsm, ha'⟩
  choose a' hsm ha' using tgt
  have h' : KSm M' := hsm
  have hMF : IsMultMap θ M' ∅ 1 (PiTensorProduct.lift.symm F) :=
    (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hF)
  have hM : ∀ F' : MultT θ M' ∅ 1, IsMultMap θ M' ∅ 1 (PiTensorProduct.lift.symm (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ))) :=
    fun F' => (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 F'.2)
  let pt : PolF D W.rank V'.rank →ₗ[ℂ] (WO V' W → ℂ) :=
    pureTensorO ψ θ V' W A.cart (Fr.ofModel M').cart A.onb (Fr.ofModel M').onb f₀
  have hp : ptF ψ θ A (Fr.ofModel M') f₀ = pt := rfl
  have hpt : ∀ φ, IsThetaFunO ψ V' W (pt φ) := fun φ =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hW.std hθ _ _ _ _ hf.1 φ
  have L := hIn.laws V' W θ ψ χS χT ω' hθ hW ν 𝓕 hν h𝓕
  have hint : ∀ F' : MultT θ M' ∅ 1, ∀ φ x g, IntegrableOn
      (fun h => thetaKO ω' g h (pt φ) * (F' : SmT M' →ₗ[ℂ] (GA D W → ℂ)) x h) 𝓕 ν := fun F' φ x g => by
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r w =>
      have := (L.integ _ _ (hpt φ) ⟨(hM F').aut w, (hM F').cusp w⟩ g 1).const_mul r
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      beta_reduce
      rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm, rTr, mul_one]
      rfl
    | add x y hx hy => simp only [map_add, Pi.add_apply, mul_add]; exact hx.add hy
  obtain ⟨B, hB⟩ := exists_trilinear ν 𝓕 (fun g h => LinearMap.proj 0 ∘ₗ ω' (g, h)) pt (MultT θ M' ∅ 1) hint
  let G : PolF D W.rank V'.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] (GA D V' → ℂ) :=
    B.compr₂ (LinearMap.applyₗ (⟨F, hF⟩ : MultT θ M' ∅ 1))
  have hG : ∀ φ x, G φ x = GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) (F x) := fun φ x => hB φ x ⟨F, hF⟩
  have hcl : ∀ w : M'.Vec, IsAutFunSm θ W (F (PiTensorProduct.tprod ℂ w)) ∧
      IsCuspFun W (F (PiTensorProduct.tprod ℂ w)) := fun w => ⟨hMF.aut w, hMF.cusp w⟩

  have hT : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ z, HasDerivAt (fun t : ℝ => ω' (1, oneP θ W τ Y t) (pt φ) z)
      (pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ) z) 0 :=
    fun τ Y hY φ z => (hIn.lie V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ (aS τ) (aT τ) hθ hW
      (hexp τ).1 (hexp τ).2 hf).2 Y hY φ z
  have hBt : ∀ τ, ∀ Y ∈ lieAt W τ, ∀ φ (w : M'.Vec) (u : M'.sm τ), (u : M'.H τ) = dRep (M'.rep τ) Y (w τ) →
      G (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ)
        (PiTensorProduct.tprod ℂ w) + G φ (PiTensorProduct.tprod ℂ (Function.update w τ u)) = 0 := by
    intro τ Y hY φ w u hu
    have e1 := GlobalTheory.MultGelf.rder_apply hMF τ w hY (w τ) u hu
    rw [Function.update_eq_self] at e1
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.dOmT θ ω' τ Y (pt φ) =
        pt (fockT τ (A.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) φ + ((aS τ : ℂ) * Y.trace) • φ) :=
      funext fun z => (hT τ Y hY φ z).deriv
    funext g
    have := L.derT_add (hpt φ) (hcl w) τ hY g
    rw [e2, add_comm] at this
    rw [Pi.add_apply, hG, hG]
    exact (congrArg (fun A => _ + GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift.lift ω' ν 𝓕 (pt φ) A g) e1).symm.trans this

  have hav := mem_span_of_average G h' fun τ φ w => by
    obtain ⟨n, φs, c, hc, hφ⟩ := frame_fock_orbit D V' W _ A M' θ ψ ω' f₀ τ (aS τ) (aT τ) hθ
      (hIn.cpt V' W A (Fr.ofModel M') θ ψ χS χT ω' f₀ τ _ _ hθ hW (hexp τ).1 (hexp τ).2 hf f0) φ
    have hk := GlobalTheory.Chain.IoLift.kMean_mem_kFin_of_coefFam D W _ M' τ n c hc (w τ)
    refine ⟨n, φs, fun i => ⟨_, h' τ (hk i)⟩, hk, ?_⟩
    funext g
    simp only [hG, Finset.sum_apply]
    exact GlobalTheory.Chain.IoLift.AvgLift.liftInt_eq_sum_average D V' W _ M' θ ψ χS χT ω' ν 𝓕 hθ hW hν h𝓕 τ n c _ _ _ _
      hc.1 (hpt φ) hφ (hcl w).1.toIsAutFun (fun i x => apply_kMean hMF τ (hc.1 i) w _ rfl x) g
      (hint ⟨F, hF⟩ _ _ g) fun i => hint ⟨F, hF⟩ _ _ g

  obtain ⟨τ₀⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  obtain ⟨p, q, r, s, l₁, l₂, l₁', l₂', h1, h2, h3, h4, hR, e1, e2⟩ := hP τ₀
  obtain ⟨p', q', hp', hq', hsig⟩ := hs τ₀
  obtain ⟨hn1, hn2⟩ := nodup_of_isParam h1 h2 hR.par
  have hcard := signCard_signed l₁ l₂ (aT τ₀) hn1 hn2
  rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.1, h1] at hp'
  rw [e1, GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.signCard_dualPar, hcard.2, h2] at hq'
  obtain rfl : p' = p - i := by omega
  obtain rfl : q' = q - i := by omega
  obtain ⟨e, he⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V').2 A τ₀ _ _ hsig
  obtain ⟨⟨e', he'⟩, m', hm', hU'⟩ := hTB X W S' M' τ₀ r s l₁' l₂' (aS τ₀)
    ⟨hR.pos', h3, h4, hR.par', hIn.chosen _ _ _ hR.par', e2⟩
  obtain ⟨U', hU'⟩ := hU' e' he'
  have hadm : Formalism.MainNotions.SchurIrreducible.AdmGK (X.ds r s (ofBlocks l₁' l₂')).HK :=
    (((hIn.hc.admQ5_of_harishChandraModules X _ _ hR.pos').1 (X.ds r s (ofBlocks l₁' l₂')).U
      ⟨(X.ds _ _ _).nontriv, (X.ds _ _ _).irred⟩).2.2 _ (X.ds _ _ _).ι
      ⟨(X.ds _ _ _).ι_inj, (X.ds _ _ _).ι_range, (X.ds _ _ _).der⟩).1
  have kvan : ∀ φ (y : KT M'), G φ (inclK h' y) = 0 := by
    have hz := span_multi (G.compl₂ (inclK h')) fun p y => by
      funext g
      let b := slice (multi ((G.compl₂ (inclK h')).compr₂ (LinearMap.proj g))) τ₀ p y
      have hb0 := pairing_eq_zero X _ _ r s (ofBlocks l₁' l₂') hadm hR.low i hi (by omega) (by omega) D V' W _ M' τ₀
        (A.ε τ₀) e e' m' (aS τ₀) U' (a' τ₀) b he he' hm' hU' (ha' τ₀) (fun Y hY Q z => by
          simp only [b, slice_apply, multi_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
            LinearMap.proj_apply]
          have eq1 : glue (Function.update p τ₀ (locT (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) Q +
              ((aS τ₀ : ℂ) * Y.trace) • Q)) =
              fockT τ₀ (A.ε τ₀) (M'.ε τ₀) (M'.fr τ₀ * Y * (M'.fr τ₀)⁻¹) (glue (Function.update p τ₀ Q)) +
                ((aS τ₀ : ℂ) * Y.trace) • glue (Function.update p τ₀ Q) := by
            rw [((GlobalTheory.T.gluing_law_holds D V'.rank W.rank).2 τ₀ _ _ _).2, Function.update_idem, Function.update_self]
            simp only [← glueM_apply, MultilinearMap.map_update_add, MultilinearMap.map_update_smul]
          have eq2 : Function.update y τ₀ (a' τ₀ Y z) = Function.update (Function.update y τ₀ z) τ₀
              (a' τ₀ Y (Function.update y τ₀ z τ₀)) := by
            rw [Function.update_idem, Function.update_self]
          rw [eq1, eq2, inclK_tprod h' (Function.update y τ₀ z), inclK_update h' (Function.update y τ₀ z) τ₀]
          refine congrFun (hBt τ₀ Y hY _ _ _ ?_) g
          exact ((ha' τ₀).der Y hY _).deriv.symm)
      have := LinearMap.congr_fun₂ hb0 (p τ₀) (y τ₀)
      simpa [b, slice_apply, multi_apply, Function.update_eq_self] using this
    exact fun φ y => LinearMap.congr_fun₂ hz φ y
  have h0 : G P v ∈ (⊥ : Submodule ℂ (GA D V' → ℂ)) :=
    Submodule.span_le.2 (by rintro _ ⟨φ, y, rfl⟩; simp [kvan φ y]) (hav P v)
  rw [Submodule.mem_bot, hG] at h0
  rw [hp]
  exact h0

end Global

end GlobalTheory.LowerMembersRule

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamIsometryFamiliesDifferByCharacter
section
open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

namespace GlobalTheory

theorem famChar_hasDerivAt : ∀ (l : Type) [Fintype l] (B : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (T U : ℝ → Sch l →ₗ[ℂ] Sch l) (Q : Sch l → EuclideanSpace ℝ l → ℂ), (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) → (∀ s t f, U (s + t) f = U s (U t f)) → (∀ f, U 0 f = f) → (∀ s t w, B (s + t) w = B s (B t w)) → (∀ w, B 0 w = w) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (B t w) ⇑(T t f)) → (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (B t w) ⇑(U t f)) → (∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T t f y) → (∀ f y, HasDerivAt (fun t => U t f y) (Q f y) 0) → ∃ c : ℂ, ∀ f y, HasDerivAt (fun t => T t f y) (Q f y + c * f y) 0 := by
  intro l _ B T U Q hT hT0 hU hU0 hB hB0 hTρ hUρ hTi hUi hTc hUd
  have hUinv : ∀ t f, U (-t) (U t f) = f := fun t f => by rw [← hU, neg_add_cancel, hU0]
  have hUinv' : ∀ t f, U t (U (-t) f) = f := fun t f => by rw [← hU, add_neg_cancel, hU0]

  have key : ∀ t, ∃ c : ℂ, ∀ f, T t f = c • U t f := by
    intro t
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_scalar_of_commute_schrodingerOperators l ((T t).comp (U (-t)))
      (fun f => by simp only [LinearMap.comp_apply]; rw [hTi, hUi])
      (fun w f f₁ h => by
        simp only [LinearMap.comp_apply]
        rw [hTρ t (B (-t) w) (U (-t) f) (U (-t) f₁) (hUρ (-t) w f f₁ h), ← hB, add_neg_cancel, hB0])
    refine ⟨c, fun f => ?_⟩
    have := hc (U t f)
    simp only [LinearMap.comp_apply, hUinv] at this
    exact this
  choose lam hlam using key
  set f₀ : Sch l := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ l)
  have hf₀ : f₀ 0 ≠ 0 := by simp [f₀]

  have hl0 : lam 0 = 1 := by
    have h := hlam 0 f₀
    rw [hT0, hU0] at h
    have h2 := congrArg (fun g : Sch l => g 0) h
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam 0 - 1) * f₀ 0 = 0 := by linear_combination -h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)
  have hlmul : ∀ s t, lam (s + t) = lam s * lam t := by
    intro s t
    have h1 := hlam (s + t) (U (-(s + t)) f₀)
    rw [hUinv', hT, hlam t, map_smul, hlam s, ← hU, hUinv', smul_smul] at h1
    have h2 := congrArg (fun g : Sch l => g 0) h1
    simp only [SchwartzMap.smul_apply, smul_eq_mul] at h2
    have : (lam s * lam t - lam (s + t)) * f₀ 0 = 0 := by linear_combination h2
    exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hf₀)).symm

  have hd : ContinuousAt (fun t => U t f₀ 0) 0 := (hUd f₀ 0).continuousAt
  have hd0 : U 0 f₀ 0 ≠ 0 := by rw [hU0]; exact hf₀
  have hlc : ContinuousAt lam 0 := by
    have hq : ContinuousAt (fun t => T t f₀ 0 / U t f₀ 0) 0 :=
      ((hTc f₀ 0).continuousAt).div hd hd0
    refine hq.congr ?_
    filter_upwards [hd.eventually_ne hd0] with t ht
    rw [hlam t f₀, SchwartzMap.smul_apply, smul_eq_mul, mul_div_assoc, div_self ht, mul_one]

  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_hasDerivAt_zero_of_continuousAt_of_map_add lam hl0 hlmul hlc
  refine ⟨c, fun f y => ?_⟩
  have hfun : (fun t => T t f y) = fun t => lam t * U t f y := by
    funext t; rw [hlam t f, SchwartzMap.smul_apply, smul_eq_mul]
  rw [hfun]
  have h := hc.mul (hUd f y)
  rw [hl0, hU0, one_mul, add_comm] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaVacuumCharactersRealPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaVacuumCharacters_realPlaces : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.VacChar D := by
  first | exact @GlobalTheory.VacuumCharacter.vacChar | exact GlobalTheory.VacuumCharacter.vacChar | (intros; apply GlobalTheory.VacuumCharacter.vacChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TruncationFamilyLeviShiftStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncation_family_levi_shift : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ P, IsPar P → ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∃ h : A0 (wittIndex V), ∀ Q ∈ parP (aP P) ∅, ∀ x Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (m * x) Tr Q = Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q + pr Q h := by
  first | exact @GlobalTheory.LeviShift.yfam_mul_levi | exact GlobalTheory.LeviShift.yfam_mul_levi | (intros; apply GlobalTheory.LeviShift.yfam_mul_levi <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypePlacesOverNormAndCoverWithConjugatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_over_norm_and_cover_with_conjugates : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → (∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) ∧ ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ PP ∈ R.Pg, Q = PP ∨ Q = GlobalTheory.IdemSupport.cP PP := by
  first | exact @GlobalTheory.SeeConjRead.places_over_g | exact GlobalTheory.SeeConjRead.places_over_g | (intros; apply GlobalTheory.SeeConjRead.places_over_g <;> assumption)
end

