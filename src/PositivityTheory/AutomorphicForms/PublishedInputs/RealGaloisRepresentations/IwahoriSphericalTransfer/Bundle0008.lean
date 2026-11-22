import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0006
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0005
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0034
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ImportsSide
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AwayDescent

theorem main : GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (P : CuspSub K a), IsBC π P → ∀ (χ : HChar (maximalRealSubfield K)) (r : G F Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (K →+* Qbar l) → Multiset ℤ), IsGalRepOf P χ ι (r.comp (res F Ω K)) wt HT → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : IsPlaceOver A v), Dec (F := F) A ≤ (res F Ω K).range → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → (∀ (rc : IrrGL (v.adicCompletion F) → WD h), IsRec h rc → ∀ σ, π.IsLocComp v σ → IsWDOf ι r (rc (algNorm σ))) ∧ ∃ x : WD h, IsWDOf ι r x ∧ (x.lpTw ((wt : ℝ) / 2)).tempered := by
  intro L F Ω _ _ _ _ _ _ K _ _ _ _ _ _ _ l _ ι a π P hBC χ r wt HT hG v A h hdec hl
  obtain ⟨w, h', i, hi⟩ := GlobalTheory.T.exists_place_completion_iso F Ω K v A h hdec
  have hlw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := by
    intro hw
    apply hl
    have e1 := (h ((l : ℕ) : 𝓞 F))
    have e2 := (h' ((l : ℕ) : 𝓞 K))
    simp only [map_natCast] at e1 e2
    exact e1.1 (e2.2 hw)
  have hL : GlobalTheory.Published.LocalLanglandsGL :=
    GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein L.loc.llc L.loc.conv L.loc.dzc L.loc.dzi
      L.loc.brauer L.loc.chev L.aut.art L.loc.exh L.loc.multi L.loc.cos L.loc.zel L.loc.geo L.loc.bz
  refine ⟨fun rc hrc σ hσ => ?_, ?_⟩
  · obtain ⟨⟨σ', hσ'⟩, -⟩ := GlobalTheory.T.local_global_compatibility_complex L K a P w
    obtain ⟨rc', hrc', -⟩ := hL.1 K Ω A w h'
    obtain ⟨e, he⟩ := hBC.split v w i hi.cont hi.loc σ σ' hσ hσ'
    have hx' := hG.away w hlw A h' rc' hrc' σ' hσ'
    obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi _ hx'
    rwa [← UpperTheory.V.Af.Cq.recTransport hL F K Ω A v w h h' _ i hi a σ σ' e he rc rc' hrc hrc' x hxx]
  · obtain ⟨x', hx', ht⟩ := hG.pure w hlw A h'
    obtain ⟨x, hx, hxx⟩ := GlobalTheory.T.galois_rep_restriction_local_completion F Ω K l ι a r A v w h h' i hi x' hx'
    exact ⟨x, hx, GlobalTheory.TemperedTransport.main F Ω K A v w h h' (algebraMap F K) i hi x x' hxx _ ht⟩

end GlobalTheory.AwayDescent
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.InertiaLeRangeOfUnramified
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.QuadraticCharacterUnramified

theorem eventually_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {P : HeightOneSpectrum (𝓞 E) → Prop} (h : ∀ᶠ w in Filter.cofinite, P w) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v ∧ P w := by
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.image fun w => w.under (𝓞 F)).subset fun v hv => ?_
  have := v.isMaximal
  obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  have e : (⟨Q, hQ.isPrime, hne⟩ : HeightOneSpectrum (𝓞 E)).under (𝓞 F) = v :=
    HeightOneSpectrum.ext hl.over.symm
  exact ⟨_, fun hP => hv ⟨_, e, hP⟩, e⟩

theorem good {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {η : HChar F}
    (hq : IsQuadCharOf K η) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 F) = v ∧
      η.UnrAt v ∧ ((η.val v : ℂˣ) : ℂ) = if normV w = normV v then 1 else -1 := by
  filter_upwards [eventually_under (F := F) hq] with v hv
  obtain ⟨w, rfl, hw⟩ := hv
  obtain ⟨h1, h3⟩ := hw (w.under (𝓞 F)) rfl
  refine ⟨w, rfl, h1, (congrArg Units.val h3).trans ?_⟩
  split_ifs <;> simp

theorem orderDvd_two {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K] {η : HChar F}
    (hq : IsQuadCharOf K η) : η.OrderDvd 2 := by
  show η ^ 2 = 1
  apply GlobalTheory.T.hecke_character_eq_of_cofinite F (η ^ 2) 1
  filter_upwards [good hq] with v hv
  obtain ⟨w, -, hu, hval⟩ := hv
  refine ⟨fun x hx => ?_, fun x _ => rfl, ?_⟩
  · rw [pow_two, HChar.loc_mul, hu x hx, one_mul]
  · have e1 : (1 : HChar F).val v = 1 := rfl
    rw [pow_two, HChar.val_mul, e1]
    apply Units.ext
    rw [Units.val_mul, hval, Units.val_one]
    split_ifs <;> norm_num

end GlobalTheory.QuadraticCharacterUnramified

theorem _root_.GlobalTheory.T.inertia_le_range_of_unramified : GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ η : HChar F, IsQuadCharOf K η → ∀ (u : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A u → η.UnrAt u → Ine (F := F) A ≤ (res F Ω K).range := by
  intro N F Ω _ _ _ _ _ K _ _ _ _ _ _ h2 η hq u A hA hu
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  obtain ⟨art, ha⟩ := N.aut.art F Ω
  obtain ⟨δ, hδc, hL⟩ := ha.exists_isLAdicOf ι
    (isAlgPos_zero_of_orderDvd two_pos (GlobalTheory.QuadraticCharacterUnramified.orderDvd_two hq))
  obtain ⟨ε, hεc, -, hε, hεu⟩ := UpperTheory.exists_quadratic_sign_character F K Ω 2 h2
  have hE : ∀ v, η.UnrAt v → CharEig ι δ v (η.val v : ℂˣ) := fun v hv B hB =>
    ⟨(hL.unr_iff ha (Or.inr rfl) hB).2 hv, fun σ hσ => by
      rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) hv hB hσ, inv_inv,
        RingEquiv.apply_symm_apply]⟩
  have hS := Filter.eventually_cofinite.1 ((GlobalTheory.QuadraticCharacterUnramified.good (K := K) hq).and hεu)
  have key := GlobalTheory.Published.ChebotarevDegreeOne.eq_of_frob (F := F) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
    (f := fun s => δ s) (f' := fun s => ε s) hδc hεc fun v hv _ B hB σ hσ => by
      obtain ⟨⟨w, hwv, hu', hval⟩, hεv⟩ := not_not.1 hv
      subst hwv
      have h1 := (hE _ hu' B hB).2 σ hσ
      have h3 := (UpperTheory.frobenius_sign_compatibility F K Ω 2 ι ε hε w hεv B hB).2 σ hσ
      have e : δ σ⁻¹ = ε σ⁻¹ := Units.ext (ι.injective (by rw [h1, h3, hval]))
      rwa [map_inv, map_inv, inv_inj] at e
  intro s hs
  have h1 : δ s = 1 := (hL.unr_iff ha (Or.inr rfl) hA).2 hu s hs
  have h3 : ε s = 1 := by
    have e : δ s = ε s := congrFun key s
    rw [← e, h1]
  exact (hε.1 s).1 h3
end

