import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0020
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsBridge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0218
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0254
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0253
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MonodromyZeroIffRestricts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.AdTransfer
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.EllipticTorusNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemWeilGroupAtPlaceOfFixesExtension
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.WeilUp

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω]
  [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω}

theorem modEq_of_cong {v' : HeightOneSpectrum (𝓞 L)} (h' : IsPlaceOver A v') {Q a b : ℕ}
    (hc : ∀ ζ : 𝓞 L, A.valuation ((algebraMap L Ω (ζ : L)) ^ (Q ^ b) - (algebraMap L Ω (ζ : L)) ^ (Q ^ a)) < 1) :
    Q ^ a ≡ Q ^ b [MOD normV v' - 1] := by
  haveI := v'.isMaximal
  letI : Field (𝓞 L ⧸ v'.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 L ⧸ v'.asIdeal) := v'.asIdeal.finiteQuotientOfFreeOfNeBot v'.ne_bot
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (𝓞 L ⧸ v'.asIdeal)ˣ)
  have hord : orderOf u = normV v' - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units]; rfl
  rw [← hord, ← pow_eq_pow_iff_modEq]
  obtain ⟨ζ, hζ⟩ := Ideal.Quotient.mk_surjective (u : 𝓞 L ⧸ v'.asIdeal)
  have hmem : ζ ^ (Q ^ b) - ζ ^ (Q ^ a) ∈ v'.asIdeal := by
    rw [← h']
    have e : algebraMap L Ω (((ζ ^ (Q ^ b) - ζ ^ (Q ^ a) : 𝓞 L)) : L) =
        (algebraMap L Ω (ζ : L)) ^ (Q ^ b) - (algebraMap L Ω (ζ : L)) ^ (Q ^ a) := by
      push_cast; simp [map_sub, map_pow]
    rw [e]; exact hc ζ
  have h0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  rw [map_sub, map_pow, map_pow, hζ, sub_eq_zero] at h0
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val]
  exact h0.symm

theorem dvd_of_modEq {q f n : ℕ} (hq : 1 < q) (h : q ^ n ≡ 1 [MOD q ^ f - 1]) : f ∣ n := by
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hd : q ^ f - 1 ∣ q ^ n - 1 := (Nat.modEq_iff_dvd' h1).mp h.symm
  have hg := Nat.pow_sub_one_gcd_pow_sub_one q f n
  rw [Nat.gcd_eq_left hd] at hg
  have h2 : 1 ≤ q ^ f := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ q ^ (f.gcd n) := Nat.one_le_pow _ _ (by omega)
  have h4 : q ^ f = q ^ (f.gcd n) := by omega
  have h5 := Nat.pow_right_injective (Nat.succ_le_of_lt hq) h4
  rw [h5]; exact Nat.gcd_dvd_right f n

theorem actsAs_of_agree {q f a b : ℕ} {σ : G K Ω} {g : G L Ω} (hg : ∀ z : Ω, σ z = g z)
    (hσ : ActsAs A q σ (f * a) (f * b)) : ActsAs A (q ^ f) g a b := by
  have e : σ = (g.restrictScalars K : G K Ω) := AlgEquiv.ext hg
  subst e
  refine ⟨hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [pow_mul, pow_mul] at this
  exact this

end GlobalTheory.AboveL.WeilUp

namespace GlobalTheory.AboveL

open GlobalTheory.AboveL.WeilUp in

theorem mem_weil_of_fix : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ : Weil h) (g : G L Ω), (∀ z : Ω, (σ : G K Ω) z = g z) → g ∈ Weil h' := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' σ g hg
  obtain ⟨f, hf⟩ := normV_eq_pow v v' (comap_eq_of_placeOver h h')
  have hq : 1 < normV v := one_lt_normV v

  have hcong : ∀ a b : ℕ, ActsAs A (normV v) (σ : G K Ω) a b →
      normV v ^ a ≡ normV v ^ b [MOD normV v ^ f - 1] := by
    intro a b hab
    rw [← hf]
    refine modEq_of_cong h' fun ζ => ?_
    have hfix : (σ : G K Ω) (algebraMap L Ω (ζ : L)) = algebraMap L Ω (ζ : L) := by
      rw [hg]; exact g.commutes _
    have hint : A.valuation (algebraMap L Ω (ζ : L)) ≤ 1 := by
      rw [A.valuation_le_one_iff]
      exact mem_of_isIntegral_int A (ζ.2.algebraMap)
    have := hab.2 _ hint
    rwa [hfix] at this
  set d := deg σ with hd
  rcases le_total 0 d with hd0 | hd0
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hd0
    have hact := actsAs_of_deg (σ := σ) (a := n) (b := 0) (by rw [← hd, hn]; simp)
    have hdiv : f ∣ n := dvd_of_modEq hq (by simpa using hcong _ _ hact)
    obtain ⟨k, rfl⟩ := hdiv
    have hact' := actsAs_of_deg (σ := σ) (a := f * k) (b := f * 0) (by rw [← hd, hn]; simp)
    exact (mem_Weil h').mpr ⟨k, 0, hf ▸ actsAs_of_agree hg hact'⟩
  · obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hd0
    have hact := actsAs_of_deg (σ := σ) (a := 0) (b := n) (by rw [← hd, hn]; simp)
    have hdiv : f ∣ n := dvd_of_modEq hq (by simpa using (hcong _ _ hact).symm)
    obtain ⟨k, rfl⟩ := hdiv
    have hact' := actsAs_of_deg (σ := σ) (a := f * 0) (b := f * k) (by rw [← hd, hn]; simp)
    exact (mem_Weil h').mpr ⟨0, k, hf ▸ actsAs_of_agree hg hact'⟩

end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsWdPst
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.AboveLRes

theorem restricts_wdPst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Qbar l ≃+* ℂ) {K L Ω : Type} [Field Ω] [Field K]
    [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω]
    [Algebra K L] [IsScalarTower K L Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') {O O' : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O']
    (Bw : LocBridge l K Ω (Dec (F := K) A) O) (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj : GlobalTheory.Pst.Induces Bw)
    (hj' : GlobalTheory.Pst.Induces Bw') (hjj : Bw'.j = Bw.j) (hle : Bw.Kw.1 ≤ Bw'.Kw.1) {LL : FinExt l} {V : Type}
    [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) :
    Restricts (wdPst P ι Bw h hj ρ) (wdPst P ι Bw' h' hj' (GlobalTheory.Pst.resTo ρ hle)) := by
  have hV' := (GlobalTheory.PstLaws.isPst_resTo_iff P ρ hle).2 hV
  haveI := hV.finite
  haveI := hV'.finite
  rw [wdPst_of_isPst ι Bw h hj hV, wdPst_of_isPst ι Bw' h' hj' hV']
  obtain ⟨e, he1, he2⟩ := GlobalTheory.T.fontaineWeilDeligneSpace_restriction_equiv l P ι K L Ω A v v' h h' O O' Bw Bw' hj hj' hle
    (fun σ σ' hσ => weilToGK_eq Bw Bw' hjj hle h h' σ σ' hσ) LL V ρ hV
  exact GlobalTheory.T.frobeniusSemisimplification_weilDeligne_restricts K L Ω A v v' h h' _ _ _ _ _ _ _ _ (isSmooth_wdRho P ι Bw h hj ρ)
    (isSmooth_wdRho P ι Bw' h' hj' _) (BridgeParam.isFrobSS_wdRep P ι Bw h hj ρ)
    (BridgeParam.isFrobSS_wdRep P ι Bw' h' hj' _) e he1 he2

theorem wdAt_resTo : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l K Ω (Dec (F := K) A) O) (hj : GlobalTheory.Pst.Induces Bw), IsPstAt P Bw (r.comp (Dec (F := K) A).subtype) → ∃ (O' : Type) (_ : CommRing O') (_ : Algebra ℤ_[l] O') (_ : TopologicalSpace O') (Bw' : LocBridge l L Ω (Dec (F := L) A) O') (hj' : GlobalTheory.Pst.Induces Bw'), IsPstAt P Bw' ((resTo L r).comp (Dec (F := L) A).subtype) ∧ Restricts (wdAt P ι Bw h hj (r.comp (Dec (F := K) A).subtype)) (wdAt P ι Bw' h' hj' ((resTo L r).comp (Dec (F := L) A).subtype)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' l _ ι P AI _ a r O _ _ _ Bw hj hr
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι Bw h hj hr
  obtain ⟨S, Bw', hjj, hS, hle⟩ := exists_bridge (L := L) Bw hj L₁
  have hj' : GlobalTheory.Pst.Induces Bw' := fun x => by rw [hjj]; exact hj x
  have key : ∀ (T : FinExt l) (hT : L₁.1 ≤ T.1), mapRep (algebraMap ↥T.1 (Om l))
      ((mapRep (IntermediateField.inclusion hT).toRingHom r₁).comp (decRes A)) =
      (GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype := by
    intro T hT
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := K) A) →* GL (Fin a) (Om l) =>
      ((f (decRes A g) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₁.2
  have hpS : IsPst P (Bw'.repE Bw'.LL ((mapRep (IntermediateField.inclusion hS).toRingHom r₁).comp (decRes A))) := by
    rw [repE_decRes Bw Bw' hjj hle]
    exact (GlobalTheory.PstLaws.isPst_resTo_iff P _ hle).2 (GlobalTheory.PstExt.isPst_enlarge P Bw hS r₁ hV₁)
  have hrL : IsPstAt P Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) :=
    ⟨Bw'.LL, _, ⟨le_rfl, key Bw'.LL hS⟩, hpS⟩
  refine ⟨_, _, _, _, Bw', hj', hrL, ?_⟩
  obtain ⟨L₃, r₃, hm₃, hV₃, e₃⟩ := wdAt_of_isPstAt ι Bw' h' hj' hrL
  have h13 : L₁.1 ≤ (supExt L₁ L₃).1 := le_sup_left
  have h33 : L₃.1 ≤ (supExt L₁ L₃).1 := le_sup_right
  have hm₃' : IsModel Bw' ((GlobalTheory.AboveL.resTo L r).comp (Dec (F := L) A).subtype) (supExt L₁ L₃)
      (mapRep (IntermediateField.inclusion h33).toRingHom r₃) := by
    refine ⟨hm₃.1.trans h33, ?_⟩
    ext g i k
    exact congrArg (fun f : ↥(Dec (F := L) A) →* GL (Fin a) (Om l) =>
      ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i k) hm₃.2
  have heq := IsModel.unique Bw' _ hm₃' ⟨hm₃.1.trans h33, key _ h13⟩
  rw [e₁, e₃, BridgeParam.wdPst_enlarge P ι Bw h hj h13 r₁ hV₁, BridgeParam.wdPst_enlarge P ι Bw' h' hj' h33 r₃ hV₃,
    heq, repE_decRes Bw Bw' hjj hle]
  exact restricts_wdPst P ι h h' Bw Bw' hj hj' hjj hle _ (GlobalTheory.PstExt.isPst_enlarge P Bw h13 r₁ hV₁)

end GlobalTheory.AboveLRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMatchBaseChange
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.SatBC

theorem normV_under_pow (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (w : HeightOneSpectrum (𝓞 M)) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem tendsto_under (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  haveI := v.isMaximal
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
    ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).subset ?_) (fun _ _ _ _ h => HeightOneSpectrum.ext h)
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨by rw [← Set.mem_singleton_iff.1 hw, HeightOneSpectrum.under_asIdeal]⟩⟩

theorem isPlaceOver_under {K M Ω : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K Ω]
    [Algebra M Ω] [Algebra K M] [IsScalarTower K M Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 M)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 K)) := fun x => by
  rw [IsScalarTower.algebraMap_apply K M Ω]
  exact h (algebraMap (𝓞 K) (𝓞 M) x)

end GlobalTheory.AboveL.SatBC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnderConjugatePlaceEqConjugatePlaceUnder
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.ConjUnder

theorem complexConj_algebraMap {K M : Type} [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (x : K) :
    IsCMField.complexConj M (algebraMap K M x) = algebraMap K M (IsCMField.complexConj K x) := by
  obtain ⟨j⟩ : Nonempty (M →+* ℂ) := inferInstance
  apply j.injective
  rw [IsCMField.complexEmbedding_complexConj M j]
  exact (IsCMField.complexEmbedding_complexConj K (j.comp (algebraMap K M)) x).symm

theorem cPl_asIdeal {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    (UpperTheory.V.Af.Bc.cPl w).asIdeal =
      w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv : 𝓞 E →+* 𝓞 E) :=
  (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc _ w)

theorem cPl_under : ∀ (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (w : HeightOneSpectrum (𝓞 M)),
    (UpperTheory.V.Af.Bc.cPl w).under (𝓞 K) = UpperTheory.V.Af.Bc.cPl (w.under (𝓞 K)) := by
  intro K M _ _ _ _ _ _ _ w
  apply HeightOneSpectrum.ext
  rw [cPl_asIdeal]
  change (UpperTheory.V.Af.Bc.cPl w).asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = (w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M))).comap _
  rw [cPl_asIdeal, Ideal.comap_comap, Ideal.comap_comap]
  congr 1
  ext x
  exact complexConj_algebraMap (x : K)

end GlobalTheory.ConjUnder
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.NormValGen

theorem valuation_eq_pow_of_norm_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) (y : (v.adicCompletion K)ˣ) (x : (w.adicCompletion L)ˣ)
    (h : ‖(y : v.adicCompletion K)‖ = ‖(x : w.adicCompletion L)‖) (f : ℕ) (hf : normV w = normV v ^ f) :
    Valued.v (y : v.adicCompletion K) = Valued.v (x : w.adicCompletion L) ^ f := by
  have hf' : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ f := hf
  have hy : Valued.v (y : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 y.ne_zero
  have hx : Valued.v (x : w.adicCompletion L) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [FinitePlace.norm_def, FinitePlace.norm_def] at h
  rw [WithZeroMulInt.toNNReal_neg_apply _ hy, WithZeroMulInt.toNNReal_neg_apply _ hx, NNReal.coe_inj, hf',
    Nat.cast_pow, ← zpow_natCast, ← zpow_mul] at h
  have h1 := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have h2 := zpow_right_injective₀ (zero_lt_one.trans h1) h1.ne' h
  rw [← WithZero.coe_unzero hy, ← WithZero.coe_unzero hx, ← WithZero.coe_pow]
  refine congrArg _ (Multiplicative.toAdd.injective ?_)
  rw [h2, toAdd_pow, nsmul_eq_mul]

theorem loc_eq_of_comp_norm {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    (ψ : HChar K) (ψ' : HChar M) (hψ : ∀ x : Ideles M, ψ'.1 x = ψ.1 (GroundTheory.Global.ideleNorm K M x))
    (w : HeightOneSpectrum (𝓞 M)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 K)) ^ f)
    (x : (w.adicCompletion M)ˣ) : ∃ y : ((w.under (𝓞 K)).adicCompletion K)ˣ,
      ψ'.loc w x = ψ.loc (w.under (𝓞 K)) y ∧
      Valued.v (y : (w.under (𝓞 K)).adicCompletion K) = Valued.v (x : w.adicCompletion M) ^ f := by
  have h := GroundTheory.Global.ideleNorm_finiteEmbedding (K := K) w x
  have hm := GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := K)
    (GroundTheory.Global.IdeleGroup.finiteEmbedding w x)
  rw [h] at hm
  have hm' := congrArg Subtype.val hm
  rw [GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding, GroundTheory.Global.IdeleGroup.ideleModule_finiteEmbedding] at hm'
  exact ⟨_, (hψ _).trans (congrArg ψ.1 h), valuation_eq_pow_of_norm_eq _ w _ x hm' f hf⟩

theorem unrAt_val_of_comp_norm : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (ψ : HChar K) (ψ' : HChar M), (∀ x : Ideles M, ψ'.1 x = ψ.1 (GroundTheory.Global.ideleNorm K M x)) → ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), normV w = normV (w.under (𝓞 K)) ^ f → ψ.UnrAt (w.under (𝓞 K)) → ψ'.UnrAt w ∧ ψ'.val w = ψ.val (w.under (𝓞 K)) ^ f := by
  intro K M _ _ _ _ _ ψ ψ' hψ w f hf hu
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, hv⟩ := loc_eq_of_comp_norm ψ ψ' hψ w f hf x
    rw [hy]
    apply hu
    unfold IsUnitAt at *
    rw [hv, hx, one_pow]
  · obtain ⟨y, hy, hv⟩ := loc_eq_of_comp_norm ψ ψ' hψ w f hf (atFin w (unif w))
    have h1 := unif_spec w
    have h2 := unif_spec (w.under (𝓞 K))
    have hunit : IsUnitAt (w.under (𝓞 K)) (y * ((atFin _ (unif (w.under (𝓞 K)))) ^ f)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, hv, h1, h2]
      exact mul_inv_cancel₀ (pow_ne_zero _ WithZero.exp_ne_zero)
    have h3 := hu _ hunit
    rw [map_mul, map_inv, mul_inv_eq_one, map_pow] at h3
    exact hy.trans h3

end GlobalTheory.NormValGen

end
end

