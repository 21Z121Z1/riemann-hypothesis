import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.JointCharacters.SameChr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0323

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinpolyIrreducibleLocalEmbedding
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocIrred

theorem minpoly_map_adicCompletion_irreducible : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (∀ σ : G K Ω, ∃ τ ∈ Dec (F := K) A, ∀ x : L, τ (algebraMap L Ω x) = σ (algebraMap L Ω x)) → ∀ ι : Ω →ₐ[K] Kbar v, IsLocEmb A v ι → ∀ α : L, Irreducible ((minpoly K α).map (algebraMap K (v.adicCompletion K))) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ A v hA hdec ι hι α
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  set a : Ω := algebraMap L Ω α with ha
  have hPa : minpoly K a = minpoly K α := by
    have := minpoly.algHom_eq (IsScalarTower.toAlgHom K L Ω) (algebraMap L Ω).injective α
    simpa [ha] using this
  rw [← hPa]
  have haint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set P := minpoly K a with hP
  have hsep : P.Separable := (minpoly.irreducible haint).separable
  set β := ι a with hβdef
  have hβ : IsIntegral (v.adicCompletion K) β := Algebra.IsIntegral.isIntegral β
  set Q := minpoly (v.adicCompletion K) β with hQ
  have hQdvd : Q ∣ P.map (algebraMap K (v.adicCompletion K)) := by
    apply minpoly.dvd
    rw [Polynomial.aeval_map_algebraMap, hβdef, Polynomial.aeval_algHom_apply, hP, minpoly.aeval, map_zero]
  obtain ⟨θ, -, -, hlift⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc K Ω A v hA ι hι
  set R := (P.map (algebraMap K Ω)).roots with hR
  have hRcard : Multiset.card R = P.natDegree :=
    by
    rw [hR, IsAlgClosed.card_roots_eq_natDegree, Polynomial.natDegree_map]
  have hRnd : R.Nodup := Polynomial.nodup_roots (hsep.map)
  have hSnd : (R.map ι).Nodup := hRnd.map ι.injective
  have hQ0 : Q ≠ 0 := minpoly.ne_zero hβ
  have hsub : R.map ι ≤ (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).roots := by
    rw [Multiset.le_iff_subset hSnd]
    intro y hy
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hy
    have hr0 : Polynomial.aeval r P = 0 := by
      have := (Polynomial.mem_roots_map (minpoly.ne_zero haint)).mp hr
      rwa [Polynomial.aeval_def]
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' haint.isAlgebraic hr0
    obtain ⟨τ, hτ, hτσ⟩ := hdec σ
    have hg : θ ⟨τ, hτ⟩ β = ι r := by
      rw [hβdef, hlift ⟨τ, hτ⟩ a, ← hσ]
      exact congrArg ι (hτσ α)
    rw [Polynomial.mem_roots_map hQ0, ← Polynomial.aeval_def, ← hg, Polynomial.aeval_algEquiv,
      AlgHom.comp_apply, hQ, minpoly.aeval, map_zero]
  have hdeg : P.natDegree ≤ Q.natDegree := by
    calc P.natDegree = Multiset.card (R.map ι) := by rw [Multiset.card_map, hRcard]
      _ ≤ Multiset.card (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).roots := Multiset.card_le_card hsub
      _ ≤ (Q.map (algebraMap (v.adicCompletion K) (Kbar v))).natDegree := Polynomial.card_roots' _
      _ = Q.natDegree := Polynomial.natDegree_map _
  have heq : P.map (algebraMap K (v.adicCompletion K)) = Q :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hβ) ((minpoly.monic haint).map _) hQdvd
      (by rw [Polynomial.natDegree_map]; exact hdeg)
  rw [heq]
  exact minpoly.irreducible hβ

end GlobalTheory.LocIrred
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullbackStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nefFib_pullback : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p), ArInt.NefFib L → ArInt.NefFib (L.pull π hπ) := by
  first | exact @GlobalTheory.ArInt.nefFib_pull | exact GlobalTheory.ArInt.nefFib_pull | (intros; apply GlobalTheory.ArInt.nefFib_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormVEqAbsNorm
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.ChiLocGal

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

open Pointwise in

theorem isFrob_conj {A : ValuationSubring Ω} {q : ℕ} {g σ : G E Ω} (hσ : IsFrob (F := E) (g • A) q σ) :
    IsFrob (F := E) A q (g⁻¹ * σ * g) := by
  have hm : ∀ x, g x ∈ g • A ↔ x ∈ A := fun x => ValuationSubring.smul_mem_pointwise_smul_iff
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h1 := hσ.2 (g x) (by rwa [ValuationSubring.valuation_le_one_iff, hm,
      ← ValuationSubring.valuation_le_one_iff])
    have e : σ (g x) - g x ^ q = g ((g⁻¹ * σ * g) x - x ^ q) := by
      rw [map_sub, map_pow, AlgEquiv.mul_apply, AlgEquiv.mul_apply, mul_inv_apply]
    rwa [e, valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ g.injective,
      ← valuation_lt_one_iff'] at h1

theorem frob_any [IsAlgClosure E Ω] {B : Type} [CommGroup B] {r r' : G E Ω →* B}
    {v : HeightOneSpectrum (𝓞 E)} {A₀ A : ValuationSubring Ω} (h0 : IsPlaceOver A₀ v) (hA : IsPlaceOver A v)
    (h : ∀ σ : G E Ω, IsFrob (F := E) A₀ (normV v) σ → r σ = r' σ) {σ : G E Ω}
    (hσ : IsFrob (F := E) A (normV v) σ) : r σ = r' σ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver h0 hA
  have e : ∀ f : G E Ω →* B, f (g⁻¹ * σ * g) = f σ := fun f => by
    rw [map_mul, map_mul, map_inv, mul_comm (f g)⁻¹ (f σ), mul_assoc, inv_mul_cancel, mul_one]
  rw [← e r, ← e r']
  exact h _ (isFrob_conj hσ)

theorem locM_eq (P : HeightOneSpectrum (𝓞 E)) (x : (P.adicCompletion E)ˣ) :
    Units.map (Formalism.L2.NC.locM P) x = localIdele E P x := by
  rfl

end General

section Values

variable {E : Type} [Field E] [NumberField E]

theorem val_of_at {χ : HChar E} {ψ : Formalism.L2.NC.HC E} (h : ∀ x, ψ.χ x = χ.1 x) {P : HeightOneSpectrum (𝓞 E)} {α : ℂ}
    (hα : ψ.At P α) : ((χ.val P : ℂˣ) : ℂ) = α := by
  rw [← hα.2 _ (unif_spec P), h, locM_eq]
  rfl

theorem normV_eq_absNorm (P : HeightOneSpectrum (𝓞 E)) : normV P = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem val_block {μ η : HChar E} {r : ℕ} {P : HeightOneSpectrum (𝓞 E)} {α z : ℂ}
    (hα : (((μ * η⁻¹).val P : ℂˣ) : ℂ) = α) (hz : z = α⁻¹ * (Real.sqrt (normV P) : ℂ) ^ (-(r : ℤ))) :
    (((GlobalTheory.GalChar.block μ η r).val P : ℂˣ) : ℂ) = z⁻¹ := by
  rw [GlobalTheory.GalChar.block_val, hα, hz, mul_inv, inv_inv, zpow_neg, inv_inv, zpow_natCast, ← normV_eq_absNorm]
  congr 1
  have h0 : (0 : ℝ) ≤ (normV P : ℝ) := Nat.cast_nonneg _
  rw [show ((normV P : ℕ) : ℂ) = ((normV P : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow h0,
    Real.sqrt_eq_rpow, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul h0]
  congr 2
  ring

end Values

theorem chi1_loc_isGal : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), AutSpec A M tp.tup Sp.iq Y Cb → ∀ (art : Ideles D.host.E →* Gab D.host.E D.nd.Om), IsGlobalArtin art → ∀ (i : X.nd.Loc) (j' : Fin D.R.m), j'.1 + 1 = X.nd.j i → ∃ n, GlobalTheory.GalChar.IsGal art (Sp.iq i) (Y.naut.iotaQC i) (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r) n ((Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp _ _ _ he _ _ big X T Sp Y Cb hAu art ha i j' hj
  letI := D.ntw.crO0 (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_isDomain (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_isDVR (T.twOf i)
  letI := D.ntw.topO0 (T.twOf i)
  haveI := D.ntw.twistBaseCoefficientRing_topologicalRing (T.twOf i)

  let C' : GlobalTheory.Mem.Chr.HFrame D.host (eExp D) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  obtain ⟨n0, h0⟩ := GlobalTheory.GalChar.exists_isAlgPos_mu0 C' he j'
  obtain ⟨n, hn⟩ := GlobalTheory.GalChar.block_alg C' ⟨_, GlobalTheory.GalChar.isAlgPos_mul h0 (GlobalTheory.GalChar.del_alg C' (X.nd.l i))⟩
  have hn' : IsAlgPos (GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r) n := hn

  have hj1 := X.nd.j_range i
  obtain ⟨B1, hB1⟩ := Bs.chi.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) hj1.1 hj1.2
  have hχ : ∀ x, (Bs.chiD.firstHeckeCharacter (T.twOf i) (X.nd.j i)).χ x = (cf.mu0 j' * cf.delAt (X.nd.l i) * cf.eta⁻¹).1 x := by
    intro x
    have h1 := Bs.ringSpec_normalisedCharacter_eq j' x
    have h2 := Bs.del_eq (T.twOf i) x
    have h3 := Bs.eta_eq x
    rw [hj] at h1
    have h4 : D.ntw.l (T.twOf i) = X.nd.l i := T.twOf_l i
    rw [h4] at h2
    simp only [Formalism.L2.NC.NChiData.firstHeckeCharacter, Formalism.L2.NC.HC.mul_χ, Formalism.L2.NC.HC.inv_χ, MonoidHom.mul_apply,
      MonoidHom.inv_apply, h1, h2, h3]
    rfl
  set χb := GlobalTheory.GalChar.block (cf.mu0 j' * cf.delAt (X.nd.l i)) cf.eta D.R.r with hχb

  have key : ∀ P ∉ B1, ∃ x : ↥D.LL0, Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x = ((χb.val P : ℂˣ) : ℂ)⁻¹ ∧
      ∀ σ : G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
        X.nd.embK i (x : D.what₂.LL) = algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
          (T.twist₂ i (Units.val (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ))) := by
    intro P hP
    obtain ⟨α, hα, x, hx, hσ⟩ := hB1 P hP
    refine ⟨x, ?_, fun σ hσ' => T.twO_emb i x _ (hσ σ hσ')⟩
    rw [val_block (val_of_at hχ hα) hx, inv_inv]
  have hev : ∀ᶠ P in Filter.cofinite, P ∉ B1 := Filter.eventually_cofinite.2 (by simpa using B1.finite_toSet)
  have hAlm : GlobalTheory.GalChar.AlmostIn (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D) χb := by
    filter_upwards [hev] with P hP
    obtain ⟨x, hx, -⟩ := key P hP
    exact ⟨x⁻¹, by rw [map_inv₀, hx, inv_inv]⟩
  have hf : ∀ x : ↥D.LL0, Y.naut.iotaQC i (Sp.iq i (((X.nd.embK i).comp D.LL0.val.toRingHom) x)) =
      Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D x := by
    intro x
    rw [← hAu.iotaQ i]
    exact Y.iota_LL i x
  have hO := X.nd.O_adic i
  have hκ := Sp.iq_alg i
  obtain ⟨r0, hr0⟩ := GlobalTheory.GalChar.exists_isGal hO hκ ha hn' hf hAlm

  haveI : T2Space (X.nd.O i) := (GlobalTheory.GalChar.isEmbedding_toQ hO hκ).t2Space
  have hlO := (GlobalTheory.CoefEmbed.embedding_closed_integral (X.nd.l i) (X.nd.O i) hO (Sp.iq i) hκ).2.2.2
  have hl0 : ((X.nd.l i : ℕ) : D.ntw.O0 (T.twOf i)) ≠ 0 := fun h => by
    have h' := congrArg (algebraMap (D.ntw.O0 (T.twOf i)) (FractionRing (D.ntw.O0 (T.twOf i)))) h
    rw [map_natCast, map_zero, ← map_natCast (D.ntw.emb0 (T.twOf i))] at h'
    have h'' := (D.ntw.emb0 (T.twOf i)).injective (h'.trans (map_zero _).symm)
    exact (Fact.out : (X.nd.l i).Prime).ne_zero (by exact_mod_cast h'')
  have hc1 : Continuous ((Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i))) :=
    GlobalTheory.GalChar.continuous_units _ ((GlobalTheory.GalChar.continuous_ringHom (D.ntw.twistBaseCoefficientRing_isAdic (T.twOf i)) hO hl0 hlO (T.twist₂ i)).comp
      (D.ntw.twistCharacterFamily_continuous (T.twOf i) (X.nd.j i) (T.twSide i)))
  have hlne : X.nd.l i ≠ 0 := (Fact.out : (X.nd.l i).Prime).ne_zero
  have heq : r0 = (Units.map (T.twist₂ i).toMonoidHom).comp (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i)) := by
    refine GlobalTheory.GalChar.eq_of_frob ha (GlobalTheory.GalChar.continuous_units r0 hr0.2.1) hc1 ?_
    filter_upwards [hev, GlobalTheory.GalChar.unr_ae χb, GlobalTheory.GalChar.away_ae (E := D.host.E) (X.nd.l i) hlne]
      with v hv hu hl A' hA' σ hσ
    refine frob_any (D.nd.plOm.2 v) hA' (fun σ' hσ' => ?_) hσ
    obtain ⟨x, hx1, hx2⟩ := key v hv
    apply Units.ext
    apply GlobalTheory.GalChar.toQ_injective (Sp.iq i)
    apply (Y.naut.iotaQC i).injective
    rw [hr0.frob ha (Or.inl hl) hu (D.nd.plOm.2 v) hσ', ← hx1]
    show _ = Y.naut.iotaQC i (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.twist₂ i (Units.val (D.ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ')))))
    rw [← hx2 σ' hσ']
    exact (hf x).symm
  exact ⟨n, heq ▸ hr0⟩

end GlobalTheory.ChiLocGal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieDirectSum
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.PolyRep

theorem lie_sum {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R]
    (A : Mat m R) :
    (ρ.sum σ).lie A = blockSum (ρ.lie A) (σ.lie A) := by
  ext i j
  simp only [lie, Matrix.of_apply]
  change Fin (ρ.M + σ.M) at i j
  change ∑ v : EntIx m, aeval (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2)
      (pderiv v (blockSum ρ.ent σ.ent i j)) * A v.1 v.2.1 v.2.2 = _
  obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective j
  rcases x with x | x <;> rcases y with y | y <;> simp [lie, sum, blockSum]

end GlobalTheory.GoodMetric.PolyRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieExteriorSquare
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.PolyRep

theorem snd_wedge2_dual {M : ℕ} {R : Type} [CommRing R] (L : Matrix (Fin M) (Fin M) R) (p q : Fin (pairCard M)) :
    TrivSqZeroExt.snd (ChernSpan.wedge2 (Matrix.of fun a b =>
        (TrivSqZeroExt.inl ((1 : Matrix (Fin M) (Fin M) R) a b) + TrivSqZeroExt.inr (L a b) : DualNumber R)) p q)
      = wedge2Lie L p q := by
  simp only [ChernSpan.wedge2, wedge2Lie, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    wedgeRaw, wedgeLieRaw, Matrix.of_apply]
  simp only [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
    smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero, zero_add]
  ring

theorem lie_wedge2 {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) :
    ρ.wedge2.lie A = wedge2Lie (ρ.lie A) := by
  ext p q
  have h := ev_dual_model ρ.wedge2 A p q
  have e : ∀ D : Mat m (DualNumber R), ρ.wedge2.ev D = ChernSpan.wedge2 (ρ.ev D) :=
    fun D => evEnt_wedge2 ρ.ent D
  have e2 : ρ.ev (R := DualNumber R) (fun τ => Matrix.of fun a b =>
        TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b))
      = Matrix.of fun a b => (TrivSqZeroExt.inl ((1 : Matrix (Fin ρ.M) (Fin ρ.M) R) a b)
        + TrivSqZeroExt.inr (ρ.lie A a b) : DualNumber R) := by
    ext a b : 1
    exact ev_dual_model ρ A a b
  rw [e, e2] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h2
  exact h2.symm.trans (snd_wedge2_dual (ρ.lie A) p q)

end GlobalTheory.GoodMetric.PolyRep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieTensorProduct
section
open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric.PolyRep

theorem lie_tensor {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ σ : PolyRep m) {R : Type} [CommRing R]
    (A : Mat m R) :
    (ρ.tensor σ).lie A = kron (ρ.lie A) 1 + kron 1 (σ.lie A) := by
  ext i j
  obtain ⟨⟨a, c⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨b, d⟩, rfl⟩ := finProdFinEquiv.surjective j
  set X : Mat m (DualNumber R) := fun τ => Matrix.of fun a b =>
    TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b) with hX
  have h := ev_dual_model (ρ.tensor σ) A (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d))
  have hk : (ρ.tensor σ).ev X = kron (ρ.ev X) (σ.ev X) := evEnt_kron ρ.ent σ.ent X
  rw [hk] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h2
  have hr : (kron (ρ.lie A) (1 : Matrix (Fin σ.M) (Fin σ.M) R) + kron (1 : Matrix (Fin ρ.M) (Fin ρ.M) R) (σ.lie A))
      (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d))
      = ρ.lie A a b * (1 : Matrix (Fin σ.M) (Fin σ.M) R) c d + (1 : Matrix (Fin ρ.M) (Fin ρ.M) R) a b * σ.lie A c d := by
    simp [kron]
  have hl : kron (ρ.ev X) (σ.ev X) (finProdFinEquiv (a, c)) (finProdFinEquiv (b, d)) = ρ.ev X a b * σ.ev X c d := by
    simp [kron]
  rw [hl, ev_dual_model ρ A a b, ev_dual_model σ A c d] at h2
  rw [← h2]
  refine Eq.trans ?_ hr.symm
  simp [TrivSqZeroExt.snd_mul]
  ring

end GlobalTheory.GoodMetric.PolyRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemFaceLevelMultiplicityStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalLevelForm_mem_faceLevelMultiplicity : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → R.cX.toMap R.prX Fn ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  first | exact @GlobalTheory.DefiniteMult.toMap_mem_levP | exact GlobalTheory.DefiniteMult.toMap_mem_levP | (intros; apply GlobalTheory.DefiniteMult.toMap_mem_levP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemSpanAdelicRationalForms
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem mem_of_avg {K : Type} [Field K] (σ : K →+* ℂ) {V : Type} [AddCommGroup V] [Module K V] {G : Type} [Group G]
    (r : Representation K G V) (P : Subgroup G) [Fintype P] (ψ : P →* Kˣ) {M : Type} [AddCommGroup M] [Module ℂ M]
    (j : V →ₛₗ[σ] M) (T : P → M →ₗ[ℂ] M) (hT : ∀ p v, T p (j v) = j (r p v))
    (S : Submodule ℂ M) (hS : ∀ v, (∀ h : P, r h v = ((ψ h : Kˣ) : K) • v) → j v ∈ S)
    (Fn : M) (hF : Fn ∈ Submodule.span ℂ (Set.range j)) (hFn : ∀ p, T p Fn = σ ((ψ p : Kˣ) : K) • Fn) : Fn ∈ S := by
  let Pj : M →ₗ[ℂ] M := (Nat.card P : ℂ)⁻¹ • ∑ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p
  have hPj : ∀ x, Pj x = (Nat.card P : ℂ)⁻¹ • ∑ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p x := by
    intro x
    simp only [Pj, LinearMap.smul_apply, LinearMap.sum_apply]
  have hcard : (Nat.card P : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hfix : Pj Fn = Fn := by
    have hterm : ∀ p : P, σ ((ψ p⁻¹ : Kˣ) : K) • T p Fn = Fn := by
      intro p
      rw [hFn, smul_smul, ← map_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, map_one, one_smul]
    rw [hPj, Finset.sum_congr rfl fun p _ => hterm p, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hmap : ∀ v, Pj (j v) ∈ S := by
    intro v
    have e : Pj (j v) = j ((Nat.card P : K)⁻¹ • ∑ p : P, ((ψ p⁻¹ : Kˣ) : K) • r p v) := by
      rw [hPj, map_smulₛₗ, map_sum, map_inv₀, map_natCast]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_smulₛₗ, hT]
    rw [e]
    exact hS _ (avg_level K V G r P ψ v)
  have hle : Submodule.span ℂ (Set.range j) ≤ S.comap Pj :=
    Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact hmap v)
  have hPF : Pj Fn ∈ S := hle hF
  rwa [hfix] at hPF

theorem exists_rowForm (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G)
    (ψ : P →* D.what₂.LLˣ) (t : T) (f : A.fam.amb.FR t) (hlv : ∀ h : P, (A.fam.R t).r h f = ((ψ h : D.what₂.LLˣ) : D.what₂.LL) • f) :
    ∃ x, rowForm A P ψ t x = f :=
  (GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char _ _ _ (A.fam.R t).r P ψ f).2 hlv

theorem jR_mem_span (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (g : A.fam.amb.FR t)
    (hg : ∀ h : (F.lvl b).P, (A.fam.R t).r h g = (((F.lvl b).ψ h : D.what₂.LLˣ) : D.what₂.LL) • g)
    (Y : Bridge.Gf D.sp.X' → R.cX.W) (hY : Y = R.B.jR t g) :
    Y ∈ Submodule.span ℂ (Set.range fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)) := by
  obtain ⟨x, hx⟩ := exists_rowForm D G Pl0 T A (F.lvl b).P (F.lvl b).ψ t g hg
  subst hY
  subst hx
  exact Submodule.subset_span ⟨x, rfl⟩

set_option maxHeartbeats 2000000 in

theorem proj_span : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (b : Bool) (t : T) (Fn : Bridge.Gf D.sp.X' → R.cX.W), Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ → (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) → Fn ∈ Submodule.span ℂ (Set.range fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F b t Fn hF hQ
  have hB := Bridge.ClassPres.extBij_holds (R.B.R t).pres
  have hF0 : Fn ∈ Submodule.span ℂ (Set.range (R.B.R t).pres.extL) := by rw [hB.2]; exact hF
  have hF' : Fn ∈ Submodule.span ℂ (Set.range (R.B.jR t)) := hF0
  obtain ⟨κ, hκ⟩ : ∃ κ : (F.lvl b).P → (levEnv D.sp.X' R.βX (R.datXt t)).Q,
      ∀ p, (R.B.R t).act_tie.red (κ p) = (p : G) :=
    ⟨fun p => ((R.B.R t).act_tie.red_surj (p : G)).choose,
      fun p => ((R.B.R t).act_tie.red_surj (p : G)).choose_spec⟩
  obtain ⟨gl, gl_apply⟩ : ∃ gl : (F.lvl b).P → (Bridge.Gf D.sp.X' → R.cX.W) →ₗ[ℂ] (Bridge.Gf D.sp.X' → R.cX.W),
      ∀ p H, gl p H = Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) H :=
    ⟨fun p => { toFun := fun H => Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) H
                map_add' := by intro H H'; funext h; simp only [Bridge.g0Act, Pi.add_apply, smul_add]
                map_smul' := by intro c H; funext h; simp only [Bridge.g0Act, Pi.smul_apply, RingHom.id_apply]; rw [smul_comm] },
      fun _ _ => rfl⟩
  have hact : ∀ (p : (F.lvl b).P) (f : A.fam.amb.FR t), gl p (R.B.jR t f) = R.B.jR t ((A.fam.R t).r p f) := by
    intro p f
    have e : (R.B.R t).pres.extL (A.leftGroupActionRight t (p : G) f) =
        Bridge.g0Act (levEnv D.sp.X' R.βX (R.datXt t)).ch (κ p) ((R.B.R t).pres.extL f) :=
      (R.B.R t).act_tie.act_eq (p : G) (κ p) (hκ p) f
    exact (gl_apply p _).trans e.symm
  have hg : ∀ p : (F.lvl b).P, gl p Fn = D.what₂.embLL (((F.lvl b).ψ p : D.what₂.LLˣ) : D.what₂.LL) • Fn := by
    intro p
    have hq : (R.B.R t).act_tie.red (κ p) ∈ (F.lvl b).P := by rw [hκ p]; exact p.2
    rw [gl_apply]
    funext h
    simp only [Bridge.g0Act, Pi.smul_apply]
    rw [hQ (κ p) hq h]
    have hp : (⟨_, hq⟩ : (F.lvl b).P) = p := Subtype.ext (hκ p)
    rw [hp, smul_smul, ← mul_assoc, Units.inv_mul, one_mul]
  exact mem_of_avg D.what₂.embLL (A.fam.R t).r (F.lvl b).P (F.lvl b).ψ (R.B.jR t) gl hact _
    (fun v hv => jR_mem_span D G Pl0 T A Ks R F b t v hv _ rfl) Fn hF' hg

end GlobalTheory.TopSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalIsometryIsometricStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_isometry_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (L M : HermLB p), RatIsom L M → L.Isometric M := by
  first | exact @GlobalTheory.HermIsom.isometric_of_ratIsom | exact GlobalTheory.HermIsom.isometric_of_ratIsom | (intros; apply GlobalTheory.HermIsom.isometric_of_ratIsom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSectionExtensionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_section_extension : ∀ (X Y Z : Scheme.{0}) [IsIntegral Y] [IsIntegral Z] (j : Y ⟶ X) [SurjectiveOnStalks j] (i : Z ⟶ X) (x : Y), i (genericPoint Z) = j x → ∀ (B : LB X), B.IsLB → ∀ (r : (B.pull j).ι → Y.functionFieldˣ), IsRatSec (B.pull j) r → ∀ (u : Y.functionFieldˣ), (∀ c, x ∈ (B.pull j).U c → UnitAt x ((u * r c : Y.functionFieldˣ) : Y.functionField)) → ∃ s : (B.pull i).ι → Z.functionFieldˣ, IsRatSec (B.pull i) s ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ Y) (y' : Sp K ⟶ Z) (c : B.ι), y ≫ j = y' ≫ i → below y = x → below y' = genericPoint Z → j x ∈ B.U c → valAt y' (s (fun _ => c) : Z.functionField) = valAt y ((u * r (fun _ => c) : Y.functionFieldˣ) : Y.functionField) := by
  first | exact @GlobalTheory.RestrictRatSec.exists_restriction | exact GlobalTheory.RestrictRatSec.exists_restriction | (intros; apply GlobalTheory.RestrictRatSec.exists_restriction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalSymplecticPoints_self_annihilator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (x : WO S T), (∀ γ ∈ ratL T S, ψ (symplO S T x γ) = 1) ↔ x ∈ ratL T S := by
  first | exact @GlobalTheory.RatAnnih.ratL_annihilator | exact GlobalTheory.RatAnnih.ratL_annihilator | (intros; apply GlobalTheory.RatAnnih.ratL_annihilator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameChrOfChrEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SameChrFin

theorem sameChr_of_chrEq : ∀ (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch) (X : ThetaX D)
    (T : ThetaTied D X) (H : Formalism.L2.Host.ThetaChrTied D C nch Tp X),
    (∀ c, Formalism.IndefR.Links.ChrEq (T.eChr c) (H.eChr c)) → Formalism.L2.JoinChr.SameChr T H := by
  intro D C nch Tp X T H h
  refine ⟨fun P => ?_, fun c P e he k x hx => (h c).2 P e he k x hx,
    fun θ hθ c τ k x hx => GlobalTheory.CharInfPlace.chrEq_infLoc D (T.eChr c) (H.eChr c) (h c) θ hθ τ k x hx⟩
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨e, he, -⟩ := GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3 P
  exact ⟨e, he⟩

end GlobalTheory.SameChrFin
end

