import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0155
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0614
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0671
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwoReadings
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0338
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0329
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0692
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0904
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0693

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsHalfIdem
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.SingleDatum

theorem exists_isHalfIdem : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l : Geo.Tor.Level H), ∃ e : AE D, IsHalfIdem l e := by
  intro D H l
  classical
  have hbar : ∀ x : 𝓞 D.host.E, H.bar x = GlobalTheory.IdemSupport.cO D x := fun x =>
    RingOfIntegers.ext (by rw [H.bar_eq, GlobalTheory.IdemSupport.cO_coe]; rfl)
  have key : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), l.Mb ≤ Q.asIdeal → ¬ l.Mb ≤ (GlobalTheory.IdemSupport.cP Q).asIdeal := by
    intro Q h1 h2
    apply Q.isPrime.ne_top
    rw [eq_top_iff, ← l.coprime]
    refine sup_le h1 (Ideal.map_le_iff_le_comap.2 fun x hx => ?_)
    have h3 := h2 hx
    rw [GlobalTheory.IdemSupport.mem_cP] at h3
    rw [Ideal.mem_comap, RingHom.coe_coe, hbar]
    exact h3
  have hne : l.Mb ≠ ⊥ := by
    intro h
    have h1 := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
    have h2 : (l.M : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
    exact h2 h1
  have hfin : {Q : HeightOneSpectrum (𝓞 D.host.E) | l.Mb ≤ Q.asIdeal}.Finite :=
    (Ideal.finite_factors (I := l.Mb) (by rwa [Ideal.zero_eq_bot])).subset fun Q hQ => Ideal.dvd_iff_le.2 hQ
  refine (GlobalTheory.GridIdem.exists_isIdemSum hfin.toFinset ?_ ?_).imp fun e he => ⟨hfin.toFinset, he, fun PP => hfin.mem_toFinset⟩
  · intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    refine GlobalTheory.Hk3.SplitMatch.exists_isIdemAt fun h => key Q hQ fun x hx => ?_
    rw [GlobalTheory.IdemSupport.mem_cP]
    have h4 : Formalism.DivisionValues.cO D.host.E x ∈ (Formalism.DivisionValues.conjPl Q).asIdeal := Ideal.mem_map_of_mem _ (hQ hx)
    rw [h] at h4
    exact h4
  · intro Q hQ Q' hQ' hu
    rw [Set.Finite.mem_toFinset] at hQ hQ'
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP hu with h | h
    · exact h
    · exact absurd (by rw [← h]; exact hQ) (key Q' hQ')

end GlobalTheory.SingleDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeSplitCm
section
open NumberField IsDedekindDomain Matrix Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.UG Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.TheRec GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitRealPrime

theorem exists_prime_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ p : ℕ, p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ w.asIdeal → IsSplitAt w := by
  intro E _ _ _
  obtain ⟨p, hp, -, hs⟩ := GlobalTheory.LargeSplitPrime.exists_splitsCompl E 0
  refine ⟨p, hp, fun w hw => ?_⟩
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hv : (p : 𝓞 (maximalRealSubfield E)) ∈ (w.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal
    rwa [map_natCast]
  obtain ⟨a, b, hab, ha, hb⟩ :=
    GlobalTheory.SplitPlace.isSplit_of_norm h2 hp (fun u hu => hs u.asIdeal u.isMaximal hu) _ hv
  by_cases h : a = w
  · exact ⟨b, fun e => hab (h.trans e.symm), HeightOneSpectrum.ext hb⟩
  · exact ⟨a, h, HeightOneSpectrum.ext ha⟩

end GlobalTheory.SplitRealPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableLatticePeriodsAcrisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semistable_lattice_periods_acris : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]), IsSst P (qRep ρ) → ∃ (N c₁ c₂ c₃ k₀ : ℕ) (F F' : Matrix (Fin d) (Fin d) (Wq l bk.a)) (X X' : Matrix (Fin d) (Fin d) (bk.S)) (Z Z' : Matrix (Fin d) (Fin d) (Per.Acris l)) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (Per.Acris l)), F * F' = (l : Wq l bk.a) ^ c₃ • (1 : Matrix (Fin d) (Fin d) (Wq l bk.a)) ∧ X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) ∧ Z * Z' = C.t ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) ∧ (C.t ^ N * (l : Per.Acris l) ^ c₁) • Z.map (phiA l) = phiA l C.t ^ N • (Z * F.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ∧ (∀ g : ↥(GK K), (C.t ^ N * (l : Per.Acris l) ^ k₀) • ((ρ g).val.map ((algebraMap (Ainf l) (Per.Acris l)).comp (algebraMap ℤ_[l] (Ainf l))) * Z.map (sigA (g : GQ l))) = sigA (g : GQ l) C.t ^ N • (Z * κ g)) ∧ (∀ g : ↥(GK K), bk.FixFlat g → κ g = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) ∧ (∀ i j, C.j ((Z * X.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l (2 * N)) ∧ (∀ i j, C.j ((X'.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) * Z') i j) ∈ Per.FilP l (2 * N)) ∧ ∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) (bk.S)), (∀ i j, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) (bk.S))) i j) ∧ ∀ (g : ↥(GK K)) i j, C.j ((κ g * (Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)).map (sigA (g : GQ l)) - (l : Per.Acris l) ^ k₀ • Λ.map ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev)) i j) ∈ Per.FilP l m := by
  first | (exact @GlobalTheory.SstPer.sst_periods) | (exact GlobalTheory.SstPer.sst_periods) | (intros; apply GlobalTheory.SstPer.sst_periods  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFull
section
noncomputable section

namespace GlobalTheory.LamTie.TrueList

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricRational
open GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.HeightCounting GlobalTheory.ToricDistribution

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_twL_full (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : RatioConj) (D : D7) (N : NData D.R D.host D.what₂)
    (hE : IsEmpty N.Loc) (T : TwR D.LL0 N) (Z : LamDat D) (hZ : Z.Ok)
    (art : Ideles D.host.E →* Gab D.host.E N.Om) (ha : IsGlobalArtin art)
    (κ : ∀ i, FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : ∀ i, Qbar (T.l i) ≃+* ℂ)
    (hκ : ∀ i (z : ℤ_[T.l i]), κ i (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
      algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i]))
    (hι : ∀ i (x : D.LL0), ι i (κ i (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hδ : ∀ i, IsGal art (κ i) (ι i) (Z.C.delAt (T.l i)) 0 (T.delta i))
    (hS : ∀ i P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ T.S0 i)
    (hT : ∀ a w, OverP D.host D.host.pde w ∨ OverP D.host D.host.pde' w → ∃ w', below w' = below w ∧ TeichTriv (Z.chi a) w') :
    ∃ (L : TwL T) (e : ∀ i, L.abelian₂ i ≃ Idx D.R),
      (∀ i lam, L.jL i lam = (e i lam).1.1 + 1 ∧ L.sideL i lam = (e i lam).2.2.2 ∧ L.s2 i lam = 2 * ((e i lam).2.2.1.1 : ℤ) ∧
        (∃ n r, IsGal art (κ i) (sideIso (ι i) (e i lam).2.2.2) (Z.lam0 (T.l i) (e i lam).1 (e i lam).2.1) n r ∧
          L.lamG i lam = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
        ∀ P, L.qs i lam P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) ∧
      ∀ F : TwF T, IsLamTieFull (T.ntw hE F L) Z := by
  let C : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j) :=
    ⟨Z.C.P, Z.C.W, Z.C.mu0, Z.C.eta, Z.C.chiPsi, Z.C.del, Z.C.del', Z.C.isMu0, Z.C.isEta, Z.C.isChi, Z.C.isDel, Z.C.isDel'⟩
  have hcu : ∀ i a P, P ∉ T.S0 i → (Z.chi a).UnrAt P := fun i a P hP => chi_unr hZ a fun h => hP (hS i P h)
  have hpD : ∀ i v, v ∈ T.pD i ↔ OverP D.host (if T.l i = D.host.pde then D.host.pde' else D.host.pde) v := fun i v => by
    rw [← Finset.mem_coe, T.pD_eq]; rfl
  have hlu : ∀ i j a P, P ∉ T.S0 i → (Z.lam0 (T.l i) j a).UnrAt P := fun i j a P hP =>
    (((Z.C.isMu0 j).unr P fun k hk => hP (T.placesOver_subset_exceptional i k hk)).mul
      ((inertialOrderFifteenChar_auxiliaryPrime_spec C (l := T.l i)).2.2.2.2.unr P fun hk => hP (T.primes_subset_exceptional i ((hpD i P).2 hk)))).mul (hcu i a P hP).inv
  choose K f f' hf hf' hK using fun i => exists_two_readings ((ι i).toRingHom.comp (κ i))
  have key := fun (i : T.Tw) (j a : Fin D.R.m) (b : Bool) =>
    hostHeckeFrame_toric_quotient_character C T.cc_cm ha (fun j τ => (D.hc _).e_int j) (T.l i) (T.O0 i) (T.twistBaseCoefficientRing_isAdic i) (κ i) (hκ i) (ι i) (K i)
      (K i).subtype (f i) (f' i) (hf i) (hf' i) (T.pD i) (T.pD_eq i) (T.delta i) (hδ i) (T.O i) (T.O_adic i) (T.O_l i) j b (Z.chi a) (Z.c a) (hZ.aux a).triv
      (by
        obtain ⟨n, hn, h⟩ := (hZ.aux a).inf
        have : n = fun τ => 2 * Z.c a τ := funext fun τ => by have := hn τ; beta_reduce at this; exact_mod_cast this
        exact this ▸ h)
      (fun v hv => by
        have h4 : OverP D.host D.host.pde v ∨ OverP D.host D.host.pde' v := by
          have := (hpD i v).1 hv
          split_ifs at this
          exacts [Or.inr this, Or.inl this]
        obtain ⟨w', e, h⟩ := hT a v h4
        exact chi_teich hZ a h4 e h)
      (valuesIn_of_unitary (hK i) (Z.C.isMu0 j).unitary (hμ i j))
      (valuesIn_of_unitary (hK i) (delAt_unitary_triv Z.C _).1 (valuesIn_of_isGal ha (hδ i)))
      (valuesIn_of_unitary (hK i) (hZ.aux a).unitary (hχ i a)) (T.S0 i) (T.twistExcludedPlaces_contains_residueChar i) (T.placesOver_subset_exceptional i) (T.primes_subset_exceptional i) (hcu i a)
  choose r g Xv h1 h2 h3 h4 h5 h6 h7 using key
  let L : (∀ i Q, Idx D.R → T.RCG i Q → FractionRing (T.O i)) → TwL T := fun th =>
    { abelian₂ := fun _ => Idx D.R
      jL := fun _ x => x.1.1 + 1
      sideL := fun _ x => x.2.2.2
      s2 := fun _ x => 2 * (x.2.2.1.1 : ℤ)
      jL_range := fun _ x => ⟨by omega, x.1.2⟩
      lamG := fun i x => g i x.1 x.2.1 x.2.2.2
      lamG_cont := fun i x => h3 i _ _ _
      lamG_unr := fun i x => h4 i _ _ _
      lamG_pD := fun i x => h5 i _ _ _
      lamG_anti := fun i x => h6 i _ _ _
      Xv := fun i x => Xv i x.1 x.2.1 x.2.2.2
      Xv_def := fun i x P hP => h7 i _ _ _ P hP _ (N.plOm.2 P)
      qs := fun i x P => ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-(x.2.2.1.1 : ℤ))
      qs_sq := fun i x P _ => by rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
      qs_conj := fun i x P P' h => by
        rw [show Ideal.absNorm P'.asIdeal = Ideal.absNorm P.asIdeal from GlobalTheory.TwistDet.normV_conj h]
      th := th }
  have hcl : ∀ th i (x : Idx D.R), (L th).jL i x = x.1.1 + 1 ∧ (L th).sideL i x = x.2.2.2 ∧
      (L th).s2 i x = 2 * (x.2.2.1.1 : ℤ) ∧
      (∃ n r, IsGal art (κ i) (sideIso (ι i) x.2.2.2) (Z.lam0 (T.l i) x.1 x.2.1) n r ∧
        (L th).lamG i x = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
      ∀ P, (L th).qs i x P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-(x.2.2.1.1 : ℤ)) := fun th i x => by
    refine ⟨rfl, rfl, rfl, ?_, fun _ => rfl⟩
    obtain ⟨n, hn⟩ := h1 i x.1 x.2.1 x.2.2.2
    exact ⟨n, _, hn, h2 i _ _ _⟩
  rcases isEmpty_or_nonempty (TwF T) with hF | ⟨⟨F₀⟩⟩
  · exact ⟨L fun _ _ _ _ => 0, fun _ => Equiv.refl _, hcl _, fun F => hF.elim F⟩
  let X₀ := T.ntw hE F₀ (L fun _ _ _ _ => 0)
  choose ι₀ hι₀ using fun i => exists_reading X₀ i (κ i) (ι i) (hκ i)
  have m0 : ∀ i, (∀ x : D.LL0, ι₀ i (D.what₂.embLL (x : D.what₂.LL)) = toBar X₀ i (T.emb0 i x)) ∧
      ∀ x : Idx D.R, IsLam X₀ Z i (atSide X₀ x.2.2.2 (ι₀ i)) x x.1 x.2.1 x.2.2.1.1 := fun i => by
    refine ⟨fun x => by rw [← hι i x]; exact hι₀ i true _, fun x => ⟨rfl, ⟨rfl, ?_, ?_⟩, fun P hP => ?_⟩⟩
    · exact_mod_cast x.2.2.1.2.1
    · exact_mod_cast x.2.2.1.2.2
    · obtain ⟨n, hn⟩ := h1 i x.1 x.2.1 x.2.2.2
      exact xv_mul_val X₀ i (hι₀ i x.2.2.2) ha hn (h2 i _ _ _) hP (hlu i _ _ P hP)
  have hL : ToricSumFormula := GlobalTheory.T.toric_sum_eq_hecke_L_value_mul_auxiliary_factors exists_isHeckeL_of_hasInf
  have tkey : ∀ i (x : Idx D.R), ∃ t : ∀ Q, T.RCG i Q → FractionRing (T.O i),
      ∀ th : ∀ i Q, X₀.abelian₂ i → X₀.RCG i Q → FractionRing (X₀.O i), (∀ Q, th i Q x = t Q) →
        IsThOf (setTh X₀ th) i (atSide X₀ x.2.2.2 (ι₀ i)) x (phi D.host) x.2.2.1.1 (Z.kap x.1 x.2.1 x.2.2.1.1)
          (cond0 D.host Z.w0) (Z.lam0 (T.l i) x.1 x.2.1) := fun i x => by
    have hl := (m0 i).2 x
    have hD := GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (T.l i) x.1 x.2.1 x.2.2.1.1 (by exact_mod_cast hl.2.1.2.1) hl.2.1.2.2
    exact exists_th_of hA hR hL (atSide_emb_mem (m0 i).1 _) hD (hS i) hl.2.2
  choose t ht using tkey
  let th : ∀ i Q, Idx D.R → T.RCG i Q → FractionRing (T.O i) := fun i Q x => t i x Q
  refine ⟨L th, fun _ => Equiv.refl _, hcl th, fun F => ?_⟩
  refine isLamTieFull_of_labels (fun _ x => x.1) (fun _ x => x.2.1) (fun _ x => x.2.2.1.1) (fun i _ => hS i)
    (fun i _ => ⟨ι₀ i, (m0 i).1, fun x => ⟨(m0 i).2 x, ht i x th fun _ => rfl⟩⟩)
    (fun i _ j a s b hs hs' => ⟨(j, a, ⟨s, hs, hs'⟩, b), rfl, rfl, rfl, rfl⟩)

end GlobalTheory.LamTie.TrueList
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltrationJumpsBreuilKisinSubsetGaloisJumpsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filtration_jumps_breuilKisin_subset_galoisJumps : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ U : Set ℤ, (∀ τ, JumpsInV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ τ U) → P.jumps ⊆ U := by
  first | exact @GlobalTheory.JumpsOfM.main | exact GlobalTheory.JumpsOfM.main | (intros; apply GlobalTheory.JumpsOfM.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IdemFin

theorem toEAf_mem_intAf_of_idem : ∀ {D : D7} {e : AE D}, e * e = e → toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  intro D e he
  have h1 : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he]
  exact GlobalTheory.LevSplit.swapAE_int (GlobalTheory.AdIdem.idempotent_mem_intAE D _ h1)

end GlobalTheory.IdemFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedAlgebraicOfLimitOfFixedElementsStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_algebraic_of_limit_of_fixed_elements : ∀ (K : Type) [Field K] [CharZero K] (B : ValuationSubring K) (τ : K ≃+* K), (∀ z, τ z ∈ B ↔ z ∈ B) → ∀ y : K, IsAlgebraic ℚ y → (∀ δ : K, δ ≠ 0 → ∃ u : K, τ u = u ∧ B.valuation (y - u) < B.valuation δ) → τ y = y := by
  first | exact @GlobalTheory.FixApprox.fix_of_approx | exact GlobalTheory.FixApprox.fix_of_approx | (intros; apply GlobalTheory.FixApprox.fix_of_approx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedVectorCoefficientLeftInvariantLevelGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedVectorCoefficient_left_invariant_levelGroup : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i t, LevFix R i t → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ k ∈ levW R i, ∀ g, coef R i t μ 𝓕 (k * g) = coef R i t μ 𝓕 g := by
  first | exact @GlobalTheory.RawLift.CoefLeft.coef_lev_mul | exact GlobalTheory.RawLift.CoefLeft.coef_lev_mul | (intros; apply GlobalTheory.RawLift.CoefLeft.coef_lev_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockMinorProductEqSignDualWeylExtremalVectorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockMinorProduct_eq_sign_dualWeylExtremalVector : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∃ s : ℤˣ, ∀ x, harmFn m w B (w.delta m) x = ((s : ℤ) : ℂ) * coefFn (RingHom.id ℂ) w.lam (ten fun τ => extremal ℂ n (w.lam τ)) (B⁻¹ * x) := by
  first | exact @GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta | exact GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta | (intros; apply GlobalTheory.ExportSeries.DeltaExtremal.harmFn_delta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatrixReductionEqOfHalfIdempotentSubset
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open scoped TensorProduct

namespace GlobalTheory.RedHalfDrop

variable {D : D7}

theorem toEAf_cA_sig (a : AE D) :
    toEAf D (cA D a) = Formalism.UG.sigR D.sp.cm.sig (Af D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add, ha, hb]
  | tmul y e => rfl

theorem int_idemAt {P : Finset (Pl D.host.E)} (h : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    toEAf D (idemAt PP) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨hu, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ PP (h.isIdemAt hPP)
  exact hu

theorem int_cA_idemAt {P : Finset (Pl D.host.E)} (h : SplitSet P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    toEAf D (cA D (idemAt PP)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [toEAf_cA_sig]
  exact GlobalTheory.ResConjPlace.conj_mem_int _ (int_idemAt h hPP)

theorem resS_eq_zero_of_mul {e a : AE D} {PP : Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (ha : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h0 : e * a = 0) :
    resS D.host.F PP ⟨toEAf D a, ha⟩ = 0 := by
  obtain ⟨hu, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D e PP he
  have hm : (⟨toEAf D e, hu⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) *
      ⟨toEAf D a, ha⟩ = 0 :=
    Subtype.ext (by show toEAf D e * toEAf D a = 0; rw [← map_mul, h0, map_zero])
  have h2 := congrArg (resS D.host.F PP) hm
  rwa [map_mul, h1, one_mul, map_zero] at h2

theorem subring_hom_dite_sub_mul_eq_of_kernel {R k : Type} [CommRing R] [CommRing k] (O : Subring R) (f : O →+* k) (x c : R) (hx : x ∈ O)
    (hc : c ∈ O) (h0 : f ⟨c, hc⟩ = 0) [Decidable (x - c * x ∈ O)] [Decidable (x ∈ O)] :
    (if h : x - c * x ∈ O then f ⟨x - c * x, h⟩ else 0) = if h : x ∈ O then f ⟨x, h⟩ else 0 := by
  have hm : x - c * x ∈ O := sub_mem hx (mul_mem hc hx)
  rw [dif_pos hm, dif_pos hx]
  have e : (⟨x - c * x, hm⟩ : O) = ⟨x, hx⟩ - ⟨c, hc⟩ * ⟨x, hx⟩ := rfl
  rw [e, map_sub, map_mul, h0, zero_mul, sub_zero]

theorem redM_sub_smul (PP : Pl D.host.E) {b a : ℕ} {N : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) {c : EAf D}
    (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (h0 : resS D.host.F PP ⟨c, hc⟩ = 0) :
    redM PP (N - c • N) = redM PP N := by
  ext i j
  unfold redM
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact subring_hom_dite_sub_mul_eq_of_kernel _ (resS D.host.F PP) _ _ (hN i j) hc h0

theorem frMapO_smul_eq {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (x : WO S T) : frMapO S T βS βT (e • x) = toEAf D e • frMapO S T βS βT x := by
  unfold frMapO
  have : (e • x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • x.map (toEAf D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul_eq {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (x : WO S T) : frMapAdj S T βS βT (e • x) = toEAf D (cA D e) • frMapAdj S T βS βT x := by
  unfold frMapAdj
  have h1 : ((e • x : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) =
      cA D e • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  have h2 : ∀ M : Matrix (Fin S.rank) (Fin T.rank) (AE D),
      (cA D e • M).map (toEAf D) = toEAf D (cA D e) • M.map (toEAf D) :=
    fun M => Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul]
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

theorem redM_drop : ∀ {D : D7} {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) {Pg Qa Qb : Finset (Pl D.host.E)}, PlacesOK Pg Qa → Qb ⊆ Qa → ∀ {x : WO S T}, IsHalf (halfIdem Pg Qa) x → IsIntM (frMapAdj S T βS βT x) → IsIntM (frMapO S T βS βT x) → (∀ PP ∈ Pg, redM PP (frMapAdj S T βS βT x) = redM PP (frMapAdj S T βS βT (halfIdem Pg Qb • x))) ∧ (∀ PP ∈ Qb, redM PP (frMapO S T βS βT x) = redM PP (frMapO S T βS βT (halfIdem Pg Qb • x))) := by
  intro D S T βS βT Pg Qa Qb hP hQ x hx h1 h2
  obtain ⟨P, hPg, hQa, hS⟩ := hP.split
  have hab : halfIdem Pg Qa = halfIdem Pg Qb + idem (Qa \ Qb) := by
    unfold halfIdem idem
    rw [← Finset.sum_sdiff hQ]
    ring
  have hxx : (halfIdem Pg Qb + idem (Qa \ Qb)) • x = x := by
    rw [← hab]
    ext i j
    exact hx i j
  have hsub : ∀ P' ∈ Qa \ Qb, P' ∈ P := fun P' hP' => hQa (Finset.sdiff_subset hP')
  constructor
  · intro PP hPP
    have e1 := frMapAdj_smul_eq βS βT (halfIdem Pg Qb + idem (Qa \ Qb)) x
    rw [hxx, map_add, map_add, add_smul] at e1
    have e2 : frMapAdj S T βS βT (halfIdem Pg Qb • x) =
        frMapAdj S T βS βT x - toEAf D (cA D (idem (Qa \ Qb))) • frMapAdj S T βS βT x := by
      rw [frMapAdj_smul_eq]
      exact eq_sub_of_add_eq e1.symm
    have hint : toEAf D (cA D (idem (Qa \ Qb))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      unfold idem
      rw [map_sum, map_sum]
      exact sum_mem fun P' hP' => int_cA_idemAt hS (hsub P' hP')
    have hz : resS D.host.F PP ⟨_, hint⟩ = 0 := resS_eq_zero_of_mul (hS.isIdemAt (hPg hPP)) hint (by
      unfold idem
      rw [map_sum, Finset.mul_sum]
      exact Finset.sum_eq_zero fun P' hP' => hS.mul_conj (hPg hPP) (hsub P' hP'))
    rw [e2, redM_sub_smul PP h1 hint hz]
  · intro PP hPP
    have e1 := frMapO_smul_eq βS βT (halfIdem Pg Qb + idem (Qa \ Qb)) x
    rw [hxx, map_add, add_smul] at e1
    have e2 : frMapO S T βS βT (halfIdem Pg Qb • x) =
        frMapO S T βS βT x - toEAf D (idem (Qa \ Qb)) • frMapO S T βS βT x := by
      rw [frMapO_smul_eq]
      exact eq_sub_of_add_eq e1.symm
    have hint : toEAf D (idem (Qa \ Qb)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      unfold idem
      rw [map_sum]
      exact sum_mem fun P' hP' => int_idemAt hS (hsub P' hP')
    have hz : resS D.host.F PP ⟨_, hint⟩ = 0 := resS_eq_zero_of_mul (hS.isIdemAt (hQa (hQ hPP))) hint (by
      unfold idem
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun P' hP' => hS.mul_eq_zero (hQa (hQ hPP)) (hsub P' hP')
        fun e => (Finset.mem_sdiff.1 hP').2 (e ▸ hPP))
    rw [e2, redM_sub_smul PP h2 hint hz]

end GlobalTheory.RedHalfDrop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalLemmaLatticeFrobFixedForallDegreeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamentalLemmaLatticeFrobFixed_forall_degree : ∀ r : ℕ, FLAt r := by
  first | exact @GlobalTheory.PMon.flAt_all | exact GlobalTheory.PMon.flAt_all | (intros; apply GlobalTheory.PMon.flAt_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisClassOfMonodromyEqZeroStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisClass_of_monodromy_eq_zero : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat ↥(OL LL) ↥LL.1 l e a ι η H) (T : QLat LL) (R : GalDat (thetaW a LL) ϖ (sQ l) D T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → η < H → 8 * H + 1 < l → ∀ y ∈ D.Y, D.Mon y = 0 → ∀ c : ℕ, (l : ↥LL.1) ^ c • D.zeta y ∈ D.MM → ∃ κ₁ ∈ latticeFiniteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.L, R.ClassOf ((l : ↥LL.1) ^ c • y) κ₁ := by
  first | exact @GlobalTheory.BKGal.classOf_of_mon_eq_zero | exact GlobalTheory.BKGal.classOf_of_mon_eq_zero | (intros; apply GlobalTheory.BKGal.classOf_of_mon_eq_zero <;> assumption)
end

