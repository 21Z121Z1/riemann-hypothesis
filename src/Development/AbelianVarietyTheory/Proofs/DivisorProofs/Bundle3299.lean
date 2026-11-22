import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3285
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulCoeffIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationAdjointEndomorphismsCommute
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3286
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0116
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceLatticeLeSpanThetaSeriesAwayFromOwnPrime
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompareOff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Formalism.HermitianLatticesTheory (localization₂)

theorem mem_localization_iff {Rr W : Type} [CommRing Rr] [AddCommGroup W] [Module Rr W] (p : Ideal Rr) [p.IsPrime]
    (L : Submodule Rr W) (x : W) : x ∈ localization₂ p L ↔ ∃ s : Rr, s ∉ p ∧ s • x ∈ L :=
  ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩, fun ⟨s, hs, h⟩ => ⟨s, hs, h⟩⟩

theorem localization_le_of_le_localization' {Rr W : Type} [CommRing Rr] [AddCommGroup W] [Module Rr W] (p : Ideal Rr) [p.IsPrime]
    (L M : Submodule Rr W) (h : L ≤ localization₂ p M) : localization₂ p L ≤ localization₂ p M := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_localization_iff p L x).1 hx
  obtain ⟨t, ht, hy⟩ := (mem_localization_iff p M _).1 (h hx)
  refine (mem_localization_iff p M x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases Ideal.IsPrime.mem_or_mem ‹p.IsPrime› hm with h1 | h1
  · exact ht h1
  · exact hs h1

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] (lam : HeightOneSpectrum (𝓞 K)) {p : ℕ} (hp : p.Prime)
    (hne : Formalism.EigenvalueLevelCeiling.plc lam ≠ p) : ((p : 𝓞 K)) ∉ lam.asIdeal := by
  intro hm
  haveI : lam.asIdeal.IsPrime := lam.isPrime
  have h0 : ((p : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hm
  have hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ p := ringChar.dvd h0
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact CharP.ringChar_ne_one h1
  · exact hne h1

theorem splitOffBad_of_mul {D : D7} {V : HSp D} {a b : ℕ} {h : GA D V} (H : SplitOffBad V (a * b) h) : SplitOffBad V a h := by
  obtain ⟨h1, e, P, h2, h3, h4⟩ := H
  refine ⟨h1, e, P, h2, fun PP hPP hm => h3 PP hPP ?_, h4⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hm

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem singleSeries_transl (R : RealDat D A Ks) (i : Fin D.R.m) {ξ χ ξR Q ω φ} (hK : KerDat R i ξ χ ξR Q ω φ)
    {k : GA D (Vc D i)} (hk : k ∈ GfC (Vc D i)) (c : ℂ) (h : GA D (Vc D i)) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    singleSeries R i ω (c • ω (k, 1) φ) h w v = c • singleSeries R i ω φ (h * k) w v := by
  funext g
  have hθ : IsInfFam R.θ := hK.vec.1.2.inf
  have hth := GlobalTheory.VecTheta.isThetaFunO_thPVec hK.vec
  simp only [singleSeries, Datum.thetaKO, Pi.smul_apply]
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ ω hK.weil R.θ hθ k hk 1
    (one_mem _) _ _ _ _ φ _ hth, map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem compareOffOwn_run : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ), CompareOffOwn hT.p fw i ℓ U ψ 1 v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hPins hβ hLU hIo hRow hPh hCS v hv hmu hQG hFO hVal hξ hMb hRun ℓ hLev hAct U hdetU ψ
  intro lam hlam
  refine localization_le_of_le_localization' _ _ _ (Submodule.span_le.2 ?_)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, s, f', Λ, h, N, x₀, P, x, hs, hsf, hSplit, hLat, hΛlam, hUni, hTriv, hTrivM, hLevN, hAdm, hP, hx⟩ :=
    GlobalTheory.T.exists_orbit_family_adapted_lattice_split_support D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins ℓ U lam f hf
  obtain ⟨y, s', hy, hs', hyLat⟩ := GlobalTheory.HarmInCoef.harm_mem_coefLat D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins Λ h (splitOffBad_of_mul hSplit) hLat lam hΛlam P hP
  obtain ⟨ω, φ, hBase⟩ := GlobalTheory.OnCmp.exists_baseKernel D G Pl0 T0 A T.J.Q.c.F R F hC i v hv hmu
  obtain ⟨χ, ξR, hKer⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel D G Pl0 T0 A T.J.Q.c.F R F hC i v hv hmu ω φ hBase
  have hEx := GlobalTheory.T.trace_shortSeries_eq_mul_adelicSeries D G Pl0 T0 A T R F κ v₀ fw O hT hC i hPins hβ hLU hIo hRow hPh hCS v hv hmu
    hQG hFO hVal hξ hMb hRun ℓ hLev hAct U hdetU ψ
  obtain ⟨y₀, c, hy₀, hcInt, hSer⟩ :=
    hEx χ ξR ω φ hKer Λ h hSplit hLat N x₀ P x f' y hUni hTriv hTrivM hLevN hAdm hP hx hy
  obtain ⟨φ', hVec, k, hk, c', m, hφ', hpc, -, hc'0, hLatk⟩ := GlobalTheory.T.freeLowerBlockVector_eq_translate_kernelDatum D G Pl0 T0 A T.J.Q.c.F R F hC i _ χ ξR _ ω φ hKer
    (ownAt D v) (fun PP hPP => by classical exact (Finset.mem_filter.1 hPP).2) hξ hVal y₀ hy₀
  obtain ⟨s'', hs'', hs''c⟩ := hcInt lam hΛlam
  obtain ⟨g', hg'⟩ : ∃ g', g' = ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f' u) := ⟨_, rfl⟩
  rw [← hg'] at hSer
  have hp : (ownAt D v).Prime := by
    rcases hFO.own with e | e <;> rw [e]
    exacts [D.host.pde_prime, D.host.pde'_prime]
  have hpl : ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ∉ lam.asIdeal := natCast_not_mem lam hp hlam
  have hA : ((s : ℕ) : D.what₂.LL) • (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) =
      algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) • g' := by
    classical
    have e1 : ∀ u, ((s : ℕ) : D.what₂.LL) • cuspTo hT.p fw i (f u) =
        algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) • cuspTo hT.p fw i (f' u) := by
      intro u
      have e2 : ((s : ℕ) : T.J.Q.c.F) • (show ↥(cutR T.J.C ((i : ℕ) + 1) (κ i)) from f u) =
          (show T.J.Q.c.F from (a : T.Q.c.F)) • (show ↥(cutR T.J.C ((i : ℕ) + 1) (κ i)) from f' u) :=
        Subtype.ext (hsf u)
      have e3 := congrArg (cutTo fw i) e2
      rw [map_smul, map_smul] at e3
      rw [← algebraMap_smul D.what₂.LL ((s : ℕ) : T.J.Q.c.F), ← algebraMap_smul D.what₂.LL (show T.J.Q.c.F from (a : T.Q.c.F)),
        map_natCast] at e3
      exact e3
    rw [hg', finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_comm, e1 u, smul_comm]
  have hdet : ∀ x : Fin (R.nW i) → D.what₂.LL,
      (∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i x (fun ρ => w ρ) = 0) → x = 0 := by
    intro x hx
    have h4 : (R.FW i).j (sg0 D A) x = 0 := by
      obtain ⟨u, hu, -⟩ := hIo i
      exact GlobalTheory.TraceIncl.eq_of_low (R := R) (i := i) hC.models.HW ⟨u, hu⟩
        (x := (R.FW i).j (sg0 D A) x) (y := 0) fun w => by rw [map_zero]; exact hx w
    by_contra hne
    exact ((hLU i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 hne)).ne_zero 0 h4
  by_cases hc : c = 0
  · have hz : g' = 0 := hdet g' fun w => by rw [hSer φ' hVec w, hc, map_zero, zero_smul]
    refine (mem_localization_iff _ _ _).2 ⟨(s : 𝓞 D.what₂.LL), hs, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.what₂.LL, hA, hz, smul_zero]
    exact zero_mem _
  · have hs'n : s' ≠ 0 := by
      rintro rfl
      exact hs' (by simp)
    have hs'0 : (s' : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hs'n
    have hp0 : ((ownAt D v : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    have hc0 : c ≠ 0 := hc
    have hce : D.what₂.embLL c ≠ 0 := (map_ne_zero _).2 hc
    have hce' : D.what₂.embLL c' ≠ 0 := (map_ne_zero _).2 hc'0
    obtain ⟨e, he⟩ : ∃ e, e = (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (c * c')⁻¹) • g' := ⟨_, rfl⟩
    have hmem : e ∈ thetaBase R i U ψ 1 v (ownAt D v) := by
      refine Submodule.subset_span ⟨ω, φ, hKer.isKernel, h * k, mul_mem hSplit.1 hk,
        ((ownAt D v : ℂ)) ^ m • ((s' : ℂ) • (O i).c0' y), hLatk h hSplit.1 _ hyLat, fun w => ?_⟩
      rw [he, adForm_smul, MultilinearMap.smul_apply, hSer φ' hVec w, hφ', singleSeries_transl R i hKer hk,
        singleSeries_smul, singleSeries_smul, map_smul, map_smul, map_smul, one_smul, smul_smul, smul_smul, smul_smul]
      congr 1
      simp only [map_mul, map_inv₀, map_pow, map_natCast]
      field_simp
    have hgg : g' = (c * c' * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL))⁻¹) • e := by
      rw [he, smul_smul]
      conv_lhs => rw [← one_smul D.what₂.LL g']
      congr 1
      field_simp
    have hint : IsIntegral ℤ (algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) *
        (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c')) :=
      ((RingOfIntegers.isIntegral_coe a).algebraMap.mul hs''c).mul hpc
    have hpr := lam.isPrime
    have ht : ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal := by
      simp only [Ideal.IsPrime.mul_mem_iff_mem_or_mem hpr, not_or]
      exact ⟨⟨⟨⟨fun h1 => hpl (hpr.mem_of_pow_mem _ h1), fun h1 => hpl (hpr.mem_of_pow_mem _ h1)⟩, hs'⟩, hs''⟩, hs⟩
    refine (mem_localization_iff _ _ _).2 ⟨_, ht, ?_⟩
    have key : (((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL)) •
        (∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo hT.p fw i (f u)) =
        (⟨_, hint⟩ : 𝓞 D.what₂.LL) • e := by
      rw [← algebraMap_smul D.what₂.LL, ← algebraMap_smul D.what₂.LL (⟨_, hint⟩ : 𝓞 D.what₂.LL)]
      have et : algebraMap (𝓞 D.what₂.LL) D.what₂.LL
          (((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * ((ownAt D v : ℕ) : 𝓞 D.what₂.LL) ^ m * (s' : 𝓞 D.what₂.LL) * s'' * (s : 𝓞 D.what₂.LL)) =
          ((ownAt D v : ℕ) : D.what₂.LL) ^ m * ((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (s'' : D.what₂.LL) *
            (s : D.what₂.LL) := by
        simp
      have hsc : ((ownAt D v : ℕ) : D.what₂.LL) ^ m * ((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL) * (s'' : D.what₂.LL) *
          (algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * (c * c' * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * (s' : D.what₂.LL))⁻¹)) =
          algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c') := by
        field_simp
      rw [et, mul_smul, hA, hgg, smul_smul, smul_smul]
      congr 1
      show _ = algebraMap T.Q.c.F D.what₂.LL (a : T.Q.c.F) * ((s'' : D.what₂.LL) * c) * (((ownAt D v : ℕ) : D.what₂.LL) ^ m * c')
      rw [← hsc]
      ring
    rw [key]
    exact Submodule.smul_mem _ _ hmem

end GlobalTheory.CompareOff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBaseChangeCompletedLocalAbelianLocStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_baseChange_completedLocal_abelianLocus : ∀ (Z : Scheme.{0}) (G₀ : Over Z) [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G₀ → ∀ (L : LB G₀.left) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (ξ : Sp R ⟶ Z) [IsCommMonObj ((Over.pullback ξ).obj G₀)] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A ((Over.pullback ξ).obj G₀)), LBIso U.LG.L (L.pull (pullback.fst G₀.hom ξ)) → (∀ y, PsiUnitOn D.toPre y (ξ ⁻¹' abLocus G₀)) → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ ψ : R →+* V, IsLocalHom ψ → (∀ w, (jK V ≫ spMap ψ ≫ ξ) w ∈ abLocus G₀) → ∃ (G' : Over (Sp V)) (_ : GrpObj G') (_ : IsCommMonObj G') (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (gm : G'.left ⟶ G₀.left) (ι : D.toPre.X ≃+ D'.toPre.X), IsSemiAbelian G' ∧ IsGrpPullback G' G₀ (spMap ψ ≫ ξ) gm ∧ LBIso U'.LG.L (L.pull gm) ∧ CoordMap D.toPre D'.toPre ψ ι.toAddMonoidHom ∧ ∀ f : G₀ ⟶ G₀, IsMonHom f → ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ f.left ∧ ∀ m m', EndChar U ((Over.pullback ξ).map f) m → EndChar U' f' m' → ∀ y, ι (m y) = m' (ι y) := by
  first | exact @GlobalTheory.Poinc.Eq8.PullComplete.main | exact GlobalTheory.Poinc.Eq8.PullComplete.main | (intros; apply GlobalTheory.Poinc.Eq8.PullComplete.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackDvrTorsionPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

open GlobalTheory.TorusExt GlobalTheory.Balanced

attribute [local instance] gtGroup

set_option maxHeartbeats 2000000 in

theorem pull_unif_tors : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f : R →+* V, Function.Injective f → J.map f ≤ maximalIdeal V → ∃ (D : DegData V (maximalIdeal V)) (hD : IsPullDeg f D₀.toPre D.toPre) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A ((Over.pullback (specOf f)).obj G₀)), IsSemiAbelian ((Over.pullback (specOf f)).obj G₀) ∧ IsPullUnif f hD (Iso.refl _) U₀ U ∧ ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (j : F₀ →+* F), Ext f j → ∀ k : ℕ, 1 ≤ k → ∀ (p₀ : QkPt D₀.toPre F₀ k) (x₀ : TFK (R := R) F₀ ⟶ A₀.A), QkToAkU U₀.toUnifPre F₀ k p₀ x₀ → ∃ (p : QkPt D.toPre F k) (x : TFK (R := V) F ⟶ A.A), p.y = hD.xe.symm p₀.y ∧ Tr f hD j p₀.g p.g ∧ QkToAkU U.toUnifPre F k p x ∧ x.left ≫ U.gen.inv.left ≫ pullback.fst ((Over.pullback (specOf f)).obj G₀).hom (jK V) ≫ pullback.fst G₀.hom (specOf f) = spMap j ≫ x₀.left ≫ U₀.gen.inv.left ≫ pullback.fst G₀.hom (jK R) := by
  intro R _ _ _ J hR D₀ A₀ G₀ _ _ U₀ hG V _ _ _ _ hV f hf hJ
  have hL := GlobalTheory.firstFiveLaws
  have hR' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV⟩
  obtain ⟨D, hD, A, U, hG', hU, hpt, -⟩ := GlobalTheory.T.uniformisation_endomorphisms_to_complete_dvr hL R J hR D₀ A₀ G₀ hG U₀ V f hV hf hJ
  refine ⟨D, hD, A, U, hG', hU, ?_⟩
  intro F₀ _ _ _ F _ _ _ j hj k hk p₀ x₀ hx₀
  letI : Algebra (FractionRing R) F := (j.comp (algebraMap (FractionRing R) F₀)).toAlgebra
  let σ : F₀ →ₐ[FractionRing R] F := { j with commutes' := fun _ => rfl }
  have hB := D₀.tau_bimult
  have hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) =
      algebraMap (FractionRing V) F (algebraMap V _ (f r)) := hj
  let p₁ : QkPt D₀.toPre F k := qkExt hB σ.toRingHom (hom_comp σ) p₀
  let x₁ : TFK (R := R) F ⟶ A₀.A := extPt σ x₀
  have hx₁ : QkToAkU U₀.toUnifPre F k p₁ x₁ := (GlobalTheory.T.qkToAkU_iff_galois_equivariant hL R J hR D₀ A₀ G₀ hG U₀ F₀ F σ k hk p₀ p₁ x₀ x₁
    ((qkExt_iff hB _ (hom_comp σ) _ _).2 rfl) rfl).1 hx₀
  obtain ⟨ex, -, io, ns⟩ := hpt F hF
  obtain ⟨g, hg, -⟩ := ex p₁.g
  let p : QkPt D.toPre F k := ⟨hD.xe.symm p₁.y, g, by
    obtain ⟨s, h1, h2⟩ := p₁.eq
    obtain ⟨s', hs', -⟩ := ex s
    exact ⟨s', (ns k _ _ _ _ hg hs').1 h1, (io _ _ _ hs').1 (by rwa [AddEquiv.apply_symm_apply])⟩⟩
  obtain ⟨x, hx⟩ := exists_toG_pull f U₀.toUnifPre U.toUnifPre hF x₁
  refine ⟨p, x, rfl, ⟨p₁.g, (eq_gtExt_iff σ.toRingHom (hom_comp σ) _ _).1 rfl, hg⟩, ?_, ?_⟩
  · exact hL.2.2.2.2.qkBaseChange R V J _ hR hR' f D₀ A₀ G₀ U₀ _ (Iso.refl _) (inferInstanceAs (IsMonHom (𝟙 _))) A D
      hD U hU F hF k hk p₁ x₁ p x rfl hg
      (by simpa only [toG, Category.assoc, Iso.refl_hom, Over.id_left, Category.id_comp] using hx) hx₁
  · simpa only [toG, Category.assoc, x₁, extPt, Over.homMk_left] using hx

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointExtendsAlongThetaMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedPoint_extends_along_thetaMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (m n : ℕ) (f : Xo.XF c ⟶ PSpace o n), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig m (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ b : o →+* c.F, f ≫ PSpace.str o n = pullback.snd _ _ ≫ spMap b → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)), Nonempty (PELUnif (IsLocalRing.maximalIdeal R) t) → ∀ y : Sp (FractionRing R) ⟶ Xo.XF c, GenOf Xo c y t → ∀ σ : Sp R ⟶ Sp o, jK R ≫ σ = y ≫ pullback.snd _ _ ≫ spMap b → ∃ ξ : Sp R ⟶ PSpace o n, jK R ≫ ξ = y ≫ f ∧ ξ ≫ PSpace.str o n = σ := by
  first | exact @GlobalTheory.UMin.ExtP.extend_theta | exact GlobalTheory.UMin.ExtP.extend_theta | (intros; apply GlobalTheory.UMin.ExtP.extend_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VeryAmplePowerOfExtensionGenericFibreAbelianMode
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ModelAmple

theorem exists_relAmple (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (G : Over (Sp W))
    [GrpObj G] (hG : IsAbelianScheme G) : ∃ L : LB G.left, L.IsLB ∧ Out.RelAmple G L := by
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := eSec G (IsLocalRing.closedPoint W)) trivial
  have he : eSec G ≫ G.hom = 𝟙 _ := by
    simpa [eSec] using Over.w η[G]
  refine GlobalTheory.ProjNormal.exists_relAmple_of_affine W G hG V hV fun s => ⟨eSec G s, ?_, ?_⟩
  · have hsp : (s : PrimeSpectrum W) ⤳ IsLocalRing.closedPoint W :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal s.2.ne_top)
    exact (hsp.map (eSec G).continuous).mem_open V.isOpen hx
  · rw [← Scheme.Hom.comp_apply, he]
    rfl

end GlobalTheory.ModelAmple

namespace GlobalTheory.ModelAmple

theorem exists_generating_sq (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K']
    [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G] (hG : IsAbelianScheme G) (N : LB G.left)
    (hN : N.IsLB) (σ : (N.pull (pullback.fst G.hom (spMap (algebraMap W K')))).Sec) (hσ : ∃ j, σ.f j ≠ 0) :
    ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (GlobalTheory.AbLaw.pw N 2)), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hK := IsPullback.of_hasPullback G.hom (spMap (algebraMap W K'))
  have hk := IsPullback.of_hasPullback G.hom (spMap (IsLocalRing.residue W))
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hK
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hk
  obtain ⟨-, ⟨t, -, a, x, hx, hxa⟩, -⟩ := GlobalTheory.DvrModel.existsUnique_zpow_mul_sec hK hk hϖ hN σ hσ
  let F := AlgebraicClosure K'
  obtain ⟨O, hO, hloc⟩ := IsLocalRing.exists_factor_valuationRing ((algebraMap K' F).comp (algebraMap W K'))
  let g : W →+* O := ((algebraMap K' F).comp (algebraMap W K')).codRestrict O.toSubring hO
  have : IsLocalHom g := hloc
  have hg : Function.Injective g := fun a b e =>
    IsFractionRing.injective W K' ((algebraMap K' F).injective (congrArg Subtype.val e))
  have hflat : g.Flat := by
    letI := g.toAlgebra
    have : Module.IsTorsionFree W O := Module.isTorsionFree_iff_algebraMap_injective.2 hg
    exact (inferInstance : Module.Flat W O)
  have : Surjective (spMap g) := by
    letI := g.toAlgebra
    have : Module.Flat W O := hflat
    have : IsLocalHom (algebraMap W O) := ‹_›
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := W) (B := O)
    exact ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := W) (B := O)⟩
  let B : Over (Sp O) := (Over.pullback (spMap g)).obj G
  let π : B.left ⟶ G.left := pullback.fst G.hom (spMap g)
  have h : IsGrpPullback B G (spMap g) π := isGrpPullback_pullback G _
  have hB := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG h
  have := hB.comm
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) h.1.flip inferInstance
  have hr : Out.Rigidified G N := DVR.exists_gen_of_isLB_local (V := W) _ (pull_isLB hN _)
  obtain ⟨R, hR, ⟨c⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.allSixLaws.1 _ G hG N hN hr
    (GlobalTheory.GenericAmpleDvr.triv_theta hG hN)
  subst hR
  obtain ⟨hLB, hr', ⟨c', -⟩, -⟩ := Out.CubePf.cubePull _ _ G B (cubeMapOf h) R c
  have cube : GlobalTheory.AbLaw.Triv (Theta B (R.L.pull π)) := ⟨c'.t, c'.isGen⟩
  obtain ⟨⟨t', ht', -⟩, H⟩ := GlobalTheory.SecPullIso.section_pull _ _ π _ _ _ hN (pull_isLB hN π)
    (Out.CubePf.idIsoL_isGen (pull_isLB hN π)) t
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap g) x
    (IsLocalRing.closedPoint O) (hx.trans (IsLocalRing.comap_closedPoint g).symm)
  have hmem : z ∈ Out.nonzeroLocus t' := by
    rw [H t' ht']
    exact (congrArg (· ∈ Out.nonzeroLocus t) hz₁).mpr (TopologicalSpace.Opens.mem_iSup.2 ⟨a, hxa⟩)
  have hu := GlobalTheory.SquareGenerated.exists_secs_sq_generate O F B hB _ (pull_isLB hN π) cube t' ⟨z, hmem, hz₂⟩
  rw [← GlobalTheory.AmpleCrit.pull_pw_eq] at hu
  obtain ⟨m, u, hu⟩ := hu
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := quasiSeparatedSpace_of_quasiSeparated G.hom
  exact GlobalTheory.AmpleCrit.exists_cover_of_pull g hflat G.hom π B.hom h.1 (GlobalTheory.AbLaw.isLB_pw hN _) u hu

end GlobalTheory.ModelAmple

namespace GlobalTheory.ModelAmple

theorem veryAmpleBy_pw_of_generic : ∀ (K W K' : Type) [Field K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra K K'], ∀ (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, ∀ (H : LB A.left) (m : ℕ) (s : Fin (m + 1) → H.Sec) (M : LB G.left) (w : LB.Iso (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) (H.pull (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))))), H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy A.hom H s → M.IsLB → w.IsGen → ∃ n : ℕ, 1 ≤ n ∧ ∃ (m' : ℕ) (t : Fin (m' + 1) → (GlobalTheory.AbLaw.pw M n).Sec), GlobalTheory.AbLaw.VeryAmpleBy G.hom (GlobalTheory.AbLaw.pw M n) t := by
  intro K W K' _ _ _ _ _ _ _ _ A _ hA G _ hG e H m s M w hH hva hM hw
  have := hG.proper
  have := hA.proper
  have : IsIso e.hom.left := by
    change IsIso ((Over.forget _).map e.hom)
    infer_instance
  have : IsProper (Over.mk (pullback.snd G.hom (spMap (algebraMap W K')))).hom :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback G.hom (spMap (algebraMap W K'))) ‹IsProper G.hom›
  have hHa : Out.RelAmple A H := GlobalTheory.MulFiniteAny.relAmple_of_veryAmpleBy' hH s hva
  have sq : IsPullback (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))
      (pullback.snd G.hom (spMap (algebraMap W K'))) A.hom (spMap (algebraMap K K')) := by
    have h1 : IsPullback e.hom.left (pullback.snd G.hom (spMap (algebraMap W K')))
        (pullback.snd A.hom (spMap (algebraMap K K'))) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simpa using Over.w e.hom⟩
    simpa using h1.paste_horiz (IsPullback.of_hasPullback A.hom (spMap (algebraMap K K')))
  have hHK := GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hH hHa sq
  have hMK : Out.RelAmple (Over.mk (pullback.snd G.hom (spMap (algebraMap W K'))))
      (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) := by
    rw [GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hH _)] at hHK
    rw [GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine _ (pull_isLB hM _)]
    exact (GlobalTheory.isAmpleLB_congr (pull_isLB hM _) (pull_isLB hH _) ⟨w, hw⟩).2 hHK
  obtain ⟨L, hL, hLa⟩ := exists_relAmple W G hG
  have he : eSec G ≫ G.hom = 𝟙 _ := by
    simpa [eSec] using Over.w η[G]
  have hne : Nonempty (Over.mk (pullback.snd G.hom (spMap (algebraMap W K')))).left :=
    ⟨pullback.lift (spMap (algebraMap W K') ≫ eSec G) (𝟙 _) (by rw [Category.assoc, he]; simp)
      (IsLocalRing.closedPoint K')⟩
  obtain ⟨a, σ, ha, hσ⟩ := GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero K'
    (Over.mk (pullback.snd G.hom (spMap (algebraMap W K')))) (L.pull (pullback.fst G.hom (spMap (algebraMap W K'))))
    (M.pull (pullback.fst G.hom (spMap (algebraMap W K')))) inferInstance hne (pull_isLB hL _) (pull_isLB hM _) hMK
  have hp : (lbPow M a).IsLB := LB.isLB_linComb hM _ _
  have hN : (LB.div (lbPow M a) L).IsLB := LB.isLB_div hp hL
  obtain ⟨σ', hσ'⟩ := GlobalTheory.AmpleSpecialisation.exists_sec_ne_zero_of_lbIso (pull_isLB hN _)
    (LB.isLB_div (LB.isLB_linComb (pull_isLB hM _) _ _) (pull_isLB hL _))
    (GlobalTheory.AmpleSpecialisation.lbIso_pull_div_lbPow hL hM (pullback.fst G.hom (spMap (algebraMap W K'))) a) ⟨σ, hσ⟩
  obtain ⟨r, u, hu⟩ := exists_generating_sq W K' G hG _ hN σ' hσ'
  have hiso : LBIso (lbPow (LB.div (lbPow M a) L) 2) (GlobalTheory.AbLaw.pw (LB.div (lbPow M a) L) 2) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (GlobalTheory.isLB_lbPow hN 2) (GlobalTheory.AbLaw.isLB_pw hN 2)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow hN, GlobalTheory.AmpleStabFinite.cls_pw hN]
    first
      | rfl
      | exact (natCast_zsmul _ 2).symm
      | exact natCast_zsmul _ 2
      | simp only [two_smul, two_nsmul]
      | (simp; done)
  choose v hv using fun i => GlobalTheory.exists_sec_nonzeroLocus_eq_of_lbIso (GlobalTheory.isLB_lbPow hN 2)
    (GlobalTheory.AbLaw.isLB_pw hN _) hiso (u i)
  have hcov : ⨆ i, Out.nonzeroLocus (v i) = ⊤ := by
    simp_rw [hv]
    exact hu
  have hLamp := (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine G hL).1 hLa
  have hMa := (GlobalTheory.isAmpleLB_pow_iff hM ha).1 (hLamp.of_pow_div_generated hp (by norm_num) v hcov)
  have hMrel := (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine G hM).2 hMa
  obtain ⟨n, hn, m', t, -, ht⟩ := GlobalTheory.AbLaw.veryAmpleBy_of_relAmple hM hMrel (𝟙 G.left) (Category.id_comp _) hM
    (GlobalTheory.lbIso_pull_id hM).symm
  exact ⟨n, hn, m', t, ht⟩

end GlobalTheory.ModelAmple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralChernCombinationStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_integral_chern_combination : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (g : CxPts p σ → ℝ) (s : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ),
    (∀ n ∈ s, ∀ ε : ℤˣ, Integrable g ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε)) →
    wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (∑ n ∈ s, c n • lin (fun i => (n i : ℝ)) ^ D)) =
      ∑ n ∈ s, c n * wInt (hX.atlas σ) g (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) := by
  first | exact @GlobalTheory.LineForm.PolarSum.wInt_sum_lin_pow | exact GlobalTheory.LineForm.PolarSum.wInt_sum_lin_pow | (intros; apply GlobalTheory.LineForm.PolarSum.wInt_sum_lin_pow <;> assumption)
end

