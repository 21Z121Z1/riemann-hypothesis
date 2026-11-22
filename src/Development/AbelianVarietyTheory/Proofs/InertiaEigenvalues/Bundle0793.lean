import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0785
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0036
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0783
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0711
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTranslateOrthogonalOfSupportMovedOff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharZeroAdicCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0300
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import GroundTheory.LocalFields.Bundle0013
import GroundTheory.LocalFields.LubinTateReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0754
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
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
open GlobalTheory.StdAtPrime

namespace GlobalTheory.StdAtPrime

theorem natCast_adicCompletion_v_le_one {E : Type} [Field E] [NumberField E]
    (Q : HeightOneSpectrum (𝓞 E)) (k : ℕ) : Valued.v ((k : Q.adicCompletion E)) ≤ 1 := by
  have h := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) (k : 𝓞 E)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  simpa using h

theorem exists_coprime_natCast_mul_v_le_one {E : Type} [Field E] [NumberField E]
    (p : ℕ) (hp : p.Prime) (Q : HeightOneSpectrum (𝓞 E)) (hpQ : (p : 𝓞 E) ∉ Q.asIdeal)
    (x : Q.adicCompletion E) :
    ∃ r : ℕ, r.Coprime p ∧ Valued.v ((r : Q.adicCompletion E) * x) ≤ 1 := by
  obtain ⟨b, hb, hbx⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers Q x
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hbx
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  set N := Ideal.absNorm (Ideal.span {b}) with hNdef
  have hN0 : N ≠ 0 := by
    rw [hNdef, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb0
  have hmem : (N : 𝓞 E) ∈ Ideal.span {b} := Ideal.absNorm_mem _
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨N / p ^ N.factorization p, (Nat.coprime_ordCompl hp hN0).symm, ?_⟩
  have hsplit := Nat.ordProj_mul_ordCompl_eq_self N p
  have hvp : Valued.v ((p : Q.adicCompletion E)) = 1 := by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) (v := Q) (p : 𝓞 E)
    have h2 : Q.valuation E (algebraMap (𝓞 E) E (p : 𝓞 E)) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem Q).mpr hpQ
    simp only [map_natCast] at h1 h2
    rw [h1, h2]
  have hNx : Valued.v ((N : Q.adicCompletion E) * x) ≤ 1 := by
    have e : ((N : Q.adicCompletion E)) = (algebraMap (𝓞 E) (Q.adicCompletion E) c) *
        (algebraMap (𝓞 E) (Q.adicCompletion E) b) := by
      rw [← map_mul, hc, map_natCast]
    rw [e, mul_assoc, Valuation.map_mul, mul_comm _ x]
    refine mul_le_one' ?_ hbx
    have h := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := E) (v := Q) c
    rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  rw [← hsplit] at hNx
  push_cast at hNx
  rw [mul_assoc, Valuation.map_mul, map_pow, hvp, one_pow, one_mul] at hNx
  exact_mod_cast hNx

end GlobalTheory.StdAtPrime

namespace GlobalTheory.StdAtPrime

theorem bnd_of_local {E : Type} [Field E] [NumberField E] (p : ℕ) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : S.Finite)
    (hin : ∀ Q ∈ S, ∀ i j, ∃ r : ℕ, r.Coprime p ∧ Valued.v ((r : Q.adicCompletion E) * (A i j) Q) ≤ 1)
    (hout : ∀ Q ∉ S, ∀ i j, Valued.v ((A i j) Q) ≤ 1) : Bnd p A := by
  classical
  let f : HeightOneSpectrum (𝓞 E) × Fin n × Fin n → ℕ := fun t =>
    if h : t.1 ∈ S then Classical.choose (hin t.1 h t.2.1 t.2.2) else 1
  have hf : ∀ t, (f t).Coprime p := by
    intro t
    by_cases h : t.1 ∈ S
    · simp only [f, dif_pos h]; exact (Classical.choose_spec (hin t.1 h t.2.1 t.2.2)).1
    · simp only [f, dif_neg h]; exact Nat.coprime_one_left p
  let T : Finset (HeightOneSpectrum (𝓞 E) × Fin n × Fin n) := hS.toFinset ×ˢ Finset.univ
  refine ⟨∏ t ∈ T, f t, Nat.Coprime.prod_left fun t _ => hf t, fun i j Q => ?_⟩
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  rw [hev, map_mul, map_natCast, ← hev]
  by_cases hQ : Q ∈ S
  · have hmem : (Q, i, j) ∈ T := by simp [T, hQ]
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f hmem
    rw [hk, Nat.cast_mul, mul_comm ((f (Q, i, j) : ℕ) : Q.adicCompletion E), mul_assoc,
      Valuation.map_mul]
    refine mul_le_one' (natCast_adicCompletion_v_le_one Q k) ?_
    have := (Classical.choose_spec (hin Q hQ i j)).2
    simpa only [f, dif_pos hQ] using this
  · rw [Valuation.map_mul]
    exact mul_le_one' (natCast_adicCompletion_v_le_one Q _) (hout Q hQ i j)

theorem one_entry_v_le_one {E : Type} [Field E] [NumberField E] (n : ℕ)
    (Q : HeightOneSpectrum (𝓞 E)) (i j : Fin n) :
    Valued.v (((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs
  · have := natCast_adicCompletion_v_le_one Q 1
    simpa using this
  · have := natCast_adicCompletion_v_le_one Q 0
    simpa using this

theorem inv_eq_one_off {E : Type} [Field E] [NumberField E] (n : ℕ)
    (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (Q : HeightOneSpectrum (𝓞 E))
    (hQ : ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) :
    ∀ i j, ((G⁻¹).1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q := by
  let ev : FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E := RestrictedProduct.evalRingHom _ Q
  have hev : ∀ x : FiniteAdeleRing (𝓞 E) E, x Q = ev x := fun _ => rfl
  have hone : ∀ i j, ev ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) =
      (1 : Matrix (Fin n) (Fin n) (Q.adicCompletion E)) i j := by
    intro i j; rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  have h1 : ev.mapMatrix G.1 = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, ← hev, hQ, hev, hone]
  have h2 : ev.mapMatrix G.1 * ev.mapMatrix (G⁻¹).1 = 1 := by
    rw [← map_mul]
    have : G.1 * (G⁻¹).1 = 1 := by
      have := congrArg Units.val (mul_inv_cancel G)
      simpa using this
    rw [this, map_one]
  rw [h1, one_mul] at h2
  intro i j
  rw [hev, hev, hone]
  have := congrFun (congrFun h2 i) j
  rwa [RingHom.mapMatrix_apply, Matrix.map_apply] at this

theorem bnd_and_bnd_inv_of_eq_one_off_finite : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → (∀ Q ∈ S, (p : 𝓞 E) ∉ Q.asIdeal) → (∀ Q ∉ S, ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) → Bnd p G.1 ∧ Bnd p (G⁻¹).1 := by
  intro E _ _ p hp n G S hS hpS hG
  have hGi := fun Q hQ => inv_eq_one_off n G Q (hG Q hQ)
  have key : ∀ A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E),
      (∀ Q ∉ S, ∀ i j, (A i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) →
      Bnd p A := by
    intro A hA
    refine bnd_of_local p n A S hS (fun Q hQ i j => ?_) (fun Q hQ i j => ?_)
    · exact exists_coprime_natCast_mul_v_le_one p hp Q (hpS Q hQ) _
    · rw [hA Q hQ i j]; exact one_entry_v_le_one n Q i j
  exact ⟨key G.1 hG, key (G⁻¹).1 hGi⟩

end GlobalTheory.StdAtPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalJacquetModuleSecondBlockOfVanishingStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidal_jacquetModule_second_block_of_vanishing : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ) (h : a + b = n) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → (∀ (r t : ℕ) (h' : r + t = n), 0 < t → t < b → Subsingleton (Jacquet π (unipRad k (two (stdSum h'))))) → IsCuspidal (k := k) (n := Fin b) ((jac₂ (stdSum h) π).comp (MonoidHom.inr (GL (Fin a) k) (GL (Fin b) k))) := by
  first | exact @GlobalTheory.JacMinCuspGL.isCuspidal_jac₂_inr | exact GlobalTheory.JacMinCuspGL.isCuspidal_jac₂_inr | (intros; apply GlobalTheory.JacMinCuspGL.isCuspidal_jac₂_inr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerCharacterFactorsAbsoluteGaloisAbelianizatiStatement
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerCharacter_factors_absoluteGaloisAbelianization : ∀ (E' Ω : Type) [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (m : ℕ) (hm : 0 < m) (ζ : E') (hζ : IsPrimitiveRoot ζ m) (c : E') (hc : c ≠ 0) (y : Ω)
    (hy : y ^ m = algebraMap E' Ω c) (σ τ : G E' Ω) (he : toAb E' Ω σ = toAb E' Ω τ), σ y / y = τ y / y := by
  first | exact @GlobalTheory.KummerAb.kummer_char_eq_of_toAb_eq | exact GlobalTheory.KummerAb.kummer_char_eq_of_toAb_eq | (intros; apply GlobalTheory.KummerAb.kummer_char_eq_of_toAb_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LFactorRecCompatible
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isSpherical_iff_unr_of_lawsLit : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ x : IrrGL (w.adicCompletion E), IsSpherical x.rep ↔ (rc x).unr := by
  intro hEx hMS hSC hZP hGL hBZ E Ω _ _ _ _ _ A w h a ha e rc H x
  constructor
  · intro hs
    obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main hBZ (w.adicCompletion E) x.1
      ⟨x.2.rep.V, x.2.rep.ρ, x.2.rep.smooth, x.2.rep.irr⟩ hs
    rw [GlobalTheory.T.epsilon_factor_rec_compatible hEx hMS hSC hZP hGL hBZ E Ω A w h a ha e rc H x α hα]
    exact (WD.unr_mk _).2 (WDRep.unr_diag _)
  · intro hu
    obtain ⟨α, hα⟩ := GlobalTheory.T.unramified_weilDeligne_eq_diagonal_inv E Ω A w h (rc x) hu
    obtain ⟨π, hπ⟩ := GlobalTheory.CuspRep.ParLaws.exists_hasSatake (k := w.adicCompletion E) α
    have φ := equivRep π
    have hπ' : HasSatake (cls π).rep α := ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hπ.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hπ.2.2⟩
    have e1 := GlobalTheory.T.epsilon_factor_rec_compatible hEx hMS hSC hZP hGL hBZ E Ω A w h a ha e rc H (cls π) α hπ'
    have e2 : cls π = x := H.bij.1 (e1.trans hα.symm)
    rw [← e2]
    exact hπ'.2.1

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingStepTheoremTOfBhattScholzeFontaineStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftingStep_theoremT_of_bhattScholze_fontaine : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ C : ℕ, 40 ≤ C → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.ElementDenominator.HodgeTateFromSandwich D HW F C := by
  first | exact @GlobalTheory.TheoremTClosing.main | exact GlobalTheory.TheoremTClosing.main | (intros; apply GlobalTheory.TheoremTClosing.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinInertiaIsUnitAtStatement
section
open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localArtin_inertia_isUnitAt : ∀ {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha : IsLocalArtin h' a') (t : Ine (F := E') A),
    IsUnitAt w' (a' (ineIncl h' t)) := by
  first | exact @GlobalTheory.ArtinInertia.isUnitAt_artin_ine | exact GlobalTheory.ArtinInertia.isUnitAt_artin_ine | (intros; apply GlobalTheory.ArtinInertia.isUnitAt_artin_ine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localArtinMap_unique_transport_placeIso : GlobalArtinReciprocity → ChevalleyUnits → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (a' : Weil h' →* (w'.adicCompletion E')ˣ), IsLocalArtin h a → IsLocalArtin h' a' → ∀ σ σ', WeilRel φ σ σ' → a' σ' = Units.map i.toRingHom.toMonoidHom (a σ) := by
  first | exact @GlobalTheory.LocLanglands.isLocalArtin_transport | exact GlobalTheory.LocLanglands.isLocalArtin_transport | (intros; apply GlobalTheory.LocLanglands.isLocalArtin_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCoeffVanishesOffLevelBadPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.BadSuppPf

theorem rank_le (D : D7) (i : Fin D.R.m) : (Wc D i).rank ≤ (Vc D i).rank := by
  rw [D.sp.W_rank _ (Nat.le_add_left _ _) i.2]
  exact r_le_V i

theorem badSupp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ P hP e f hPf k hk hnot
  classical
  have hv := hL.thP.vP i t
  have hθ := GlobalTheory.VecTheta.isThetaFunO_thPVec hv
  obtain ⟨-, e', he', hth⟩ := hv
  obtain ⟨cV, hBV⟩ := hL.lev.βV i
  obtain ⟨cW, hBW⟩ := hL.lev.βW i
  rw [one_pow] at hBV hBW
  have hsdV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βV i)
  have hsdW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βW i)
  have hdat : (fun x : WO (Vc D i) (Wc D i) => if IsHalf (cA D e') x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) *
          omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x))
        else 0) = GlobalTheory.FinZeta.levDatum (Vc D i) (Wc D i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t) (R.xiR t) e' := by
    funext x
    simp only [GlobalTheory.FinZeta.levDatum, GlobalTheory.Survey.LevelVectorSizeBounds.omegaG_triv R i]
  rw [hdat] at hth
  obtain ⟨hkf, hk1⟩ := GlobalTheory.SuppLocal.suppF_local D (Wc D i) P e f k hPf hk
  have hZ : ∀ PP, PP ∈ R.Pg ∪ R.Q t ↔ PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ R.Q t := fun PP => Finset.mem_union
  have hsb := GlobalTheory.FinZeta.isSBHalf_levDatum D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv)
    (R.Q t) (R.xiR t) (R.Pg ∪ R.Q t) e' hsdV hsdW hBV.1 hBW.1 he'
  have horth := GlobalTheory.ThetaOrth.orth D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hF i t).datum (R.ΛV i) (R.ΛW i) hsdV hsdW
    (R.Pg ∪ R.Q t) e' he' (R.vacP i) _ (R.vP i t) hsb hth hθ μ 𝓕 hμ k hkf (fun x hx => by
      by_contra hx'
      obtain ⟨k', hk', hag⟩ := GlobalTheory.T.mem_level_of_levelDatum_ne_zero_translate D (Vc D i) (Wc D i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t)
        (R.xiR t) (R.Pg ∪ R.Q t) e' hsdW hBW.1 (rank_le D i) rfl he' hZ k hkf x hx hx'
      apply hnot
      have hlo := (GlobalTheory.FinZeta.LevelOff.level_offS D (Wc D i) (R.βW i) (R.ΛW i) (R.datWp i R.triv) ((R.Pg ∪ R.Q t).image (fun PP => PP.under (𝓞 D.host.F))) hBW
        (fun PP hPP => Finset.mem_image_of_mem _ (by
          rcases hPP with h | h
          · exact Finset.mem_union_left _ h
          · exact absurd h (Finset.notMem_empty _)))).2.1 k hkf
      refine hlo.2 ⟨⟨k', hk', fun v hvS => ?_⟩, fun v hvS => ?_⟩
      · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hvS
        exact hag PP hPP
      · have hne : v ≠ P.under (𝓞 D.host.F) := fun h => hvS (h ▸ Finset.mem_image_of_mem _
          (hP.elim (fun h => Finset.mem_union_left _ h) (fun h => Finset.mem_union_right _ h)))
        rw [hk1 v hne]
        exact Subgroup.one_mem _)
  have h0 : thetaIP μ 𝓕 (R.ωP i t (1, k) (R.vP i t)) (R.vP i t) = 0 := by
    have h1 : Formalism.IndefR.Lift.pet μ 𝓕 (R.ωP i t (1, k) (R.vP i t)) (R.vP i t) = 0 := horth
    unfold Formalism.IndefR.Lift.pet at h1
    unfold thetaIP
    have h2 : (fun w => star (R.ωP i t (1, k) (R.vP i t) w) * R.vP i t w) =
        fun w => starRingEnd ℂ (R.ωP i t (1, k) (R.vP i t) w * starRingEnd ℂ (R.vP i t w)) := by
      funext w; simp [mul_comm]
    rw [h2, integral_conj, h1, map_zero]
  unfold coef
  rw [h0, zero_div]

end GlobalTheory.BadSuppPf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentContinuousIsoFixedStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_continuous_iso_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.w.adicCompletion L))) (θ : GL (Fin n) (s.w.adicCompletion L) → ℂ) (U : Set (GL (Fin n) (s.w.adicCompletion L))), K ≤ GlobalTheory.SplitWeil.KO (s.w.adicCompletion L) (Fin n) → GlobalTheory.SplitWeil.KOne (s.w.adicCompletion L) (Fin n) ≤ K → IsOpen U → (1 : GL (Fin n) (s.w.adicCompletion L)) ∈ U → (∀ g ∈ U, g ∈ K → θ g = 1) → ∀ f ∈ NG.isoTyp a.ρ S, (∀ x : GAf L n, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x) ∈ K → NG.rt L n x f = θ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n x)) • f) → ∀ (ι : Type) [Fintype ι] (xs : ι → GAf L n) (z : ι → ℂ), (∀ j, TrivOutside {s.v} (xs j)) → ∑ j, z j • NG.rt L n (xs j) f ≠ 0 → ∃ y : σ.V, (∀ h ∈ K, σ.ρ h y = θ h • y) ∧ ∑ j, z j • σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc n (xs j))) y ≠ 0 := by
  first | exact @GlobalTheory.EigLocalSum.exists_eigen_local_sum | exact GlobalTheory.EigLocalSum.exists_eigen_local_sum | (intros; apply GlobalTheory.EigLocalSum.exists_eigen_local_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateAction
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LTRecip

theorem lubinTate_action : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (ι : Ω →ₐ[E] Kbar w), IsLocEmb A w ι →
    ∀ [ValuativeRel (Kbar w)] [TopologicalSpace (Kbar w)] [IsValuativeTopology (Kbar w)]
      [ValuativeExtension (w.adicCompletion E) (Kbar w)] {π : 𝒪[w.adicCompletion E]} (hπ : Irreducible π)
      {f : PowerSeries 𝒪[w.adicCompletion E]} (hf : IsLubinTateSeries π f)
      (c : Dec (F := E) A →* (w.adicCompletion E)ˣ),
      Continuous (fun g => ((c g : (w.adicCompletion E)ˣ) : w.adicCompletion E)) →
      (∀ σ : Weil h, ((c ⟨σ, Weil_le_Dec h σ.2⟩ : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        (a σ : w.adicCompletion E) * (π : w.adicCompletion E) ^ deg σ) →
      ∀ (g : Dec (F := E) A) (τ : GalLoc w), Lifts ι τ (g : G E Ω) →
      ∀ (u : 𝒪[w.adicCompletion E]), (u : w.adicCompletion E) = (c g : w.adicCompletion E) →
      ∀ (n : ℕ), ∀ x ∈ lubinTateTorsion (Kbar w) (hπ := hπ) hf n, lubinTateGalPointMap (hπ := hπ) hf τ x = u • x := by
  intro E Ω _ _ _ _ _ A w h a ha ι hι _ _ _ _ π hπ f hf c hc hcW g τ hτ u hu n x hx

  have hWeil : ∀ (σ : Weil h) (τ' : GalLoc w), Lifts ι τ' (σ : G E Ω) → ∀ (u' : 𝒪[w.adicCompletion E]),
      (u' : w.adicCompletion E) = (a σ : w.adicCompletion E) * (π : w.adicCompletion E) ^ deg σ →
      lubinTateGalPointMap (hπ := hπ) hf τ' x = u' • x := by
    intro σ τ' hτ' u' hu'
    obtain ⟨v, hv⟩ := GlobalTheory.T.local_artin_unit_of_uniformizer E Ω A w h a ha σ π u' hπ hu'
    have hy : unitUniformizerPow hπ v (-deg σ) = a σ := by
      apply Units.ext
      rw [unitUniformizerPow, Units.val_mul, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      change ((v : 𝒪[w.adicCompletion E]) : w.adicCompletion E) * _ = _
      rw [hv, hu', zpow_neg, mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (coe_ne_zero_of_irreducible hπ)), mul_one]
    have hvx : (v : 𝒪[w.adicCompletion E]) • x ∈ lubinTateTorsion (Kbar w) (hπ := hπ) hf n :=
      Submodule.smul_mem _ _ hx
    obtain ⟨hz, hact⟩ := GlobalTheory.T.lubin_tate_torsion_galois_action (w.adicCompletion E) (Kbar w) hπ hf v (-deg σ) n _ hvx
    have key := GlobalTheory.T.local_artin_frobenius_action E Ω A w h a ha ι hι σ τ' hτ' _ hz
    rw [← hy, hact, smul_smul, Units.inv_mul, one_smul] at key
    apply IdealPoint.ext
    rw [lubinTateGalPointMap_val, key, ← hv]
  set K := w.adicCompletion E
  have hπ0 : (π : K) ≠ 0 := coe_ne_zero_of_irreducible hπ
  set γ := valuation K ((π : K) ^ n) with hγ
  have hγ0 : γ ≠ 0 := by simp [γ, hπ0]

  set T := lubinTateField (Kbar w) hπ hf n
  have hU : IsOpen (T.fixingSubgroup : Set (GalLoc w)) := T.fixingSubgroup_isOpen

  set V : Set (Dec (F := E) A) :=
    (fun g' => ((c g' : Kˣ) : K)) ⁻¹' {z : K | valuation K (z - (c g : K)) < γ} with hVdef
  have hball : IsOpen {z : K | valuation K (z - (c g : K)) < γ} := by
    refine isOpen_iff_mem_nhds.2 fun z hz => (IsValuativeTopology.mem_nhds_iff).2 ⟨Units.mk0 γ hγ0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have e : z + y - (c g : K) = (z - (c g : K)) + y := by ring
    show valuation K (z + y - (c g : K)) < γ
    rw [e]
    exact Valuation.map_add_lt _ hz hy
  have hV : IsOpen V := hball.preimage hc
  have hgV : g ∈ V := by
    show valuation K (((c g : Kˣ) : K) - (c g : K)) < γ
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hγ0
  obtain ⟨σ, τ', hτ', hU', hV'⟩ := GlobalTheory.T.weil_group_dense_in_decomposition E Ω A w h ι hι g τ hτ _ hU V hV hgV

  set cσ : K := ((c ⟨σ, Weil_le_Dec h σ.2⟩ : Kˣ) : K) with hcσ
  have hclose : valuation K (cσ - (u : K)) < γ := by rw [hu]; exact hV'
  have hγ1 : γ ≤ 1 := by
    rw [hγ, map_pow]
    exact pow_le_one₀ zero_le π.2
  have huv : valuation K (u : K) ≤ 1 := u.2
  have hcσ1 : valuation K cσ ≤ 1 := by
    have e : cσ = (cσ - (u : K)) + (u : K) := by ring
    rw [e]
    exact (Valuation.map_add _ _ _).trans (max_le (hclose.le.trans hγ1) huv)
  let uσ : 𝒪[K] := ⟨cσ, hcσ1⟩
  have hWeil := hWeil σ τ' hτ' uσ (hcW σ)

  have hxT : x.val ∈ T := val_mem_lubinTateField hπ hf hx
  have hfix : (τ⁻¹ * τ') x.val = x.val := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hU' _ hxT
  have hττ' : τ' x.val = τ x.val := by
    rw [AlgEquiv.mul_apply] at hfix
    have := congrArg τ hfix
    rwa [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at this

  set t : K := (cσ - (u : K)) / (π : K) ^ n with ht
  have htv : valuation K t ≤ 1 := by
    rw [ht, map_div₀]
    rw [div_le_one₀ (zero_lt_iff.2 hγ0)]
    exact hclose.le
  let t' : 𝒪[K] := ⟨t, htv⟩
  have hsplit : uσ = u + π ^ n * t' := by
    apply Subtype.ext
    show cσ = (u : K) + (π : K) ^ n * t
    rw [ht, mul_div_cancel₀ _ (pow_ne_zero n hπ0)]
    ring
  have hxn : π ^ n • x = 0 := (mem_lubinTateTorsion hf n x).1 hx
  have hmod : uσ • x = u • x := by
    rw [hsplit, add_smul, mul_comm, mul_smul, hxn, smul_zero, add_zero]
  apply IdealPoint.ext
  rw [lubinTateGalPointMap_val, ← hττ', ← lubinTateGalPointMap_val, hWeil, hmod]

end GlobalTheory.LTRecip

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelEisensteinDoubledThetaTermsEqLagrangianIntStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelEisenstein_doubledTheta_terms_eq_lagrangianIntegrals : ∀ (D : D7) ψ (V W : HSp D) χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr, SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (ν : Measure (Mx D V.rank W.rank)) (𝓖' : Set (Mx D V.rank W.rank)), IsCovolOne (ratL V W) ν 𝓖' → ∃ e : GlobalTheory.Eis.Cosets (GlobalTheory.Doubling.siegel W) (GQ (GlobalTheory.Doubling.dblSp W)) ≃ Lag W, ∀ q, ∃ C, IsLagFrame W (e q) C ∧ ∫ y in 𝓖', GlobalTheory.SWPairProof.dbl V W f₁ f₂ (actO (GlobalTheory.Doubling.dblSp W) V ((q.out : GQ (GlobalTheory.Doubling.dblSp W)) : GA D (GlobalTheory.Doubling.dblSp W))⁻¹ 1 (GlobalTheory.SiegelFormula.lagr W V y)) ∂ν = lagTerm μ 𝓕 C f₁ f₂ := by
  first | exact @GlobalTheory.SWLagTerms.lagTerms_eq | exact GlobalTheory.SWLagTerms.lagTerms_eq | (intros; apply GlobalTheory.SWLagTerms.lagTerms_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCaseBoundAtPointOfAdmittedItemsStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitCase_bound_at_point_of_admitted_items_alt : GlobalTheory.Published.GlobalArtinReciprocity → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ep : Bool) (e' : ℕ) (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB → (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) → EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB := by
  first | exact @GlobalTheory.splitCase_bound_at_point_of_admitted_items | exact GlobalTheory.splitCase_bound_at_point_of_admitted_items | (intros; apply GlobalTheory.splitCase_bound_at_point_of_admitted_items <;> assumption)
end

