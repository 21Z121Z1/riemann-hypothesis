import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0858
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0516
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlacesThetaFunctionFixedVectorShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0689
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSupportedClassScalarMemValuationRing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0782
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypePlacesIsSplitNonconjugateOfAdmissible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0859
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0625
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0805
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0592

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGoodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downwardThetaLift_preserves_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodMem R i t := by
  first | exact @GlobalTheory.GoodLift.goodMem_of_given | exact GlobalTheory.GoodLift.goodMem_of_given | (intros; apply GlobalTheory.GoodLift.goodMem_of_given <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalPreimageOfSupportedAtPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem suppF_finIdem_mem_range : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ k : GA D V, SuppF V f k → ∃ a : GlobalTheory.FinZeta.Gv V v, GlobalTheory.FinZeta.embV V v a = k := by
  intro D V v f hf k hk
  obtain ⟨ε, hε, rfl⟩ := hf
  obtain ⟨a, ha⟩ := (GlobalTheory.AdelicU.Supp.suppF_iff_mem_range V hε k).1 hk
  exact ⟨a, ha⟩

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPlacesThetaFunctionFixedVectorShapeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_places_thetaFunction_fixedVectorShape : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∃ Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)), GlobalTheory.DownLift.GenFinite.LikeOff R i t Sb f := by
  first | exact @GlobalTheory.DownLift.ShapeOff.exists_likeOff | exact GlobalTheory.DownLift.ShapeOff.exists_likeOff | (intros; apply GlobalTheory.DownLift.ShapeOff.exists_likeOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarMemCoefficientRingAuxiliaryLevel
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipScalUnit

open Formalism.L2.Host

theorem locK_eq_val_zpow {L : Type} [Field L] [NumberField L] (χ : HChar L) (R : HeightOneSpectrum (𝓞 L))
    (hR : χ.UnrAt R) (m : Lˣ) : χ.locK R m = χ.val R ^ ordF R m := by
  set N := ordF R m with hN
  set u : Lˣ := m * (unif R ^ N)⁻¹ with hu
  have hmu : m = u * unif R ^ N := by rw [hu, inv_mul_cancel_right]
  have hPv : R.valuation L (m : L) = WithZero.exp (-N) := by
    have h0 : R.valuation L (m : L) ≠ 0 := by simp
    rw [hN, ordF, neg_neg]
    exact (WithZero.exp_log h0).symm
  have hatFin : ∀ (x : Lˣ), Valued.v ((atFin R x : (R.adicCompletion L)ˣ) : R.adicCompletion L) = R.valuation L (x : L) :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' R (x : L)
  have hunit : IsUnitAt R (atFin R u) := by
    have h1 := unif_spec R
    unfold IsUnifAt at h1
    unfold IsUnitAt
    rw [hu, map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h1, hatFin, hPv, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have h1 : χ.locK R u = 1 := hR _ hunit
  calc χ.locK R m = χ.locK R (u * unif R ^ N) := by rw [← hmu]
    _ = χ.val R ^ N := by rw [map_mul, map_zpow, h1, one_mul]; rfl

open Formalism.L2.JoinChr in
set_option maxHeartbeats 800000 in

theorem char_flipDet {D : D7} (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) (he : IsIdemSum e T) (m : D.host.Eˣ) (x : (AE D)ˣ)
    (hx : (x : AE D) * (e * incA D (m : D.host.E) + (1 - e)) = 1) :
    ((c x : Circle) : ℂ) = ∏ R ∈ T, ((χ.locK R m⁻¹ : ℂˣ) : ℂ) := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  have hinf : infPart D (x : AE D) = 1 := by
    have h0 := congrArg (infPart D) hx
    simp only [map_mul, map_add, map_sub, map_one, GlobalTheory.PlaceVec.idemSum_infPart he, zero_mul, zero_add, sub_zero,
      mul_one] at h0
    exact h0
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ R : HeightOneSpectrum (𝓞 D.host.E), AE D →+* R.adicCompletion D.host.E,
      ∀ R z, ev R z = GlobalTheory.CharLocProd.evalAt R (ι (finPart D z)) :=
    ⟨fun R => (GlobalTheory.CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (finPart D)), fun _ _ => rfl⟩
  have hidem : ∀ Q ∈ T, ev Q (es Q) = 1 ∧ ∀ R, R ≠ Q → ev R (es Q) = 0 := by
    intro Q hQ
    simp only [hev]
    refine GlobalTheory.TameSplitChar.idem_apply _ (by rw [← RingEquiv.map_mul, ← RingHom.map_mul, (hes Q hQ).1.1]) Q fun y hy => ?_
    refine ((hes Q hQ).2 y hy).trans (not_congr ((h2 _).trans ?_))
    rw [RingHom.map_mul, RingEquiv.map_mul, show finPart D (incA D ((y : D.host.E)⁻¹)) =
      (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((y : D.host.E)⁻¹) from rfl, h1]
    rfl
  have heT : ∀ R ∈ T, ev R e = 1 := by
    intro R hR
    rw [hsum, map_sum, Finset.sum_eq_single R, (hidem R hR).1]
    · intro Q hQ hne; exact (hidem Q hQ).2 R hne.symm
    · intro h; exact absurd hR h
  have heT' : ∀ R, R ∉ T → ev R e = 0 := by
    intro R hR
    rw [hsum, map_sum]
    exact Finset.sum_eq_zero fun Q hQ => (hidem Q hQ).2 R fun h => hR (h ▸ hQ)
  have hinc : ∀ R (k : D.host.E), ev R (incA D k) = algebraMap D.host.E (R.adicCompletion D.host.E) k := by
    intro R k
    rw [hev, show finPart D (incA D k) = (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] k from rfl, h1,
      GlobalTheory.CharLocProd.evalAt_algebraMap]
  have hxT : ∀ R ∈ T, ev R x = algebraMap D.host.E (R.adicCompletion D.host.E) ((m⁻¹ : D.host.Eˣ) : D.host.E) := by
    intro R hR
    have h0 := congrArg (ev R) hx
    simp only [map_mul, map_add, map_sub, map_one, heT R hR, one_mul, sub_self, add_zero, hinc] at h0
    rw [eq_inv_of_mul_eq_one_left h0, Units.val_inv_eq_inv_val, map_inv₀]
  have hxT' : ∀ R, R ∉ T → ev R x = 1 := by
    intro R hR
    have h0 := congrArg (ev R) hx
    simp only [map_mul, map_add, map_sub, map_one, heT' R hR, zero_mul, zero_add, sub_zero, mul_one] at h0
    exact h0
  have hfin : {R : HeightOneSpectrum (𝓞 D.host.E) | R.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hN.ne')
  have key := hprod x hinf (T ∪ hfin.toFinset) (fun R => if R ∈ T then m⁻¹ else 1) ?_ ?_
  rotate_left
  · intro R _
    change Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x))) = _ ∧
      Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x)) - _) ≤ _
    rw [← hev]
    by_cases hR : R ∈ T
    · simp only [if_pos hR]
      rw [hxT R hR, sub_self, map_zero, GlobalTheory.CharLocProd.val_algebraMap]
      exact ⟨rfl, zero_le'⟩
    · simp only [if_neg hR]
      rw [hxT' R hR, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le'⟩
  · intro R hR
    rw [Finset.mem_union, not_or] at hR
    change Valued.v (GlobalTheory.CharLocProd.evalAt R (ι (finPart D x))) = _ ∧ _
    rw [← hev, hxT' R hR.1, map_one]
    exact ⟨rfl, fun h => hR.2 (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 h))⟩
  rw [key, ← Finset.prod_subset Finset.subset_union_left
    (fun R _ hR => by rw [if_neg hR, map_one, Units.val_one])]
  exact Finset.prod_congr rfl fun R hR => by rw [if_pos hR]

end GlobalTheory.FlipScalUnit

open GlobalTheory.FlipScalUnit in
set_option maxHeartbeats 1600000 in

theorem GlobalTheory.LevelSeries.flipScal_mem_valRing_of_unit : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l pd : ℕ), ChiData χW χ M₀ → l.Prime → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime pd (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT pd x → flipScal χW V W T pd x ∈ O := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hv hodd χ M₀ l pd hχ hl hpM hpl hpbad k _ _ σ la O hla hVR hConj hVI T eT x hT
    hpT hx
  classical
  have hpair := hv.1
  have hpd0 : pd ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' ((Nat.coprime_zero_left l).1 hpl)
  have hnot : ∀ (a b : ℕ), Nat.Coprime a b → ∀ R : HeightOneSpectrum (𝓞 D.host.E),
      ((a : ℕ) : 𝓞 D.host.E) ∈ R.asIdeal → ((b : ℕ) : 𝓞 D.host.E) ∉ R.asIdeal := by
    intro a b hab R ha hb
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hab
    have h1 : (((u * a + v * b : ℤ)) : 𝓞 D.host.E) = 1 := by rw [huv]; simp
    apply R.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← h1]
    push_cast
    exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)
  have hu : ∀ R ∈ T, χ.UnrAt R := fun R hR => hχ.2.1 R (hnot pd M₀ hpM R (hpT R hR))
  have hlR : ∀ R ∈ T, ((l : ℕ) : 𝓞 D.host.E) ∉ R.asIdeal := fun R hR => hnot pd l hpl R (hpT R hR)
  have hO : ∀ m : ℕ, Nat.Coprime m l → ((m : ℂ))⁻¹ ∈ O := fun m hm => by
    have h1 := hVR ((m : k)⁻¹) (by rw [map_inv₀, GlobalTheory.ScalarUnit.val_natCast la hla hm, inv_one])
    simpa using h1
  letI : Algebra k ℂ := σ.toAlgebra
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_valuationSubring_over (Ω := ℂ) la
  have hA' : ∀ x : 𝓞 k, A.valuation (σ (x : k)) < 1 ↔ x ∈ la.asIdeal := hA
  have hpA : (l : ℂ) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    have h1 := (hA' (l : 𝓞 k)).2 hla
    simpa using h1
  choose bW hbW using hpair.expW
  have hval : ∀ R ∈ T, ((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ∈ O := by
    intro R hR
    obtain ⟨y, hy⟩ := hVI R (hu R hR)
    have hy' : σ y = ((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) := by
      rw [hy, Formalism.L2.Host.HChar.valTw, GlobalTheory.LevelSeriesScal.natCast_cpow_half]
    obtain ⟨h1, -⟩ := GlobalTheory.LevelSeriesScal.val_mul_sqrt_unit D χW χ hχ.1 _ hbW l A hl hpA R (hlR R hR)
    rw [← hy'] at h1
    have hy0 : la.valuation k y ≤ 1 :=
      GlobalTheory.LevelSeriesScal.val_le_one_of_mem σ la A hA' y ((A.valuation_le_one_iff _).2 h1)
    exact hy' ▸ hVR y hy0
  have hNl : ∀ R ∈ T, Nat.Coprime (Ideal.absNorm R.asIdeal) l := by
    intro R hR
    have hle : Ideal.span {((pd : ℕ) : 𝓞 D.host.E)} ≤ R.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 (hpT R hR)
    have hd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [Ideal.absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 D.host.E)) pd, Algebra.norm_algebraMap,
      Int.natAbs_pow, Int.natAbs_natCast] at hd
    exact Nat.Coprime.coprime_dvd_left hd (Nat.Coprime.pow_left _ hpl)
  have hN0 : ∀ R : HeightOneSpectrum (𝓞 D.host.E), Ideal.absNorm R.asIdeal ≠ 0 := fun R h =>
    R.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  set mU : D.host.Eˣ := Units.mk0 ((pd : ℕ) : D.host.E) (by exact_mod_cast hpd0) with hmU
  set nR : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun R =>
    (Associates.mk R.asIdeal).count (Associates.mk (Ideal.span {((pd : ℕ) : 𝓞 D.host.E)})).factors with hnR
  have hord : ∀ R : HeightOneSpectrum (𝓞 D.host.E), Formalism.L2.Host.ordF R mU = (nR R : ℤ) := by
    intro R
    have h0 : ((pd : ℕ) : 𝓞 D.host.E) ≠ 0 := by exact_mod_cast hpd0
    have e1 : ((mU : D.host.Eˣ) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ((pd : ℕ) : 𝓞 D.host.E) := by
      rw [hmU, Units.val_mk0, map_natCast]
    unfold Formalism.L2.Host.ordF
    rw [e1, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def, if_neg h0, WithZero.log_exp,
      neg_neg]
  have hx' : (x : AE D) * (eT * incA D ((mU ^ V.rank : D.host.Eˣ) : D.host.E) + (1 - eT)) = 1 := by
    have h := hx
    unfold IsFlipDet at h
    rwa [Units.val_pow_eq_pow_val, map_pow, hmU, Units.val_mk0, map_natCast]
  have hcx := char_flipDet χW χ hχ.1 T eT hT (mU ^ V.rank) x hx'
  have hcx' : ((χW x : Circle) : ℂ) = ∏ R ∈ T, (((χ.val R : ℂˣ) : ℂ) ^ (nR R * V.rank))⁻¹ := by
    rw [hcx]
    refine Finset.prod_congr rfl fun R hR => ?_
    rw [map_inv, map_pow, locK_eq_val_zpow χ R (hu R hR), hord R, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      zpow_natCast, Units.val_pow_eq_pow_val, ← pow_mul]
  have hsq : Real.sqrt ((flipIdx V W T pd : ℕ) : ℝ) =
      ∏ R ∈ T, Real.sqrt (Ideal.absNorm R.asIdeal) ^ (nR R * V.rank * W.rank) := by
    have hnn : 0 ≤ ∏ R ∈ T, Real.sqrt (Ideal.absNorm R.asIdeal) ^ (nR R * V.rank * W.rank) :=
      Finset.prod_nonneg fun _ _ => pow_nonneg (Real.sqrt_nonneg _) _
    rw [← Real.sqrt_sq hnn]
    congr 1
    unfold flipIdx
    rw [← Finset.prod_pow]
    push_cast
    refine Finset.prod_congr rfl fun R _ => ?_
    unfold HeightOneSpectrum.maxPowDividing
    have hsN : Real.sqrt (Ideal.absNorm R.asIdeal : ℝ) ^ 2 = (Ideal.absNorm R.asIdeal : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg _)
    rw [map_pow, Nat.cast_pow]
    conv_lhs => rw [← hsN]
    simp only [hnR, ← pow_mul]
    ring_nf
  obtain ⟨s, hs⟩ := hodd
  have hfac : flipScal χW V W T pd x = ∏ R ∈ T, ((((χ.val R : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ)) ^
      (nR R * V.rank) * (((Ideal.absNorm R.asIdeal ^ (nR R * V.rank * (s + 1)) : ℕ) : ℂ))⁻¹) := by
    unfold flipScal
    rw [hcx', hsq, ← Finset.prod_inv_distrib, Complex.ofReal_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun R _ => ?_
    have hs0 : ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero, Real.sqrt_ne_zero']
      exact_mod_cast Nat.pos_of_ne_zero (hN0 R)
    have h2 : ((Real.sqrt (Ideal.absNorm R.asIdeal) : ℝ) : ℂ) ^ 2 = ((Ideal.absNorm R.asIdeal : ℕ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      rfl
    rw [inv_inv, Complex.ofReal_pow, Nat.cast_pow, ← h2, hs, mul_pow, ← pow_mul]
    field_simp
    ring
  rw [hfac]
  exact prod_mem fun R hR => O.mul_mem (O.pow_mem (hval R hR) _) (hO _ (Nat.Coprime.pow_left _ (hNl R hR)))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodFormsSpannedByThetaSeriesOfClassSums
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 10000000

namespace GlobalTheory.BaseClassSum

variable {D : D7} {S T : HSp D}

theorem series_move {B : Base S T} (hB : B.Good) (hS : S.SigOK) {t : Twist D Circle} (ht : t.Good) (hQ : B.admitted t.Q)
    {ω : PairRep S T} (hω : B.IsWeil t.chi ω) {h h' : GA D S} (hh : h ∈ GfC S) (hh' : h' ∈ GfC S) (γ : GQ S) (k : B.levJ t)
    (e : finPt S h = Bridge.ratF S γ * finPt S h' * (k : Bridge.Gf S)) (P : PolF D T.rank S.rank) :
    series B.F ω (B.vecFlat t) h P =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • series B.F ω (B.vecFlat t) h' (B.act ((γ⁻¹ : GQ S) : GA D S) P) := by
  obtain ⟨hsplit, hcomm, htriv, -, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D S
  obtain ⟨x, hx⟩ := (k : Bridge.Gf S).2
  obtain ⟨kk, hkk, -, -, -, hfk⟩ := GlobalTheory.LiftUnfold.exists_fin_mul_real S x
  have hkk' : finPt S kk = (k : Bridge.Gf S) := hfk.trans (Subtype.ext hx)
  obtain ⟨ga, hga, gf, hgf, hγ⟩ := hsplit (γ : GA D S)
  have hfγ : Bridge.ratF S γ = finPt S gf := by
    change finPt S (γ : GA D S) = _
    rw [hγ]
    dsimp only [finPt]
    rw [map_mul]
    have : (finHom S).rangeRestrict ga = 1 := Subtype.ext (MonoidHom.mem_ker.1 hga)
    rw [this, one_mul]
  have eh : h = (γ : GA D S) * h' * ga⁻¹ * kk := by
    have eg : gf = (γ : GA D S) * ga⁻¹ := by
      rw [hγ, hcomm ga hga gf hgf, mul_inv_cancel_right]
    have e1 : h = gf * h' * kk := by
      set y := (gf * h' * kk)⁻¹ * h with hy
      have hyf : y ∈ GfC S := mul_mem (inv_mem (mul_mem (mul_mem hgf hh') hkk)) hh
      have hyi : y ∈ GinfC S := by
        have : finPt S y = 1 := by
          rw [hy]
          dsimp only [finPt] at hkk' hfγ e ⊢
          rw [map_mul, map_inv, map_mul, map_mul, hkk', ← hfγ]
          change _ * ((finHom S).rangeRestrict h) = 1
          rw [e]
          exact inv_mul_cancel _
        exact MonoidHom.mem_ker.2 (congrArg Subtype.val this)
      have := htriv y hyi hyf
      rw [hy, inv_mul_eq_one] at this
      exact this.symm
    rw [e1, eg, mul_assoc (γ : GA D S) ga⁻¹ h', hcomm ga⁻¹ (inv_mem hga) h' hh', ← mul_assoc]
  have hact : B.act ((γ⁻¹ : GQ S) : GA D S) = B.act ga⁻¹ := by
    have hr : GlobalTheory.ExportSeries.realGL B.F.θ S gf = 1 := by
      funext τ
      show Formalism.UG.bc (B.F.θ τ) (infHom S gf) = 1
      rw [MonoidHom.mem_ker.1 hgf, map_one]
    rw [Base.act, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_inv, hγ, _root_.mul_inv_rev, map_mul, map_inv _ gf, hr,
      inv_one, one_mul]
  have hJ : finPt S kk ∈ B.levJ t := hkk' ▸ k.2
  have hθf : ∀ P, IsThetaFunO B.F.ψ S T (B.F.fock (B.vecFlat t) P) := Base.isThetaFunO_fock_vecAt hB hQ _
  have hk : ω (kk, 1) (B.F.fock (B.vecFlat t) P) = ((B.levLam t k : ℂˣ) : ℂ)⁻¹ • B.F.fock (B.vecFlat t) P := by
    have h1 := GlobalTheory.ExportSeries.DualType.dual_type_fock hB hS ht hQ hω hkk hJ P
    have e2 : ((B.levLam t ⟨_, hJ⟩ : ℂˣ) : ℂ) = ((B.levLam t k : ℂˣ) : ℂ) :=
      congrArg (fun z : B.levJ t => ((B.levLam t z : ℂˣ) : ℂ)) (Subtype.ext hkk')
    rw [← e2]
    exact h1
  have ha : ω (ga⁻¹, 1) (B.F.fock (B.vecFlat t) P) = B.F.fock (B.vecFlat t) (B.act ga⁻¹ P) :=
    GlobalTheory.RealFockAction.om_fock_vecAt D S T B t ω t.Q _ hB ht hQ hω ga⁻¹ (inv_mem hga) P
  have ep : ∀ g : GA D T, (((γ : GA D S) * h' * ga⁻¹ * kk, g) : GA D S × GA D T) =
      ((γ : GA D S), 1) * ((h', g) * ((ga⁻¹, 1) * (kk, 1))) := fun g => by
    ext <;> simp [mul_assoc]
  have key : ∀ g : GA D T, ω (h, g) (B.F.fock (B.vecFlat t) P) 0 =
      ((B.levLam t k : ℂˣ) : ℂ)⁻¹ * ω (h', g) (B.F.fock (B.vecFlat t) (B.act ga⁻¹ P)) 0 := fun g => by
    rw [eh, ep g, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, hk, map_smul, ha,
      map_smul, map_smul, Pi.smul_apply, hω.om_aut _ γ.2 1 (one_mem _) _ (hω.om_pres _ _ (hθf _)), smul_eq_mul]
  refine funext fun g => ?_
  rw [Pi.smul_apply, smul_eq_mul, hact]
  exact key g

theorem series_triv (ρ : Setup D.ntw) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b 0 ∅ 1).chi) ((ρ.B i j b).vecFlat (ρ.tw i b 0 ∅ 1)) h P = ρ.theta i j b h P := by
  have key : ∀ t : Twist D Circle, t.Q = ∅ → t.chi = 1 →
      series (ρ.B i j b).F (ρ.om i j b t.chi) ((ρ.B i j b).vecFlat t) h P = ρ.theta i j b h P := by
    rintro ⟨_, _, r⟩ rfl rfl
    show series _ _ ((ρ.B i j b).vecAt ∅ _) h P = series _ _ (ρ.B i j b).vecBase h P
    rw [Base.vecAt_empty]
  exact key _ (half_empty _) (charOf_one _ _)

theorem term_mem_span {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {F : Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank} (hF : F ∈ (ρ.B i j b).formsC (ρ.tw i b 0 ∅ 1))
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) :
    series (ρ.B i j b).F (ρ.om i j b (ρ.tw i b 0 ∅ 1).chi) ((ρ.B i j b).vecFlat (ρ.tw i b 0 ∅ 1)) h (F (finPt _ h)) ∈
      Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P} := by
  obtain ⟨hg, ha, -⟩ := GlobalTheory.T.twistingCharacter_admissibleGaloisTwist_good D _ D.ntw ρ hρ i j b 0 ∅ 1 (twOK_one i 0)
  have hB := hρ.base i j b
  have hω := hρ.weil i j b _ hg
  obtain ⟨γ, s, h', k, hs, hoff, hh', hsupp, e⟩ := GlobalTheory.T.exists_split_supported_rep_finite_unitary_class D ρ hρ i j b h hh
  have hlaw := ((ρ.B i j b).mem_formsC.1 hF).2 γ (finPt _ h') k
  have hval : F (finPt _ h') ∈ (ρ.B i j b).valSpace := ((ρ.B i j b).mem_formsC.1 hF).1 _
  have hinv : ((ρ.B i j b).act ((γ⁻¹ : GQ (Vc D j)) : GA D (Vc D j))) ((ρ.B i j b).act (γ : GA D (Vc D j)) (F (finPt _ h'))) =
      F (finPt _ h') := by
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [e, hlaw, LinearMap.map_smul, series_move hB (D.sp.V_sig _) hg ha hω hh hh' γ k e, hinv, smul_smul,
    mul_inv_cancel₀ (Units.ne_zero _), one_smul, series_triv]

  have hspan : F (finPt _ h') ∈ Submodule.span ℂ (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) := by
    have hm : ∀ τ, (ρ.B i j b).w.p τ + (ρ.B i j b).w.q τ ≤ (Wc D j).rank := fun τ => by
      have h1 := hB.sig τ
      have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (tauE D τ)
      rw [← h1] at h2
      exact h2.le
    have hlat : Submodule.IsLattice D.host.E ((ρ.B i j b).latAt (finPt _ h')) :=
      Formalism.UG.P.csGlob_lattice _ (Module.Finite.iff_fg.2 hB.frame.sdS.1.fg) hB.frame.sdS.1.span_eq_top _
    have h2 := (GlobalTheory.T.fockHarmonicLattice_fg_and_spans_value_space D (Wc D j).rank (Vc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS _ (Formalism.L2.Host.embLL0 D) (labLL0 D)
      (ρ.eO i b).range ((ρ.B i j b).latAt (finPt _ h')) hB.wt hm (hρ.isCoefRing i b) hlat).2
    have h3 : (ρ.lat i j b (ρ.eO i b).range h' : Set (PolF D (Wc D j).rank (Vc D j).rank)) =
        (harmLat (Formalism.L2.Host.embLL0 D) (labLL0 D) (ρ.eO i b).range (Wc D j).rank (ρ.B i j b).w (ρ.B i j b).F.BS
          ((ρ.B i j b).latAt (finPt _ h')) : Set (PolF D (Wc D j).rank (Vc D j).rank)) := rfl
    rw [h3, h2]
    exact hval
  have hmap := Submodule.mem_map_of_mem (f := (ρ.B i j b).theta (ρ.om i j b 1) h') hspan
  rw [Submodule.map_span] at hmap
  refine Submodule.span_mono ?_ hmap
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨s, h', P, ⟨hs, hoff, hh', hsupp, hP⟩, rfl⟩

theorem sum_mem_span {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    {F : Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank}
    (hF : F ∈ Submodule.span ℂ (ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))) :
    ρ.sum i j b 0 ∅ 1 F ∈ Submodule.span ℂ {f | ∃ s h P, ρ.IsDatum i j b s h P ∧ f = ρ.theta i j b h P} := by
  obtain ⟨hg, ha, -⟩ := GlobalTheory.T.twistingCharacter_admissibleGaloisTwist_good D _ D.ntw ρ hρ i j b 0 ∅ 1 (twOK_one i 0)
  have hc := hρ.classes i j b _ hg ha
  induction hF using Submodule.span_induction with
  | mem F hF =>
    have hF' := ((ρ.B i j b).mem_mtLat _ _ _).1 hF
    rw [Setup.sum, Base.classSum_apply]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (term_mem_span hρ i j b hF'.1 (hc.fin c))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end GlobalTheory.BaseClassSum

namespace GlobalTheory.TwInputs

theorem spanGood_of_sumOnto : ∀ (D : D7) (ρ : Setup D.ntw) (hρ : ρ.Good) (rd : Rds D.nexp ρ), ∀ i, SumOnto rd i → SpanGood rd i := by
  intro D ρ hρ rd i hS j b x hx
  obtain ⟨F, hF, e⟩ := hS j b x hx
  rw [e]
  exact GlobalTheory.BaseClassSum.sum_mem_span hρ i j b hF

end GlobalTheory.TwInputs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorThetaLiftOfBaseLevelLawStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodProjector_thetaLift_of_baseLevelLaw : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ y' : (X.R.HV j t).H, (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y' (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y' h) ∧
      (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y) (X.geo.v₀ j _) = X.R.thF j t y' (X.geo.v₀ j _) := by
  first | exact @GlobalTheory.ProjLiftLaw.projLift_law | exact GlobalTheory.ProjLiftLaw.projLift_law | (intros; apply GlobalTheory.ProjLiftLaw.projLift_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBOfBlochKatoTateDualityEulerC
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremB_closing : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, (320 : ℝ) ≤ C → ArcLiftingSetup.aux₃ D HW F C := by
  intro hBK hTD hEC D HW F Cm C hC
  have h22 : CrystallineLiftingBounds.adm22 D HW F := GlobalTheory.FontaineIneq.one_place_admissible_of_gap_constant_le D HW F
  have h23 : CrystallineLiftingBounds.adm23 D HW F := (GlobalTheory.jumps_exact_adm D HW F).1
  have hN1 : Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  have hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F := GlobalTheory.T.letterConditionGlobal_of_N1used D HW F Cm hN1
  exact GlobalTheory.T.theoremB_of_localFilteredHypotheses D HW F Cm C 10 23 32 32 8 hC h22 h23 hC4 (GlobalTheory.T.localLifting_theoremB_hypotheses_admitted hBK hTD hEC D HW F Cm)

end GlobalTheory
end

