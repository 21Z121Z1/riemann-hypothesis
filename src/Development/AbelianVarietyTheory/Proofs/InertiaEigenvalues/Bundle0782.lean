import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinPullbackIsGoodTwistOfAnticyclotomicTame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0747
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfIsSupercuspidal
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterTwistUniversalCharAtChosenPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ResTwist

theorem res_twist_spec : ∀ {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (ρ : Setup X), ρ.Good →
  ∀ (Y : NExp D.R D.host D.what₂ D.LL0 N X), GlobalTheory.UnivChar.IsUnivChar Y →
  ∀ (i : X.Tw) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ),
    TwOK i k Q (χ.comp (Y.delU i Q M)) →
    ∀ (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (x : (kP PP.1)ˣ),
      (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).resC PP.1 x : ℂˣ) : ℂ) =
        ρ.eOk i b k ((χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i)
          (Pi.single PP (Multiplicative.toAdd ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1 x))))) : (X.Ok i k)ˣ) : X.Ok i k) := by
  intro D N X ρ hρ Y hY i b k Q M χ hT PP x
  let χc : Multiplicative (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) →* Circle :=
    unitPart.comp ((Units.map (ρ.eOk i b k).toMonoidHom).comp (χ.comp (AddMonoidHom.toMultiplicative (spread Y i Q M (ρ.ch i)))))
  have hgood := GlobalTheory.UnivGood.univOf_good D N X ρ hρ Y i Q M

  have hchar : charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M)) = χc.comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) := by
    ext1 y
    obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym y
    have hψ : IsOpen ((χ.comp (Y.delU i Q M)).ker : Set (G D.host.E N.Om)) :=
      Subgroup.isOpen_mono (H₁ := (Y.delU i Q M).ker) (fun g hg => by simp [MonoidHom.mem_ker.1 hg]) (Y.delU_open i Q M)
    have hco : ∀ P : Pl D.host.E, IsOpen ((coord Y i (admissibleConjugatePairPlaces X i Q M) M P).ker : Set (G D.host.E N.Om)) := by
      intro P
      by_cases hP : P ∈ admissibleConjugatePairPlaces X i Q M
      · refine Subgroup.isOpen_mono (H₁ := (Y.delU i (admissibleConjugatePairPlaces X i Q M) M).ker) (fun g hg => ?_) (Y.delU_open i (admissibleConjugatePairPlaces X i Q M) M)
        refine MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)
        rw [coord_apply Y i (admissibleConjugatePairPlaces X i Q M) M hP, MonoidHom.mem_ker.1 hg]
        rfl
      · rw [coord, dif_neg hP]
        simp
    have e1 : (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) y = Multiplicative.ofAdd fun P : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ) := by
      change Multiplicative.ofAdd (fun PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (ρ.rc.pull (coord Y i (admissibleConjugatePairPlaces X i Q M) M PP.1) y)) = _
      congr 1
      funext P
      exact congrArg Multiplicative.toAdd (ρ.rc.pull_eq (hco P.1) hσ)
    have e2 : Y.delU i Q M σ = AddMonoidHom.toMultiplicative (spread Y i Q M (ρ.ch i))
        (Multiplicative.ofAdd fun P : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => Multiplicative.toAdd (coord Y i (admissibleConjugatePairPlaces X i Q M) M P.1 σ)) :=
      Multiplicative.toAdd.injective (delU_eq_spread hY (twSet_of_twOK hT) (hρ.ch i) σ)
    simp only [charOf, MonoidHom.comp_apply]
    rw [ρ.rc.pull_eq hψ hσ, e1, MonoidHom.comp_apply, e2]
    rfl
  have hspec := GlobalTheory.ExportSeries.SpecGood.spec_good D (ZMod (X.l i ^ M)) Circle (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc hgood
  have hres : IsResAt (χc.comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).delQ (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)))) PP.1 (((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1) := hspec.res PP.1 PP.2
  have hidem := hgood.1.isIdemAt PP.2
  have htres : (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).res PP.1 = ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1 := by
    change resOf (charOf ρ.rc (ρ.eOk i b k) (χ.comp (Y.delU i Q M))) PP.1 = _
    rw [hchar]
    exact GlobalTheory.ConjTwist.isResAt_unique hidem (isResAt_resOf ⟨_, hres⟩) hres
  have hs : ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).spec (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) χc).res PP.1 = χc.comp ((AddMonoidHom.toMultiplicative
      (AddMonoidHom.single (fun _ : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) => ZMod (X.l i ^ M)) ⟨PP.1, PP.2⟩)).comp ((univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc).kap PP.1)) := dif_pos PP.2
  have hz : ∀ z : Multiplicative (DelQM D.host (X.l i) Q M), z ^ (X.l i ^ M) = 1 := by
    intro z
    rw [← ofAdd_toAdd z, ← ofAdd_nsmul]
    refine congrArg Multiplicative.ofAdd (funext fun v => ?_)
    simp [nsmul_eq_mul, ZMod.natCast_self]
  change (((ρ.tw i b k Q (χ.comp (Y.delU i Q M))).res PP.1 x : Circle) : ℂ) = _
  rw [htres, hs]
  simp only [χc, MonoidHom.comp_apply]
  rw [unitPart_of_pow (n := X.l i ^ M) (pow_ne_zero _ (X.lPrime i).out.ne_zero)
    (by rw [← map_pow, ← map_pow, hz, map_one, map_one])]
  rfl

end GlobalTheory.ResTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurL2PairingRealFiniteTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem schur_trPair_real_fin : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → ∀ i, LevProd R i → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x y : (R.HW i (sg0 D A)).H), ∀ u ∈ GinfC (Wc D i), ∀ γ ∈ GfC (Wc D i), dimProd A i * ∫ z in R.fdW i, star (val R i v x z) * val R i v y (z * (u * γ)) ∂(R.νW i) = trPair R i γ x y * ∏ ρ, ⟪((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ), (R.MW i (sg0 D A)).rep ρ (infMat D.sp.cm.sig (Wc D i).gram (R.θ ρ) u) ((v ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ)⟫_ℂ := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL i hLP v x y u hu γ hγ
  have hθ : IsInfFam R.θ := hL.models.inf
  obtain ⟨-, hr, -⟩ := hL.models.HW i (sg0 D A)
  have hHaar : (R.νW i).IsHaarMeasure := (hL.models.νW i).1.1
  have hfd : IsFundamentalDomain (GQ (Wc D i)) (R.fdW i) (R.νW i) := (hL.models.νW i).2
  have hTm : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e x) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ x
      exact this)
  have hTm' : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) ((R.HW i (sg0 D A)).e y) :=
    (GlobalTheory.MultMem.mem_mult_iff ..).1 (by
      have : (R.HW i (sg0 D A)).e y ∈ R.Wall i (sg0 D A) := hr ▸ LinearMap.mem_range_self _ y
      exact this)
  set J' : Set (GA D (Wc D i)) := {k | k ∈ levW R i ∧ γ⁻¹ * k * γ ∈ levW R i} with hJ'
  have hT1 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1) ((R.HW i (sg0 D A)).e x) :=
    ⟨hTm.aut, hTm.cusp, fun w k hk g => by rw [hTm.lev w k hk.1 g, hLP.2.1 k hk.1], hTm.equiv, hTm.cont⟩
  have hT2 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1)
      (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y)) := by
    have hT3 : IsMultMap R.θ (R.MW i (sg0 D A)) J' (fun _ => 1) ((R.HW i (sg0 D A)).e y) :=
      ⟨hTm'.aut, hTm'.cusp, fun w k hk g => by rw [hTm'.lev w k hk.1 g, hLP.2.1 k hk.1], hTm'.equiv, hTm'.cont⟩
    refine GlobalTheory.SphericalOps.isMultMap_heckeOn hT3 (fun k hk => ?_) (fun w k hk g => ?_)
    · rw [Finset.mem_singleton] at hk
      exact hk ▸ hγ
    · simp only [heckeLin_apply, Finset.sum_singleton, one_mul]
      have e : g * k * γ = g * γ * (γ⁻¹ * k * γ) := by group
      rw [e, hTm'.lev w _ hk.2 (g * γ), hLP.2.1 _ hk.2, one_mul]
  obtain ⟨c, hc⟩ := GlobalTheory.MultFinite.schurMult (θ := R.θ) (M := R.MW i (sg0 D A)) (J := J') (χ := fun _ => 1) hP
    (R.νW i) (R.fdW i) hθ hHaar hfd _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hT1) _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hT2)
  have hip := ipM_spec _ _ _ _ _ ⟨c, hc⟩
  obtain ⟨v', hv', hmove⟩ := GlobalTheory.RealPointMove.translate_eq_move D R.θ hθ (Wc D i) _ (R.MW i (sg0 D A)) J' (fun _ => 1) _ hT2
    u hu (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))
  have htr : trPair R i γ x y = dimProd A i * ipM (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) ((R.HW i (sg0 D A)).e x)
      (heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y)) := rfl
  have hint : ∀ z, star (val R i v x z) * val R i v y (z * (u * γ)) =
      star ((R.HW i (sg0 D A)).e x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) z) *
        heckeOn (R.MW i (sg0 D A)) {γ} ((R.HW i (sg0 D A)).e y) v' z := fun z => by
    rw [← hmove z]
    simp [val, heckeOn, postOn_apply, heckeLin_apply, mul_assoc]
  simp_rw [hint]
  rw [(hip (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) v').2, htr, mul_assoc]
  congr 2
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [hv' ρ]

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmoothWeilCharEqOneOfToAbsGaloisAbEqOneStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothWeilChar_eq_one_of_toAbsGaloisAb_eq_one : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (ξ : Weil h →* ℂˣ), GlobalTheory.WeilDeligne.IsSmooth ξ → ∀ σ : Weil h, GlobalTheory.HeckeGal.toAb E Ω σ = 1 → ξ σ = 1 := by
  first | exact @GlobalTheory.WeilCharKer.apply_eq_one_of_toAb_eq_one | exact GlobalTheory.WeilCharKer.apply_eq_one_of_toAb_eq_one | (intros; apply GlobalTheory.WeilCharKer.apply_eq_one_of_toAb_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitSetInertiaPowerTrivial
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwistPullTame

theorem coprime_absNorm {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {m : ℕ}
    (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal) : Nat.Coprime m (Ideal.absNorm P.asIdeal) := by
  first
  | exact @_root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem
  | exact _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem
  | (apply _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoprimeAbsNorm.coprime_absNorm_of_natCast_notMem ..)

open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin) in

theorem tameAt_of_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {art : Neutral.B1.Ideles E →* Gab E Ω}
    (ha : IsGlobalArtin art) {r : G E Ω →* ℂˣ} {χ : Formalism.L2.Host.HChar E} (h : GlobalTheory.ToricDistribution.Corr art r χ)
    {P : HeightOneSpectrum (𝓞 E)} {B : ValuationSubring Ω} (hB : IsPlaceOver B P) {m : ℕ}
    (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal) (hi : ∀ σ ∈ Ine (F := E) B, r σ ^ m = 1) : χ.TameAt P := by
  intro x hx hx1
  obtain ⟨a, ha'⟩ := GlobalTheory.Mem.UnrAe.exists_levelLe χ P
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal
  have hlt : Valued.v ((Ideal.absNorm P.asIdeal : ℕ) : P.adicCompletion E) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) (P.adicCompletion E)), GlobalTheory.Mem.WildChar.valued_algebraMap_lt_one]
    exact hmem
  have h3 := ha' _ (GlobalTheory.Mem.UnrAe.isUnitAt_pow hx (Ideal.absNorm P.asIdeal ^ a)) (by
    rw [Units.val_pow_eq_pow_val]
    refine GlobalTheory.Mem.WildChar.val_pow_pow_sub_one_le _ (le_of_eq hx) (hx1.trans_lt ?_) hlt a
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num)
  rw [map_pow] at h3
  have h4 : χ.loc P x ^ m = 1 := by
    obtain ⟨σ, hσ, e⟩ := (ha.ine P B hB _).mp ⟨x, hx, rfl⟩
    have e2 : χ.loc P x = r σ := h _ σ e.symm
    rw [e2, hi σ hσ]
  have hc : Nat.Coprime m (Ideal.absNorm P.asIdeal ^ a) := (coprime_absNorm hm).pow_right a
  rw [← pow_one (χ.loc P x), ← hc.gcd_eq_one]
  exact pow_gcd_eq_one.2 ⟨h4, h3⟩

theorem ine_pow_of_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) {A : Type} [CommGroup A]
    {φ : G D.host.E N.Om →* A} (hanti : AntiHom X.cc φ) {P P' : Pl D.host.E} (hc : Formalism.BasicNotions.IsConjPl D.host P P') {m : ℕ}
    (h : ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1)
    (B' : ValuationSubring N.Om) (hB' : IsPlaceOver B' P') (σ : G D.host.E N.Om) (hσ : σ ∈ Ine (F := D.host.E) B') :
    φ σ ^ m = 1 := by
  have h1 := GlobalTheory.TwistDet.cConj_mem_ine X hσ
  have h2 := GlobalTheory.TwistDet.isPlaceOver_moveVal_cc X (GlobalTheory.TwistDet.isConjPl_symm hc) hB'
  have h3 := h _ h2 _ h1
  rw [GlobalTheory.TwistDet.antiHom_cConj X hanti, inv_pow, inv_eq_one] at h3
  exact h3

theorem natCast_mem_conj {D : D7} {P P' : Pl D.host.E} (hc : Formalism.BasicNotions.IsConjPl D.host P P') (m : ℕ) :
    ((m : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal ↔ ((m : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [GlobalTheory.TwistDet.isConjPl_iff.1 hc, map_natCast]

end GlobalTheory.TwistPullTame

namespace GlobalTheory.TwistPullTame

open GlobalTheory.TwistPull

theorem good_pull_tame : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (a : Recip D N.Om), a.Good → ∀ (A : Type) [CommGroup A] (φ : G D.host.E N.Om →* A), IsOpen (φ.ker : Set (G D.host.E N.Om)) → AntiHom X.cc φ → ∀ Q : Finset (Pl D.host.E), SplitSet Q → (∀ P ∈ Q, ∃ m : ℕ, ((m : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧ ∀ B : ValuationSubring N.Om, IsPlaceOver B P → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1) → (∀ v : Pl D.host.E, v ∉ Q → (∀ P ∈ Q, ¬ Formalism.BasicNotions.IsConjPl D.host P v) → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ σ ∈ Ine (F := D.host.E) B, φ σ = 1) → (⟨Q, a.pull φ, resOf (a.pull φ)⟩ : Twist D A).Good := by
  intro D N X a ha A _ φ hφ hanti Q hQ hQm hunr
  haveI := finite_range (D := D) hφ
  set M := Nat.card φ.range with hMdef
  have hM : M ≠ 0 := Nat.card_pos.ne'
  have hr : ∀ f : φ.range →* ℂˣ, IsOpen ((f.comp φ.rangeRestrict).ker : Set (G D.host.E N.Om)) ∧
      ∀ σ, (f.comp φ.rangeRestrict) σ ^ M = 1 := fun f => by
    refine ⟨Subgroup.isOpen_mono (H₁ := φ.ker) (fun g hg => ?_) hφ, fun σ => ?_⟩
    · have : φ.rangeRestrict g = 1 := Subtype.ext (MonoidHom.mem_ker.1 hg)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, this, map_one]
    · rw [MonoidHom.comp_apply, ← map_pow, pow_card_eq_one', map_one]
  have hanti' : ∀ f : φ.range →* ℂˣ, AntiHom X.cc (f.comp φ.rangeRestrict) := fun f g g' hg => by
    have e : φ.rangeRestrict g' = (φ.rangeRestrict g)⁻¹ := Subtype.ext (hanti g g' hg)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_inv]

  have hin : ∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → ∃ m : ℕ,
      ((m : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal ∧
        ∀ B : ValuationSubring N.Om, IsPlaceOver B P' → ∀ σ ∈ Ine (F := D.host.E) B, φ σ ^ m = 1 := by
    intro P hP P' hP'
    obtain ⟨m, hm, hB⟩ := hQm P hP
    rcases hP' with rfl | hc
    · exact ⟨m, hm, hB⟩
    · exact ⟨m, fun h => hm ((natCast_mem_conj hc m).1 h), ine_pow_of_conj X hanti hc hB⟩
  have htame : ∀ (f : φ.range →* ℂˣ) (χ : Formalism.L2.Host.HChar D.host.E),
      GlobalTheory.ToricDistribution.Corr a.art (f.comp φ.rangeRestrict) χ →
      ∀ P ∈ Q, ∀ P' : Pl D.host.E, (P' = P ∨ Formalism.BasicNotions.IsConjPl D.host P P') → χ.TameAt P' := by
    intro f χ hχ P hP P' hP'
    obtain ⟨m, hm, hB⟩ := hin P hP P' hP'
    obtain ⟨B, hB'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver N.Om P'
    refine tameAt_of_ine ha.artin hχ hB' hm fun σ hσ => ?_
    have e : φ.rangeRestrict σ ^ m = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, MonoidHom.coe_rangeRestrict, hB B hB' σ hσ]; rfl)
    rw [MonoidHom.comp_apply, ← map_pow, e, map_one]
  refine ⟨isOpen_ker_pull ha hφ, fun x => pull_rat ha φ x, fun y => ?_, hQ, ?_, fun PP hPP => isResAt_resOf ?_⟩
  ·
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨h1, h2⟩ := hr f
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha h1 hM h2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [real_C D N X a.art ha.artin _ _ hM h2 (hanti' f) c χ hc hχ y]
    simp
  ·
    intro x h1 h2 h3 h4
    refine (pull_eq_of_chars a hφ (y := 1) fun f => ?_).trans (map_one _)
    obtain ⟨o1, o2⟩ := hr f
    obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha o1 hM o2
    rw [map_one]
    refine Units.ext ((hcr _).symm.trans ?_)
    rw [GlobalTheory.T.heckeChar_unramified_outside_split_set_of_tame D N a.art ha.artin _ M hM o2 c χ hc hχ Q hQ (htame f χ hχ) (fun v hv hc' B hB σ hσ => by
      rw [MonoidHom.comp_apply, show φ.rangeRestrict σ = 1 from Subtype.ext (hunr v hv hc' B hB σ hσ), map_one]) x h1 h2 h3 h4]
    simp
  ·
    have hPP := hQ.isIdemAt hPP
    have same : ∀ (x x' : (AE D)ˣ) (u : (kP PP)ˣ), (1 - idemAt PP) * (x : AE D) = 1 - idemAt PP →
        (1 - idemAt PP) * (x' : AE D) = 1 - idemAt PP →
        ∀ (hi : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
          (hi' : toEAf D (x' : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
        resS D.host.F PP ⟨_, hi⟩ = u → resS D.host.F PP ⟨_, hi'⟩ = u → a.pull φ x = a.pull φ x' := by
      intro x x' u hx hx' hi hi' hu hu'
      refine pull_eq_of_chars a hφ fun f => ?_
      obtain ⟨o1, o2⟩ := hr f
      obtain ⟨c, χ, hc, hχ, hcr⟩ := exists_chrEq_pull ha o1 hM o2
      have ht : χ.TameAt PP := htame f χ hχ PP ‹_› PP (Or.inl rfl)
      obtain ⟨ρ, hρ⟩ := GlobalTheory.exists_isRes_of_tameAt D χ PP ht
      have e : ∀ z : (AE D)ˣ, (1 - idemAt PP) * (z : AE D) = 1 - idemAt PP →
          ∀ (hz : toEAf D (z : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
          resS D.host.F PP ⟨_, hz⟩ = u → a.pull (f.comp φ.rangeRestrict) z = ρ u := fun z hz hzi hzu =>
        Units.ext ((hcr z).symm.trans (GlobalTheory.ConjTwist.eq_res_of_chrEq hc hPP ht hρ z hz hzi u hzu))
      rw [e x hx hi hu, e x' hx' hi' hu']
    have hlift := fun u => GlobalTheory.ConjTwist.exists_isLocUnit hPP u
    choose xs hxs using hlift
    have hmul : ∀ u v, a.pull φ (xs (u * v)) = a.pull φ (xs u * xs v) := fun u v => by
      obtain ⟨hi, hu⟩ := (hxs (u * v)).res
      obtain ⟨hi1, hu1⟩ := (hxs u).res
      obtain ⟨hi2, hu2⟩ := (hxs v).res
      have hi3 : toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
        rw [Units.val_mul, map_mul]
        exact mul_mem hi1 hi2
      refine same _ _ (u * v) (hxs (u * v)).off ?_ hi hi3 hu ?_
      · rw [Units.val_mul, ← mul_assoc, (hxs u).off, (hxs v).off]
      · have : (⟨_, hi3⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨_, hi1⟩ * ⟨_, hi2⟩ :=
          Subtype.ext (by
            change toEAf D ((xs u * xs v : (AE D)ˣ) : AE D) = toEAf D (xs u : AE D) * toEAf D (xs v : AE D)
            rw [Units.val_mul, map_mul])
        rw [this, map_mul, hu1, hu2, Units.val_mul]
    refine ⟨MonoidHom.mk' (fun u => a.pull φ (xs u)) (fun u v => ?_), ?_⟩
    · show a.pull φ (xs (u * v)) = a.pull φ (xs u) * a.pull φ (xs v)
      rw [hmul, map_mul]
    · intro x hx hi u hu
      show a.pull φ x = a.pull φ (xs u)
      obtain ⟨hi', hu'⟩ := (hxs u).res
      exact same x (xs u) u hx (hxs u).off hi hi' hu hu'

end GlobalTheory.TwistPullTame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupled
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TameRecord

section Transport

variable {G H V : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_comp (ρ : Representation ℂ H V) (φ : G →* H) (hφ : Continuous φ) (h : GlobalTheory.PRep.IsSmooth ρ) :
    GlobalTheory.PRep.IsSmooth (ρ.comp φ) := fun v => (h v).preimage hφ

theorem isIrreducible_comp (ρ : Representation ℂ H V) (φ : G →* H) (hs : Function.Surjective φ)
    (h : GlobalTheory.GLp.IsIrrRep ρ) : Representation.IsIrreducible (ρ.comp φ) := by
  rw [GlobalTheory.CuspRep.isIrreducible_iff]
  refine ⟨h.1, fun W hW => h.2 W fun y v hv => ?_⟩
  obtain ⟨x, rfl⟩ := hs y
  exact hW x v hv

theorem isSupercuspidal_comp [IsTopologicalGroup G] [IsTopologicalGroup H] (ρ : Representation ℂ H V) (φ : G →* H)
    (ψ : H →* G) (hφ : Continuous φ) (hψ : Continuous ψ) (h1 : ∀ x, ψ (φ x) = x) (h2 : ∀ y, φ (ψ y) = y)
    (h : GlobalTheory.PRep.IsSupercuspidal ρ) : GlobalTheory.PRep.IsSupercuspidal (ρ.comp φ) := by
  refine ⟨isSmooth_comp ρ φ hφ h.1, fun v l hl => ?_⟩
  have hl' : l ∈ GlobalTheory.PRep.smoothPart (Representation.dual ρ) := by
    have e : {y : H | Representation.dual ρ y l = l} =
        ψ ⁻¹' {x : G | Representation.dual (ρ.comp φ) x l = l} := by
      ext y
      simp [Representation.dual_apply, h2]
    show IsOpen {y : H | Representation.dual ρ y l = l}
    rw [e]
    exact hl.preimage hψ
  obtain ⟨C, hC, hCv⟩ := h.2 v l hl'
  refine ⟨ψ '' C, hC.image hψ, fun x hx => ?_⟩
  obtain ⟨z, hz, c, hc, e⟩ := hCv (φ x) hx
  refine ⟨ψ z, Subgroup.mem_center_iff.2 fun y => ?_, ψ c, ⟨c, hc, rfl⟩, ?_⟩
  · rw [← h1 y, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz (φ y))]
  · rw [← map_mul, ← e, h1]

end Transport

section GLMap

variable {n : Type} [Fintype n] [DecidableEq n] {K₁ K₂ : Type} [Field K₁] [Field K₂] [TopologicalSpace K₁]
  [TopologicalSpace K₂] [IsTopologicalRing K₁] [IsTopologicalRing K₂]

theorem continuous_glMap (f : K₁ →+* K₂) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := n) f) :=
  Continuous.units_map _ (Continuous.matrix_map continuous_id hf)

theorem glMap_symm_apply (i : K₁ ≃+* K₂) (x : GL n K₁) :
    Matrix.GeneralLinearGroup.map i.symm.toRingHom (Matrix.GeneralLinearGroup.map i.toRingHom x) = x := by
  ext a b
  simp

theorem glMap_apply_symm (i : K₁ ≃+* K₂) (y : GL n K₂) :
    Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map i.symm.toRingHom y) = y := by
  ext a b
  simp

end GLMap

theorem continuous_symm {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i) : Continuous i.symm := by
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toRingHom.toAddMonoidHom i.surjective hi
  exact (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous

def transRep {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) :=
  ⟨_, π.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom),
    isSmooth_comp _ _ (continuous_glMap _ (continuous_symm _ (I.i k v) (I.cont k v))) hs,
    isIrreducible_comp _ _ (fun y => ⟨_, glMap_apply_symm (I.i k v).symm y⟩) h⟩

theorem transRep_comp {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])) (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    (transRep I k v π h hs).ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom) = π.ρ :=
  MonoidHom.ext fun x => by
    show π.ρ _ = π.ρ x
    rw [glMap_symm_apply]

theorem iso_pull {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])) (h : GlobalTheory.GLp.IsIrrRep π.ρ) (hs : GlobalTheory.PRep.IsSmooth π.ρ) :
    Nonempty (π ≅ pull I k v (transRep I k v π h hs)) :=
  by
    have E : π.ρ.Equiv ((transRep I k v π h hs).ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom)) := by
      rw [transRep_comp]; exact Representation.Equiv.refl _
    exact ⟨(Rep.mkIso E : Rep.of π.ρ ≅ _)⟩

theorem tameParam_record : GlobalTheory.Published.DepthZeroInertia → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), IsRc hL T I rc → ∀ (L : ∀ k, LabelDatum (D.host.g k)) (k : Fin 2) (v : D.nd.PlG k) (κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen → TameGen.TameParam (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v)) (fun π : Supp.GLRep _ => rc k v π.1 π.2) := by
  intro hDZ hL D T I rc hrc L k v κ hκ ρ hρ τ P hP hinf
  obtain ⟨n, π⟩ := ρ
  have hs : GlobalTheory.PRep.IsSmooth π.ρ := hρ.2.2.1
  set σ := transRep I k v π hρ.2.1 hs
  have hsc : GlobalTheory.PRep.IsSupercuspidal σ.ρ :=
    isSupercuspidal_comp π.ρ _ (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom)
      (continuous_glMap _ (continuous_symm _ (I.i k v) (I.cont k v))) (continuous_glMap _ (I.cont k v))
      (glMap_apply_symm (I.i k v)) (glMap_symm_apply (I.i k v)) hρ.2.2
  have hcusp : (GlobalTheory.LocLanglands.cls σ).IsCusp := GlobalTheory.LocGL.IrrGL.isCusp_of.2 ⟨hρ.1, GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal _ n _ σ.ρ hsc⟩
  have hinf' : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom)) τ := by
    rw [transRep_comp]; exact hinf
  show D.naut.inePol (rc k v n π) (D.ntypes.tg k v) = _
  rw [T.inePol _ _ _ (D.ntypes.tg_mem k v), hrc k v n σ π (iso_pull I k v π hρ.2.1 hs)]
  exact hDZ D.host.E D.nd.Om (D.host.g k) _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _
    (GlobalTheory.CuspRep.ParLaws.isRec_locRec hL _) (I.i k v) (I.cont k v) κ (L k) _ (D.ntypes.tg_mem k v) hκ n σ hcusp
    τ P hP hinf'

end GlobalTheory.TameRecord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistingCharacterAdmissibleGaloisTwistGoodStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistingCharacter_admissibleGaloisTwist_good : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ) (Q : Finset (Pl D.host.E)) (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), Formalism.MainNotions.IntegralHeckeForms.TwOK i k Q ψ → (ρ.tw i b k Q ψ).Good ∧ (ρ.B i j b).admitted (ρ.tw i b k Q ψ).Q ∧ ∀ x, ∃ u : (X.Ok i k)ˣ, (((ρ.tw i b k Q ψ).chi x : Circle) : ℂ) = ρ.eOk i b k u := by
  first | exact @GlobalTheory.TwistGood.tw_good | exact GlobalTheory.TwistGood.tw_good | (intros; apply GlobalTheory.TwistGood.tw_good <;> assumption)
end

