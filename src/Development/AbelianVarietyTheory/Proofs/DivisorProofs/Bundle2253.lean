import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnderEqOfConj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0275
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0465
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0590
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsUniqueIsConnOfLift
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelVectorUnitMulDilatedFlat
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp

open Classical in

theorem kerDat_twoStep {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    {i : Fin D.R.m} {ξ : Formalism.L2.Host.HChar D.host.E} {χ : (AE D)ˣ →* Circle} {ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    {Q : Finset (Pl D.host.E)} {ω : WeilRep D i} {φ : WO (Vc D i) (Wc D i) → ℂ} (hK : KerDat R i ξ χ ξR Q ω φ)
    (hQ : ∃ t, Q ⊆ R.Q t) {eg eQ : AE D} {fg : WO (Vc D i) (Wc D i) → ℂ} (hg : IsIdemSum eg R.Pg) (hq : IsIdemSum eQ Q)
    (hfg : IsTypeVec R i eg fg) :
    IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eQ) (lattice₂ R i) 1 fg
      (fun x => if IsHalf (cA D eQ) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) φ := by
  obtain ⟨⟨hψ, -⟩, e, he, hTe⟩ := hK.vec
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  obtain ⟨t, ht⟩ := hQ
  have hd : Disjoint R.Pg Q := Disjoint.mono_right ht (GlobalTheory.TwistPlaces.typePlaces_disjoint_twistPlaces R F hC t)
  have hsum : e = eg + eQ := by
    rw [← GlobalTheory.ExportSeries.idem_eq he, ← GlobalTheory.ExportSeries.idem_eq hg, ← GlobalTheory.ExportSeries.idem_eq hq]
    exact Finset.sum_union hd
  subst hsum
  have heg := GlobalTheory.PlaceVec.idemSum_mul_self hg
  have heQ := GlobalTheory.PlaceVec.idemSum_mul_self hq
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hgQ : eg * eQ = 0 := by
    refine GlobalTheory.PlaceVec.natCast_mul_eq_zero 2 _ two_pos ?_
    push_cast
    linear_combination hee - heg - heQ
  have hcg : cA D eg * cA D eg = cA D eg := by rw [← map_mul, heg]
  have hcQ : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, heQ]
  have hQg : cA D eQ * cA D eg = 0 := by rw [← map_mul, mul_comm, hgQ, map_zero]
  have hgQ' : cA D eg * cA D eQ = 0 := by rw [mul_comm, hQg]
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True),
      a • u ∈ (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) :=
    fun a ha u hu => GlobalTheory.PlaceModelSum.idem_smul_latO ha hu
  have hinfg : infPart D (cA D eg) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg)
  have hinfQ : infPart D (cA D eQ) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hq)
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfg (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBQ := GlobalTheory.PlaceVec.isSBHalf_of_red hSV.1 hSW.1 hinfQ (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    Q (fun y => omegaQ Q (Wc D i).rank ξR (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  obtain ⟨⟨Te, hTe1⟩, hTe2⟩ := hTe
  have hc : cA D (eg + eQ) = cA D eQ + cA D eg := by rw [map_add, add_comm]
  have hc' : cA D (eg + eQ) = cA D eg + cA D eQ := map_add _ _ _
  have hm1 := GlobalTheory.TwoStepModel.isPlaceModel_comp_tensorHalf hcQ hcg hQg hΛ hSBg (hc ▸ hTe1)
  have hm2 := GlobalTheory.ExportSeries.isPlaceModel_comp_restrictHalf hcg hcQ hgQ' hΛ (hc' ▸ hTe1)
  have hbase := hfg.2 _ hm2
  simp only [LinearMap.comp_apply] at hbase
  rw [← hbase] at hm1
  refine ⟨⟨_, hm1⟩, fun T' hT' => ?_⟩
  rw [hTe2 Te hTe1, GlobalTheory.TwoStepModel.datum_eq_tensorHalf (R.βV i) (R.βW i) hg hq hd he ξR]
  exact GlobalTheory.PlaceVec.placeModel_unique hψ hSV hSW hcQ hinfQ hm1 hT' hSBQ

end GlobalTheory.BaseCmp

namespace GlobalTheory.BaseCmp

open GlobalTheory.ChainOnto in

theorem kerDat_xiR_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ),
    KerDat R i ξ χ ξR Q ω φ → ∀ PP ∈ Q, ξR PP ≠ 1 := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i ξ χ ξR Q ω φ hK
  intro PP hP h1
  refine (hK.ram PP).2 (Or.inl hP) fun x hx => ?_
  have hc := hK.res PP hP
  rw [h1] at hc
  have hU : IsOpen {z : PP.adicCompletion D.host.E | Valued.v (z - x) < 1} :=
    (GlobalTheory.ChainOnto.TameRes.isOpen_ltOne PP).preimage (continuous_sub_right _)
  obtain ⟨k, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap D.host.E PP).exists_mem_open hU ⟨x, by simp⟩
  have hk' : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) < Valued.v (x : PP.adicCompletion D.host.E) := by
    rw [hx]; exact hk
  have hv : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k) = 1 := by
    rw [Valuation.map_eq_of_sub_lt _ hk']; exact hx
  have hv1 : PP.valuation D.host.E k = 1 := by rw [← GlobalTheory.ChainOnto.TameRes.val_alg]; exact hv
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hv1
  obtain ⟨a, s, h⟩ := PP.exists_primeCompl_mul_eq_of_integer k hv1.le
  have hs : (s : 𝓞 D.host.E) ∉ PP.asIdeal := s.2
  have hsv := GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem PP _ hs
  have hav : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E a) = 1 := by
    rw [← h, map_mul, hv1, hsv, one_mul]
  have ha : a ∉ PP.asIdeal := fun hm =>
    absurd hav (ne_of_lt ((PP.valuation_lt_one_iff_mem (K := D.host.E) a).mpr hm))
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  have key : ∀ (b : 𝓞 D.host.E), b ∉ PP.asIdeal → ∀ y : D.host.Eˣ, (y : D.host.E) = b → ξ.locK PP y = 1 := by
    intro b hb y hy
    have hms : (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hb
    obtain ⟨b', hb'⟩ := Ideal.Quotient.exists_inv hms
    exact (hc b y (Units.mkOfMulEqOne _ b' hb') hy rfl).symm
  have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hsv; exact zero_ne_one hsv
  have ha0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hav; exact zero_ne_one hav
  have hkk : Units.mk0 k hk0 * Units.mk0 _ hs0 = Units.mk0 _ ha0 := Units.ext h
  have hk1 : ξ.locK PP (Units.mk0 k hk0) = 1 := by
    have := congrArg (ξ.locK PP) hkk
    rwa [map_mul, key _ hs (Units.mk0 _ hs0) rfl, key _ ha (Units.mk0 _ ha0) rfl, mul_one] at this
  set y := Formalism.L2.Host.atFin PP (Units.mk0 k hk0) with hy
  have hyv : (y : PP.adicCompletion D.host.E) = algebraMap D.host.E (PP.adicCompletion D.host.E) k := rfl
  have ht := hK.tame PP (y * x⁻¹) (by
    unfold Formalism.L2.Host.IsUnitAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hyv, hv, hx, inv_one, mul_one]) (by
    have e : ((y * x⁻¹ : (PP.adicCompletion D.host.E)ˣ) : PP.adicCompletion D.host.E) - 1 =
        (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) * (x : PP.adicCompletion D.host.E)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hyv, sub_mul, mul_inv_cancel₀ x.ne_zero]
    unfold Formalism.L2.Host.IsUnitAt at hx
    rw [e, map_mul, map_inv₀, hx, inv_one, mul_one]
    have hlt : Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) < 1 := hk
    generalize Valued.v (algebraMap D.host.E (PP.adicCompletion D.host.E) k - x) = z at hlt
    rcases eq_or_ne z 0 with rfl | hz
    · exact zero_le'
    · rw [← WithZero.exp_log hz] at hlt ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]
      push_cast
      omega)
  have hk2 : ξ.loc PP y = 1 := hk1
  rw [map_mul, hk2, one_mul, map_inv, inv_eq_one] at ht
  exact ht

end GlobalTheory.BaseCmp

namespace GlobalTheory.BaseCmp

open Classical in

theorem liftKer_of_ne : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ),
    KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg →
    ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
      ∃ Gc : ℂ, UnitOff N Gc ∧ IsSBHalf eQ (lattice₂ R i) (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) ∧
        ∀ Tm, IsModel R i eQ fg Tm → φ = Tm (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hG i hV ξ χ ξR Q ω φ hK hQ N hN hNQ eg eQ fg hg hq hfg ϖ hϖ0 hϖ
  have hθ := kerDat_twoStep hC hK hQ hg hq hfg
  obtain ⟨Y, a, Gc, hU, hY, hΦ, hS⟩ := GlobalTheory.T.lift_datum_conjugate_half_finite_fourier_sum D G Pl0 T0 A Ks R F hC hG i hV ξR Q hQ
    (kerDat_xiR_ne D G Pl0 T0 A Ks R F hC i ξ χ ξR Q ω φ hK) N hN hNQ eQ hq ϖ hϖ0 hϖ
  refine ⟨Gc, hU, GlobalTheory.T.dilatedFlatDatum_isSBHalf_tameKernel D G Pl0 T0 A Ks R F hC hG i hV ξR Q hQ eQ hq ϖ hϖ0 hϖ Gc, fun Tm hTm => ?_⟩
  have h1 := GlobalTheory.DatumFourier.thetaAt_eq_sum (fun q : Y => q.1) (fun q : Y => a q.1) hθ
    (fun q => by rw [GlobalTheory.LatVac.cA_cA]; exact hY q.1 q.2)
    (fun t => by rw [hΦ t]; congr 1; exact (Finset.sum_coe_sort Y fun y => a y * R.ψ (symplO (Vc D i) (Wc D i) t y)).symm)
  have h2 : (fun x => Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) x)) =
      ∑ y ∈ Y, a y • fun t => halfInd eQ (lattice₂ R i) (t + y) := by
    funext t
    rw [← hS t, Finset.sum_apply]
    rfl
  have hvac : Tm (halfInd eQ (lattice₂ R i)) = fg := by simpa using hTm.vac
  rw [h1, h2, map_sum, ← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, hTm.trans _ (GlobalTheory.isSBHalf_halfInd eQ (lattice₂ R i)) _ (hY q.1 q.2), hvac]

end GlobalTheory.BaseCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentGroupPullbackEpsilonLift
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers TensorProduct TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CrysConn

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSSym

variable {R : Type} [CommRing R] {X : Scheme.{0}}

abbrev epsMap {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') : DualNumber B →+* DualNumber B' :=
  extMap σ σ.toSemilinearMap

@[simp] theorem fst_epsMap {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') (a : DualNumber B) :
    (epsMap σ a).fst = σ a.fst := add_zero _

@[simp] theorem snd_epsMap {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') (a : DualNumber B) :
    (epsMap σ a).snd = σ a.snd := zero_add _

theorem isDPMorphism_epsMap {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (σ : R →+* B) :
    IsDPMorphism (epsDP R) (extDP B δ) (epsMap σ) := by
  have hm : ∀ a ∈ RingHom.ker (fstHom R R R).toRingHom, (epsMap σ a).fst = 0 := fun a ha ↦ by
    have ha' : a.fst = 0 := ha
    rw [fst_epsMap, ha', map_zero]
  have hJ : ∀ a ∈ RingHom.ker (fstHom R R R).toRingHom, epsMap σ a ∈ J.comap (pr B B) := fun a ha ↦ by
    change (epsMap σ a).fst ∈ J
    rw [hm a ha]; exact J.zero_mem
  refine (isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 hJ, fun n hn a ha ↦ ?_⟩
  rcases n with _ | _ | n
  · exact absurd rfl hn
  · rw [zero_add, (epsDP R).dpow_one ha, (extDP B δ).dpow_one (hJ a ha)]
  · have e : (epsDP R).dpow (n + 1 + 1) a = 0 := squareZeroDividedPowers_dpow _ (by omega) a
    rw [e, map_zero]
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [fst_extDP, hm a ha, dpow_eval_zero _ (by omega)]; rfl
    · rw [snd_extDP, hm a ha, dpPred, dpow_eval_zero _ (by omega), zero_smul]; rfl

variable {s : X ⟶ Sp R} {s' : X ⟶ Sp (DualNumber R)}

def epsThick (hs : s' = s ≫ DeRham.epsRed R) (T : Thick (dp0 R) s) : Thick (epsDP R) s' where
  B := DualNumber T.B
  alg := (epsMap (algebraMap R T.B)).toAlgebra
  J := T.J.comap (pr T.B T.B)
  δ := extDP T.B T.δ
  nil := isDPNilpotent_extend _ T.nil
  dp := isDPMorphism_epsMap T.δ _
  B₀ := T.B₀
  π := T.π.comp (pr T.B T.B)
  surj := T.surj.comp fun r ↦ ⟨inl r, rfl⟩
  ker := fun b ↦ T.ker b.fst
  x := T.x
  w := by
    rw [hs, ← Category.assoc, T.w, ← Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun a ↦ congrArg T.π (fst_epsMap (algebraMap R T.B) a).symm

def epsFunctor (hs : s' = s ≫ DeRham.epsRed R) : Thick (dp0 R) s ⥤ Thick (epsDP R) s' where
  obj := epsThick hs
  map {T T'} f :=
    { φ := { epsMap (f.φ : T.B →+* T'.B) with
        commutes' := fun r ↦ TrivSqZeroExt.ext
          ((fst_epsMap _ _).trans ((congrArg _ (fst_epsMap _ _)).trans
            ((f.φ.commutes _).trans (fst_epsMap (algebraMap R T'.B) r).symm)))
          ((snd_epsMap _ _).trans ((congrArg _ (snd_epsMap _ _)).trans
            ((f.φ.commutes _).trans (snd_epsMap (algebraMap R T'.B) r).symm))) }
      φ₀ := f.φ₀
      comm := fun b ↦ (f.comm _).trans (congrArg T'.π (fst_epsMap (f.φ : T.B →+* T'.B) b).symm)
      dp := isDPMorphism_extMap f.dp _
      pt := f.pt }
  map_id T := Thick.hom_ext fun b ↦ TrivSqZeroExt.ext (fst_epsMap _ _) (snd_epsMap _ _)
  map_comp f g := Thick.hom_ext fun b ↦ TrivSqZeroExt.ext
    ((fst_epsMap _ _).trans ((congrArg _ (fst_epsMap _ _)).symm.trans (fst_epsMap _ _).symm))
    ((snd_epsMap _ _).trans ((congrArg _ (snd_epsMap _ _)).symm.trans (snd_epsMap _ _).symm))

def inlCoef (hs : s' = s ≫ DeRham.epsRed R) :
    CoefMap (algebraMap R (DualNumber R)) (O (dp0 R) s) (epsFunctor hs ⋙ O (epsDP R) s') where
  G := 𝟭 _
  α T := algebraMap T.B (DualNumber T.B)
  naturality {T T'} f b := TrivSqZeroExt.ext (fst_epsMap (f.φ : T.B →+* T'.B) (inl b)).symm
    ((map_zero (f.φ : T.B →+* T'.B)).symm.trans (snd_epsMap (f.φ : T.B →+* T'.B) (inl b)).symm)
  smul T r b := by
    have e : ∀ b : T.B, (inl (r • b) : DualNumber T.B) = epsMap (algebraMap R T.B) (inl r) * inl b := fun b ↦ by
      ext <;> simp [Algebra.smul_def]
    exact e b

theorem eq_zero_of_pull2 (hs : s' = s ≫ DeRham.epsRed R) {φ : X ⟶ X} (hφ : φ = 𝟙 X)
    (m : IsMor (dp0 R) s (epsDP R) s' (algebraMap R (DualNumber R)) φ) (z₀ z₁ : SecondDeRham s)
    (h : m.pull2 z₀ + (DualNumber.eps : DualNumber R) • m.pull2 z₁ = 0) : z₀ = 0 ∧ z₁ = 0 := by
  let n := CoefMap.restrict (O (epsDP R) s') (epsFunctor hs)
  let θ : (inlCoef hs).G ⟶ (m.coef.comp n).G :=
    { app := fun T ↦
        { φ := { algebraMap T.B (DualNumber T.B) with
            commutes' := fun r ↦ TrivSqZeroExt.ext (fst_epsMap (algebraMap R T.B) (inl r)).symm
              ((map_zero (algebraMap R T.B)).symm.trans (snd_epsMap (algebraMap R T.B) (inl r)).symm) }
          φ₀ := RingHom.id _
          comm := fun _ ↦ rfl
          dp := isDPMorphism_inl T.B T.δ
          pt := by
            change spMap (RingHom.id T.B₀) ≫ T.x = T.x ≫ φ
            rw [Cris.spMap_id, hφ]; simp }
      naturality := fun T T' f ↦ Thick.hom_ext fun b ↦ (inlCoef hs).naturality f b }
  have key : ∀ z, n.pull2 (m.pull2 z) = (inlCoef hs).pull2 z := fun z ↦
    (m.coef.pullCohomologyTwo_comp n z).symm.trans
      ((inlCoef hs).pullCohomologyTwo_eq_of_natTrans (m.coef.comp n) θ (fun _ _ ↦ rfl) z).symm
  have h1 := congrArg n.pull2 h
  rw [map_add, map_smul, key, key, map_zero] at h1
  obtain ⟨z₀, rfl⟩ := H2.mk_surjective _ z₀
  obtain ⟨z₁, rfl⟩ := H2.mk_surjective _ z₁
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, ← map_smul, ← map_add, H2.mk_eq_zero] at h1
  obtain ⟨f, hf⟩ := h1
  have alg : ∀ {B B' : Type} [CommRing B] [CommRing B'] (σ : B →+* B') (τ : R →+* B') (u : DualNumber B)
      (v w : DualNumber B') (a b : B'), epsMap σ u - v + w = inl a + epsMap τ DualNumber.eps * inl b →
      σ u.fst - v.fst + w.fst = a ∧ σ u.snd - v.snd + w.snd = b := fun σ τ u v w a b e ↦
    ⟨by simpa using congrArg TrivSqZeroExt.fst e, by simpa using congrArg TrivSqZeroExt.snd e⟩
  have hv := fun (T T' T'' : Thick (dp0 R) s) (a : T ⟶ T') (b : T' ⟶ T'') ↦
    alg (b.φ : T'.B →+* T''.B) (algebraMap R T''.B) (f T T' a) (f T T'' (a ≫ b)) (f T' T'' b) (z₀.1 T T' T'' a b)
      (z₁.1 T T' T'' a b) (congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') a) b)
  constructor
  · refine H2.mk_eq_zero.2 ⟨fun T T' a ↦ TrivSqZeroExt.fst (R := T'.B) (M := T'.B) (f T T' a), ?_⟩
    funext T T' T'' a b
    exact (hv T T' T'' a b).1
  · refine H2.mk_eq_zero.2 ⟨fun T T' a ↦ TrivSqZeroExt.snd (R := T'.B) (M := T'.B) (f T T' a), ?_⟩
    funext T T' T'' a b
    exact (hv T T' T'' a b).2

open GlobalTheory.Published

theorem exists_const_add (P : AbelianDeRham) {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (p : prim (epsDP R) (DeRham.epsRed R) A) :
    ∃ u v : primDR A, p = (constMor A).pull u + (DualNumber.eps : DualNumber R) • (constMor A).pull v := by
  obtain ⟨z, rfl⟩ := constMor_surjective P hA hg p
  induction z with
  | zero => exact ⟨0, 0, by simp only [map_zero, smul_zero, add_zero]⟩
  | add x y hx hy =>
    obtain ⟨u, v, e⟩ := hx
    obtain ⟨u', v', e'⟩ := hy
    refine ⟨u + u', v + v', ?_⟩
    rw [map_add, e, e', map_add, map_add, smul_add]
    abel
  | tmul r c =>
    refine ⟨r.fst • c, r.snd • c, ?_⟩
    rw [liftSemi_tmul, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, smul_smul, ← add_smul]
    congr 1
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_wedge (P : AbelianDeRham.Free) {A : Over (Sp R)} [GrpObj A] {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) (x y : HdR A) :
    ∃ Λ : SecondDeRham (A.hom ≫ 𝟙 _) →ₗ[R] R, ∀ c d : primDR A, Λ (cup _ c.1 d.1) = x c * y d - x d * y c := by
  obtain ⟨h0, -, -, -, e, he⟩ := P R A g hA hg
  let o : primDR A ≃ₗ[R] FirstDeRham (A.hom ≫ 𝟙 _) := LinearEquiv.ofTop _ h0
  let x' : Module.Dual R (FirstDeRham (A.hom ≫ 𝟙 _)) := x ∘ₗ o.symm.toLinearMap
  let y' : Module.Dual R (FirstDeRham (A.hom ≫ 𝟙 _)) := y ∘ₗ o.symm.toLinearMap
  have ex : ∀ c : primDR A, x' c.1 = x c := fun c => congrArg x (o.symm_apply_apply c)
  have ey : ∀ c : primDR A, y' c.1 = y c := fun c => congrArg y (o.symm_apply_apply c)
  refine ⟨exteriorPower.alternatingMapLinearEquiv (wedgeDual x' y') ∘ₗ e.symm.toLinearMap, fun c d ↦ ?_⟩
  rw [← he, LinearMap.comp_apply, LinearEquiv.coe_coe, e.symm_apply_apply]
  simp [wedgeDual, ex, ey]

set_option maxHeartbeats 1000000 in

theorem snd_polForm (P : AbelianDeRham) {A : Over (Sp R)} [GrpObj A] {n : ℕ} (hA : IsAbelianScheme A)
    (hn : SmoothOfRelativeDimension n A.hom) {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left}
    (h : IsGrpPullback A A' (DeRham.epsRed R) i) {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {π' : A'.left ⟶ Y}
    {ψ : LinearMap.BilinForm R (HdR A)} (hψ : IsPolForm (dp0 R) (𝟙 _) A (L.pull (i ≫ π')) ψ)
    {ψ' : LinearMap.BilinForm (DualNumber R) (HdR A')} (hψ' : IsPolForm (dp0 _) (𝟙 _) A' (L.pull π') ψ')
    {f g k k' : HdR A} {d d' : Crys (epsDP R) (DeRham.epsRed R) A}
    (ed : ∀ c : primDR A, d ((constMor A).pull c) = inl (f c) + inr (k c))
    (ed' : ∀ c : primDR A, d' ((constMor A).pull c) = inl (g c) + inr (k' c)) :
    (ψ' (crysToDR (epsDP R) h d) (crysToDR (epsDP R) h d')).snd = ψ f k' + ψ k g := by
  obtain ⟨N, a, b, hc, rfl⟩ := hψ
  obtain ⟨N', a', b', hc', rfl⟩ := hψ'
  have c₀ := isChern_pull (constMor A).isMor hc
  have c₁ := isChern_pull (liftMor (epsDP R) h).isMor hc'
  have hl := pull_isLB hL (i ≫ π')
  have iso := (isChern_existsUnique_and_iso _ _ (epsDP R) _ (A.hom ≫ DeRham.epsRed R)).2
  have c₀' := iso _ _ (pull_isLB hl _) (pull_isLB hL (Over.Hom.left (𝟙 A) ≫ i ≫ π'))
    (LBIso.chartPull (Geo.Tor.chartPullPull (L.pull (i ≫ π')) _ _ rfl) (chartPullSame L _ _ _ _ fun _ => rfl)
      (ChernExists.lbIso_refl hl)) _ c₀
  have c₁' := iso _ _ (pull_isLB (pull_isLB hL π') i) hl
    (LBIso.chartPull (Geo.Tor.chartPullPull (L.pull π') i i rfl) (chartPullSame L _ _ _ i fun _ => rfl)
      (ChernExists.lbIso_refl (pull_isLB hL π'))) _ c₁
  rw [show Over.Hom.left (𝟙 A) ≫ i ≫ π' = i ≫ π' from Category.id_comp _] at c₀'
  have hz := ((isChern_existsUnique_and_iso _ _ (epsDP R) _ _).1 _ hl).unique c₁' c₀'
  choose u v huv using fun j ↦ exists_const_add P hA hn ((liftMor (epsDP R) h).pull (a' j))
  choose w x hwx using fun j ↦ exists_const_add P hA hn ((liftMor (epsDP R) h).pull (b' j))
  have hz' : (constMor A).isMor.pull2 (∑ j, cup _ (u j).1 (w j).1 - ∑ j, cup _ (a j).1 (b j).1) +
      (DualNumber.eps : DualNumber R) •
        (constMor A).isMor.pull2 (∑ j, (cup _ (u j).1 (x j).1 + cup _ (v j).1 (w j).1)) = 0 := by
    rw [map_sub, ← hz, sub_add_eq_add_sub, sub_eq_zero, map_sum, map_sum, map_sum, Finset.smul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have e₁ : (liftMor (epsDP R) h).isMor.pull1 (a' j).1 = (constMor A).isMor.pull1 (u j).1 +
      (DualNumber.eps : DualNumber R) • (constMor A).isMor.pull1 (v j).1 := congrArg Subtype.val (huv j)
    have e₂ : (liftMor (epsDP R) h).isMor.pull1 (b' j).1 = (constMor A).isMor.pull1 (w j).1 +
      (DualNumber.eps : DualNumber R) • (constMor A).isMor.pull1 (x j).1 := congrArg Subtype.val (hwx j)
    simp only [map_add, IsMor.pullCohomologyTwo_cup, e₁, e₂,
      map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_smul, DualNumber.eps_mul_eps, zero_smul,
      add_zero]
    abel
  obtain ⟨z₀, z₁⟩ := eq_zero_of_pull2 (s := A.hom ≫ 𝟙 _) (by rw [Category.comp_id]) rfl (constMor A).isMor _ _ hz'
  obtain ⟨Λ₁, e₁⟩ := exists_wedge P.1 hA hn f k'
  obtain ⟨Λ₂, e₂⟩ := exists_wedge P.1 hA hn k g
  obtain ⟨Λ₃, e₃⟩ := exists_wedge P.1 hA hn f g
  have t₁ := congrArg Λ₁ (sub_eq_zero.1 z₀)
  have t₂ := congrArg Λ₂ (sub_eq_zero.1 z₀)
  have t₃ := congrArg Λ₃ z₁
  simp only [map_sum, map_add, map_zero, e₁, e₂, e₃] at t₁ t₂ t₃
  rw [wedgeForm_apply, wedgeForm_apply, wedgeForm_apply, ← t₁, ← t₂, ← add_zero (_ + _ : R), ← t₃,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, snd_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [crysToDR_apply, huv, hwx, map_add, map_smul, ed, ed', smul_eq_mul]
  simp
  ring

end GlobalTheory.KSSym

namespace GlobalTheory.KSSym

open NumberField Formalism.L2.Pj MonObj

theorem ks_symm : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X)
    (x' : Sp (DualNumber K) ⟶ Xo.X) (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp (DualNumber K))) [GrpObj A']
    (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left)
    (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) (ψ : LinearMap.BilinForm K (GlobalTheory.DeRham.HdR A)),
    IsGrpPullback A Xo.univ.t.G x π → IsGrpPullback A' Xo.univ.t.G x' π' → i ≫ π' = π →
    GlobalTheory.DeRham.IsPolForm (GlobalTheory.Cris.dp0 K) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ →
    ∀ f g k k' : GlobalTheory.DeRham.HdR A, GlobalTheory.DeRham.IsFilLift h f k → GlobalTheory.DeRham.IsFilLift h g k' →
      ψ f k' + ψ k g = 0 := by
  rintro Pr E _ _ _ H Dw l Xo K _ x x' A _ A' _ π π' i h ψ hπ hπ' rfl hψ f g k k' ⟨d, hd, ed⟩ ⟨d', hd', ed'⟩
  have hA := PolPull.isAbelianScheme_of_isGrpPullback (ObjDim.isAbelianScheme Xo.univ) hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨ψ', hψ', iso, -⟩ := GlobalTheory.PolExistsRing.polForm_exists Pr.p5 Xo hπ'
  rw [← snd_polForm Pr.p5 hA gA h Xo.univ.t.PP.isLB hψ hψ' ed ed', iso _ hd _ hd']
  rfl

end GlobalTheory.KSSym
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharEntireNeZeroAutomorphy
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem thetaChar_entire_ne_zero_automorphy : ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → Half a → Half b → Differentiable ℂ (thetaChar τ a b) ∧ (∃ z, thetaChar τ a b z ≠ 0) ∧ ∀ M N z, thetaChar τ a b (z + perV τ M N) = autV τ a b M N z * thetaChar τ a b z := by
  intro g τ a b hs hp ha hb
  obtain ⟨h1, -⟩ := GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g a b ha hb
  obtain ⟨hd, hne⟩ := h1 τ hs hp
  refine ⟨hd, hne, fun M N z => ?_⟩
  rw [perV, autV]
  unfold cv
  rw [GlobalTheory.ThetaAH.thetaChar_add_period hs a b z M N]
  congr 1
  rw [dotProduct_comm b]
  ring_nf

end GlobalTheory.MBLow.Cl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionNormComplexPointsEqTwoPiPowStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = x) → Nonempty (KeySec Xo c) → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ C : ℝ, 0 < C ∧ |Real.log C| ≤ 2 * (g : ℝ) * Real.log (2 * Real.pi) ∧ ∀ k, ∀ y ∈ (U.X k).dom, homN U x (wtOf Dw 0 (-4)) (K : Rul Xo c) ⟨k, y⟩ = C := by
  first | exact @GlobalTheory.KeyArchNorm.homN_key_const | exact GlobalTheory.KeyArchNorm.homN_key_const | (intros; apply GlobalTheory.KeyArchNorm.homN_key_const <;> assumption)
end

