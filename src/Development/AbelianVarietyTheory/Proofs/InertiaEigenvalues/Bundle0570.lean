import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0527
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0555
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0537
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EOsurjOneX
import Formalism.LocalRingCardinality.SpanPowerMembership
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0551
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0548
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachModuleOfXPowSmulFrobeniusGamma
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0539
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0529
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0557
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCocyclesMemSpanPushoutSummandLattice
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.Pass.LocDual.OneX

theorem span_stable (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (γ : GE D.nd) :
    ∀ v ∈ Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)),
      actK i r Xs x γ v ∈ Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) := by
  let f : (Fin a → Fin D.R.nV → KK D.nd i) →ₗ[KK D.nd i] (Fin a → Fin D.R.nV → KK D.nd i) :=
    LinearMap.pi fun b => Matrix.toLin' (mapM (toK D.nd i) (rTwO D.nd i r (x b)) γ) ∘ₗ LinearMap.proj b
  have hf : ∀ v, f v = actK i r Xs x γ v := fun v => rfl
  intro v hv
  rw [← hf]
  have h : Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i)) ≤
      (Submodule.span (KK D.nd i) (Y : Set (Fin a → Fin D.R.nV → KK D.nd i))).comap f := by
    refine Submodule.span_le.2 fun y hy => ?_
    rw [SetLike.mem_coe, Submodule.mem_comap, hf]
    exact Submodule.subset_span (hst γ y hy)
  exact h hv

end GlobalTheory.Pass.LocDual.OneX

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.Pass.LocDual.OneX.main : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))),
    GoodR D.nd i r → ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M)
      (F : Finset (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)),
      (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ⊆ cutCoc i w hw r Xs M →
      ∃ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw),
        IsSummandTw i w hw r Xs X ∧
        Submodule.span (Br.OLL D.nbr i w hw) (F : Set (Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T)) ≤
          BlochKatoDuality.spanPush (Br.PD D.loc D.nbr i w hw) X (locU i w hw M hSub.1) (Br.locLat D.nbr i w hw M) := by
  intro D hF i r hr Xs w hw n hP k M hSub F hFs
  obtain ⟨a, x, E, Y, hYfg, hst, hE, hc⟩ := GlobalTheory.Pass.LocDual.OneX.cutCoc_finset_common D i w hw r Xs M F hFs
  have hC := GlobalTheory.BlockSum.exists_stable_compl_actK D i r Xs hr x (Submodule.span (KK D.nd i) (Y : Set _))
    (fun γ => GlobalTheory.Pass.LocDual.OneX.span_stable D i r Xs x Y hst γ)
  refine ⟨GlobalTheory.Pass.LocDual.OneX.XG i w hw r Xs hr x Y hst,
    GlobalTheory.Pass.LocDual.OneX.isSummandTw_XG D i w hw r Xs hr x Y hst hC, ?_⟩
  obtain ⟨LY, hLY⟩ := GlobalTheory.T.localIntegerSpanOfImage_is_stable_lattice D i w hw r Xs hr x Y hst hYfg
  have hy := GlobalTheory.Pass.LocDual.OneX.yfun_Z1fT D hF i r hr Xs w hw n hP x Y hst E hE LY hLY
  apply Submodule.span_le.2
  intro c hcF
  obtain ⟨φ, hφ, rfl⟩ := hc c hcF
  obtain ⟨φ', hG, hpush⟩ := GlobalTheory.Pass.LocDual.OneX.PushEq.main D i w hw r Xs hr x Y hst E hE M LY hLY φ hφ
  unfold BlochKatoDuality.spanPush
  exact Submodule.subset_span (R := Br.OLL D.nbr i w hw) (M := Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T) ⟨LY, φ', hG, ⟨_, hy.1⟩, hy, (hpush ⟨_, hy.1⟩ rfl).symm⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGapNonemptyAndRecordNonempty
section
open Formalism Formalism.BasicNotions
namespace GlobalTheory.MemLoc

theorem localGap_nonempty : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R),
    Nonempty (Formalism.BasicNotions.Examples₂.LocalGap H) := by
  intro R H
  obtain ⟨L, A, ⟨T⟩⟩ := exists_locTheory_tied
  exact ⟨⟨L, A, T⟩⟩

theorem record_nonempty : Nonempty Formalism.BasicNotions.D7 :=
  Formalism.BasicNotions.Examples₂.record_nonempty_of_localGap (localGap_nonempty _)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateEndomorphismUnique
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK

namespace GlobalTheory.PZ

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem resCard_eq_card_residueField :
    resCard K = Nat.card (IsLocalRing.ResidueField ↥(OL K)) :=
  (GlobalTheory.AinfK.main l K).1.symm

theorem one_lt_resCard [Finite (IsLocalRing.ResidueField ↥(OL K))] : 1 < resCard K := by
  rw [resCard_eq_card_residueField]
  exact Finite.one_lt_card

theorem isLubinTateSeries_ltSeries [Finite (IsLocalRing.ResidueField ↥(OL K))] (π : ↥(OL K)) :
    IsLubinTateSeries π (ltSeries K π) := by
  have hq := one_lt_resCard K
  refine ⟨?_, ?_, fun n => ?_⟩
  · simp [ltSeries, show resCard K ≠ 0 by omega]
  · simp [ltSeries, PowerSeries.coeff_X_pow, show 1 ≠ resCard K by omega]
  · rw [← resCard_eq_card_residueField, ltSeries, add_sub_cancel_right, PowerSeries.coeff_C_mul]
    exact dvd_mul_right _ _

theorem subst_ltSeries (π : ↥(OL K)) {φ : PowerSeries ↥(OL K)} (h : PowerSeries.constantCoeff φ = 0) :
    PowerSeries.subst φ (ltSeries K π) = PowerSeries.C π * φ + φ ^ resCard K := by
  have hs : PowerSeries.HasSubst φ := PowerSeries.HasSubst.of_constantCoeff_zero' h
  rw [ltSeries, PowerSeries.subst_add hs, PowerSeries.subst_pow hs, PowerSeries.subst_mul hs,
    PowerSeries.subst_X hs, PowerSeries.subst_C]
  rfl

theorem isLTEndo_iff_eq_lubinTateHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l)
    [Finite (IsLocalRing.ResidueField ↥(OL K))] (π : ↥(OL K)) (hπ : Irreducible π),
    ∃ hf : IsLubinTateSeries π (ltSeries K π),
      ∀ (a : ↥(OL K)) (φ : PowerSeries ↥(OL K)),
        IsLTEndo K π a φ ↔ φ = (lubinTateHom hπ hf hf a).toPowerSeries := by
  intro l _ K _ π hπ
  refine ⟨isLubinTateSeries_ltSeries K π, fun a φ => ⟨?_, ?_⟩⟩
  · rintro ⟨h0, h1, h2⟩
    exact eq_lubinTateHom_toPowerSeries hπ _ _ a h0 h1 (by rw [subst_ltSeries K π h0, h2])
  · rintro rfl
    have h0 := (lubinTateHom hπ (isLubinTateSeries_ltSeries K π) (isLubinTateSeries_ltSeries K π) a).constantCoeff_eq_zero
    refine ⟨h0, coeff_one_lubinTateHom hπ _ _ a, ?_⟩
    rw [← subst_ltSeries K π h0]
    exact subst_lubinTateHom hπ _ _ a

end GlobalTheory.PZ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTatePeriodThetaKernel
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.AinfK GroundTheory.LocalField.FormalGroup GlobalTheory.AcrisK
open GlobalTheory.Prism IsLocalRing
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LTPeriodKerSq

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem intToOC_mem_max {π : ↥(OL K)} (hπ : Irreducible π) : intToOC K π ∈ maximalIdeal (OC l) := by
  obtain ⟨n, hn⟩ := GlobalTheory.AinfK.exists_l_dvd_pow hπ
  have h1 := map_dvd (intToOC K) hn
  rw [map_natCast, map_pow] at h1
  by_contra h
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
  exact (inferInstance : Fact ¬IsUnit ((l : ℕ) : OC l)).out (isUnit_of_dvd_unit h1 (h.pow _))

theorem not_sq_dvd {π : ↥(OL K)} (hπ : Irreducible π) {p : PreTilt (OC l) l} (hp : p.untilt = intToOC K π)
    (r : ℕ) {u v : AK K} (hu : u = inO K π * v + v ^ (r + 2))
    (hs : eta π p ^ 2 ∣ inO K π + u ^ (r + 1)) : False := by
  have hϖm := intToOC_mem_max hπ
  obtain ⟨c, hc⟩ := hs
  have hθ : intToOC K π + thetaK K u ^ (r + 1) = 0 := by
    have := congrArg (thetaK K) hc
    rwa [map_add, map_pow, thetaK_inO, map_mul, map_pow, thetaK_eta hp, zero_pow two_ne_zero, zero_mul] at this
  have hre : red K (eta π p) = p := by
    rw [eta, map_sub, red_teich, red_inO_eq_zero hπ.not_isUnit, sub_zero]
  have hr : red K v ^ ((r + 2) * (r + 1)) = p ^ 2 * red K c := by
    have := congrArg (red K) hc
    rw [map_add, red_inO_eq_zero hπ.not_isUnit, zero_add, map_pow, hu, map_add, map_mul,
      red_inO_eq_zero hπ.not_isUnit, zero_mul, zero_add, map_pow, map_mul, map_pow, hre, ← pow_mul] at this
    exact this
  have ha : (red K v).untilt ^ ((r + 2) * (r + 1)) = intToOC K π ^ 2 * (red K c).untilt := by
    have := congrArg PreTilt.untilt hr
    rwa [map_pow, map_mul, map_pow, hp] at this
  obtain ⟨d, hd⟩ := dvd_thetaK_sub hπ v
  have hz1 : thetaK K u = intToOC K π * thetaK K v + thetaK K v ^ (r + 2) := by
    rw [hu, map_add, map_mul, thetaK_inO, map_pow]
  have hmp : (maximalIdeal (OC l)).IsPrime := inferInstance
  have ham : (red K v).untilt ∈ maximalIdeal (OC l) :=
    hmp.mem_of_pow_mem ((r + 2) * (r + 1)) (by
      rw [ha]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hϖm 2 two_pos))
  have hz2m : thetaK K v ∈ maximalIdeal (OC l) := by
    rw [show thetaK K v = (red K v).untilt + intToOC K π * d by linear_combination hd]
    exact Ideal.add_mem _ ham (Ideal.mul_mem_right _ _ hϖm)
  have hS : (∑ i ∈ Finset.range (r + 2), thetaK K v ^ i * (red K v).untilt ^ (r + 2 - 1 - i)) ∈
      maximalIdeal (OC l) := Ideal.sum_mem _ fun i _ => by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ham _ (by omega))
    · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hz2m _ hi0)
  have e1 := geom_sum₂_mul (thetaK K v) (red K v).untilt (r + 2)
  have e2 := geom_sum₂_mul (thetaK K u) ((red K v).untilt ^ (r + 2)) (r + 1)
  have ha' : ((red K v).untilt ^ (r + 2)) ^ (r + 1) = intToOC K π ^ 2 * (red K c).untilt := by
    rw [← pow_mul, ha]
  set S := ∑ i ∈ Finset.range (r + 2), thetaK K v ^ i * (red K v).untilt ^ (r + 2 - 1 - i)
  set S' := ∑ i ∈ Finset.range (r + 1), thetaK K u ^ i * ((red K v).untilt ^ (r + 2)) ^ (r + 1 - 1 - i)
  have key : intToOC K π * (1 + intToOC K π * (red K c).untilt + S' * (thetaK K v + S * d)) = 0 := by
    linear_combination hθ + e2 - ha' - S' * hz1 + S' * e1 - S' * S * hd
  have hϖ0 : intToOC K π ≠ 0 := (map_ne_zero_iff _ (GlobalTheory.BKReal.intToOC_injective K)).2 hπ.ne_zero
  have h1 := (mul_eq_zero.1 key).resolve_left hϖ0
  have hmem : (1 : OC l) ∈ maximalIdeal (OC l) := by
    rw [show (1 : OC l) = -(intToOC K π * (red K c).untilt + S' * (thetaK K v + S * d)) by
      linear_combination h1]
    exact neg_mem (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hϖm)
      (Ideal.mul_mem_left _ _ (Ideal.add_mem _ hz2m (Ideal.mul_mem_right _ _ hS))))
  exact (maximalIdeal.isMaximal (OC l)).ne_top ((Ideal.eq_top_iff_one _).2 hmem)

theorem eq_zero_of_red {π : ↥(OL K)} (hπ : Irreducible π) (r : ℕ) {ω : AK K}
    (hF : frobq K ω = inO K π * ω + ω ^ (r + 2)) (h0 : red K ω = 0) : ω = 0 := by
  have := complete_pi hπ
  have hπ0 : inO K π ≠ 0 := fun h => one_ne_zero (eq_zero_of_mul_pi hπ 1 (by rw [h, mul_zero]))
  have key : ∀ n : ℕ, inO K π ^ (n + 1) ∣ ω := fun n => by
    induction n with
    | zero =>
      rw [zero_add, pow_one, ← Ideal.mem_span_singleton, ← ker_red hπ]
      exact h0
    | succ n ih =>
      obtain ⟨y, rfl⟩ := ih
      obtain ⟨x, hx⟩ := (frobq_bijective K).2 (y + inO K π ^ (n * r + n + r) * y ^ (r + 2))
      rw [map_mul, map_pow, frobq_inO] at hF
      have h1 : frobq K y = frobq K (inO K π * x) := by
        refine mul_left_cancel₀ (pow_ne_zero (n + 1) hπ0) ?_
        rw [hF, map_mul, frobq_inO, hx]
        ring
      exact ⟨x, by rw [(frobq_bijective K).1 h1]; ring⟩
  exact GlobalTheory.Per.AinfComplete.eq_zero_of_haus (inO K π) ω fun n =>
    Ideal.mem_span_singleton.2 ((pow_dvd_pow _ n.le_succ).trans (key n))

open GlobalTheory.Per.AinfComplete in

theorem not_mem_sq {π : ↥(OL K)} (hπ : Irreducible π) {ω : AK K} (hω0 : ω ≠ 0) (hθ : thetaK K ω = 0)
    (hF : frobq K ω = inO K π * ω + ω ^ resCard K) : ω ∉ RingHom.ker (thetaK K) ^ 2 := by
  intro hω2
  obtain ⟨p, hp⟩ := GlobalTheory.MemLoc.FundOnto.untilt_surjective l (intToOC K π)
  have hker := ker_thetaK hπ hp
  have hq : 2 ≤ resCard K :=
    hl.out.two_le.trans (Nat.le_self_pow (card_res' K).1 l)
  obtain ⟨r, hr⟩ : ∃ r, resCard K = r + 2 := ⟨resCard K - 2, by omega⟩
  have hr' : l ^ fK K = r + 2 := hr
  rw [hr] at hF
  have hdiv : ∀ x, thetaK K x = 0 ↔ eta π p ∣ x := fun x => by
    rw [← RingHom.mem_ker, hker, Ideal.mem_span_singleton]
  have hη0 : eta π p ≠ 0 := fun h => hω0 (zero_dvd_iff.1 (h ▸ (hdiv ω).1 hθ))
  have hηp : Prime (eta π p) := by
    rw [← Ideal.span_singleton_prime hη0, ← hker]
    exact RingHom.ker_isPrime _
  have hϖ0 : intToOC K π ≠ 0 := (map_ne_zero_iff _ (GlobalTheory.BKReal.intToOC_injective K)).2 hπ.ne_zero
  rw [hker, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hω2
  obtain ⟨G, hG⟩ := (frobq_bijective K).2.hasRightInverse
  let w : ℕ → AK K := fun n => G^[n] ω
  have hw : ∀ n, frobq K (w (n + 1)) = w n := fun n => by
    simp only [w, Function.iterate_succ_apply']
    exact hG _
  have hFw : ∀ n, frobq K (w n) = inO K π * w n + w n ^ (r + 2) := fun n => by
    induction n with
    | zero => exact hF
    | succ n ih =>
      refine (frobq_bijective K).1 ?_
      rw [map_add, map_mul, map_pow, frobq_inO, hw, ih]
  have hrec : ∀ n, w n = inO K π * w (n + 1) + w (n + 1) ^ (r + 2) := fun n => by rw [← hFw, hw]
  have hall : ∀ n, eta π p ^ 2 ∣ w n := fun n => by
    induction n with
    | zero => exact hω2
    | succ n ih =>
      rw [hrec n] at ih
      by_cases hu : eta π p ∣ w (n + 1)
      · obtain ⟨a, ha⟩ := hu
        rw [ha, show inO K π * (eta π p * a) + (eta π p * a) ^ (r + 2) =
          eta π p * (inO K π * a + eta π p * (eta π p ^ r * a ^ (r + 2))) by ring, sq,
          mul_dvd_mul_iff_left hη0, dvd_add_left (dvd_mul_right _ _)] at ih
        rcases hηp.dvd_or_dvd ih with h | h
        · exact absurd (thetaK_inO π ▸ (hdiv _).2 h) hϖ0
        · rw [ha, sq]
          exact mul_dvd_mul_left _ h
      · rw [show inO K π * w (n + 1) + w (n + 1) ^ (r + 2) =
          w (n + 1) * (inO K π + w (n + 1) ^ (r + 1)) by ring] at ih
        exact (not_sq_dvd hπ hp r (hrec (n + 1)) (hηp.pow_dvd_of_dvd_mul_left 2 hu ih)).elim
  have hre : red K (eta π p) = p := by
    rw [eta, map_sub, red_teich, red_inO_eq_zero hπ.not_isUnit, sub_zero]
  have hred : ∀ n, red K ω = red K (w n) ^ (r + 2) ^ n := fun n => by
    induction n with
    | zero => simp [w]
    | succ n ih => rw [ih, ← hw n, red_frobq, hr', ← pow_mul, ← pow_succ']
  have hpu : ¬ IsUnit p := fun h => intToOC_mem_max hπ (hp ▸ h.map PreTilt.untilt)
  have h1 : IsNilpotent (Perfection.coeff (ModP (OC l) l) l 0 p) :=
    nilpotent_of_not_isUnit l _ fun h => hpu (perfection_isUnit _ h)
  refine hω0 (eq_zero_of_red hπ r hF (perfection_haus (p := l) (R := ModP (OC l) l) h1 (red K ω) fun n => ?_))
  have h2 : p ∣ red K (w n) := by
    rw [← hre]
    exact map_dvd _ ((dvd_pow_self _ two_ne_zero).trans (hall n))
  have h3 : p ^ n ∣ red K ω := by
    rw [hred n]
    exact (pow_dvd_pow p (Nat.lt_pow_self (by omega)).le).trans (pow_dvd_pow_of_dvd h2 _)
  exact h3

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∀ ω : AK K, ω ≠ 0 → thetaK K ω = 0 → frobq K ω = inO K π * ω + ω ^ resCard K →
      (∀ (g : ↥(GK K)) (a : ↥(OL K)) (φ : PowerSeries ↥(OL K)), (a : ↥K.1) = (χ g : ↥K.1) → IsLTEndo K π a φ →
        ∀ n : ℕ, gal K g ω - ∑ j ∈ Finset.range n, inO K (PowerSeries.coeff j φ) * ω ^ j ∈ RingHom.ker (thetaK K) ^ n) →
      ω ∉ RingHom.ker (thetaK K) ^ 2 := by
  intro l _ K χ π z hLT ω hω0 hθ hF _
  exact not_mem_sq hLT.1 hω0 hθ hF

end GlobalTheory.LTPeriodKerSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.DdREqDcris

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem ιV_mulVB (c : K₀) (d : V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [mulVdR, ιV, mulVB, ← IsScalarTower.algebraMap_apply]

theorem act_mulVB (g : G) (c : K₀) (d : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (actVB PD ρ g d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [actVB, mulVB]

theorem mulVB_mem (c : K₀) {d : V ⊗[Qp] B} (hd : d ∈ Dcris PD ρ) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d ∈ Dcris PD ρ := by
  rw [CrisDR.mem_Dcris_iff] at hd ⊢
  intro g
  rw [act_mulVB, hd g]

theorem mulVdR_one (y : V ⊗[Qp] BdR) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) 1 y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v b => simp [mulVdR]

theorem ιV_injective : Function.Injective (ιV PD (LL := LL) (V := V)) := by
  rw [injective_iff_map_eq_zero]
  intro d hd
  refine CrisDR.eq_zero_of_sum PD (LL := LL) (m := 1) (fun _ => (1 : K)) ?_ (fun _ => d) ?_ 0
  · intro b hb i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    apply PD.ι_inj
    simpa using hb
  · simp [hd]

theorem map_Dcris_eq (hb : Function.Surjective (algebraMap K₀ K))
    (h : ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (c i) (ιV PD (LL := LL) (V := V) (d i))) :
    (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ := by
  apply le_antisymm
  · rintro _ ⟨d, hd, rfl⟩
    have := CrisDR.mul_ι_mem PD ρ (1 : K) hd
    rwa [mulVdR_one] at this
  · intro y hy
    obtain ⟨m, c, d, hd, rfl⟩ := h y hy
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c₀, hc₀⟩ := hb (c i)
    rw [← hc₀, ← ιV_mulVB]
    exact Submodule.mem_map_of_mem (mulVB_mem PD ρ c₀ (hd i))

theorem FildR_eq (hb : Function.Surjective (algebraMap K₀ K))
    (h : (Dcris PD ρ).map (ιV PD (LL := LL) (V := V)) = DdR PD ρ) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a = (FilCris PD ρ a ⊓ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))).map
      (ιV PD (LL := LL) (V := V)) := by
  apply le_antisymm
  · rintro y ⟨⟨hy, hτ⟩, hF⟩
    rw [← h] at hy
    obtain ⟨d, hd, rfl⟩ := hy
    refine Submodule.mem_map_of_mem ⟨⟨hd, hF⟩, hd, ?_⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hτ ⊢
    intro c
    apply ιV_injective PD (LL := LL)
    rw [ιV_mulVB, hτ, map_smul]
    rfl
  · rintro _ ⟨d, ⟨⟨hd, hF⟩, -, hτ⟩, rfl⟩
    refine ⟨⟨h ▸ Submodule.mem_map_of_mem hd, ?_⟩, hF⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at hτ ⊢
    intro c
    obtain ⟨c₀, rfl⟩ := hb c
    rw [← ιV_mulVB, hτ, map_smul]
    rfl

end Abstract

theorem map_Dcris_eq_DdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → (Dcris (P.PD K) ρ).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) = DdR (P.PD K) ρ ∧ ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, FiniteDimensional ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧ finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = finrank ↥LL.1 V ∧ ∀ a : ℤ, FildR (P.PD K) ρ τ a = (FilCris (P.PD K) ρ a ⊓ DcrisL (P.PD K) ρ (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))).map (ιV (P.PD K) (LL := ↥LL.1) (V := V)) := by
  intro l _ P AI T K LL hb V _ _ _ _ _ ρ hc
  obtain ⟨hdr, hspan⟩ := CrisDR.isDR_of_isCrys l P AI T K LL V ρ hc
  have h := map_Dcris_eq (P.PD K) ρ hb.2 hspan
  refine ⟨h, fun τ => ?_⟩
  obtain ⟨h1, -, h2⟩ := (GlobalTheory.T.deRhamComponents_crystallineLetters_finrank l P AI T K LL V ρ).1 τ
  exact ⟨h1, h2 hdr, FildR_eq (P.PD K) ρ hb.2 h τ⟩

end GlobalTheory.Per.DdREqDcris
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachModuleOfXPowSmulFrobeniusGammaStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wachModule_of_X_pow_smul_frobenius_gamma : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M a : ℕ) (m : W.DD T), W.φD T m - m ∈ invN W T (W.Q ^ M) → W.γ T m - m ∈ aN W T letπ → W.X ^ a • m ∈ W.N T → m ∈ W.N T := by
  first | exact @GlobalTheory.NL.ExtLattice.mem_N | exact GlobalTheory.NL.ExtLattice.mem_N | (intros; apply GlobalTheory.NL.ExtLattice.mem_N <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicTraceGeWhittakerDimensionGLnStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_trace_ge_whittakerDimension_GLn : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ χ : Gn g N → ℂ, IsChar χ → ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤ (tr (eJ g N k s ψ) χ).re := by
  first | exact @GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison | exact GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison | (intros; apply GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MkSumProdHsymmMulProdOneSubStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mk_sum_hsymm_mul_prod_one_sub_eq_one : ∀ {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ),
    PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) *
      ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) = 1 := by
  first | exact @GlobalTheory.JSW.mk_sum_prod_hsymm_mul_prod_one_sub | exact GlobalTheory.JSW.mk_sum_prod_hsymm_mul_prod_one_sub | (intros; apply GlobalTheory.JSW.mk_sum_prod_hsymm_mul_prod_one_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegCycPowerBlockCrysDeRhamJumpsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negCycPowerBlock_crys_deRham_jumps : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (t : ℕ) (ρ : Representation ↥LL.1 ↥(GK K) (Fin t → ↥LL.1)), (∀ g v (c : Fin t), ρ g v c = (((cycLL (P.PD K) ↥LL.1 g)⁻¹ ^ (c : ℕ) : (↥LL.1)ˣ) : ↥LL.1) * v c) → IsCrys (P.PD K) ρ ∧ IsDR (P.PD K) ρ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = if 0 ≤ a ∧ a < (t : ℤ) then 1 else 0 := by
  first | exact @GlobalTheory.negCycBlock_jumps | exact GlobalTheory.negCycBlock_jumps | (intros; apply GlobalTheory.negCycBlock_jumps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyCompletedLocalizationPrismStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_completedLocalizationPrism : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A), GenAway B f d → Nonempty (LocP B f d) := by
  first | exact @GlobalTheory.BSP.GenAway₂ | exact GlobalTheory.BSP.GenAway₂ | (intros; apply GlobalTheory.BSP.GenAway₂ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMemOfFrobeniusLinkedBoundedSeriesIdealsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_of_frobenius_linked_boundedSeries_ideals : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (l e a M₁ M₂ : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (J : ZMod a → Set K⟦X⟧), (∀ τ, ∀ x ∈ J τ, ∀ y ∈ J τ, x + y ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∃ c : ℝ, ∀ n, ‖coeff n x‖ ≤ c) → (∀ τ, ∃ g ∈ J τ, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → (∀ τ, ∀ h ∈ J (τ - 1), E K l e ^ M₁ * frob K l h ∈ J τ) → (∀ τ, ∀ h ∈ J τ, ∀ i < l, frobSlice l i (E K l e ^ M₂ * h) ∈ J (τ - 1)) → ∀ τ, (1 : K⟦X⟧) ∈ J τ := by
  first | exact @GlobalTheory.BK.GcdCore.one_mem | exact GlobalTheory.BK.GcdCore.one_mem | (intros; apply GlobalTheory.BK.GcdCore.one_mem <;> assumption)
end

