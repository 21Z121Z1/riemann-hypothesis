import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0464
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0460
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.LevelLetterCocycles.MemPrimesOverOfMem
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevInductionGrowBoundOfPresentation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0197
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0487
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionClosedDiscBreuilKisin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedActionAcrisTensorSubEventuallyLpow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.OCrCont

open Filter Topology

theorem galOCr_sub_smul_eventually {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    (r : OCr l O) (m : ℕ) :
    ∀ᶠ h in nhds (1 : GQ l), ∃ w : OCr l O, galOCr O h r - r = ((l : O) ^ m) • w := by
  induction r using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun h => ⟨0, by simp⟩
  | tmul o a =>
    filter_upwards [GlobalTheory.AcrisGal.galC_sub_dvd_mem_nhds l a m] with h hh
    obtain ⟨c, hc⟩ := hh
    refine ⟨o ⊗ₜ c, ?_⟩
    have e1 : galOCr O h (o ⊗ₜ[ℤ_[l]] a) = o ⊗ₜ galC h a := rfl
    rw [e1, ← TensorProduct.tmul_sub, hc, TensorProduct.smul_tmul', smul_eq_mul]
    have e2 : ((l : Per.Acris l) ^ m * c) = ((l : ℤ_[l]) ^ m) • c := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [e2, ← TensorProduct.smul_tmul, Algebra.smul_def, map_pow, map_natCast]
  | add x y hx hy =>
    filter_upwards [hx, hy] with h ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    rw [map_add, smul_add, ← hu, ← hv]; abel

theorem twact_sub_smul_eventually : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G]
    (s : G →* GQ l), Continuous s → ∀ (T : LocLat G ℚ_[l] K O),
    (∀ t ∈ T.L.T, ∀ m : ℕ, ∀ᶠ g in nhds (1 : G), ∃ t' ∈ T.L.T, T.ρ g t - t = ((l : O) ^ m) • t') →
    ∀ (β : TW (OCr l O) T) (m : ℕ), ∀ᶠ g in nhds (1 : G), ∃ γ : TW (OCr l O) T,
      TWact (galOCr O (s g)) T g β - β = ((l : O) ^ m) • γ := by
  intro l _ O K _ _ _ _ _ _ G _ _ s hs T hT β m
  have hts : Tendsto s (nhds 1) (nhds 1) := by
    simpa [map_one] using hs.tendsto (1 : G)
  induction β using TensorProduct.induction_on with
  | zero => exact Filter.Eventually.of_forall fun g => ⟨0, by simp⟩
  | tmul r t =>
    filter_upwards [hts.eventually (galOCr_sub_smul_eventually r m), hT t.1 t.2 m] with g ⟨w, hw⟩ ⟨t', ht', htt⟩
    refine ⟨w ⊗ₜ T.actT g t + r ⊗ₜ ⟨t', ht'⟩, ?_⟩
    have e1 : TWact (galOCr O (s g)) T g (r ⊗ₜ[O] t) = galOCr O (s g) r ⊗ₜ T.actT g t := rfl
    have e2 : T.actT g t - t = ((l : O) ^ m) • (⟨t', ht'⟩ : ↥T.L.T) := Subtype.ext (by
      rw [Submodule.coe_sub, Submodule.coe_smul]; exact htt)
    have e3 : galOCr O (s g) r ⊗ₜ[O] T.actT g t - r ⊗ₜ[O] t
        = (galOCr O (s g) r - r) ⊗ₜ[O] T.actT g t + r ⊗ₜ[O] (T.actT g t - t) := by
      rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
    rw [e1, e3, hw, e2, smul_add, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  | add x y hx hy =>
    filter_upwards [hx, hy] with g ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    rw [map_add, smul_add, ← hu, ← hv]; abel

end GlobalTheory.OCrCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFamilyPotentiallyCrystallineFrobStable
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial
open Classical

noncomputable section

namespace GlobalTheory.PotTwist

theorem frob : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal)
    (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'),
    finrank ℚ_[l] ↥K.1 = 1 → ∃ F : ↥(GK K), (pc P h hN hF hS).IsFrob F := by
  intro l _ P K K' h hN hF hS hK
  have hbot : K.1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 hK
  obtain ⟨g, hg⟩ : ∃ g : GQ l, ∀ x : ↥(Loc.K0 K'), g x = (((P.PD K').σ x : ↥(Loc.K0 K')) : Om l) := by
    let τ : ↥(Loc.K0 K') →ₐ[ℚ_[l]] Om l := (Loc.K0 K').val.comp (P.PD K').σ
    exact ⟨AlgEquiv.ofBijective (τ.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _),
      fun x => τ.liftNormal_commutes (Om l) x⟩
  have hmem : g ∈ GK K := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hbot] at hx
    obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact g.commutes a
  refine ⟨⟨g, hmem⟩, fun c => ?_⟩
  change (P.PD K).actB _ _ = algebraMap _ _ ((P.PD K').σ c)
  rw [P.PD_actB]
  exact P.actQ_Kur g (IntermediateField.inclusion (inf_le_right : Loc.K0 K' ≤ MaximalUnramifiedExtension l) c)
    (IntermediateField.inclusion (inf_le_right : Loc.K0 K' ≤ MaximalUnramifiedExtension l) ((P.PD K').σ c)) (hg c)

theorem main : ∀ (D : D7), PcrisTensorL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 →
  ∀ (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig0 : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ)) (c : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ) (n : ℕ),
  c ∈ Sig0 → Sig0.card ≤ n →
  (∀ x ∈ Xs, Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))) →
  (∀ x ∈ Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) ∧
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) Sig0) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) →
  (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w))) {c} →
  PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n := by
  intro D hT i w hw hdeg r Xs K' h hN hF hS Sig0 c n hc hcard hcont hx hχ1 hχ2

  have hequiv : ∀ (g : Br.G D.nbr i w hw) (v : Br.LL D.nbr i w hw),
      (LinearEquiv.funUnique (Fin 1) (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)).symm
        (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1)) g v) =
      (D.nbr i w hw).rep ((chiGL i).comp (decS D.nd w)) g
        ((LinearEquiv.funUnique (Fin 1) (Br.LL D.nbr i w hw) (Br.LL D.nbr i w hw)).symm v) := by
    intro g v
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [WeaklyAdmissibleFiltrations.charRep, LocBridge.rep, Br.locChi, Br.chiG, chiGL, Br.ι, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply, mul_comm]
  obtain ⟨tr1, tr2⟩ := GlobalTheory.HTW.Rec.potCrysData_transport (pc (D.loc (D.nd.l i)) h hN hF hS) _ _ _ hequiv
  have htw : ∀ x : ↥Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) ∧
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
        (Sig0.image (fun a => a * c⁻¹)) := fun x =>
    GlobalTheory.TwistPotCrys.twist_potCrys D hT i w hw r x K' h hN hF hS Sig0 c (hcont x x.2) (hx x x.2).1 (hx x x.2).2 (tr1 hχ1) (tr2 _ hχ2)
  obtain ⟨Fr, hFr⟩ := frob (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' h hN hF hS hdeg
  have h1 : (1 : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ) ∈ Sig0.image (fun a => a * c⁻¹) :=
    Finset.mem_image.2 ⟨c, hc, mul_inv_cancel c⟩
  obtain ⟨Sig, hsub, h1', hst, hit⟩ := GlobalTheory.frobStable_inertial_subset (pc (D.loc (D.nd.l i)) h hN hF hS)
    (fun x : ↥Xs => matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) (Fr : Br.G D.nbr i w hw) _ h1 (fun x => (htw x).2)
  exact ⟨K', h, hN, hF, hS, Sig, Fr, hFr, hst, h1',
    le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le hcard), fun x => ⟨(htw x).1, hit x⟩⟩

end GlobalTheory.PotTwist

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoEALe
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink.RowA

theorem two_eA_le {D : D7} (L : SizeData₂ D) {CA C : ℝ} (hCA : 0 ≤ CA) (hC : 2 * (3 * CA + 1) ≤ C)
    {l : ℕ} (hl : 5 ≤ l) : 2 * (eA L CA l : ℝ) ≤ Formalism.MainNotions.TwistedPlaces.eP L C l := by
  have h1 : 1 ≤ Formalism.MainNotions.TwistedPlaces.hB L := Formalism.MainNotions.TwistedPlaces.one_le_hB L
  set h := Formalism.MainNotions.TwistedPlaces.hB L with hh
  have hl' : (5 : ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (0 : ℝ) < l := by linarith
  have hl1 : (1 : ℝ) < l := by linarith
  set a : ℝ := ((hN L : ℕ) : ℝ) with ha
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have haN : a ≤ h := Nat.floor_le (by linarith)
  have hlog1 : 0 ≤ Real.logb l (a + a + 1) := Real.logb_nonneg hl1 (by linarith)
  have hlh : 0 ≤ Real.logb l h := Real.logb_nonneg hl1 h1
  have hlog2 : Real.logb l (a + a + 1) ≤ 1 + Real.logb l h := by
    have hle : a + a + 1 ≤ l * h := by nlinarith
    calc Real.logb l (a + a + 1) ≤ Real.logb l (l * h) :=
          Real.logb_le_logb_of_le hl1 (by linarith) hle
      _ = 1 + Real.logb l h := by
          rw [Real.logb_mul hl0.ne' (by linarith), Real.logb_self_eq_one hl1]
  have hdiv : (a + a) / l ≤ 2 * (h / l) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by linarith) hl0.le
  have hhl : 0 ≤ h / l := div_nonneg (by linarith) hl0.le
  have hY : 1 ≤ 1 + h / l + Real.logb l h := by linarith
  have hin : 1 + (a + a) / l + (1 + Real.logb l (a + a + 1)) ≤ 3 * (1 + h / l + Real.logb l h) := by
    linarith
  have hnn : 0 ≤ CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) := by
    apply mul_nonneg hCA
    have : 0 ≤ (a + a) / l := div_nonneg (by linarith) hl0.le
    linarith
  have hceil : (eA L CA l : ℝ) < CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) + 1 := by
    unfold eA
    push_cast
    exact Nat.ceil_lt_add_one hnn
  have harg : CA * (1 + (a + a) / l + (1 + Real.logb l (a + a + 1))) ≤
      CA * (3 * (1 + h / l + Real.logb l h)) := mul_le_mul_of_nonneg_left hin hCA
  have hE : (eA L CA l : ℝ) ≤ (3 * CA + 1) * (1 + h / l + Real.logb l h) := by nlinarith
  unfold Formalism.MainNotions.TwistedPlaces.eP
  rw [← hh]
  nlinarith

theorem main : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.admA L (tabX L X) C := by
  intro D L P HW X R C hD hR i _htw hcond
  obtain ⟨h5, hsp, _, _⟩ := hcond
  obtain ⟨_, _, _, hCA, hC1, _, _, _, _, _, hCC⟩ := hR
  have hl0 : D.nd.l i ≠ 0 := by omega
  have hfin := FamilyRepresentationConstants.placesOver_finite D.host.E (D.nd.l i) hl0
  have he := two_eA_le L hCA hCC h5
  have heP : 0 ≤ Formalism.MainNotions.TwistedPlaces.eP L C (D.nd.l i) := Formalism.MainNotions.TwistedPlaces.eP_nonneg L (by linarith) _
  unfold TwistedPlaces.sumOver
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro lam _
  have hk : (0 : ℝ) ≤ 2 * (TwistedPlaces.nLam D lam : ℝ) * D.R.m + 1 := by positivity
  have hconst : (fun π => X.len0 i π lam) =
      fun _ => ((lenA i (X.dc i) (eA L R.CA (D.nd.l i)) lam : ℚ) : ℝ) := by
    funext π
    rw [hD.len0S i hsp π lam, hD.eS i hsp]
  show 2 * KillingConditions.supZ i (fun π => X.len0 i π lam) ≤ _
  rw [hconst]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenA
    split_ifs
    · push_cast
      have : (TwistedPlaces.nLam D lam : ℝ) = (locDeg D.host.E lam : ℝ) := rfl
      rw [← this]
      nlinarith
    · push_cast; nlinarith
  · nlinarith

end GlobalTheory.NLink.RowA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalCocycleRowsRelationNewPlace
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrimeRel

theorem one_add_pow_of_sq {B : Type} [CommRing B] {x : B} (hx : x * x = 0) (n : ℕ) : (1 + x) ^ n = 1 + (n : B) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    linear_combination (n : B) * hx

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} {i : X.Tw}

theorem tame_rel (hT : TameQuotient) (_hl : 0 < nu X i) {M : ℕ} {L : Subgroup (GE N)} {p : PlE D.host}
    {d : GE N →* Multiplicative (ZMod (X.l i ^ M))} {σ γ : GE N} (hM : nu X i + 2 ≤ M) (hp : NewPl i M L p d σ γ)
    {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] [TopologicalSpace W] [DiscreteTopology W]
    (ρ : Representation R (GE N) W) (a b : R) (h4 : ∀ m : W, (X.l i ^ (nu X i + 1)) • m = 0) (hb : b * b = 0)
    (hI : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), ∀ m, ρ τ m = m + (((Multiplicative.toAdd (d τ)).val : R) * b) • m)
    (hσ : ∀ m, ρ σ m = m + a • m) (z : Z1 ρ) : a • z.1 γ = b • z.1 σ := by
  have := X.lPrime i
  obtain ⟨h0, -, hn, -, hd, hσ', hγ, hdγ⟩ := hp
  have h8 : normV p % (2 * X.l i ^ (nu X i + 1)) = 1 :=
    KStar.Tree.mod_two_mul_pow_of_le (X.lPrime i).out (by omega) hn
  exact (GlobalTheory.T.tame_relation_cocycle_squareZero_inertia hT D.host.E N.Om (X.l i) (N.plOm.1 p) p (N.plOm.2 p)
    (fun h => h0 p (Or.inl rfl) (X.twistExcludedPlaces_contains_residueChar i h)) (nu X i + 1) h8 M d γ σ (by omega) hd hγ hdγ hσ' R W ρ a b h4 hb hI hσ z).1

theorem rel : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N) (p : PlE D.host) (d : GE N →* Multiplicative (ZMod (X.l i ^ M))) (σ γ : GE N), nu X i + 2 ≤ M → Small2 i s M L z → NewPl i M L p d σ γ → ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (κ : GE N →* Bˣ) (x y : B), Kills i B → AntiHom X.cc κ → x * x = 0 → (∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), ((κ τ : Bˣ) : B) * (1 + x) ^ (Multiplicative.toAdd (d τ)).val = 1) → ((κ σ : Bˣ) : B) * (1 + y) = 1 → ∀ (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) B) Z, Univ bkP i s κ Q Φ Z → ∀ j : Bool × Fin D.R.r, x • Z (two X σ j.1) j.2 - (y * (if j.1 then 1 else ((κ σ : Bˣ) : B))) • Z (two X γ j.1) j.2 ∈ what₂ Φ := by
  intro hT D N X bkP i s hl M L z₀ p d σ γ hM hL hp B _ _ κ x y hK hκ hx hI hσ Q a Φ Z hU j

  let Y := (Fin a → B) ⧸ what₂ Φ
  letI : TopologicalSpace Y := ⊥
  haveI : DiscreteTopology Y := ⟨rfl⟩
  let mk : (Fin a → B) →ₗ[B] Y := (what₂ Φ).mkQ
  have hmk : ∀ v ∈ what₂ Φ, mk v = 0 := fun v hv => (Submodule.Quotient.mk_eq_zero _).2 hv

  let x0 : Fin a → Y := fun j => mk (Pi.single j 1)
  have hrow : ∀ (r : ℕ) (A : Matrix (Fin r) (Fin a) B) (c : Fin r), ∑ j, A c j • x0 j = mk (A c) := by
    intro r A c
    simp only [x0, ← map_smul, ← map_sum]
    congr 1
    ext j
    simp [Pi.single_apply]
  have hx0 : matAct Φ x0 = 0 := by
    ext c
    change ∑ j, Φ c j • x0 j = 0
    rw [hrow]
    exact hmk _ (Submodule.subset_span ⟨c, rfl⟩)
  have hrect : ∀ g c, rect (Z g) x0 c = mk (Z g c) := fun g c => hrow _ _ _

  obtain ⟨z, hz, -⟩ := (hU Y).1 x0 hx0

  have h4 : ∀ m : Fin D.R.r → Y, (X.l i ^ (nu X i + 1)) • m = 0 := fun m => by
    have h1 := hK _ (GlobalTheory.Growth.sq_mem_idl (X := X) (i := i))
    rw [map_natCast] at h1
    rw [← Nat.cast_smul_eq_nsmul B]
    exact (congrArg (· • m) h1).trans (zero_smul _ _)
  have htr : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Bˣ) : B) • m := fun g hg =>
    (GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z₀ (by omega) hL B κ _ hK (isDual_dualRep i s) Y g hg).1
  have hdec : DecV N p ≤ L := hp.2.2.2.1
  have hIL : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p), τ ∈ L := fun τ hτ => hdec (Ine_le_Dec _ hτ)
  have hσL : σ ∈ L := hdec hp.2.2.2.2.2.1.1
  have hcL : ∀ g, g ∈ L → cConj X g ∈ L := fun g hg => (hL.1.2.2.1 g _ (cConj_apply X g)).1 hg

  have hIv : ∀ τ ∈ Ine (F := D.host.E) (N.plOm.1 p),
      ((κ τ : Bˣ) : B) * (1 + ((Multiplicative.toAdd (d τ)).val : B) * x) = 1 := fun τ hτ => by
    rw [← one_add_pow_of_sq hx]
    exact hI τ hτ

  have r1 := tame_rel hT.1 hl hM hp (repOn (Tgl i s) κ Y) (-(y * ((κ σ : Bˣ) : B))) (-x) h4 (by rw [neg_mul_neg, hx])
    (fun τ hτ m => by
      have h := hIv τ hτ
      have hκτ : ((κ τ : Bˣ) : B) = 1 + ((Multiplicative.toAdd (d τ)).val : B) * -x := by
        linear_combination (1 - ((Multiplicative.toAdd (d τ)).val : B) * x) * h +
          ((Multiplicative.toAdd (d τ)).val : B) * ((Multiplicative.toAdd (d τ)).val : B) * ((κ τ : Bˣ) : B) * hx
      rw [htr τ (hIL τ hτ), hκτ, add_smul, one_smul])
    (fun m => by
      have hκσ : ((κ σ : Bˣ) : B) = 1 + -(y * ((κ σ : Bˣ) : B)) := by linear_combination hσ
      rw [htr σ hσL]
      nth_rw 1 [hκσ]
      rw [add_smul, one_smul]) z

  have hcont : Continuous (cConj X) := GlobalTheory.ResConjTriv.continuous_cConj X
  let z' : Z1 ((repOn (Tgl i s) κ Y).comp (cConj X)) :=
    ⟨fun g => z.1 (cConj X g), z.2.1.comp hcont, fun g h => by
      change z.1 (cConj X (g * h)) = _
      rw [map_mul]
      exact z.2.2 _ _⟩
  have r2 := tame_rel hT.1 hl hM hp ((repOn (Tgl i s) κ Y).comp (cConj X)) y x h4 hx
    (fun τ hτ m => by
      change repOn (Tgl i s) κ Y (cConj X τ) m = _
      rw [htr _ (hcL τ (hIL τ hτ)), antiHom_cConj X hκ, Units.inv_eq_of_mul_eq_one_right (hIv τ hτ), add_smul, one_smul])
    (fun m => by
      change repOn (Tgl i s) κ Y (cConj X σ) m = _
      rw [htr _ (hcL σ hσL), antiHom_cConj X hκ, Units.inv_eq_of_mul_eq_one_right hσ, add_smul, one_smul]) z'

  obtain ⟨b, c⟩ := j
  have key : ∀ (u v : B) (g h : GE N), u • z.1 g = v • z.1 h → u • Z g c - v • Z h c ∈ what₂ Φ := by
    intro u v g h e
    have e' := congrFun e c
    simp only [Pi.smul_apply, hz, hrect] at e'
    rw [← Submodule.Quotient.mk_eq_zero (what₂ Φ)]
    change mk (u • Z g c - v • Z h c) = 0
    rw [map_sub, map_smul, map_smul, e', sub_self]
  cases b
  · simp only [two, Bool.false_eq_true, ↓reduceIte, mul_one]
    apply key
    have := r1
    rw [neg_smul, neg_smul, neg_inj] at this
    exact this.symm
  · simp only [two, ↓reduceIte, mul_one]
    apply key
    exact r2.symm

end GlobalTheory.NewPrimeRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusSeriesLinearIndependentOfFirstTer
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem Lam_indep_of_first_terms : ∀ (l : ℕ) [Fact l.Prime] (h d : ℕ) (r : ℝ) (y : Fin d → ℕ → Fl l), 2 ≤ h → 0 ≤ r → r < 1 → (∀ a k, ‖sh (y a k)‖ ≤ r) → (∀ n : Fin d → ℕ, ‖sh (∑ a, n a • y a 0)‖ ≤ r ^ l ^ h → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ j : ℕ, j < 2 → ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * abelian₂ h j (y a) = 0) → c = 0 := by
  intro l _ h d r y hh hr0 hr1 hy hdet c hc
  have h1 : 1 ≤ h := by omega
  refine GlobalTheory.T.indep_over_padic_of_indep_mod_prime l d (Fin 2) (fun a i => abelian₂ h i (y a)) (fun i => gam l h i r) ?_ ?_ c ?_
  · intro a i
    exact (GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h i r (y a) h1 hr1 (hy a)).2.2.1
  · intro n hn
    apply hdet n
    have hls := fun j => GlobalTheory.T.untiltFrobeniusLaurentSeries_natCombination_approx l h j d r (fun a => y a 0) n h1 hr0 hr1 (fun a => hy a 0)
    have hρ0 : 0 ≤ r ^ l ^ h := pow_nonneg hr0 _
    have hρ1 : r ^ l ^ h < 1 := pow_lt_one₀ hr0 hr1 (pow_pos (Fact.out : l.Prime).pos h).ne'
    refine GlobalTheory.T.norm_tiltUntilt_le_of_frobeniusSeries_size_le l h (r ^ l ^ h) (∑ a, n a • y a 0) hh hρ0 hρ1 (lt_of_le_of_lt (hls 0).1 hr1) ?_
    intro j hj
    have hG := GlobalTheory.T.untiltFrobeniusSeriesRadiusSize_laws l h j r h1 hr0 hr1
    rw [hG.2.2.2.2.1]
    have hnn : 0 ≤ ‖(l : ℂ_[l])‖ * gam l h j r := mul_nonneg (norm_nonneg _) hG.2.2.1
    have hA := (hls j).2
    have hB : ‖∑ a, (n a : ℂ_[l]) * (lam h j (y a 0) - abelian₂ h j (y a))‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hnn fun a _ => ?_
      rw [norm_mul]
      have hb := (GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds l h j r (y a) h1 hr1 (hy a)).2.1
      rw [norm_sub_rev] at hb
      calc ‖(n a : ℂ_[l])‖ * ‖lam h j (y a 0) - abelian₂ h j (y a)‖ ≤ 1 * (‖(l : ℂ_[l])‖ * gam l h j r) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ _) hb (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hC : ‖∑ a, (n a : ℂ_[l]) * abelian₂ h j (y a)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r := hn ⟨j, hj⟩
    have heq : lam h j (∑ a, n a • y a 0) = (lam h j (∑ a, n a • y a 0) - ∑ a, (n a : ℂ_[l]) * lam h j (y a 0)) + (∑ a, (n a : ℂ_[l]) * (lam h j (y a 0) - abelian₂ h j (y a)) + ∑ a, (n a : ℂ_[l]) * abelian₂ h j (y a)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]; ring
    rw [heq]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hB hC)
  · intro i
    exact hc i.1 i.2

end GlobalTheory.PSer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticesExistAllLayersOfBhattScholzeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachLatticesExistAllLayers_of_bhattScholze : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → WachEx AI := by
  first | exact @GlobalTheory.WachLattice.main | exact GlobalTheory.WachLattice.main | (intros; apply GlobalTheory.WachLattice.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachSaturationImageFreeAndSpansStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachSaturation_image_free_and_spans : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₀.ρ → IsCrys ((D.loc l).PD K) T₁.ρ → IsCrys ((D.loc l).PD K) T₂.ρ → IsSESLat (Qp := ℚ_[l]) ι π → Module.Flat (AA K LL) W.EE → FreeA W T₂ (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)) ∧ IsBaseChange W.EE (GlobalTheory.NL.Coker.satM l ((W.N T₁).map (mapA W π)) (W.N T₂)).subtype := by
  first | exact @GlobalTheory.NL.SatFree.satM_free_and_spans | exact GlobalTheory.NL.SatFree.satM_free_and_spans | (intros; apply GlobalTheory.NL.SatFree.satM_free_and_spans <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassDivisionClosedDiscBreuilKisinStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrass_division_closedDisc_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 → ∀ y : bk.DS ρ, ∃ (q : bk.DS ρ) (k : ℕ) (r : Polynomial (Wq l bk.a)), r.degree < bk.Ep.degree ∧ ((l : ℕ) : bk.DS ρ) ^ k * y = toDisc l (X : bk.S) ρ bk.E * q + toDisc l (X : bk.S) ρ (r : bk.S) := by
  first | exact @GlobalTheory.BSP.WDiv.weierstrass_div | exact GlobalTheory.BSP.WDiv.weierstrass_div | (intros; apply GlobalTheory.BSP.WDiv.weierstrass_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeierstrassPreparationWittOfTiltFiniteField
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory

theorem weierstrass_prep_not_dvd_l : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : (Wq l a)⟦X⟧), ¬ (l : (Wq l a)⟦X⟧) ∣ g →
    ∃ (P : Polynomial (Wq l a)) (U : (Wq l a)⟦X⟧), IsUnit U ∧ P.Monic ∧
      (∀ i < P.natDegree, (l : Wq l a) ∣ P.coeff i) ∧ g = U * (P : (Wq l a)⟦X⟧) := by
  intro l _ a _ g hg
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have hsurj : Function.Surjective (WittVector.constantCoeff (p := l) (R := Fq l a)) :=
    fun x => ⟨WittVector.teichmuller l x, by simp⟩
  have hm : IsLocalRing.maximalIdeal (Wq l a) = Ideal.span {(l : Wq l a)} := by
    rw [← WittVector.ker_constantCoeff]
    haveI := RingHom.ker_isMaximal_of_surjective _ hsurj
    exact (IsLocalRing.eq_maximalIdeal this).symm
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (Wq l a)) (Wq l a) := hm ▸ inferInstance
  have hg' : g.map (IsLocalRing.residue (Wq l a)) ≠ 0 := by
    intro h0
    apply hg
    apply dvd_of_map_eq_zero l a g
    ext n
    have h1 : IsLocalRing.residue (Wq l a) (coeff n g) = 0 := by
      simpa using congrArg (coeff n) h0
    rw [IsLocalRing.residue_eq_zero_iff, hm, ← WittVector.ker_constantCoeff, RingHom.mem_ker] at h1
    simpa using h1
  obtain ⟨f, h, H⟩ := g.exists_isWeierstrassFactorization hg'
  refine ⟨f, h, H.isUnit, H.isDistinguishedAt.monic, fun i hi => ?_, ?_⟩
  · have := H.isDistinguishedAt.mem hi
    rw [hm] at this
    exact Ideal.mem_span_singleton.1 this
  · rw [H.eq_mul, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRestrictionUnramifiedFrobeniusConjugatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRestriction_unramified_frobeniusConjugates : WeilRes := by
  first | exact @GlobalTheory.PMon.weilRes | exact GlobalTheory.PMon.weilRes | (intros; apply GlobalTheory.PMon.weilRes <;> assumption)
end

