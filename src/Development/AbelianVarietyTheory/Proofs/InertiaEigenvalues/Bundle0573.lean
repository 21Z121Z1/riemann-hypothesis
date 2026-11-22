import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0048
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import ReciprocityTheory.GaloisValuations.ArithOfA
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0006
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVOfNotJump
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfTiltCompatibleSequence
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.FrobRoots

open Ideal

section General

theorem root_step {A : Type} [CommRing A] (φ : A →+* A) (hφ : Function.Injective φ) (c : A) (hc : φ c = c) (q : ℕ)
    (ω : ℕ → A) (hω : ∀ n, φ (ω (n + 1)) = ω n) (h0 : φ (ω 0) = c * ω 0 + ω 0 ^ q) :
    ∀ n, c * ω (n + 1) + ω (n + 1) ^ q = ω n := by
  intro n
  induction n with
  | zero =>
    apply hφ
    rw [map_add, map_mul, map_pow, hc, hω, h0]
  | succ n ih =>
    apply hφ
    rw [map_add, map_mul, map_pow, hc, hω, hω, ih]

theorem pow_pow_eq {R : Type} [Monoid R] (q : ℕ) (r : ℕ → R) (h : ∀ n, r (n + 1) ^ q = r n) :
    ∀ n, r n ^ (q ^ n) = r 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, h, ih]

theorem coeff_pow_eq {O : Type} [CommRing O] {l : ℕ} [Fact l.Prime] [Fact (¬ IsUnit (l : O))]
    (z : PreTilt O l) (m : ℕ) : PreTilt.coeff m (z ^ (l ^ m)) = PreTilt.coeff 0 z := by
  rw [map_pow, GlobalTheory.LTTilt.coeff_eq_pow z 0 m, zero_add]

theorem sub_mem_of_three {O : Type} [CommRing O] (I : Ideal O) {u t y v : O} (h1 : u - t ∈ I) (h2 : t - y ∈ I)
    (h3 : y - v ∈ I) : u - v ∈ I := by
  have := I.add_mem (I.add_mem h1 h2) h3
  rwa [sub_add_sub_cancel, sub_add_sub_cancel] at this

theorem sub_mem_pow {O : Type} [CommRing O] {l : ℕ} [Fact l.Prime] (I : Ideal O) (hlI : (l : O) ∈ I) {P : O}
    (hP : P ∈ I) {f : ℕ} (hf : 0 < f) {u v : ℕ → O} (hu : ∀ n, P * u (n + 1) + u (n + 1) ^ l ^ f = u n)
    (hv : ∀ n, P * v (n + 1) + v (n + 1) ^ l ^ f = v n) (h1 : ∀ n, u n - v n ∈ I) :
    ∀ k n, u n - v n ∈ I ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro n; simpa using h1 n
  | succ k ih =>
    intro n
    have hq : u (n + 1) ^ l ^ f - v (n + 1) ^ l ^ f ∈ I ^ (k + 1 + 1) := by
      obtain ⟨g, hg⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
      rw [hg, show l ^ (g + 1) = l ^ g * l from pow_succ l g, pow_mul, pow_mul]
      exact GlobalTheory.LTTilt.pow_l_sub_mem I hlI (by omega) (GlobalTheory.LTTilt.pow_sub_mem _ (ih (n + 1)) _)
    have e : u n - v n = P * (u (n + 1) - v (n + 1)) + (u (n + 1) ^ l ^ f - v (n + 1) ^ l ^ f) := by
      rw [← hu n, ← hv n]; ring
    rw [e]
    refine Ideal.add_mem _ ?_ hq
    rw [pow_succ' I (k + 1)]
    exact Ideal.mul_mem_mul hP (ih (n + 1))

end General

section OC

open Formalism.BasicNotions

theorem eq_of_forall_mem_pow {l : ℕ} [Fact l.Prime] {P a b : OC l} (hP : ¬ IsUnit P)
    (h : ∀ k, a - b ∈ (Ideal.span {P}) ^ (k + 1)) : a = b := by
  have hP1 := GlobalTheory.LTTilt.norm_lt_one_of_not_isUnit P hP
  have hk : ∀ k, ‖((a - b : OC l) : ℂ_[l])‖ ≤ ‖(P : ℂ_[l])‖ ^ (k + 1) := by
    intro k
    have := h k
    rw [Ideal.span_singleton_pow, GlobalTheory.LTTilt.mem_span_iff_norm, SubmonoidClass.coe_pow, norm_pow] at this
    exact this
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hP1).comp (Filter.tendsto_add_atTop_nat 1)
  have h0 := ge_of_tendsto' hlim fun k => hk k
  have h2 : ((a - b : OC l) : ℂ_[l]) = 0 := norm_le_zero_iff.1 h0
  have h3 : a - b = 0 := Subtype.ext h2
  exact sub_eq_zero.1 h3

end OC

section Main

theorem sub_mem_of_root {l : ℕ} [Fact l.Prime] {P u a v : OC l} (hlP : ((l : ℕ) : OC l) ∈ span {P})
    {x y : OCb l} {m : ℕ} (hxy : y ^ (l ^ m) = x)
    (ha : PreTilt.coeff m x = Ideal.Quotient.mk (span {((l : ℕ) : OC l)}) a) (hav : a - v ∈ span {P})
    (hu : P ∣ u - y.untilt) : u - v ∈ span {P} := by
  refine sub_mem_of_three _ (Ideal.mem_span_singleton.2 hu) ?_ hav
  refine span_le.2 (Set.singleton_subset_iff.2 hlP) ?_
  rw [← hxy, coeff_pow_eq, ← PreTilt.mk_untilt_eq_coeff_zero] at ha
  exact Ideal.Quotient.eq.1 ha

theorem thetaK_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ (v : ℕ → OC l) (ω : ℕ → AK K),
    (∀ n, intToOC K π * v (n + 1) + v (n + 1) ^ l ^ fK K = v n) →
    GlobalTheory.LTTilt.IsTiltOf (fK K) (intToOC K π) (red K (ω 0)) v → (∀ n, frobq K (ω (n + 1)) = ω n) →
    frobq K (ω 0) = inO K π * ω 0 + ω 0 ^ l ^ fK K → ∀ n, thetaK K (ω n) = v n := by
  intro l _ K π hπ v ω hv hx hω h0
  have hF : ∀ n, inO K π * ω (n + 1) + ω (n + 1) ^ l ^ fK K = ω n :=
    root_step (frobq K).toRingHom (frobq_bijective K).1 (inO K π) (frobq_inO K π) _ ω hω h0
  have hu : ∀ n, intToOC K π * thetaK K (ω (n + 1)) + thetaK K (ω (n + 1)) ^ l ^ fK K = thetaK K (ω n) := by
    intro n
    have := congrArg (thetaK K) (hF n)
    rwa [map_add, map_mul, map_pow, thetaK_inO] at this
  have hr : ∀ n, red K (ω n) ^ (l ^ (fK K * n)) = red K (ω 0) := by
    intro n
    rw [pow_mul]
    exact pow_pow_eq (l ^ fK K) (fun n => red K (ω n))
      (fun n => (red_frobq (ω (n + 1))).symm.trans (congrArg (red K) (hω n))) n
  have hlP := GlobalTheory.LTTilt.natCast_mem_span_intToOC K hπ
  have h1 : ∀ n, thetaK K (ω n) - v n ∈ span {intToOC K π} := fun n =>
    (hx n).elim fun a ha => sub_mem_of_root hlP (hr n) ha.1 ha.2 (dvd_thetaK_sub hπ (ω n))
  exact fun n => eq_of_forall_mem_pow (GlobalTheory.LTTilt.not_isUnit_intToOC K hπ) fun k =>
    sub_mem_pow _ hlP (Ideal.mem_span_singleton_self _) (Nat.pos_of_ne_zero (NeZero.ne (fK K)))
      (u := fun n => thetaK K (ω n)) hu hv h1 k n

end Main

end GlobalTheory.FrobRoots
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferEqOfIsOpenKer
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.ArtinTransfer

open scoped Pointwise
open UpperTheory.V.Base (galOf galEmb galEmbTop range_galEmb galEmb_mem)
open Formalism.L2.Host (IsUnitAt IsUnifAt aboveF)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

section Group

variable {Γ B : Type} [Group Γ] [CommGroup B] {H : Subgroup Γ} [H.FiniteIndex] (φ : H →* B)

end Group

theorem card_le_of_pow_eq {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 1 < n) (h : ∀ x : F, x ^ n = x) :
    Nat.card F ≤ n := by
  haveI := Fintype.ofFinite F
  by_contra hlt
  refine FiniteField.X_pow_card_sub_X_ne_zero F hn
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ Function.injective_id (fun x => by simp [h]) ?_)
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq F hn, ← Nat.card_eq_fintype_card]
  omega

section Places

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]

omit [NumberField L] in
theorem int_mem (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω (x : L) ∈ A := by
  have h : IsIntegral A (algebraMap L Ω (x : L)) :=
    (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  rw [← hy]
  exact y.2

variable [Algebra K L] [IsScalarTower K L Ω]

theorem isPlaceOver_under {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 K)) := fun x => by
  rw [IsScalarTower.algebraMap_apply K L Ω]
  exact h (algebraMap (𝓞 K) (𝓞 L) x)

theorem normV_eq_pow [IsAlgClosure L Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)} (hA : IsPlaceOver A w)
    {σ : G K Ω} (hσ : IsFrob A (normV (w.under (𝓞 K))) σ) (hI : Ine (F := K) A ≤ galOf K L Ω) {m : ℕ}
    (hm : ∀ n, σ ^ n ∈ galOf K L Ω ↔ m ∣ n) : normV w = normV (w.under (𝓞 K)) ^ m := by
  set v := w.under (𝓞 K)
  have h2 : normV w = normV v ^ w.asIdeal.inertiaDeg (𝓞 K) := by
    simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
    exact (Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal).symm
  set f := w.asIdeal.inertiaDeg (𝓞 K)
  haveI := w.isMaximal
  haveI := v.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  have hq : 1 < normV v := Finite.one_lt_card
  have hw : 1 < normV w := Finite.one_lt_card
  have hf : 0 < f := Nat.pos_of_ne_zero fun h => by
    rw [h, pow_zero] at h2
    omega
  obtain ⟨s, hs⟩ := exists_isFrob hA
  have hs' : IsFrob A (normV v ^ f) (galEmb K L Ω s) := h2 ▸ ⟨hs.1, hs.2⟩
  have h3 : m ∣ f := by
    rw [← hm]
    have := hI (inv_mul_mem_Ine_of_isFrob hs' (GlobalTheory.FrobRestrict.isFrob_pow hσ f))
    exact ((galOf K L Ω).mul_mem_cancel_left ((galOf K L Ω).inv_mem (galEmb_mem K L Ω s))).1 this
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hf.ne' (zero_dvd_iff.1 h3)
  have h4 : normV w ≤ normV v ^ m := by
    refine card_le_of_pow_eq (Nat.one_lt_pow hm0 hq) fun x => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h5 := (GlobalTheory.FrobRestrict.isFrob_pow hσ m).2 _ ((A.valuation_le_one_iff _).2 (int_mem A x))
    rw [(hm m).2 dvd_rfl x] at h5
    rw [← map_pow, eq_comm, Ideal.Quotient.eq, ← hA]
    simpa using h5
  rw [h2] at h4 ⊢
  rw [le_antisymm ((pow_le_pow_iff_right₀ hq).1 h4) (Nat.le_of_dvd hf h3)]

end Places

section Ideles

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def compAt (v : HeightOneSpectrum (𝓞 K)) : AdeleRing (𝓞 K) K →* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def infPart : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl

variable {K} in
theorem loc_same (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  exact Pi.mulSingle_eq_same v _

variable {K} in
theorem loc_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v) (x : (v.adicCompletion K)ˣ) :
    (localIdele K v x).val.2 w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem ideleMap_apply (a : Ideles K) (w : HeightOneSpectrum (𝓞 L)) :
    (ideleMap K L a).val.2 w = finiteCompletionMap K L w (a.val.2 (w.under (𝓞 K))) := rfl

theorem ideleMap_mem_infConn {a : Ideles K} (ha : a ∈ infConn K) : ideleMap K L a ∈ infConn L := by
  obtain ⟨y, hy, rfl⟩ := ha
  have hc : Continuous (infiniteAdeleMap K L) :=
    continuous_fst.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp (Continuous.prodMk_left 0))
  refine ⟨Units.map (infiniteAdeleMap K L).toMonoidHom y, ?_,
    Units.ext (Prod.ext rfl (map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L)).symm)⟩
  have := (Continuous.units_map (infiniteAdeleMap K L).toMonoidHom hc).image_connectedComponent_subset 1 ⟨y, hy, rfl⟩
  rwa [map_one] at this

end Ideles

section Artin

variable {K L Ω B : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [Algebra L Ω]
  [CommGroup B]

variable [Algebra K L]

theorem descend [TopologicalSpace B] [T1Space B] {artK : Ideles K →* Gab K Ω} {artL : Ideles L →* Gab L Ω}
    (hK : IsGlobalArtin artK) (hL : IsGlobalArtin artL) (μ : Gab L Ω →* B) (hμ : Continuous μ) :
    ∃ ν : G K Ω →* B, Continuous ν ∧ ∀ (x : Ideles K) (σ : G K Ω), artK x = toAb K Ω σ →
      ν σ = μ (artL (ideleMap K L x)) := by
  let ψ : Ideles K →* B := μ.comp (artL.comp (ideleMap K L))
  have hψ : Continuous ψ := hμ.comp (hL.quot.continuous.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap K L))
  have hk : ∀ z ∈ (diagUnits L).range ⊔ infConn L, μ (artL z) = 1 := fun z hz => by
    have : z ∈ artL.ker := hL.ker ▸ Subgroup.le_topologicalClosure _ hz
    rw [MonoidHom.mem_ker.1 this, map_one]
  have hle : artK.ker ≤ ψ.ker := by
    rw [hK.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) ?_
    · rintro _ ⟨k, rfl⟩
      exact hk _ (Subgroup.mem_sup_left ⟨_, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele K L k).symm⟩)
    · intro y hy
      exact hk _ (Subgroup.mem_sup_right (ideleMap_mem_infConn K L hy))
    · exact isClosed_singleton.preimage hψ
  let f : Gab K Ω →* B := artK.liftOfSurjective hK.quot.surjective ⟨ψ, hle⟩
  have hf : ∀ x, f (artK x) = ψ x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply artK _ _ ⟨ψ, hle⟩ x
  have hc : Continuous f := by
    rw [hK.quot.isQuotientMap.continuous_iff]
    exact hψ.congr fun x => (hf x).symm
  refine ⟨f.comp (toAb K Ω), hc.comp continuous_quot_mk, fun x σ h => ?_⟩
  rw [MonoidHom.comp_apply, ← h, hf]
  rfl

omit [Algebra K L] in
variable (K L Ω) in

def overL : galOf K L Ω →* G L Ω where
  toFun s := AlgEquiv.ofRingEquiv (f := s.1.toRingEquiv) s.2
  map_one' := AlgEquiv.ext fun _ => rfl
  map_mul' _ _ := AlgEquiv.ext fun _ => rfl

variable [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]

end Artin

end GlobalTheory.ArtinTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.UnramifiedChar

theorem norm_eq_one_of_compact {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField k]
    (d : Γ →* k) (hd : Continuous d) (g : Γ) : ‖d g‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_norm.comp hd)).bddAbove
  have hle : ∀ g, ‖d g‖ ≤ 1 := by
    intro g
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have : ‖d (g ^ n)‖ ≤ C := hC ⟨g ^ n, rfl⟩
    rw [map_pow, norm_pow] at this
    linarith
  have h1 : ‖d g‖ * ‖d g⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, mul_inv_cancel, map_one, norm_one]
  have := hle g; have := hle g⁻¹; have := norm_nonneg (d g); have := norm_nonneg (d g⁻¹)
  nlinarith

variable {l : ℕ} [Fact l.Prime]

theorem val_mem_OL (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ)
    (hμ : Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) (g : ↥(GK K)) :
    ((μ g : (↥LL.1)ˣ) : ↥LL.1) ∈ OL LL := by
  haveI := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  let d : ↥(GK K) →* Om l :=
    ((LL.1.val : ↥LL.1 →ₐ[ℚ_[l]] Om l) : ↥LL.1 →* Om l).comp ((Units.coeHom ↥LL.1).comp μ)
  have hd : Continuous d := continuous_subtype_val.comp hμ
  exact (GlobalTheory.Per.Val.mem_OL_iff LL _).2 (norm_eq_one_of_compact d hd g).le

def unitLat (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ)
    (hμ : Continuous fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := ↥LL.1
  ρ := charRep μ
  cont := fun x => hμ.mul continuous_const
  L := GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.charLat Subtype.val_injective μ fun g => ⟨⟨_, val_mem_OL K LL μ hμ g⟩, rfl⟩

theorem isCrys_and_multV_eq : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (μ : ↥(GK K) →* (↥LL.1)ˣ), Continuous (fun g => ((μ g : (↥LL.1)ˣ) : ↥LL.1)) → (∀ g ∈ IK K, μ g = 1) → IsCrys (P.PD K) (charRep μ) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (b : ℤ), multV (P.PD K) (charRep μ) τ b = if b = 0 then 1 else 0 := by
  intro l _ P AI T K LL μ hμ hI
  obtain ⟨hc, hj⟩ := GlobalTheory.UnramifiedRep.isCrys_and_jump_eq_zero l P AI T K LL (unitLat K LL μ hμ)
    (fun g hg (x : ↥LL.1) => by
      change ((μ g : (↥LL.1)ˣ) : ↥LL.1) * x = x
      rw [hI g hg, Units.val_one, one_mul])
  change IsCrys (P.PD K) (charRep μ) at hc
  change ∀ τ a, IsJumpV (P.PD K) (charRep μ) τ a → a = 0 at hj
  refine ⟨hc, fun τ b => ?_⟩
  obtain ⟨hcomp, -⟩ := GlobalTheory.Per.Components.components_finrank l P AI T K LL ↥LL.1 (charRep μ)
  obtain ⟨hfd, -, hdr⟩ := hcomp τ
  haveI := hfd
  have hdim : finrank ↥LL.1 ↥(DdRE (P.PD K) (charRep μ) τ) = 1 := by
    rw [hdr (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T K LL ↥LL.1 (charRep μ) hc).1, finrank_self]
  have hnj : ∀ a, a ≠ 0 → multV (P.PD K) (charRep μ) τ a = 0 := fun a ha =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.rk_multV_of_not_jump (P.PD K) (charRep μ) τ a (fun h => ha (hj τ a h))
  split_ifs with hb
  · subst hb
    obtain ⟨lo, hlo⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_lo (P.PD K) (charRep μ) τ
    obtain ⟨hi, hhi⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fildR_hi (P.PD K) (charRep μ) τ
    have hsum := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_sum_multV (P.PD K) (charRep μ) τ (min lo 0) (max hi 1) (by omega)
    rw [hlo _ (min_le_left _ _), hhi _ (le_max_left _ _), finrank_bot, Nat.cast_zero, sub_zero, hdim,
      Finset.sum_eq_single (0 : ℤ) (fun a _ ha => hnj a ha)
        (fun h => absurd (Finset.mem_Ico.2 ⟨min_le_right _ _, by omega⟩) h)] at hsum
    exact_mod_cast hsum
  · exact hnj b hb

end GlobalTheory.UnramifiedChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZeroStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_isCrys_and_jump_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), (∀ g ∈ IK K, ∀ x, T.ρ g x = x) → IsCrys (P.PD K) T.ρ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T.ρ τ a → a = 0 := by
  first | exact @GlobalTheory.UnramifiedRep.isCrys_and_jump_eq_zero | exact GlobalTheory.UnramifiedRep.isCrys_and_jump_eq_zero | (intros; apply GlobalTheory.UnramifiedRep.isCrys_and_jump_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionCuspidalGreenDegreeEqOne
section
noncomputable section

namespace GlobalTheory.GLq

open Polynomial Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, -, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

variable {g : ℕ} [Fact g.Prime]

theorem res_zero_left {d : ℕ} (χ : Gn g d → ℂ) (h : Gn g 0) (y : Gn g d) :
    res 0 d χ h y = χ y := by
  unfold res
  have key : ∀ x : Gn g d, (InPar 0 (x : Mt g d) ∧ tl 0 (x : Mt g d) = (h : Mt g 0) ∧
      br 0 d (x : Mt g d) = (y : Mt g d)) ↔ x = y := by
    intro x
    constructor
    · rintro ⟨-, -, hb⟩
      apply Units.ext
      funext i j
      have := congrFun (congrFun hb i) j
      simpa [br, entN, i.isLt, j.isLt] using this
    · rintro rfl
      refine ⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩
      funext i j
      simp [br, entN, i.isLt, j.isLt]
  simp only [key, Nat.zero_mul, pow_zero, inv_one, one_mul]
  rw [Finset.sum_ite_eq' Finset.univ y]
  simp

theorem der_zero_one (ψ : AddChar (ZMod g) ℂ) {d : ℕ} (χ : Gn g d → ℂ) :
    der ψ 0 χ 1 = wh ψ χ := by
  unfold der
  have : res 0 (d - 0) χ 1 = χ := funext fun y => res_zero_left χ 1 y
  rw [this]

theorem der_cusp_eq_zero (ψ : AddChar (ZMod g) ℂ) {d m : ℕ} {χ : Gn g d → ℂ} (hχ : IsCusp χ)
    (h0 : 0 < m) (hm : m < d) (h : Gn g m) : der ψ m χ h = 0 := by
  unfold der wh tr
  have : res m (d - m) χ h = fun _ => 0 := funext fun y => res_cusp_eq_zero g d m χ hχ h0 hm h y
  rw [this]
  simp

theorem green_deg_ne_zero (d : ℕ) : ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hi1 : i ≠ 0 := by simp at hi; omega
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hlt : 1 < g ^ i := Nat.one_lt_pow hi1 hg
  intro h
  have h' : ((g ^ i : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; exact sub_eq_zero.mp h
  have := Nat.cast_injective h'
  omega

theorem wh_cusp_eq_one : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ)
    (χ : Gn g d → ℂ), IsCusp χ → χ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) → wh ψ χ = 1 := by
  intro g _ ψ hψ d χ hχ hdeg
  have hd : 0 < d := hχ.1
  have hform := GlobalTheory.T.classFunction_degree_eq_sum_derivatives g ψ hψ d χ hd (isClass_of_isIrr hχ.2.1)
  rw [Finset.sum_eq_single 0] at hform
  · rw [der_zero_one, zero_add, hdeg] at hform
    have hne := green_deg_ne_zero (g := g) d
    have : (wh ψ χ - 1) * ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) = 0 := by
      rw [sub_mul, ← hform]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hne)
  · intro m hm hm0
    rw [der_cusp_eq_zero ψ hχ (Nat.pos_of_ne_zero hm0) (Finset.mem_range.mp hm), zero_mul]
  · intro h; exact absurd (Finset.mem_range.mpr hd) h

end GlobalTheory.GLq
end
end

