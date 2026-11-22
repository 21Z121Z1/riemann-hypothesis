import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0089
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubMemOfMk
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0259
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0154
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0140
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0159
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0158
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0271
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0269
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MemBoundariesZeroIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0270
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementProperties
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.EpsFacts

variable {l : ℕ} [Fact l.Prime]

theorem geom_sum_eq_zero {R : Type*} [CommRing R] [IsDomain R] {z : R} {m : ℕ} (h : z ^ m = 1) (h1 : z ≠ 1) :
    ∑ i ∈ Finset.range m, z ^ i = 0 := by
  have e := mul_geom_sum z m
  rw [h, sub_self] at e
  exact (mul_eq_zero.1 e).resolve_left (sub_ne_zero.2 h1)

theorem pow_chain {M : Type*} [Monoid M] {m : ℕ} (e : ℕ → M) (hs : ∀ k, e (k + 1) ^ m = e k) (k j : ℕ) :
    e (k + j) ^ m ^ j = e k := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ m j, mul_comm, pow_mul, ← add_assoc, hs, ih]

theorem prim_chain {M : Type*} [CommMonoid M] (e : ℕ → M) (hs : ∀ k, e (k + 1) ^ l = e k) (h0 : e 0 = 1)
    (h1 : e 1 ≠ 1) (m : ℕ) : IsPrimitiveRoot (e m) (l ^ m) := by
  cases m with
  | zero => simpa [h0] using IsPrimitiveRoot.one
  | succ k =>
    have a : e (k + 1) ^ l ^ k = e 1 := by
      have := pow_chain e hs 1 k
      rwa [add_comm 1 k] at this
    have b : e (k + 1) ^ l ^ (k + 1) = 1 := by
      have := pow_chain e hs 0 (k + 1)
      rwa [zero_add, h0] at this
    have o : orderOf (e (k + 1)) = l ^ (k + 1) :=
      orderOf_eq_prime_pow (by rw [a]; exact h1) b
    exact o ▸ IsPrimitiveRoot.orderOf _

theorem coeff_not_isUnit {R : Type*} [CommRing R] [IsLocalRing R] (a : R) (ha : ¬ IsUnit (a - 1)) (i : ℕ) :
    ¬ IsUnit ((WittVector.teichmuller l a - 1 : WittVector l R).coeff i) := by
  have h1 : IsLocalRing.residue R a = 1 := by
    have : IsLocalRing.residue R (a - 1) = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).2 ((IsLocalRing.mem_maximalIdeal _).2 ha)
    rwa [map_sub, map_one, sub_eq_zero] at this
  have h2 : WittVector.map (IsLocalRing.residue R) (WittVector.teichmuller l a - 1 : WittVector l R) = 0 := by
    rw [map_sub, map_one, WittVector.map_teichmuller, h1, map_one, sub_self]
  have h3 : IsLocalRing.residue R ((WittVector.teichmuller l a - 1 : WittVector l R).coeff i) = 0 := by
    rw [← WittVector.map_coeff, h2, WittVector.zero_coeff]
  exact (IsLocalRing.mem_maximalIdeal _).1 ((IsLocalRing.residue_eq_zero_iff _).1 h3)

variable (l) in
theorem isLocalRing_oc : IsLocalRing (OC l) := ValuationRing.isLocalRing (OC l)

variable (l) in
theorem isLocalRing_ob : IsLocalRing (Ob l) :=
  haveI := isLocalRing_oc l
  GlobalTheory.preTilt_isLocalRing l (OC l)

variable (l) in
theorem pFlat_not_isUnit : ¬ IsUnit (pFlat l) := fun h => by
  have h1 : IsUnit (theta0 l (WittVector.teichmuller l (pFlat l))) := (h.map (WittVector.teichmuller l)).map (theta0 l)
  rw [WittVector.fontaineTheta_teichmuller, untilt_pFlat] at h1
  exact (inferInstance : Fact (¬ IsUnit (l : OC l))).out h1

theorem integral_prime_dvd_epsilon_zero_sub_one (ε : Eps l) : pFlat l ∣ ((ε.e 0 : Ob l) - 1) := by
  have h := ((RL.sharp_cong (base l)).2.1 (ε.e 0 : Ob l) 1).1 (by
    have h0 : (base l).sharp (ε.e 0 : Ob l) = 1 := ε.sharp_e (base l)
    rw [h0, map_one, sub_self]
    exact zero_mem _)
  exact Ideal.mem_span_singleton.1 h

theorem epsilon_one_sub_one_not_isUnit (ε : Eps l) : ¬ IsUnit ((ε.e 1 : Ob l) - 1) := fun h => by
  haveI : CharP (Ob l) l := inferInstance
  have h1 : IsUnit (((ε.e 1 : Ob l) - 1) ^ l) := h.pow l
  have e : (ε.e 1 : Ob l) ^ l = ε.e 0 := by
    have := congrArg Units.val (ε.succ 0)
    rwa [Units.val_pow_eq_pow_val] at this
  rw [sub_pow_char, e, one_pow] at h1
  exact pFlat_not_isUnit l (isUnit_of_dvd_unit (integral_prime_dvd_epsilon_zero_sub_one ε) h1)

theorem theta_e_succ (ε : Eps l) (k : ℕ) :
    theta0 l (WittVector.teichmuller l (ε.e (k + 1) : Ob l)) ^ l = theta0 l (WittVector.teichmuller l (ε.e k : Ob l)) := by
  rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ε.succ]

theorem qk_succ (ε : Eps l) (k : ℕ) : ε.qk (k + 1) ^ l = ε.qk k := by
  rw [Eps.qk, ← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ε.succ, Eps.qk]

theorem sum_mem_ker (ε : Eps l) :
    ∑ i ∈ Finset.range l, (WittVector.teichmuller l (ε.e 1 : Ob l)) ^ i ∈ RingHom.ker (theta0 l) := by
  rw [RingHom.mem_ker, map_sum]
  simp only [map_pow]
  exact geom_sum_eq_zero ((theta_e_succ ε 0).trans ε.one) ε.prim

theorem cris_sum_mem (ε : Eps l) (A : PAlg l) (n : ℕ) :
    A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1 := by
  have e : ∑ i ∈ Finset.range l, ε.qk 1 ^ i =
      algebraMap (Ainf l) (Acris l) (∑ i ∈ Finset.range l, (WittVector.teichmuller l (ε.e 1 : Ob l)) ^ i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, Eps.qk]
  have h := sum_mem_ker ε
  rw [ker_theta0] at h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  rw [e, cris_algebraMap, ← hc, map_mul, map_mul]
  change _ * A.toAcr n A.xi ∈ _
  rw [toAcr_xi]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨1, le_rfl, rfl⟩)

theorem mu_eq (ε : Eps l) : ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i := by
  rw [mul_geom_sum, qk_succ ε 0, Eps.μ]

theorem eps_facts : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l), D.InWm l ((WittVector.teichmuller l (ε.e 1 : Ob l)) - 1) ∧ (∀ k, ε.qk (k + 1) ^ l = ε.qk k) ∧ (∀ (A : PAlg l) (n : ℕ), A.cris n (∑ i ∈ Finset.range l, ε.qk 1 ^ i) ∈ A.Fil n 1) ∧ ε.μ = (ε.qk 1 - 1) * ∑ i ∈ Finset.range l, ε.qk 1 ^ i ∧ ∀ m, IsPrimitiveRoot (theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (l ^ m) := by
  intro l _ ε
  haveI := isLocalRing_ob l
  exact ⟨fun i => coeff_not_isUnit _ (epsilon_one_sub_one_not_isUnit ε) i, qk_succ ε, cris_sum_mem ε, mu_eq ε,
    prim_chain (fun m => theta0 l (WittVector.teichmuller l (ε.e m : Ob l))) (theta_e_succ ε) ε.one ε.prim⟩

end GlobalTheory.CompanionTheory.EpsFacts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGradedFormOnAffineChart
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech.Omega
open GlobalTheory.CompanionTheory.GrForm GlobalTheory.CompanionTheory.GrVB

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem evLift_mul_sub {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hP : ∀ T, P T → InU W T) (z x : Γ(X, W))
    (T : P.FullSubcategory) :
    (show T.obj.B from evLift hP z T) * lft W T.obj x - lft W T.obj (z * x) ∈ T.obj.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, mk_evLift, lft_spec _ (hP _ T.property), lft_spec _ (hP _ T.property), map_mul]

theorem rp_fAct {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hF : IsFil (sP P) (sFil P))
    (hP : ∀ T, P T → InU W T) {d r : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) (z : Γ(X, W)) (x : Idx r d → Γ(X, W)) (c : HU (GF q r) P r)
    (hc : Rp (W := W) P u x c) : Rp (W := W) P u (fun I => z * x I) (fAct hF hP r z c) := by
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(mulMor hF r (evLift hP z) (evLift_nat hP z)).pullC r f, ?_, rfl, ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · intro s
    let uu : Fin d → ∀ T : P.FullSubcategory, (sP P).A.obj T := fun i T => u i T.obj
    have hl : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'), uu i T' - ((sP P).A.map φ).hom (uu i T) ∈ (sP P).J.S T' :=
      fun i {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) (t i) _ _
        (hu i _ (hP _ T.property)) (hu i _ (hP _ T'.property))
    change Ideal.Quotient.mk _ (show (sP P).A.obj (s.obj (Fin.last r)) from evLift hP z (s.obj (Fin.last r))) *
      (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f s).1 = _
    rw [hfs s, ← map_mul, Ideal.Quotient.eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have hw := wz_mem hF uu hl I.1 s
    have := J_mul_sFil P r _ (evLift_mul_sub hP z (x I) (s.obj (Fin.last r))) hw
    have e := units_mul_relation_rearrange_commRing (S := (sP P).A.obj (s.obj (Fin.last r)))
      (evLift hP z (s.obj (Fin.last r))) (wz uu I.1 s) (lft W (s.obj (Fin.last r)).obj (x I))
      (lft W (s.obj (Fin.last r)).obj (z * x I))
    exact Eq.mpr (congrArg (fun v => v ∈ (sFil P ((r : ℤ) + 1)).S (s.obj (Fin.last r))) e) this

theorem basis : KH.LocGr → KH.PolyTf → ∀ {O : Type} [CommRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {W₀ : X.Opens} {d : ℕ}
    (c : Coord q W₀ d) (r : ℕ) (hr : r < s),
    ∃ ω : Idx r d → HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) (St (TF l s) {W₀}) r,
      ∀ (W : X.Opens) (hW : IsAffineOpen W) (hle : W ≤ W₀) (Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))))
        (hQ : Q = St (TF l s) {W}) (hQ₀ : Q ≤ St (TF l s) {W₀}) (hF : IsFil (sP Q) (sFil Q)) (hQW : ∀ T, Q T → InU W T)
        (h : HU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) Q r),
        ∃! f : Idx r d → Γ(X, W), h = ∑ k, GlobalTheory.CompanionTheory.GrCech.fAct hF hQW r (f k) ((resU (GlobalTheory.CompanionTheory.GrCech.grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) hQ₀).pull r (ω k)) := by
  classical
  intro hLoc hPoly O _ l s hb X q W₀ d c r hr
  have hL : StLoc := stLoc stFrame hLoc hPoly
  have hE : StExists := exists_of_cocycle stCocycle
  let u : Fin d → ∀ T : Thick (LL q), T.B := fun k T => lft W₀ T (c.t k)
  have hu : IsLift W₀ c.t u := fun k T h => lft_spec T h _
  choose ω hω using fun k : Idx r d => hE W₀ c.t u hu (SS q l s W₀) (ss_inU l s W₀) r (Pi.single k 1)
  refine ⟨ω, ?_⟩
  intro W hW hle Q hQ hQ₀ hF hQW h
  have hFree : Free W Q r u := free_at hL hb hle hW c hu hr hQ
  have hu' : IsLift W (fun i => rs hle (c.t i)) u := isLift_res hle hu fun _ => rfl
  have hrep : ∀ f : Idx r d → Γ(X, W), Rp (W := W) Q u f
      (∑ k, fAct hF hQW r (f k) ((resU (GF q r) hQ₀).pull r (ω k))) := by
    intro f
    have s1 := rp_sum hE stAdd hu' hQW Finset.univ
      (fun k I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(X, W₀)) I)) _
      (fun k _ => rp_fAct hF hQW hu' (f k) _ _
        (stRes W₀ W hle c.t u hu (SS q l s W₀) Q hQ₀ (ss_inU l s W₀) hQW r _ _ (hω k)))
    have e : (∑ k, fun I => f k * rs hle ((Pi.single k 1 : Idx r d → Γ(X, W₀)) I)) = f := by
      funext I
      rw [Finset.sum_apply, Finset.sum_eq_single I]
      · simp
      · intro b _ hb'
        simp [Pi.single_eq_of_ne (Ne.symm hb')]
      · simp
    rwa [e] at s1
  obtain ⟨x, hx⟩ := hFree.1 h
  refine ⟨x, rp_class hx (hrep x), fun y hy => ?_⟩
  have hy' : Rp (W := W) Q u y h := by
    rw [hy]
    exact hrep y
  exact rp_coef stAdd hu' hQW hFree hy' hx

end GlobalTheory.CompanionTheory.GrCech.Omega
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLubinTateCharacterUnitaryStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lubin_tate_character_unitary : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l), ∃ χ : ↥(GK K) →* (↥K.1)ˣ, IsLTChar K χ ∧
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) ∧ ∀ g, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.LTHodge.exists_lubinTateChar | exact GlobalTheory.CompanionTheory.LTHodge.exists_lubinTateChar | (intros; apply GlobalTheory.CompanionTheory.LTHodge.exists_lubinTateChar <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueHom
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfLift

variable {l : ℕ} [Fact l.Prime] {R S : Type} [CommRing R] [CommRing S]

def powHom (hS : (l : S) = 0) (n : ℕ) : S →+* S where
  toFun x := x ^ l ^ n
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq (Fact.out : l.Prime) x y n
    rw [hr, hS]; simp

theorem powHom_apply (hS : (l : S) = 0) (n : ℕ) (x : S) : powHom hS n x = x ^ l ^ n := rfl

def rootHom [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) : R ≃+* R :=
  RingEquiv.ofBijective (powHom hR n)
    (PerfectRing.bijective_frobenius : Function.Bijective fun x : R => x ^ l ^ n)

theorem rootHom_pow [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) (a : R) :
    ((rootHom hR n).symm a) ^ l ^ n = a :=
  (rootHom hR n).apply_symm_apply a

theorem rootHom_symm_pow [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) (b : R) :
    (rootHom hR n).symm (b ^ l ^ n) = b :=
  (rootHom hR n).symm_apply_apply b

def level [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (n : ℕ) : R →+* S ⧸ Ideal.span {π} ^ l ^ n :=
  (Ideal.quotientMap (Ideal.span {π} ^ l ^ n) (powHom hS n)
    (fun _ hx => Ideal.mem_comap.2 (Ideal.pow_mem_pow hx _))).comp
      (g.comp ((rootHom hR n).symm : R →+* R))

theorem level_spec [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (n : ℕ) (b : R) (x : S)
    (hx : Ideal.Quotient.mk _ x = g b) :
    level hR hS π g n (b ^ l ^ n) = Ideal.Quotient.mk _ (x ^ l ^ n) := by
  have h1 : ((rootHom hR n).symm : R →+* R) (b ^ l ^ n) = b := rootHom_symm_pow hR n b
  simp only [level, RingHom.comp_apply, h1, ← hx, Ideal.quotientMap_mk, powHom_apply]

theorem strictMono_pow : StrictMono fun n : ℕ => l ^ n :=
  strictMono_nat_of_lt_succ fun n => Nat.pow_lt_pow_right (Fact.out : l.Prime).one_lt (Nat.lt_succ_self n)

theorem level_compat [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (m : ℕ) :
    (Ideal.Quotient.factorPow (Ideal.span {π}) ((strictMono_pow (l := l)).monotone m.le_succ)).comp
      (level hR hS π g (m + 1)) = level hR hS π g m := by
  ext a
  obtain ⟨b, rfl⟩ : ∃ b : R, b ^ l ^ (m + 1) = a := ⟨_, rootHom_pow hR (m + 1) a⟩
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (g b)
  have hx' : Ideal.Quotient.mk (Ideal.span {π}) (x ^ l) = g (b ^ l) := by
    rw [map_pow, map_pow, hx]
  have e1 : b ^ l ^ (m + 1) = (b ^ l) ^ l ^ m := by rw [← pow_mul, pow_succ']
  have e2 : x ^ l ^ (m + 1) = (x ^ l) ^ l ^ m := by rw [← pow_mul, pow_succ']
  rw [RingHom.comp_apply, level_spec hR hS π g (m + 1) b x hx, e1, level_spec hR hS π g m _ _ hx', e2]
  rfl

theorem exists_lift [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    [IsAdicComplete (Ideal.span {π}) S] (g : R →+* S ⧸ Ideal.span {π}) :
    ∃ f : R →+* S, (Ideal.Quotient.mk _).comp f = g := by
  refine ⟨IsAdicComplete.StrictMono.liftRingHom (Ideal.span {π}) (strictMono_pow (l := l))
    (level hR hS π g) (fun {m} => level_compat hR hS π g m), ?_⟩
  ext a
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (g a)
  have h0 := IsAdicComplete.StrictMono.mk_liftRingHom (Ideal.span {π}) (strictMono_pow (l := l))
    (level hR hS π g) (fun {m} => level_compat hR hS π g m) (n := 0) a
  have h1 := level_spec hR hS π g 0 a x hx
  have ea : a ^ l ^ 0 = a := by simp
  have ex : x ^ l ^ 0 = x := by simp
  rw [ea, ex] at h1
  have h2 := Ideal.Quotient.eq.1 (h0.trans h1)
  have eI : Ideal.span {π} ^ l ^ 0 = Ideal.span {π} := by simp
  rw [eI] at h2
  rw [RingHom.comp_apply, ← hx]
  exact Ideal.Quotient.eq.2 h2

theorem lift_unique [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    [IsHausdorff (Ideal.span {π}) S] (f f' : R →+* S)
    (h : (Ideal.Quotient.mk (Ideal.span {π})).comp f = (Ideal.Quotient.mk _).comp f') : f = f' := by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' (Ideal.span {π}) (strictMono_pow (l := l))
  intro n a
  obtain ⟨b, rfl⟩ : ∃ b : R, b ^ l ^ n = a := ⟨_, rootHom_pow hR n a⟩
  have hb : f b - f' b ∈ Ideal.span {π} :=
    Ideal.Quotient.eq.1 (RingHom.congr_fun h b)
  refine Ideal.Quotient.eq.2 ?_
  have e : f (b ^ l ^ n) - f' (b ^ l ^ n) = (f b - f' b) ^ l ^ n := by
    have := map_sub (powHom hS n) (f b) (f' b)
    simpa only [powHom_apply, map_pow] using this.symm
  rw [e]
  exact Ideal.pow_mem_pow hb _

theorem existsUnique_hom {l : ℕ} [Fact l.Prime] (A A' : PAlg l)
    (g : A.A →+* A'.A ⧸ Ideal.span {A'.pi})
    (hg : g.comp A.s = (Ideal.Quotient.mk _).comp A'.s) :
    ∃! φ : A ⟶ A', (Ideal.Quotient.mk _).comp (PAlg.Hom.f φ) = g := by
  have : IsAdicComplete (Ideal.span {A'.pi}) A'.A := A'.compl
  have hOb : ((l : ℕ) : Ob l) = 0 := CharP.cast_eq_zero _ l
  obtain ⟨f, hf⟩ := exists_lift A.natCast_l A'.natCast_l A'.pi g
  have hcomm : f.comp A.s = A'.s := by
    refine lift_unique hOb A'.natCast_l A'.pi _ _ ?_
    rw [← RingHom.comp_assoc, hf, hg]
  refine ⟨⟨f, hcomm⟩, hf, fun φ hφ => ?_⟩
  apply PAlg.Hom.ext
  exact lift_unique A.natCast_l A'.natCast_l A'.pi _ _ (hφ.trans hf.symm)

end GlobalTheory.CompanionTheory.PerfLift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredModuleFiniteOfGraded
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LenDev

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem finite_mid [IsNoetherianRing R] {M₁ M₂ M₃ : Type 1} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (e : Function.Exact f g)
    [Module.Finite R M₁] [Module.Finite R M₃] : Module.Finite R M₂ := by
  have h₁ : Module.Finite R (LinearMap.ker g) := by
    rw [LinearMap.exact_iff.1 e]
    exact Module.Finite.range f
  have h₂ : Module.Finite R (M₂ ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

theorem H_subsingleton (F : C ⥤ ModuleCat.{0} R) (h : ∀ T, Subsingleton (F.obj T)) (n : ℕ) :
    Subsingleton (CH.H F n) := by
  have hX : Subsingleton ((CH.cx F).X n) := ⟨fun a b => funext fun s => (h _).elim _ _⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 x
  obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) n).1 y
  have e : a = b := hX.elim _ _
  subst e
  rfl

theorem sqM_rep (a b : IdF A) (T : C) (x : sqM a b T) :
    ∃ (y : A.obj T) (hy : y ∈ a.S T), x = sqMk a b y hy := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact ⟨y, hy, rfl⟩

theorem sq_self_subsingleton (a : IdF A) (T : C) : Subsingleton ((sq a a).obj T) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x', hx, rfl⟩ := sqM_rep a a T x
  obtain ⟨y', hy, rfl⟩ := sqM_rep a a T y
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ x' = Ideal.Quotient.mk _ y'
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hx, Ideal.Quotient.eq_zero_iff_mem.2 hy]

variable {a b c : IdF A}

theorem sq_inj (hba : ∀ T, b.S T ≤ a.S T) (T : C) :
    Function.Injective ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).τ T) := by
  intro x y h
  obtain ⟨x', hx, rfl⟩ := sqM_rep b c T x
  obtain ⟨y', hy, rfl⟩ := sqM_rep b c T y
  have h' := congrArg (fun z : sqM a c T => z.1) h
  exact Subtype.ext h'

theorem sq_exact (hba : ∀ T, b.S T ≤ a.S T) (hcb : ∀ T, c.S T ≤ b.S T) (T : C) :
    Function.Exact ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).τ T)
      ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).τ T) := by
  intro x
  obtain ⟨x', hx, rfl⟩ := sqM_rep a c T x
  constructor
  · intro h
    have h' : (Ideal.Quotient.mk (b.S T) x') = 0 := congrArg Subtype.val h
    exact ⟨sqMk b c x' (Ideal.Quotient.eq_zero_iff_mem.1 h'), rfl⟩
  · rintro ⟨y, hy⟩
    obtain ⟨y', hy', rfl⟩ := sqM_rep b c T y
    have e : (Ideal.Quotient.mk (c.S T) y') = Ideal.Quotient.mk (c.S T) x' := congrArg Subtype.val hy
    refine Subtype.ext ?_
    change Ideal.Quotient.mk (b.S T) x' = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have := Ideal.Quotient.eq.1 e
    have h2 := hcb T this
    have h3 := (b.S T).sub_mem hy' h2
    simpa using h3

theorem sq_surj (hcb : ∀ T, c.S T ≤ b.S T) (T : C) :
    Function.Surjective ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).τ T) := by
  intro x
  obtain ⟨x', hx, rfl⟩ := sqM_rep a b T x
  exact ⟨sqMk a c x' hx, rfl⟩

theorem sq_les (hba : ∀ T, b.S T ≤ a.S T) (hcb : ∀ T, c.S T ≤ b.S T) (n : ℕ) :
    Function.Exact ((sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).pull n)
      ((sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).pull n) := by
  obtain ⟨δ, -, -, e, -⟩ := CrystallineSemistableComparison.P.les
    (sqLe (a := b) (b := c) (a' := a) (b' := c) hba fun _ => le_rfl).hom
    (sqLe (a := a) (b := c) (a' := a) (b' := b) (fun _ => le_rfl) hcb).hom
    (fun n x y h => funext fun s => sq_inj hba _ (congrFun h s))
    (fun n y => ⟨fun hy => ⟨fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose,
        funext fun s => ((sq_exact hba hcb _ (y s)).1 (congrFun hy s)).choose_spec⟩, by
      rintro ⟨x, rfl⟩
      funext s
      exact (sq_exact hba hcb _ _).2 ⟨_, rfl⟩⟩)
    (fun n y => ⟨fun s => (sq_surj hcb _ (y s)).choose, funext fun s => (sq_surj hcb _ (y s)).choose_spec⟩)
  exact e n

theorem finite_dev [IsNoetherianRing R] (a : ℕ → IdF A) (hanti : ∀ k l, k ≤ l → ∀ T, (a l).S T ≤ (a k).S T) (s n : ℕ)
    (hgr : ∀ r, r < s → Module.Finite R (CH.H (sq (a r) (a (r + 1))) n)) :
    ∀ (d r : ℕ), r + d = s → Module.Finite R (CH.H (sq (a r) (a s)) n) := by
  intro d
  induction d with
  | zero =>
    intro r h
    obtain rfl : r = s := by omega
    have := H_subsingleton _ (sq_self_subsingleton (a r)) n
    exact Module.Finite.of_finite
  | succ d ih =>
    intro r h
    have := ih (r + 1) (by omega)
    have := hgr r (by omega)
    exact finite_mid _ _ (sq_les (hanti r (r + 1) (by omega)) (hanti (r + 1) s (by omega)) n)

theorem finite_H_sq : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (Fil : ℤ → IdF A),
    (∀ r r' : ℤ, r ≤ r' → ∀ T, (Fil r').S T ≤ (Fil r).S T) → ∀ s : ℕ,
    (∀ r : ℕ, r < s → ∀ j, Module.Finite R (CH.H (sq (Fil r) (Fil ((r : ℤ) + 1))) j)) →
    ∀ j, Module.Finite R (CH.H (sq (Fil 0) (Fil s)) j) := by
  intro R _ _ C _ A Fil hanti s hgr j
  have key := finite_dev (fun r : ℕ => Fil (r : ℤ))
    (fun k l h T => hanti _ _ (by exact_mod_cast h) T) s j
    (fun r hr => by
      have h := hgr r hr j
      rw [← Nat.cast_succ] at h
      exact h) s 0 (by omega)
  beta_reduce at key
  rw [Nat.cast_zero] at key
  exact key

end GlobalTheory.CompanionTheory.LenDev
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceNormOneCompactSupportStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_place_norm_one_compact_support : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (S : Finset (Pl F)), (∀ s ∈ S, IsCompact {x : Q d β (Kp s) | qn x = 1}) → IsCompact (SuppAt d β (S : Set (Pl F))) := by
  first | exact @GlobalTheory.CompanionTheory.PlaneSA.CptAdelic.isCompact_suppAt | exact GlobalTheory.CompanionTheory.PlaneSA.CptAdelic.isCompact_suppAt | (intros; apply GlobalTheory.CompanionTheory.PlaneSA.CptAdelic.isCompact_suppAt <;> assumption)
end

