import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0078
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PadicIntHomUnique
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0083
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OverOnePrimeOfCardLeOne
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.SharpRestriction.InertJacobiLevels.HostFam

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusEigenFilEqQlMulTPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.FixR

theorem step_abs {R A K : Type} [CommRing R] [CommRing A] [IsDomain A] [Field K]
    (i : R →+* A) (f : R →+* R) (φ : A →+* A) (Θ : A →+* K) (p : A) (hp : Θ p ≠ 0)
    (hφp : φ p = p) (hf : ∀ a, φ (i a) = i (f a))
    (μ : R) (hμ : ∀ n, Θ (i (f^[n] μ)) = 0)
    (hI : ∀ a : R, (∀ n, Θ (i (f^[n] a)) = 0) → μ ∣ a)
    (w : A) (m : ℕ) (hw : p * w = i μ ^ (m + 1))
    (himg : ∀ y, ∃ a z, φ y = i a + w * z)
    (t u : A) (hu : IsUnit u) (ht : t = i μ * u) (ht0 : t ≠ 0) (hφt : φ t = p * t)
    (r : ℕ) (x : A) (hx : φ x = p ^ (r + 1) * x) (hx0 : Θ x = 0) :
    ∃ x', p ^ (r + 2) * x = t * x' ∧ φ x' = p ^ r * x' := by
  have hit : ∀ n a, φ^[n] (i a) = i (f^[n] a) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro a; rw [Function.iterate_succ_apply, hf, ih, Function.iterate_succ_apply]
  have hpn : ∀ n, (φ ^ n) p = p := by
    intro n
    rw [RingHom.coe_pow]
    exact Function.iterate_fixed hφp n
  have hit' : ∀ n a, (φ ^ n) (i a) = i (f^[n] a) := by
    intro n a
    rw [RingHom.coe_pow]; exact hit n a
  have hxn : ∀ n, Θ ((φ ^ n) x) = 0 := by
    intro n
    induction n with
    | zero => simpa using hx0
    | succ n ih =>
      rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, hx]
      simp only [map_mul, ih, mul_zero]
  have hwn : ∀ n, Θ ((φ ^ n) w) = 0 := by
    intro n
    have := congrArg (fun y => Θ ((φ ^ n) y)) hw
    simp only [map_mul, map_pow, hpn, hit', hμ] at this
    simpa [hp] using this
  obtain ⟨a, z, haz⟩ := himg x
  obtain ⟨b, hb⟩ : μ ∣ a := by
    apply hI
    intro n
    have := congrArg (fun y => Θ ((φ ^ n) y)) (hx.symm.trans haz)
    simpa only [map_mul, map_add, hxn, hwn, hit', mul_zero, zero_mul, add_zero, eq_comm] using this
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hp0 : p ≠ 0 := fun h => hp (by rw [h, map_zero])
  have h1 : p ^ (r + 2) * x = t * (v * (p * i b + i μ ^ m * z)) := by
    have e := hx.symm.trans haz
    rw [hb, map_mul] at e
    rw [ht]
    linear_combination p * e + z * hw - (i μ * (p * i b + i μ ^ m * z)) * hv
  refine ⟨_, h1, ?_⟩
  set x' := v * (p * i b + i μ ^ m * z)
  have h2 := congrArg φ h1
  rw [map_mul, map_mul, map_pow, hφp, hx, hφt] at h2
  apply mul_left_cancel₀ (mul_ne_zero hp0 ht0)
  linear_combination p ^ (r + 1) * h1 - h2

variable {l : ℕ} [Fact l.Prime]

theorem alg_eq (a : Per.Ainf l) : algebraMap (Per.Ainf l) (Per.Acris l) a =
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

theorem phi_nat (n : ℕ) : phiA l (n : Per.Acris l) = n := map_natCast _ _

theorem phi_alg (a : Per.Ainf l) : phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem j_alg {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (a : Per.Ainf l) :
    j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [alg_eq, hj.on0]
  rfl

theorem theta_phi_mu (e : Per.Fl l) (he : e.untilt = 1) (n : ℕ) :
    Per.θ l ((Per.φA l)^[n] (mu e)) = 0 := by
  induction n generalizing e with
  | zero => simp [mu, he]
  | succ n ih =>
    have h : Per.φA l (mu e) = mu (e ^ l) := by
      simp only [mu, map_sub, map_one, GlobalTheory.RingIface.phiA_teich]
    rw [Function.iterate_succ_apply, h]
    exact ih _ (by rw [map_pow, he, one_pow])

theorem exists_w (e : Per.Fl l) (he : e.untilt = 1) : ∃ w : Per.Acris l,
    (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) := by
  obtain ⟨w, hw, -⟩ := GlobalTheory.T.exists_teichmullerTiltMinusOne_pow_div_envelope l e he
  have h : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  refine ⟨algebraMap (Per.Acris0 l) (Per.Acris l) w, ?_⟩
  rw [alg_eq, ← map_pow, ← h, map_mul, map_natCast]

theorem fil_div (C : Core l) (r : ℕ) (y : Per.BdRp l) (h : C.j C.t * y ∈ Per.FilP l (r + 1)) :
    y ∈ Per.FilP l r := by
  obtain ⟨hF, hreg, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε (GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C)
  obtain ⟨-, h1, h2, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  obtain ⟨-, hk, hun, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  rw [hF] at h h1 h2 ⊢
  obtain ⟨v, hv⟩ := h1
  have hvu : IsUnit v := by
    apply hun
    intro h0
    obtain ⟨c, hc⟩ := (hF _ _).1 ((hk v).1 h0)
    exact h2 ⟨c, by rw [hv, hc]; ring⟩
  obtain ⟨c, hc⟩ := h
  rw [← hvu.dvd_mul_left]
  refine ⟨c, sub_eq_zero.1 (hreg _ ?_)⟩
  rw [hv] at hc
  linear_combination hc

end GlobalTheory.MemLoc.FixR

namespace GlobalTheory.MemLoc
open FixR

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem fix_pow (l : ℕ) [Fact l.Prime] (C : Core l) (r : ℕ) (x : Per.Acris l)
    (hx : phiA l x = (l : Per.Acris l) ^ r * x) (hF : C.j x ∈ Per.FilP l r) :
    ∃ (z : ℤ_[l]) (k : ℕ), (l : Per.Acris l) ^ k * x =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z) * C.t ^ r := by
  induction r generalizing x with
  | zero =>
    obtain ⟨z, hz⟩ := GlobalTheory.T.acris_frobenius_fixed_eq_padicInt l x (by simpa using hx)
    exact ⟨z, 0, by simpa using hz⟩
  | succ r ih =>
    have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
    haveI := (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).1
    haveI : IsDomain (Per.Acris l) := (GlobalTheory.T.acrisToBdRPlus_injective l C.j C.j_cris).isDomain C.j
    obtain ⟨hFil, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he
    obtain ⟨-, hk, -, hth, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
    obtain ⟨w, hw⟩ := exists_w C.ε he.1
    obtain ⟨t, u, htl, hu, htu⟩ := GlobalTheory.T.exists_log_teichmuller_acris_eq_mu_mul_unit l C.ε he.1
    have htt : C.t = t := (GlobalTheory.T.acris_logTeichmuller_unique_galois_frobenius_bdR l C.ε t he.1 htl).1 _ C.t_log
    have hΘ : ∀ a, ((Per.θD l).comp C.j) (algebraMap (Per.Ainf l) (Per.Acris l) a) =
        (Per.θ l a : ℂ_[l]) := fun a => by
      rw [RingHom.comp_apply, j_alg C.j_cris, hth]
    have hl2 : l - 1 = (l - 2) + 1 := by
      have := (Fact.out : l.Prime).two_le
      omega
    obtain ⟨x', h1, h2⟩ := step_abs (algebraMap (Per.Ainf l) (Per.Acris l)) (Per.φA l) (phiA l)
      ((Per.θD l).comp C.j) (l : Per.Acris l) (by rw [map_natCast]; exact GlobalTheory.RingBasics.p_ne_zero)
      (phi_nat l) (phi_alg (l := l)) (mu C.ε)
      (fun n => by rw [hΘ, theta_phi_mu _ he.1]; rfl)
      (fun a ha => GlobalTheory.T.teichmullerTiltMinusOne_dvd_of_theta_frobenius_zero l C.ε he a fun n => Subtype.ext ((hΘ _).symm.trans (ha n)))
      w (l - 2) (hl2 ▸ hw) (GlobalTheory.T.frobenius_acris_decomposition_mu_power l C.ε he w hw) C.t u hu (htt.trans htu)
      (fun h => (GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C).2.2.1 (by rw [h, map_zero]; exact zero_mem _))
      (GlobalTheory.T.acrisFrobenius_fontaine_t_eq_mul l C) r x hx
      ((hk _).2 ((hFil _ _).2 ((pow_dvd_pow _ (by omega)).trans ((hFil _ _).1 hF))))
    have h3 : C.j x' ∈ Per.FilP l r := by
      apply fil_div C
      rw [← map_mul, ← h1, map_mul]
      exact Ideal.mul_mem_left _ _ hF
    obtain ⟨z, k, hz⟩ := ih x' h2 h3
    exact ⟨z, k + (r + 2), by linear_combination (l : Per.Acris l) ^ k * h1 + C.t * hz⟩

end GlobalTheory.MemLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExt
section
namespace GlobalTheory.MemLoc.InvDR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

section Abstract
variable {R F G : Type} [CommRing R] [IsDomain R] [Field F]

theorem inv_ker_eq_zero (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c : G → R) (t : R) (ht : t ≠ 0)
    (hker : ∀ y, θ y = 0 → t ∣ y) (hsep : ∀ y, (∀ n : ℕ, t ^ n ∣ y) → y = 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (z : R) (hz : θ z = 0) (hinv : ∀ g, σ g z = z) : z = 0 := by
  have key : ∀ m : ℕ, t ^ (m + 1) ∣ z := by
    intro m
    induction m with
    | zero => simpa using hker z hz
    | succ m ih =>
      obtain ⟨w, hw⟩ := ih
      have h1 : ∀ g, σ g w * c g ^ (m + 1) = w := by
        intro g
        have h := hinv g
        rw [hw, map_mul, map_pow, hσt] at h
        apply mul_left_cancel₀ (pow_ne_zero (m + 1) ht)
        rw [← h]
        ring
      have h2 : θ w = 0 := by
        refine tate ((m + 1 : ℕ) : ℤ) _ (by omega) fun g => ?_
        rw [zpow_natCast, ← hθ, ← map_pow, ← map_mul, h1]
      obtain ⟨v, hv⟩ := hker w h2
      exact ⟨v, by rw [hw, hv]; ring⟩
  exact hsep z fun n => (pow_dvd_pow t (Nat.le_succ n)).trans (key n)

theorem eigen_eq (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c : G → R) (t : R) (ht : t ≠ 0)
    (hker : ∀ y, θ y = 0 → t ∣ y) (hc : ∀ g, θ (c g) ≠ 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (n : ℕ) : ∀ y : R, (∀ g, σ g y = c g ^ n * y) → ∃ w, y = t ^ n * w ∧ ∀ g, σ g w = w := by
  induction n with
  | zero => intro y hy; exact ⟨y, by simp, fun g => by simpa using hy g⟩
  | succ n ih =>
    intro y hy
    have h2 : θ y = 0 := by
      refine tate (-((n + 1 : ℕ) : ℤ)) _ (by omega) fun g => ?_
      rw [zpow_neg, zpow_natCast, ← hθ, hy, map_mul, map_pow]
      have := pow_ne_zero (n + 1) (hc g)
      field_simp
    obtain ⟨v, hv⟩ := hker y h2
    obtain ⟨w, hw, hw'⟩ := ih v fun g => by
      have h := hy g
      rw [hv, map_mul, hσt] at h
      have hc0 : c g ≠ 0 := fun h0 => hc g (by rw [h0, map_zero])
      apply mul_left_cancel₀ (mul_ne_zero hc0 ht)
      rw [h]
      ring
    exact ⟨w, by rw [hv, hw]; ring, hw'⟩

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem j_alg (C : Core l) (a : Per.Ainf l) :
    C.j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [GlobalTheory.RingIface.tower, C.j_cris.on0, aDp, RingHom.comp_apply, SubalgebraClass.coe_algebraMap]

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem invariants_BdR (l : ℕ) [Fact l.Prime] (C : Core l) (K : FinExt l) (b : Per.BdR l)
    (hb : ∀ g ∈ GK K, Per.σD g b = b) :
    ∃ y ∈ K.1, algebraMap (Per.BdRp l) (Per.BdR l) (C.o y) = b := by
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨hdom, hinj, -, hfrac⟩ := GlobalTheory.T.bdRPlus_isDomain_bdR_isField l
  obtain ⟨hfil, hreg, hcompl, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, hθ⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  obtain ⟨-, ht1, ht2, -⟩ := GlobalTheory.T.fontaine_t_isUnit_bcris_and_uniformizer_bdRPlus l C
  obtain ⟨-, -, hoσ⟩ := GlobalTheory.T.bdRPlus_simple_roots_section_unique_equivariant l C.o C.o_sec
  obtain ⟨-, hjσ, -⟩ := GlobalTheory.T.canonicalAcrisToBdRPlus_unique_equivariant_approx l C.j C.j_cris
  have hσD := (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1
  have hact := GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic l C
  have htate := GlobalTheory.T.eq_zero_of_tateTwist_invariant_finiteExtension l C K
  have hast := GlobalTheory.T.cLTate_invariants_finiteExtension_mem l K
  generalize hx : aDp l (xi C.ε) = x at *
  obtain ⟨n, y0, hy0⟩ := hfrac C.ε he b
  rw [hx] at hy0
  generalize htt : C.j C.t = t at *
  obtain ⟨u, hu⟩ := (hfil 1 t).1 ht1
  rw [pow_one] at hu
  have huu : IsUnit u := by
    refine hunit u fun h0 => ht2 ?_
    obtain ⟨v, hv⟩ := (hfil 1 u).1 ((hker u).1 h0)
    exact (hfil 2 t).2 ⟨v, by rw [hu, hv]; ring⟩
  have ht0 : t ≠ 0 := fun h0 => ht2 (h0 ▸ zero_mem _)
  have htx : t ∣ x := by rw [hu]; exact huu.mul_right_dvd.2 dvd_rfl
  have hxt : x ∣ t := ⟨u, hu⟩
  let c : ↥(GK K) → Per.BdRp l := fun g => C.o (algebraMap ℚ_[l] (Om l) ((C.χ g.1 : ℤ_[l]) : ℚ_[l]))
  have hθc : ∀ g, Per.θD l (c g) = algebraMap ℚ_[l] ℂ_[l] ((C.χ g.1 : ℤ_[l]) : ℚ_[l]) := fun g =>
    (C.o_sec.th _).trans rfl
  have hc : ∀ g, Per.θD l (c g) ≠ 0 := fun g => by
    rw [hθc, map_ne_zero]
    exact fun h => (C.χ g.1).ne_zero (PadicInt.coe_eq_zero.1 h)
  have hσt : ∀ g : ↥(GK K), Per.σDp g.1 t = c g * t := fun g => by
    rw [← htt, ← hjσ, hact, map_mul, j_alg, ← C.o_sec.z]
  have hker' : ∀ y, Per.θD l y = 0 → t ∣ y := fun y hy =>
    htx.trans (by simpa using (hfil 1 y).1 ((hker y).1 hy))
  have hsep : ∀ y : Per.BdRp l, (∀ n : ℕ, t ^ n ∣ y) → y = 0 := fun y hy => by
    refine hcompl.toIsHausdorff.haus y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (pow_dvd_pow_of_dvd hxt n).trans (hy n)
  have tate : ∀ (i : ℤ) (x : ℂ_[l]), i ≠ 0 →
      (∀ g : ↥(GK K), Per.σC g.1 x * Per.θD l (c g) ^ i = x) → x = 0 := fun i x hi h =>
    htate i x hi fun g hg => by simpa only [hθc] using h ⟨g, hg⟩
  have hy : b * algebraMap (Per.BdRp l) (Per.BdR l) t ^ n =
      algebraMap (Per.BdRp l) (Per.BdR l) (y0 * u ^ n) := by
    rw [hu, map_mul, map_mul, map_pow, ← hy0]
    ring
  generalize y0 * u ^ n = y at hy
  have hyσ : ∀ g : ↥(GK K), Per.σDp g.1 y = c g ^ n * y := fun g => by
    apply hinj
    rw [← hσD, ← hy, map_mul, map_pow, hσD, hσt, hb g.1 g.2, map_mul, map_mul, map_pow, ← hy]
    ring
  obtain ⟨w, hw, hw'⟩ := eigen_eq (Per.θD l) (fun g : ↥(GK K) => Per.σDp g.1) (fun g => Per.σC g.1) c t ht0
    hker' hc (fun g y => hθ g.1 y) hσt tate n y hyσ
  obtain ⟨k, hk, hkθ⟩ := hast (Per.θD l w) fun g hg => by rw [← hθ, hw' ⟨g, hg⟩]
  have hz : w - C.o k = 0 := by
    refine inv_ker_eq_zero (Per.θD l) (fun g : ↥(GK K) => Per.σDp g.1) (fun g => Per.σC g.1) c t ht0
      hker' hsep (fun g y => hθ g.1 y) hσt tate _ ?_ fun g => ?_
    · rw [map_sub, C.o_sec.th, hkθ, sub_self]
    · have hg : g.1 k = k := g.2 ⟨k, hk⟩
      rw [map_sub, hw' g, hoσ, hg]
  refine ⟨k, hk, ?_⟩
  rw [← sub_eq_zero.1 hz]
  haveI : IsDomain (Per.BdR l) := (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.2.1.isDomain
  have ht' : algebraMap (Per.BdRp l) (Per.BdR l) t ^ n ≠ 0 :=
    pow_ne_zero n ((map_ne_zero_iff _ hinj).2 ht0)
  apply mul_right_cancel₀ ht'
  rw [hy, hw, map_mul, map_pow, mul_comm]

end GlobalTheory.MemLoc.InvDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspidalLabelPolynomialUniqueAllPrimesStatement
section
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_label_polynomial_unique_all_primes : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (d : ℕ) (P P' : (ZMod g)[X]) (χ : GlobalTheory.GLq.Gn g d → ℂ), GlobalTheory.GLq.IsCuspOf L P χ → GlobalTheory.GLq.IsCuspOf L P' χ → P = P' := by
  first | exact @GlobalTheory.GLq.isCuspOf_label_unique_allPrimes | exact GlobalTheory.GLq.isCuspOf_label_unique_allPrimes | (intros; apply GlobalTheory.GLq.isCuspOf_label_unique_allPrimes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConductorAdicCompletionEssFiniteTypeStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conductor_adicCompletion_essFiniteType : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [CharZero A] [Algebra.EssFiniteType ℤ A], ∃ x : A, x ≠ 0 ∧ ∀ c : FractionRing (AdicCompletion (maximalIdeal A) A), IsIntegral (AdicCompletion (maximalIdeal A) A) c → ∃ s : AdicCompletion (maximalIdeal A) A, algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) s = algebraMap _ (FractionRing (AdicCompletion (maximalIdeal A) A)) (algebraMap A (AdicCompletion (maximalIdeal A) A) x) * c := by
  first | exact @GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType | exact GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType | (intros; apply GlobalTheory.exists_conductor_adicCompletion_of_essFiniteType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCrisP
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.CrisMap

variable (l : ℕ) [Fact l.Prime]

noncomputable def gA (n : ℕ) : Per.Ainf l →+* Per.AinfP l ⧸ Per.kerP l ^ n :=
  (Ideal.Quotient.mk _).comp (algebraMap (Per.Ainf l) (Per.AinfP l))

noncomputable def fD (n : ℕ) : Per.Acris0 l →+* Per.AinfP l ⧸ Per.kerP l ^ n :=
  (Ideal.Quotient.mk _).comp (Per.Acris0 l).val.toRingHom

theorem unit_l (n : ℕ) : IsUnit ((l : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) := by
  have h : IsUnit (algebraMap (Per.Ainf l) (Per.AinfP l) (l : Per.Ainf l)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have h2 := h.map (Ideal.Quotient.mk (Per.kerP l ^ n))
  rwa [map_natCast, map_natCast] at h2

end GlobalTheory.MemLoc.CrisMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowJointStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_of_tameGenAt_of_char_pow_eq_one : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {M : Type} [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (L : ℕ)
    (γ : Formalism.ConjugateSelfDual.G E Ω) (π : Ω) (w : E),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω)) → ((L : ℕ) : 𝓞 E) ∉ P.asIdeal → Formalism.BasicNotions.TameGenAt A γ →
    (∀ τ : Formalism.ConjugateSelfDual.G E Ω, (∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) → φ τ = 1) → φ γ ^ L = 1 →
    π ≠ 0 → π ^ L = algebraMap E Ω w →
    ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ b : ℕ, φ σ = φ γ ^ b ∧ σ π = (γ π / π) ^ b * π := by
  first | exact @GlobalTheory.TameJoint.exists_pow_joint | exact GlobalTheory.TameJoint.exists_pow_joint | (intros; apply GlobalTheory.TameJoint.exists_pow_joint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FieldsIsConductorPrimesModulus
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem

theorem Base.fields_isCond : ∀ (B : Base) (X : PreX B.toPre), B.fields.IsCond (B.primes X).cond := by
  intro B X j
  exact UpperTheory.Ram.isCond_condN B.host j

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterOfPolynomialOfCuspidalLabelStatement
section
open CategoryTheory Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidalCharacterOfPolynomial_of_cuspidalLabel : ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : Formalism.L2.NT.IsGenSys L.gen), t = L.teich → ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (P : (ZMod g)[X]), 1 ≤ d → GlobalTheory.GLq.IsCusp (fun x => V.character x) → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (Formalism.L2.NT.convC t ht L.gen hζ) V P → GlobalTheory.GLq.IsCuspOf L P (fun x => V.character x) := by
  first | exact @GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel | exact GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel | (intros; apply GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionFlatten
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem linComb_pow_pow_sec {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ) (hm : m = a * n) (g : Y ⟶ X)
    (s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n))) :
    ∃ s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι),
      g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  let M := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)
  let N := LB.LinComb M (K := Fin 1) (fun _ => g) (fun _ => n)
  let P := LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)
  have le : ∀ i : Fin 1 → L.ι, P.U i ≤ N.U (fun k _ => i k) := fun i y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy k
  have gN : ∀ (x : Y) (i j : Fin 1 → L.ι) (hi : x ∈ P.U i) (hj : x ∈ P.U j),
      gm (𝟙 Y) x (P.U i ⊓ P.U j) (P.g i j) =
        gm (𝟙 Y) x (N.U (fun k _ => i k) ⊓ N.U (fun k _ => j k)) (N.g (fun k _ => i k) (fun k _ => j k)) := by
    intro x i j hi hj
    refine (gm_linComb L (fun _ : Fin 1 => g) (fun _ => m) (𝟙 Y) x i j hi hj).trans
      (Eq.trans ?_ (gm_linComb M (fun _ : Fin 1 => g) (fun _ => n) (𝟙 Y) x _ _ (le i hi) (le j hj)).symm)
    simp only [Fintype.prod_unique]
    refine Eq.trans ?_ (congrArg (· ^ n) (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => a) (𝟙 Y ≫ g) x
      (fun _ => i default) (fun _ => j default) (Set.mem_iInter.1 (le i hi) default)
      (Set.mem_iInter.1 (le j hj) default))).symm
    simp only [Fintype.prod_unique, Category.comp_id, hm, zpow_mul]
  refine ⟨⟨fun i => (Y.presheaf.map (homOfLE (le i)).op).hom (s.f (fun k _ => i k)), fun i j => ?_⟩, ?_⟩
  · apply fn_ext
    intro x hx
    have hx' : (𝟙 Y) x ∈ P.U i ⊓ P.U j := hx
    have hN : (𝟙 Y) x ∈ N.U (fun k _ => i k) ⊓ N.U (fun k _ => j k) := ⟨le i hx.1, le j hx.2⟩
    have e := congrArg (gs (𝟙 Y) x _) (s.compat (fun k _ => i k) (fun k _ => j k))
    rw [gs_res _ _ _ hN, gs_mul _ _ _ hN, gs_unit _ _ _ hN, gs_res _ _ _ hN] at e
    have hi : (𝟙 Y) x ∈ P.U i := hx.1
    have hj : (𝟙 Y) x ∈ P.U j := hx.2
    rw [gs_res _ _ _ hx', gs_res (𝟙 Y) x (le i) hi, gs_mul _ _ _ hx', gs_unit _ _ _ hx', gs_res _ _ _ hx',
      gs_res (𝟙 Y) x (le j) hj, e, gN x i j hx.1 hx.2]
  · intro Z r z j hj
    have hz : r z ∈ P.U (fun _ => j) := Set.mem_iInter.2 fun _ => hj
    exact gs_res r z (le _) hz _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NegOneNormFromCmFieldFiniteAdelesStatement
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_one_norm_from_cmField_finiteAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), ∃ y : E ⊗[F] FiniteAdeleRing (𝓞 F) F, Formalism.UG.sigR cm.sig (FiniteAdeleRing (𝓞 F) F) y * y = -1 := by
  first | exact @GlobalTheory.neg_one_norm_finiteAdele | exact GlobalTheory.neg_one_norm_finiteAdele | (intros; apply GlobalTheory.neg_one_norm_finiteAdele <;> assumption)
end

