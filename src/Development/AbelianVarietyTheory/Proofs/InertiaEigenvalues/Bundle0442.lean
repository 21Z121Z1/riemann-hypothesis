import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0427
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0400
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0425
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallSubgroupCocycleFormNeZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.FormNonzero

theorem cob_of_vanish {G Λ V : Type} [Group G] [CommRing Λ] [AddCommGroup V] [Module Λ V] (π : Representation Λ G V)
    (L : Subgroup G) (hL : ∀ h ∈ L, ∀ m, π h m = m) (z : G) (d : Λ) (hd : IsUnit (d - 1)) (hz : ∀ m, π z m = d • m)
    (hc : ∀ g, g * z * g⁻¹ * z⁻¹ ∈ L) (f : G → V) (hf : ∀ g h, f (g * h) = f g + π g (f h)) (h0 : ∀ h ∈ L, f h = 0) :
    Cob π f := by
  obtain ⟨u, hu⟩ := hd
  refine ⟨((u⁻¹ : Λˣ) : Λ) • f z, fun g => ?_⟩
  have e1 : f (g * z) = f (z * g) := by
    have : g * z = (g * z * g⁻¹ * z⁻¹) * (z * g) := by group
    rw [this, hf, h0 _ (hc g), hL _ (hc g), zero_add]
  rw [hf, hf, hz] at e1
  rw [map_smul, ← smul_sub]
  have e2 : π g (f z) - f z = (d - 1) • f g := by
    rw [sub_smul, one_smul, sub_eq_sub_iff_add_eq_add, add_comm (π g (f z)), e1, add_comm]
  rw [e2, smul_smul, ← hu, Units.inv_mul, one_smul]

theorem repOn_scalar {G O Λ : Type} [Group G] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : G →* GL (Fin r) O)
    (κ : G →* Λˣ) (Y : Type) [AddCommGroup Y] [Module Λ Y] (z : G) (d : O) (hκ : κ z = 1)
    (hz : (ρ z : Matrix (Fin r) (Fin r) O) = d • (1 : Matrix (Fin r) (Fin r) O)) (m : Fin r → Y) :
    repOn ρ κ Y z m = algebraMap O Λ d • m := by
  funext a
  simp only [repOn, matAct, MonoidHom.coe_mk, OneHom.coe_mk, hκ, hz, Units.val_one, one_smul, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply_ne hb.symm]
  · simp

theorem exists_bform_ne_zero : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (x₀ : Fin a → A) (j : Fin a) (c : A) (y : Z1 (repOn ρ κ⁻¹ A)), matAct Φ x₀ = 0 → x₀ j ∣ c → ¬ Cob (repOn ρ κ⁻¹ A) (fun g => ((X.l i : A) ^ nu X i * c) • y.1 g) → ∃ h ∈ L, bform (X := X) (fun g => rect (Z g) x₀) y.1 h ≠ 0 := by
  intro D N X bkP i s hl M L z hM hz hL A _ _ _ _ _ _ κ Q ρ hS hK hρ hanti hκz hκL a Φ Z hU x₀ j c y hx₀ hj hy
  by_contra hcon
  push Not at hcon
  apply hy
  obtain ⟨d, hd, hd2, hd1, he⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z hS.1.1 hz
  obtain ⟨x, hx, -⟩ := (hU A).1 x₀ hx₀
  have hcl := GlobalTheory.T.two_mul_cocycle_values_zero_on_small_subgroup D N X bkP i s hl M L z hM hz hL A κ Q ρ hS hK hρ hanti hκz hκL x y
    (fun h hh => by rw [hx]; exact hcon h hh)
  let I : Ideal A := Ideal.span {t | ∃ h ∈ L, ∃ b, t = x.1 h b}
  have hjI : x₀ j ∈ I := by
    letI : TopologicalSpace (A ⧸ I) := ⊥
    haveI : DiscreteTopology (A ⧸ I) := ⟨rfl⟩
    have hker : matAct Φ (fun k => I.mkQ (x₀ k)) = 0 := by
      funext k
      have := congrArg I.mkQ (congrFun hx₀ k)
      simpa only [matAct, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, Pi.zero_apply, map_zero] using this
    obtain ⟨x', hx', -⟩ := (hU (A ⧸ I)).1 _ hker
    have h0 := (hU (A ⧸ I)).2.1 _ hker (by
      rw [← hx']
      refine cob_of_vanish _ L (fun h hh m => ?_) z (algebraMap (X.O0 i) A d) (by simpa using hd1.map (algebraMap (X.O0 i) A))
        (repOn_scalar _ _ _ z _ hκz (by rw [Tgl_coe, hd])) hL.1.2.2.2.1 _ x'.2.2 (fun h hh => ?_)
      · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z hM hL A κ ρ hK hρ (A ⧸ I) h hh).1, hκL h hh, Units.val_one, one_smul]
      · funext b
        have e : x'.1 h b = I.mkQ (x.1 h b) := by
          rw [hx, hx']
          simp only [rect, map_sum, map_smul]
        rw [e, Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Ideal.subset_span ⟨h, hh, b, rfl⟩)
    have := congrFun h0 j
    rwa [Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have hcI : c ∈ I := by
    obtain ⟨t, rfl⟩ := hj
    exact I.mul_mem_right _ hjI
  have hkill : ∀ t ∈ I, ∀ h' ∈ L, ∀ b, (X.l i : A) ^ nu X i * t * y.1 h' b = 0 := by
    intro t ht h' hh' b
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨h, hh, b', rfl⟩ := ht
      exact hcl h hh h' hh' b' b
    | zero => simp
    | add t t' _ _ h1 h2 => rw [mul_add, add_mul, h1, h2, add_zero]
    | smul u t _ h1 => rw [smul_eq_mul]; linear_combination u * h1
  have hρz : (ρ z : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • 1 := by
    have hinv : (Tmat i s z)⁻¹ = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • 1 := by
      apply Matrix.inv_eq_left_inv
      rw [hd, Matrix.smul_mul, one_mul, smul_smul, Units.inv_mul, one_smul]
    rw [hρ z, Tdual, he, hinv, Units.val_one, one_smul, Matrix.transpose_smul, Matrix.transpose_one]
  have hdi := GlobalTheory.TwSys.TameScalar.isUnit_sub_one _ (GlobalTheory.TwSys.TameScalar.isUnit_inv_sq_sub_one d hd2)
  refine cob_of_vanish _ L (fun h hh m => ?_) z (algebraMap (X.O0 i) A ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i))
    (by simpa only [map_sub, map_one] using hdi.map (algebraMap (X.O0 i) A))
    (repOn_scalar _ _ _ z _ (by simp [hκz]) hρz) hL.1.2.2.2.1 _ (fun g h => ?_) (fun h hh => ?_)
  · rw [(GlobalTheory.T.twisted_representation_kills_small_subgroup D N X i s hl M L z hM hL A κ⁻¹ ρ hK hρ A h hh).2.1]
    simp [hκL h hh]
  · rw [y.2.2, smul_add, map_smul]
  · funext b
    exact hkill c hcI h hh b

end GlobalTheory.NewPrime.FormNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserEisensteinNotInXPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.EisShift

theorem taylor_coeff_pred {R : Type*} [CommRing R] (f : Polynomial R) (hf : f.Monic) (n : ℕ)
    (hn : f.natDegree = n + 1) (r : R) :
    (Polynomial.taylor r f).coeff n = f.coeff n + ((n + 1 : ℕ) : R) * r := by
  have h1 : (Polynomial.hasseDeriv n f).natDegree ≤ 1 := by
    have := Polynomial.natDegree_hasseDeriv_le f n
    omega
  have hl : f.coeff (1 + n) = 1 := by
    rw [add_comm, ← hn]; exact hf.coeff_natDegree
  rw [Polynomial.taylor_coeff, Polynomial.eq_X_add_C_of_natDegree_le_one h1]
  simp only [Polynomial.hasseDeriv_coeff, hl, zero_add, Nat.choose_self, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [add_comm 1 n, Nat.choose_succ_self_right]
  push_cast
  ring

theorem sq_dvd {R O : Type*} [CommRing R] [IsDomain R] [CommRing O] [IsLocalRing O] [Algebra R O]
    (p : R) (hp : p ≠ 0) (π : O) (hπ : ¬ IsUnit π) (E : Polynomial R) (hE : E.Monic)
    (h2 : 2 ≤ E.natDegree) (hd : ∀ i < E.natDegree, p ∣ E.coeff i)
    (w : Rˣ) (h0 : E.coeff 0 = p * w) (hr : Polynomial.aeval π E = 0) :
    π ^ 2 ∣ algebraMap R O p := by
  have hg : Polynomial.C p ∣ E - Polynomial.X ^ E.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i E.natDegree with h | h | h
    · rw [if_neg h.ne, sub_zero]; exact hd i h
    · rw [if_pos h, h, hE.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_self]; exact dvd_zero _
  obtain ⟨g, hg⟩ := hg
  have hg0 : g.coeff 0 = w := by
    have := congrArg (fun q => Polynomial.coeff q 0) hg
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul] at this
    rw [if_neg (by omega), sub_zero, h0] at this
    exact (mul_left_cancel₀ hp this).symm
  have hu : IsUnit (Polynomial.aeval π g) := by
    have e : Polynomial.aeval π g
        = algebraMap R O w + π * Polynomial.aeval π g.divX := by
      conv_lhs => rw [← Polynomial.X_mul_divX_add g]
      simp [hg0, add_comm]
    by_contra hn
    have h1 : Polynomial.aeval π g ∈ IsLocalRing.maximalIdeal O := hn
    have h3 : π * Polynomial.aeval π g.divX ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ hπ
    have h4 := Ideal.sub_mem _ h1 h3
    rw [e, add_sub_cancel_right] at h4
    exact h4 ((Units.isUnit w).map (algebraMap R O))
  have e := congrArg (Polynomial.aeval π) hg
  simp only [map_sub, hr, map_pow, Polynomial.aeval_X, map_mul, Polynomial.aeval_C, zero_sub] at e
  rw [← hu.dvd_mul_right, ← e, dvd_neg]
  exact pow_dvd_pow _ h2

theorem exists_uniformiser : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (Wq l a) O] [Module.Finite (Wq l a) O], Function.Injective (algebraMap (Wq l a) O) → (∀ x : O, ∃ c : Wq l a, ¬ IsUnit (x - algebraMap (Wq l a) O c)) → ∃ (π : O) (Ep : Polynomial (Wq l a)), Irreducible π ∧ (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) ∧ (∃ i, ¬ l ∣ i ∧ Ep.coeff i ≠ 0) ∧ Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f := by
  intro l _ a _ O _ _ _ _ _ hinj hres
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨E, hm, hpos, hd, ⟨w, h0⟩, hr, hs, hmin⟩ := GlobalTheory.T.eisenstein_minpoly_uniformizer_witt_totallyRamified l a O hinj hres π hπ
  by_cases h : ∃ i, ¬ l ∣ i ∧ E.coeff i ≠ 0
  · exact ⟨π, E, hπ, ⟨hm, hpos, hd, w, h0⟩, h, hr, hs, hmin⟩
  push_neg at h
  haveI : CharZero (Wq l a) := by
    refine charZero_of_inj_zero fun n hn => ?_
    by_contra hn0
    have hx : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hn0
    have e := congrArg (algebraMap ℤ_[l] (Wq l a)) (PadicInt.unitCoeff_spec hx)
    rw [map_natCast, hn, map_mul, map_pow, map_natCast] at e
    exact mul_ne_zero ((Units.isUnit _).map (algebraMap ℤ_[l] (Wq l a))).ne_zero
      (pow_ne_zero _ (WittVector.p_nonzero l (Fq l a))) e.symm
  have hl : l.Prime := Fact.out
  have hl0 : (l : Wq l a) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have hle : l ∣ E.natDegree := by
    by_contra hn
    have := h _ hn
    rw [hm.coeff_natDegree] at this
    exact one_ne_zero this
  have h2 : 2 ≤ E.natDegree := hl.two_le.trans (Nat.le_of_dvd hpos hle)
  obtain ⟨t, ht⟩ := sq_dvd (l : Wq l a) hl0 π hπ.not_isUnit E hm h2 hd w h0 hr
  have hu : IsUnit (1 + π * t) := by
    by_contra hn
    have h1 : 1 + π * t ∈ IsLocalRing.maximalIdeal O := hn
    have h3 : π * t ∈ IsLocalRing.maximalIdeal O := Ideal.mul_mem_right _ _ hπ.not_isUnit
    have h4 := Ideal.sub_mem _ h1 h3
    rw [add_sub_cancel_right] at h4
    exact h4 isUnit_one
  have hπ' : Irreducible (π + algebraMap (Wq l a) O l) := by
    have : π + algebraMap (Wq l a) O l = π * (1 + π * t) := by rw [ht]; ring
    rw [this]
    exact (irreducible_mul_isUnit hu).2 hπ
  obtain ⟨F, fm, fpos, fd, fw, fr, fs, fmin⟩ := GlobalTheory.T.eisenstein_minpoly_uniformizer_witt_totallyRamified l a O hinj hres _ hπ'
  refine ⟨_, F, hπ', ⟨fm, fpos, fd, fw⟩, ?_, fr, fs, fmin⟩
  have d1 : F ∣ Polynomial.taylor (-(l : Wq l a)) E := by
    apply fmin
    rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simpa using hr
  have d2 : E ∣ Polynomial.taylor (l : Wq l a) F := by
    apply hmin
    rw [Polynomial.taylor_apply, Polynomial.aeval_comp]
    simpa using fr
  have mt : ∀ (r : Wq l a) (f : Polynomial (Wq l a)), f.Monic → (Polynomial.taylor r f).Monic := by
    intro r f hf
    rw [Polynomial.taylor_apply]
    exact hf.comp_X_add_C r
  have n2 := Polynomial.natDegree_le_of_dvd d2 (mt _ _ fm).ne_zero
  rw [Polynomial.natDegree_taylor] at n2
  have heq : Polynomial.taylor (-(l : Wq l a)) E = F :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le fm (mt _ _ hm) d1
      (by rw [Polynomial.natDegree_taylor]; exact n2)
  obtain ⟨n, hn⟩ : ∃ n, E.natDegree = n + 1 := ⟨E.natDegree - 1, by omega⟩
  have hnd : ¬ l ∣ n := by
    intro hc
    rw [hn] at hle
    exact hl.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right hc).1 hle))
  refine ⟨n, hnd, ?_⟩
  rw [← heq, taylor_coeff_pred E hm n hn, h n hnd, zero_add]
  exact mul_ne_zero (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)) (neg_ne_zero.2 hl0)

end GlobalTheory.EisShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLevelCupSwapCoboundaryIff
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKSwapCup

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem liftQ_mem (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (q : ↥L.T ⧸ I) :
    Formalism.MainNotions.LocalSituation.liftQ L I q ∈ L.T :=
  (Submodule.Quotient.mk_surjective I q).choose.2

theorem mk_liftQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (q : ↥L.T ⧸ I) :
    (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L I q, liftQ_mem L I q⟩ : ↥L.T) : ↥L.T ⧸ I) = q :=
  (Submodule.Quotient.mk_surjective I q).choose_spec

theorem liftQ_sub (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (x : ↥L.T)
    (q : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (hq : Submodule.Quotient.mk x = q) :
    ∃ t ∈ L.T, Formalism.MainNotions.LocalSituation.liftQ L _ q - (x : V) = (algebraMap O LL ϖ) ^ r • t := by
  have h : (⟨Formalism.MainNotions.LocalSituation.liftQ L _ q, liftQ_mem L _ q⟩ : ↥L.T) - x ∈
      (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T) :=
    (Submodule.Quotient.eq _).1 ((mk_liftQ L _ q).trans hq.symm)
  generalize hy : (⟨Formalism.MainNotions.LocalSituation.liftQ L _ q, liftQ_mem L _ q⟩ : ↥L.T) - x = y at h
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨t, -, ht⟩ := h
  subst ht
  refine ⟨t, t.2, ?_⟩
  rw [← map_pow, algebraMap_smul, ← Submodule.coe_smul, ← hy]
  rfl

theorem inv_pow_mul_pow_mem (ϖ : O) (r : ℕ) :
    ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * (algebraMap O LL ϖ) ^ r = algebraMap O LL e := by
  rcases eq_or_ne (algebraMap O LL ϖ) 0 with h | h
  · rcases Nat.eq_zero_or_pos r with hr | hr
    · exact ⟨1, by subst hr; simp⟩
    · exact ⟨0, by rw [h, zero_pow hr.ne', mul_zero, map_zero]⟩
  · exact ⟨1, by rw [← mul_pow, inv_mul_cancel₀ h, one_pow, map_one]⟩

end Gen
end GlobalTheory.BKSwapCup

namespace GlobalTheory.BKSwapCup

section Cong
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def swapF (L : Lattice (O := O) ρ) (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O) (r : ℕ)
    (s : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (d : G → V') (g : G) : LL :=
  (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (d g)

theorem swap_cong (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (hint : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ e : O, P x y = algebraMap O LL e)
    (χ : G → LL) (hχ : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (ϖ : O) (r : ℕ)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (s : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (hs : ∀ g h, s (g * h) = s g + actQ L _ hI g (s h))
    (d : G → V') (hdT : ∀ g, d g ∈ L'.T) (hdmul : ∀ g h, d (g * h) = d g + ρ' g (d h))
    (q : G → ↥L'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L'.T))
    (hq : ∀ h, Submodule.Quotient.mk (⟨d h, hdT h⟩ : ↥L'.T) = q h) (g h : G) :
    ∃ e : O, GlobalTheory.BKFinLevel.cupQ L L' P ϖ r s q (g, h)
      + cupLD L P.flip d (fun g => GlobalTheory.BKFinLevel.ioL L ϖ r (s g)) (g, h)
      + (χ g * swapF L P ϖ r s d h - swapF L P ϖ r s d (g * h) + swapF L P ϖ r s d g)
      = algebraMap O LL e := by
  have huT : ∀ g, Formalism.MainNotions.LocalSituation.liftQ L _ (s g) ∈ L.T := fun g => liftQ_mem L _ (s g)
  have hmk : ∀ g, (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s g), huT g⟩ : ↥L.T) :
      ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) = s g :=
    fun g => mk_liftQ L _ (s g)

  have hq3 : (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s g), huT g⟩ +
      actT L g ⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s h), huT h⟩ : ↥L.T) :
      ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) = s (g * h) := by
    rw [hs g h]
    exact (Submodule.Quotient.mk_add _).trans
      (congrArg₂ (· + ·) (hmk g) (congrArg (actQ L _ hI g) (hmk h)))
  obtain ⟨t3, ht3, hu3⟩ := liftQ_sub L ϖ r _ _ hq3

  obtain ⟨t1, ht1, hd1⟩ := liftQ_sub L' ϖ r _ _ (hq h)

  have hio : GlobalTheory.BKFinLevel.ioL L ϖ r (s h) =
      Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) :=
    (congrArg (GlobalTheory.BKFinLevel.ioL L ϖ r) (mk_liftQ L _ (s h))).symm.trans
      (GlobalTheory.BKFinLevel.ioL_mk L ϖ r _)
  have hl : (Submodule.Quotient.mk (liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h))) : V ⧸ L.T) =
      GlobalTheory.BKFinLevel.ioL L ϖ r (s h) :=
    (Submodule.Quotient.mk_surjective L.T _).choose_spec
  have ht2 := (Submodule.Quotient.eq _).1 (hl.trans hio)
  show ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (ρ' g (Formalism.MainNotions.LocalSituation.liftQ L' _ (q h)))
      + P.flip (d g) (ρ g (liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h))))
      + (χ g * ((algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) (d h))
        - (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s (g * h))) (d (g * h))
        + (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (d g)) = algebraMap O LL e
  generalize liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h)) = w at ht2 ⊢
  obtain ⟨t2, ht2', rfl⟩ : ∃ t2 ∈ L.T,
      w = (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ L _ (s h) + t2 :=
    ⟨_, ht2, by abel⟩
  have E1 : Formalism.MainNotions.LocalSituation.liftQ L' _ (q h) = d h + (algebraMap O LL ϖ) ^ r • t1 :=
    sub_eq_iff_eq_add'.1 hd1
  have E3 : Formalism.MainNotions.LocalSituation.liftQ L _ (s (g * h)) = Formalism.MainNotions.LocalSituation.liftQ L _ (s g) +
      ρ g (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) + (algebraMap O LL ϖ) ^ r • t3 :=
    sub_eq_iff_eq_add'.1 hu3
  obtain ⟨e0, he0⟩ := inv_pow_mul_pow_mem (LL := LL) ϖ r
  obtain ⟨e1, he1⟩ := hint _ (huT g) _ (L'.stable g _ ht1)
  obtain ⟨e2, he2⟩ := hint _ (L.stable g _ ht2') _ (hdT g)
  obtain ⟨e3, he3⟩ := hint t3 ht3 (d g + ρ' g (d h)) (by rw [← hdmul]; exact hdT _)
  refine ⟨e0 * e1 + e2 - e0 * e3, ?_⟩
  have E5 : χ g * ((algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) (d h)) =
      (algebraMap O LL ϖ)⁻¹ ^ r * P (ρ g (Formalism.MainNotions.LocalSituation.liftQ L _ (s h))) (ρ' g (d h)) := by
    rw [hχ]; ring
  rw [E1, E3, hdmul, E5]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.flip_apply] at he3 ⊢
  rw [map_sub, map_add, map_mul, map_mul, ← he0, ← he1, ← he2, ← he3]
  ring

end Cong
end GlobalTheory.BKSwapCup

namespace GlobalTheory.BKSwapCup

section Cob

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem cobO_swap (hopen : IsOpen (Set.range (algebraMap O LL)))
    (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL)) {A A' : GRep G Qp LL O}
    (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (hm : IsDualLat1 PD LA LA' m) (ϖ : O) (r : ℕ)
    (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
    (s : G → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hs : s ∈ quotientCocycles LA _ hI)
    (d : ↥(latticeCocycles LA')) :
    CobO PD L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔
      CobO PD L1 (cupLD LA m.flip (d : G → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  have hdT : ∀ g, (d : G → A'.V) g ∈ LA'.T := fun g => d.2.2 g (Set.mem_univ g)
  have hint : ∀ x ∈ LA.T, ∀ y ∈ LA'.T, ∃ e : O, m x y = algebraMap O LL e :=
    fun x hx y hy => (hm.2 y).1 hy x hx
  have key := swap_cong LA LA' m hint (fun g => ((cycLL PD LL g : LLˣ) : LL)) hm.1.1 ϖ r hI s
    hs.2 (d : G → A'.V) hdT d.2.1.2 (redT LA' _ d) (fun _ => rfl)
  let Fq : G → LL ⧸ L1.T := fun g =>
    Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) g)
  have hFq : Fq ∈ ReciprocityTheory.Def.C1 G (⊤ : Submodule O (LL ⧸ L1.T)) := by
    refine ⟨?_, fun _ => Submodule.mem_top⟩
    have hT : IsOpen (L1.T : Set LL) := by rw [hL1]; exact hopen
    have hu : Continuous fun g => Formalism.MainNotions.LocalSituation.liftQ LA _ (s g) :=
      (hs.1.comp (Formalism.MainNotions.LocalSituation.liftQ LA _)).continuous
    have hc : Continuous (swapF LA m ϖ r s (d : G → A'.V)) :=
      continuous_const.mul ((IsModuleTopology.continuous_bilinear_of_finite_left m).comp
        (hu.prodMk d.2.1.1))
    exact Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk L1.T hT _ hc
  have hD : ReciprocityTheory.Def.d1 (repD L1) Fq ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := ⟨Fq, hFq, rfl⟩
  have heq : (fun x => (Submodule.Quotient.mk
      (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d) x) : LL ⧸ L1.T)) =
      -((fun x => (Submodule.Quotient.mk (cupLD LA m.flip (d : G → A'.V)
        (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g)) x) : LL ⧸ L1.T)) +
          ReciprocityTheory.Def.d1 (repD L1) Fq) := by
    funext x
    obtain ⟨g, h⟩ := x
    obtain ⟨e, he⟩ := key g h
    show (Submodule.Quotient.mk (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d) (g, h)) :
        LL ⧸ L1.T) = -(Submodule.Quotient.mk (cupLD LA m.flip (d : G → A'.V)
          (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g)) (g, h)) +
        (Submodule.Quotient.mk (((cycLL PD LL g : LLˣ) : LL) * swapF LA m ϖ r s (d : G → A'.V) h)
          - Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) (g * h))
          + Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) g)))
    rw [eq_neg_iff_add_eq_zero, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add,
      ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add, ← add_assoc, he,
      Submodule.Quotient.mk_eq_zero, hL1]
    exact ⟨e, rfl⟩
  unfold CobO
  rw [heq, neg_mem_iff, Submodule.add_mem_iff_left _ hD]

end Cob

theorem cobO_cupQ_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), ∀ s ∈ quotientCocycles LA _ hI, ∀ d : ↥(latticeCocycles LA'), CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔ CobO (P.PD K) L1 (cupLD LA m.flip (d : ↥(GK K) → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  intro l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hm ϖ r hI s hs d
  obtain ⟨-, -, -, htr, hopen⟩ := hO
  haveI := htr
  exact cobO_swap (P.PD K) hopen L1 hL1 LA LA' m hm ϖ r hI s hs d

end GlobalTheory.BKSwapCup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineInequalityDcrisFiniteConcreteRings
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Module TensorProduct

namespace GlobalTheory.Per.FontaineBound

theorem dcris_finite_le_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) :
    Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
      finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
  have := isDomain_cris (P.PD K) (isField_of_tied T)
  have := (P.PD K).finK₀
  have := LL.2
  refine finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.T.ratio_invariant_in_K0 l P AI T K b' b hb fun g hg => ?_) ρ
  have h1 := h ⟨g, hg⟩
  rw [P.PD_actB, P.PD_actB] at h1
  rw [mul_comm, h1, mul_comm]

theorem fontaineLe_of_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ K LL : FinExt l, FontaineLe (P.PD K) ↥LL.1 ∧
      ∀ (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
        [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V),
        FiniteDimensional ↥LL.1 ↥(Dcris (P.PD K) ρ) :=
  fun _ _ _ _ T K LL => ⟨fun V _ _ _ _ _ ρ => (dcris_finite_le_of_tied T K LL V ρ).2,
    fun V _ _ _ _ _ ρ => (dcris_finite_le_of_tied T K LL V ρ).1⟩

end GlobalTheory.Per.FontaineBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesMemOfFinset
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.CoefField

theorem entries_mem_of_finset : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → ∃ S : Finset (Qbar l), ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, z ∈ K) → ∀ g s t, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  intro l _ E Ω _ _ _ _ _ a ρ hρ
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a ρ hρ
    ⟨⊥, inferInstance⟩
  haveI := L.2
  let B := Module.finBasis ℚ_[l] ↥L.1
  classical
  refine ⟨Finset.univ.image (fun i => ((B i : ↥L.1) : Qbar l)), fun K hK g s t => ?_⟩
  have key : ∀ x : ↥L.1, (x : Qbar l) ∈ K := by
    intro x
    have hx : x ∈ Submodule.span ℚ_[l] (Set.range B) := B.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    | zero => simpa using K.zero_mem
    | add y z _ _ hy hz => simpa using K.add_mem hy hz
    | smul c y _ hy => simpa using K.smul_mem hy (x := c)
  exact key ⟨_, hL g s t⟩

end GlobalTheory.CoefField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Hilbert90MatrixCoboundaryCharPFiniteLevelStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_matrix_coboundary_of_fixed_frobenius_pow : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (R : Type) [CommRing R] [IsDomain R] [CharP R p] (ρ : G →* (R ≃+* R)) (m : ℕ), 0 < m → Finite (G ⧸ GlobalTheory.UnramifiedCrys.fixer ρ p m) → ∀ (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) R), (∀ g h i j, ρ g (M h i j) = M h i j) → (∀ h i j, M h i j ^ p ^ m = M h i j) → (∀ g ∈ GlobalTheory.UnramifiedCrys.fixer ρ p m, M g = 1) → ∃ W : Matrix (Fin r) (Fin r) R, IsUnit W.det ∧ (∀ i j, W i j ^ p ^ m = W i j) ∧ ∀ g, M g * W.map (ρ g) = W := by
  first | exact @GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary | exact GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary | (intros; apply GlobalTheory.UnramifiedHilbertNinety.exists_matrix_coboundary <;> assumption)
end

