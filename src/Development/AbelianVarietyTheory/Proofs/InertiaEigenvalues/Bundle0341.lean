import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import GroundTheory.LocalFields.Bundle0003
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
import GroundTheory.LocalFields.Bundle0010

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastEqOneOfMod
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ScalarFrob

section HidaSetting

open IsLocalRing GlobalTheory.TwistDet GlobalTheory.PrimeToInertia

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

theorem natCast_eq_one_of_mod {q : ℕ} (hq : q % X.l i = 1) : (q : ResidueField (X.O0 i)) = 1 := by
  have hl : ((X.l i : ℕ) : ResidueField (X.O0 i)) = 0 := by
    rw [← map_natCast (residue (X.O0 i)), (residue_eq_zero_iff _).2 (l_mem i)]
  rw [← Nat.mod_add_div q (X.l i), hq]
  push_cast
  rw [hl]
  simp

theorem frob_scalar_place (bkP : BKPh X) (h : GalHyp bkP i s) {P : PlE D.host} {z : GE N} {L : Subgroup (GE N)}
    (hz : IsTameInertiaElementAtTwistPrime X i z) (hL : Small i s L z) (hA : ∀ v, Over P v → v ∉ X.S0 i ∧ normV v % X.l i = 1)
    (hS : ∀ σ : GE N, IsFrob (N.plOm.1 P) (normV P) σ → ∃ g : GE N, g * σ * g⁻¹ * z⁻¹ ∈ L)
    {v : PlE D.host} (hv : Over P v) {σ : GE N}
    (hσ : IsFrob (N.plOm.1 v) (normV v) σ) : ∃ c : ResidueField (X.O0 i), c ≠ 0 ∧ c ≠ 1 ∧ resT i s σ = c • 1 := by
  obtain ⟨e, he, -, hu, -⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have key : ∀ τ : GE N, IsFrob (N.plOm.1 P) (normV P) τ → resT i s τ = residue (X.O0 i) e • 1 := by
    intro τ hτ
    obtain ⟨g, hg⟩ := hS τ hτ
    have e1 : resT i s (g * τ * g⁻¹ * z⁻¹ * z) = residue (X.O0 i) e • 1 := by
      rw [map_mul, resT_apply, (hL.2.2.2.2 _ hg).1, one_mul, resT_apply, he]
      ext a b
      by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    have e2 := conj_scalar _ e1 g⁻¹
    rwa [show g⁻¹ * (g * τ * g⁻¹ * z⁻¹ * z) * g⁻¹⁻¹ = τ by group] at e2
  have hp := hA v hv
  have hp0 := hA _ (over_refl P)
  rcases hv with rfl | hv
  · exact ⟨_, c0, c1, key σ hσ⟩
  · have ε := eps_frob i hp.1 (natCast_eq_one_of_mod i hp.2) hσ
    obtain ⟨τ, g, hτ, rfl⟩ := exists_frob_of_conj X hv hσ
    have ε0 := eps_frob i hp0.1 (natCast_eq_one_of_mod i hp0.2) hτ
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at ε
    refine ⟨_, inv_ne_zero c0, inv_ne_one.2 c1, conj_scalar _ (scalar_of_dual i s ε c0 ?_) g⟩
    obtain ⟨A, hA⟩ := h.2.2.1
    have e3 : ((((eps0 X i τ : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s τ).map (residue (X.O0 i)) =
        residue (X.O0 i) e • 1 := by
      rw [← key τ hτ, resT_apply]
      ext a b
      simp [ε0]
    rw [hA τ _ (cConj_apply X τ), Matrix.map_mul, Matrix.map_mul, e3, mul_smul_comm, mul_one, smul_mul_assoc,
      ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

end HidaSetting

open GlobalTheory.PrimeToInertia in

theorem firstPlace : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstPlace i s := by
  intro h1 h2 h3 D N X bkP i s h P z L hz hL hA hS Λ _ _ _ _ κ hκ hκl B _ _ _ _ hB ρ hρ v hv
  have hp := hA v hv
  have hq := natCast_eq_one_of_mod i hp.2
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
  obtain ⟨c, c0, c1, hc⟩ := frob_scalar_place i s bkP h hz hL hA hS hv hσ
  obtain ⟨c', c1', hc'⟩ : ∃ c' : IsLocalRing.ResidueField (X.O0 i), c' ≠ 1 ∧
      ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (IsLocalRing.residue _) = c' • 1 := by
    rcases hρ with rfl | hρ
    · exact ⟨c, c1, by rw [Tgl_coe, ← resT_apply, hc]⟩
    · exact ⟨c⁻¹, inv_ne_one.2 c1, by rw [hρ, dual_of_scalar i s (eps_frob i hp.1 hq hσ) c0 hc]⟩
  have hcont : Continuous fun g => ((ρ g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
    rcases hρ with rfl | hρ
    · simp_rw [Tgl_coe]; exact continuous_Tmat i s
    · simp_rw [show ∀ g, _ = _ from hρ]; exact continuous_Tdual i s
  refine primary_case (l := X.l i) h1 h2 h3 (N.plOm.2 v) (fun h => hp.1 (X.twistExcludedPlaces_contains_residueChar i h)) _
    ?_ (fun m => ?_) ⟨σ, hσ.1⟩ hσ (fun m hm => ?_) (fun m hm => ?_)
  · exact (contAction_repOn (X.twistBaseCoefficientRing_isAdic i) ρ hcont κ hκ hB).comp
      (f := fun p : DecV N v × (Fin D.R.r → B) => ((p.1 : GE N), p.2)) (by fun_prop)
  · obtain ⟨n, hn⟩ := exists_pow_kill hB m
    refine ⟨n, funext fun a => ?_⟩
    have := hn _ (map_mem_pow (Λ := Λ) (Ideal.pow_mem_pow (l_mem i) n)) a
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this
    exact this
  · exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκl σ) c1' hc' (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm)
  · exact eq_zero_of_scalar Fact.out (l_mem i) ρ κ (hκl σ) c1' hc' hq m hm

end GlobalTheory.ScalarFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodMatrixRestrictionScalarsBlockDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem unramifiedToBst_algebraMap_padic {l : ℕ} [Fact l.Prime] (P : LocPrime l) (q : ℚ_[l]) :
    ks P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] (Bst P) q := by
  simp only [ks, RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, Polynomial.algebraMap_apply]

theorem frobeniusSemistablePow_unramifiedToBst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) :
    (phiSt P ^ m) (ks P c) = ks P (fr l m c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, add_comm, fr_add, fr_one]
    have := phiSt_algebraMap P (fr l m c)
    rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply] at this
    exact this

theorem frobeniusSemistablePow_galoisAction_comm {l : ℕ} [Fact l.Prime] (P : LocPrime l) (g : GQ l) (m : ℕ) (b : Bst P) :
    (phiSt P ^ m) (actSt P g b) = actSt P g ((phiSt P ^ m) b) := by
  induction m generalizing b with
  | zero => rfl
  | succ m ih => rw [pow_succ', AlgHom.mul_apply, ih, phiSt_actSt, AlgHom.mul_apply]

end GlobalTheory.PMon

namespace GlobalTheory.PMon

theorem inv_entries_mem_finiteExtension_unramified {l : ℕ} [Fact l.Prime] {N : Type} [Fintype N] [DecidableEq N] (K : FinExt l)
    (p : GL N ↥(MaximalUnramifiedExtension l)) (h : ∀ i j, (((p : Matrix N N ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) (i j : N) :
    ((((p⁻¹ : GL N ↥(MaximalUnramifiedExtension l)) : Matrix N N ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1 := by
  let S : Subfield ↥(MaximalUnramifiedExtension l) := K.1.toSubfield.comap (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))
  let A : Matrix N N S := Matrix.of fun i j => ⟨(p : Matrix N N ↥(MaximalUnramifiedExtension l)) i j, h i j⟩
  have hA : (S.subtype).mapMatrix A = (p : Matrix N N ↥(MaximalUnramifiedExtension l)) := by refine Matrix.ext fun i j => ?_; rfl
  have hmem : ((p : Matrix N N ↥(MaximalUnramifiedExtension l))⁻¹ i j) ∈ S := by
    rw [Matrix.inv_def, ← hA, ← RingHom.map_adjugate, ← RingHom.map_det]
    simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, Ring.inverse_eq_inv']
    exact S.mul_mem (S.inv_mem (A.det).2) (A.adjugate i j).2
  rw [Matrix.coe_units_inv]
  exact hmem

theorem period_resScalars : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l])
    (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) →
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    ∃ Q₀ : GL (n × Fin r) (Bst P), ∀ g : ↥(GK K),
      (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P)) *
        (Q₀ : Matrix (n × Fin r) (n × Fin r) (Bst P)).map (actSt P (g : GQ l)) = Q₀ := by
  intro l _ P n _ _ K r σ Q ρ₀ p h1 h2 h3
  classical
  let φm : Fin r → Bst P →+* Bst P := fun m => ((phiSt P ^ (m : ℕ) : Bst P →ₐ[ℚ_[l]] Bst P) : Bst P →+* Bst P)
  let Pu : GL (n × Fin r) (Bst P) := Units.map (RingHom.mapMatrix (m := n × Fin r) (ks P)).toMonoidHom p⁻¹
  let Du : GL (n × Fin r) (Bst P) := Units.map (Matrix.blockDiagonalRingHom n (Fin r) (Bst P)).toMonoidHom
    (MulEquiv.piUnits.symm fun m => Units.map (RingHom.mapMatrix (m := n) (φm m)).toMonoidHom Q)
  refine ⟨Pu * Du, fun g => ?_⟩
  set pv : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) with hpv
  have hPu : (Pu : Matrix (n × Fin r) (n × Fin r) (Bst P)) = pv.map (ks P) := rfl
  have hDu : (Du : Matrix (n × Fin r) (n × Fin r) (Bst P)) =
      Matrix.blockDiagonal fun m => (Q : Matrix n n (Bst P)).map (φm m) := rfl
  set act := actSt P (g : GQ l)

  have hPfix : (pv.map (ks P)).map act = pv.map (ks P) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact act_ks P g (inv_entries_mem_finiteExtension_unramified K p h2 i j)

  have hrel : (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) * pv =
      pv * Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) := by
    have hp : pv * (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1 := by
      rw [hpv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hp' : (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * pv = 1 := by
      rw [hpv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc _ = pv * ((p : Matrix _ _ ↥(MaximalUnramifiedExtension l)) * (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map
            (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) * pv := by rw [← Matrix.mul_assoc, hp, Matrix.one_mul]
      _ = _ := by rw [h3, Matrix.mul_assoc, Matrix.mul_assoc, hp', Matrix.mul_one]
  have hrelB := congrArg (fun M => M.map (ks P)) hrel
  simp only [Matrix.map_mul, Matrix.map_map] at hrelB
  have hks : (ks P) ∘ (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = algebraMap ℚ_[l] (Bst P) := funext (unramifiedToBst_algebraMap_padic P)
  rw [hks, Matrix.blockDiagonal_map _ _ (map_zero _)] at hrelB

  have hblock : ∀ m : Fin r, ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (ks P) *
      ((Q : Matrix n n (Bst P)).map (φm m)).map act = (Q : Matrix n n (Bst P)).map (φm m) := by
    intro m
    have e1 : ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (ks P) =
        ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).map (φm m) := by
      refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply, φm, AlgHom.coe_toRingHom]; exact (frobeniusSemistablePow_unramifiedToBst P m _).symm
    have e2 : ((Q : Matrix n n (Bst P)).map (φm m)).map act =
        ((Q : Matrix n n (Bst P)).map act).map (φm m) := by
      refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply, φm, AlgHom.coe_toRingHom, act]; exact (frobeniusSemistablePow_galoisAction_comm P _ m _).symm
    rw [e1, e2, ← Matrix.map_mul, h1 g]
  rw [Units.val_mul, hPu, hDu, Matrix.map_mul, hPfix, Matrix.blockDiagonal_map _ _ (map_zero _),
    ← Matrix.mul_assoc, hrelB, Matrix.mul_assoc, ← Matrix.blockDiagonal_mul]
  congr 2
  funext m
  exact hblock m

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeMemUnitFiltrationUnitsMin
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_one_add_pow_eq {R : Type*} [CommRing R] (y : R) (k : ℕ) :
    ∃ w : R, (1 + y) ^ k = 1 + (k : R) * y + y ^ 2 * w := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(1 + y) * w + k, ?_⟩
    rw [pow_succ, hw]; push_cast; ring

theorem one_add_pow_sub_one_mem {R : Type*} [CommRing R] (I : Ideal R) {n e k : ℕ} {y : R}
    (hy : y ∈ I ^ n) (hk : (k : R) ∈ I ^ e) :
    (1 + y) ^ k - 1 ∈ I ^ min (2 * n) (n + e) := by
  obtain ⟨w, hw⟩ := exists_one_add_pow_eq y k
  have h : (1 + y) ^ k - 1 = (k : R) * y + y ^ 2 * w := by rw [hw]; ring
  rw [h]
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.pow_le_pow_right (min_le_right _ _) ?_
    rw [add_comm n e, pow_add]
    exact Ideal.mul_mem_mul hk hy
  · refine Ideal.pow_le_pow_right (min_le_left _ _) ?_
    refine Ideal.mul_mem_right _ _ ?_
    rw [two_mul, pow_add, pow_two]
    exact Ideal.mul_mem_mul hy hy

theorem natCast_mem_maximalIdeal_pow_of_ordIs {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {p e : ℕ} (h : OrdIs F p e) : (p : 𝒪[F]) ∈ 𝓂[F] ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ]
  rw [OrdIs] at h
  rw [h]
  simp

theorem pow_mem_unitFiltrationUnits (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p e n : ℕ) (hp : OrdIs F p e) :
    ∀ x ∈ unitFiltrationUnits F n, x ^ p ∈ unitFiltrationUnits F (min (2 * n) (n + e)) := by
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨u ^ p, ?_, by simp⟩
  rw [SetLike.mem_coe, mem_unitFiltration] at hu ⊢
  have := one_add_pow_sub_one_mem (𝓂[F]) hu (natCast_mem_maximalIdeal_pow_of_ordIs hp)
  simpa using this

end GlobalTheory.PMon.Ram

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowInvSmulLiftMemDivisibleCocycles
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DivLift

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mk_inv_smul_liftQ (L : Lattice (O := O) ρ) (a : O) (ha : algebraMap O LL a ≠ 0)
    (y : ↥L.T) :
    (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L
      (Ideal.span {a} • ⊤ : Submodule O ↥L.T) (Submodule.Quotient.mk y)) : V ⧸ L.T) =
      Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • (y : V)) := by
  obtain ⟨y0, hy0, hs⟩ : ∃ y0 : ↥L.T, (y0 : V) = Formalism.MainNotions.LocalSituation.liftQ L
      (Ideal.span {a} • ⊤ : Submodule O ↥L.T) (Submodule.Quotient.mk y) ∧
      (Submodule.Quotient.mk y0 : ↥L.T ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) =
        Submodule.Quotient.mk y :=
    ⟨_, rfl, (Submodule.Quotient.mk_surjective _ (Submodule.Quotient.mk y)).choose_spec⟩
  rw [← hy0]
  have hmem := (Submodule.Quotient.eq _).1 hs
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨t, -, ht⟩ := hmem
  have ht' : a • (t : V) = (y0 : V) - (y : V) := congrArg Subtype.val ht
  rw [Submodule.Quotient.eq, ← smul_sub, ← ht', ← algebraMap_smul LL a, smul_smul,
    inv_mul_cancel₀ ha, one_smul]
  exact t.2

theorem inv_smul_liftQ_mem_Z1D [TopologicalSpace G] (L : Lattice (O := O) ρ) (a : O)
    (ha : algebraMap O LL a ≠ 0) (hI : StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T))
    (c : G → ↥L.T ⧸ (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) (hc : c ∈ quotientCocycles L _ hI) :
    (fun g => (Submodule.Quotient.mk ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ (c g)) :
      V ⧸ L.T)) ∈ divisibleCocycles L := by
  refine ⟨hc.1.comp (fun x => (Submodule.Quotient.mk
    ((algebraMap O LL a)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ L _ x) : V ⧸ L.T)), fun g h => ?_⟩
  have hgh := hc.2 g h
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (c g)
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (c h)
  have h1 : c (g * h) = Submodule.Quotient.mk (x + actT L g y) := by
    rw [hgh, ← hx, ← hy]; rfl
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + actD L g (Submodule.Quotient.mk _)
  rw [h1, ← hx, ← hy, mk_inv_smul_liftQ L a ha, mk_inv_smul_liftQ L a ha,
    mk_inv_smul_liftQ L a ha]
  show _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk (ρ g ((algebraMap O LL a)⁻¹ • (y : V)))
  rw [← Submodule.Quotient.mk_add, map_smul, ← smul_add]
  rfl

end Gen

theorem pow_inv_smul_liftQ_mem_Z1D : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) (c' : ↥(quotientCocycles LA' _ hI')), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
  intro l _ K LL _ _ _ O _ _ _ A' LA' r hI' c'
  have he : algebraMap O LL (((l : ℕ) : O) ^ r) = ((l : ℕ) : LL) ^ r := by
    rw [map_pow, map_natCast]
  have hl : ((l : ℕ) : LL) ≠ 0 := by
    intro h
    have h' : algebraMap ℚ_[l] LL (l : ℚ_[l]) = 0 := by rw [map_natCast]; exact h
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] LL).injective] at h'
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h')
  have := inv_smul_liftQ_mem_Z1D LA' (((l : ℕ) : O) ^ r) (by rw [he]; exact pow_ne_zero _ hl)
    hI' c'.1 c'.2
  rwa [he] at this

end GlobalTheory.DivLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumAddTwoMulDifferentExponentLe
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_add_two_mul_card_inf_le_of_not_le {G : Type} [Group G] [Finite G] (H J : Subgroup G)
    (h : ¬ H ≤ J) : Nat.card ↥H + 2 * Nat.card ↥(H ⊓ J) ≤ 2 * Nat.card ↥H := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_left : H ⊓ J ≤ H)
  have hpos : 0 < Nat.card ↥(H ⊓ J) := Nat.card_pos
  have hposH : 0 < Nat.card ↥H := Nat.card_pos
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply h
    have he := Subgroup.eq_of_le_of_card_ge (inf_le_left : H ⊓ J ≤ H) (by rw [hk, mul_one])
    rw [← he]
    exact inf_le_right
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk2 : 2 ≤ k := by omega
  rw [hk]
  nlinarith

open Classical in

theorem ite_add_two_mul_card_inf_sub_one_le {G : Type} [Group G] [Finite G] (H J : Subgroup G) :
    (if H ≤ J then 0 else Nat.card ↥H) + 2 * (Nat.card ↥(H ⊓ J) - 1) ≤ 2 * (Nat.card ↥H - 1) := by
  have h1 : 0 < Nat.card ↥(H ⊓ J) := Nat.card_pos
  have h2 : Nat.card ↥(H ⊓ J) ≤ Nat.card ↥H := Subgroup.card_le_of_le inf_le_left
  split_ifs with h
  · omega
  · have := card_add_two_mul_card_inf_le_of_not_le H J h
    omega

theorem jumpSum_add_two_mul_differentExponent_fixedField_le (F L : Type) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L]
    [IsGalois F L] (J : Subgroup (L ≃ₐ[F] L)) :
    jumpSum (wild F L) ⊤ J + 2 * differentExponent ↥(IntermediateField.fixedField J) L ≤
      2 * differentExponent F L := by
  classical
  obtain ⟨N, hN⟩ := exists_lowerRamificationGroup_eq_bot F L
  have hcard : ∀ i : ℤ, Nat.card ↥(lowerRamificationGroup (↥(IntermediateField.fixedField J)) L i) =
      Nat.card ↥(lowerRamificationGroup F L i ⊓ J) := by
    intro i
    rw [← lowerRamificationGroup_map_fixedField J i,
      Subgroup.card_map_of_injective (AlgEquiv.restrictScalarsHom_injective F)]
  have hFbot : lowerRamificationGroup F L ((N + 1 : ℕ) : ℤ) = ⊥ := hN _ (by push_cast; omega)
  have hMbot : lowerRamificationGroup (↥(IntermediateField.fixedField J)) L ((N + 1 : ℕ) : ℤ) = ⊥ := by
    rw [← Subgroup.map_eq_bot_iff_of_injective _ (AlgEquiv.restrictScalarsHom_injective F),
      lowerRamificationGroup_map_fixedField, hFbot, bot_inf_eq]
  have hjs : jumpSum (wild F L) ⊤ J = ∑ t ∈ Finset.range N,
      (if lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ) ≤ J then 0
        else Nat.card ↥(lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ))) := by
    unfold jumpSum
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range N)]
    · refine Finset.sum_congr rfl fun t _ => ?_
      simp only [wild, top_inf_eq, Nat.cast_add, Nat.cast_one]
    · intro t ht
      rw [Function.mem_support] at ht
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h'
      apply ht
      simp only [wild, top_inf_eq]
      rw [hN _ (by omega)]
      simp
  rw [hjs, differentExponent_eq_sum_card_lowerRamificationGroup F L hFbot,
    differentExponent_eq_sum_card_lowerRamificationGroup _ L hMbot,
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [hcard]
  have hterm := Finset.sum_le_sum (s := Finset.range N) fun t _ =>
    ite_add_two_mul_card_inf_sub_one_le (lowerRamificationGroup F L ((t + 1 : ℕ) : ℤ)) J
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hterm
  have h0 : Nat.card ↥(lowerRamificationGroup F L ((0 : ℕ) : ℤ) ⊓ J) - 1 ≤
      Nat.card ↥(lowerRamificationGroup F L ((0 : ℕ) : ℤ)) - 1 :=
    Nat.sub_le_sub_right (Subgroup.card_le_of_le inf_le_left) 1
  rw [mul_add, mul_add]
  omega

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_comap_injective :
    ∀ (G G' : Type) [Group G] [Group G'] (j : G' →* G) (R : ℕ → Subgroup G) (B : Subgroup G), Function.Injective j →
      jumpSum (fun t => (R t).comap j) ⊤ (B.comap j) = jumpSum R j.range B := by
  intro G G' _ _ j R B hj
  unfold jumpSum
  apply finsum_congr
  intro t
  have h1 : (⊤ ⊓ (R t).comap j ≤ B.comap j) ↔ (j.range ⊓ R t ≤ B) := by
    rw [top_inf_eq]
    constructor
    · rintro h x ⟨⟨y, rfl⟩, hy⟩
      exact h (show y ∈ (R t).comap j from hy)
    · intro h y hy
      exact h ⟨⟨y, rfl⟩, hy⟩
  have h2 : Nat.card ↥(⊤ ⊓ (R t).comap j) = Nat.card ↥(j.range ⊓ R t) := by
    rw [top_inf_eq, ← Subgroup.map_comap_eq, Subgroup.card_map_of_injective hj]
  rw [h2]
  by_cases h : j.range ⊓ R t ≤ B
  · rw [if_pos (h1.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (h1.mp h')), if_neg h]

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumLeAdd
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_support_subset {G : Type} [Group G] (R : ℕ → Subgroup G) (A B : Subgroup G) (hR : Antitone R)
    (m : ℕ) (hm : R m = ⊥) :
    Function.support (fun t : ℕ => by classical exact if A ⊓ R t ≤ B then 0 else Nat.card ↥(A ⊓ R t)) ⊆
      ↑(Finset.range m) := by
  classical
  intro t ht
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  push_neg at h
  apply ht
  have h1 : R t = ⊥ := le_bot_iff.mp (hm ▸ hR h)
  simp [h1]

theorem jumpSum_le_add : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R →
    (∃ m, R m = ⊥) → B ≤ A → jumpSum R A C ≤ jumpSum R A B + jumpSum R B C := by
  intro G _ R A B C hR ⟨m, hm⟩ hBA
  classical
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A C hR m hm),
    finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R A B hR m hm),
    finsum_eq_sum_of_support_subset _ (jumpSum_support_subset R B C hR m hm),
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  by_cases hC : A ⊓ R t ≤ C
  · simp [hC]
  · by_cases hB : A ⊓ R t ≤ B
    · have heq : B ⊓ R t = A ⊓ R t :=
        le_antisymm (inf_le_inf_right _ hBA) (le_inf hB inf_le_right)
      have hC' : ¬ B ⊓ R t ≤ C := by rw [heq]; exact hC
      simp [hC, hC', heq]
    · simp [hC, hB]

end GlobalTheory.PMon.Ram
end

