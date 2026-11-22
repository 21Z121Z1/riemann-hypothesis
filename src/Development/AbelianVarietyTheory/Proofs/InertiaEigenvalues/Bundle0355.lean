import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedMatrixUnitsOfLatticeBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0069
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0178
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0326
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0019
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedMatrixUnitsOfLatticeBasisStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobeniusFixed_matrix_units_of_lattice_basis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n), (∀ m, UnitM P (U m)) → ∀ (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → ∀ a : n → n → P.R.B, Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) → ∃ A : GL n P.R.B, (∀ i j, P.φB^[r] ((A : Matrix n n P.R.B) i j) = (A : Matrix n n P.R.B) i j) ∧ ∀ m : Fin r, ∃ W : GL n P.R.BdR, UnitM P W ∧ (A : Matrix n n P.R.B).map (ev P m) = (U m : Matrix n n P.R.BdR) * Matrix.diagonal (fun j => tz P (eps x y (m, j))) * (W : Matrix n n P.R.BdR) := by
  first | exact @GlobalTheory.PMon.Extract.extract | exact GlobalTheory.PMon.Extract.extract | (intros; apply GlobalTheory.PMon.Extract.extract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusFixedUnramifiedTowerBasisStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobeniusFixed_unramified_tower_basis : ∀ (l : ℕ) [Fact l.Prime] (r : ℕ) (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → LinearIndependent ℚ_[l] ω → (∀ c : ↥(MaximalUnramifiedExtension l), fr l r c = c → ∃ a : Fin r → ℚ_[l], c = ∑ k, a k • ω k) → ∀ (M : Type) [AddCommGroup M] [Module ↥(MaximalUnramifiedExtension l) M] [Module ℚ_[l] M] [IsScalarTower ℚ_[l] ↥(MaximalUnramifiedExtension l) M] (n : Type) [Fintype n] [DecidableEq n] (v : n × Fin r → M), LinearIndependent ℚ_[l] v → (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c, e • v c ∈ Submodule.span ℚ_[l] (Set.range v)) → ∃ a : n → M, (∀ j, a j ∈ Submodule.span ℚ_[l] (Set.range v)) ∧ LinearIndependent ℚ_[l] (fun jk : n × Fin r => ω jk.2 • a jk.1) ∧ Submodule.span ℚ_[l] (Set.range fun jk : n × Fin r => ω jk.2 • a jk.1) = Submodule.span ℚ_[l] (Set.range v) := by
  first | exact @GlobalTheory.exists_frFixed_tower_basis | exact GlobalTheory.exists_frFixed_tower_basis | (intros; apply GlobalTheory.exists_frFixed_tower_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSeriesAcrisUntilt
section
noncomputable section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer

theorem iter_tm {l : ℕ} [Fact l.Prime] (j : ℕ) (z : Fl l) :
    (⇑(GlobalTheory.MemLoc.phiA l))^[j] (algebraMap (Ainf l) (Acris l) (tm z)) =
      algebraMap (Ainf l) (Acris l) (tm (z ^ l ^ j)) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, (GlobalTheory.CrisMaps.phiA_extends l).alg]
    congr 1
    refine (GlobalTheory.RingIface.phiA_teich l (z ^ l ^ j)).trans ?_
    rw [← pow_mul, ← pow_succ]

theorem acris_cancel {l : ℕ} [Fact l.Prime] (k : ℕ) (u v : Acris l)
    (e : (l : Acris l) ^ k * u = (l : Acris l) ^ k * v) : u = v := by
  induction k with
  | zero => simpa using e
  | succ k ih =>
    apply ih
    rw [← sub_eq_zero]
    apply (GlobalTheory.MemLoc.acris_basic l).2.1
    linear_combination e

theorem series_acris : ∀ (l : ℕ) [Fact l.Prime] (h : ℕ) (x : Fl l), 2 ≤ h → ‖sh x‖ ≤ ‖(l : ℂ_[l])‖ → ∃ w : Acris l, (GlobalTheory.MemLoc.phiA l)^[h] w = (l : Acris l) * w ∧ ∀ (Θ : Acris l →+* ℂ_[l]), (∀ a, ‖Θ a‖ ≤ 1) → (∀ z : Fl l, Θ (algebraMap (Ainf l) (Acris l) (tm z)) = sh z) → ∀ j : ℕ, Θ ((GlobalTheory.MemLoc.phiA l)^[j] w) = lam h j x := by
  intro l _ h x h2 hx
  obtain ⟨-, -, -, hpw_comp, hpw_nat, -, -⟩ := GlobalTheory.T.tiltFrobeniusIntegerPower_laws l
  obtain ⟨c, hdvd, hc⟩ := GlobalTheory.T.acris_series_terms_mem_prime_pow l h x h2 hx
  haveI := (GlobalTheory.MemLoc.acris_basic l).1
  have hφl : ∀ (j : ℕ) (k : ℕ) (a : Acris l), (⇑(GlobalTheory.MemLoc.phiA l))^[j] ((l : Acris l) ^ k * a) =
      (l : Acris l) ^ k * (⇑(GlobalTheory.MemLoc.phiA l))^[j] a := by
    intro j k a
    rw [← RingHom.coe_pow, map_mul, map_pow, map_natCast]
  have hpwj : ∀ (n : ℤ) (j : ℕ), pw (n * h) x ^ l ^ j = pw (n * h + j) x := by
    intro n j
    rw [← hpw_nat, ← hpw_comp, add_comm]
  have shift : ∀ n : ℤ, (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n) = (l : Acris l) * c (n + 1) := by
    intro n
    apply acris_cancel (n.toNat + (n+1).toNat)
    have e1 := congrArg ((⇑(GlobalTheory.MemLoc.phiA l))^[h]) (hc n)
    rw [hφl, hφl, iter_tm, hpwj] at e1
    have e2 := hc (n + 1)
    have hh : (n + 1) * (h : ℤ) = n * h + h := by ring
    rw [hh] at e2
    calc (l : Acris l) ^ (n.toNat + (n+1).toNat) * (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n)
        = (l : Acris l) ^ (n+1).toNat * ((l : Acris l) ^ n.toNat * (⇑(GlobalTheory.MemLoc.phiA l))^[h] (c n)) := by ring
      _ = (l : Acris l) ^ (n+1).toNat * ((l : Acris l) ^ (-n).toNat *
            algebraMap (Ainf l) (Acris l) (tm (pw (n * h + h) x))) := by rw [e1]
      _ = (l : Acris l) ^ (n.toNat + 1) * ((l : Acris l) ^ (-(n+1)).toNat *
            algebraMap (Ainf l) (Acris l) (tm (pw (n * h + h) x))) := by
          rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
          congr 2
          omega
      _ = _ := by rw [← e2]; ring
  obtain ⟨w, hw, hsum⟩ := GlobalTheory.T.twoSided_shift_series_hasSum l (Acris l) (GlobalTheory.MemLoc.phiA l) h c hdvd shift
  refine ⟨w, hw, fun Θ hΘ hΘt j => ?_⟩
  have hs := hsum (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (fun a => hΘ _)
  have hl : (l : ℂ_[l]) ≠ 0 := GlobalTheory.RingBasics.p_ne_zero
  have hterm : ∀ n : ℤ, (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (c n) =
      (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x) := by
    intro n
    have e := congrArg (Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) (hc n)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_pow, hφl, hφl, iter_tm, hpwj, map_mul,
      map_mul, map_pow, map_pow, map_natCast, hΘt] at e
    rw [RingHom.comp_apply, RingHom.coe_pow]
    have hn : -n = ((-n).toNat : ℤ) - (n.toNat : ℤ) := by omega
    have ha : (l : ℂ_[l]) ^ n.toNat ≠ 0 := pow_ne_zero _ hl
    rw [hn, zpow_sub₀ hl, zpow_natCast, zpow_natCast]
    calc Θ ((⇑(GlobalTheory.MemLoc.phiA l))^[j] (c n))
        = ((l : ℂ_[l]) ^ n.toNat)⁻¹ * ((l : ℂ_[l]) ^ n.toNat * Θ ((⇑(GlobalTheory.MemLoc.phiA l))^[j] (c n))) := by
          rw [inv_mul_cancel_left₀ ha]
      _ = _ := by rw [e]; ring
  have hs' : HasSum (fun n : ℤ => (l : ℂ_[l]) ^ (-n) * sh (pw (n * h + j) x))
      ((Θ.comp (GlobalTheory.MemLoc.phiA l ^ j)) w) := by
    simpa only [hterm] using hs
  rw [lam, hs'.tsum_eq, RingHom.comp_apply, RingHom.coe_pow]

end GlobalTheory.PSer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisEqEmbeddingsOCModPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.EmbTwo

theorem range_eq_of_normal {F E L : Type} [Field F] [Field E] [Algebra F E] [Normal F E] [Field L]
    [Algebra F L] (φ ψ : E →ₐ[F] L) : φ.fieldRange = ψ.fieldRange := by
  let e : E ≃ₐ[F] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal F ψ.fieldRange := Normal.of_algEquiv e
  have h := AlgHom.fieldRange_of_normal (E := ψ.fieldRange) (φ.comp e.symm.toAlgHom)
  rw [← h]
  ext x
  simp only [AlgHom.mem_fieldRange, AlgHom.comp_apply]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨e y, by simp⟩
  · rintro ⟨y, rfl⟩; exact ⟨_, rfl⟩

variable {l : ℕ} [Fact l.Prime]

theorem exists_approx (y : OC l) : ∃ (z : OC l) (w : OC l), (∃ z' : Om l, (z : ℂ_[l]) = (z' : ℂ_[l])) ∧
    y = z + (l : OC l) * w := by
  have hl : 0 < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  obtain ⟨z', hz'⟩ := (UniformSpace.Completion.denseRange_coe (α := Om l)).exists_dist_lt (y : ℂ_[l]) hl
  set w : ℂ_[l] := (y : ℂ_[l]) - (z' : ℂ_[l]) with hw
  have hw1 : ‖w‖ < ‖((l : ℕ) : ℂ_[l])‖ := by rw [hw, ← dist_eq_norm]; exact hz'
  have hwO : w ∈ 𝓞_ℂ_[l] := (GlobalTheory.RingBasics.mem_OC _).2 (hw1.le.trans GlobalTheory.RingBasics.norm_p_lt.le)
  have hzO : (z' : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
    have : (z' : ℂ_[l]) = (y : ℂ_[l]) - w := by rw [hw]; ring
    rw [this]; exact Subring.sub_mem _ y.2 hwO
  have hq : w / ((l : ℕ) : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
    rw [GlobalTheory.RingBasics.mem_OC, norm_div, div_le_one hl]; exact hw1.le
  refine ⟨⟨_, hzO⟩, ⟨_, hq⟩, ⟨z', rfl⟩, Subtype.ext ?_⟩
  push_cast
  rw [mul_div_cancel₀ _ GlobalTheory.RingBasics.p_ne_zero, hw]; ring

end GlobalTheory.EmbTwo

open GlobalTheory.EmbTwo in

theorem GlobalTheory.EmbTwo.exists_gal_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (D : Type) [CommRing D] [IsDomain D] (θ₁ θ₂ : OC l →+* D), Function.Injective θ₁ → Function.Injective θ₂ → (∀ r : ↥(OL K), θ₁ (intToOC K r) = θ₂ (intToOC K r)) → ∃ g : ↥(GK K), (∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO (g : GQ l) y)) ∧ ∀ y : OC l, ((l : ℕ) : D) ∣ θ₂ y - θ₁ (Per.σO (g : GQ l) y) := by
  intro l _ K D _ _ θ₁ θ₂ h1 h2 hK
  let F := FractionRing D
  have i1 : Function.Injective ((algebraMap D F).comp θ₁) := (IsFractionRing.injective D F).comp h1
  have i2 : Function.Injective ((algebraMap D F).comp θ₂) := (IsFractionRing.injective D F).comp h2
  let τ₁ : ℂ_[l] →+* F := IsFractionRing.lift i1
  let τ₂ : ℂ_[l] →+* F := IsFractionRing.lift i2
  let σ₁ : Om l →+* F := τ₁.comp (algebraMap (Om l) ℂ_[l])
  let σ₂ : Om l →+* F := τ₂.comp (algebraMap (Om l) ℂ_[l])
  have hτ₁ : ∀ y : OC l, τ₁ (y : ℂ_[l]) = algebraMap D F (θ₁ y) := fun y =>
    IsFractionRing.lift_algebraMap (K := ℂ_[l]) i1 y
  have hτ₂ : ∀ y : OC l, τ₂ (y : ℂ_[l]) = algebraMap D F (θ₂ y) := fun y =>
    IsFractionRing.lift_algebraMap (K := ℂ_[l]) i2 y

  have hO : ∀ r : ↥(OL K), σ₁ ((r : ↥K.1) : Om l) = σ₂ ((r : ↥K.1) : Om l) := fun r => by
    change τ₁ ((intToOC K r : OC l) : ℂ_[l]) = τ₂ ((intToOC K r : OC l) : ℂ_[l])
    rw [hτ₁, hτ₂, hK]

  have hKK : ∀ x : ↥K.1, σ₁ (x : Om l) = σ₂ (x : Om l) := fun x => by
    have ha : IsAlgebraic ℤ_[l] x :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥K.1).2 (Algebra.IsAlgebraic.isAlgebraic x)
    obtain ⟨y, hy0, hy⟩ := ha.exists_integral_multiple
    let r : ↥(OL K) := ⟨y • x, hy⟩
    let s : ↥(OL K) := algebraMap ℤ_[l] ↥(OL K) y
    have hrs : ((r : ↥K.1) : Om l) = ((s : ↥K.1) : Om l) * (x : Om l) := by
      change ((y • x : ↥K.1) : Om l) = _
      rw [Algebra.smul_def]; rfl
    have hs0 : ((s : ↥K.1) : Om l) ≠ 0 := by
      intro h0
      apply hy0
      have : (s : ↥K.1) = 0 := Subtype.ext h0
      have h3 : algebraMap ℤ_[l] ↥K.1 y = 0 := this
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1, _root_.map_eq_zero] at h3
      exact (IsFractionRing.injective ℤ_[l] ℚ_[l]) (h3.trans (map_zero _).symm)
    have e1 := hO r
    rw [hrs, map_mul, map_mul, hO s] at e1
    exact mul_left_cancel₀ ((map_ne_zero σ₂).2 hs0) e1
  letI : Algebra ↥K.1 F := (σ₁.comp (algebraMap ↥K.1 (Om l))).toAlgebra
  let φ₁ : Om l →ₐ[↥K.1] F := { σ₁ with commutes' := fun _ => rfl }
  let φ₂ : Om l →ₐ[↥K.1] F := { σ₂ with commutes' := fun x => (hKK x).symm }
  have hR := range_eq_of_normal φ₁ φ₂
  let e₁ : Om l ≃ₐ[↥K.1] φ₁.fieldRange := AlgEquiv.ofInjectiveField φ₁
  have hmem : ∀ z, φ₂ z ∈ φ₁.fieldRange := fun z => hR ▸ ⟨z, rfl⟩
  let g₀ : Om l →ₐ[↥K.1] Om l := e₁.symm.toAlgHom.comp (φ₂.codRestrict φ₁.fieldRange.toSubalgebra hmem)
  have hg₀ : ∀ z, σ₁ (g₀ z) = σ₂ z := fun z => by
    have := congrArg Subtype.val (e₁.apply_symm_apply ⟨φ₂ z, hmem z⟩)
    exact this
  let g₁ : Om l ≃ₐ[↥K.1] Om l := AlgEquiv.ofBijective g₀ (Algebra.IsAlgebraic.algHom_bijective g₀)
  let g : GQ l := g₁.restrictScalars ℚ_[l]
  have hgK : g ∈ GK K := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact g₀.commutes ⟨x, hx⟩
  have hg : ∀ z : Om l, σ₁ (g z) = σ₂ z := hg₀
  have c1 : ∀ y : OC l, (∃ z : Om l, (y : ℂ_[l]) = (z : ℂ_[l])) → θ₂ y = θ₁ (Per.σO g y) := by
    rintro y ⟨z, hz⟩
    apply IsFractionRing.injective D F
    rw [← hτ₁, ← hτ₂]
    have e2 : ((Per.σO g y : OC l) : ℂ_[l]) = ((g z : Om l) : ℂ_[l]) := by
      refine (GlobalTheory.RingIface.sigO_coe l g y).trans ?_
      rw [hz, GlobalTheory.RingBasics.σC_coe]
    rw [e2, hz]
    exact (hg z).symm
  refine ⟨⟨g, hgK⟩, c1, fun y => ?_⟩
  obtain ⟨z, w, hz, rfl⟩ := exists_approx y
  refine ⟨θ₂ w - θ₁ (Per.σO g w), ?_⟩
  have := c1 z hz
  simp only [map_add, map_mul, map_natCast]
  rw [this]; ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDisc
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSer

variable (l : ℕ) {W : Type} [CommRing W] (ρ : ℝ≥0)

theorem isUnit_l : IsUnit (l : (PreDisc l (0 : W) 1)⟦X⟧) := by
  rw [← map_natCast (C : PreDisc l (0 : W) 1 →+* (PreDisc l (0 : W) 1)⟦X⟧)]
  refine IsUnit.map _ ?_
  rw [← map_natCast (algebraMap W (PreDisc l (0 : W) 1))]
  exact IsLocalization.Away.algebraMap_isUnit _

def phi : PreDisc l (X : W⟦X⟧) ρ →+* (PreDisc l (0 : W) 1)⟦X⟧ :=
  IsLocalization.Away.lift (l : W⟦X⟧) (g := PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1))) (by
    rw [map_natCast]; exact isUnit_l l)

theorem phi_alg (s : W⟦X⟧) :
    phi l ρ (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) s) = PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1)) s :=
  IsLocalization.Away.lift_eq _ _ s

theorem phi_inv :
    phi l ρ (IsLocalization.Away.invSelf (l : W⟦X⟧)) = C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) := by
  have h := congrArg (phi l ρ) (IsLocalization.Away.mul_invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧))
  rw [map_mul, phi_alg, map_natCast, map_one] at h
  have h2 : (l : (PreDisc l (0 : W) 1)⟦X⟧) * C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) = 1 := by
    rw [← map_natCast (C : PreDisc l (0 : W) 1 →+* (PreDisc l (0 : W) 1)⟦X⟧), ← map_mul,
      ← map_natCast (algebraMap W (PreDisc l (0 : W) 1)), IsLocalization.Away.mul_invSelf, map_one]
  exact (isUnit_l l).mul_left_cancel (h.trans h2.symm)

def aPre (n : ℕ) : PreDisc l (X : W⟦X⟧) ρ →+ PreDisc l (0 : W) 1 :=
  (coeff n : (PreDisc l (0 : W) 1)⟦X⟧ →ₗ[PreDisc l (0 : W) 1] PreDisc l (0 : W) 1).toAddMonoidHom.comp
    (phi l ρ).toAddMonoidHom

theorem aPre_apply (n : ℕ) (y : PreDisc l (X : W⟦X⟧) ρ) : aPre l ρ n y = coeff n (phi l ρ y) := rfl

theorem aPre_mono (n a b c : ℕ) :
    aPre l ρ n (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) ((l : W⟦X⟧) ^ a * X ^ b) *
      IsLocalization.Away.invSelf (l : W⟦X⟧) ^ c) =
    if n = b then algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
      IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c else 0 := by
  rw [aPre_apply, map_mul, phi_alg, map_pow, phi_inv]
  have e : PowerSeries.map (algebraMap W (PreDisc l (0 : W) 1)) ((l : W⟦X⟧) ^ a * X ^ b) *
      C (IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W)) ^ c =
      C (algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
        IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c) * X ^ b := by
    simp only [map_mul, map_pow, map_natCast, map_X]; ring
  rw [e, coeff_C_mul_X_pow]

theorem norm_W_mono (hl : 0 < l) (a c : ℕ) :
    ‖algebraMap W (PreDisc l (0 : W) 1) ((l : W) ^ a) *
      IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c‖ ≤ (l : ℝ) ^ c / (l : ℝ) ^ a := by
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  exact gauge_le l (0 : W) 1 (by positivity) (Submodule.subset_span ⟨a, 0, c, by field_simp; simp, by simp⟩)

theorem norm_aPre_le (hl : 0 < l) (hρ : ρ ≤ 1) (y : PreDisc l (X : W⟦X⟧) ρ) (n : ℕ) :
    ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖ := by
  suffices h : ∀ r : ℝ, 0 < r → y ∈ ball l (X : W⟦X⟧) ρ r → ∀ n, ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ r from
    le_of_forall_gt_imp_ge_of_dense fun r hr =>
      h r ((norm_nonneg y).trans_lt hr) (mem_ball_of_gauge_lt l _ ρ hr) n
  have hρ' : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  have hadd : ∀ (r : ℝ) (n : ℕ) (z w : PreDisc l (0 : W) 1), ‖z‖ * (ρ : ℝ) ^ n ≤ r → ‖w‖ * (ρ : ℝ) ^ n ≤ r →
      ‖z + w‖ * (ρ : ℝ) ^ n ≤ r := fun r n z w hz hw =>
    (mul_le_mul_of_nonneg_right (gauge_add_le_max l (0 : W) 1 z w) (by positivity)).trans
      (by rw [max_mul_of_nonneg _ _ (by positivity)]; exact max_le hz hw)
  intro r hr hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, c, h1, rfl⟩ := hx
    intro n
    rw [aPre_mono]
    split_ifs with hn
    · subst hn
      calc _ ≤ (l : ℝ) ^ c / (l : ℝ) ^ a * (ρ : ℝ) ^ n :=
            mul_le_mul_of_nonneg_right (norm_W_mono l hl a c) (by positivity)
        _ ≤ r := by rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; exact h1
    · rw [norm_zero, zero_mul]; exact hr.le
  | zero => intro n; rw [map_zero, norm_zero, zero_mul]; exact hr.le
  | add x y _ _ hx hy => intro n; rw [map_add]; exact hadd r n _ _ (hx n) (hy n)
  | smul s x _ hx =>
    intro n
    rw [aPre_apply, Algebra.smul_def, map_mul, phi_alg, coeff_mul]
    refine Finset.sum_induction _ (fun z => ‖z‖ * (ρ : ℝ) ^ n ≤ r) (fun z w hz hw => hadd r n z w hz hw)
      (by rw [norm_zero, zero_mul]; exact hr.le) (fun p hp => ?_)
    have hp2 : p.2 ≤ n := by have := _root_.Finset.HasAntidiagonal.mem_antidiagonal.1 hp; omega
    rw [coeff_map]
    calc ‖algebraMap W (PreDisc l (0 : W) 1) (coeff p.1 s) * coeff p.2 (phi l ρ x)‖ * (ρ : ℝ) ^ n
        ≤ (1 * ‖coeff p.2 (phi l ρ x)‖) * (ρ : ℝ) ^ p.2 :=
          mul_le_mul ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_algebraMap_le (l := l) (u := (0 : W)) (ρ := 1) _) (norm_nonneg _)))
            (pow_le_pow_of_le_one (by positivity) hρ' hp2) (by positivity) (by positivity)
      _ ≤ r := by rw [one_mul]; exact hx p.2

theorem norm_X_pow_le (hρ0 : 0 < ρ) (m : ℕ) :
    ‖algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) (X ^ m)‖ ≤ (ρ : ℝ) ^ m := by
  have := norm_toDisc_pow_le (l := l) (u := (X : W⟦X⟧)) (ρ := ρ) m hρ0
  rwa [toDisc, RingHom.comp_apply, norm_ofPre] at this

theorem norm_le_of_aPre [Fact l.Prime] (hρ0 : 0 < ρ) (hρ : ρ < 1) (y : PreDisc l (X : W⟦X⟧) ρ) (r : ℝ)
    (hr : 0 ≤ r) (h : ∀ n, ‖aPre l ρ n y‖ * (ρ : ℝ) ^ n ≤ r) : ‖y‖ ≤ r := by
  have hl : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  have hy : y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  have hco : ∀ n, aPre l ρ n y =
      algebraMap W (PreDisc l (0 : W) 1) (coeff n s) * IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c := by
    intro n
    rw [hy, aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  have ht0 : 0 < t := hr.trans_lt ht
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos ht0 (pow_pos hl c)) (show (ρ : ℝ) < 1 by exact_mod_cast hρ)
  set hd : W⟦X⟧ := ∑ m ∈ Finset.range N, C (coeff m s) * X ^ m with hhd
  obtain ⟨s', hs'⟩ : (X : W⟦X⟧) ^ N ∣ s - hd := X_pow_dvd_iff.2 fun m hm => by
    simp [hhd, map_sub, coeff_C_mul_X_pow, map_sum, Finset.mem_range, hm]
  have hsplit : y = ∑ m ∈ Finset.range N, algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (C (coeff m s) * X ^ m) *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c +
      algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X ^ N * s') *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    rw [hy, ← Finset.sum_mul, ← map_sum, ← add_mul, ← map_add, ← hs', ← hhd, add_sub_cancel]
  rw [hsplit]
  refine (gauge_add_le_max l _ ρ _ _).trans (max_le ?_ ?_)
  · refine Finset.sum_induction _ (fun z => ‖z‖ ≤ t)
      (fun a b ha hb => (gauge_add_le_max l _ ρ a b).trans (max_le ha hb)) (by rw [norm_zero]; exact ht0.le)
      fun m _ => ?_
    have e : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (C (coeff m s) * X ^ m) *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c =
        preMap l (0 : W) 1 (X : W⟦X⟧) ρ C (algebraMap W _ (coeff m s) *
          IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c) *
          algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ) (X ^ m) := by
      rw [map_mul (preMap l (0 : W) 1 (X : W⟦X⟧) ρ C), map_pow (preMap l (0 : W) 1 (X : W⟦X⟧) ρ C), preMap_alg, preMap_inv,
        map_mul (algebraMap W⟦X⟧ (PreDisc l (X : W⟦X⟧) ρ))]; ring
    rw [e]
    have hpm := norm_preMap_le (l := l) (u := (0 : W)) (ρ := 1) (u' := (X : W⟦X⟧)) (ρ' := ρ) C (by simp)
      (algebraMap W _ (coeff m s) * IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c)
    refine (norm_mul_le _ _).trans ((mul_le_mul hpm (norm_X_pow_le l ρ hρ0 m) (norm_nonneg _)
      (norm_nonneg _)).trans ?_)
    rw [← hco]; exact (h m).trans ht.le
  · have e : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X ^ N * s') *
        IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c =
        s' • (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) ((l : W⟦X⟧) ^ 0 * X ^ N) *
          IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) := by
      rw [Algebra.smul_def, pow_zero, one_mul, mul_comm ((X : W⟦X⟧) ^ N) s', map_mul, mul_assoc]
    rw [e]
    refine gauge_le l _ ρ ht0 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, N, c, ?_, rfl⟩))
    rw [lt_div_iff₀ (by positivity)] at hN
    rw [pow_zero, mul_one, mul_comm]; exact hN.le

theorem continuous_aPre (hl : 0 < l) (hρ0 : 0 < ρ) (hρ : ρ ≤ 1) (n : ℕ) : Continuous (aPre l ρ n (W := W)) :=
  AddMonoidHomClass.continuous_of_bound _ ((ρ : ℝ) ^ n)⁻¹ fun y => by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; exact norm_aPre_le l ρ hl hρ y n

theorem norm_aPre_le_const (hl : 0 < l) (y : PreDisc l (X : W⟦X⟧) ρ) :
    ∃ C : ℝ, ∀ n, ‖aPre l ρ n y‖ ≤ C := by
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  have hy : y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
    rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
  refine ⟨(l : ℝ) ^ c / (l : ℝ) ^ 0, fun n => ?_⟩
  rw [hy, aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]
  refine (norm_mul_le _ _).trans ((mul_le_mul (norm_algebraMap_le (l := l) (u := (0 : W)) (ρ := 1) _)
    le_rfl (norm_nonneg _) zero_le_one).trans ?_)
  rw [one_mul]
  have := norm_W_mono (W := W) l hl 0 c
  rwa [pow_zero, map_one, one_mul] at this

theorem exists_coeff_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∃ a : ℕ → (bk.DS ρ →+ Disc l (0 : Wq l bk.a) 1),
      (∀ n x, a n (toDisc l (X : bk.S) ρ x) = toDisc l (0 : Wq l bk.a) 1 (coeff n x)) ∧
      (∀ n y, ‖a n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖) ∧
      (∀ y (r : ℝ), 0 ≤ r → (∀ n, ‖a n y‖ * (ρ : ℝ) ^ n ≤ r) → ‖y‖ ≤ r) ∧
      ∀ y, Filter.Tendsto (fun n => ‖a n y‖ * (ρ : ℝ) ^ n) Filter.atTop (nhds 0) := by
  intro l _ K bk ρ hρ0 hρ1
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hl' : (0 : ℝ) < l := Nat.cast_pos.2 hl
  have hc := fun n => continuous_aPre l (W := Wq l bk.a) ρ hl hρ0 hρ1.le n
  let A : ℕ → (bk.DS ρ →+ Disc l (0 : Wq l bk.a) 1) := fun n => (aPre l ρ n).completion (hc n)
  have hA : ∀ n y, A n (ofPre l (X : bk.S) ρ y) = ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n y) := fun n y =>
    AddMonoidHom.completion_coe _ _ y
  have hAc : ∀ n, Continuous (A n) := fun n => AddMonoidHom.continuous_completion _ _
  have h2 : ∀ n y, ‖A n y‖ * (ρ : ℝ) ^ n ≤ ‖y‖ := by
    intro n y
    refine (denseRange_ofPre l (X : bk.S) ρ).induction_on y
      (isClosed_le (((hAc n).norm).mul continuous_const) continuous_norm) fun y => ?_
    rw [hA, norm_ofPre, norm_ofPre]
    exact norm_aPre_le l ρ hl hρ1.le y n
  refine ⟨A, fun n x => ?_, h2, fun y r hr h => ?_, fun y => ?_⟩
  · change A n (ofPre l (X : bk.S) ρ (algebraMap _ _ x)) = ofPre l (0 : Wq l bk.a) 1 (algebraMap _ _ (coeff n x))
    rw [hA, aPre_apply, phi_alg, coeff_map]
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨z, hz⟩ := (denseRange_ofPre l (X : bk.S) ρ).exists_dist_lt y (half_pos hε)
    rw [dist_eq_norm] at hz
    have hz' : ‖z‖ ≤ r + ε / 2 := by
      refine norm_le_of_aPre l ρ hρ0 hρ1 z _ (by positivity) fun n => ?_
      rw [show ‖aPre l ρ n z‖ = ‖ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ from (norm_ofPre l (0 : Wq l bk.a) 1 _).symm, show ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z) =
        A n y - A n (y - ofPre l (X : bk.S) ρ z) by rw [map_sub, sub_sub_cancel, hA]]
      refine (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (by positivity)).trans ?_
      rw [add_mul]
      exact add_le_add (h n) ((h2 n _).trans hz.le)
    calc ‖y‖ ≤ ‖y - ofPre l (X : bk.S) ρ z‖ + ‖ofPre l (X : bk.S) ρ z‖ := norm_le_norm_sub_add _ _
      _ ≤ ε / 2 + (r + ε / 2) := add_le_add hz.le (by rw [norm_ofPre]; exact hz')
      _ = r + ε := by ring
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨z, hz⟩ := (denseRange_ofPre l (X : bk.S) ρ).exists_dist_lt y (half_pos hε)
    rw [dist_eq_norm] at hz
    obtain ⟨C, hC⟩ := norm_aPre_le_const l ρ hl z
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos (half_pos hε) (show (0 : ℝ) < C + 1 by linarith))
      (show (ρ : ℝ) < 1 by exact_mod_cast hρ1)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    have hρn : (ρ : ℝ) ^ n ≤ (ρ : ℝ) ^ N := pow_le_pow_of_le_one (by positivity) (by exact_mod_cast hρ1.le) hn
    rw [lt_div_iff₀ (by linarith)] at hN
    have e : A n y = A n (y - ofPre l (X : bk.S) ρ z) + ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z) := by
      rw [← hA, ← map_add, sub_add_cancel]
    rw [e]
    calc ‖A n (y - ofPre l (X : bk.S) ρ z) + ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ * (ρ : ℝ) ^ n
        ≤ (‖A n (y - ofPre l (X : bk.S) ρ z)‖ + ‖aPre l ρ n z‖) * (ρ : ℝ) ^ n := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [show ‖aPre l ρ n z‖ = ‖ofPre l (0 : Wq l bk.a) 1 (aPre l ρ n z)‖ from (norm_ofPre l (0 : Wq l bk.a) 1 _).symm]
          exact norm_add_le _ _
      _ = ‖A n (y - ofPre l (X : bk.S) ρ z)‖ * (ρ : ℝ) ^ n + ‖aPre l ρ n z‖ * (ρ : ℝ) ^ n := add_mul _ _ _
      _ ≤ ‖y - ofPre l (X : bk.S) ρ z‖ + C * (ρ : ℝ) ^ N :=
          add_le_add (h2 n _) (mul_le_mul (hC n) hρn (by positivity) hC0)
      _ < ε / 2 + ε / 2 := by
          refine add_lt_add_of_lt_of_le hz ?_
          nlinarith [pow_nonneg (show (0 : ℝ) ≤ ρ by positivity) N]
      _ = ε := add_halves ε

end GlobalTheory.BSP.DiscSer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeTateBasisOfCrystallineOverKsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodgeTateBasis_of_crystalline_over_Ks : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O), IsCrysOn S S.W.GKs T → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∀ m : ℕ, s ≤ m → (Jset S T).Finite ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K m) M (Jset S T) := by
  first | exact @GlobalTheory.HTBasisEx.exists_htBasis | exact GlobalTheory.HTBasisEx.exists_htBasis | (intros; apply GlobalTheory.HTBasisEx.exists_htBasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegerFixedFieldTraceEqSqMulOfAxStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integer_fixedField_trace_eq_sq_mul_of_ax : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p r : ℕ) (x : L) (a : (L ≃ₐ[F] L) → ℤ) (J : Subgroup (L ≃ₐ[F] L)) [J.Normal] (σ₁ : L ≃ₐ[F] L) (c : ℤ), (p : L) ≠ 0 → AxIn F L p → (∀ σ : L ≃ₐ[F] L, ∃ z ∈ 𝒪[L], σ x - x = (a σ : L) + (p : L) ^ r * z) → (∀ σ ∈ J, (p : ℤ) ^ r ∣ a σ) → c * (p : ℤ) ^ r = (J.index : ℤ) * a σ₁ → ∃ z : 𝒪[↥(IntermediateField.fixedField J)], Algebra.trace F ↥(IntermediateField.fixedField J) (z : ↥(IntermediateField.fixedField J)) = (p : F) ^ 2 * (c : F) := by
  first | exact @GlobalTheory.PMon.Ram.exists_integer_fixedField_trace_eq | exact GlobalTheory.PMon.Ram.exists_integer_fixedField_trace_eq | (intros; apply GlobalTheory.PMon.Ram.exists_integer_fixedField_trace_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRingSqZeroNilpotentAugmentedStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_sq_zero_nilpotent_augmented : ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (m : ℕ), 0 < m → ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (j : A →ₐ[O] B) (π : B →ₐ[O] A) (x y : B), (∀ a, π (j a) = a) ∧ (∀ b, π b = 0 → b ∈ Ideal.span {x, y}) ∧ π x = 0 ∧ π y = 0 ∧ x * x = 0 ∧ y ^ m = 0 ∧ ∀ f, x * y ^ (m - 1) * f = 0 → π f = 0 := by
  first | exact @GlobalTheory.SqZeroPow.exists_ring | exact GlobalTheory.SqZeroPow.exists_ring | (intros; apply GlobalTheory.SqZeroPow.exists_ring <;> assumption)
end

