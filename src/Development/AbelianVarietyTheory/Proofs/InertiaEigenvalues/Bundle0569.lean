import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PotentiallySemistableCyclotomicSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0330
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0554
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0434
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0545
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0555
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0559

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasHodgeTateWeightFrameCharacterTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
noncomputable section

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def actM (g : GQ l) : P.R.BdR →* P.R.BdR := (P.actQdR g).toRingEquiv.toRingHom.toMonoidHom

theorem actM_apply (g : GQ l) (b : P.R.BdR) : actM P g b = P.actQdR g b := rfl

variable {P}

theorem unit_zpow_mem {u : P.R.BdRˣ} (h0 : (u : P.R.BdR) ∈ Fil P 0)
    (h1 : ((u⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0) (k : ℤ) : ((u ^ k : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0 := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one]; exact one_mem_Fil
  | succ k ih => rw [zpow_add_one, Units.val_mul]; exact Fil_mul_left ih h0
  | pred k ih => rw [zpow_sub_one, Units.val_mul]; exact Fil_mul_left ih h1

theorem unitM_scal {n : Type} [Fintype n] [DecidableEq n] {U : GL n P.R.BdR} (hU : UnitM P U) {v : P.R.BdRˣ}
    (h0 : (v : P.R.BdR) ∈ Fil P 0) (h1 : ((v⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0) :
    UnitM P (scalGL n v * U) := by
  constructor
  · intro i j
    rw [scalGL_mul_val, Matrix.smul_apply, smul_eq_mul]
    exact Fil_mul_left h0 (hU.1 i j)
  · intro i j
    rw [mul_inv_rev, ← map_inv, ← (scalGL_commute n v⁻¹ U⁻¹).eq, scalGL_mul_val, Matrix.smul_apply, smul_eq_mul]
    exact Fil_mul_left h1 (hU.2 i j)

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem frame_scal {n : Type} [Fintype n] [DecidableEq n] {K K' : FinExt l} (hK : K.1 ≤ K'.1)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (a : ℤ) (m : ℕ) (v : n → ℤ) (d : ℤ)
    (U : GL n P.R.BdR) (hU : ∀ g : ↥(GK K), matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ v j : ℚ_[l]ˣ) : ℚ_[l]))
    (u : P.R.BdRˣ) (hu : ∀ g : ↥(GK K'), P.actQdR (g : GQ l) (u : P.R.BdR) =
      kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) * algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-d) : ℚ_[l]ˣ) : ℚ_[l]) * u)
    (g : ↥(GK K')) :
    matD P (twist hK ρ χ a) m g *
        ((scalGL n (u ^ (-a)) * U : GL n P.R.BdR) : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      ((scalGL n (u ^ (-a)) * U : GL n P.R.BdR) : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (v j + d * a) : ℚ_[l]ˣ) : ℚ_[l]) := by
  set F : P.R.BdRˣ := Units.map (kd P).toMonoidHom (Units.map (fr l m).toMonoidHom (χ g)) with hFdef
  set Q : P.R.BdRˣ := Units.map (algebraMap ℚ_[l] P.R.BdR).toMonoidHom (P.χQ (g : GQ l)) with hQdef
  have hF : ∀ k : ℤ, ((F ^ k : P.R.BdRˣ) : P.R.BdR) = kd P (fr l m ((χ g ^ k : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l))) := by
    intro k
    have : F ^ k = Units.map (kd P).toMonoidHom (Units.map (fr l m).toMonoidHom (χ g ^ k)) := by
      simp only [hFdef, map_zpow]
    rw [this]; rfl
  have hQ : ∀ k : ℤ, ((Q ^ k : P.R.BdRˣ) : P.R.BdR) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ k : ℚ_[l]ˣ) : ℚ_[l]) := by
    intro k
    have : Q ^ k = Units.map (algebraMap ℚ_[l] P.R.BdR).toMonoidHom (P.χQ (g : GQ l) ^ k) := by
      simp only [hQdef, map_zpow]
    rw [this]; rfl
  have hu' : Units.map (actM P (g : GQ l)) u = F * Q ^ (-d) * u := by
    apply Units.ext
    rw [Units.coe_map, actM_apply, hu g, Units.val_mul, Units.val_mul, hQ]
    have := hF 1
    rw [zpow_one, zpow_one] at this
    rw [this]
  have hs : P.actQdR (g : GQ l) ((u ^ (-a) : P.R.BdRˣ) : P.R.BdR) = (((F * Q ^ (-d) * u) ^ (-a) : P.R.BdRˣ) : P.R.BdR) := by
    rw [← hu', ← map_zpow, Units.coe_map, actM_apply]
  have hmat : matD P (twist hK ρ χ a) m g =
      ((F ^ a : P.R.BdRˣ) : P.R.BdR) • matD P ρ m ⟨g, GK_le hK g.2⟩ := by
    ext i j
    simp only [matD, twist_val, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hF]
  have hmap : ∀ (s : P.R.BdR) (M : Matrix n n P.R.BdR),
      (s • M).map (P.actQdR (g : GQ l)) = P.actQdR (g : GQ l) s • M.map (P.actQdR (g : GQ l)) := by
    intro s M
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hdiag : (Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (v j + d * a) : ℚ_[l]ˣ) : ℚ_[l])) =
      ((Q ^ (d * a) : P.R.BdRˣ) : P.R.BdR) • Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ v j : ℚ_[l]ˣ) : ℚ_[l]) := by
    rw [hQ, ← Matrix.diagonal_smul]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, zpow_add, Units.val_mul, map_mul, mul_comm]
  rw [hmat, scalGL_mul_val, hmap, hs, hdiag, smul_mul_smul_comm, smul_mul_smul_comm]
  have hUg := hU ⟨g, GK_le hK g.2⟩
  rw [hUg, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [mul_zpow, mul_zpow, ← zpow_mul, neg_mul_neg, ← mul_assoc, ← mul_assoc, ← zpow_add, add_neg_cancel,
    zpow_zero, one_mul, mul_comm]

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon.Twist

set_option maxHeartbeats 1000000 in

theorem framed_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type)
    [Fintype n] [DecidableEq n] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r N : ℕ) (hr : 0 < r)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ),
    IsRat r ρ → Framed P ρ w →
    (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) →
    P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < r * N → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) →
    Framed P (GlobalTheory.PMon.Twist.twist hK ρ χ a)
      (fun (m : Fin (r * N)) j => w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then a else 0) := by
  intro l _ P AI T n _ _ K K' hK r N hr ρ w χ x a hρ hf hx hx1 hx2 hev m
  obtain ⟨-, -, hshift, hunit, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  have hgal : ∀ g : ↥(GK K'), P.actQdR (g : GQ l) (ev P m x) = kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) * ev P m x := by
    intro g
    rw [← ev_act, hx g, ← evHom_apply, map_mul, evHom_apply, evHom_apply, ev_kur]
  obtain ⟨e, he0, he1, hegal⟩ : ∃ e : P.R.BdR, e ∈ Fil P 0 ∧ e ∉ Fil P 1 ∧ ∀ g : ↥(GK K'),
      P.actQdR (g : GQ l) e = kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) *
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-(if (m : ℕ) = 0 then 1 else 0 : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * e := by
    by_cases hm : (m : ℕ) = 0
    · have e0 : ev P (m : ℕ) x = P.ιB x := by rw [hm]; rfl
      refine ⟨tz P (-1) * ev P m x, ?_, ?_, fun g => ?_⟩
      · have h := (hshift 1 (-1) (P.ιB x)).1 hx1
        rw [show (1 : ℤ) + -1 = 0 by norm_num] at h
        rwa [e0]
      · intro h
        rw [e0] at h
        apply hx2
        refine (hshift 2 (-1) (P.ιB x)).2 ?_
        rwa [show (2 : ℤ) + -1 = 1 by norm_num]
      · rw [if_pos hm, map_mul, GlobalTheory.PMon.Model.act_tz, hgal g]
        ring
    · have hj := hev m (Nat.pos_of_ne_zero hm) m.2
      refine ⟨ev P m x, hj.1, hj.2, fun g => ?_⟩
      rw [if_neg hm, hgal g, neg_zero, zpow_zero, Units.val_one, map_one, mul_one]
  obtain ⟨y, hy0, hey⟩ := hunit e he0 he1
  let u : P.R.BdRˣ := ⟨e, y, hey, by rw [mul_comm]; exact hey⟩
  have hu0 : (u : P.R.BdR) ∈ Fil P 0 := he0
  have hu1 : ((u⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0 := hy0
  obtain ⟨U, hUm, hU⟩ := hf ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩
  have hper : ∀ g, matD P ρ m g = matD P ρ ((m : ℕ) % r) g := fun g => by
    ext i j
    simp only [matD, Matrix.map_apply]
    rw [fr_mod (hρ.rat g i j)]
  refine ⟨scalGL n (u ^ (-a)) * U, unitM_scal hUm (unit_zpow_mem hu0 hu1 _)
    (by rw [← zpow_neg]; exact unit_zpow_mem hu0 hu1 _), fun g => ?_⟩
  have key := frame_scal hK ρ χ a m (w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩) (if (m : ℕ) = 0 then 1 else 0) U
    (fun g' => by rw [hper]; exact hU g') u hegal g
  have hda : (if (m : ℕ) = 0 then (1 : ℤ) else 0) * a = if (m : ℕ) = 0 then a else 0 := by
    split_ifs <;> simp
  simp only [hda] at key
  exact key

end GlobalTheory.PMon.Twist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponentsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.image_deRham_eq_eisenstein_pow_mul_of_components : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) [CompleteSpace K] (C : GlobalTheory.MemLoc.Core l) (η : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, ∃ r ∈ Rpi O K l e, (f τ : K⟦X⟧) = E K l e ^ η * r) → ∃ z : OD l O, iotaO O C (ϖ.iB t K f) = dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ η * z) := by
  first | exact @GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul | exact GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul | (intros; apply GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralElementsUnitFactorization
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace BridgeWittDvd

section Witt
variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]

theorem dvd_iff (x : WittVector p k) : (p : WittVector p k) ∣ x ↔ x.coeff 0 = 0 := by
  rw [← Ideal.mem_span_singleton]
  exact WittVector.mem_span_p_iff_coeff_zero_eq_zero x

theorem exists_limit (w : ℕ → WittVector p k) (h : ∀ n, (p : WittVector p k) ^ n ∣ w (n + 1) - w n) :
    ∃ z : WittVector p k, ∀ n, (p : WittVector p k) ^ n ∣ z - w n := by
  have hc : IsAdicComplete (Ideal.span {(p : WittVector p k)}) (WittVector p k) := inferInstance
  have key : ∀ (n : ℕ) (x y : WittVector p k),
      x ≡ y [SMOD (Ideal.span {(p : WittVector p k)} ^ n • ⊤ : Submodule (WittVector p k) (WittVector p k))] ↔
        (p : WittVector p k) ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have step : ∀ m d : ℕ, (p : WittVector p k) ^ m ∣ w (m + d) - w m := by
    intro m d
    induction d with
    | zero => simp
    | succ d ih =>
      have e : w (m + (d + 1)) - w m = (w (m + d + 1) - w (m + d)) + (w (m + d) - w m) := by
        rw [← add_assoc]; ring
      rw [e]
      exact dvd_add ((pow_dvd_pow _ (Nat.le_add_right m d)).trans (h _)) ih
  obtain ⟨z, hz⟩ := hc.toIsPrecomplete.prec (f := w) (fun {m n} hmn => by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [key, ← dvd_neg, neg_sub]
    exact step m d)
  refine ⟨z, fun n => ?_⟩
  rw [← dvd_neg, neg_sub]
  exact (key n _ _).1 (hz n)

theorem series_dvd (s : (WittVector p k)⟦X⟧)
    (h : PowerSeries.map (WittVector.constantCoeff (p := p) (R := k)) s = 0) :
    (p : (WittVector p k)⟦X⟧) ∣ s := by
  have hd : ∀ n, ∃ c, PowerSeries.coeff n s = (p : WittVector p k) * c := by
    intro n
    apply (dvd_iff _).2
    have := congrArg (PowerSeries.coeff n) h
    simpa using this
  choose c hc using hd
  refine ⟨PowerSeries.mk c, ?_⟩
  ext1 n
  rw [← map_natCast (PowerSeries.C (R := WittVector p k)) p, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc]

theorem decomp (w : WittVector p k) (h0 : w ≠ 0) :
    ∃ (n : ℕ) (v : WittVector p k), IsUnit v ∧ w = (p : WittVector p k) ^ n * v := by
  obtain ⟨n, v, e⟩ := WittVector.exists_eq_pow_p_mul' w h0
  exact ⟨n, v, v.isUnit, e⟩
end Witt

theorem perfect_frac (p : ℕ) [Fact p.Prime] (R F : Type) [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [CharP R p] [CharP F p] [PerfectRing R p] : PerfectRing F p := by
  refine PerfectRing.ofSurjective F p fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨a', rfl⟩ := (bijective_frobenius R p).2 a
  obtain ⟨b', rfl⟩ := (bijective_frobenius R p).2 b
  exact ⟨algebraMap R F a' / algebraMap R F b', by simp [frobenius_def, div_pow]⟩

end BridgeWittDvd

theorem Bridge.kisin_reduction_unit_at_uniformizer : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (K : Formalism.BasicNotions.Loc.FinExt l) (bk : GlobalTheory.BSP.BK K), (∀ w ∈ bk.OE, l.cast ∣ w → ∃ v ∈ bk.OE, w = l.cast * v) ∧ (∃ w ∈ bk.OE, HMul.hMul (α := Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (β := fun (x : bk.S) ↦ Formalism.BasicNotions.Loc.WCb l) bk.evW PowerSeries.X : Formalism.BasicNotions.Loc.WCb l) w = OfNat.ofNat 1) ∧ (∀ (s : bk.S), ¬l.cast ∣ s → ∃ w ∈ bk.OE, HMul.hMul (α := Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (β := fun (x : bk.S) ↦ Formalism.BasicNotions.Loc.WCb l) bk.evW s : Formalism.BasicNotions.Loc.WCb l) w = OfNat.ofNat 1) ∧ (∀ w ∈ bk.OE, w ≠ OfNat.ofNat 0 → ∃ (k : ℕ) (v : Formalism.BasicNotions.Loc.WCb l) (v' : Formalism.BasicNotions.Loc.WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = OfNat.ofNat 1 ∧ w = HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast k * v) ∧ (∀ (w : ℕ → Formalism.BasicNotions.Loc.WCb l), (∀ (n : ℕ), w n ∈ bk.OE) → (∀ (n : ℕ), HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast n ∣ w (n + OfNat.ofNat 1) - w n) → ∃ z ∈ bk.OE, ∀ (n : ℕ), HPow.hPow (α := Formalism.BasicNotions.Loc.WCb l) l.cast n ∣ z - w n) ∧ (∀ (g : ↥(Formalism.BasicNotions.Loc.GK K)), bk.FixFlat g → ∀ w ∈ bk.OE, DFunLike.coe (F := Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.WCb l) ↦ Formalism.BasicNotions.Loc.WCb l) (DFunLike.coe (F := Formalism.BasicNotions.Loc.GQ l →* Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.GQ l) ↦ Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (GlobalTheory.Prism.galW l) (g.val (p := fun (x : Formalism.BasicNotions.Loc.GQ l) ↦ x ∈ Formalism.BasicNotions.Loc.GK K)) : Formalism.BasicNotions.Loc.WCb l ≃ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) w = w) ∧ ∀ w ∈ bk.OE, Membership.mem (α := Formalism.BasicNotions.Loc.WCb l) bk.OE (DFunLike.coe (F := Formalism.BasicNotions.Loc.WCb l →ₐ[ℤ_[l]] Formalism.BasicNotions.Loc.WCb l) (β := fun (x : Formalism.BasicNotions.Loc.WCb l) ↦ Formalism.BasicNotions.Loc.WCb l) (Formalism.BasicNotions.Loc.frobW l) w : Formalism.BasicNotions.Loc.WCb l) := by
  intro l _ K bk
  haveI : PerfectRing (Cb l) l := BridgeWittDvd.perfect_frac l (OCb l) (Cb l)
  obtain ⟨ek, -, hek, hinj, -, -⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  obtain ⟨-, hS, hX, -, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨hsat, hcl, hφ, hgal, hunit⟩ := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  have hsatn : ∀ (n : ℕ) (v : WCb l), ((l : ℕ) : WCb l) ^ n * v ∈ bk.OE → v ∈ bk.OE := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, mul_assoc] at hv
      exact hsat v (ih _ hv)
  refine ⟨?_, hunit _ (hS _) hX, ?_, ?_, ?_, hgal, hφ⟩
  · rintro w hw ⟨v, rfl⟩
    exact ⟨v, hsat v hw, rfl⟩
  · intro s hs
    refine hunit _ (hS s) (WittVector.isUnit_of_coeff_zero_ne_zero _ fun h0 => hs ?_)
    apply BridgeWittDvd.series_dvd
    apply hinj
    rw [hek, map_zero]
    have e : (bk.evW s).coeff 0 = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := rfl
    rw [e] at h0
    exact (FaithfulSMul.algebraMap_injective (OCb l) (Cb l)) (h0.trans (map_zero _).symm)
  · intro w hw h0
    obtain ⟨n, v, hv, e⟩ := BridgeWittDvd.decomp (p := l) (k := Cb l) w h0
    have hvO : v ∈ bk.OE := hsatn n v (e ▸ hw)
    obtain ⟨v', hv', e'⟩ := hunit v hvO hv
    exact ⟨n, v, v', hvO, hv', e', e⟩
  · intro w hw h
    obtain ⟨z, hz⟩ := BridgeWittDvd.exists_limit (p := l) (k := Cb l) w h
    exact ⟨z, hcl z fun n => ⟨w n, hw n, hz n⟩, hz⟩

namespace GlobalTheory.OEDvr

variable {l : ℕ} [hl : Fact l.Prime]

theorem perfectRing_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  refine ⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) /
    algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)),
    ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p,
    frobeniusEquiv_symm_pow_p]

variable {K : FinExt l} (bk : BK K)

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w ∈ bk.OE, ((l : ℕ) : WCb l) ∣ w → ∃ v ∈ bk.OE, w = (l : WCb l) * v) ∧ (∃ w ∈ bk.OE, bk.evW X * w = 1) ∧ (∀ s : bk.S, ¬ (l : bk.S) ∣ s → ∃ w ∈ bk.OE, bk.evW s * w = 1) ∧ (∀ w ∈ bk.OE, w ≠ 0 → ∃ (k : ℕ) (v v' : WCb l), v ∈ bk.OE ∧ v' ∈ bk.OE ∧ v * v' = 1 ∧ w = (l : WCb l) ^ k * v) ∧ (∀ w : ℕ → WCb l, (∀ n, w n ∈ bk.OE) → (∀ n, (l : WCb l) ^ n ∣ w (n + 1) - w n) → ∃ z ∈ bk.OE, ∀ n, (l : WCb l) ^ n ∣ z - w n) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) :=
  Bridge.kisin_reduction_unit_at_uniformizer

end GlobalTheory.OEDvr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteDividedPowerSeriesSubringPrimeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_dividedPowerSeriesSubring_prime : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(Sd t K e))}) ↥(Sd t K e) := by
  first | exact @GlobalTheory.CrysPrism.isAdicComplete_Sd | exact GlobalTheory.CrysPrism.isAdicComplete_Sd | (intros; apply GlobalTheory.CrysPrism.isAdicComplete_Sd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteDividedTwoVariableSubringStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_dividedTwoVariableSubring : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), IsAdicComplete (Ideal.span {(l : ↥(PPd t K e))}) ↥(PPd t K e) := by
  first | exact @GlobalTheory.CrysPrism.PPd_isAdicComplete | exact GlobalTheory.CrysPrism.PPd_isAdicComplete | (intros; apply GlobalTheory.CrysPrism.PPd_isAdicComplete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeltaRingHomPowerSeriesOfRankOneImageStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDeltaRingHom_powerSeries_of_rank_one_image : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Type) [CommRing C] (DC : Delta l C) (J : Ideal C), (l : C) ∈ J → IsHausdorff J C → ∀ (σ : (Wq l a)⟦X⟧ →+* C) (e : ℕ), σ X ^ e ∈ J → DC.δ (σ X) = 0 → IsδMap (deltaS l a) DC σ := by
  first | exact @GlobalTheory.sdelta_of_rank_one | exact GlobalTheory.sdelta_of_rank_one | (intros; apply GlobalTheory.sdelta_of_rank_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

namespace GlobalTheory.Per.SESJumps

theorem isJumpV_iff_of_isSESLat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsSESLat (Qp := ℚ_[l]) ι π → IsCrys (P.PD K) T₀.ρ → IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), IsJumpV (P.PD K) T₁.ρ τ a ↔ IsJumpV (P.PD K) T₀.ρ τ a ∨ IsJumpV (P.PD K) T₂.ρ τ a := by
  intro l _ P AI hT K LL T₀ T₁ T₂ ι π hS _ h₁ _ τ a
  obtain ⟨hi, hs, -, hex, -⟩ := hS
  have hrk : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact (hex x).symm
  have hDR := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI hT K LL T₁.V T₁.ρ h₁).1
  exact ((GlobalTheory.T.de_rham_representation_tensor_comparison l P AI hT K LL T₀.V T₀.ρ T₁.V T₁.ρ T₂.V T₂.ρ ι.f π.f ι.equiv π.equiv
    hi hs hrk hDR).2.2 τ a).2.2

end GlobalTheory.Per.SESJumps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfFrobeniusDvdEisensteinPowMulStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_of_frobenius_dvd_eisenstein_pow_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ g : bk.S, ¬ (l : bk.S) ∣ g → ∀ M : ℕ, frobS l bk.a g ∣ bk.E ^ M * g → IsUnit g := by
  first | exact @GlobalTheory.LemZ.isUnit_of_frob_dvd | exact GlobalTheory.LemZ.isUnit_of_frob_dvd | (intros; apply GlobalTheory.LemZ.isUnit_of_frob_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacobiTrudiAlternantExpansionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobi_trudi_alternant_expansion : ∀ {A : Type} [CommRing A] (m d : ℕ) (h : ℕ → A),
    GlobalTheory.JSW.alternant A m (GlobalTheory.JSW.staircase m) *
                 ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, MvPolynomial.C (h (k j)) * MvPolynomial.X j ^ (k j) =
      ∑ l ∈ GlobalTheory.JSW.antiParts m d,
        MvPolynomial.C (GlobalTheory.JSW.jtDet m h l) * GlobalTheory.JSW.alternant A m (fun i => l i + GlobalTheory.JSW.staircase m i) := by
  first | exact @GlobalTheory.JSW.alternant_staircase_mul_antidiagonal | exact GlobalTheory.JSW.alternant_staircase_mul_antidiagonal | (intros; apply GlobalTheory.JSW.alternant_staircase_mul_antidiagonal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerTowerGaloisPreservesBreuilKisinModuleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerTowerGalois_preserves_breuilKisinModule : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → ∀ (g : Gl l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ (sQ l g) γ → ∀ v : ME P, v.1 ∈ P.M → ∃ v' : ME P, v'.1 ∈ P.M ∧ I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v' := by
  first | exact @GlobalTheory.GKinfStable.main | exact GlobalTheory.GKinfStable.main | (intros; apply GlobalTheory.GKinfStable.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LadicDescentStepToOE
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DescentStep

variable {l : ℕ} [Fact l.Prime]

theorem perfectRing_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a, rfl⟩ := (bijective_frobenius (OCb l) l).2 a
  obtain ⟨b, rfl⟩ := (bijective_frobenius (OCb l) l).2 b
  exact ⟨algebraMap _ _ a / algebraMap _ _ b, by simp [frobenius_def]⟩

theorem constantCoeff_frobW (w : WCb l) :
    WittVector.constantCoeff (p := l) (R := Cb l) (frobW l w) =
      WittVector.constantCoeff (p := l) (R := Cb l) w ^ l := by
  rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]
  change (WittVector.map (frobenius (Cb l) l) w).coeff 0 = _
  rw [WittVector.map_coeff, frobenius_def]

theorem constantCoeff_galW (g : GQ l) (w : WCb l) :
    WittVector.constantCoeff (p := l) (R := Cb l) (galW l g w) =
      autCb l (galTilt l g) (WittVector.constantCoeff (p := l) (R := Cb l) w) := by
  rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]
  change (WittVector.map (autCb l (galTilt l g)).toRingHom w).coeff 0 = _
  rw [WittVector.map_coeff]
  rfl

end GlobalTheory.BSP.DescentStep

open GlobalTheory.BSP.DescentStep in

theorem GlobalTheory.BSP.BK.descent_step : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (κ : Type) [Fintype κ] (x b : κ → WCb l) (c : κ → κ → WCb l), (∀ i j, c i j ∈ bk.OE) → (∀ j, b j ∈ bk.OE) → (∀ j, x j = ∑ i, frobW l (x i) * c i j + b j) → (∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x j) = x j) → ∃ v x' b' : κ → WCb l, (∀ j, v j ∈ bk.OE) ∧ (∀ j, b' j ∈ bk.OE) ∧ (∀ j, x j = v j + ((l : ℕ) : WCb l) * x' j) ∧ (∀ j, x' j = ∑ i, frobW l (x' i) * c i j + b' j) ∧ ∀ g : ↥(GK K), bk.FixFlat g → ∀ j, galW l (g : GQ l) (x' j) = x' j := by
  intro l _ K bk κ _ x b c hc hb hx hg
  haveI : PerfectRing (Cb l) l := perfectRing_Cb
  obtain ⟨sat, -, hφ, hfix, -⟩ := GlobalTheory.T.breuilKisin_OE_stability_properties l K bk
  set cc := WittVector.constantCoeff (p := l) (R := Cb l) with hcc
  have hmemc : ∀ w ∈ bk.OE, cc w ∈ bk.OE.map cc := fun w hw => Subring.mem_map.2 ⟨w, hw, rfl⟩
  have key : ∀ j, cc (x j) ∈ bk.OE.map cc := by
    refine GlobalTheory.T.tilt_invariant_mem_reduction_of_frobenius_equation l K bk κ (fun j => cc (x j)) ?_ ?_
    · intro g hgf j
      have h1 := congrArg cc (hg g hgf j)
      rw [constantCoeff_galW] at h1
      exact h1
    · intro T _ i₁ i₂ h12
      refine ⟨fun i j => i₁ (cc (c i j)), fun j => ?_⟩
      have e1 : ∀ i' : Cb l →+* T,
          i' (cc (x j)) = ∑ i, i' (cc (x i)) ^ l * i' (cc (c i j)) + i' (cc (b j)) := by
        intro i'
        conv_lhs => rw [hx j]
        rw [RingHom.map_add cc, map_sum cc, RingHom.map_add i', map_sum i']
        refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
        rw [RingHom.map_mul cc, RingHom.map_mul i', constantCoeff_frobW, RingHom.map_pow i']
      have e2 : ∀ i, i₂ (cc (c i j)) = i₁ (cc (c i j)) := fun i => (h12 _ (hmemc _ (hc i j))).symm
      rw [e1 i₁, e1 i₂, ← h12 _ (hmemc _ (hb j))]
      simp_rw [e2]
      rcases subsingleton_or_nontrivial T with hT | hT
      · exact Subsingleton.elim _ _
      · haveI : CharP T l := charP_of_injective_ringHom i₁.injective l
        simp_rw [sub_pow_char, sub_mul, Finset.sum_sub_distrib]
        ring
  choose v hv hvx using fun j => Subring.mem_map.1 (key j)
  have hker : ∀ j, x j - v j ∈ RingHom.ker cc := fun j => by
    rw [RingHom.mem_ker, map_sub, hvx j, sub_self]
  rw [hcc, WittVector.ker_constantCoeff] at hker
  choose x' hx' using fun j => Ideal.mem_span_singleton'.1 (hker j)

  set b' : κ → WCb l := fun j => x' j - ∑ i, frobW l (x' i) * c i j with hb'
  have hlb : ∀ j, ((l : ℕ) : WCb l) * b' j = b j - v j + ∑ i, frobW l (v i) * c i j := by
    intro j
    have h3 : ∀ i, ((l : ℕ) : WCb l) * (frobW l (x' i) * c i j) = (frobW l (x i) - frobW l (v i)) * c i j := by
      intro i
      rw [← map_sub, ← hx' i, map_mul, map_natCast]
      ring
    simp only [hb', mul_sub, Finset.mul_sum, h3]
    rw [mul_comm, hx' j]
    conv_lhs => rw [hx j]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hb'mem : ∀ j, b' j ∈ bk.OE := fun j => sat _ (by
    rw [hlb j]
    refine bk.OE.add_mem (bk.OE.sub_mem (hb j) (hv j)) (bk.OE.sum_mem fun i _ => bk.OE.mul_mem (hφ _ (hv i)) (hc i j)))
  refine ⟨v, x', b', hv, hb'mem, fun j => ?_, fun j => ?_, fun g hgf j => ?_⟩
  · linear_combination (hx' j).symm
  · simp only [hb']
    ring
  · have h5 : galW l (g : GQ l) (x' j * ((l : ℕ) : WCb l)) = x' j * ((l : ℕ) : WCb l) := by
      rw [hx' j, map_sub, hg g hgf j, hfix g hgf _ (hv j)]
    rw [map_mul, map_natCast] at h5
    have h4 : (galW l (g : GQ l) (x' j) - x' j) * ((l : ℕ) : WCb l) = 0 := by
      linear_combination h5
    exact sub_eq_zero.1 (WittVector.eq_zero_of_p_mul_eq_zero _ h4)
end
end

