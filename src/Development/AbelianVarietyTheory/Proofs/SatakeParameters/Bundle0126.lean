import Mathlib
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0005
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0002
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0115
import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.GramFrameComposition.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogPeriodCongruenceBdr
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.StLat

theorem exists_mul_eq_pow_pred {l : ℕ} [Fact l.Prime] {j m : ℕ} (hj : j ≠ 0) (hm : ¬ l ^ m ∣ j) :
    ∃ c : ℤ_[l], ((j : ℕ) : ℤ_[l]) * c = (l : ℤ_[l]) ^ (m - 1) := by
  first
  | exact @_root_.GlobalTheory.PolynomialNormBound.main
  | exact _root_.GlobalTheory.PolynomialNormBound.main
  | (apply _root_.GlobalTheory.PolynomialNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialNormBound.main ..)

theorem not_pow_dvd {l m j : ℕ} (h1 : j ≠ 0) (h2 : j < 2 * l ^ m) (h3 : j ≠ l ^ m) : ¬ l ^ m ∣ j := by
  rintro ⟨t, rfl⟩
  rcases t with _ | _ | t
  · simp at h1
  · simp at h3
  · have : l ^ m * 2 ≤ l ^ m * (t + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem log_trunc_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) → ∀ u : Per.BdRp l, IsLogP (beta ϖ) u →
  ∀ m : ℕ, 1 ≤ m → ∃ s ∈ Sg ϖ, ∃ e : Per.BdRp l, (e = 1 ∨ e = -1) ∧
    betaD ϖ ^ (2 * l ^ m) ∣ ((l : ℕ) : Per.BdRp l) * (((l : ℕ) : Per.BdRp l) ^ (m - 1) * u - s) -
      e * betaD ϖ ^ (l ^ m) := by
  intro l _ ϖ hker hfil u hu m hm
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set M := l ^ (m + 1) with hM
  set n := 2 * M with hn
  have hlpos : 0 < l := (Fact.out : l.Prime).pos
  have hMpos : 0 < M := pow_pos hlpos _
  set β := beta ϖ with hβ

  have hc : ∀ j : ℕ, ∃ c : ℤ_[l], (j ≠ 0 ∧ j < n ∧ j ≠ M) → ((j : ℕ) : ℤ_[l]) * c = (l : ℤ_[l]) ^ m := by
    intro j
    by_cases h : j ≠ 0 ∧ j < n ∧ j ≠ M
    · obtain ⟨c, hc⟩ := exists_mul_eq_pow_pred (l := l) (m := m + 1) h.1 (not_pow_dvd h.1 h.2.1 h.2.2)
      exact ⟨c, fun _ => by simpa using hc⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose c hc using hc
  let d : ℕ → ℤ_[l] := fun j => if j = M ∨ j = n then 0 else c j
  let a : ℕ → Per.AinfP l := fun k => (-1) ^ k * Per.zP l (d (k + 1)) * β ^ (k + 1)
  let S : Per.AinfP l := ∑ k ∈ Finset.range n, a k
  let e0 : Per.AinfP l := (-1) ^ (M - 1)
  let T : Per.AinfP l := (-1) ^ (n - 1) * ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
    ((n.factorial / (n - 1 + 1) : ℕ) : Per.AinfP l) * β ^ (n - 1 + 1)
  have hS : S ∈ Sa ϖ := by
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ?_ _) ?_) (Subalgebra.pow_mem _ ?_ _)
    · exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
    · first
      | exact Subalgebra.algebraMap_mem _ _
      | (rw [GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp]; exact Subalgebra.algebraMap_mem _ _)
    · exact Algebra.subset_adjoin (Set.mem_singleton _)

  have hterm : ∀ k ∈ Finset.range n, ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
      ((-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1)) =
      ((n.factorial : ℕ) : Per.AinfP l) * ((l : ℕ) : Per.AinfP l) * a k +
      (if k = M - 1 then ((n.factorial : ℕ) : Per.AinfP l) * ((-1) ^ k * β ^ (k + 1)) else 0) +
      (if k = n - 1 then (-1) ^ k * ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
        ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hdvd : (k + 1) ∣ n.factorial := Nat.dvd_factorial (by omega) (by omega)
    have hq : (((n.factorial / (k + 1) : ℕ) : Per.AinfP l)) * ((k + 1 : ℕ) : Per.AinfP l) =
        ((n.factorial : ℕ) : Per.AinfP l) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    by_cases h1 : k = M - 1
    · have h2 : ¬ k = n - 1 := by omega
      have hk1 : k + 1 = M := by omega
      have hda : d (k + 1) = 0 := by simp [d, hk1]
      rw [if_pos h1, if_neg h2]
      simp only [a, hda, map_zero, mul_zero, zero_mul, add_zero, zero_add]
      rw [← hq, hk1, hM, Nat.cast_pow]
      ring
    · by_cases h2 : k = n - 1
      · have hk1 : k + 1 = n := by omega
        have hda : d (k + 1) = 0 := by simp [d, hk1]
        rw [if_neg h1, if_pos h2]
        simp only [a, hda, map_zero, mul_zero, zero_mul, add_zero, zero_add]
        ring
      · have hne : ¬ (k + 1 = M ∨ k + 1 = n) := by omega
        have hda : d (k + 1) = c (k + 1) := by simp only [d, hne, if_false]
        have hck := hc (k + 1) ⟨by omega, by omega, by omega⟩
        have hck' := congrArg (Per.zP l) hck
        rw [map_mul, map_natCast, map_pow, map_natCast] at hck'
        rw [if_neg h1, if_neg h2]
        simp only [a, hda, add_zero]
        rw [← hq]
        linear_combination -(-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) *
          ((l : ℕ) : Per.AinfP l) * hck'
  have hsum : ((l : ℕ) : Per.AinfP l) ^ (m + 1) * ∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) =
      ((n.factorial : ℕ) : Per.AinfP l) * (((l : ℕ) : Per.AinfP l) * S + e0 * β ^ M) + T := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.mul_sum]
    have hm1 : M - 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
    have hn1 : n - 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
    rw [if_pos hm1, if_pos hn1, Nat.sub_add_cancel (by omega : 1 ≤ M)]
    simp only [S, e0, T]
    ring
  have hβI : β ∈ Per.kerP l := by rw [hker]; exact Ideal.mem_span_singleton_self _
  have hT : T ∈ Per.kerP l ^ n := by
    have : β ^ (n - 1 + 1) ∈ Per.kerP l ^ n := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact Ideal.pow_mem_pow hβI n
    exact Ideal.mul_mem_left _ _ this

  let s : Per.BdRp l := algebraMap (Per.AinfP l) (Per.BdRp l) S
  refine ⟨s, Subring.mem_map.2 ⟨S, hS, rfl⟩, algebraMap (Per.AinfP l) (Per.BdRp l) e0, ?_, ?_⟩
  · rcases neg_one_pow_eq_or (Per.AinfP l) (M - 1) with h | h
    · left; simp [e0, h]
    · right; simp [e0, h]
  · rw [← Ideal.mem_span_singleton, ← hfil]
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    have hev : ∀ x : Per.AinfP l, Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) =
        Ideal.Quotient.mk _ x := fun x => GlobalTheory.RingIface.ev_alg l n x
    let q : Per.AinfP l →+* Per.AinfP l ⧸ Per.kerP l ^ n := Ideal.Quotient.mk _
    have hunit : IsUnit ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) := by
      have := (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero).map q
      rwa [map_natCast] at this
    have hqT : q T = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hT
    have hs2 := congrArg q hsum
    simp only [map_add, map_mul, map_pow, map_natCast, hqT, add_zero] at hs2
    have hun := hu n
    apply hunit.mul_left_cancel
    rw [mul_zero]
    simp only [betaD, map_sub, map_mul, map_pow, map_natCast, s, hev]
    change ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) * (((l : ℕ) : _) * (((l : ℕ) : _) ^ m * Per.ev l n u - q S) -
      q e0 * q β ^ M) = 0
    change _ = q _ at hun
    linear_combination ((l : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) ^ (m + 1) * hun + hs2

end GlobalTheory.Pst.StLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialOfSplitPlaceStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitStab

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_eq (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = dotProduct (fun i => σ (x i)) (J.mulVec y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_smul_left (a : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (fun i => a * x i) y = σ a * Formalism.UG.hform σ J x y := by
  simp only [hform_eq, dotProduct, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (a : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x (fun i => a * y i) = a * Formalism.UG.hform σ J x y := by
  have : (fun i => a * y i) = a • y := rfl
  rw [hform_eq, hform_eq, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hform_mulVec {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT σ g * J * g = J) (x y : Fin n → A) :
    Formalism.UG.hform σ J (g.mulVec x) (g.mulVec y) = Formalism.UG.hform σ J x y := by
  have e : (fun i => σ (g.mulVec x i)) = Matrix.vecMul (fun i => σ (x i)) (Formalism.UG.cT σ g) := by
    funext i
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, mul_comm]
  rw [hform_eq, hform_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem stab_of_half (I : AddSubgroup A) (L : AddSubgroup (Fin n → A))
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, Formalism.UG.hform σ J z y ∈ I) {p : A}
    (hp : ∀ y ∈ L, (fun i => p * y i) ∈ L) (hq : ∀ y ∈ L, (fun i => σ p * y i) ∈ L)
    {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT σ g * J * g = J)
    (hs : ∀ i j, (p + σ p) * (g - 1) i j = (g - 1) i j)
    (h1 : ∀ y ∈ L, (fun i => p * g.mulVec y i) ∈ L)
    (h2 : ∀ y ∈ L, ∃ z ∈ L, (fun i => p * y i) = fun i => p * g.mulVec z i) (y : Fin n → A) :
    y ∈ L ↔ g.mulVec y ∈ L := by
  have fwd : ∀ y ∈ L, g.mulVec y ∈ L := by
    intro y hy
    have hc : (fun i => σ p * g.mulVec y i) ∈ L := by
      refine (hL _).2 fun z hz => ?_
      obtain ⟨z', hz', e⟩ := h2 z hz
      rw [hform_smul_right, ← hform_smul_left, e, hform_smul_left, hform_mulVec σ J hg, ← hform_smul_right]
      exact (hL _).1 (hq y hy) z' hz'
    have hs' : (p + σ p) • (g - 1) = g - 1 := Matrix.ext hs
    have e : (p + σ p) • (g.mulVec y - y) = g.mulVec y - y := by
      have := congrArg (fun m => Matrix.mulVec m y) hs'
      simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using this
    have e2 : g.mulVec y = y + ((fun i => p * g.mulVec y i) + (fun i => σ p * g.mulVec y i) -
        (fun i => p * y i) - fun i => σ p * y i) := by
      funext i
      have := congrFun e i
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this ⊢
      linear_combination -this
    rw [e2]
    exact add_mem hy (sub_mem (sub_mem (add_mem (h1 y hy) hc) (hp y hy)) (hq y hy))
  refine ⟨fwd y, fun hy => (hL _).2 fun z hz => ?_⟩
  rw [← hform_mulVec σ J hg]
  exact (hL _).1 hy _ (fwd z hz)

theorem supp_map {B : Type} [CommRing B] (φ : A →+* B) {f : A} {g : Matrix (Fin n) (Fin n) A}
    (hs : ∀ i j, f * (g - 1) i j = (g - 1) i j) (i j : Fin n) :
    φ f * (g.map φ - 1) i j = (g.map φ - 1) i j := by
  have e : (g.map φ - 1) i j = φ ((g - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, ← map_mul, hs]

end Alg

variable {D : D7}

theorem finPart_conj (x : Formalism.L2.Theta.AE D) :
    finPart D (cA D x) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem finMat_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) (finMat D.sp.cm.sig V.gram g) *
      JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram * finMat D.sp.cm.sig V.gram g =
      JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram := by
  have h : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * JR (AF D.host.F) V.gram * mt V g =
      JR (AF D.host.F) V.gram := g.2
  have h2 := congrArg (fun m => Matrix.map m (finPart D)) h
  simp only [Matrix.map_mul] at h2
  have e1 : (JR (AF D.host.F) V.gram).map (finPart D) = JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram := rfl
  have e2 : (mt V g).map (finPart D) = finMat D.sp.cm.sig V.gram g := rfl
  have e3 : (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g)).map (finPart D) =
      Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) (finMat D.sp.cm.sig V.gram g) := by
    ext i j
    exact finPart_conj _
  rwa [e1, e2, e3] at h2

theorem mem_ksph_of_split : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (g : GA D V), IsSplitIdem D e → Formalism.L2.Theta.SuppAt e V g → (∀ y ∈ LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec y a) ∈ LamHat V) → (∀ y ∈ LamHat V, ∃ z ∈ LamHat V, (fun a => finPart D e * y a) = fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec z a) → g ∈ KsphC V ∅ := by
  intro D V e g he hs h1 h2
  obtain ⟨hd, hm⟩ := GlobalTheory.LatDual.lamHat_selfDual_and_module V
  obtain ⟨i1, -, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
  have hp : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, i1])
  have hq : sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ← RingHom.map_mul, i1])
  refine ⟨?_, ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  · have h5 : infPart D (e + cA D e) = 0 := by
      rw [h4]
      exact TensorProduct.zero_tmul _ _
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h6 := congrArg (infPart D) (hs i j)
    rw [RingHom.map_mul, h5, zero_mul, Matrix.sub_apply, RingHom.map_sub] at h6
    have h7 : infPart D (mt V g i j) = infPart D ((1 : Matrix _ _ (Formalism.L2.Theta.AE D)) i j) :=
      sub_eq_zero.1 h6.symm
    refine h7.trans ?_
    rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact RingHom.map_one _
    · exact RingHom.map_zero _
  · refine stab_of_half (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig)
      (JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram) (intAE D) (LamHat V) hd (p := finPart D e)
      (hm _ hp) (hm _ hq) (finMat_unitary V g) (fun i j => ?_) h1 h2
    rw [← finPart_conj, ← RingHom.map_add]
    exact supp_map (finPart D) hs i j

end GlobalTheory.SplitStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRangeWittAlgClosureOfBoundedRingHom
section
open Filter Topology

noncomputable section

namespace GlobalTheory.TeichImage

variable {p : ℕ} [hp : Fact p.Prime]

theorem coprime_pow_sub_one {n : ℕ} (hn : 0 < n) : Nat.Coprime (p ^ n - 1) p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out]
  intro h
  have h1 : p ∣ p ^ n := dvd_pow_self p hn.ne'
  have h2 : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp.out.pos
  have h3 : p ∣ p ^ n - (p ^ n - 1) := Nat.dvd_sub h1 h
  rw [show p ^ n - (p ^ n - 1) = 1 by omega] at h3
  exact hp.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem mem_range_of_pow_eq {n : ℕ} (hn : 0 < n) {τ : ℂ_[p]} (hτ : τ ^ (p ^ n) = τ) :
    τ ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  by_cases h0 : τ = 0
  · exact ⟨0, by rw [h0, map_zero]⟩
  have hq : 2 ≤ p ^ n := le_trans hp.out.two_le (Nat.le_self_pow hn.ne' p)
  have h1 : τ ^ (p ^ n - 1) = 1 := by
    have : τ ^ (p ^ n - 1) * τ = 1 * τ := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega), hτ, one_mul]
    exact mul_right_cancel₀ h0 this
  exact Formalism.L2.G.Pend.root_mem_range p (by omega) (coprime_pow_sub_one hn) h1

theorem exists_lim {n : ℕ} (hn : 0 < n) (a : ℂ_[p])
    (ha : ∀ M : ℕ, ‖a ^ ((p ^ n) ^ (M + 1)) - a ^ ((p ^ n) ^ M)‖ ≤ ((p : ℝ)⁻¹) ^ (M + 1)) :
    ∃ τ ∈ Set.range (Formalism.L2.G.Pend.wToC p), ∀ N : ℕ, ‖a ^ ((p ^ n) ^ N) - τ‖ ≤ ((p : ℝ)⁻¹) ^ (N + 1) := by
  set r : ℝ := (p : ℝ)⁻¹ with hr
  have hr0 : 0 ≤ r := Formalism.L2.G.Pend.r_nonneg p
  have hr1 : r < 1 := Formalism.L2.G.Pend.r_lt_one p
  set u : ℕ → ℂ_[p] := fun M => a ^ ((p ^ n) ^ M) with hu
  have hcau : CauchySeq u := by
    refine cauchySeq_of_le_geometric r r hr1 fun m => ?_
    rw [dist_eq_norm, norm_sub_rev, ← pow_succ']
    exact ha m
  obtain ⟨τ, hτ⟩ := cauchySeq_tendsto_of_complete hcau
  have hball : ∀ N M : ℕ, N ≤ M → ‖u M - u N‖ ≤ r ^ (N + 1) := by
    intro N M hNM
    induction M, hNM using Nat.le_induction with
    | base => rw [sub_self, norm_zero]; exact pow_nonneg hr0 _
    | succ M hNM ih =>
      have : u (M + 1) - u N = (u (M + 1) - u M) + (u M - u N) := by ring
      rw [this]
      refine Formalism.L2.G.Pend.nadd p ((ha M).trans ?_) ih
      exact pow_le_pow_of_le_one hr0 hr1.le (by omega)
  have hlim : ∀ N : ℕ, ‖u N - τ‖ ≤ r ^ (N + 1) := by
    intro N
    have hmem : τ ∈ Metric.closedBall (u N) (r ^ (N + 1)) :=
      Metric.isClosed_closedBall.mem_of_tendsto hτ
        (eventually_atTop.2 ⟨N, fun M hM => by rw [Metric.mem_closedBall, dist_eq_norm]; exact hball N M hM⟩)
    rw [Metric.mem_closedBall, dist_eq_norm] at hmem
    rw [norm_sub_rev]; exact hmem
  have hsucc : ∀ M, u (M + 1) = u M ^ (p ^ n) := by
    intro M
    show a ^ ((p ^ n) ^ (M + 1)) = (a ^ ((p ^ n) ^ M)) ^ (p ^ n)
    rw [← pow_mul a ((p ^ n) ^ M) (p ^ n), ← pow_succ]
  have h1 : Tendsto (fun M => u (M + 1)) atTop (𝓝 τ) := hτ.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun M => u (M + 1)) atTop (𝓝 (τ ^ (p ^ n))) := by
    simp only [hsucc]; exact hτ.pow _
  have hfix : τ ^ (p ^ n) = τ := tendsto_nhds_unique h2 h1
  exact ⟨τ, mem_range_of_pow_eq hn hfix, hlim⟩

section Ring

variable {W : Type} [CommRing W] {n : ℕ}

theorem dvd_pow_iter (hW : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (N : ℕ) (x : W) :
    (p : W) ∣ x ^ ((p ^ n) ^ N) - x := by
  induction N with
  | zero => rw [pow_zero, pow_one, sub_self]; exact dvd_zero _
  | succ N ih =>
    have e : x ^ ((p ^ n) ^ (N + 1)) = (x ^ ((p ^ n) ^ N)) ^ (p ^ n) := by
      rw [← pow_mul x ((p ^ n) ^ N) (p ^ n), ← pow_succ]
    rw [e, show (x ^ ((p ^ n) ^ N)) ^ (p ^ n) - x =
      ((x ^ ((p ^ n) ^ N)) ^ (p ^ n) - x ^ ((p ^ n) ^ N)) + (x ^ ((p ^ n) ^ N) - x) by ring]
    exact dvd_add (hW _) ih

theorem dvd_pow_iter_succ (hn : 0 < n) (hW : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (M : ℕ) (x : W) :
    (p : W) ^ (M + 1) ∣ x ^ ((p ^ n) ^ (M + 1)) - x ^ ((p ^ n) ^ M) := by
  have h := dvd_sub_pow_of_dvd_sub (hW x) (n * M)
  have e1 : (x ^ (p ^ n)) ^ (p ^ (n * M)) = x ^ ((p ^ n) ^ (M + 1)) := by
    rw [← pow_mul, pow_succ, ← pow_mul, mul_comm]
  have e2 : x ^ (p ^ (n * M)) = x ^ ((p ^ n) ^ M) := by rw [← pow_mul]
  rw [e1, e2] at h
  exact (pow_dvd_pow _ (by have := Nat.le_mul_of_pos_left M hn; omega)).trans h

theorem norm_map_pow_mul (φ : W →+* ℂ_[p]) (hφ : ∀ x, ‖φ x‖ ≤ 1) (k : ℕ) (c : W) :
    ‖φ ((p : W) ^ k * c)‖ ≤ ((p : ℝ)⁻¹) ^ k := by
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Formalism.L2.G.Pend.norm_p_C]
  exact mul_le_of_le_one_right (pow_nonneg (Formalism.L2.G.Pend.r_nonneg p) k) (hφ c)

end Ring

end GlobalTheory.TeichImage

namespace GlobalTheory

theorem mem_range_wToC_of_pow_congr : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n →
    (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → IsAdicComplete (Ideal.span {(p : W)}) W →
    ∀ φ : W →+* ℂ_[p], (∀ x, ‖φ x‖ ≤ 1) → ∀ x, φ x ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  intro p _ n W _ hn hW _ φ hφ x
  have hr0 : 0 ≤ ((p : ℝ)⁻¹) := Formalism.L2.G.Pend.r_nonneg p
  have key : ∀ k : ℕ, ∀ x : W, ∃ w, ‖φ x - Formalism.L2.G.Pend.wToC p w‖ ≤ ((p : ℝ)⁻¹) ^ k := by
    intro k
    induction k with
    | zero => intro x; exact ⟨0, by rw [map_zero, sub_zero, pow_zero]; exact hφ x⟩
    | succ k ih =>
      intro x
      obtain ⟨τ, ⟨wτ, hwτ⟩, hτ⟩ := TeichImage.exists_lim hn (φ x) (fun M => by
        obtain ⟨c, hc⟩ := TeichImage.dvd_pow_iter_succ hn hW M x
        rw [← map_pow, ← map_pow, ← map_sub, hc]
        exact TeichImage.norm_map_pow_mul φ hφ (M + 1) c)
      obtain ⟨c, hc⟩ := TeichImage.dvd_pow_iter hW k x
      obtain ⟨w₁, hw₁⟩ := ih (-c)
      refine ⟨wτ + (p : Formalism.L2.G.Pend.WW p) * w₁, ?_⟩
      have hx : x = x ^ ((p ^ n) ^ k) + (p : W) * (-c) := by linear_combination -hc
      have e : φ x - Formalism.L2.G.Pend.wToC p (wτ + (p : Formalism.L2.G.Pend.WW p) * w₁) =
          (φ x ^ ((p ^ n) ^ k) - τ) + (p : ℂ_[p]) * (φ (-c) - Formalism.L2.G.Pend.wToC p w₁) := by
        conv_lhs => rw [hx]
        rw [map_add, map_add, map_mul, map_mul, map_pow, map_natCast, map_natCast, hwτ]
        ring
      rw [e]
      refine Formalism.L2.G.Pend.nadd p ((hτ k)) ?_
      rw [norm_mul, Formalism.L2.G.Pend.norm_p_C, pow_succ']
      exact mul_le_mul_of_nonneg_left hw₁ hr0
  apply Formalism.L2.G.Pend.mem_range_of_closure p
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (Formalism.L2.G.Pend.r_lt_one p)
  obtain ⟨w, hw⟩ := key N x
  exact ⟨_, ⟨w, rfl⟩, by rw [dist_eq_norm]; exact lt_of_le_of_lt hw hN⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesLinearCoordsEqFlatTaylorStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicSeries_linearCoords_eq_flatTaylor : ∀ (D : D7) (X : Fields) (s : Seam D X) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ ≃+* ℂ_[p]), Formalism.L2.KerInert.IotaExt lm ι → ∀ G : TaylorLogMetric.VC D N N' → ℂ, AnalyticOnNhd ℂ G Set.univ → TaylorLogMetric.CoefIn D G TaylorLogMetric.Qbar → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), TaylorLogMetric.atLin M (fun j => MvPowerSeries.X j) (TaylorLogMetric.pSer D lm G) = Formalism.L2.Th1.G.linSub (fun (i : DVar X.Tau N N') x => M (s.iT i.1, i.2) x) (MvPowerSeries.map (ι : ℂ →+* ℂ_[p]) (taylorMv fun z => G (s.flatV N N' z))) := by
  first | exact @GlobalTheory.FlatTaylorBridge.bridge | exact GlobalTheory.FlatTaylorBridge.bridge | (intros; apply GlobalTheory.FlatTaylorBridge.bridge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairEmbeddingsCongrModRootMinusD
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

noncomputable section

namespace GlobalTheory.DFrame

theorem congr_at_d : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ (ι : ℂ ≃+* ℂ_[p]) (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) → δ ^ 2 = -(p : D.host.E) → s δ = -δ → (∀ y, s (s y) = y) → (∀ (t : HH D) (y : D.host.E), TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) → (∀ (τ : D.what₂.Tau) (y : D.host.E), s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) → (‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ ≤ 1 ∧ ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) ≠ 0) ∧ ∀ (t : HH D) (y : 𝓞 D.host.E), ‖GlobalTheory.DFrame.rho D ι (false, t) (D.host.conj (y : D.host.E)) - GlobalTheory.DFrame.rho D ι (true, t) (y : D.host.E)‖ ≤ ‖ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ))‖ := by
  intro D p _ hpd ι cE s δ hcE hδ hsδ hss hpair hK
  set th : ℂ_[p] := ι (Complex.I * ((Real.sqrt D.host.d : ℝ) : ℂ)) with hth
  have hp0 : (0 : ℝ) < ‖(p : ℂ_[p])‖ := Formalism.L2.Th1.GD.norm_p_pos
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := Formalism.L2.Th1.GD.norm_p_lt_one
  have hsq : th ^ 2 = -(p : ℂ_[p]) := by
    rw [hth, ← map_pow, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), ← hpd]
    simp
  have hnorm2 : ‖th‖ ^ 2 = ‖(p : ℂ_[p])‖ := by
    rw [← norm_pow, hsq, norm_neg]
  have hnth : ‖th‖ = ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← hnorm2, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_contra h
    push_neg at h
    have : 1 < ‖th‖ ^ 2 := by nlinarith
    linarith
  · intro h
    rw [h, norm_zero] at hnorm2
    simp at hnorm2
    linarith
  · intro t y
    have hp2 : p ≠ 2 := by
      have h := hypOdd_of_hostHyp D.host.hyp
      obtain ⟨-, -, h1, h2, h3⟩ := h
      omega
    have hI := Formalism.L2.Th1.GD.InertiaRam_proof p hp2 D.host.E s δ (rho D ι (false, t)) hδ hsδ hss
      (fun y hy => hK _ y hy)
    let y' : 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv y
    have hy' : ((y' : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := rfl
    have h2 := hI.2.1 y'
    rw [hy'] at h2
    have htrue : rho D ι (true, t) (y : D.host.E) = rho D ι (false, t) (s (D.host.conj (y : D.host.E))) := by
      show ι (TaylorLogMetric.embT D (tauPl D (true, t)) (y : D.host.E)) = ι (TaylorLogMetric.embT D (tauPl D (false, t)) _)
      rw [hpair t, hcE]
    rw [htrue, hnth]
    exact h2

end GlobalTheory.DFrame
end
end

