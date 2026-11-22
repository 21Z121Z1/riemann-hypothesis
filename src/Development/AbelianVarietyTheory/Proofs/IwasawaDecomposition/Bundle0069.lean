import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002
import Formalism.UnipotentAdelicQuotients.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0035
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLift
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

variable {l : ℕ} [Fact l.Prime]

theorem exists_isTiltOf (c : Om l) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m) (hc : c ^ m = 1) :
    ∃ xb : Per.Fl l, IsTiltOf c m xb := by
  have hcC : (c : ℂ_[l]) ^ m = 1 := by
    have := congrArg (algebraMap (Om l) ℂ_[l]) hc
    rw [map_pow, map_one] at this
    exact this
  have hn : ‖(c : ℂ_[l])‖ = 1 := by
    have := congrArg norm hcC
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this
  let C : Per.OC l := ⟨(c : ℂ_[l]), (GlobalTheory.RingBasics.mem_OC _).2 hn.le⟩
  have hC : C ^ m = 1 := Subtype.ext (by simpa using hcC)
  have hcop : Nat.Coprime l m := ((Fact.out : l.Prime).coprime_iff_not_dvd).2 hl
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a * l ≡ 1 [MOD m] := by
    refine ⟨l ^ (Nat.totient m - 1), ?_⟩
    rw [← pow_succ, Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
    exact Nat.ModEq.pow_totient hcop
  let y : ℕ → Per.OC l := fun k => C ^ (a ^ k)
  have hy : ∀ k, y (k + 1) ^ l = y k := by
    intro k
    simp only [y]
    rw [← pow_mul]
    refine pow_eq_pow_of_modEq ?_ hC
    rw [pow_succ, mul_assoc]
    simpa using ha.mul_left (a ^ k)
  have hy0 : ∀ k, y k ^ (l ^ k) = C := by
    intro k
    induction k with
    | zero => simp [y]
    | succ k ih => rw [pow_succ', pow_mul, hy, ih]
  refine ⟨(⟨fun k => Ideal.Quotient.mk _ (y k), fun k => ?_⟩ : Perfection (ModP (Per.OC l) l) l), fun k => ⟨y k, ?_, ?_, rfl⟩⟩
  · rw [← map_pow, hy]
  · have := congrArg Subtype.val (hy0 k)
    simpa using this
  · simp only [y]
    rw [← pow_mul, mul_comm, pow_mul, hC, one_pow]

theorem IsTiltOf.pow_eq_one {c : Om l} {m : ℕ} {xb : Per.Fl l} (h : IsTiltOf c m xb) : xb ^ m = 1 := by
  refine Perfection.ext fun k => ?_
  obtain ⟨y, -, h2, h3⟩ := h k
  change PreTilt.coeff k (xb ^ m) = PreTilt.coeff k (1 : Per.Fl l)
  rw [map_pow, map_one, h3, ← map_pow, h2, map_one]

theorem IsTiltOf.untilt_eq {c : Om l} {m : ℕ} {xb : Per.Fl l} (h : IsTiltOf c m xb) :
    ((xb.untilt : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) := by
  obtain ⟨y0, h0, -, -⟩ := h 0
  rw [pow_zero, pow_one] at h0
  have : xb.untilt = y0 := by
    refine Perfection.teichmuller_spec (I := Ideal.span {((l : ℕ) : Per.OC l)}) fun n => ?_
    obtain ⟨y, h1, -, h3⟩ := h n
    refine ⟨y, h3.symm, ?_⟩
    have : y ^ l ^ n = y0 := Subtype.ext (by simpa [h0] using h1)
    rw [this]
  rw [this, h0]

theorem rootOfUnity_teichmuller : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → ∀ (c : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → (∃ xb : Per.Fl l, IsTiltOf c m xb) ∧ ∀ xb : Per.Fl l, IsTiltOf c m xb → xb ^ m = 1 ∧ ((xb.untilt : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) ∧ aDp l (Per.tm xb) = o c := by
  intro l _ o ho c m hm hl hc
  refine ⟨exists_isTiltOf c m hm hl hc, fun xb h => ⟨IsTiltOf.pow_eq_one h, IsTiltOf.untilt_eq h, ?_⟩⟩
  obtain ⟨-, -, hu, hθ, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have h1 : aDp l (Per.tm xb) ^ m = 1 := by
    rw [← map_pow, ← map_pow, IsTiltOf.pow_eq_one h, map_one, map_one]
  have h2 : o c ^ m = 1 := by rw [← map_pow, hc, map_one]
  have t1 : Per.θD l (aDp l (Per.tm xb)) = (c : ℂ_[l]) := by
    rw [hθ, WittVector.fontaineTheta_teichmuller, IsTiltOf.untilt_eq h]
  have t2 : Per.θD l (o c) = (c : ℂ_[l]) := ho.th c
  generalize aDp l (Per.tm xb) = y at h1 t1 ⊢
  have hc0 : (c : ℂ_[l]) ≠ 0 := by
    intro h0
    have := congrArg (Per.θD l) h2
    rw [map_pow, map_one, t2, h0, zero_pow hm.ne'] at this
    exact zero_ne_one this
  have hg := (Commute.all y (o c)).geom_sum₂_mul m
  rw [h1, h2, sub_self] at hg
  have hS : IsUnit (∑ i ∈ Finset.range m, y ^ i * o c ^ (m - 1 - i)) := by
    apply hu
    rw [map_sum]
    simp only [map_mul, map_pow, t1, t2]
    rw [geom_sum₂_self]
    exact mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hc0)
  exact sub_eq_zero.1 (hS.mul_right_eq_zero.1 hg)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqExpLocalChart
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.ExpBallSandwich

section Matrices
variable {n : Type} [Fintype n] [DecidableEq n]

noncomputable def sumAbs (M : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖

omit [DecidableEq n] in
theorem sumAbs_nonneg (M : Matrix n n ℂ) : 0 ≤ sumAbs M := by
  unfold sumAbs; positivity

omit [DecidableEq n] in
theorem sumAbs_add_le (A B : Matrix n n ℂ) : sumAbs (A + B) ≤ sumAbs A + sumAbs B := by
  unfold sumAbs
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_le _ _

omit [DecidableEq n] in
theorem sumAbs_neg (A : Matrix n n ℂ) : sumAbs (-A) = sumAbs A := by
  simp [sumAbs]

omit [DecidableEq n] in
theorem sumAbs_mul_le (A B : Matrix n n ℂ) : sumAbs (A * B) ≤ sumAbs A * sumAbs B := by
  first
  | exact @_root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le
  | exact _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le
  | (apply _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.EntrySumMulBound.entrySum_mul_le ..)

section Op
open scoped Matrix.Norms.Operator

theorem row_le_op (M : Matrix n n ℂ) (i : n) : ∑ j, ‖M i j‖ ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have := Finset.le_sup (f := fun i : n => ∑ j, ‖M i j‖₊) (Finset.mem_univ i)
  have h2 : ((∑ j, ‖M i j‖₊ : NNReal) : ℝ) ≤ _ := NNReal.coe_le_coe.2 this
  simpa using h2

theorem op_le_sumAbs (M : Matrix n n ℂ) : ‖M‖ ≤ sumAbs M := by
  rw [Matrix.linfty_opNorm_def]
  have : (Finset.univ.sup fun i : n => ∑ j, ‖M i j‖₊) ≤ ∑ i, ∑ j, ‖M i j‖₊ :=
    Finset.sup_le fun i _ => Finset.single_le_sum (f := fun l => ∑ j, ‖M l j‖₊)
          (fun l _ => by positivity) (Finset.mem_univ i)
  have h2 := NNReal.coe_le_coe.2 this
  simpa [sumAbs] using h2

theorem sumAbs_le_op (M : Matrix n n ℂ) : sumAbs M ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  unfold sumAbs
  calc _ ≤ ∑ _i : n, ‖M‖ := Finset.sum_le_sum fun i _ => row_le_op M i
    _ = _ := by simp

theorem exp_strict (η : ℝ) (hη : 0 < η) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ A B : Matrix n n ℂ,
    sumAbs A < ρ → sumAbs B < ρ →
    sumAbs (NormedSpace.exp A - NormedSpace.exp B - (A - B)) ≤ η * sumAbs (A - B) := by
  have h := (hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)).isLittleO
  have hc : 0 < η / ((Fintype.card n : ℝ) + 1) := by positivity
  have h2 := h.def hc
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨ρ, hρ, h3⟩ := h2
  refine ⟨ρ, hρ, fun A B hA hB => ?_⟩
  have h4 := @h3 (A, B) (by
    rw [Prod.dist_eq, dist_zero_right, dist_zero_right]
    exact max_lt ((op_le_sumAbs A).trans_lt hA) ((op_le_sumAbs B).trans_lt hB))
  simp only [ContinuousLinearMap.one_apply] at h4
  have h5 := op_le_sumAbs (A - B)
  have h6 := sumAbs_nonneg (A - B)
  calc _ ≤ _ := sumAbs_le_op _
    _ ≤ (Fintype.card n : ℝ) * (η / ((Fintype.card n : ℝ) + 1) * sumAbs (A - B)) := by
        refine mul_le_mul_of_nonneg_left (h4.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left h5 hc.le
    _ ≤ ((Fintype.card n : ℝ) + 1) * (η / ((Fintype.card n : ℝ) + 1) * sumAbs (A - B)) := by
        gcongr; linarith
    _ = _ := by field_simp

end Op

theorem defect_le (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ X Y Z : Matrix n n ℂ,
    sumAbs X < ρ → sumAbs Y < ρ → sumAbs Z < ρ →
    NormedSpace.exp Y = NormedSpace.exp X * NormedSpace.exp Z →
    sumAbs (Y - X - Z) ≤ η * sumAbs (Y - X) + 3 * η * sumAbs Z := by
  obtain ⟨ρ, hρ, h⟩ := exp_strict (n := n) η hη
  refine ⟨min ρ (η / 2), by positivity, fun X Y Z hX hY hZ he => ?_⟩
  rw [lt_min_iff] at hX hY hZ
  have h0 : sumAbs (0 : Matrix n n ℂ) < ρ := by simpa [sumAbs] using hρ
  have key : ∀ W : Matrix n n ℂ, sumAbs W < ρ →
      sumAbs (NormedSpace.exp W - 1 - W) ≤ η * sumAbs W ∧
      sumAbs (NormedSpace.exp W - 1) ≤ 2 * sumAbs W := by
    intro W hW
    have h1 := h W 0 hW h0
    rw [NormedSpace.exp_zero, sub_zero] at h1
    refine ⟨h1, ?_⟩
    have h2 := sumAbs_add_le (NormedSpace.exp W - 1 - W) W
    rw [sub_add_cancel] at h2
    have := sumAbs_nonneg W
    nlinarith
  have e : Y - X - Z = -(NormedSpace.exp Y - NormedSpace.exp X - (Y - X)) +
      ((NormedSpace.exp Z - 1 - Z) + (NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1)) := by
    rw [he]; noncomm_ring
  have a1 := h Y X hY.1 hX.1
  have a2 := (key Z hZ.1).1
  have a3 := (key Z hZ.1).2
  have a4 : sumAbs (NormedSpace.exp X - 1) ≤ η := by linarith [(key X hX.1).2, hX.2]
  have a5 : sumAbs ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1)) ≤ η * (2 * sumAbs Z) :=
    (sumAbs_mul_le _ _).trans (mul_le_mul a4 a3 (sumAbs_nonneg _) hη.le)
  rw [e]
  refine (sumAbs_add_le _ _).trans ?_
  rw [sumAbs_neg]
  have a6 := sumAbs_add_le (NormedSpace.exp Z - 1 - Z)
    ((NormedSpace.exp X - 1) * (NormedSpace.exp Z - 1))
  linarith

end Matrices

theorem mat_mul {P Q : ℕ} (g h : UpqT P Q) : UpqT.mat (g * h) = UpqT.mat g * UpqT.mat h := rfl

end GlobalTheory.ExpBallSandwich
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnit
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylTensorSubst

def drop {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ := ν s - Formalism.GradedWeylDivisibility.nuNext ν s

def antiOf {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) : ℕ := ∑ t ∈ Finset.Ici s, drop ν t

theorem antiOf_antitone {n : ℕ} (ν : Fin n → ℕ) : Antitone (antiOf ν) := fun s s' h =>
  Finset.sum_le_sum_of_subset (Finset.Ici_subset_Ici.2 h)

theorem antiOf_eq {n : ℕ} (ν : Fin n → ℕ) (s : Fin n) :
    antiOf ν s = drop ν s + Formalism.GradedWeylDivisibility.nuNext (antiOf ν) s := by
  unfold antiOf
  rw [Finset.Ici_eq_cons_Ioi, Finset.sum_cons]
  congr 1
  unfold Formalism.GradedWeylDivisibility.nuNext
  split_ifs with h
  · congr 1
    ext t
    simp only [Finset.mem_Ioi, Finset.mem_Ici, Fin.lt_def, Fin.le_iff_val_le_val]
    omega
  · have : Finset.Ioi s = ∅ := by
      ext t
      simp only [Finset.mem_Ioi, Finset.notMem_empty, iff_false, Fin.lt_def, not_lt]
      omega
    rw [this, Finset.sum_empty]

theorem hw_antiOf (R : Type) [CommRing R] {n : ℕ} (ν : Fin n → ℕ) :
    Formalism.GradedWeylDivisibility.hw R le_rfl (antiOf ν) = Formalism.GradedWeylDivisibility.hw R le_rfl ν := by
  unfold Formalism.GradedWeylDivisibility.hw
  refine Finset.prod_congr rfl fun s _ => ?_
  have := antiOf_eq ν s
  unfold drop at this
  congr 1
  omega

theorem weyl_eq_antiOf (R : Type) [CommRing R] (N : ℕ) (ν : Fin N → ℕ) :
    WeylLatticeDuality.weyl R N N le_rfl ν = Formalism.GradedWeylDivisibility.weyl R N N le_rfl (antiOf ν) := by
  show Formalism.GradedWeylDivisibility.weyl R N N le_rfl ν = _
  unfold Formalism.GradedWeylDivisibility.weyl
  rw [hw_antiOf]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

variable {p : ℕ} [Fact p.Prime] {N : ℕ}

def ev (h : MvPolynomial (Fin N × Fin N) ℤ) (y : Matrix (Fin N) (Fin N) ℂ_[p]) : ℂ_[p] :=
  eval (fun k : Fin N × Fin N => y k.1 k.2) (map (Int.castRingHom ℂ_[p]) h)

def Expands (ν : Fin N → ℕ) (φ : Matrix (Fin N) (Fin N) ℂ_[p] → ℂ_[p]) : Prop :=
  ∃ (m : ℕ) (o : Fin m → ℂ_[p]) (h : Fin m → MvPolynomial (Fin N × Fin N) ℤ),
    (∀ j, ‖o j‖ ≤ 1) ∧ (∀ j, h j ∈ WeylLatticeDuality.weyl ℤ N N le_rfl ν) ∧ φ = fun y => ∑ j, o j * ev (h j) y

theorem expands_zero (ν : Fin N → ℕ) : Expands (p := p) ν 0 :=
  ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0, by funext y; simp⟩

theorem expands_add {ν : Fin N → ℕ} {φ ψ : Matrix (Fin N) (Fin N) ℂ_[p] → ℂ_[p]} (hφ : Expands ν φ)
    (hψ : Expands ν ψ) : Expands ν (φ + ψ) := by
  obtain ⟨m, o, h, ho, hh, rfl⟩ := hφ
  obtain ⟨m', o', h', ho', hh', rfl⟩ := hψ
  refine ⟨m + m', Fin.append o o', Fin.append h h', fun j => ?_, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [ho, ho']
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp [hh, hh']
  · funext y
    simp [Fin.sum_univ_add]

theorem expands_smul {ν : Fin N → ℕ} {φ : Matrix (Fin N) (Fin N) ℂ_[p] → ℂ_[p]} (c : ℂ_[p]) (hc : ‖c‖ ≤ 1)
    (hφ : Expands ν φ) : Expands ν (fun y => c * φ y) := by
  obtain ⟨m, o, h, ho, hh, rfl⟩ := hφ
  refine ⟨m, fun j => c * o j, h, fun j => ?_, hh, ?_⟩
  · rw [norm_mul]; exact mul_le_one₀ hc (norm_nonneg _) (ho j)
  · funext y
    simp only [Finset.mul_sum, mul_assoc]

theorem expands_rowSubst (ν : Fin N → ℕ) (g : Matrix (Fin N) (Fin N) ℂ_[p]) (hg : ∀ a b, ‖g a b‖ ≤ 1)
    {f : MvPolynomial (Fin N × Fin N) ℤ} (hf : f ∈ WeylLatticeDuality.weyl ℤ N N le_rfl ν) :
    Expands ν (fun y => ev f (g * y)) := by
  let O := ball p
  let M : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hsub : O.subtype.comp (Int.castRingHom O) = Int.castRingHom ℂ_[p] := RingHom.ext_int _ _
  rw [weyl_eq_antiOf] at hf

  have h1 : map (Int.castRingHom O) f ∈ Formalism.GradedWeylDivisibility.weyl O N N le_rfl (antiOf ν) := by
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact Submodule.subset_span ⟨w, by
        beta_reduce
        rw [← Formalism.GradedWeylDivisibility.lclosedeq_hw_map (Int.castRingHom O), Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_zsmul]; exact zsmul_mem hx c
  have h2 := GlobalTheory.WeylRowAll.rowAct_mem_weyl_square O N (antiOf ν) (antiOf_antitone ν) M _ h1
  have e : (fun y => ev f (g * y)) =
      fun y => eval (fun k : Fin N × Fin N => y k.1 k.2) (map O.subtype (Formalism.GradedWeylDivisibility.rowAct O M (map (Int.castRingHom O) f))) := by
    funext y
    unfold ev
    have : (eval (fun k : Fin N × Fin N => (g * y) k.1 k.2)).comp (map (Int.castRingHom ℂ_[p])) =
        ((eval (fun k : Fin N × Fin N => y k.1 k.2)).comp (map O.subtype)).comp
          ((Formalism.GradedWeylDivisibility.rowAct O M (n := N)).toRingHom.comp (map (Int.castRingHom O))) := by
      refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun v => ?_
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply, M, O]
    exact RingHom.congr_fun this f
  rw [e]
  generalize Formalism.GradedWeylDivisibility.rowAct O M (map (Int.castRingHom O) f) = F at h2
  induction h2 using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨1, fun _ => 1, fun _ => Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ le_rfl (antiOf ν)), fun _ => by simp,
      fun _ => ?_, ?_⟩
    · rw [weyl_eq_antiOf]; exact Submodule.subset_span ⟨w, rfl⟩
    · funext y
      simp only [Finset.univ_unique, Finset.sum_singleton, one_mul, ev]
      rw [← Formalism.GradedWeylDivisibility.lclosedeq_hw_map (Int.castRingHom O), Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, map_map, hsub]
  | zero =>
    convert expands_zero (p := p) ν using 1
    funext z
    simp
  | add x y _ _ hx hy =>
    have := expands_add hx hy
    convert this using 1
    funext z
    simp
  | smul c x _ hx =>
    have := expands_smul (c : ℂ_[p]) c.2 hx
    convert this using 1
    funext z
    rw [smul_eq_C_mul, map_mul, map_C, eval_mul, eval_C]
    rfl

theorem inv_entry_le {g : Matrix (Fin N) (Fin N) ℂ_[p]} (hg : ∀ a b, ‖g a b‖ ≤ 1) (hd : ‖g.det‖ = 1) (a b : Fin N) :
    ‖g⁻¹ a b‖ ≤ 1 := by
  let O := ball p
  let Mo : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hM : g = Mo.map O.subtype := by ext a b; rfl
  have hadj : g.adjugate a b = ((Mo.adjugate a b : O) : ℂ_[p]) := by
    have h := RingHom.map_adjugate O.subtype Mo
    rw [hM]
    exact (congrFun (congrFun h a) b).symm
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', norm_mul, norm_inv, hd, inv_one, one_mul,
    hadj]
  exact (Mo.adjugate a b).2

variable {T : Type} [Fintype T]

theorem subst_mem {ν : T → Fin N → ℕ} (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (hc : ‖c‖ ≤ 1)
    (hg : ∀ τ a b, ‖g τ a b‖ ≤ 1) {F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]}
    (hF : F ∈ WeylLatticeDuality.DelW p T N ν) :
    (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  induction hF using AddSubgroup.closure_induction with
  | mem F hF =>
    obtain ⟨r, f, hr, hf, rfl⟩ := hF
    choose m o h ho hh he using fun τ => expands_rowSubst (ν τ) (g τ) (hg τ) (hf τ)
    have hb : ∀ x : ∀ τ, Fin (m τ), ‖c * r * ∏ τ, o τ (x τ)‖ ≤ 1 := fun x => by
      rw [norm_mul, norm_mul, norm_prod]
      exact mul_le_one₀ (mul_le_one₀ hc (norm_nonneg _) hr) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun τ _ => ho τ _)
    have hgen : ∀ x : ∀ τ, Fin (m τ), (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] => (c * r * ∏ τ, o τ (x τ)) *
        ∏ τ, eval (fun k : Fin N × Fin N => y τ k.1 k.2) (map (Int.castRingHom ℂ_[p]) (h τ (x τ)))) ∈
        WeylLatticeDuality.DelW p T N ν := fun x =>
      AddSubgroup.subset_closure ⟨c * r * ∏ τ, o τ (x τ), fun τ => h τ (x τ), hb x, fun τ => hh τ _, rfl⟩
    convert AddSubgroup.sum_mem _ (t := Finset.univ) (fun x _ => hgen x) using 1
    funext y
    rw [Finset.sum_apply]
    have e : ∀ τ, eval (fun k : Fin N × Fin N => (g τ * y τ) k.1 k.2) (map (Int.castRingHom ℂ_[p]) (f τ)) =
        ∑ j, o τ j * ev (h τ j) (y τ) := fun τ => congrFun (he τ) (y τ)
    simp only [e]
    classical
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib]
    simp only [ev]
    ring
  | zero =>
    convert zero_mem (WeylLatticeDuality.DelW p T N ν) using 1
    funext y; simp
  | add F G _ _ hF hG =>
    convert add_mem hF hG using 1
    funext y; simp [mul_add]
  | neg F _ hF =>
    convert neg_mem hF using 1
    funext y; simp

theorem subst_mem_iff (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) :
    ‖c‖ = 1 → (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) →
    ((fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν ↔ F ∈ WeylLatticeDuality.DelW p T N ν) := by
  intro hc hg hd
  constructor
  · intro h
    have hc0 : c ≠ 0 := fun h0 => by rw [h0, norm_zero] at hc; exact zero_ne_one hc
    have hu : ∀ τ, IsUnit (g τ).det := fun τ => isUnit_iff_ne_zero.2 fun h0 => by
      have := hd τ; rw [h0, norm_zero] at this; exact zero_ne_one this
    have := subst_mem (fun τ => (g τ)⁻¹) c⁻¹ (by rw [norm_inv, hc, inv_one])
      (fun τ => inv_entry_le (hg τ) (hd τ)) h
    convert this using 1
    funext y
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu _), Matrix.one_mul, inv_mul_cancel_left₀ hc0]
  · exact subst_mem g c hc.le hg

end GlobalTheory.WeylTensorSubst

end
end

