import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0003
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ValuationBoundAdd

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.InClassOfExp
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset
open Formalism.InvariantFactorPaths.G7 (low_sum expSum exp_term sum_triangle eq_of_low)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff low_mul_sub)

section IntRLemmas

variable {ι K : Type} [Field K] {R : Subring K}

theorem IntR_mul {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) : IntR R (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact Subring.sum_mem _ fun x _ => R.mul_mem (hf _) (hg _)

theorem IntR_C {a : K} (ha : a ∈ R) : IntR R (MvPowerSeries.C a : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact R.zero_mem

theorem IntR_one : IntR R (1 : MvPowerSeries ι K) := by
  have := IntR_C (ι := ι) R.one_mem
  rwa [map_one] at this

theorem IntR_pow {f : MvPowerSeries ι K} (hf : IntR R f) (k : ℕ) : IntR R (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact IntR_one
  | succ k ih => rw [pow_succ]; exact IntR_mul ih hf

theorem IntR_prod {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K) (h : ∀ a ∈ s, IntR R (f a)) :
    IntR R (∏ a ∈ s, f a) :=
  Finset.prod_induction f (IntR R) (fun _ _ => IntR_mul) IntR_one h

theorem IntR_mono {R' : Subring K} (h : R ≤ R') {f : MvPowerSeries ι K} (hf : IntR R f) : IntR R' f :=
  fun n => h (hf n)

end IntRLemmas

section Exp

variable {ι K : Type} [Field K]

def expK (f : MvPowerSeries ι K) : MvPowerSeries ι K :=
  fun n => ∑ k ∈ range (n.degree + 1), ((k.factorial : K))⁻¹ * MvPowerSeries.coeff n (f ^ k)

theorem coeff_expK (f : MvPowerSeries ι K) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (expK f) = ∑ k ∈ range (n.degree + 1), ((k.factorial : K))⁻¹ * MvPowerSeries.coeff n (f ^ k) :=
  rfl

theorem low_expK_sub {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) (M : ℕ) :
    Low M (expK f - expSum f M) := by
  intro d hd
  rw [map_sub, coeff_expK, expSum, map_sum, sub_eq_zero]
  simp only [MvPowerSeries.coeff_C_mul]
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun k _ hk => ?_
  rw [low_pow ((low_one_iff _).2 hf) k d (by simp only [mem_range] at hk; omega), mul_zero]

theorem expK_add [CharZero K] {a b : MvPowerSeries ι K}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    expK (a + b) = expK a * expK b := by
  have hab : MvPowerSeries.constantCoeff (a + b) = 0 := by rw [map_add, ha, hb, add_zero]
  have la := (low_one_iff _).2 ha
  have lb := (low_one_iff _).2 hb
  refine eq_of_low fun M => ?_
  have h3 : Low M (expSum a M * expSum b M - expSum (a + b) M) := by
    have e : expSum (a + b) M = ∑ k ∈ range M, ∑ l ∈ range (M - k),
        (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l) := by
      unfold expSum
      rw [Finset.sum_congr rfl fun i _ => exp_term a b i]
      exact sum_triangle (fun k l => (MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l)) M
    rw [e]
    unfold expSum
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine low_sum _ _ _ fun k _ => ?_
    rw [Finset.mul_sum]
    intro d hd
    rw [map_sub, map_sum, map_sum, sub_eq_zero]
    symm
    refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le _ _)) fun l _ hl => ?_
    have hkl : Low (k + l) ((MvPowerSeries.C ((k.factorial : K)⁻¹) * a ^ k) *
          (MvPowerSeries.C ((l.factorial : K)⁻¹) * b ^ l)) := by
      simpa using low_mul (low_mul (low_zero (MvPowerSeries.C ((k.factorial : K)⁻¹))) (low_pow la k))
        (low_mul (low_zero (MvPowerSeries.C ((l.factorial : K)⁻¹))) (low_pow lb l))
    exact hkl d (by simp only [mem_range] at hl; omega)
  have e : expK (a + b) - expK a * expK b = (expK (a + b) - expSum (a + b) M) -
      ((expK a - expSum a M) * expK b + expSum a M * (expK b - expSum b M) +
        (expSum a M * expSum b M - expSum (a + b) M)) := by ring
  rw [e]
  refine low_sub (low_expK_sub hab M) (low_add (low_add ?_ ?_) h3)
  · simpa using low_mul (low_expK_sub ha M) (low_zero (expK b))
  · simpa using low_mul (low_zero (expSum a M)) (low_expK_sub hb M)

theorem IntR_expK {R : Subring K} {c : K} (hc : ∀ k : ℕ, c ^ k * ((k.factorial : K))⁻¹ ∈ R)
    {G : MvPowerSeries ι K} (hG : IntR R G) : IntR R (expK (MvPowerSeries.C c * G)) := by
  intro n
  rw [coeff_expK]
  refine Subring.sum_mem _ fun k _ => ?_
  rw [mul_pow, ← map_pow, MvPowerSeries.coeff_C_mul, ← mul_assoc, mul_comm _ (c ^ k)]
  exact R.mul_mem (hc k) (IntR_pow hG k n)

theorem low_prod_sub {Pl : Type} (s : Finset Pl) (a a' : Pl → MvPowerSeries ι K) (M : ℕ)
    (h : ∀ v ∈ s, Low M (a v - a' v)) : Low M (∏ v ∈ s, a v - ∏ v ∈ s, a' v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, sub_self]
    intro d _
    simp
  | insert v s hv ih =>
    rw [Finset.prod_insert hv, Finset.prod_insert hv]
    exact low_mul_sub (h v (Finset.mem_insert_self _ _)) (ih fun v' hv' => h v' (Finset.mem_insert_of_mem hv'))

theorem neg_pow_mem {R : Subring K} {c : K} (hc : ∀ k : ℕ, c ^ k * ((k.factorial : K))⁻¹ ∈ R) (k : ℕ) :
    (-c) ^ k * ((k.factorial : K))⁻¹ ∈ R := by
  rw [neg_pow, mul_assoc]
  exact R.mul_mem (R.pow_mem (R.neg_mem R.one_mem) k) (hc k)

theorem term_exp {pp c : K} (hpp : pp ≠ 0) (h : MvPowerSeries ι K) (i : ℕ) :
    MvPowerSeries.C ((i.factorial : K)⁻¹) * (-(MvPowerSeries.C (c / pp) * h)) ^ i =
      MvPowerSeries.C ((pp ^ i)⁻¹) * h ^ i * MvPowerSeries.C ((-c) ^ i * ((i.factorial : K))⁻¹) := by
  have e : -(MvPowerSeries.C (c / pp) * h) = MvPowerSeries.C (-c / pp) * h := by
    rw [neg_div, map_neg, neg_mul]
  rw [e, mul_pow, ← map_pow]
  have e2 : (MvPowerSeries.C ((-c / pp) ^ i) : MvPowerSeries ι K) =
      MvPowerSeries.C ((pp ^ i)⁻¹) * MvPowerSeries.C ((-c) ^ i) := by
    rw [← map_mul]
    congr 1
    rw [div_pow, div_eq_mul_inv, mul_comm]
  rw [e2, map_mul]
  ring

theorem inClass_of_exp {R : Subring K} {pp c : K} (hpp : pp ≠ 0) (hc : ∀ k : ℕ, c ^ k * ((k.factorial : K))⁻¹ ∈ R)
    (h : MvPowerSeries ι K) (h0 : MvPowerSeries.constantCoeff h = 0) {V : MvPowerSeries ι K} (hV : IntR R V) :
    ∃ g : ℕ → MvPowerSeries ι K, (∀ i, IntR R (g i)) ∧ ∀ n : ι →₀ ℕ,
      MvPowerSeries.coeff n (expK (-(MvPowerSeries.C (c / pp) * h)) * V) =
        ∑ i ∈ range (n.degree + 1), ((pp ^ i)⁻¹ * MvPowerSeries.coeff n (h ^ i * g i)) := by
  refine ⟨fun i => MvPowerSeries.C ((-c) ^ i * ((i.factorial : K))⁻¹) * V,
    fun i => IntR_mul (IntR_C (neg_pow_mem hc i)) hV, fun n => ?_⟩
  have hx : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (c / pp) * h)) = 0 := by
    rw [map_neg, map_mul, h0, mul_zero, neg_zero]
  have h1 : Low (n.degree + 1) ((expK (-(MvPowerSeries.C (c / pp) * h)) -
      expSum (-(MvPowerSeries.C (c / pp) * h)) (n.degree + 1)) * V) := by
    simpa using low_mul (low_expK_sub hx (n.degree + 1)) (low_zero V)
  have h2 := h1 n (by omega)
  rw [sub_mul, map_sub, sub_eq_zero] at h2
  rw [h2, expSum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [term_exp hpp, ← MvPowerSeries.coeff_C_mul]
  congr 1
  ring

theorem inProd_of_exp {Pl : Type} [Fintype Pl] [DecidableEq Pl] {R : Subring K} {pp c : K} (hpp : pp ≠ 0)
    (hc : ∀ k : ℕ, c ^ k * ((k.factorial : K))⁻¹ ∈ R)
    (h : Pl → MvPowerSeries ι K) (h0 : ∀ v, MvPowerSeries.constantCoeff (h v) = 0) {V : MvPowerSeries ι K}
    (hV : IntR R V) :
    ∃ g : (Pl → ℕ) → MvPowerSeries ι K, (∀ i, IntR R (g i)) ∧ ∀ α : ι →₀ ℕ,
      MvPowerSeries.coeff α ((∏ v, expK (-(MvPowerSeries.C (c / pp) * h v))) * V) =
        ∑ i ∈ Fintype.piFinset (fun _ : Pl => range (α.degree + 1)),
          MvPowerSeries.coeff α (MvPowerSeries.C (∏ v, (pp ^ i v)⁻¹) * (∏ v, h v ^ i v) * g i) := by
  refine ⟨fun i => MvPowerSeries.C (∏ v, ((-c) ^ i v * (((i v).factorial : K))⁻¹)) * V,
    fun i => IntR_mul (IntR_C (Subring.prod_mem _ fun v _ => neg_pow_mem hc (i v))) hV, fun α => ?_⟩
  have hx : ∀ v, MvPowerSeries.constantCoeff (-(MvPowerSeries.C (c / pp) * h v)) = 0 := fun v => by
    rw [map_neg, map_mul, h0, mul_zero, neg_zero]
  have h1 : Low (α.degree + 1) ((∏ v, expK (-(MvPowerSeries.C (c / pp) * h v)) -
      ∏ v, expSum (-(MvPowerSeries.C (c / pp) * h v)) (α.degree + 1)) * V) := by
    simpa using low_mul (low_prod_sub univ _ _ (α.degree + 1) fun v _ => low_expK_sub (hx v) (α.degree + 1))
      (low_zero V)
  have h2 := h1 α (by omega)
  rw [sub_mul, map_sub, sub_eq_zero] at h2
  rw [h2]
  unfold expSum
  rw [Finset.prod_univ_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Finset.prod_congr rfl fun v _ => term_exp hpp (h v) (i v), Finset.prod_mul_distrib,
    Finset.prod_mul_distrib]
  simp only [map_prod]
  ring

end Exp

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.InLatCSmulC
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

theorem inLatC_sum {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} {κ : Type*} (s : Finset κ) (f : κ → XspC (X.Pj j) Y.Kc)
    (h : ∀ k ∈ s, Y.inLatC j g L (f k)) : Y.inLatC j g L (∑ k ∈ s, f k) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h ⊢
  exact AddSubgroup.sum_mem _ h

theorem inLatC_smulC {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} (b : Y.Kc) (k : ℤ)
    (hb : b * (p : Y.Kc) ^ k ∈ Y.Oc) {y : XspC (X.Pj j) Y.Kc} (h : Y.inLatC j g L y) :
    Y.inLatC j (g - k) L (b • y) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h ⊢
  have hm := AddSubgroup.mem_map_of_mem (DistribMulAction.toAddMonoidHom (XspC (X.Pj j) Y.Kc) b) h
  rw [AddMonoidHom.map_closure] at hm
  refine AddSubgroup.closure_mono ?_ hm
  rintro _ ⟨_, ⟨a, ha, z, hz, rfl⟩, rfl⟩
  exact ⟨b * a, geC_mul_shift (Y := Y) k ha hb, z, hz, by simp [smul_smul]⟩

theorem inLatC_rep {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} {y' : XspC (X.Pj j) Y.Kc} (h : Y.inLatC j g L y') :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → Y.Kc) (z : κ → (X.Pj j).Xsp), (∀ k, Y.geC (a k) g) ∧
      (∀ k, z k ∈ (X.Pj j).HtupW L) ∧ y' = ∑ k, a k • MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (z k) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h
  induction h using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    exact ⟨Unit, inferInstance, fun _ => a, fun _ => z, fun _ => ha, fun _ => hz, by simp⟩
  | zero =>
    exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun k => k.elim, fun k => k.elim, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨κ1, i1, a1, z1, ha1, hz1, rfl⟩ := hx
    obtain ⟨κ2, i2, a2, z2, ha2, hz2, rfl⟩ := hy
    refine ⟨κ1 ⊕ κ2, inferInstance, Sum.elim a1 a2, Sum.elim z1 z2, ?_, ?_, ?_⟩
    · rintro (k | k)
      exacts [ha1 k, ha2 k]
    · rintro (k | k)
      exacts [hz1 k, hz2 k]
    · rw [Fintype.sum_sum_type]
      rfl
  | neg x _ hx =>
    obtain ⟨κ1, i1, a1, z1, ha1, hz1, rfl⟩ := hx
    refine ⟨κ1, i1, fun k => -a1 k, z1, fun k => geC_neg (Y := Y) (ha1 k), hz1, ?_⟩
    simp [neg_smul]

theorem descent {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} (y : (X.Pj j).Xsp)
    (h : Y.inLatC j g L (MvPolynomial.map (algebraMap X.G.Kf Y.Kc) y)) :
    y ∈ scale (X.vsc g) ((X.Pj j).HtupW L) := by
  classical
  obtain ⟨κ, _, a, z, ha, hz, hy⟩ := inLatC_rep Y h
  obtain ⟨c, hc, hyc⟩ := descent_core (K := X.G.Kf) (Kc := Y.Kc) (V := (X.Pj j).Xsp) (Vc := XspC (X.Pj j) Y.Kc)
    (MvPolynomial.map (algebraMap X.G.Kf Y.Kc)).toAddMonoidHom
    (by
      intro c v
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, MvPolynomial.smul_eq_C_mul, map_mul,
        MvPolynomial.map_C])
    (fun m => MvPolynomial.lcoeff X.G.Kf m) (fun m => MvPolynomial.lcoeff Y.Kc m)
    (by intro m v; simp [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_map])
    (by
      intro v hv
      ext m
      simpa [MvPolynomial.lcoeff_apply] using hv m)
    (RK X) (RK_val Y) (geCgrp Y g)
    (by
      intro r hr a ha
      exact geC_mul_Oc Y ha ((mem_RK_iff Y).mp hr))
    (Finset.univ : Finset κ).card Finset.univ rfl z a (fun k _ => ha k) y hy
  rw [hyc]
  refine Submodule.sum_mem _ fun k _ => ?_
  have h1 := vGeK_of_geC Y (c k) g (hc k (Finset.mem_univ k))
  unfold Sys.vGeK at h1
  rw [mem_scale_iff] at h1
  obtain ⟨o, ho, hok⟩ := h1
  obtain ⟨t, rfl⟩ := mem_intKF.mp ho
  rw [mem_scale_iff]
  refine ⟨t • z k, Submodule.smul_mem _ _ (hz k), ?_⟩
  rw [← hok, smul_eq_mul, mul_smul, algebraMap_smul]

theorem natInv_mem (m : ℕ) (hm : ¬ p ∣ m) : ((m : Y.Kc))⁻¹ ∈ Y.Oc := by
  have hk : ((m : kb p)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (kb p) p]
    exact hm

  have hu : IsUnit ((m : WW p)) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    have hc : WittVector.constantCoeff ((m : WW p)) = (m : kb p) := map_natCast _ m
    change WittVector.constantCoeff ((m : WW p)) ≠ 0
    rw [hc]
    exact hk
  obtain ⟨u, hu⟩ := hu
  have h1 : algebraMap (K0 p) Y.Kc (algebraMap (WW p) (K0 p) (↑u⁻¹ : WW p)) * (m : Y.Kc) = 1 := by
    rw [← map_natCast (algebraMap (K0 p) Y.Kc), ← map_natCast (algebraMap (WW p) (K0 p)), ← map_mul,
      ← map_mul, ← hu, Units.inv_mul, map_one, map_one]
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact Y.witt_mem_integers_Cp _

theorem wt_inv (N d : ℕ) (hpos : 0 < N) (hle : padicValNat p N ≤ d) :
    ((N : Y.Kc))⁻¹ * (p : Y.Kc) ^ ((d : ℕ) : ℤ) ∈ Y.Oc := by
  have hpp : p.Prime := Fact.out
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' p hpp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have he : e ≤ d := by
    have hv : padicValNat p (p ^ e * m) = e := by
      rw [padicValNat.mul (pow_ne_zero _ hpp.ne_zero) hm0, padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd hm, add_zero]
    omega
  have hp := pKc_ne (Y := Y)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  have key : ((p ^ e * m : ℕ) : Y.Kc)⁻¹ * (p : Y.Kc) ^ (((e + k : ℕ)) : ℤ) = ((m : Y.Kc))⁻¹ * (p : Y.Kc) ^ k := by
    rw [zpow_natCast, pow_add, Nat.cast_mul, Nat.cast_pow, mul_inv, mul_comm (((p : Y.Kc) ^ e)⁻¹),
      mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hp)]
  rw [key]
  exact Y.Oc.mul_mem (natInv_mem Y m hm) (Y.Oc.pow_mem (natCast_mem Y.Oc p) _)

theorem stab_inv (j : ℕ) (hj : j ≤ X.mm) (La : X.Lt j) (hLa : (X.Pj j).IsLatTup La.2) :
    algebraMap X.G.Kf Y.Kc (((X.stab j La : X.G.Kf))⁻¹) * (p : Y.Kc) ^ ((X.dG j : ℕ) : ℤ) ∈ Y.Oc := by
  rw [map_inv₀, map_natCast]
  exact wt_inv Y _ _ (Y.stab_fin j hj La hLa) (X.dG_spec j hj La.1 La.2 hLa)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcSummableMin
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset

theorem nc_geom (p : ℕ) (hp : 2 ≤ p) :
    HasSum (fun e : ℕ => (((p : ℝ)) ^ (2 * e + 1))⁻¹) (Formalism.MainNotions.FormalGroupSystem.gam p) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hq : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hr : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have h0 : 0 ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
  have := (hasSum_geometric_of_lt_one h0 hr).mul_left ((p : ℝ)⁻¹)
  have e1 : (fun e : ℕ => ((p : ℝ) ^ (2 * e + 1))⁻¹) = fun i : ℕ => (p : ℝ)⁻¹ * ((p : ℝ) ^ 2)⁻¹ ^ i := by
    funext e
    rw [pow_succ, pow_mul, mul_inv, inv_pow]
    ring
  have e2 : Formalism.MainNotions.FormalGroupSystem.gam p = (p : ℝ)⁻¹ * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
    rw [Formalism.MainNotions.FormalGroupSystem.gam]
    first
      | (field_simp; ring)
      | field_simp
  rw [e1, e2]
  exact this

theorem nc_geomc (p : ℕ) (hp : 2 ≤ p) (c : ℝ) :
    HasSum (fun e : ℕ => c / ((p : ℝ)) ^ (2 * e + 1)) (c * Formalism.MainNotions.FormalGroupSystem.gam p) := by
  have := (nc_geom p hp).mul_left c
  simpa [div_eq_mul_inv] using this

theorem nc_abs_min_le (a b : ℝ) (hb : 0 ≤ b) : |min a b| ≤ |a| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, abs_of_nonneg hb, abs_of_nonneg (hb.trans h)]
    exact h

theorem nc_summable_min (p : ℕ) (hp : 2 ≤ p) (y : ℝ) (z : ℕ → ℝ) (hz : ∀ e, 0 ≤ z e) :
    Summable fun e : ℕ => min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e) := by
  have hg : Summable (fun e : ℕ => |y| / ((p : ℝ)) ^ (2 * e + 1)) := (nc_geomc p hp |y|).summable
  have hb : ∀ e : ℕ, ‖min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e)‖ ≤ |y| / ((p : ℝ)) ^ (2 * e + 1) := by
    intro e
    have hq : (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
      positivity
    rw [Real.norm_eq_abs]
    calc |min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e)| ≤ |y / ((p : ℝ)) ^ (2 * e + 1)| := nc_abs_min_le _ _ (hz e)
      _ = |y| / ((p : ℝ)) ^ (2 * e + 1) := by rw [abs_div, abs_of_pos hq]
  first
    | exact Summable.of_norm_bounded hg hb
    | exact Summable.of_norm_bounded _ hg hb

theorem nc_min (p : ℕ) (hp : 2 ≤ p) (y yu : ℝ) (z zu : ℕ → ℝ) (hy : y ≤ yu) (hz : ∀ e, zu e ≤ z e)
    (hz0 : ∀ e, 0 ≤ zu e) :
    Formalism.MainNotions.FormalGroupSystem.gam p * y - ∑' e : ℕ, min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e) ≤
      Formalism.MainNotions.FormalGroupSystem.gam p * yu - ∑' e : ℕ, min (yu / ((p : ℝ)) ^ (2 * e + 1)) (zu e) := by
  have hs1 := nc_geomc p hp y
  have hs2 := nc_geomc p hp yu
  have m1 := nc_summable_min p hp y z (fun e => (hz0 e).trans (hz e))
  have m2 := nc_summable_min p hp yu zu hz0
  rw [mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p) y, mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p) yu, ← hs1.tsum_eq, ← hs2.tsum_eq]
  rw [← hs1.summable.tsum_sub m1, ← hs2.summable.tsum_sub m2]
  refine (hs1.summable.sub m1).tsum_le_tsum (fun e => ?_) (hs2.summable.sub m2)
  have hq : (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    positivity
  have ha : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy hq.le
  have hze := hz e
  simp only [Pi.sub_apply, min_def]
  split_ifs <;> linarith

theorem nc_pos (p : ℕ) (hp : 2 ≤ p) (y yu : ℝ) (z zu : ℕ → ℝ) (ex exu : ℕ → Prop) [DecidablePred ex]
    [DecidablePred exu] (hy : y ≤ yu) (hyu : 0 ≤ yu) (hz : ∀ e, zu e ≤ z e) (hz0 : ∀ e, 0 ≤ zu e)
    (hex : ∀ e, exu e → ex e) :
    ∑' e : ℕ, (if ex e then 0 else max 0 (y / ((p : ℝ)) ^ (2 * e + 1) - z e)) ≤
      ∑' e : ℕ, (if exu e then 0 else max (yu / ((p : ℝ)) ^ (2 * e + 1) - zu e) 0) := by
  have hq : ∀ e : ℕ, (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
    intro e
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    positivity
  have hS := (nc_geomc p hp yu).summable
  have hR : Summable (fun e : ℕ => if exu e then 0 else max (yu / ((p : ℝ)) ^ (2 * e + 1) - zu e) 0) := by
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hS
    · split_ifs
      · exact le_rfl
      · exact le_max_right _ _
    · have h1 : 0 ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_nonneg hyu (hq e).le
      have h2 := hz0 e
      split_ifs
      · exact h1
      · exact max_le (by linarith) h1
  have hLs : Summable (fun e : ℕ => if ex e then 0 else max 0 (y / ((p : ℝ)) ^ (2 * e + 1) - z e)) := by
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hS
    · split_ifs
      · exact le_rfl
      · exact le_max_left _ _
    · have h1 : 0 ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_nonneg hyu (hq e).le
      have h3 : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy (hq e).le
      have h2 := hz0 e
      have h4 := hz e
      split_ifs
      · exact h1
      · exact max_le h1 (by linarith)
  refine hLs.tsum_le_tsum (fun e => ?_) hR
  have h3 : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy (hq e).le
  have h4 := hz e
  by_cases he : ex e
  · rw [if_pos he]
    split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  · have heu : ¬ exu e := fun h => he (hex e h)
    rw [if_neg he, if_neg heu]
    exact max_le (le_max_right _ _) (le_trans (by linarith) (le_max_left _ _))

variable {n' k1 : ℕ}

theorem nc_gB_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (ya zc : Fin n' → ℝ) (dlv : ℝ) (h1 : ∀ s ∈ TT, ya s ≤ al TT lam0 s)
    (h2 : ∀ s, (cap t TT lam0 w j s : ℝ) ≤ zc s) (h3 : ∀ s, 0 ≤ cap t TT lam0 w j s)
    (hd : de p t TT lam0 w j ≤ dlv) :
    Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ TT, ya s -
              ∑ s ∈ TT.filter IsOddPos, ∑' e : ℕ,
                min (ya s / ((p : ℝ)) ^ (2 * e + 1)) (zc (Formalism.MainNotions.G.posAdd s (2 * e + 1))) - dlv ≤
      gB p t TT lam0 w j := by
  unfold gB
  have hg0 : 0 ≤ Formalism.MainNotions.FormalGroupSystem.gam p := (nc_geom p hp).nonneg fun e => by positivity
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not TT IsOddPos,
    ← Finset.sum_filter_add_sum_filter_not TT IsOddPos (fun s => Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ))]
  have hA : ∑ s ∈ TT.filter IsOddPos, (Formalism.MainNotions.FormalGroupSystem.gam p * ya s - ∑' e : ℕ,
        min (ya s / ((p : ℝ)) ^ (2 * e + 1)) (zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) ≤
      ∑ s ∈ TT.filter IsOddPos, (Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ) - ∑' e : ℕ,
        min ((al TT lam0 s : ℝ) / ((p : ℝ)) ^ (2 * e + 1)) (cap t TT lam0 w j (Formalism.MainNotions.G.posAdd s (2 * e + 1)) : ℝ)) := by
    apply Finset.sum_le_sum
    intro s hs
    exact nc_min p hp _ _ _ _ (h1 s (Finset.mem_filter.1 hs).1) (fun e => h2 _) (fun e => by exact_mod_cast h3 _)
  have hB : ∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), Formalism.MainNotions.FormalGroupSystem.gam p * ya s ≤
      ∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ) := by
    apply Finset.sum_le_sum
    intro s hs
    exact mul_le_mul_of_nonneg_left (h1 s (Finset.mem_filter.1 hs).1) hg0
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hA
  linarith

theorem nc_gA_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (ya zc : Fin n' → ℝ) (dlv : ℝ) (ex : Fin n' → ℕ → Prop) [∀ s, DecidablePred (ex s)]
    (h1 : ∀ s ∈ TT, ya s ≤ al TT lam0 s) (h0 : ∀ s, 0 ≤ al TT lam0 s)
    (h2 : ∀ s, (cap t TT lam0 w j s : ℝ) ≤ zc s) (h3 : ∀ s, 0 ≤ cap t TT lam0 w j s)
    (hex : ∀ s ∈ TT, ∀ e, 2 * e + 1 ∈ dSet TT s → ex s e)
    (hd : de p t TT lam0 w j ≤ dlv) :
    ∑ s ∈ TT, ∑' e : ℕ, (if ex s e then 0 else
        max 0 (ya s / ((p : ℝ)) ^ (2 * e + 1) - zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) - dlv ≤
      gA p t TT lam0 w j := by
  unfold gA
  have hA : ∑ s ∈ TT, ∑' e : ℕ, (if ex s e then 0 else
        max 0 (ya s / ((p : ℝ)) ^ (2 * e + 1) - zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) ≤
      ∑ s ∈ TT, ∑' e : ℕ, (if 2 * e + 1 ∈ dSet TT s then 0 else
        max ((al TT lam0 s : ℝ) / (p : ℝ) ^ (2 * e + 1) -
          (cap t TT lam0 w j (Formalism.MainNotions.G.posAdd s (2 * e + 1)) : ℝ)) 0) := by
    apply Finset.sum_le_sum
    intro s hs
    exact nc_pos p hp _ _ _ _ (ex s) (fun e => 2 * e + 1 ∈ dSet TT s) (h1 s hs) (by exact_mod_cast h0 s)
      (fun e => h2 _) (fun e => by exact_mod_cast h3 _) (hex s hs)
  linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

