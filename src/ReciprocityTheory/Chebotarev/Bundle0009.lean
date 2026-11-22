import ReciprocityTheory.Chebotarev.Bundle0004
import ReciprocityTheory.Chebotarev.Bundle0008
import ReciprocityTheory.Chebotarev.Bundle0007
import ReciprocityTheory.Chebotarev.Bundle0006
import ReciprocityTheory.Chebotarev.Bundle0002
import ReciprocityTheory.Chebotarev.Bundle0005
import ReciprocityTheory.Chebotarev.SplitF
import ReciprocityTheory.Chebotarev.Bundle0003

-- bundled from ReciprocityTheory.Chebotarev.CTrick
section
open NumberField NumberField.mixedEmbedding NumberField.Units

open scoped Classical

namespace ReciprocityTheory.Cheb

variable {E : Type} [Field E] [NumberField E]

noncomputable def mulDvdEquiv (c : NZIdeal E) : NZIdeal E ≃ {a : NZIdeal E // c.1 ∣ a.1} :=
  Equiv.ofBijective (fun b => ⟨⟨c.1 * b.1, mul_ne_zero c.2 b.2⟩, dvd_mul_right _ _⟩) (by
    constructor
    · intro b b' h
      have h1 : c.1 * b.1 = c.1 * b'.1 := congrArg (fun x => x.1.1) h
      exact Subtype.ext (mul_left_cancel₀ c.2 h1)
    · rintro ⟨a, ⟨b, hb⟩⟩
      have hb0 : b ≠ ⊥ := by
        rintro rfl
        exact a.2 (by rw [hb]; simp)
      exact ⟨⟨b, hb0⟩, Subtype.ext (Subtype.ext hb.symm)⟩)

theorem mulDvdEquiv_apply (c b : NZIdeal E) : (mulDvdEquiv c b).1.1 = c.1 * b.1 := rfl

theorem tsum_dvd_eq {l : ℕ} (χ : DirichletCharacter ℂ l) (c : NZIdeal E) {s : ℝ} (hs : 1 < s) :
    ∑' a : NZIdeal E, (if c.1 ∣ a.1 then
        χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) else 0) =
      χ ((Ideal.absNorm c.1 : ℕ) : ZMod l) * ((Ideal.absNorm c.1 : ℕ) : ℂ) ^ (-(s : ℂ)) * Lser E χ s := by
  set g : NZIdeal E → ℂ := fun a =>
    χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ)) with hg
  have h1 : (∑' a : NZIdeal E, (if c.1 ∣ a.1 then g a else 0)) =
      ∑' a : {a : NZIdeal E // c.1 ∣ a.1}, g a.1 := by
    rw [show (∑' a : {a : NZIdeal E // c.1 ∣ a.1}, g a.1) =
      ∑' a : ({a : NZIdeal E | c.1 ∣ a.1} : Set (NZIdeal E)), g a.1 from rfl, tsum_subtype]
    exact tsum_congr (fun a => by simp [Set.indicator_apply])
  rw [h1, ← (mulDvdEquiv c).tsum_eq, Lser, ← tsum_mul_left]
  refine tsum_congr (fun b => ?_)
  simp only [hg]
  rw [mulDvdEquiv_apply]
  simp only [map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

theorem tsum_eq_sum_cls (F : NZIdeal E → ℂ) (hF : Summable F) :
    ∑' a : NZIdeal E, F a = ∑ C : ClassGroup (𝓞 E), ∑' a : NZIdeal E, (if cls a = C then F a else 0) := by
  rw [← Summable.tsum_finsetSum (fun C _ => ?_)]
  · refine tsum_congr (fun a => ?_)
    rw [Finset.sum_ite_eq]
    simp
  · have := hF.indicator {a | cls a = C}
    refine this.congr (fun a => ?_)
    simp [Set.indicator_apply]

theorem exists_cls_eq (C : ClassGroup (𝓞 E)) : ∃ b : NZIdeal E, cls b = C := by
  obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective C
  exact ⟨⟨I.1, nonZeroDivisors.ne_zero I.2⟩, hI⟩

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.KHoldA
section
open NumberField NumberField.mixedEmbedding NumberField.Units Set

open scoped Classical

namespace ReciprocityTheory.Cheb

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def gfun {l : ℕ} (χ : DirichletCharacter ℂ l) (c : NZIdeal E) (s : ℝ) (a : NZIdeal E) : ℂ :=
  χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) * (1 - (Ideal.absNorm c.1 : ℂ) * (if c.1 ∣ a.1 then 1 else 0)) *
    ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))

theorem exists_F {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2,
      F s = ∑' α : b.1, cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E)) := by
  obtain ⟨hle, reps, hmem, hcover, huniq, hper, hmean⟩ := exists_reps_meanZero χ b c hcop
  obtain ⟨R₀, C, hRC⟩ := gs_diff_bound (E := E) χ (∑ β ∈ reps, ‖β‖)
  have hr : -(Module.finrank ℚ E : ℝ) - 1 < -(Module.finrank ℤ (latOf b.1) : ℝ) := by
    rw [finrank_latOf b.2]; linarith
  have hd : ∀ s ∈ Icc (1 : ℝ) 2, ∀ β ∈ reps, ∀ x ∈ latOf (mbc l b.1 c.1), R₀ ≤ ‖x‖ →
      ‖Gs χ s (x + β) - Gs χ s x‖ ≤ C * ‖x‖ ^ (-(Module.finrank ℚ E : ℝ) - 1) := by
    intro s hs β hβ x _ hR
    exact hRC s hs x β (Finset.single_le_sum (f := fun β => ‖β‖) (fun _ _ => norm_nonneg _) hβ) hR
  have hbd : ∀ s ∈ Icc (1 : ℝ) 2, ∀ x ∈ latOf b.1, ‖Gs χ s x‖ ≤ 1 := by
    intro s hs x hx
    obtain ⟨α, -, rfl⟩ := mem_latOf.mp hx
    exact norm_gs_embZ_le χ hs.1 α
  have hsm : ∀ s ∈ Ioc (1 : ℝ) 2, Summable fun α : latOf b.1 => Gs χ s (α : mixedSpace E) := fun s hs =>
    summable_gs χ (latOf b.1) (finrank_latOf b.2) hs.1
  have hct : ∀ x ∈ latOf b.1, ContinuousOn (fun s => Gs χ s x) (Icc 1 2) := fun x _ =>
    (continuous_gs χ x).continuousOn
  obtain ⟨F, hF, hFeq⟩ := exists_continuousOn_latticeSum (latOf b.1) (latOf (mbc l b.1 c.1)) hle reps
    hmem hcover huniq (cfun χ b.1 c.1) hper hmean (fun s => Gs χ s) _ hr ⟨R₀, C, hd⟩ 1 hbd hsm hct
  refine ⟨F, hF, fun s hs => ?_⟩
  rw [hFeq s hs]
  exact tsum_latOf b.1 (fun x => cfun χ b.1 c.1 x * Gs χ s x)

def Hfun {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (I : Ideal (𝓞 E)) : ℂ :=
  ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) * (χ (((Ideal.absNorm I / Ideal.absNorm b.1 : ℕ)) : ZMod l) *
    (1 - (Ideal.absNorm c.1 : ℂ) * (if b.1 * c.1 ∣ I then 1 else 0)) * ((Ideal.absNorm I : ℕ) : ℂ) ^ (-(s : ℂ)))

theorem natCast_cpow_mul_cpow_neg {n : ℕ} (hn : n ≠ 0) (s : ℂ) : (n : ℂ) ^ s * (n : ℂ) ^ (-s) = 1 := by
  rw [Complex.cpow_neg, mul_inv_cancel₀]
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => hn (by exact_mod_cast h.1)

theorem Hfun_mul {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (a : NZIdeal E) :
    Hfun χ b c s (a.1 * b.1) = gfun χ c s a := by
  have hb : Ideal.absNorm b.1 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact b.2
  have hdvd : (b.1 * c.1 ∣ a.1 * b.1) ↔ c.1 ∣ a.1 := by
    rw [mul_comm a.1]; exact mul_dvd_mul_iff_left b.2
  simp only [Hfun, gfun, map_mul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb), hdvd, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow]
  have := natCast_cpow_mul_cpow_neg hb (s : ℂ)
  linear_combination (χ ((Ideal.absNorm a.1 : ℕ) : ZMod l) *
    (1 - (Ideal.absNorm c.1 : ℂ) * (if c.1 ∣ a.1 then 1 else 0)) * ((Ideal.absNorm a.1 : ℕ) : ℂ) ^ (-(s : ℂ))) * this

theorem uphi_Hfun_span {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ) (α : b.1) :
    ((uphi (embZ (α : 𝓞 E)) : ℝ) : ℂ) * Hfun χ b c s (Ideal.span {(α : 𝓞 E)}) =
      ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) *
        (cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E))) := by
  obtain ⟨q, hq⟩ := absNorm_dvd_algebraNorm α.2
  have hbc : (b.1 * c.1 ∣ Ideal.span {(α : 𝓞 E)}) ↔ (α : 𝓞 E) ∈ b.1 * c.1 := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  have hb : Ideal.absNorm b.1 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact b.2
  have hsg := rsgn_mul_norm (α : 𝓞 E)
  have hchi : χ ((((Ideal.absNorm (Ideal.span {(α : 𝓞 E)})) / Ideal.absNorm b.1 : ℕ)) : ZMod l) =
      χ ((Algebra.norm ℤ (α : 𝓞 E) / (Ideal.absNorm b.1 : ℤ) : ℤ) : ZMod l) * χ (rsgn (embZ (α : 𝓞 E)) : ZMod l) := by
    rw [← map_mul, ← Int.cast_mul, ← Int.cast_natCast, Ideal.absNorm_span_singleton, Int.natCast_div,
      Int.natCast_natAbs, ← hsg, Int.mul_ediv_assoc _ (absNorm_dvd_algebraNorm α.2), mul_comm]
  have hn : ((mixedEmbedding.norm (embZ (α : 𝓞 E)) : ℝ) : ℂ) =
      ((Ideal.absNorm (Ideal.span {(α : 𝓞 E)}) : ℕ) : ℂ) := by
    rw [norm_embZ, Ideal.absNorm_span_singleton, Nat.cast_natAbs]
    rw [← Int.cast_abs, Complex.ofReal_intCast]
  simp only [Hfun, cfun, Gs, preZ_embZ, hbc, hchi, hn]
  ring

theorem class_sum_eq {l : ℕ} (χ : DirichletCharacter ℂ l) (b c : NZIdeal E) (s : ℝ)
    (hg : Summable (gfun χ c s)) :
    ∑' a : NZIdeal E, (if cls a * cls b = 1 then gfun χ c s a else 0) =
      ((torsionOrder E : ℕ) : ℂ)⁻¹ * ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) *
        ∑' α : b.1, cfun χ b.1 c.1 (embZ (α : 𝓞 E)) * Gs χ s (embZ (α : 𝓞 E)) := by
  have h := tsum_class_eq_latSum b (Hfun χ b c s) (by simpa only [Hfun_mul] using hg)
  simp only [Hfun_mul] at h
  rw [h]
  simp_rw [uphi_Hfun_span]
  rw [tsum_mul_left, mul_assoc]

theorem exists_class_cont {l : ℕ} [Fact l.Prime] (χ : DirichletCharacter ℂ l) (b c : NZIdeal E)
    (hcop : Nat.Coprime (Ideal.absNorm c.1) (l * Ideal.absNorm b.1)) :
    ∃ F : ℝ → ℂ, ContinuousOn F (Icc 1 2) ∧ ∀ s ∈ Ioc (1 : ℝ) 2, Summable (gfun χ c s) →
      ∑' a : NZIdeal E, (if cls a * cls b = 1 then gfun χ c s a else 0) =
        ((torsionOrder E : ℕ) : ℂ)⁻¹ * ((Ideal.absNorm b.1 : ℕ) : ℂ) ^ (s : ℂ) * F s := by
  obtain ⟨F, hF, hFeq⟩ := exists_F χ b c hcop
  exact ⟨F, hF, fun s hs hg => by rw [class_sum_eq χ b c s hg, hFeq s hs]⟩

end

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.SplitB
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem csb_nrm_pos {E : Type} [Field E] [NumberField E] (q : Prm E) : 1 ≤ Nrm q := by
  unfold Nrm
  rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact q.ne_bot

theorem csb_pow_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ^ 2 ≤ b) (s : ℝ) (hs : 1 < s) :
    ((b : ℕ) : ℝ) ^ (-s) ≤ ((a : ℕ) : ℝ) ^ (-2 : ℝ) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : ((a : ℝ)) ^ 2 ≤ (b : ℝ) := by exact_mod_cast hab
  have hb' : (1 : ℝ) ≤ b := le_trans (one_le_pow₀ ha') hab'
  calc ((b : ℝ)) ^ (-s) ≤ (b : ℝ) ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hb' (by linarith)
    _ = (b : ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ ((a : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hab'
    _ = (a : ℝ) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (by positivity), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem PE_cyclotomicField_le_mul_Pcl_add_const (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (hirr : Irreducible (Polynomial.cyclotomic l E)) :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s → PE (CyclotomicField l E) s ≤ ((l - 1 : ℕ) : ℝ) * Pcl E l 1 s + C := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hfin := splitA_finite_not_coprime E l hl0
  set A : ℝ := ∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ)
  set B : ℝ := ∑' q : Prm E, (if Nat.Coprime (Nrm q) l then (0 : ℝ) else 1)
  refine ⟨((l - 1 : ℕ) : ℝ) * (A + B), fun s hs => ?_⟩
  have hA : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ)) := affine_proper_base_change.2.2 E 2 (by norm_num)
  have hB : Summable (fun q : Prm E => (if Nat.Coprime (Nrm q) l then (0 : ℝ) else 1)) := by
    apply summable_of_ne_finset_zero (s := hfin.toFinset)
    intro q hq
    rw [Set.Finite.mem_toFinset] at hq
    simp only [Set.mem_ofPred_eq, not_not] at hq
    simp [hq]
  have hP1 : Summable (fun q : Prm E =>
      if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
    refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_) (affine_proper_base_change.2.2 E s hs)
    · split_ifs <;> positivity
    · split_ifs
      · exact le_rfl
      · positivity
  let h : Prm E → ℝ := fun q =>
    ((if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) + ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ)) +
      (if Nat.Coprime (Nrm q) l then (0 : ℝ) else 1)
  have hh0 : ∀ q, 0 ≤ h q := by
    intro q
    simp only [h]
    have : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ) := by positivity
    split_ifs <;> positivity
  have hhs : Summable h := (hP1.add hA).add hB
  have hfh : ∀ P : Prm (CyclotomicField l E), ((Nrm P : ℕ) : ℝ) ^ (-s) ≤ h (under P) := by
    intro P
    set q := under (E := E) P with hq
    have hq1 := csb_nrm_pos q
    have hP1' := csb_nrm_pos P
    have h2 : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-2 : ℝ) := by positivity
    have hPs : 0 ≤ ((Nrm P : ℕ) : ℝ) ^ (-s) := by positivity
    simp only [h]
    by_cases hc : Nat.Coprime (Nrm q) l
    · have hnd : ¬ l ∣ Nrm q := by
        rw [← Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
        exact hc.symm
      rw [if_pos hc, add_zero]
      rcases splitA_norm E l q P hq.symm hnd with ⟨he, h1⟩ | hsq
      · rw [if_pos h1, he]
        linarith
      · have := csb_pow_le _ _ hq1 hsq s hs
        have : 0 ≤ (if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
          split_ifs <;> positivity
        linarith
    · rw [if_neg hc]
      have : ((Nrm P : ℕ) : ℝ) ^ (-s) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hP1') (by linarith)
      have : 0 ≤ (if ((Nrm q : ℕ) : ZMod l) = 1 then ((Nrm q : ℕ) : ℝ) ^ (-s) else 0) := by
        split_ifs <;> positivity
      linarith
  have key := fibre_sum_le (under (E := E)) (fun P : Prm (CyclotomicField l E) => ((Nrm P : ℕ) : ℝ) ^ (-s)) h
    (l - 1) (fun P => by positivity) hfh hh0 hhs (fun q => splitA_fibre E l hirr q)
  have hsum : ∑' q, h q = Pcl E l 1 s + A + B := by
    simp only [h]
    rw [(hP1.add hA).tsum_add hB, hP1.tsum_add hA]
    rfl
  have : PE (CyclotomicField l E) s ≤ ((l - 1 : ℕ) : ℝ) * ∑' q, h q := key.2
  rw [hsum] at this
  linarith

end ReciprocityTheory.Cheb
end

-- bundled from ReciprocityTheory.Chebotarev.SplitC
section
open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem splitC_nrm_pos {E : Type} [Field E] [NumberField E] (q : Prm E) : 0 < ((Nrm q : ℕ) : ℝ) := by
  have : Nrm q ≠ 0 := by
    unfold Nrm
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact q.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

theorem splitC_nrm_ge_one {E : Type} [Field E] [NumberField E] (q : Prm E) : 1 ≤ ((Nrm q : ℕ) : ℝ) := by
  have h := splitC_nrm_pos q
  have : 0 < Nrm q := by exact_mod_cast h
  exact_mod_cast this

theorem splitC_indicator_le {E : Type} [Field E] [NumberField E] (S : Set (Prm E)) (hS : S.Finite) (s : ℝ)
    (hs : 0 ≤ s) : ∑' q, S.indicator (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) q ≤ hS.toFinset.card := by
  rw [tsum_eq_sum (s := hS.toFinset)]
  · calc ∑ q ∈ hS.toFinset, S.indicator (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) q
        ≤ ∑ _q ∈ hS.toFinset, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Set.indicator_of_mem (hS.mem_toFinset.mp hq)]
          exact Real.rpow_le_one_of_one_le_of_nonpos (splitC_nrm_ge_one q) (by linarith)
      _ = hS.toFinset.card := by simp
  · intro q hq
    rw [Set.indicator_of_notMem]
    intro h'
    exact hq (hS.mem_toFinset.mpr h')

theorem splitC_bound (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (S : Set (Prm E)) (hS : S.Finite)
    (h : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard) (s : ℝ) (hs : 1 < s) :
    (k : ℝ) * PE E s ≤ PE E' s + k * hS.toFinset.card := by
  have key := fibre_sum_ge (under (E := E) (E' := E')) (fun P : Prm E' => ((Nrm P : ℕ) : ℝ) ^ (-s))
    (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) k (fun P => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (affine_proper_base_change.2.2 E' s hs) (fun q => Real.rpow_nonneg (Nat.cast_nonneg _) _) (affine_proper_base_change.2.2 E s hs) S hS
    (by
      intro q hq
      have hset : {P : Prm E' | under P = q ∧ ((Nrm P : ℕ) : ℝ) ^ (-s) = ((Nrm q : ℕ) : ℝ) ^ (-s)} =
          {P : Prm E' | under P = q ∧ Nrm P = Nrm q} := by
        ext P
        simp only [Set.mem_ofPred_eq]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          have := (Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by linarith : -s ≠ 0)).mp h2
          exact_mod_cast this
        · rintro ⟨h1, h2⟩
          exact ⟨h1, by rw [h2]⟩
      rw [hset]
      exact h q hq)
  have hind := splitC_indicator_le S hS s (by linarith)
  unfold PE
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hind hk0]

theorem splitC_not_almost_split (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E']
    (k : ℕ) (hk : 2 ≤ k)
    (h : {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard}.Finite) : False := by
  set S := {q : Prm E | ¬ k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard} with hSdef
  have hfib : ∀ q ∉ S, k ≤ {P : Prm E' | under P = q ∧ Nrm P = Nrm q}.ncard := by
    intro q hq
    by_contra hc
    exact hq hc
  obtain ⟨C1, hC1⟩ := chebyshev_log_bounded E
  obtain ⟨C2, hC2⟩ := chebyshev_log_bounded E'
  set N : ℝ := (h.toFinset.card : ℝ)
  set M : ℝ := max (C2 + k * (N + C1)) 0
  set s : ℝ := 1 + Real.exp (-(M + 1))
  have he : 0 < Real.exp (-(M + 1)) := Real.exp_pos _
  have he1 : Real.exp (-(M + 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ M := le_max_right _ _
    linarith)
  have hs1 : 1 < s := by simp only [s]; linarith
  have hs2 : s ∈ Set.Ioc 1 2 := ⟨hs1, by simp only [s]; linarith⟩
  have hlog : Real.log (1 / (s - 1)) = M + 1 := by
    simp only [s, add_sub_cancel_left, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hb := splitC_bound E E' k S h hfib s hs1
  have h1 := hC1 s hs2
  have h2 := hC2 s hs2
  rw [hlog] at h1 h2
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hM : C2 + k * (N + C1) ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := le_max_right _ _
  have a1 := abs_le.mp h1
  have a2 := abs_le.mp h2
  have : (k : ℝ) * (M + 1 - C1) ≤ k * PE E s := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

end ReciprocityTheory.Cheb
end

