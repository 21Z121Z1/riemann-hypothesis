import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0032
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0093
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0164
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0127
import Formalism.LocalToGlobal.Columns.AlgebraMapMemMaximalIdealPowIff
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveOfPhiModuleExactTriple
section
open PowerSeries GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

theorem mulVec_eq_zero_of_subalgebra {O S : Type} [CommRing O] [CommRing S] [IsDomain S] [Algebra O S]
    (B : Subalgebra O S) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (M : Matrix κ ι S) (hM : ∀ i j, M i j ∈ B)
    (hinj : ∀ v : ι → S, (∀ j, v j ∈ B) → M *ᵥ v = 0 → v = 0) (w : ι → S) (hw : M *ᵥ w = 0) :
    w = 0 := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_9 h_10 h_11 h_12; revert O S h_2 h_3 h_4 h_5 B ι κ h_9 h_10 h_11 h_12 M hM hinj w hw; exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra)
  | exact @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra
  | (apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SubalgebraMulVecZero.mulVec_eq_zero_of_subalgebra ..)

end GlobalTheory.BK

theorem GlobalTheory.BK.IsExactTriple.injective_app : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) [Fact l.Prime] (ι κ μ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T : PhiMod O K l e a μ) (F : Hom P Q) (G : Hom Q T), IsExactTriple F G → Function.Injective F.app := by
  intro O K _ _ _ _ _ l e a _ ι κ μ _ _ _ _ _ _ P Q T F G hex
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  funext τ
  refine mulVec_eq_zero_of_subalgebra (A O K) (F.mat τ) (F.mem τ) ?_ (w τ) ?_
  · intro v hv hMv
    have hu : Pi.single τ v ∈ P.M := mem_tot.2 fun τ' => by
      by_cases h : τ' = τ
      · subst h; simpa using (mem_vecs.2 hv)
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _
    have h0 : F.app (Pi.single τ v) = 0 := by
      funext τ'
      rw [Hom.app_apply]
      by_cases h : τ' = τ
      · subst h; simpa using hMv
      · rw [Pi.single_eq_of_ne h, Matrix.mulVec_zero]; rfl
    have := congrFun (hex.inj _ hu h0) τ
    simpa using this
  · have := congrFun hw τ
    rwa [Hom.app_apply] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAdicCompleteTwistedInvariantLattice
section
noncomputable section

namespace GlobalTheory.BK

open PowerSeries Filter Topology

section Lim

variable {K : Type} [NormedField K]

theorem exists_lim_of_norm_sub_le_pow [CompleteSpace K] {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    {c : ℕ → K} (h : ∀ m n, m ≤ n → ‖c n - c m‖ ≤ r ^ m) : ∃ x, ∀ n, ‖c n - x‖ ≤ r ^ n := by
  have hc : CauchySeq c := by
    refine cauchySeq_of_le_tendsto_0 (fun N => r ^ N) (fun n m N hn hm => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr)
    rw [dist_eq_norm]
    rcases le_total n m with hnm | hnm
    · rw [norm_sub_rev]
      exact (h n m hnm).trans (pow_le_pow_of_le_one hr0 hr.le hn)
    · exact (h m n hnm).trans (pow_le_pow_of_le_one hr0 hr.le hm)
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨x, fun n => ?_⟩
  have ht : Tendsto (fun m => ‖c n - c m‖) atTop (𝓝 ‖c n - x‖) :=
    (tendsto_const_nhds.sub hx).norm
  refine le_of_tendsto ht ?_
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [norm_sub_rev]
  exact h n m hm

theorem eq_zero_of_norm_le_pow_of_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) {x : K}
    (h : ∀ n, ‖x‖ ≤ r ^ n) : x = 0 :=
  norm_le_zero_iff.1 (ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr) h)

end Lim

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K]

omit [IsUltrametricDist K] [IsUnitBall O K] [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] in

theorem pow_l_smul_vec_eq (n : ℕ) (v : Vec K a ι) : ((l : O) ^ n) • v = ((l : K) ^ n) • v := by
  rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem norm_coeff_pow_l_smul_le {P : PhiMod O K l e a ι} {t : Vec K a ι} (ht : t ∈ P.M) (n : ℕ)
    (τ : ZMod a) (i : ι) (k : ℕ) : ‖coeff k ((((l : K) ^ n) • t) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
  simp only [Pi.smul_apply, coeff_smul, smul_eq_mul, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (mem_A.1 (mem_vecs.1 (mem_tot.1 ht τ) i) k)

theorem pow_l_inv_smul_mem_M {P : PhiMod O K l e a ι} {v : Vec K a ι} {n : ℕ}
    (h : ∀ τ i k, ‖coeff k (v τ i)‖ ≤ ‖(l : K)‖ ^ n) : ((l : K) ^ n)⁻¹ • v ∈ P.M :=
  mem_tot.2 fun τ => mem_vecs.2 fun i => mem_A.2 fun k => by
    simp only [Pi.smul_apply, coeff_smul, smul_eq_mul, norm_mul, norm_inv, norm_pow]
    have hl : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
    rw [inv_mul_le_iff₀ hl, mul_one]
    exact h τ i k

variable [CompleteSpace K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

namespace BKDat

variable (D : BKDat O K l e a ι η H)

theorem mem_Y'_iff_coeff {v : Vec K a ι} : v ∈ D.Y' ↔ E K l e ^ η • v ∈ D.M ∧
    (∀ g, D.desc.act g v = v) ∧ ∀ τ i k, k < e → coeff k (v τ i) = 0 := by
  constructor
  · intro hv
    obtain ⟨y, hy, rfl⟩ := (Descent.mem_Y' _).1 hv
    have h2 := (Descent.mem_invOf _).1 (Descent.Y'_le_Y _ η hv)
    refine ⟨mem_divE.1 h2.1, h2.2, fun τ i k hk => ?_⟩
    show coeff k ((X : K⟦X⟧) ^ e * y τ i) = 0
    rw [coeff_X_pow_mul', if_neg (by omega)]
  · rintro ⟨h1, h2, h3⟩
    have hd : ∀ τ i, (X : K⟦X⟧) ^ e ∣ v τ i := fun τ i => X_pow_dvd_iff.2 fun k hk => h3 τ i k hk
    choose y hy using hd
    have hv : v = (X : K⟦X⟧) ^ e • (y : Vec K a ι) := funext fun τ => funext fun i => hy τ i
    have hXinj : ∀ w w' : Vec K a ι, (X : K⟦X⟧) ^ e • w = (X : K⟦X⟧) ^ e • w' → w = w' :=
      fun w w' h => funext fun τ => funext fun i =>
        mul_left_cancel₀ (pow_ne_zero _ X_ne_zero) (congrFun (congrFun h τ) i)
    refine (Descent.mem_Y' _).2 ⟨y, (Descent.mem_invOf _).2 ⟨mem_divE.2 ?_, fun g => hXinj _ _ ?_⟩, hv.symm⟩
    · refine mem_tot.2 fun τ => mem_vecs.2 fun i => mem_A.2 fun k => ?_
      have := mem_A.1 (mem_vecs.1 (mem_tot.1 h1 τ) i) (k + e)
      have h4 : (E K l e ^ η • v) τ i = (X : K⟦X⟧) ^ e * (E K l e ^ η • y) τ i := by
        rw [hv]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rwa [h4, coeff_X_pow_mul] at this
    · rw [← D.desc.act_X_pow_smul, ← hv, h2 g]

theorem smodEq_Y'_iff (x y : D.Y') (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {(l : O)} ^ n • ⊤ : Submodule O D.Y')] ↔
      ∃ z ∈ D.Y', (x : Vec K a ι) - y = ((l : K) ^ n) • z := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨b, -, hb⟩
    refine ⟨b, b.2, ?_⟩
    rw [← pow_l_smul_vec_eq (O := O)]
    exact (congrArg Subtype.val hb).symm
  · rintro ⟨z, hz, h⟩
    refine ⟨⟨z, hz⟩, Submodule.mem_top, Subtype.ext ?_⟩
    show ((l : O) ^ n) • z = (x : Vec K a ι) - y
    rw [pow_l_smul_vec_eq, h]

theorem isHausdorff_Y' : IsHausdorff (Ideal.span {(l : O)}) D.Y' := ⟨fun x hx => by
  have hE : ∀ n τ i k, ‖coeff k ((E K l e ^ η • (x : Vec K a ι)) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
    intro n
    obtain ⟨z, hz, h⟩ := (D.smodEq_Y'_iff x 0 n).1 (hx n)
    rw [ZeroMemClass.coe_zero, sub_zero] at h
    rw [h, smul_comm]
    exact norm_coeff_pow_l_smul_le ((D.mem_Y'_iff_coeff).1 hz).1 n
  have h0 : E K l e ^ η • (x : Vec K a ι) = 0 := funext fun τ => funext fun i => ext fun k =>
    eq_zero_of_norm_le_pow_of_lt_one (norm_nonneg _) (norm_l_lt_one l) fun n => hE n τ i k
  exact Subtype.ext (((isUnit_E (K := K) l e).pow η).smul_left_cancel.1 (h0.trans (smul_zero _).symm))⟩

theorem isPrecomplete_Y' : IsPrecomplete (Ideal.span {(l : O)}) D.Y' := ⟨fun f hf => by
  have hl0 : ∀ n, ((l : K) ^ n) ≠ 0 := fun n => pow_ne_zero _ (l_ne_zero l)
  have hr0 : (0 : ℝ) ≤ ‖(l : K)‖ := norm_nonneg _
  have hr1 : ‖(l : K)‖ < 1 := norm_l_lt_one l
  have hfY : ∀ n, _ := fun n => (D.mem_Y'_iff_coeff).1 (f n).2
  set s : ℕ → Vec K a ι := fun n => E K l e ^ η • (f n : Vec K a ι) with hs_def
  have hs : ∀ m n, m ≤ n → ∀ τ i k, ‖coeff k (s n τ i) - coeff k (s m τ i)‖ ≤ ‖(l : K)‖ ^ m := by
    intro m n hmn τ i k
    obtain ⟨z, hz, h⟩ := (D.smodEq_Y'_iff _ _ m).1 (hf hmn)
    have h' : s m - s n = ((l : K) ^ m) • (E K l e ^ η • z) := by
      simp only [hs_def]
      rw [← smul_sub, h, smul_comm]
    have := norm_coeff_pow_l_smul_le ((D.mem_Y'_iff_coeff).1 hz).1 m τ i k
    rw [← h', Pi.sub_apply, Pi.sub_apply, map_sub] at this
    rwa [norm_sub_rev]
  choose w hw using fun p : ZMod a × ι × ℕ =>
    exists_lim_of_norm_sub_le_pow hr0 hr1 (c := fun n => coeff p.2.2 (s n p.1 p.2.1))
      (fun m n hmn => hs m n hmn p.1 p.2.1 p.2.2)
  set W : Vec K a ι := fun τ i => PowerSeries.mk fun k => w (τ, i, k) with hW_def
  have hW : ∀ n τ i k, ‖coeff k ((s n - W) τ i)‖ ≤ ‖(l : K)‖ ^ n := fun n τ i k => by
    simpa [hW_def] using hw (τ, i, k) n

  have hsinv : ∀ n g, D.desc.act g (s n) = s n := fun n g => by
    simp only [hs_def]
    rw [D.desc.act_E_pow_smul, (hfY n).2.1 g]
  have hWinv : ∀ g, D.desc.act g W = W := fun g => by
    have hsm : ∀ n τ i k, ‖coeff k ((D.desc.act g W - W) τ i)‖ ≤ ‖(l : K)‖ ^ n := by
      intro n
      have hb : ∀ τ i k, ‖coeff k ((W - s n) τ i)‖ ≤ ‖(l : K)‖ ^ n := fun τ i k => by
        rw [Pi.sub_apply, Pi.sub_apply, map_sub, norm_sub_rev, ← map_sub, ← Pi.sub_apply,
          ← Pi.sub_apply]
        exact hW n τ i k
      have ht := pow_l_inv_smul_mem_M (P := D.toPhiMod) hb
      set t := ((l : K) ^ n)⁻¹ • (W - s n) with ht_def
      have hWt : W - s n = ((l : K) ^ n) • t := by rw [ht_def, smul_inv_smul₀ (hl0 n)]
      have : D.desc.act g W - W = ((l : K) ^ n) • (D.desc.act g t - t) := by
        rw [smul_sub, ← map_smul, ← hWt, map_sub, hsinv n g]
        abel
      rw [this]
      exact norm_coeff_pow_l_smul_le (sub_mem (D.desc.act_mem_M g t ht) ht) n
    exact sub_eq_zero.1 (funext fun τ => funext fun i => ext fun k =>
      eq_zero_of_norm_le_pow_of_lt_one hr0 hr1 fun n => hsm n τ i k)
  have hWlow : ∀ τ i, (X : K⟦X⟧) ^ e ∣ W τ i := fun τ i => X_pow_dvd_iff.2 fun k hk => by
    have h0 : coeff k (s 0 τ i) = 0 := by
      have hdv : (X : K⟦X⟧) ^ e ∣ s 0 τ i :=
        Dvd.dvd.mul_left (X_pow_dvd_iff.2 fun k hk => (hfY 0).2.2 τ i k hk) _
      exact X_pow_dvd_iff.1 hdv k hk
    refine eq_zero_of_norm_le_pow_of_lt_one hr0 hr1 fun n => ?_
    have h1 : coeff k (s n τ i) = 0 := by
      have hdv : (X : K⟦X⟧) ^ e ∣ s n τ i :=
        Dvd.dvd.mul_left (X_pow_dvd_iff.2 fun k hk => (hfY n).2.2 τ i k hk) _
      exact X_pow_dvd_iff.1 hdv k hk
    have := hW n τ i k
    rwa [Pi.sub_apply, Pi.sub_apply, map_sub, h1, zero_sub, norm_neg] at this

  obtain ⟨u, hu⟩ := (isUnit_E (K := K) l e).pow η
  set L : Vec K a ι := ((u⁻¹ : K⟦X⟧ˣ) : K⟦X⟧) • W with hL_def
  have hEL : E K l e ^ η • L = W := by
    rw [hL_def, smul_smul, ← hu, Units.mul_inv, one_smul]
  have hLinv : ∀ g, D.desc.act g L = L := fun g => by
    refine ((isUnit_E (K := K) l e).pow η).smul_left_cancel.1 ?_
    rw [← D.desc.act_E_pow_smul, hEL, hWinv g]
  have key : ∀ n, ((l : K) ^ n)⁻¹ • ((f n : Vec K a ι) - L) ∈ D.Y' := fun n => by
    refine (D.mem_Y'_iff_coeff).2 ⟨?_, fun g => ?_, fun τ i k hk => ?_⟩
    · rw [smul_comm, smul_sub, hEL]
      exact pow_l_inv_smul_mem_M (hW n)
    · rw [map_smul, map_sub, (hfY n).2.1 g, hLinv g]
    · have hdv : (X : K⟦X⟧) ^ e ∣ (((l : K) ^ n)⁻¹ • ((f n : Vec K a ι) - L)) τ i := by
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_C_mul]
        refine Dvd.dvd.mul_left (dvd_sub (X_pow_dvd_iff.2 fun k hk => (hfY n).2.2 τ i k hk) ?_) _
        simp only [hL_def, Pi.smul_apply, smul_eq_mul]
        exact Dvd.dvd.mul_left (hWlow τ i) _
      exact X_pow_dvd_iff.1 hdv k hk
  have hLmem : L ∈ D.Y' := by
    have := sub_mem (f 0).2 (key 0)
    rwa [pow_zero, inv_one, one_smul, sub_sub_cancel] at this
  refine ⟨⟨L, hLmem⟩, fun n => (D.smodEq_Y'_iff _ _ n).2 ⟨_, key n, ?_⟩⟩
  exact (smul_inv_smul₀ (hl0 n) _).symm⟩

end BKDat

theorem BKDat.isAdicComplete_Y' : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
    [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H),
    IsAdicComplete (Ideal.span {(l : O)}) D.Y' := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact { toIsHausdorff := D.isHausdorff_Y', toIsPrecomplete := D.isPrecomplete_Y' }

end GlobalTheory.BK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemisimpleRepOfIsSemisimpleRingRange
section
open Formalism.MainNotions.N

namespace GlobalTheory

theorem isSSRep_of_isSemisimpleRing_range :
    ∀ (Γ k : Type) [Group Γ] [Field k] (d : ℕ) (ρ : MonoidAlgebra k Γ →ₐ[k] Matrix (Fin d) (Fin d) k),
      IsSemisimpleRing ρ.range → IsSSRep ((ρ.toMonoidHom.comp (MonoidAlgebra.of k Γ)).toHomUnits) := by
  intro Γ k _ _ d ρ hss W hW

  have hB : ∀ x : MonoidAlgebra k Γ, ∀ v ∈ W, (ρ x).mulVec v ∈ W := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g => intro v hv; exact hW g v hv
    | add x y hx hy =>
      intro v hv; rw [map_add, Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
    | smul c x hx =>
      intro v hv; rw [map_smul, Matrix.smul_mulVec]; exact W.smul_mem c (hx v hv)
  let WB : Submodule ρ.range (Fin d → k) :=
    { carrier := W
      add_mem' := W.add_mem
      zero_mem' := W.zero_mem
      smul_mem' := by
        rintro ⟨b, x, rfl⟩ v hv
        exact hB x v hv }
  have hWB : WB.restrictScalars k = W := by ext v; rfl
  obtain ⟨WB', hc⟩ := exists_isCompl WB
  refine ⟨WB'.restrictScalars k, ?_, ?_⟩
  · intro g v hv
    have hmem : ρ (MonoidAlgebra.of k Γ g) ∈ ρ.range := ⟨_, rfl⟩
    exact WB'.smul_mem ⟨_, hmem⟩ hv
  · rw [← hWB]
    exact hc.map (Submodule.restrictScalarsLatticeHom k ρ.range (Fin d → k))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JHypMemInducedFourierWeyl
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.HypJ

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) →
    ∀ φ', IsTest φ' → A.InI (A.jHyp μK ψ φ') ∧
      ∀ h, A.jHyp μK ψ (A.fourK μK ψ φ') h = A.jHyp μK ψ φ' (h * wS A.K) := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ
  have hH : μK.IsAddHaarMeasure := hsd.1
  have hT := GlobalTheory.T.partialFourier_etaleKProd_locallyConstantCompactSupport F E A ψ hψ μK hH φ' hφ
  refine ⟨⟨?_, fun z s g => GlobalTheory.T.jHyp_unipotent_torus_equivariance F E A μK hH ψ φ' z s g⟩, ?_⟩
  · obtain ⟨U, hU, hk⟩ := GlobalTheory.T.test_function_locally_invariant A.K _ hT
    refine ⟨U, hU, fun g k hkU => ?_⟩
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have := hk k hkU (t * g 1 0) (t * g 1 1)
    simp only at this
    have e1 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 0 =
        g 1 0 * k 0 0 + g 1 1 * k 1 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have e2 : ((g * k : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 1 =
        g 1 0 * k 0 1 + g 1 1 * k 1 1 := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [e1, e2]
    rw [← this]; congr 2 <;> ring
  · intro h
    have key : ∀ c u, A.tilde μK ψ (A.fourK μK ψ φ') c u = A.tilde μK ψ φ' (-u) c := by
      intro c u
      have hG := GlobalTheory.TestFn.slice_test _ hT c
      have := hsd.2 _ hG u
      rw [← this]
      unfold Et.tilde fourB
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only
      rw [GlobalTheory.T.fourierEtaleK_eq_integral_partialFourier F E A ψ hψ μK hH φ' hφ b c]
      unfold fourB Et.tilde Et.kerK
      rw [mul_comm u b]
    unfold Et.jHyp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [key]
    congr 2
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]; simp [wS]

end GlobalTheory.JR.HypJ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeProjectionBaseChangeDvrComm
section
open Formalism.BasicNotions Formalism.L2 NumberField IsDedekindDomain Module

namespace GlobalTheory

theorem projection_span_extend_scalars
    (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [FiniteDimensional K V] [AddCommGroup V'] [Module (FractionRing O) V']
    [Module O V'] [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V') (ι : Type) (b : Basis ι K V) :
    LinearIndependent (FractionRing O) (fun a => iV (b a)) →
    (∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) →
    ∀ (A : Submodule (𝓞 K) V) (U U' : Submodule K V), IsCompl U U' →
    Submodule.span O (iV '' ((U.restrictScalars (𝓞 K) ⊓ (A ⊔ U'.restrictScalars (𝓞 K)) :
        Submodule (𝓞 K) V) : Set V)) =
      (Submodule.span (FractionRing O) (iV '' (U : Set V))).restrictScalars O ⊓
        (Submodule.span O (iV '' (A : Set V)) ⊔
          (Submodule.span (FractionRing O) (iV '' (U' : Set V))).restrictScalars O) := by
  intro hli _ A U U' hUU'
  set F := FractionRing O

  let p : V →ₗ[K] V := U.subtype ∘ₗ U.projectionOnto U' hUU'
  have hpU : ∀ u ∈ U, p u = u := fun u hu => by
    have h := Submodule.projectionOnto_apply_left hUU' ⟨u, hu⟩
    show ((U.projectionOnto U' hUU') ((⟨u, hu⟩ : U) : V) : V) = u
    rw [h]
  have hpU' : ∀ u ∈ U', p u = 0 := fun u hu => by
    have h := Submodule.projectionOnto_apply_right hUU' ⟨u, hu⟩
    show ((U.projectionOnto U' hUU') ((⟨u, hu⟩ : U') : V) : V) = 0
    rw [h]; rfl
  have hpmem : ∀ v, p v ∈ U := fun v => by simp [p]
  have hdec : ∀ v, ∃ u ∈ U, ∃ u' ∈ U', u + u' = v := fun v => by
    have : v ∈ U ⊔ U' := by rw [hUU'.sup_eq_top]; trivial
    exact Submodule.mem_sup.mp this
  have hpdiff : ∀ v, p v - v ∈ U' := fun v => by
    obtain ⟨u, hu, u', hu', rfl⟩ := hdec v
    rw [map_add, hpU u hu, hpU' u' hu', add_zero]
    simpa using U'.neg_mem hu'

  let W : Submodule F V' := Submodule.span F (Set.range fun a => iV (b a))
  let f : W →ₗ[F] V' := (Basis.span hli).constr F (fun a => iV (p (b a)))
  obtain ⟨q, hq⟩ := LinearMap.exists_extend f
  have hqi : ∀ v, q (iV v) = iV (p v) := by
    have : (q.comp iV : V →ₛₗ[e] V') = iV.comp p := by
      refine b.ext fun a => ?_
      have hmem : iV (b a) ∈ W := Submodule.subset_span ⟨a, rfl⟩
      have h1 : q (iV (b a)) = f ⟨iV (b a), hmem⟩ := by
        rw [← hq]; rfl
      have h2 : (⟨iV (b a), hmem⟩ : W) = Basis.span hli a := by
        rw [Basis.span_apply]
      simp only [LinearMap.comp_apply]
      rw [h1, h2, Basis.constr_basis]
    intro v
    exact congrArg (fun g => g v) this
  have hqU : ∀ x ∈ Submodule.span F (iV '' (U : Set V)), q x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hqi, hpU u hu]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  have hqU' : ∀ x ∈ Submodule.span F (iV '' (U' : Set V)), q x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      rw [hqi, hpU' u hu, map_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem] at hw
    obtain ⟨hwU, hwA⟩ := hw
    obtain ⟨a, ha, u', hu', rfl⟩ := Submodule.mem_sup.mp hwA
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact Submodule.subset_span ⟨_, hwU, rfl⟩
    · rw [map_add]
      refine Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) ?_
      exact Submodule.subset_span ⟨u', hu', rfl⟩
  · intro x hx
    obtain ⟨hxU, hxs⟩ := Submodule.mem_inf.mp hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxs
    have hxq : q (y + z) = y + z := hqU _ hxU
    rw [map_add, hqU' z hz, add_zero] at hxq
    rw [← hxq]
    have hmap : q y ∈ Submodule.map (q.restrictScalars O) (Submodule.span O (iV '' (A : Set V))) :=
      ⟨y, hy, rfl⟩
    rw [Submodule.map_span] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨p a, ?_, (hqi a).symm⟩
    simp only [SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]
    refine ⟨hpmem a, ?_⟩
    have : p a = a + (p a - a) := by abel
    rw [this]
    exact Submodule.add_mem_sup ha (hpdiff a)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRigidFunctionsClosedDiscOfAdicLimit
section
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory

theorem mem_R_of_adic_limit (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧)
    (hs : ∀ n, s n ∈ R O K l k) (hf : ∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n)
    (ht : Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0)) : f ∈ R O K l k := by
  rw [mem_R]
  have hr : ∀ m : ℕ, 0 ≤ rad l k ^ m := fun m => pow_nonneg (rad_nonneg l k) m
  have hc : ∀ m, coeff m f = coeff m (s m) := fun m => by
    have := X_pow_dvd_iff.1 (hf m) m (Nat.lt_succ_self m)
    rwa [map_sub, sub_eq_zero] at this
  rw [Metric.tendsto_atTop] at ht ⊢
  intro ε hε
  obtain ⟨j, hj⟩ := ht ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (mem_R.1 (hs j)) ε hε
  refine ⟨max j N, fun m hm => ?_⟩
  have key : ∀ t, j ≤ t → ‖coeff m (s t)‖ * rad l k ^ m < ε := by
    intro t h
    induction t, h using Nat.le_induction with
    | base =>
      have := hN m (le_of_max_le_right hm)
      rw [Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans_lt this
    | succ t h ih =>
      have h1 := hj t h
      rw [Real.dist_eq, sub_zero] at h1
      have h2 : ‖coeff m (s (t + 1) - s t)‖ * rad l k ^ m < ε :=
        (le_normR (O := O) (sub_mem (hs (t + 1)) (hs t)) m).trans_lt ((le_abs_self _).trans_lt h1)
      have h3 : coeff m (s (t + 1)) = coeff m (s t) + coeff m (s (t + 1) - s t) := by
        rw [map_sub]; ring
      rw [h3]
      refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (hr m)).trans_lt ?_
      rw [max_mul_of_nonneg _ _ (hr m)]
      exact max_lt ih h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hr m)), hc]
  exact key m (le_of_max_le_left hm)

end GlobalTheory
end

