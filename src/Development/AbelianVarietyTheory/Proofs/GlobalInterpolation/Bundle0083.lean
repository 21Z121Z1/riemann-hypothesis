import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0015
import Formalism.GradedWeylDivisibility.FinalC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0014
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0078
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValueLatticeAddSubgroupSmulMoveLaws
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RenameMemDualWeyl
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.SubstMem

open Formalism.GradedWeylDivisibility

variable {K : Type} [Field K]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in

theorem _root_.GlobalTheory.SubstMem.rename_mem_dualWeyl {a b : ℕ} (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ)
    (h1 : ∀ i, ν' (Fin.castLE hab i) = ν i) (h2 : ∀ j : Fin b, a ≤ (j : ℕ) → ν' j = 0)
    (f : MvPolynomial (Fin a × Fin a) K) (hf : f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K a a ν) :
    rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K b b ν' := by
  rw [_root_.Formalism.GradedWeylDivisibility.mem_dualWeyl_iff] at hf ⊢
  obtain ⟨hhom, hinv⟩ := hf
  refine ⟨?_, ?_⟩
  · intro d hd
    have hinj : Function.Injective (Prod.map (Fin.castLE hab) (Fin.castLE hab)) :=
      (Fin.castLE_injective hab).prodMap (Fin.castLE_injective hab)
    have hmem : d ∈ (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f).support :=
      mem_support_iff.2 hd
    rw [support_rename_of_injective hinj, Finset.mem_image] at hmem
    obtain ⟨d0, hd0, rfl⟩ := hmem
    have h0 := hhom (mem_support_iff.1 hd0)
    rw [Finsupp.weight_apply] at h0
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul])]
    funext k
    by_cases hk : (k : ℕ) < a
    · have hk' : k = Fin.castLE hab ⟨k, hk⟩ := Fin.ext rfl
      rw [hk', h1, ← h0]
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp [_root_.Formalism.GradedWeylDivisibility.colW, Pi.single_apply]
      simp only [Fin.ext_iff, Fin.coe_castLE]
    · rw [h2 k (not_lt.1 hk)]
      simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_eq_zero fun v _ => ?_
      have hne : Fin.castLE hab v.2 ≠ k := by
        intro h; apply hk; rw [← h]; simp
      simp [_root_.Formalism.GradedWeylDivisibility.colW, Pi.single_apply, Ne.symm hne]
  · intro l j hlj
    by_cases hj : (j : ℕ) < a
    · have hl : (l : ℕ) < a := lt_trans hlj hj
      obtain ⟨l', rfl⟩ : ∃ l' : Fin a, Fin.castLE hab l' = l := ⟨⟨l, hl⟩, Fin.ext rfl⟩
      obtain ⟨j', rfl⟩ : ∃ j' : Fin a, Fin.castLE hab j' = j := ⟨⟨j, hj⟩, Fin.ext rfl⟩
      have key : (_root_.Formalism.GradedWeylDivisibility.colAddGen K (Fin.castLE hab l') (Fin.castLE hab j')).comp
          (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) =
          (rename (Option.map (Prod.map (Fin.castLE hab) (Fin.castLE hab)))).comp
            (_root_.Formalism.GradedWeylDivisibility.colAddGen K (r := a) l' j') := by
        apply MvPolynomial.algHom_ext
        rintro ⟨v1, v2⟩
        by_cases hv : v2 = j'
        · subst hv
          simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, Prod.map_fst,
            if_pos rfl]
          simp only [ite_true, if_true, map_add, map_mul, rename_X]
          rfl
        · have hv' : Fin.castLE hab v2 ≠ Fin.castLE hab j' :=
            fun h => hv (Fin.castLE_injective hab h)
          simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, Prod.map_fst,
            if_neg hv, if_neg hv']
          rfl
      have e := DFunLike.congr_fun key f
      simp only [AlgHom.comp_apply] at e
      rw [e, hinv l' j' (show l' < j' from hlj), rename_rename, rename_rename]
      rfl
    · have key : (_root_.Formalism.GradedWeylDivisibility.colAddGen K l j).comp (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) =
          (rename some).comp (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab))) := by
        apply MvPolynomial.algHom_ext
        intro v
        have hne : Fin.castLE hab v.2 ≠ j := by
          intro h; apply hj; rw [← h]; exact v.2.isLt
        simp only [AlgHom.comp_apply, rename_X, _root_.Formalism.GradedWeylDivisibility.colAddGen, aeval_X, Prod.map_snd, if_neg hne]
      exact DFunLike.congr_fun key f

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in

theorem _root_.GlobalTheory.SubstMem.det_pow_mem (a m : ℕ) :
    _root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl ^ m ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl K a a (fun _ => m) := by
  refine _root_.Formalism.GradedWeylDivisibility.dualWeyl_of_eq (_root_.Formalism.GradedWeylDivisibility.dualWeyl_pow (_root_.Formalism.GradedWeylDivisibility.initMinor_mem (R := K) (id : Fin a → Fin a) le_rfl) m) ?_
  funext i
  simp [_root_.Formalism.GradedWeylDivisibility.initW]

def padRows {a b : ℕ} (A : Matrix (Fin a) (Fin b) K) : Matrix (Fin b) (Fin b) K :=
  fun α β => if h : (α : ℕ) < a then A ⟨α, h⟩ β else 0

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
theorem _root_.GlobalTheory.SubstMem.substAdj_blockEmb {ι : Type} {a b : ℕ} (hab : a ≤ b)
    (ap : ι → Matrix (Fin a) (Fin b) K) (τ : ι) (f : MvPolynomial (Fin a × Fin a) K) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab ap (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ f) =
      _root_.Formalism.GradedWeylDivisibility.blockEmb K τ (_root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))
        (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)) f)) := by
  have key : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab ap).comp (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ) = (_root_.Formalism.GradedWeylDivisibility.blockEmb K τ).comp
      ((_root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))).comp
        (rename (Prod.map (Fin.castLE hab) (Fin.castLE hab)))) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj, _root_.Formalism.GradedWeylDivisibility.blockEmb, _root_.Formalism.GradedWeylDivisibility.rowAct, _root_.GlobalTheory.SubstMem.padRows, map_sum]
  exact DFunLike.congr_fun key f

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem DomWeight_detShift_eq_w_last {N : ℕ} (l : _root_.Formalism.BasicNotions.DomWeight N) (h : 0 < N) :
    l.detShift = l.w ⟨N - 1, by omega⟩ := by
  unfold _root_.Formalism.BasicNotions.DomWeight.detShift
  rw [dif_pos h]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem DomWeight_detShift_le_w {N : ℕ} (l : _root_.Formalism.BasicNotions.DomWeight N) (i : Fin N) : l.detShift ≤ l.w i := by
  rw [DomWeight_detShift_eq_w_last l (Fin.pos i)]
  exact l.anti (Fin.le_def.2 (by simp; omega))

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem isWeightedHomogeneous_colW_rowAct_of_isWeightedHomogeneous {R : Type} [CommRing R] {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) {f : MvPolynomial (Fin r × Fin n) R} {ν : Fin n → ℕ}
    (hf : IsWeightedHomogeneous (_root_.Formalism.GradedWeylDivisibility.colW r n) f ν) :
    IsWeightedHomogeneous (_root_.Formalism.GradedWeylDivisibility.colW r n) (_root_.Formalism.GradedWeylDivisibility.rowAct R g f) ν := by
  rw [← mem_weightedHomogeneousSubmodule]
  rw [← support_sum_monomial_coeff f, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  rw [mem_weightedHomogeneousSubmodule, ← hf (mem_support_iff.1 hd)]
  have e : _root_.Formalism.GradedWeylDivisibility.rowAct R g (monomial d (coeff d f)) =
      C (coeff d f) * d.prod (fun v k => (_root_.Formalism.GradedWeylDivisibility.rowAct R g (X v)) ^ k) := by
    simp only [_root_.Formalism.GradedWeylDivisibility.rowAct, aeval_monomial, aeval_X, algebraMap_eq]
  rw [e, Finsupp.weight_apply, ← zero_add (d.sum fun i c => c • _root_.Formalism.GradedWeylDivisibility.colW r n i)]
  exact (isWeightedHomogeneous_C _ _).mul
    (IsWeightedHomogeneous.prod _ _ _ fun v _ => (_root_.Formalism.GradedWeylDivisibility.rowAct_X_isWH g v).pow (d v))

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem rowAct_mem_dualWeyl_of_mem_dualWeyl {R : Type} [CommRing R] {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) {ν : Fin n → ℕ} {f : MvPolynomial (Fin r × Fin n) R}
    (hf : f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl R r n ν) : _root_.Formalism.GradedWeylDivisibility.rowAct R g f ∈ _root_.Formalism.GradedWeylDivisibility.dualWeyl R r n ν := by
  rw [_root_.Formalism.GradedWeylDivisibility.mem_dualWeyl_iff] at hf ⊢
  refine ⟨isWeightedHomogeneous_colW_rowAct_of_isWeightedHomogeneous g hf.1, fun l j hlj => ?_⟩
  rw [_root_.Formalism.GradedWeylDivisibility.colAddGen_rowAct, hf.2 l j hlj, ← _root_.Formalism.GradedWeylDivisibility.rename_rowAct]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in
private theorem frDet_eq_blockEmb_initMinor_id {K : Type} [Field K] {ι : Type} (a : ℕ) (τ : ι) :
    _root_.Formalism.L2.Ker.frDet K a τ = _root_.Formalism.GradedWeylDivisibility.blockEmb K τ (_root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl) := by
  simp only [_root_.Formalism.L2.Ker.frDet, _root_.Formalism.GradedWeylDivisibility.initMinor, AlgHom.map_det]
  congr 1
  ext p q
  simp [_root_.Formalism.GradedWeylDivisibility.blockEmb]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] in

theorem _root_.GlobalTheory.SubstMem.substAdj_sharp_mem : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι]
    (a b : ℕ) (hab : a < b) (lam : ι → _root_.Formalism.BasicNotions.DomWeight a) (lam' : ι → _root_.Formalism.BasicNotions.DomWeight b) (s s' : ι → ℤ)
    (n : ι → ℕ), _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.WtCompat hab lam lam' s s' n →
    ∀ (ap : ι → Matrix (Fin a) (Fin b) K), ∀ P ∈ _root_.Formalism.L2.DIV.VV K lam,
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.substAdj hab.le ap (_root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.sharp n P) ∈ _root_.Formalism.L2.DIV.VV K lam' := by
  intro K _ ι _ a b hab lam lam' s s' n hc ap P hP
  obtain ⟨hc1, hc2, hc3⟩ := hc
  have hd' : ∀ τ, (lam' τ).detShift = -s τ := fun τ => by
    rw [DomWeight_detShift_eq_w_last _ (by omega)]
    exact hc2 τ _ (by simp; omega)
  have hw1 : ∀ τ i, (lam' τ).natW (Fin.castLE hab.le i) = (lam τ).natW i + n τ := by
    intro τ i
    have e1 := hc1 τ i
    have e2 := hc3 τ
    have e3 := DomWeight_detShift_le_w (lam τ) i
    have e4 := hd' τ
    simp only [_root_.Formalism.BasicNotions.DomWeight.natW]
    omega
  have hw2 : ∀ τ (j : Fin b), a ≤ (j : ℕ) → (lam' τ).natW j = 0 := by
    intro τ j hj
    have e1 := hc2 τ j hj
    have e4 := hd' τ
    simp only [_root_.Formalism.BasicNotions.DomWeight.natW]
    omega
  have hsharp : ∀ Q : _root_.Formalism.L2.DIV.Pol K ι a, _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.sharp n Q = Q * ∏ τ, _root_.Formalism.L2.Ker.frDet K a τ ^ n τ :=
    fun Q => rfl
  unfold _root_.Formalism.L2.DIV.VV _root_.Formalism.GradedWeylDivisibility.tensorLat at hP ⊢
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    rw [hsharp, ← Finset.prod_mul_distrib, map_prod]
    refine Submodule.subset_span ⟨fun τ => _root_.Formalism.GradedWeylDivisibility.rowAct K (_root_.GlobalTheory.SubstMem.padRows (ap τ))
      (rename (Prod.map (Fin.castLE hab.le) (Fin.castLE hab.le))
        (F τ * _root_.Formalism.GradedWeylDivisibility.initMinor K (id : Fin a → Fin a) le_rfl ^ n τ)), fun τ => ?_, ?_⟩
    · refine rowAct_mem_dualWeyl_of_mem_dualWeyl _ ?_
      refine _root_.GlobalTheory.SubstMem.rename_mem_dualWeyl hab.le ((lam τ).natW + fun _ => n τ) _
        (fun i => by simp [hw1]) (hw2 τ) _ ?_
      exact _root_.Formalism.GradedWeylDivisibility.dualWeyl_mul (hF τ) (_root_.GlobalTheory.SubstMem.det_pow_mem a (n τ))
    · refine Finset.prod_congr rfl fun τ _ => ?_
      rw [frDet_eq_blockEmb_initMinor_id, ← map_pow, ← map_mul, _root_.GlobalTheory.SubstMem.substAdj_blockEmb]
  | zero => simp [hsharp]
  | add x y _ _ hx hy =>
    rw [hsharp, add_mul, map_add]
    exact add_mem (by rw [← hsharp]; exact hx) (by rw [← hsharp]; exact hy)
  | smul c x _ hx =>
    rw [hsharp, smul_mul_assoc, map_smul]
    exact Submodule.smul_mem _ c (by rw [← hsharp]; exact hx)

end GlobalTheory.SubstMem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StepBoxIffStepSuppDeg
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MoveCompare

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions
open GlobalTheory.IndefiniteRowSideFullHecke

section Clauses

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mulLat_le_divLat {H : Type} [AddCommGroup H] [Module (𝓞 E) H] (cA cB : ℕ) (M : Submodule (𝓞 E) H) :
    mulLat cB M ≤ divLat cA M := by
  rintro _ ⟨z, hz, rfl⟩
  exact M.smul_mem _ (M.smul_mem _ hz)

open Classical in

theorem inRange_indicator (K : Type) [Field K] {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) :
    MovementLaw.InRangeOf S cA cB N N' (fun x => if x ∈ divLat cA (homAt S N N') then (1 : K) else 0) := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · by_contra h
    exact hx (if_neg h)
  · have hy' := mulLat_le_divLat cA cB _ hy
    have : x + y ∈ divLat cA (homAt S N N') ↔ x ∈ divLat cA (homAt S N N') := Submodule.add_mem_iff_left _ hy'
    simp only [this]

end Clauses

open Classical in

theorem degAt_eq {X : Fields} {a b : ℕ} (m : DVar X.Tau a b →₀ ℕ) (τ : X.Tau) :
    IndexExponentDegree.degAt m τ = ∑ k ∈ m.support.filter (fun k => k.1 = τ), m k := by
  unfold IndexExponentDegree.degAt
  rw [Finset.sum_filter, Finset.sum_subset (Finset.subset_univ m.support) (by
    intro k _ hk
    simp [Finsupp.notMem_support_iff.1 hk]), Fintype.sum_prod_type, Finset.sum_eq_single τ]
  · rw [Fintype.sum_prod_type]
    simp
  · intro σ _ hσ
    simp [hσ]
  · simp

theorem nuW_detShift_nonneg {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    0 ≤ (W.nuW u (i + 1) τ).detShift := by
  have hpos : 0 < R.N i := R.N_pos i
  have hlt : R.N i < R.N R.m := by
    unfold Ranks.N
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right hi (Nat.succ_pos R.t)) _
  have hb : Examples₂.blkN R (R.N i) = i := by
    unfold Examples₂.blkN Ranks.N
    rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel _ (Nat.succ_pos _)]
  have h1 : Examples₂.wtN (W.hc u τ) (R.N i) = -wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1) := by
    unfold Examples₂.wtN
    rw [dif_neg (by unfold Ranks.N; omega), dif_pos (by rw [hb]; exact hi)]
    simp only [hb]
  have h2 := Examples₂.wtN_anti (W.hc u τ) (Nat.sub_le (R.N i) 1) hlt
  have h3 := Examples₂.lamOf_eq (W.hc u τ) i hi.le ⟨R.N i - 1, by omega⟩
  rw [Examples₂.wtQ_eq_wtN] at h3
  have h4 : (W.nuW u (i + 1) τ).detShift =
      (Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ + ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ := by
    unfold DomWeight.detShift
    rw [dif_pos (show 0 < R.N (i + 1 - 1) from hpos)]
    simp only [Wts.nuW, shiftW, Wts.lamN, RowPar.eAt, RowPar.of, Nat.add_sub_cancel, hi, dif_pos]
    rfl
  rw [h4]
  have h5 : -(Examples₂.lamOf (W.hc u τ) i).w ⟨R.N i - 1, by omega⟩ ≤ ⌊wG R ((W.hc u τ).e ⟨i, hi⟩) (i + 1)⌋ := by
    rw [Int.le_floor]
    push_cast
    rw [h3]
    simp only at h2 ⊢
    linarith
  omega

theorem degNu_eq {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau) :
    IndexExponentDegree.degNu (W.lamTrue u i) (nuLast W u i) τ = ∑ k, (W.nuW u (i + 1) τ).w k := by
  have hpos : 0 < R.N i := R.N_pos i
  unfold IndexExponentDegree.degNu nuLast
  rw [Int.toNat_of_nonneg (nuW_detShift_nonneg W u hi τ)]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold DomWeight.detShift
  rw [dif_pos (show 0 < R.N (i + 1 - 1) from hpos), dif_pos hpos]
  show ((W.lamN u i τ).w s + _) - ((W.lamN u i τ).w ⟨R.N i - 1, _⟩ + _) + ((W.lamN u i τ).w ⟨R.N i - 1, _⟩ + _) =
    (W.lamN u i τ).w s + _
  ring

theorem delta_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : δ ≠ 0 := by
  rintro rfl
  have h1 : B.L.ω₁ ∈ TaylorLogMetric.lamOf D cc 0 := by
    rw [← B.lat]
    exact B.L.ω₁_mem_lattice
  have h2 : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    unfold TaylorLogMetric.lamOf
    rw [AddSubgroup.closure_le]
    rintro w ⟨c, -, rfl⟩
    simp
  have h3 : B.L.ω₁ = 0 := h2 h1
  exact B.L.indep.ne_zero 0 (by simpa using h3)

section Jets

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E))) (cA cB : ℕ)

def JetsAll (deg : X.Tau → ℤ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Prop :=
  ∀ Ξ : HomE X.E a b → X.K, MovementLaw.InRangeOf S cA cB N N' Ξ → MovementLaw.JetsIn A S cB deg N N' Ξ

theorem jetsIn_iff (lam : X.Tau → DomWeight a) (n : X.Tau → ℕ) (deg : X.Tau → ℤ) (h : ∀ τ, IndexExponentDegree.degNu lam n τ = deg τ)
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) :
    IndexExponentDegree.JetsIn A S cA cB lam n N N' ↔ JetsAll A S cA cB deg N N' := by
  constructor
  · intro hJ Ξ hΞ x hx m hm
    refine hJ x (hΞ.1 x hx) m fun τ => ?_
    rw [degAt_eq, h τ, ← hm τ]
  · intro hJ x hx m hm
    refine hJ _ (inRange_indicator X.K S cA cB N N') x (by simp [hx]) m fun τ => ?_
    rw [← h τ, ← hm τ, degAt_eq]

open Classical in

def JetsDeg (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M : ℕ) (deg : X.Tau → ℤ) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x : HomE X.E a b), InRange S M c N N' x →
    ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, ((∑ k ∈ m.support.filter (fun k => k.1 = τ), m k : ℕ) : ℤ) = deg τ) →
      ∃ k : X.K, A.σ₀ k = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd S N N' c x) m

theorem jetsAll_of_deg (deg : X.Tau → ℤ) (h : JetsDeg A a b S (cA * cB) deg) (hB : 0 < cB)
    {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') :
    JetsAll A S cA cB deg N N' := by
  intro Ξ hΞ x hx m hm
  refine h N N' cB x ⟨hN, hN', hB, Dvd.intro_left _ rfl, ?_⟩ m hm
  have h1 : ((cA : ℕ) : 𝓞 X.E) • x ∈ homAt S N N' := hΞ.1 x hx
  show ((cA * cB : ℕ) : 𝓞 X.E) • x ∈ homAt S N N'
  rw [Nat.cast_mul, mul_comm, mul_smul]
  exact Submodule.smul_mem _ _ h1

end Jets

theorem cBof_pos {X : Fields} {Pr : Primes X} (hP : Pr.Ok) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) : 0 < cBof sel mu cst u := by
  unfold cBof
  refine Nat.mul_pos (hP.T_prime u).pos (pow_pos (Finset.prod_pos fun P _ => ?_) _)
  exact Nat.pos_of_ne_zero (by unfold Formalism.L2.Col.qOf; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.1.ne_bot)

abbrev StepSt : Type 1 :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (_ : Wts X Pr.Word R) (_ : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (_ : LocCst X (rowSG Pr sel mu)) (_ : Pr.Word) (_ : Amb X) (_ : ℕ) (b : ℕ) (_ : X.Tau → DomWeight b), Prop

def StepBox : StepSt := fun X Pr R W Ch sel _ mu cst u A i b lam' =>
  ∀ (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b))
    (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K),
    IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' →
    IndexExponentDegree.AgreeOff (Pr.T u) N₁ N₂ → IndexExponentDegree.AgreeOff (Pr.T u) N₁' N₂' →
    IndexExponentDegree.InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
    IndexExponentDegree.InBox (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
    IndexExponentDegree.JetsIn A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₁ N₁' →
    IndexExponentDegree.JetsIn A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (W.lamTrue u i) (nuLast W u i) N₂ N₂' →
    kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
      IndexExponentDegree.moveScal Ch mu u i N₁ N₂ N₁' N₂' •
        kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ

def StepSupp : StepSt := fun X Pr R W Ch sel _ mu cst u A i b lam' =>
  ∀ (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' →
    MovementLaw.AgreeOff (Pr.T u) N₁ N₂ → MovementLaw.AgreeOff (Pr.T u) N₁' N₂' →
  ∀ (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K),
    MovementLaw.InRangeOf (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
    MovementLaw.InRangeOf (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
    MovementLaw.JetsIn A (Sall sel mu u) (cBof sel mu cst u) (fun τ => ∑ k, (W.nuW u (i + 1) τ).w k) N₁ N₁' Ξ →
    MovementLaw.JetsIn A (Sall sel mu u) (cBof sel mu cst u) (fun τ => ∑ k, (W.nuW u (i + 1) τ).w k) N₂ N₂' Ξ →
    kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
      MovementLaw.moveScal Ch mu u i N₁ N₂ N₁' N₂' •
        kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ

def StepAll : StepSt := fun X Pr R W Ch sel _ mu cst u A i b lam' =>
  ∀ (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E (R.N i))) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)),
    IsSdLat N₁ → IsSdLat N₂ → IsSdLat N₁' → IsSdLat N₂' →
    MovementLaw.AgreeOff (Pr.T u) N₁ N₂ → MovementLaw.AgreeOff (Pr.T u) N₁' N₂' →
  ∀ (fr : Frs X.E (R.N i) (rowSG Pr sel mu)) (fr' : Frs X.E b (rowSG Pr sel mu)) (Ξ : HomE X.E (R.N i) b → X.K),
    MovementLaw.InRangeOf (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ N₁' Ξ →
    MovementLaw.InRangeOf (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ N₂' Ξ →
    JetsAll A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (fun τ => ∑ k, (W.nuW u (i + 1) τ).w k) N₁ N₁' →
    JetsAll A (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) (fun τ => ∑ k, (W.nuW u (i + 1) τ).w k) N₂ N₂' →
    kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₁ fr N₁' fr' Ξ =
      MovementLaw.moveScal Ch mu u i N₁ N₂ N₁' N₂' •
        kerOf (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u) N₂ fr N₂' fr' Ξ

def StepField : StepSt := fun _ _ R W _ sel _ mu cst u A i b _ =>
  JetsDeg A (R.N i) b (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (fun τ => ∑ k, (W.nuW u (i + 1) τ).w k)

def OverField (St : StepSt) : StepSt := fun X Pr R W Ch sel S mu cst u A i b lam' =>
  StepField X Pr R W Ch sel S mu cst u A i b lam' → St X Pr R W Ch sel S mu cst u A i b lam'

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (A : Amb X) {i : ℕ} {b : ℕ} (lam' : X.Tau → DomWeight b)

end Step

def OverWide (St : StepSt) : Prop :=
  ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word)
    (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ),
    X.Ok → Pr.Ok → Ch.FromHecke W s.σ₀ → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) →
    s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsChi D χ →
    (∀ P ∈ Sall sel mu u, Nat.Coprime (Ideal.absNorm cc) (Ideal.absNorm P.asIdeal)) →
    ∀ (i : ℕ), i < R.m → ∀ (b : ℕ), b = R.N (i + 1) → ∀ (lam' : X.Tau → DomWeight b),
      St X Pr R W Ch sel S mu cst u (ambOf s B χ cD) i b lam'

def OverNarrow (St : StepSt) : Prop :=
  ∀ (Dt : Dat), Dt.Ok →
  ∀ (D : D7) (s : Seam D Dt.X), s.Ok → s.σ₀ = Dt.sig0 →
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → δ ≠ 0 →
  ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ →
  ∀ (cD : D.what₂.Tau → ℂ)
    (sel : HeightOneSpectrum (𝓞 Dt.X.F) → HeightOneSpectrum (𝓞 Dt.X.E)), IsSel Dt.X sel →
  ∀ (S : Set ℕ), hostS D.host.q D.host.d (Dt.Pr.g 0) (Dt.Pr.g 1) (Set.range Dt.Pr.T ∪ (D.host.small : Set ℕ)) ⊆ S →
  ∀ (mu : Tup Dt.X.F Dt.X.E Dt.X.K S) (cst : LocCst Dt.X (rowSG Dt.Pr sel mu)) (u : Dt.Pr.Word),
    (∀ P ∈ Sall (Pr := Dt.Pr) sel mu u, Nat.Coprime (Ideal.absNorm cc) (Formalism.L2.Col.qOf P)) →
  ∀ (i j : ℕ), j = i + 1 → j ≤ Dt.R.m →
    St Dt.X Dt.Pr Dt.R Dt.W Dt.Ch sel S mu cst u (ambOf s B χ cD) i (Dt.R.N j) (Dt.W.lamTrue u j)

end GlobalTheory.MoveCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowTopsBandBottomsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_card_TT_le_Nstar_and_rhoP_le_and_bT_le : SzRow (fun C D L => ((D.host.TT.card : ℝ) ≤ Nstar L) ∧ (rhoP L C.P.Crho ≤ L.sc.x ^ (-2 : ℝ)) ∧ (∀ t, (L.bT t : ℝ) ≤ L.sc.b' + Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k)) := by
  first | exact @GlobalTheory.EX.szRow_tops_band_bottoms | exact GlobalTheory.EX.szRow_tops_band_bottoms | (intros; apply GlobalTheory.EX.szRow_tops_band_bottoms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ValueLatticeAddSubgroupSmulMoveLawsStatement
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valueLattice_addSubgroup_smul_move_laws : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → ∀ (V : Finset X.A.vT) (p : M.Pt), (0 : M.Val) ∈ Co.valB w V p ∧ (∀ y ∈ Co.valB w V p, ∀ y' ∈ Co.valB w V p, y + y' ∈ Co.valB w V p) ∧ (∀ r ∈ Ow D w, ∀ y ∈ Co.valB w V p, D.what₂.embLL r • y ∈ Co.valB w V p) ∧ ∀ (g : M.G), ∀ y ∈ Co.valB w V p, M.act g y ∈ Co.valB w V (g • p) := by
  first | exact @GlobalTheory.LvT.ValEq.valB_laws | exact GlobalTheory.LvT.ValEq.valB_laws | (intros; apply GlobalTheory.LvT.ValEq.valB_laws <;> assumption)
end

