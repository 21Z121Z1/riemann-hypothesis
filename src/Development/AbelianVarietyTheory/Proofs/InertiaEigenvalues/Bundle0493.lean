import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0461
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0465
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0460
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0462
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelTorsionFreeOfBoundedLeftInverse
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.TorsFree

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_coeff_le_one_of_mul {x g : K⟦X⟧} (hx : ∃ B : ℝ, ∀ n, ‖coeff n x‖ ≤ B)
    (hg : ∀ n, ‖coeff n g‖ ≤ 1) (hg1 : ∃ n, ‖coeff n g‖ = 1) (hgx : ∀ n, ‖coeff n (g * x)‖ ≤ 1) :
    ∀ n, ‖coeff n x‖ ≤ 1 := by
  classical
  obtain ⟨B, hB⟩ := hx
  have hbdd : BddAbove (Set.range fun n => ‖coeff n x‖) := ⟨B, by rintro _ ⟨n, rfl⟩; exact hB n⟩
  set S := ⨆ n, ‖coeff n x‖ with hSdef
  have hxS : ∀ n, ‖coeff n x‖ ≤ S := fun n => le_ciSup hbdd n
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hxS 0)
  set d := Nat.find hg1 with hd
  have hgd : ‖coeff d g‖ = 1 := Nat.find_spec hg1
  have hlt : ∀ i < d, ‖coeff i g‖ < 1 := fun i hi =>
    lt_of_le_of_ne (hg i) (Nat.find_min hg1 hi)
  set θ : NNReal := (Finset.range d).sup fun i => ‖coeff i g‖₊ with hθdef
  have hθ1 : θ < 1 := by
    rw [hθdef, Finset.sup_lt_iff (by simp)]
    intro i hi
    have := hlt i (Finset.mem_range.1 hi)
    rw [← NNReal.coe_lt_coe]; simpa using this
  have hθi : ∀ i < d, ‖coeff i g‖ ≤ (θ : ℝ) := fun i hi => by
    have : ‖coeff i g‖₊ ≤ θ := Finset.le_sup (f := fun i => ‖coeff i g‖₊) (Finset.mem_range.2 hi)
    exact_mod_cast this
  have hθ0 : (0 : ℝ) ≤ θ := θ.2
  set Mx := max 1 ((θ : ℝ) * S) with hMx
  have hM0 : 0 ≤ Mx := le_trans zero_le_one (le_max_left _ _)
  have key : ∀ n, ‖coeff n x‖ ≤ Mx := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    have hmem : (d, n) ∈ Finset.HasAntidiagonal.antidiagonal (n + d) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; exact add_comm d n
    have hc := coeff_mul (n + d) g x
    rw [← Finset.add_sum_erase _ _ hmem] at hc
    have hrest : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (n + d)).erase (d, n), coeff p.1 g * coeff p.2 x‖ ≤ Mx := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hM0 fun p hp => ?_
      obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [norm_mul]
      rcases lt_trichotomy p.1 d with h | h | h
      · calc ‖coeff p.1 g‖ * ‖coeff p.2 x‖ ≤ θ * S :=
            mul_le_mul (hθi _ h) (hxS _) (norm_nonneg _) hθ0
          _ ≤ Mx := le_max_right _ _
      · exact absurd (Prod.ext h (by omega)) hne
      · have hj : p.2 < n := by omega
        calc ‖coeff p.1 g‖ * ‖coeff p.2 x‖ ≤ 1 * Mx :=
            mul_le_mul (hg _) (ih _ hj) (norm_nonneg _) zero_le_one
          _ = Mx := one_mul _
    have heq : coeff d g * coeff n x = coeff (n + d) (g * x) -
        ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (n + d)).erase (d, n), coeff p.1 g * coeff p.2 x := by
      rw [hc]; ring
    have : ‖coeff n x‖ = ‖coeff d g * coeff n x‖ := by rw [norm_mul, hgd, one_mul]
    rw [this, heq, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_neg]; exact hrest))
    exact (hgx _).trans (le_max_left _ _)
  have hSM : S ≤ Mx := ciSup_le key
  have hS1 : S ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : S ≤ θ * S := by
      rcases le_total 1 ((θ : ℝ) * S) with h3 | h3
      · rwa [hMx, max_eq_right h3] at hSM
      · rw [hMx, max_eq_left h3] at hSM; linarith
    have : (1 - (θ : ℝ)) * S ≤ 0 := by linarith
    have h4 : (0 : ℝ) < 1 - θ := by have := (NNReal.coe_lt_coe.2 hθ1); simp at this; linarith
    nlinarith
  exact fun n => (hxS n).trans hS1

end GlobalTheory.BK.TorsFree

namespace GlobalTheory.BK.Hom

open GlobalTheory.BK.TorsFree

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fact l.Prime]
  {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

theorem mem_imM_of_smul_mem (F : Hom P Q)
    (hg : ∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧
      Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧))
    (hl : ∀ τ, (1 : K⟦X⟧) ∈ F.ldivSet τ) {v : Vec K a κ} (hv : v ∈ Q.M) {f : K⟦X⟧}
    (hf0 : f ≠ 0) (hfv : f • v ∈ F.imM) : v ∈ F.imM := by
  unfold imM at hfv ⊢
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.1 hfv
  rw [LinearMap.restrictScalars_apply] at hwv
  choose Y hYb hY using fun τ => (hl τ).2
  choose Y0 g hY0A hg1 hY0 using hg
  have hv' : ∀ τ i, v τ i ∈ A O K := fun τ => mem_tot.1 hv τ
  let x : Vec K a ι := fun τ => Y τ *ᵥ v τ
  have hfx : ∀ τ, f • x τ = w τ := by
    intro τ
    have h1 : f • v τ = F.mat τ *ᵥ w τ := by rw [← app_apply, hwv]; rfl
    change f • (Y τ *ᵥ v τ) = w τ
    rw [← Matrix.mulVec_smul, h1, Matrix.mulVec_mulVec, hY τ, one_smul, Matrix.one_mulVec]
  have hFx : F.app x = v := by
    funext τ i
    have h2 : f • F.app x τ = f • v τ := by
      rw [app_apply, ← Matrix.mulVec_smul, hfx τ, ← app_apply, hwv]; rfl
    exact mul_left_cancel₀ hf0 (congrFun h2 i)
  have hbx : ∀ τ i, ∃ B : ℝ, ∀ n, ‖coeff n (x τ i)‖ ≤ B := by
    intro τ i
    obtain ⟨c, hc⟩ := hYb τ
    refine ⟨max c 0, fun n => ?_⟩
    change ‖coeff n (∑ j, Y τ i j * v τ j)‖ ≤ max c 0
    rw [map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (le_max_right _ _) fun j _ => ?_
    have := norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
      (le_max_right c 0) zero_le_one (f := Y τ i j) (g := v τ j)
      (fun m => by rw [mul_one]; exact (hc i j m).trans (le_max_left _ _))
      (fun m => by rw [mul_one]; exact hv' τ j m) n
    rwa [mul_one, mul_one] at this
  have hgA : ∀ τ (i : ι), ∀ n, ‖coeff n (g τ)‖ ≤ 1 := by
    intro τ i
    have h5 : g τ = (Y0 τ * F.mat τ) i i := by rw [hY0 τ]; simp
    rw [h5]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY0A τ i j) (F.mem τ j i)
  have hgx : ∀ τ i, ∀ n, ‖coeff n (g τ * x τ i)‖ ≤ 1 := by
    intro τ i
    have h3 : g τ • x τ = Y0 τ *ᵥ v τ := by
      conv_rhs => rw [← hFx]
      rw [app_apply, Matrix.mulVec_mulVec, hY0 τ]
      first
        | rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
        | rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    have h4 : g τ * x τ i = (Y0 τ *ᵥ v τ) i := by rw [← h3]; rfl
    rw [h4]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY0A τ i j) (hv' τ j)
  have hxA : x ∈ P.M := mem_tot.2 fun τ i =>
    norm_coeff_le_one_of_mul (hbx τ i) (hgA τ i) (hg1 τ) (hgx τ i)
  exact Submodule.mem_map.2 ⟨x, hxA, by rw [LinearMap.restrictScalars_apply]; exact hFx⟩

end GlobalTheory.BK.Hom

theorem GlobalTheory.BK.Hom.coker_torsionFree : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), (∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → (∀ τ, (1 : K⟦X⟧) ∈ F.ldivSet τ) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F hg hl v hv f _ hf0 hfv
  exact F.mem_imM_of_smul_mem hg hl hv hf0 hfv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversActionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.action_of_covers : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (k : GQ l) (γ : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) ∧ k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 := by
  first | exact @GlobalTheory.BKGal.covers_action | exact GlobalTheory.BKGal.covers_action | (intros; apply GlobalTheory.BKGal.covers_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversOfActionStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covers_of_action' : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (γ : TameGal ↥LL.1 l e a), ∀ k ∈ ϖ.GKinf, (∀ x : Om l, x ^ l ^ a = x → k x = x ^ l ^ γ.shift.val) → k (ϖ.seq 0) = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 → Covers ↥LL.1 (thetaW a LL) ϖ k γ := by
  first | exact @GlobalTheory.BKGal.covers_of_action | exact GlobalTheory.BKGal.covers_of_action | (intros; apply GlobalTheory.BKGal.covers_of_action <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversTameActsRingEndoWittPowerSeries
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CoverRing

variable {l : ℕ} [hl : Fact l.Prime]

theorem smul_eq_zero_ainf {c : ℤ_[l]} (hc : c ≠ 0) {z : Ainf l} (h : c • z = 0) : z = 0 := by
  have h1 := PadicInt.unitCoeff_spec hc
  rw [h1, Algebra.smul_def, map_mul, map_pow, map_natCast, mul_assoc] at h
  have h2 : (l : Ainf l) ^ c.valuation * z = 0 :=
    ((PadicInt.unitCoeff hc).isUnit.map (algebraMap ℤ_[l] (Ainf l))).mul_right_eq_zero.1 h
  have key : ∀ n : ℕ, ∀ z : Ainf l, (l : Ainf l) ^ n * z = 0 → z = 0 := by
    intro n
    induction n with
    | zero => intro z h; simpa using h
    | succ n ih => intro z h; exact ih z (ainf_torsionFree _ (by rw [← mul_assoc, ← pow_succ']; exact h))
  exact key _ z h2

theorem one_tmul_inj {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Nontrivial O]
    {x y : Ainf l} (h : (1 : O) ⊗ₜ[ℤ_[l]] x = (1 : O) ⊗ₜ[ℤ_[l]] y) : x = y := by
  set b := Module.Free.chooseBasis ℤ_[l] O
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact one_ne_zero (b.repr.injective (by ext i; simp [hc i]))
  have h1 := congrArg (fun w => TensorProduct.lid ℤ_[l] (Ainf l) ((b.coord i).rTensor (Ainf l) w)) h
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Module.Basis.coord_apply] at h1
  rw [← sub_eq_zero, ← smul_sub] at h1
  exact sub_eq_zero.1 (smul_eq_zero_ainf hi h1)

variable {a : ℕ} [NeZero a]

theorem exists_root {e : ℕ} [NeZero e] (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]
    (γ : TameGal ↥LL.1 l e a) :
    ∃ c : Wq l a, ∀ τ, algebraMap ↥(OL LL) ↥LL.1 (emb (thetaW a LL) τ c) = γ.root τ := by
  obtain ⟨z, ω, hω, hz, -⟩ := exists_gen l a
  have he : e = l ^ a - 1 := by
    have := TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a); omega
  set w : ↥LL.1 := ((thetaW a LL (WittVector.teichmuller l z) : ↥(OL LL)) : ↥LL.1) with hwdef
  have hw : (w : Om l) = ω := by
    refine (algebraMap (Om l) ℂ_[l]).injective ?_
    have h1 := congrArg (fun y : OC l => (y : ℂ_[l])) (intToOC_thetaW a LL (WittVector.teichmuller l z))
    simp only [coe_intToOC, wA_teich, WittVector.fontaineTheta_teichmuller] at h1
    exact h1.trans (GlobalTheory.MemLoc.IsTiltOf.untilt_eq hz)
  have hwp : IsPrimitiveRoot w e := by
    rw [he]
    refine IsPrimitiveRoot.of_map_of_injective (f := (LL.1).val) ?_ Subtype.val_injective
    simpa [hw] using hω
  have hpow : (((γ.left : (↥LL.1)ˣ) : ↥LL.1)) ^ e = 1 := (mem_rootsOfUnity' _ _).1 γ.left.2
  obtain ⟨k, -, hk⟩ := hwp.eq_pow_of_pow_eq_one hpow
  refine ⟨WittVector.teichmuller l z ^ k, fun τ => ?_⟩
  change ((thetaW a LL ((sigma l a ^ (-τ).val) (WittVector.teichmuller l z ^ k)) : ↥(OL LL)) : ↥LL.1) = _
  rw [map_pow, sigma_pow_teich, map_pow, map_pow, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, ← hwdef,
    TameGal.root, powL_apply]
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, ← hk]
  ring

end GlobalTheory.BKGal.CoverRing

open GlobalTheory.BKGal.CoverRing GlobalTheory.BKGal.CoverBridge in

theorem GlobalTheory.BKGal.covers_ringEndo : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (g : GQ l) (γ : TameGal ↥LL.1 l e a),
    Covers ↥LL.1 (thetaW a LL) ϖ g γ →
      ∃ ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧, ∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x) := by
  intro l _ a e _ _ ϖ LL _ _ g γ hcov
  obtain ⟨c, hc⟩ := exists_root LL γ
  refine ⟨(rescale c).comp (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
    Wq l a →+* Wq l a)), fun x => ?_⟩
  have h := hcov (toAc (thetaW a LL) ↥LL.1 x)
    (toAc (thetaW a LL) ↥LL.1 (rescale c (PowerSeries.map ((sigma l a ^ γ.shift.val : Wq l a ≃ₐ[ℤ_[l]] Wq l a) :
      Wq l a →+* Wq l a) x))) (fun τ => toAc_rescale (thetaW a LL) γ c hc x τ)
  rw [PiSys.iTot_toAc, PiSys.iTot_toAc, galOA_tmul] at h
  exact (one_tmul_inj h).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalBasisTransportFreeOverPrism
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.CrysIndep

theorem exists_read {Z O S W R N ι : Type} [CommRing Z] [CommRing O] [CommRing S] [CommRing W] [CommRing R]
    [Algebra Z O] [Algebra Z S] [Algebra Z W] [Algebra O R] [Module.Flat Z O] [AddCommGroup N]
    (ρ : S →ₐ[Z] W) (hρ : Function.Injective ρ) (g : S →+* R)
    (hg : ∀ z, g (algebraMap Z S z) = algebraMap O R (algebraMap Z O z)) (D : N →+ (ι → O ⊗[Z] W))
    (hD : ∀ x i, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) ρ z = D x i) :
    ∃ V : N →+ (ι → R), (∀ s x x' i, D x' i = ((1 : O) ⊗ₜ[Z] ρ s) * D x i → V x' i = g s * V x i) ∧
      (∀ (c : O) x i, D x i = algebraMap O _ c → V x i = algebraMap O R c) := by
  letI : Algebra Z R := ((algebraMap O R).comp (algebraMap Z O)).toAlgebra
  haveI : IsScalarTower Z O R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g' : S →ₐ[Z] R := { toRingHom := g, commutes' := hg }
  let Ψ : O ⊗[Z] S →ₐ[O] R :=
    Algebra.TensorProduct.lift (Algebra.ofId O R) g' fun _ _ => Commute.all _ _
  have hi : Function.Injective (Algebra.TensorProduct.map (AlgHom.id O O) ρ) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := O) ρ.toLinearMap hρ
  choose C hC using hD
  refine ⟨AddMonoidHom.mk' (fun x i => Ψ (C x i)) fun x y => funext fun i => ?_, fun s x x' i h => ?_,
    fun c x i h => ?_⟩
  · have : C (x + y) i = C x i + C y i := hi (by rw [map_add, hC, hC, hC, map_add, Pi.add_apply])
    change Ψ (C (x + y) i) = Ψ (C x i) + Ψ (C y i)
    rw [this, map_add]
  · have : C x' i = ((1 : O) ⊗ₜ[Z] s) * C x i := hi (by
      rw [map_mul, hC, hC, h, Algebra.TensorProduct.map_tmul]; rfl)
    change Ψ (C x' i) = g s * Ψ (C x i)
    rw [this, map_mul, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  · have : C x i = algebraMap O _ c := hi (by rw [hC, h, AlgHom.commutes])
    change Ψ (C x i) = _
    rw [this, AlgHom.commutes]

theorem indep_of_coord {Z O S W B R M N ι : Type} [CommRing Z] [CommRing O] [CommRing S] [CommRing W] [CommRing B]
    [CommRing R] [Algebra Z O] [Algebra Z S] [Algebra Z W] [Algebra O R] [Module.Flat Z O] [AddCommGroup M]
    [Module S M] [AddCommGroup N] [Module B N] [Fintype ι] [DecidableEq ι] {f : S →+* B} {u : M →ₛₗ[f] N}
    (hu : SemiBC u) (ρ : S →ₐ[Z] W) (hρ : Function.Injective ρ) (ψ : B →+* R)
    (hψ : ∀ z, ψ (f (algebraMap Z S z)) = algebraMap O R (algebraMap Z O z)) (D : M →+ (ι → O ⊗[Z] W))
    (hD : ∀ x i, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) ρ z = D x i)
    (hs : ∀ (s : S) x, D (s • x) = ((1 : O) ⊗ₜ[Z] ρ s) • D x) (m : O → ι → M)
    (hm : ∀ o j k, D (m o j) k = o • if k = j then 1 else 0) :
    ∃ lam : N →+ (ι → R), ∀ (Q : Type) [Fintype Q] (c : ι → Q → O) (y : ι → Q → B) (i : ι),
      lam (∑ j, ∑ q, y j q • u (m (c j q) j)) i = ∑ q, c i q • ψ (y i q) := by
  obtain ⟨V, hV1, hV2⟩ := exists_read ρ hρ (ψ.comp f) hψ D hD
  have hVb : ∀ (o : O) j k, V (m o j) k = algebraMap O R (if k = j then o else 0) := fun o j k => by
    refine hV2 _ _ _ ?_
    rw [hm]
    split_ifs
    · exact (Algebra.algebraMap_eq_smul_one o).symm
    · rw [smul_zero, map_zero]
  let V' : M →+ (Unit → ι → R) := AddMonoidHom.mk' (fun x _ => V x)
    fun x y => funext fun _ => map_add V x y
  obtain ⟨lam, hl1, hl2⟩ := CrysExt.exists_ext hu (fun _ : Unit => ψ) V' fun w x _ k =>
    hV1 w x (w • x) k (by rw [hs]; rfl)
  refine ⟨(Pi.evalAddMonoidHom _ ()).comp lam, fun Q _ c y i => ?_⟩
  have h3 : ∀ j q, lam (y j q • u (m (c j q) j)) () i =
      if i = j then c j q • ψ (y j q) else 0 := fun j q => by
    rw [hl1, hl2]
    change _ * V _ i = _
    rw [hVb]
    split_ifs
    · rw [Algebra.smul_def, mul_comm]
    · rw [map_zero, mul_zero]
  change lam _ () i = _
  simp only [map_sum, Finset.sum_apply, h3]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]

variable (a) in

noncomputable def evW (ϖ : PiSys l e) : (Wq l a)⟦X⟧ →ₐ[ℤ_[l]] WCb l where
  toRingHom := (inclW l).comp (ϖ.ev a)
  commutes' z := by
    change inclW l (ϖ.ev a (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) = _
    rw [PowerSeries.algebraMap_apply, PiSys.ev_C, AlgHom.commutes]
    exact (inclWA l).commutes z

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] {P : PhiMod O K l e a ι}

theorem exists_toW_eq {m : Vec K a ι} (hm : m ∈ P.M) (i : ι) :
    ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) (evW a ϖ) z = toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩ i := by
  have h1 : toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩ i =
      OfCrystal.iR K t ϖ fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩ :=
    ϖ.iW_of_mem t K fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩
  obtain ⟨s, hs⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O)
    (fun τ => ⟨m τ i, mem_tot.1 hm τ i⟩)
  refine ⟨∑ k, Module.Free.chooseBasis ℤ_[l] O k • ((1 : O) ⊗ₜ[ℤ_[l]] s k), ?_⟩
  rw [h1, hs, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, map_smul, OfCrystal.iR_toAc]
  rfl

theorem toW_bas (j : ι) (hm : (bas j : Vec K a ι) ∈ P.M) (i : ι) :
    toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩ i = if i = j then 1 else 0 := by
  rw [toW_apply]
  split_ifs with h
  · rw [← map_one (ϖ.iW t K)]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [bas, h]))
  · rw [← map_zero (ϖ.iW t K)]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [bas, h]))

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → (∀ i, (oE 1).u (ϖ.prism a) (b i) = b i) ∧ ∀ (P' : Obj l ↥(OL (ϖ.field a))) (f : GlobalTheory.Prism.Hom (ϖ.prism a) P') (Q Q' : Type) [Fintype Q] [Fintype Q'] (c : ι → Q → O) (y : ι → Q → P'.A) (c' : ι → Q' → O) (y' : ι → Q' → P'.A), ∑ i, ∑ q, y i q • (oE (c i q)).u P' (E.tr f (b i)) = ∑ i, ∑ q, y' i q • (oE (c' i q)).u P' (E.tr f (b i)) → ∀ (R : Type) [CommRing R] [Algebra O R] (ψ : P'.A →+* R), (∀ z : ℤ_[l], ψ (f.f (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) = algebraMap O R (algebraMap ℤ_[l] O z)) → ∀ i, ∑ q, c i q • ψ (y i q) = ∑ q, c' i q • ψ (y' i q) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  letI := zlLat T
  intro E jA H him oE hoE b hb
  have h0 : ∃ J : E.M (ϖ.prism a) →+ TW (OW l O) T, ∀ x, J x = kappa T (jA (E.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (jA.toAddMonoidHom.comp (E.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  obtain ⟨J, hJ⟩ := h0
  have hi : Function.Injective J := by
    have := E.proj (ainfObj (ϖ.field a))
    have := E.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact BKCoord.semiBC_injective (E.tr_bc (ϖ.toAinf a)) (BKCoord.ev_injective ϖ)
      (BKCoord.semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  have hJo : ∀ c x, J ((oE c).u (ϖ.prism a) x) = c • J x := fun c x => by
    have h3 := (congrArg jA ((oE c).u_tr (ϖ.toAinf a) x)).symm.trans (hoE c _)
    have h4 := (congrArg (kappa T) h3).trans (OfCrystal.kappa_mulZ T c _)
    rewrite [hJ, hJ]
    exact h4
  have hJs : ∀ (w : (ϖ.prism a).A) x, J (w • x) = ((1 : O) ⊗ₜ[ℤ_[l]] evW a ϖ w : OW l O) • J x :=
    fun w x => by
    have h3 := congrArg jA ((E.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (jA.map_smulₛₗ _ _))
    have h5 := h4.trans (BKCoord.kappa_smul T _ _)
    rewrite [hJ, hJ]
    exact h5
  refine ⟨fun i => hi (by rw [hJo, one_smul]), ?_⟩
  intro P' f Q Q' _ _ c y c' y' heq R _ _ ψ hψ i
  have h1 : ∃ D : E.M (ϖ.prism a) →+ (ι → OW l O), ∀ x, D x = I.j.symm (J x) :=
    ⟨I.j.symm.toLinearMap.toAddMonoidHom.comp J, fun _ => rfl⟩
  obtain ⟨D, hD⟩ := h1
  have h2 : ∀ x k, ∃ z, Algebra.TensorProduct.map (AlgHom.id O O) (evW a ϖ) z = D x k := fun x k => by
    obtain ⟨m, hm, h⟩ := (him (J x)).1 ⟨x, hJ x⟩
    rw [hD, h, LinearEquiv.symm_apply_apply]
    exact exists_toW_eq t ϖ hm k
  have h3 : ∀ (w : (ϖ.prism a).A) x, D (w • x) = ((1 : O) ⊗ₜ[ℤ_[l]] evW a ϖ w : OW l O) • D x :=
    fun w x => (hD _).trans ((congrArg I.j.symm (hJs w x)).trans
      ((I.j.symm.map_smul _ _).trans (congrArg _ (hD x).symm)))
  have h4 : ∀ (o : O) j k, D ((oE o).u (ϖ.prism a) (b j)) k = o • if k = j then 1 else 0 := fun o j k => by
    obtain ⟨hm, h⟩ := hb j
    have h5 : I.j.symm (J (b j)) = toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩ :=
      I.j.symm_apply_eq.2 ((hJ _).trans h)
    have h6 : I.j.symm (o • J (b j)) = o • I.j.symm (J (b j)) := LinearMapClass.map_smul_of_tower _ _ _
    have h7 := ((hD _).trans (congrArg I.j.symm (hJo o (b j)))).trans (h6.trans (congrArg (o • ·) h5))
    exact (congrFun h7 k).trans (congrArg (o • ·) (toW_bas t ϖ j hm k))
  letI : Algebra ℤ_[l] (ϖ.prism a).A := (inferInstance : Algebra ℤ_[l] (Wq l a)⟦X⟧)
  obtain ⟨lam, hlam⟩ := indep_of_coord (Z := ℤ_[l]) (S := (ϖ.prism a).A) (E.tr_bc f) (evW a ϖ)
    (OfCrystal.ev_injective ϖ t K) ψ hψ D h2 h3 (fun o j => (oE o).u (ϖ.prism a) (b j)) h4
  simp only [FHom.u_tr] at heq
  exact (hlam Q c y i).symm.trans ((congrArg (lam · i) heq).trans (hlam Q' c' y' i))

end GlobalTheory.CrysIndep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalCoordinatesConstantCoeffEqStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_coordinates_constantCoeff_eq : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (j₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, j₀ τ (δ.f y) = PowerSeries.constantCoeff (j τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∀ y τ i, PowerSeries.constantCoeff (lam₀ y τ i) = PowerSeries.constantCoeff (lam₁ y τ i) := by
  first | exact @GlobalTheory.CrysConst.constantCoeff_eq | exact GlobalTheory.CrysConst.constantCoeff_eq | (intros; apply GlobalTheory.CrysConst.constantCoeff_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinatesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (hl : (l : PP.A) ∈ PP.I) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → (∀ τ y, J τ (PP.D.φ y) = φ₂ (J (τ - 1) y)) → (∀ f, φ₂ (g f) = g (frob K l f)) → Function.Injective g → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i))) → ∀ (y n : EE.M PP) (k : ℕ), IsFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ y) n k → ∀ τ i, lam n τ i = (l : K⟦X⟧⟦X⟧) ^ k * (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i := by
  first | exact @GlobalTheory.CrysFrobCoord.frob_in_coordinates | exact GlobalTheory.CrysFrobCoord.frob_in_coordinates | (intros; apply GlobalTheory.CrysFrobCoord.frob_in_coordinates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFilteredDeRhamComparisonStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_filtered_deRham_comparison : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsCrys (P.PD K) ρ → ∀ (a : ℤ), ∀ y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) a, ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) (k i) ∧ b i ∈ (P.PD K).Fil (a - k i)) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  first | exact @GlobalTheory.SeedFil.crys_filtered | exact GlobalTheory.SeedFil.crys_filtered | (intros; apply GlobalTheory.SeedFil.crys_filtered <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CstSApply
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

def cstS : Wq l a →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (C : K →+* K⟦X⟧).comp ((algebraMap O K).comp (emb t τ).toRingHom)

theorem cstS_apply (w : Wq l a) (τ : ZMod a) : cstS t K w τ = C (algebraMap O K (emb t τ w)) := rfl

variable (a) {K} in

def dpS (e n : ℕ) : ZMod a → K⟦X⟧ := fun _ => monomial n (((n / e).factorial : K)⁻¹)

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictnessStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_subrep_quotient_and_strictness : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V' : Type) [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V'] [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V') (f : V →ₗ[↥LL.1] V'), (∀ g x, f (ρ g x) = ρ' g (f x)) → (Function.Injective f → IsDR (P.PD K) ρ' → IsDR (P.PD K) ρ) ∧ (Function.Surjective f → IsDR (P.PD K) ρ → IsDR (P.PD K) ρ' ∧ ∀ (a : ℤ), ∀ y ∈ DdR (P.PD K) ρ' ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V') a, ∃ x ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) x = y) := by
  first | exact @GlobalTheory.DRSubQuot.deRham_sub_quot | exact GlobalTheory.DRSubQuot.deRham_sub_quot | (intros; apply GlobalTheory.DRSubQuot.deRham_sub_quot <;> assumption)
end

