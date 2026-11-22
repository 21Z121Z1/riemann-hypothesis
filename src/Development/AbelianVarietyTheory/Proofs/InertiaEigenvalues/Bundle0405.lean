import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0373
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0375
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0370
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockSumSemisimpleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_sum_semisimple : ∀ {k Γ : Type} [Field k] [Group Γ] {r t : ℕ} (ρ : Γ →* Matrix (Fin r) (Fin r) k) (χ : Fin t → (Γ →* kˣ)), GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.IsIrred (matRep ρ) → IsSS (GlobalTheory.IndefiniteRowSideFullHecke.SemisimplificationConstituents.blockSum ρ χ) := by
  first | exact @GlobalTheory.isSS_blockSum_of_isIrred | exact GlobalTheory.isSS_blockSum_of_isIrred | (intros; apply GlobalTheory.isSS_blockSum_of_isIrred <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscRestrictInjective
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem disc_restrict_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ ρ' : ℝ≥0), 0 < ρ' → ρ' ≤ ρ →
    ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS ρ', IsDiscMap (RingHom.id bk.S) R → Function.Injective R := by
  intro l _ K bk ρ ρ' h0 hle h1 R hR
  have hρ0 : 0 < ρ := h0.trans_le hle
  obtain ⟨a, ha1, ha2, ha3, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ0 h1
  obtain ⟨a', ha1', ha2', -, -⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ' h0 (hle.trans_lt h1)
  obtain ⟨-, -, hdense, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ
  have htors : ∀ z : Disc l (0 : Wq l bk.a) 1, l • z = 0 → z = 0 := by
    intro z hz
    rw [nsmul_eq_mul] at hz
    exact ((isUnit_l_disc l (0 : Wq l bk.a) 1).mul_right_eq_zero).1 hz
  have hbound : ∀ (σ : ℝ≥0), 0 < σ → ∀ (b : bk.DS σ →+ Disc l (0 : Wq l bk.a) 1) (n : ℕ),
      (∀ y, ‖b y‖ * (σ : ℝ) ^ n ≤ ‖y‖) → ∀ y, ‖b y‖ ≤ ((σ : ℝ) ^ n)⁻¹ * ‖y‖ := by
    intro σ hσ b n hb y
    have hp : (0 : ℝ) < (σ : ℝ) ^ n := pow_pos (by exact_mod_cast hσ) n
    rw [inv_mul_eq_div, le_div_iff₀ hp]
    exact hb y
  have hcoef : ∀ n y, a' n (R y) = a n y := by
    intro n
    have e := hdense (Disc l (0 : Wq l bk.a) 1) htors ((a' n).comp R.toAddMonoidHom) (a n)
      (AddMonoidHomClass.continuous_of_bound _ (((ρ' : ℝ) ^ n)⁻¹) fun y =>
        (hbound ρ' h0 (a' n) n (ha2' n) (R y)).trans
          (mul_le_mul_of_nonneg_left (hR.norm_le y) (inv_nonneg.2 (by positivity))))
      (AddMonoidHomClass.continuous_of_bound _ (((ρ : ℝ) ^ n)⁻¹) (hbound ρ hρ0 (a n) n (ha2 n)))
      (fun x => by
        change a' n (R (toDisc l (X : bk.S) ρ x)) = a n (toDisc l (X : bk.S) ρ x)
        rw [hR.ext x, RingHom.id_apply, ha1', ha1])
    intro y
    exact DFunLike.congr_fun e y
  refine (injective_iff_map_eq_zero R).2 fun y hy => ?_
  have h := ha3 y 0 le_rfl fun n => by rw [← hcoef n y, hy, map_zero, norm_zero, zero_mul]
  exact norm_le_zero_iff.1 h

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopesAdicTopologicalBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem envelopes_topBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X))
    (En₂ : Env bk En.Q (BK.hf En.inl bk.E) (BK.hf En.inl X)),
    Nonempty (TopBasis (BK.hf En.inl) bk.J (Digits l)) ∧
      ∃ ι : Type, Nonempty (TopBasis (BK.hf (En₂.inl.comp En.inl)) bk.J ι) := by
  intro l _ K bk En En₂
  have h1 : bk.J.map (BK.hf En.inl) =
      Ideal.span {(BK.hf En.inl) (l : bk.S)} ⊔ Ideal.span {(BK.hf En.inl) bk.E} := by
    simp only [BK.J, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  have h2 : (BK.hf En.inl) (l : bk.S) = (l : En.Q.A) := map_natCast (BK.hf En.inl) l
  have h3 : En.Q.I = Ideal.span {(BK.hf En.inl) bk.E} := En.I_eq
  have hI : Ideal.span {(l : En.Q.A)} ⊔ En.Q.I = bk.J.map (BK.hf En.inl) :=
    (h1.trans (congrArg₂ (· ⊔ ·) (congrArg (fun x => Ideal.span {x}) h2) h3.symm)).symm
  have T₁ : TopBasis (BK.hf En.inl) bk.J (Digits l) := En.tb
  have T₂ : TopBasis En₂.inl.f (Ideal.span {(l : En.Q.A)} ⊔ En.Q.I) (Digits l) := En₂.tb
  have key := GlobalTheory.T.adicTopologicalBasis_exists_comp bk.S En.Q.A (BK.hf En.inl) bk.J (Digits l) T₁ En₂.Q.A En₂.inl.f
    (Ideal.span {(l : En.Q.A)} ⊔ En.Q.I) (Digits l) T₂ hI
  exact ⟨⟨T₁⟩, Digits l × Digits l, key.elim fun TC _ => ⟨TC⟩⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHomImageXDeltaZeroLiftsUniformizerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinHom_image_X_delta_zero_lifts_uniformizer : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (g : Hom bk.prism C), C.D.δ (BK.hf g X) = 0 ∧ Ideal.Quotient.mk C.I (BK.hf g X) = C.str (bk.str.symm (Ideal.Quotient.mk _ X)) := by
  first | exact @GlobalTheory.BSP.hf_X_δ_and_str | exact GlobalTheory.BSP.hf_X_δ_and_str | (intros; apply GlobalTheory.BSP.hf_X_δ_and_str <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameCocyclesLinkedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinLatticeFrame_cocycles_linked : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N d ρ) (F' : Frame bk N' d' ρ') (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ (g : ↥(GK K)) i j, (l : Ainf l) ^ n ∣ (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g) i j := by
  first | exact @GlobalTheory.BKLim.LinkCocycle.main | exact GlobalTheory.BKLim.LinkCocycle.main | (intros; apply GlobalTheory.BKLim.LinkCocycle.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLatticeFrameLimitGaloisInvariant
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.BinfInv

private theorem exists_isEps_pt (l : ℕ) [Fact l.Prime] : ∃ e : Per.Fl l, IsEps e := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  refine ⟨ε, ?_, ?_⟩
  · have := hr 0
    rw [h0, map_one] at this
    exact Subtype.ext this
  · intro h
    have := hr 1
    have e : rootT ε 1 = 1 := h
    rw [e] at this
    apply h1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← this, map_one]
    rfl

private theorem algebraMap_mem_filtration_one_iff_mem_ker (l : ℕ) [Fact l.Prime] (a : Per.AinfP l) :
    algebraMap (Per.AinfP l) (Per.BdRp l) a ∈ Per.FilP l 1 ↔ a ∈ Per.kerP l := by
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, GlobalTheory.RingIface.ev_alg, Ideal.Quotient.eq_zero_iff_mem, pow_one]

private theorem galoisAction_mem_filtration (l : ℕ) [Fact l.Prime] (g : Per.Gq l) (n : ℕ) (y : Per.BdRp l)
    (hy : y ∈ Per.FilP l n) : Per.σDp g y ∈ Per.FilP l n := by
  obtain ⟨e, he⟩ := exists_isEps_pt l
  obtain ⟨hP, -, -, -⟩ := GlobalTheory.MemLoc.filtration_eq_xi_pow l e he
  have hξ : aDp l (xi e) ∈ Per.FilP l 1 := (hP 1 _).2 (by rw [pow_one])
  have ha : aDp l (xi e) = algebraMap (Per.AinfP l) (Per.BdRp l)
      (algebraMap (Per.Ainf l) (Per.AinfP l) (xi e)) := by
    unfold aDp
    rw [RingHom.comp_apply]
  have hσ : Per.σDp g (aDp l (xi e)) ∈ Per.FilP l 1 := by
    rw [ha] at hξ ⊢
    rw [GlobalTheory.RingIface.sigDp_alg, algebraMap_mem_filtration_one_iff_mem_ker]
    exact GlobalTheory.RingBasics.ker_σ g ((algebraMap_mem_filtration_one_iff_mem_ker l _).1 hξ)
  have hd : aDp l (xi e) ∣ Per.σDp g (aDp l (xi e)) := by
    simpa only [pow_one] using (hP 1 _).1 hσ
  refine (hP n _).2 ((pow_dvd_pow_of_dvd hd n).trans ?_)
  rw [← map_pow]
  exact map_dvd _ ((hP n _).1 hy)

theorem σDp_mem_FilP {l : ℕ} [Fact l.Prime] (g : Per.Gq l) (m : ℕ) {x : Per.BdRp l}
    (hx : x ∈ Per.FilP l m) : Per.σDp g x ∈ Per.FilP l m :=
  galoisAction_mem_filtration l g m x hx

theorem eq_of_forall_mem_FilP {l : ℕ} [Fact l.Prime] {x : Per.BdRp l}
    (hx : ∀ m, x ∈ Per.FilP l m) : x = 0 :=
  GlobalTheory.RingIface.ev_ext l x 0 fun m =>
    ((GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l m x).1 (hx m)).trans (map_zero (Per.ev l m)).symm

theorem inv : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (B : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β ∧ ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m) → ∀ g : ↥(GK K), (F.ε g).map ((aDp l).comp WittVector.frobenius) * B.map (Per.σDp (g : GQ l)) = B := by
  intro l _ K bk N d ρ F B hB g
  ext i j
  rw [← sub_eq_zero]
  refine eq_of_forall_mem_FilP fun m => ?_
  obtain ⟨k, β, hβ, hb⟩ := hB m
  set σ := Per.σDp (g : GQ l) with hσ
  set Φ := (F.ε g).map ((aDp l).comp WittVector.frobenius) with hΦ
  set b : Matrix (Fin d) (Fin d) (Per.BdRp l) := β.map ((aDp l).comp bk.ev) with hbdef
  have h1 := ((GlobalTheory.AinfEPow.ePow_facts l K bk m).2.2.1 _).2 (hβ.2 g i j)
  have h1' : (Φ * b.map σ - b) i j ∈ Per.FilP l m := by
    convert h1 using 1
    simp only [Matrix.sub_apply, Matrix.mul_apply, map_sub, map_sum, map_mul, Matrix.map_apply, hΦ, hbdef, hσ,
      RingHom.comp_apply, GlobalTheory.MemLoc.ActLaws.σDp_aDp]
  have h2 : ∀ x y, (l : Per.BdRp l) ^ k * B x y - b x y ∈ Per.FilP l m := fun x y => by
    have := (Ideal.neg_mem_iff _).2 (hb x y)
    simpa [hbdef, neg_sub] using this
  have key : (l : Per.BdRp l) ^ k * ((Φ * B.map σ) i j - B i j) =
      (Φ * b.map σ - b) i j + ∑ x, Φ i x * σ ((l : Per.BdRp l) ^ k * B x j - b x j) +
        (b i j - (l : Per.BdRp l) ^ k * B i j) := by
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, map_sub, map_mul, map_pow, map_natCast,
      mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    have e : ∑ x, Φ i x * ((l : Per.BdRp l) ^ k * σ (B x j)) = ∑ x, (l : Per.BdRp l) ^ k * (Φ i x * σ (B x j)) :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    ring
  have h3 : (l : Per.BdRp l) ^ k * ((Φ * B.map σ) i j - B i j) ∈ Per.FilP l m := by
    rw [key]
    refine Ideal.add_mem _ (Ideal.add_mem _ h1' (Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ ?_)) (by simpa [hbdef] using hb i j)
    exact σDp_mem_FilP _ m (h2 x j)
  obtain ⟨u, hu⟩ := ((GlobalTheory.MemLoc.isUnit_l_BdRp l).pow k).exists_left_inv
  have := Ideal.mul_mem_left _ u h3
  rwa [← mul_assoc, hu, one_mul] at this

end GlobalTheory.BKLim.BinfInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentField
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.OEmod

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K)

def ψ : bk.S →+* Cb l := (WittVector.constantCoeff (p := l) (R := Cb l)).comp bk.evW

theorem ψ_apply (s : bk.S) : ψ bk s = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := by
  simp [ψ, BK.evW, inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem ψ_X : ψ bk X = algebraMap (OCb l) (Cb l) bk.flat := by
  rw [ψ_apply, bk.ev_X, WittVector.teichmuller_coeff_zero]

theorem cc_evW_X : WittVector.constantCoeff (bk.evW X) = algebraMap (OCb l) (Cb l) bk.flat := ψ_X bk

theorem cc_l_mul (y : WCb l) : WittVector.constantCoeff ((l : WCb l) * y) = 0 := by
  rw [WittVector.constantCoeff_apply, mul_comm]
  exact WittVector.mul_charP_coeff_zero y

theorem evW_X_eq : bk.evW X = WittVector.teichmuller l (algebraMap (OCb l) (Cb l) bk.flat) := by
  simp [BK.evW, bk.ev_X, inclW, WittVector.map_teichmuller]

theorem l_dvd_of_not_isUnit (a : ℕ) [NeZero a] (x : Wq l a) (h : ¬ IsUnit x) : (l : Wq l a) ∣ x := by
  by_cases h0 : x = 0
  · exact h0 ▸ dvd_zero _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul x h0
  cases m with
  | zero => exact absurd (by simpa using WittVector.isUnit_of_coeff_zero_ne_zero b hb) h
  | succ m => exact Dvd.intro _ (by rw [pow_succ', mul_assoc])

theorem exists_unit (s : bk.S) (hs : ψ bk s ≠ 0) :
    ∃ (k : ℕ) (s₁ : bk.S), IsUnit s₁ ∧ ψ bk s = ψ bk X ^ k * ψ bk s₁ := by
  have hex : ∃ i, IsUnit (coeff i s) := by
    by_contra hno
    push_neg at hno
    have hd : ∀ i, (l : Wq l bk.a) ∣ coeff i s := fun i => l_dvd_of_not_isUnit bk.a _ (hno i)
    choose c hc using hd
    have : s = (l : bk.S) * PowerSeries.mk c := by
      ext i
      rw [← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, hc i]
    apply hs
    rw [this, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
  classical
  let k := Nat.find hex
  have hk : IsUnit (coeff k s) := Nat.find_spec hex
  have hlt : ∀ i < k, (l : Wq l bk.a) ∣ coeff i s := fun i hi =>
    l_dvd_of_not_isUnit bk.a _ (Nat.find_min hex hi)
  choose! c hc using hlt
  let s₁ : bk.S := PowerSeries.mk fun i => coeff (i + k) s
  let s₂ : bk.S := PowerSeries.mk fun i => if i < k then c i else 0
  have hs₁ : IsUnit s₁ := by
    rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]
    exact hk
  have hsplit : s = X ^ k * s₁ + (l : bk.S) * s₂ := by
    ext i
    rw [map_add, coeff_X_pow_mul', ← map_natCast (C (R := Wq l bk.a)), coeff_C_mul, coeff_mk, coeff_mk]
    by_cases hi : i < k
    · rw [if_neg (by omega), if_pos hi, zero_add, hc i hi]
    · rw [if_pos (by omega), if_neg hi, mul_zero, add_zero, Nat.sub_add_cancel (by omega)]
  refine ⟨k, s₁, hs₁, ?_⟩
  conv_lhs => rw [hsplit]
  rw [map_add, map_mul, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero]

end GlobalTheory.BSP.OEmod

open GlobalTheory.BSP.OEmod in
theorem GlobalTheory.BSP.oe_mod_l : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S), algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0)) ∧ (∀ s : bk.S, bk.evW s ∈ bk.OE) ∧ IsUnit (bk.evW X) ∧ (∀ w : WCb l, bk.evW X * w ∈ bk.OE → w ∈ bk.OE) ∧ ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), y⁻¹ ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  intro l _ K bk
  have hflat : bk.flat ≠ 0 := (GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk).2.2.2.1
  have hf : algebraMap (OCb l) (Cb l) bk.flat ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 hflat
  have hunit : IsUnit (bk.evW X) := by
    rw [evW_X_eq]
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [WittVector.teichmuller_coeff_zero]
    exact hf
  have h1 : ∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S),
      algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := by
    intro y
    rw [Subring.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨m, s, z, h⟩ := hw 1
      refine ⟨m, s, ?_⟩
      have := congrArg (WittVector.constantCoeff (p := l) (R := Cb l)) h
      rw [map_mul, map_pow, map_add, pow_one, cc_l_mul, add_zero, cc_evW_X] at this
      rw [this, ← ψ_apply]
      rfl
    · rintro ⟨m, s, h⟩
      obtain ⟨u, hu⟩ := hunit
      refine ⟨(↑(u⁻¹) : WCb l) ^ m * bk.evW s, fun n => ⟨m, s, 0, ?_⟩, ?_⟩
      · rw [mul_zero, add_zero, ← mul_assoc, ← mul_pow, ← hu, Units.mul_inv, one_pow, one_mul]
      · have hc : WittVector.constantCoeff (bk.evW X) * WittVector.constantCoeff ((↑(u⁻¹) : WCb l)) = 1 := by
          rw [← map_mul, ← hu, Units.mul_inv, map_one]
        rw [cc_evW_X] at hc
        rw [map_mul, map_pow]
        have hs : WittVector.constantCoeff (bk.evW s) = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := ψ_apply bk s
        rw [hs, ← h, ← mul_assoc, ← mul_pow, mul_comm _ (algebraMap (OCb l) (Cb l) bk.flat), hc, one_pow, one_mul]
  refine ⟨h1, fun s n => ⟨0, s, 0, by simp⟩, hunit, fun w hw n => ?_, fun y hy => ?_⟩
  · obtain ⟨m, s, z, h⟩ := hw n
    exact ⟨m + 1, s, z, by rw [pow_succ, mul_assoc, h]⟩
  · by_cases hy0 : y = 0
    · rw [hy0, inv_zero]; exact Subring.zero_mem _
    obtain ⟨m, s, h⟩ := (h1 y).1 hy
    rw [← ψ_apply] at h
    have hs : ψ bk s ≠ 0 := by rw [← h]; exact mul_ne_zero (pow_ne_zero _ hf) hy0
    obtain ⟨k, s₁, ⟨t, rfl⟩, hk⟩ := exists_unit bk s hs
    rw [h1]
    refine ⟨k, ((X : bk.S) ^ m * ↑(t⁻¹) : bk.S), ?_⟩
    rw [← ψ_apply, map_mul, map_pow, ψ_X]
    rw [hk, ψ_X] at h
    have ht : ψ bk ↑t * ψ bk ↑(t⁻¹) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have ht0 : ψ bk ↑t ≠ 0 := left_ne_zero_of_mul_eq_one ht
    have hinv : ψ bk ↑(t⁻¹) = (ψ bk ↑t)⁻¹ := eq_inv_of_mul_eq_one_right ht
    rw [hinv]
    field_simp
    linear_combination -h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinQuotientEisensteinEquivStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_quotient_eisenstein_equiv : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [Algebra (Wq l a) O] (π : O) (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → (Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f) → ∃ str : O ≃+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {(Ep : (Wq l a)⟦X⟧)}), ∀ f : Polynomial (Wq l a), str (Polynomial.aeval π f) = Ideal.Quotient.mk _ (f : (Wq l a)⟦X⟧) := by
  first | exact @GlobalTheory.bkStr_quotient_equiv | exact GlobalTheory.bkStr_quotient_equiv | (intros; apply GlobalTheory.bkStr_quotient_equiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSeedDiscNormBounds
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.RhoZeroNormBounds

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem ρ₀_pos (bk : BK K) : 0 < bk.ρ₀ := by
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 hl.out.pos
  unfold BK.ρ₀
  exact NNReal.rpow_pos hl0

theorem ρ₀_pow (bk : BK K) : bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 hl.out.pos
  have he : (bk.Ep.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 bk.deg_pos.ne'
  unfold BK.ρ₀
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he, NNReal.rpow_neg_one]

theorem norm_l_mul (bk : BK K) (y : bk.DA bk.ρ₀) : ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖ := by
  rw [(GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).2.1 y, div_eq_inv_mul]

theorem norm_iS_le (bk : BK K) (x : bk.S) : ‖bk.iS x‖ ≤ 1 :=
  norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) (bk.ev x)

theorem norm_iS_E (bk : BK K) : ‖bk.iS bk.E‖ ≤ (l : ℝ)⁻¹ := by
  haveI := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Ainf l) (bk.ev X) bk.ρ₀).1
  have hE : bk.E = bk.Ep.eval₂ PowerSeries.C PowerSeries.X := (Polynomial.eval₂_C_X_eq_coe).symm
  rw [hE, Polynomial.hom_eval₂, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]
  have hinv : (0 : ℝ) ≤ (l : ℝ)⁻¹ := by positivity
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hinv fun i hi => ?_
    obtain ⟨d, hd⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    have e : (bk.iS.comp PowerSeries.C) (bk.Ep.coeff i) * bk.iS PowerSeries.X ^ i =
        (l : bk.DA bk.ρ₀) * bk.iS (PowerSeries.C d * PowerSeries.X ^ i) := by
      rw [hd, RingHom.comp_apply, map_mul, map_mul, map_mul, map_pow, map_natCast, map_natCast, mul_assoc]
    rw [e, norm_l_mul]
    exact mul_le_of_le_one_right hinv (norm_iS_le bk _)
  · rw [bk.monic.coeff_natDegree, map_one, one_mul, ← map_pow]
    change ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev (PowerSeries.X ^ bk.Ep.natDegree))‖ ≤ _
    rw [map_pow]
    refine (norm_toDisc_pow_le _ (ρ₀_pos bk)).trans ?_
    rw [← NNReal.coe_pow, ρ₀_pow, NNReal.coe_inv, NNReal.coe_natCast]

theorem norm_iA_ker (bk : BK K) (a : Ainf l) (ha : Per.θ l a = 0) : ‖bk.iA a‖ ≤ (l : ℝ)⁻¹ := by
  have hmem : a ∈ Ideal.span {bk.ev bk.E} := by rw [bk.span_ev]; exact ha
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hmem
  rw [map_mul]
  refine (norm_mul_le _ _).trans ?_
  have h1 : ‖bk.iA c‖ ≤ 1 := norm_toDisc_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) c
  have h2 : ‖bk.iA (bk.ev bk.E)‖ ≤ (l : ℝ)⁻¹ := norm_iS_E bk
  calc ‖bk.iA c‖ * ‖bk.iA (bk.ev bk.E)‖ ≤ 1 * (l : ℝ)⁻¹ := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem seed_norms : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ‖bk.iS bk.E‖ ≤ (l : ℝ)⁻¹ ∧ (∀ y : bk.DA bk.ρ₀, ‖(l : bk.DA bk.ρ₀) * y‖ = (l : ℝ)⁻¹ * ‖y‖) ∧ ∀ a : Ainf l, Per.θ l a = 0 → ‖bk.iA a‖ ≤ (l : ℝ)⁻¹ :=
  fun _ _ _ bk => ⟨norm_iS_E bk, norm_l_mul bk, norm_iA_ker bk⟩

end GlobalTheory.BSP.RhoZeroNormBounds
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMemStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)) (v : ℝ), lowerRamificationGroup F L 0 = ⊤ → ∀ σ ∈ upperRamificationGroup F L v, σ ∉ B → (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
  first | exact @GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem | exact GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem | (intros; apply GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralActsOnHeckeEigenspaceOfTypeSectionsStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralActsOnHeckeEigenspace_of_typeSections : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), (∀ i, Nonempty (Sec D i)) → OnMtPreservesTypeV D → EigSpan P := by
  first | exact @GlobalTheory.PendOf.EigSpanProof.main | exact GlobalTheory.PendOf.EigSpanProof.main | (intros; apply GlobalTheory.PendOf.EigSpanProof.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansionStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_decomposition_and_classFunction_expansion : ∀ (G : Type) [Group G] [Fintype G] (χ : G → ℂ), (IsChar χ → ∃ L : List (G → ℂ), (∀ ρ ∈ L, IsIrr ρ) ∧ χ = L.sum) ∧ (IsClass χ → χ = ∑ᶠ ρ ∈ {ρ : G → ℂ | IsIrr ρ}, ip χ ρ • ρ) ∧ (IsChar χ → IsClass χ) ∧ (IsChar χ → ip χ χ = 1 → IsIrr χ) ∧ (∀ L : List (G → ℂ), (∀ ρ ∈ L, IsChar ρ) → IsChar L.sum) := by
  first | exact @GlobalTheory.charDec | exact GlobalTheory.charDec | (intros; apply GlobalTheory.charDec <;> assumption)
end

