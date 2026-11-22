import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0675
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperMatrixUnitKillsUnipotentInvariantOnLevi
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnderEqOfConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.Small

theorem exists_under (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) = v := by
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 D.host.E) v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 D.host.F) (𝓞 D.host.E))]
      exact bot_le)
  refine ⟨⟨Q, hQ, fun h => v.ne_bot ?_⟩, HeightOneSpectrum.ext hQv⟩
  rw [← hQv, h]
  exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)

theorem under_eq_of_conj {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    P.under (𝓞 D.host.F) = P'.under (𝓞 D.host.F) := by
  refine HeightOneSpectrum.ext ((P.under (𝓞 D.host.F)).isMaximal.eq_of_le (P'.under (𝓞 D.host.F)).isPrime.ne_top
    fun a ha => ?_)
  obtain ⟨c', h1, h2⟩ := h (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a) ha
  have hfix : star (algebraMap D.host.F D.host.E (a : D.host.F)) = algebraMap D.host.F D.host.E (a : D.host.F) :=
    (D.sp.cm.fixed _).2 ⟨_, rfl⟩
  have e : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a = c' := RingOfIntegers.ext (h2.trans hfix).symm
  change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) a ∈ P'.asIdeal
  rwa [e]

end GlobalTheory.RawLift.Small

namespace GlobalTheory.RawLift.Small

theorem norm_eq_rpow {z : ℂ} {L n : ℕ} (h : ‖z‖ ^ 2 * (L : ℝ) ^ n = 1) : ‖z‖ = (L : ℝ) ^ (-(n : ℝ) / 2) := by
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hLn : (L : ℝ) ^ n ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact zero_ne_one h
  have h1 : ((L : ℝ) ^ (-(n : ℝ) / 2)) ^ 2 = ((L : ℝ) ^ n)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL, show -(n : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(n : ℝ) by push_cast; ring,
      Real.rpow_neg hL, Real.rpow_natCast]
  have h2 : ‖z‖ ^ 2 = ((L : ℝ) ^ n)⁻¹ := eq_inv_of_mul_eq_one_left h
  exact (pow_left_inj₀ (norm_nonneg z) (Real.rpow_nonneg hL _) two_ne_zero).1 (h2.trans h1.symm)

theorem locSmall : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, BadSupp R i t → GoodMod R i t → IndexSum (Wc D i) (Vc D i).rank → LocSmall R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t hB hG hI μ 𝓕 hμ
  obtain ⟨s, hs, hs1, hsC⟩ := hI
  refine ⟨fun v => max (s v) 0, ?_, fun v => max_lt (hs1 v) one_pos, ?_⟩
  · exact Summable.of_nonneg_of_le (fun v => le_max_right _ _) (fun v => max_le (le_abs_self _) (abs_nonneg _)) hs.abs
  intro v f hf C hC hCd
  by_cases hbad : ∃ P, (P ∈ R.Pg ∨ P ∈ R.Q t) ∧ ∃ e f', IsPrimeIdem P e f' ∧ f' = f
  · obtain ⟨P, hP, e, f', hPI, rfl⟩ := hbad
    rw [Finset.sum_eq_zero fun g hg => by rw [hB μ 𝓕 hμ P hP e f' hPI g (hC g hg).1 (hC g hg).2, norm_zero]]
    exact le_max_right _ _
  push_neg at hbad
  obtain ⟨ε, hε, hfε⟩ := hf
  have hI0 := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents (Wc D i)
  obtain ⟨P, hPv⟩ := exists_under D v
  obtain ⟨e, fP, hPI⟩ := hI0.2.1 P
  have hfP : fP = f := by
    rw [GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hPI hPv, hfε, GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hε]
  subst hfP
  obtain ⟨c, hβ⟩ := hL.lev.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    obtain ⟨e', f', h'⟩ := hI0.2.1 PP
    have hne := hbad PP (Or.inl hPP') e' f' h'
    refine ⟨fun h => hne ?_, fun h => hne ?_⟩
    · subst h
      exact ((hI0.2.2.1 PP e fP hPI).2.2.2.1 e' f' h').2
    · rw [GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem h' ((under_eq_of_conj h).trans hPv),
        GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hPI hPv]
  obtain ⟨hJ, -, -⟩ := (GlobalTheory.LevSplit.lev_split (Wc D i) (R.βW i) (R.ΛW i) (1 ^ c) (R.datWp i R.triv) hβ).2 P e fP hPI hN hoff
  have hPI' := hI0.2.2.1 P e fP hPI
  obtain ⟨L, hL'⟩ := (hI0.1 fP hPI'.1 hPI'.2.1).1
  have hsupp : ∀ g ∈ C, ∀ g' ∈ C, SuppF (Wc D i) fP (g⁻¹ * g') := fun g hg g' hg' =>
    (hL' _).1 (L.mul_mem (L.inv_mem ((hL' g).2 (hC g hg).1)) ((hL' g').2 (hC g' hg').1))
  calc ∑ g ∈ C, ‖coef R i t μ 𝓕 g‖ = ∑ g ∈ C, (latIndex (Wc D i) g : ℝ) ^ (-((Vc D i).rank : ℝ) / 2) :=
        Finset.sum_congr rfl fun g hg => norm_eq_rpow (hG μ 𝓕 hμ v fP ⟨ε, hε, hfε⟩ hbad g (hC g hg).1)
    _ ≤ s v := hsC v fP ⟨ε, hε, hfε⟩ C (fun g hg => ⟨(hC g hg).1, fun hk => (hC g hg).2 ((hJ g (hC g hg).1).2 hk)⟩)
        fun g hg g' hg' hk => hCd g hg g' hg' ((hJ _ (hsupp g hg g' hg')).2 hk)
    _ ≤ max (s v) 0 := le_max_left _ _

end GlobalTheory.RawLift.Small

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitarisableSegmentTwistPrecedesAddOneLeStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (δ δ' : IrrGL k) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
    IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y := by
  first | exact @GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes | exact GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes | (intros; apply GlobalTheory.LocGL.UnitaryOrder.add_one_le_of_precedes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperMatrixUnitKillsUnipotentInvariantOnLeviStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperMatrixUnit_kills_unipotentInvariant_on_levi : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (ψ : Sm E N), (∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g) → ∀ (τ : E →+* ℂ) (p q : Fin N), blk (stdBlocks n h) p < blk (stdBlocks n h) q → ∀ m, (Eop τ p q ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 := by
  first | exact @GlobalTheory.UnipKill.eop_leviEmb_eq_zero | exact GlobalTheory.UnipKill.eop_leviEmb_eq_zero | (intros; apply GlobalTheory.UnipKill.eop_leviEmb_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneParamDualListSumAbsTwistSpecial
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open TensorProduct Module
namespace GlobalTheory.WDDual
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem iso_sum_dual (a : WDRep h V) (b : WDRep h V') : (a.dual.sum b.dual).Iso (a.sum b).dual := by
  refine ⟨Module.dualProdDualEquivDual ℂ V V', fun σ x => ?_, fun x => ?_⟩
  · ext v <;> simp
  · ext v <;> simp

theorem iso_tensor_dual (a : WDRep h V) (b : WDRep h V') :
    (a.dual.tensor b.dual).Iso (a.tensor b).dual := by
  refine ⟨TensorProduct.dualDistribEquiv ℂ V V', fun σ x => ?_, fun x => ?_⟩
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      refine TensorProduct.ext' fun m n => ?_
      simp [TensorProduct.dualDistrib_apply]
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul f g =>
      refine TensorProduct.ext' fun m n => ?_
      simp [TensorProduct.dualDistrib_apply]
      ring
    | add x y hx hy => simp only [map_add, hx, hy]

omit [IsAlgClosure E Ω] in

theorem qPow_neg' (s : ℝ) : qPow w (-s) = (qPow w s)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← qPow_add, neg_add_cancel, qPow_zero])

theorem iso_tw_dual (a : WDRep h V) (s : ℝ) : (a.tw s).dual.Iso (a.dual.tw (-s)) := by
  refine ⟨LinearEquiv.refl ℂ _, fun σ f => ?_, fun f => rfl⟩
  ext v
  simp only [WDRep.tw, WDRep.dual_ρ, WDRep.twist_ρ, unrChar_apply, LinearEquiv.refl_apply,
    LinearMap.dualMap_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, qPow_neg', map_inv, _root_.inv_zpow']
  congr 2
  simp

theorem shiftEnd_single {n : ℕ} (j : Fin n) :
    shiftEnd n (Pi.single j 1) = if hj : (j : ℕ) + 1 < n then Pi.single ⟨j + 1, hj⟩ 1 else 0 := by
  ext k
  rw [shiftEnd_apply]
  split_ifs with h1 h2 h2 <;> simp only [Pi.single_apply, Fin.ext_iff, Fin.val_mk, Pi.zero_apply] <;>
    split_ifs <;> first | rfl | (exfalso; have := k.2; have := j.2; omega)

theorem spEig_rev {n : ℕ} (i : Fin n) : WDRep.spEig w n i.rev = (WDRep.spEig w n i)⁻¹ := by
  rw [WDRep.spEig, WDRep.spEig, ← qPow_neg']
  congr 1
  rw [Fin.val_rev]
  have : (i : ℕ) + 1 ≤ n := i.2
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem diagEnd_single {n : ℕ} (c : Fin n → ℂ) (j : Fin n) :
    diagEnd c (Pi.single j 1) = c j • Pi.single j (1 : ℂ) := by
  ext k; by_cases hk : k = j
  · subst hk; simp
  · simp [hk]

def spDualMap (n : ℕ) : Dual ℂ (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) where
  toFun f i := (-1 : ℂ) ^ (i : ℕ) * f (Pi.single i.rev 1)
  map_add' f g := by ext i; simp [mul_add]
  map_smul' c f := by ext i; simp; ring

theorem spDualMap_apply {n : ℕ} (f : Dual ℂ (Fin n → ℂ)) (i : Fin n) :
    spDualMap n f i = (-1 : ℂ) ^ (i : ℕ) * f (Pi.single i.rev 1) := rfl

theorem spDualMap_injective (n : ℕ) : Function.Injective (spDualMap n) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  refine LinearMap.pi_ext fun j x => ?_
  have := congrFun hf j.rev
  rw [spDualMap_apply, Fin.rev_rev, Pi.zero_apply, mul_eq_zero] at this
  have h1 : f (Pi.single j 1) = 0 := this.resolve_left (pow_ne_zero _ (by norm_num))
  have h2 : (Pi.single j x : Fin n → ℂ) = x • Pi.single j (1 : ℂ) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [h2, map_smul, h1, smul_zero]; simp

theorem iso_sp_dual (n : ℕ) : (WDRep.sp h n).dual.Iso (WDRep.sp h n) := by
  refine ⟨LinearMap.linearEquivOfInjective (spDualMap n) (spDualMap_injective n)
    (by simp [Subspace.dual_finrank_eq]), fun σ f => ?_, fun f => ?_⟩
  · ext i
    simp only [LinearMap.linearEquivOfInjective_apply, spDualMap_apply, WDRep.dual_ρ, WDRep.sp_ρ,
      LinearMap.dualMap_apply, diagEnd_single, map_smul, smul_eq_mul, diagEnd_apply, spEig_rev]
    simp
    ring
  · ext i
    simp only [LinearMap.linearEquivOfInjective_apply, spDualMap_apply, WDRep.dual_N, WDRep.sp_N,
      LinearMap.neg_apply, LinearMap.dualMap_apply, shiftEnd_single, shiftEnd_apply]
    by_cases hi : 1 ≤ (i : ℕ)
    · have hr : (i.rev : ℕ) + 1 < n := by rw [Fin.val_rev]; omega
      rw [dif_pos hr, if_pos hi]
      have he : (⟨(i.rev : ℕ) + 1, hr⟩ : Fin n) = (⟨(i : ℕ) - 1, by omega⟩ : Fin n).rev := by
        ext; simp only [Fin.val_rev]; omega
      rw [he]
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
      simp only [hk, Nat.add_sub_cancel, pow_succ]
      ring
    · have hr : ¬ (i.rev : ℕ) + 1 < n := by rw [Fin.val_rev]; omega
      rw [dif_neg hr, if_neg hi]
      simp

namespace WDClass

theorem lpDual_lpZero : (WD.lpZero h).lpDual = WD.lpZero h := by
  rw [WD.lpZero, WD.lpDual_mk]
  exact WD.sound ⟨LinearEquiv.ofFinrankEq _ _ (by simp [Subspace.dual_finrank_eq]),
    fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem lpDual_lpSum (x y : WD h) : (x.lpSum y).lpDual = x.lpDual.lpSum y.lpDual := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.lpSum_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpSum_mk]
      exact WD.sound (iso_sum_dual a b).symm

theorem lpDual_sumList (l : List (WD h)) : (sumList l).lpDual = sumList (l.map WD.lpDual) := by
  induction l with
  | nil => exact lpDual_lpZero
  | cons x l ih =>
    show (x.lpSum (sumList l)).lpDual = x.lpDual.lpSum (sumList (l.map WD.lpDual))
    rw [lpDual_lpSum, ih]

theorem lpDual_lpTw (y : WD h) (s : ℝ) : (y.lpTw s).lpDual = y.lpDual.lpTw (-s) := by
  induction y using WD.ind with
  | hP n a =>
    rw [WD.lpTw_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpTw_mk]
    exact WD.sound (iso_tw_dual a s)

theorem lpDual_lpChar_lpSp (y : WD h) (n : ℕ) :
    (y.lpChar (WD.lpSp h n)).lpDual = y.lpDual.lpChar (WD.lpSp h n) := by
  induction y using WD.ind with
  | hP m a =>
    rw [WD.lpSp, WD.lpChar_mk, WD.lpDual_mk, WD.lpDual_mk, WD.lpChar_mk]
    exact WD.sound ((iso_tensor_dual a (WDRep.sp h n)).symm.trans
      ((WDRep.Iso.refl a.dual).tensor (iso_sp_dual n)))

end WDClass

theorem lpDual_sum_tw_sp : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w),
    (∀ l : List (WD h), (sumList l).lpDual = sumList (l.map WD.lpDual)) ∧
    (∀ (y : WD h) (s : ℝ), (y.lpTw s).lpDual = y.lpDual.lpTw (-s)) ∧
    ∀ (y : WD h) (n : ℕ), (y.lpChar (WD.lpSp h n)).lpDual = y.lpDual.lpChar (WD.lpSp h n) :=
  fun _ _ _ _ _ _ _ _ _ _ =>
    ⟨WDClass.lpDual_sumList, WDClass.lpDual_lpTw, WDClass.lpDual_lpChar_lpSp⟩

end GlobalTheory.WDDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimple
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem exists_frob_pow_mul_ineIncl_mul (m : ℕ) (hm : 0 < m) (σ : Weil h) :
    ∃ (r : ℕ) (τ : Ine (F := E) A) (q : ℤ), r < m ∧
      σ = frob h ^ r * ineIncl h τ * (frob h ^ m) ^ q := by
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdeg : deg (σ * (frob h ^ m) ^ (-(deg σ / m))) = deg σ % m := by
    rw [deg_mul, deg_zpow, deg_pow, deg_frob, Int.emod_def]
    ring
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul (deg_frob (h := h)) (σ * (frob h ^ m) ^ (-(deg σ / m)))
  have hr0 : 0 ≤ deg σ % (m : ℤ) := Int.emod_nonneg _ hm'
  have hr1 : deg σ % (m : ℤ) < m := Int.emod_lt_of_pos _ (by exact_mod_cast hm)
  refine ⟨(deg σ % m).toNat, τ, deg σ / m, by omega, ?_⟩
  have hz : frob h ^ (deg σ % (m : ℤ)).toNat = frob h ^ (deg σ % (m : ℤ)) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hr0]
  rw [hz, ← hdeg, ← hτ, mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]

theorem isSemisimpleRepresentation_of_isSmooth [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Weil h) V) (hρ : IsSmooth ρ)
    (hss : ∀ σ, Module.End.IsSemisimple (ρ σ)) : ρ.IsSemisimpleRepresentation := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 0 < m := ⟨1, one_pos⟩
  refine ⟨fun P => ?_⟩
  have hPinv : P.toSubmodule ∈ Module.End.invtSubmodule (ρ (frob h ^ m)) := by
    rw [Module.End.mem_invtSubmodule]
    intro v hv
    exact P.apply_mem_toSubmodule _ hv
  obtain ⟨Q, hQ, hc⟩ := (Module.End.isSemisimple_iff.mp (hss (frob h ^ m))) _ hPinv
  rw [Module.End.mem_invtSubmodule] at hQ
  let p : Module.End ℂ V := P.toSubmodule.projection Q hc
  have hp1 : ∀ v ∈ P.toSubmodule, p v = v := fun v hv => Submodule.projection_apply_left hc ⟨v, hv⟩
  have hp2 : ∀ v ∈ Q, p v = 0 := fun v hv => Submodule.projection_apply_right hc ⟨v, hv⟩
  have hpm : ∀ v, p v ∈ P.toSubmodule := fun v => Submodule.projection_apply_mem hc v
  have hpT : ρ (frob h ^ m) * p = p * ρ (frob h ^ m) := by
    ext v
    obtain ⟨x, hx, y, hy, rfl⟩ :=
      Submodule.mem_sup.1 (show v ∈ P.toSubmodule ⊔ Q by rw [hc.sup_eq_top]; trivial)
    simp only [Module.End.mul_apply, map_add, hp1 _ hx, hp2 _ hy, add_zero,
      hp1 _ (hPinv hx), hp2 _ (hQ hy), map_zero]
  have hinv : ∀ σ : Weil h, ρ σ * ρ σ⁻¹ = 1 := fun σ => by rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ∀ σ : Weil h, ρ σ⁻¹ * ρ σ = 1 := fun σ => by rw [← map_mul, inv_mul_cancel, map_one]
  let c : Weil h → Module.End ℂ V := fun σ => ρ σ * p * ρ σ⁻¹
  have hcm : ∀ σ v, c σ v ∈ P.toSubmodule := fun σ v => P.apply_mem_toSubmodule σ (hpm _)
  have hc1 : ∀ σ, ∀ v ∈ P.toSubmodule, c σ v = v := by
    intro σ v hv
    show ρ σ (p (ρ σ⁻¹ v)) = v
    rw [hp1 _ (P.apply_mem_toSubmodule _ hv), ← Module.End.mul_apply, hinv, Module.End.one_apply]
  have hper : ∀ σ, c (σ * frob h ^ m) = c σ := by
    intro σ
    simp only [c, _root_.mul_inv_rev, map_mul]
    calc ρ σ * ρ (frob h ^ m) * p * (ρ (frob h ^ m)⁻¹ * ρ σ⁻¹)
        = ρ σ * (ρ (frob h ^ m) * p * ρ (frob h ^ m)⁻¹) * ρ σ⁻¹ := by simp only [mul_assoc]
      _ = ρ σ * (p * (ρ (frob h ^ m) * ρ (frob h ^ m)⁻¹)) * ρ σ⁻¹ := by rw [hpT]; simp only [mul_assoc]
      _ = ρ σ * p * ρ σ⁻¹ := by rw [hinv, mul_one]
  have hzper : ∀ σ (q : ℤ), c (σ * (frob h ^ m) ^ q) = c σ := by
    intro σ q
    induction q using Int.induction_on with
    | zero => simp
    | succ q ih => rw [_root_.zpow_add_one, ← mul_assoc, hper, ih]
    | pred q ih =>
      rw [← ih, ← hper, mul_assoc, ← _root_.zpow_add_one]
      congr 3
      ring
  have hFfin := hρ.finite_range
  have hCfin : (Set.range c).Finite := by
    refine (((Set.finite_Iio m).prod (hFfin.prod hFfin)).image
      (fun t : ℕ × (Module.End ℂ V × Module.End ℂ V) =>
        ρ (frob h ^ t.1) * (t.2.1 * p * t.2.2) * ρ ((frob h ^ t.1)⁻¹))).subset ?_
    rintro _ ⟨σ, rfl⟩
    obtain ⟨r, τ, q, hr, rfl⟩ := exists_frob_pow_mul_ineIncl_mul m hm σ
    refine ⟨(r, ρ (ineIncl h τ), ρ (ineIncl h τ⁻¹)), ⟨hr, ⟨τ, rfl⟩, ⟨τ⁻¹, rfl⟩⟩, ?_⟩
    show _ = c _
    rw [hzper]
    simp only [c, _root_.mul_inv_rev, map_mul, map_inv, mul_assoc]
  set Cf := hCfin.toFinset with hCf
  have hCmem : ∀ x, x ∈ Cf ↔ ∃ σ, c σ = x := fun x => by simp [Cf]
  have hcard : Cf.card ≠ 0 := Finset.card_ne_zero_of_mem ((hCmem _).2 ⟨1, rfl⟩)
  let S : Module.End ℂ V := ∑ x ∈ Cf, x
  let qa : Module.End ℂ V := (Cf.card : ℂ)⁻¹ • S
  have hSm : ∀ v, S v ∈ P.toSubmodule := by
    intro v
    simp only [S]
    rw [LinearMap.sum_apply]
    refine P.toSubmodule.sum_mem fun x hx => ?_
    obtain ⟨σ, rfl⟩ := (hCmem x).1 hx
    exact hcm σ v
  have hS1 : ∀ v ∈ P.toSubmodule, S v = (Cf.card : ℂ) • v := by
    intro v hv
    simp only [S]
    rw [LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro x hx
    obtain ⟨σ, rfl⟩ := (hCmem x).1 hx
    exact hc1 σ v hv
  have hSeq : ∀ g : Weil h, ρ g * S = S * ρ g := by
    intro g
    have h1 : ∑ x ∈ Cf, ρ g * x * ρ g⁻¹ = ∑ x ∈ Cf, x := by
      refine Finset.sum_nbij' (fun x => ρ g * x * ρ g⁻¹) (fun x => ρ g⁻¹ * x * ρ g)
        ?_ ?_ ?_ ?_ (fun _ _ => rfl)
      · intro x hx
        obtain ⟨σ, rfl⟩ := (hCmem x).1 (Finset.mem_coe.1 hx)
        exact Finset.mem_coe.2 ((hCmem _).2 ⟨g * σ, by simp only [c, _root_.mul_inv_rev, map_mul, mul_assoc]⟩)
      · intro x hx
        obtain ⟨σ, rfl⟩ := (hCmem x).1 (Finset.mem_coe.1 hx)
        exact Finset.mem_coe.2 ((hCmem _).2 ⟨g⁻¹ * σ, by
          simp only [c, _root_.mul_inv_rev, map_mul, inv_inv, mul_assoc]⟩)
      · intro x _
        simp only [← mul_assoc, hinv', one_mul]
        rw [mul_assoc, hinv', mul_one]
      · intro x _
        simp only [← mul_assoc, hinv, one_mul]
        rw [mul_assoc, hinv, mul_one]
    calc ρ g * S = (∑ x ∈ Cf, ρ g * x * ρ g⁻¹) * ρ g := by
          rw [Finset.sum_mul]
          simp only [S, Finset.mul_sum, mul_assoc, hinv', mul_one]
      _ = S * ρ g := by rw [h1]
  have hqm : ∀ v, qa v ∈ P.toSubmodule := fun v => P.toSubmodule.smul_mem _ (hSm v)
  have hq1 : ∀ v ∈ P.toSubmodule, qa v = v := by
    intro v hv
    show (Cf.card : ℂ)⁻¹ • S v = v
    rw [hS1 v hv, inv_smul_smul₀ (by exact_mod_cast hcard)]
  have hqe : ∀ g v, qa (ρ g v) = ρ g (qa v) := by
    intro g v
    show (Cf.card : ℂ)⁻¹ • S (ρ g v) = ρ g ((Cf.card : ℂ)⁻¹ • S v)
    rw [map_smul, ← Module.End.mul_apply S, ← hSeq, Module.End.mul_apply]
  let q' : V →ₗ[ℂ] P.toSubmodule := qa.codRestrict P.toSubmodule hqm
  have hcompl : IsCompl P.toSubmodule (LinearMap.ker q') :=
    LinearMap.isCompl_of_proj fun x => Subtype.ext (hq1 x x.2)
  refine ⟨⟨LinearMap.ker q', fun g v hv => ?_⟩, ?_⟩
  · have h0 : qa v = 0 := congrArg Subtype.val hv
    apply Subtype.ext
    show qa (ρ g v) = 0
    rw [hqe, h0, map_zero]
  · rw [isCompl_iff, disjoint_iff, codisjoint_iff,
      ← Subrepresentation.toSubmodule_injective.eq_iff,
      ← Subrepresentation.toSubmodule_injective.eq_iff]
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl
    exact hcompl

end GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.WDRep

theorem isSemisimpleRepresentation_rho : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (n : ℕ) (a : WDRep h (Fin n → ℂ)), a.ρ.IsSemisimpleRepresentation := by
  intro E Ω _ _ _ _ _ A w h n a
  exact isSemisimpleRepresentation_of_isSmooth a.ρ a.smooth a.semisimple

end GlobalTheory.WeilDeligne.WDRep
end
end

