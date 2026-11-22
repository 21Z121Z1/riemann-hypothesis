import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0217
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0201
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0088
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
import GroundTheory.PAdicHodge.AxLemma
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0348
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleCocyclesCardLeSumDims
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.AdmBound

theorem inZZ_mono {k : Type} [Field k] {l n m r : ℕ} {R : RingPG k l} (D : ModPG R n (Vc k m)) (Dt : TopData n r)
    {N N' : Lats k n m} (h : ∀ i, N i ≤ N' i) {b g : ZMod n → Vc k m} (hz : InZZ D Dt N b g) :
    InZZ D Dt N' b g := by
  intro i
  obtain ⟨h0, h1, h2, h3⟩ := hz i
  refine ⟨h0, sh_le_sh 1 (h i) h1, fun hG => sh_le_sh _ (h i) (h2 hG), fun hB => ?_⟩
  obtain ⟨hb, x, hx, hx'⟩ := h3 hB
  exact ⟨sh_le_sh _ (pull_le_pull _ (h (i - 1))) hb, x, h i hx, sh_le_sh _ (h i) hx'⟩

theorem repr_sum {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A : Ob k G) {ι : Type} (z : ι → G → Fin A.m → k)
    (b g : ι → ZMod n → Vc k A.m) (h : ∀ a, Repr F A (z a) (b a) (g a)) (a₀ : ι) (c : ι → k) (t : Finset ι) :
    Repr F A (∑ a ∈ t, c a • z a) (∑ a ∈ t, c a • b a) (∑ a ∈ t, c a • g a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h0 := GlobalTheory.T.repr_smul_add F A (-1) (z a₀) (z a₀) (b a₀) (g a₀) (b a₀) (g a₀) (h a₀) (h a₀)
    simpa only [neg_one_smul, neg_add_cancel, Finset.sum_empty] using h0
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.T.repr_smul_add F A (c a) (z a) _ (b a) (g a) _ _ (h a) ih

theorem indep_pairs {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A : Ob k G) {s : ℕ} (z : Fin s → G → Fin A.m → k)
    (b g : Fin s → ZMod n → Vc k A.m) (h : ∀ a, Repr F A (z a) (b a) (g a))
    (hz : LinearIndependent k (fun a => (cob A).mkQ (z a))) :
    LinearIndependent k (fun a => (herrB (F.D A)).mkQ (b a, g a)) := by
  classical
  rw [linearIndependent_iff'] at hz ⊢
  intro t c hc a ha
  have e1 : ∑ a ∈ t, c a • (herrB (F.D A)).mkQ (b a, g a) =
      (herrB (F.D A)).mkQ (∑ a ∈ t, c a • b a, ∑ a ∈ t, c a • g a) := by
    rw [show ((∑ a ∈ t, c a • b a, ∑ a ∈ t, c a • g a) : (ZMod n → Vc k A.m) × (ZMod n → Vc k A.m)) =
        ∑ a ∈ t, c a • (b a, g a) by ext <;> simp [Prod.fst_sum, Prod.snd_sum]]
    simp only [map_sum, map_smul]
  rw [e1, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
  have hcob := GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary F A _ _ _ (repr_sum F A z b g h a c t) hc
  refine hz t c ?_ a ha
  have e2 : ∑ a ∈ t, c a • (cob A).mkQ (z a) = (cob A).mkQ (∑ a ∈ t, c a • z a) := by
    simp only [map_sum, map_smul]
  rw [e2, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hcob

private theorem exists_ne_zero_smul_mem_of_mem_span' (hψ : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi) {k : Type} [Field k] {l n m r : ℕ} [Fact l.Prime]
    [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (Dt : TopData n r)
    (N : Lats k n m) (hr : m = r) (hc : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι) (h1 : Dt.T1 l) (h2 : Dt.T2 l)
    (h3 : Dt.T3 l) (habc : ABC D Dt.w Dt.wst N)
    (hsen : ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen (D.γ i) (N i) (a : k) = 0) ∧
      (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen (D.γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧
      (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen (D.γ i) (N i) (a : k) = r ∧
        EPoly (D.γ i) (N i) (Dt.wst i + 1)))
    (s : ℕ) (z : Fin s → (ZMod n → Vc k m) × (ZMod n → Vc k m)) (hz : ∀ a, InZZ D Dt N (z a).1 (z a).2)
    (hind : LinearIndependent k (fun a => (herrB D).mkQ (z a))) : s ≤ Dt.dsum := by
  subst hr
  exact GlobalTheory.T.card_cocycles_independent_mod_coboundaries_le hψ D ι Dt N hc h1 h2 h3 habc hsen s z hz hind

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.LemmaPsi → ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (s : ℕ) (z : Fin s → G → Fin M.T.m → k), (∀ a, z a ∈ M.twistedModelAdmissibleCocycles M.T) → LinearIndependent k (fun a => (cob M.T).mkQ (z a)) → s ≤ Dt.dsum := by
  intro hψ k G _ _ l n _ _ _ R F r Dt M ι hc h1 h2 h3 s z hz hind
  choose N b g hN hR hZ using fun a => GlobalTheory.T.exists_phiGammaModel_extension_cocycle_pair F M h1 h2 h3 M.T (z a) (hz a)
  obtain ⟨Nm, hNm, hmax⟩ := GlobalTheory.T.exists_largest_model' F M M.T M.Nstd M.std_model
  have hS := GlobalTheory.T.twistedPhiGammaModel_sen_weight_count F M h1 h2 h3 Nm hNm (hmax _ M.std_model)
  refine exists_ne_zero_smul_mem_of_mem_span' hψ (F.D M.T) ι Dt Nm M.T_m hc h1 h2 h3 (GlobalTheory.T.obj_and_abc_of_model F M M.T Nm hNm).2
    (fun i => ⟨(hS i).1, (hS i).2.1, fun hB => ⟨(hS i).2.2 hB,
      GlobalTheory.Models.EPolyModel.model_ePoly F M h1 h3 M.T Nm hNm i hB⟩⟩)
    s (fun a => (b a, g a)) (fun a => inZZ_mono _ _ (hmax _ (hN a)) (hZ a)) (indep_pairs F M.T z b g hR hind)

end GlobalTheory.Models.AdmBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosed
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfSat

section Coeff

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

theorem coeff_pow_mul_add (r : ℕ) (w : WittVector p R) (i : ℕ) :
    (((p : WittVector p R) ^ r * w).coeff (i + r)) = (w.coeff i) ^ (p ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : (p : WittVector p R) ^ (r + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ r * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h, show i + (r + 1) = (i + r).succ by omega, WittVector.verschiebung_coeff_succ,
      WittVector.coeff_frobenius_charP, ih, ← pow_mul, pow_succ]

theorem coeff_pow_mul_lt (n : ℕ) (w : WittVector p R) :
    ∀ j, j < n → ((p : WittVector p R) ^ n * w).coeff j = 0 := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    have h : (p : WittVector p R) ^ (n + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ n * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h]
    cases j with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ j =>
      rw [WittVector.verschiebung_coeff_succ, WittVector.coeff_frobenius_charP, ih j (by omega),
        zero_pow hp.out.ne_zero]

theorem coeff_eq_of_dvd {n : ℕ} {u v : WittVector p R} (h : (p : WittVector p R) ^ n ∣ u - v)
    (j : ℕ) (hj : j < n) : u.coeff j = v.coeff j := by
  obtain ⟨w, hw⟩ := h
  have hz : WittVector.truncate n (u - v) = 0 := by
    ext k
    rw [WittVector.coeff_truncate, hw, coeff_pow_mul_lt n w k k.2]
    simp
  have ht : WittVector.truncate n u = WittVector.truncate n v := by
    rw [map_sub, sub_eq_zero] at hz; exact hz
  have := congrArg (TruncatedWittVector.coeff (⟨j, hj⟩ : Fin n)) ht
  simpa [WittVector.coeff_truncate] using this

end Coeff

variable (l : ℕ) [Fact l.Prime]

theorem exists_of_pow_eq (r : ℕ) (d : Cb l) (b : OCb l)
    (h : d ^ (l ^ r) = algebraMap (OCb l) (Cb l) b) : ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = d := by
  refine ⟨(iterateFrobeniusEquiv (OCb l) l r).symm b, ?_⟩
  apply iterateFrobenius_inj (Cb l) l r
  rw [iterateFrobenius_def, iterateFrobenius_def, h, ← map_pow]
  congr 1
  have := (iterateFrobeniusEquiv (OCb l) l r).apply_symm_apply b
  rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at this

theorem mem_range_of_pow_mul (r : ℕ) (y : WCb l)
    (hy : ∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * y - inclW l a) :
    ∃ a : Ainf l, y = inclW l a := by
  have hc : ∀ i, ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = y.coeff i := by
    intro i
    obtain ⟨a, ha⟩ := hy (i + r + 1)
    have he := coeff_eq_of_dvd ha (i + r) (by omega)
    rw [coeff_pow_mul_add] at he
    exact exists_of_pow_eq l r _ _ (by rw [he]; exact WittVector.map_coeff _ _ _)
  choose c hc using hc
  refine ⟨WittVector.mk l c, ?_⟩
  ext i
  rw [show inclW l (WittVector.mk l c) = WittVector.map (algebraMap (OCb l) (Cb l)) (WittVector.mk l c)
    from rfl, WittVector.map_coeff]
  exact (hc i).symm

theorem mem_ideal_of_saturated : ∀ (l : ℕ) [Fact l.Prime] (ι : Ainf l), IsUnit (inclW l ι) →
    ∀ (r : ℕ) (x : WCb l), (∀ n : ℕ, ∃ a : Ainf l,
      (l : WCb l) ^ n ∣ (l : WCb l) ^ r * x - inclW l (ι * a)) →
    ∃ a : Ainf l, x = inclW l (ι * a) := by
  intro l _ ι hu r x hx
  obtain ⟨u, hu⟩ := hu
  obtain ⟨a, ha⟩ := mem_range_of_pow_mul l r (↑u⁻¹ * x) (by
    intro n
    obtain ⟨a, w, hw⟩ := hx n
    refine ⟨a, ↑u⁻¹ * w, ?_⟩
    have : (l : WCb l) ^ r * (↑u⁻¹ * x) - inclW l a
        = ↑u⁻¹ * ((l : WCb l) ^ r * x - inclW l (ι * a)) := by
      rw [map_mul, ← hu, mul_sub]
      rw [← mul_assoc (↑u⁻¹ : WCb l) (↑u) _, Units.inv_mul, one_mul]
      ring
    rw [this, hw]; ring)
  refine ⟨a, ?_⟩
  rw [map_mul, ← ha, ← hu, ← mul_assoc, Units.mul_inv, one_mul]

end GlobalTheory.AinfSat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfUnitBoundedTeichmullerFlatDenominatorsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_unit_bounded_teichmullerFlat_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), IsUnit (inclW l a) → ∀ n : ℕ, ∃ (m : ℕ) (t : Ainf l), (l : Ainf l) ^ n ∣ t * a - bk.ev X ^ m := by
  first | exact @GlobalTheory.BSP.BddDen.main | exact GlobalTheory.BSP.BddDen.main | (intros; apply GlobalTheory.BSP.BddDen.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjectiveStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective : ∀ (l : ℕ) [Fact l.Prime] (c : Core l), c.TensorInj := by
  first | exact @GlobalTheory.MemLoc.TensorInj.tensorInj | exact GlobalTheory.MemLoc.TensorInj.tensorInj | (intros; apply GlobalTheory.MemLoc.TensorInj.tensorInj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxBdRPlusFilMatrixMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem use₁₀ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n d : ℕ) (X Z : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * X i j ∈ Per.FilP l n) → (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * Z i j ∈ Per.FilP l n) → ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * (X * Z) i j ∈ Per.FilP l n := by
  intro l _ K bk n d X Z ⟨k₁, s₁, h₁⟩ ⟨k₂, s₂, h₂⟩
  refine ⟨k₁ + k₂, s₁ * s₂, fun i j => ?_⟩
  have e : aDp l (bk.ev ((s₁ * s₂) i j)) - (l : Per.BdRp l) ^ (k₁ + k₂) * (X * Z) i j
      = ∑ m, (aDp l (bk.ev (s₁ i m)) * (aDp l (bk.ev (s₂ m j)) - (l : Per.BdRp l) ^ k₂ * Z m j)
        + (aDp l (bk.ev (s₁ i m)) - (l : Per.BdRp l) ^ k₁ * X i m) * ((l : Per.BdRp l) ^ k₂ * Z m j)) := by
    rw [Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_mul, pow_add]
    ring
  rw [e]
  exact Ideal.sum_mem _ fun m _ => Ideal.add_mem _ (Ideal.mul_mem_left _ _ (h₂ m j)) (Ideal.mul_mem_right _ _ (h₁ i m))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.AwayT

theorem away_of_injective {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R)
    (hu : IsUnit (algebraMap R S t))
    (hs : ∀ b : S, ∃ (r : ℕ) (x : R), b * algebraMap R S t ^ r = algebraMap R S x)
    (hi : Function.Injective (algebraMap R S)) : IsLocalization.Away t S :=
  IsLocalization.Away.mk t hu hs fun _ _ h => ⟨0, by rw [hi h]⟩

theorem lift_injective {R P S : Type} [CommRing R] [CommRing P] [CommRing S] [Algebra R P] (x : R)
    [IsLocalization.Away x P] (f : R →+* S) (g : P →+* S) (hg : ∀ a, g (algebraMap R P a) = f a)
    (hf : Function.Injective f) : Function.Injective g := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj x z
  have h1 : f a = 0 := by rw [← hg, ← ha, map_mul, hz, zero_mul]
  have h2 : a = 0 := hf (h1.trans (map_zero f).symm)
  rw [h2, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (S := P) x).pow n).mul_left_eq_zero.1 ha

variable {l : ℕ} [Fact l.Prime]

theorem plusInj (C : Core l) : C.PlusInj :=
  lift_injective ((l : ℕ) : Per.Acris l) C.j C.jP C.jP_alg (crisP_injective l C.j C.j_cris)

theorem plusToB_injective (C : Core l) : Function.Injective (plusToB l) := fun x y h =>
  plusInj C ((BdRField.bdR_isField l).2.1 (by rw [← C.ι_plusToB, ← C.ι_plusToB, h]))

theorem acris_injective (C : Core l) : Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) :=
  fun x y h => crisP_injective l C.j C.j_cris
    ((BdRField.bdR_isField l).2.1 (by rw [← C.ι_j, ← C.ι_j, h]))

theorem awayT (C : Core l) : C.AwayT :=
  away_of_injective C.t (core_t_unit_fil l C).1 (GlobalTheory.T.bcris_eq_acris_localization_periodT l C) (acris_injective C)

theorem plusAwayT (C : Core l) : C.PlusAwayT := by
  letI := (plusToB l).toAlgebra
  have e : ∀ x : Per.Acris l, algebraMap (BcrisP l) (Per.Bcris l) (algebraMap _ _ x) =
      algebraMap (Per.Acris l) (Per.Bcris l) x := plusToB_alg
  refine away_of_injective _ ?_ (fun b => ?_) (plusToB_injective C)
  · rw [e]
    exact (core_t_unit_fil l C).1
  · obtain ⟨r, x, h⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
    exact ⟨r, algebraMap _ _ x, by rw [e, e]; exact h⟩

theorem away_and_inj (l : ℕ) [Fact l.Prime] (C : Core l) : C.AwayT ∧ C.PlusAwayT ∧ C.PlusInj :=
  ⟨awayT C, plusAwayT C, plusInj C⟩

end GlobalTheory.MemLoc.AwayT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaFiniteGaloisPadic
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem norm_natCast_self_Om (l : ℕ) [Fact l.Prime] : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have h : (l : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := (map_natCast _ _).symm
  rw [h, PadicAlgCl.norm_extends, Padic.norm_p]

theorem axConstant_le_sq (l : ℕ) [hl : Fact l.Prime] : GroundTheory.PAdicHodge.axConstant l ≤ (l : ℝ) ^ 2 := by
  have h2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hexp : (l : ℝ) / ((l : ℝ) - 1) ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  unfold GroundTheory.PAdicHodge.axConstant
  calc (l : ℝ) ^ ((l : ℝ) / ((l : ℝ) - 1) ^ 2) ≤ (l : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    _ = (l : ℝ) ^ 2 := by norm_cast

theorem axIn_padic : ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra ℚ_[l] L] [ValuativeExtension ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [IsGalois ℚ_[l] L] [Algebra L (Om l)] [IsScalarTower ℚ_[l] L (Om l)], AxIn ℚ_[l] L l := by
  intro l _ L _ _ _ _ _ _ _ _ _ _
  intro J x hx
  have hO := GlobalTheory.T.localFieldInteger_iff_algebraicClosureNorm l L
  let φ : L →ₐ[ℚ_[l]] Om l := IsScalarTower.toAlgHom ℚ_[l] L (Om l)
  have hφ : ∀ y : L, φ y = algebraMap L (Om l) y := fun y => rfl
  let F : IntermediateField ℚ_[l] L := IntermediateField.fixedField J
  let E : IntermediateField ℚ_[l] (Om l) := F.map φ
  have hmove : ∀ g : Gal(Om l/E), ‖g (φ x) - φ x‖ ≤ 1 := by
    intro g
    let g' : Om l ≃ₐ[ℚ_[l]] Om l := g.restrictScalars ℚ_[l]
    let τ : L ≃ₐ[ℚ_[l]] L := AlgEquiv.restrictNormalHom L g'
    have hτ : ∀ y : L, φ (τ y) = g' (φ y) := fun y => AlgEquiv.restrictNormal_commutes g' L y
    have hτJ : τ ∈ J := by
      rw [← IntermediateField.fixingSubgroup_fixedField J]
      rintro ⟨y, hy⟩
      apply φ.toRingHom.injective
      change φ (τ y) = φ y
      rw [hτ]
      have hyE : φ y ∈ E := ⟨y, hy, rfl⟩
      exact g.commutes ⟨φ y, hyE⟩
    have h1 := (hO (τ x - x)).1.1 (hx τ hτJ)
    rw [map_sub, ← hφ, ← hφ, hτ] at h1
    exact h1
  obtain ⟨Y, hYE, hY⟩ := GroundTheory.PAdicHodge.ax_lemma (K := E) (φ x) hmove
  obtain ⟨y, hyF, rfl⟩ := hYE
  refine ⟨y, fun σ hσ => (IntermediateField.mem_fixedField_iff J y).1 hyF σ hσ, ?_⟩
  rw [(hO _).1, map_mul, map_pow, map_natCast, map_sub, norm_mul, norm_pow, norm_natCast_self_Om, ← hφ, ← hφ]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hc := axConstant_le_sq l
  rw [mul_one] at hY
  calc ((l : ℝ)⁻¹) ^ 2 * ‖φ x - φ y‖ ≤ ((l : ℝ)⁻¹) ^ 2 * (l : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (hY.trans hc) (by positivity)
    _ = 1 := by rw [inv_pow, inv_mul_cancel₀ (by positivity)]

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisMatrixMapCancelLeft
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

theorem mat_cancel_left {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (B M M' : Matrix n n R) (hB : B.det ∈ nonZeroDivisors R) (h : B * M = B * M') : M = M' := by
  have h2 : B.det • M = B.det • M' := by
    have e : ∀ N : Matrix n n R, B.det • N = B.adjugate * (B * N) := fun N => by
      rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [e, e, h]
  ext i j
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h3
  have h4 : (M i j - M' i j) * B.det = 0 := by rw [sub_mul, mul_comm (M i j), mul_comm (M' i j), h3, sub_self]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff_right.1 hB) _ h4)

theorem bas_map_cancel_left : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (C : Type) [CommRing C] (F : bk.DS bk.ρ₀ →+* C), F (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈ nonZeroDivisors C → ∀ M M' : Matrix (Fin d) (Fin d) C, ht.bas.map F * M = ht.bas.map F * M' → M = M' := by
  intro l _ K bk d ρ τ s ht C _ F hE M M' h
  set G : bk.S →+* C := F.comp (toDisc l (X : bk.S) bk.ρ₀) with hG
  have hbas : ht.bas.map F = s.X.map G * ht.Z.map F := by
    rw [bas, Matrix.map_mul, Matrix.map_map]; rfl
  have hl : IsUnit (G (l : bk.S)) := by
    rw [map_natCast]
    have := (isUnit_l_disc l (X : bk.S) bk.ρ₀).map F
    rwa [map_natCast] at this
  have hc : G ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) ∈ nonZeroDivisors C := by
    rw [map_mul, map_pow, map_pow]
    exact Submonoid.mul_mem _ (Submonoid.pow_mem _ hl.mem_nonZeroDivisors _) (Submonoid.pow_mem _ hE _)
  have hdet : (s.X.map G).det * (s.X'.map G).det = G ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) ^ d := by
    rw [← Matrix.det_mul, ← Matrix.map_mul, s.X_mul, Matrix.smul_one_eq_diagonal, Matrix.diagonal_map (map_zero G),
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hX : (s.X.map G).det ∈ nonZeroDivisors C :=
    (mul_mem_nonZeroDivisors.1 (hdet ▸ Submonoid.pow_mem _ hc _)).1
  have hZ : IsUnit (ht.Z.map F).det := by
    have := ht.Z_unit.map F.mapMatrix
    exact (Matrix.isUnit_iff_isUnit_det _).1 this
  refine mat_cancel_left _ M M' ?_ h
  rw [hbas, Matrix.det_mul]
  exact Submonoid.mul_mem _ hX hZ.mem_nonZeroDivisors

end GlobalTheory.BSP.Height
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisOfCongrBasisModNilpotentIdeal
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem family_congr_basis_mod_nilpotent (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (ι : Type) (b b' : ι → M) (I : Ideal R) (n : ℕ) :
    I ^ n = ⊥ → LinearIndependent R b → Submodule.span R (Set.range b) = ⊤ →
    (∀ k, b' k - b k ∈ I • (⊤ : Submodule R M)) →
    LinearIndependent R b' ∧ Submodule.span R (Set.range b') = ⊤ := by
  intro hIn hli hsp hb
  let B : Module.Basis ι R M := Module.Basis.mk hli (by rw [hsp])
  let ν : Module.End R M := B.constr R (fun i => b' i - b i)
  have hν : ∀ i, ν (b i) = b' i - b i := by
    intro i
    have := B.constr_basis R (fun i => b' i - b i) i
    simpa [B, Module.Basis.mk_apply] using this
  have hrange : LinearMap.range ν ≤ I • (⊤ : Submodule R M) := by
    have e : LinearMap.range ν = Submodule.map ν (Submodule.span R (Set.range b)) := by
      rw [hsp, LinearMap.range_eq_map]
    rw [e, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    show ν (b i) ∈ _
    rw [hν]; exact hb i
  have hpow : ∀ k : ℕ, LinearMap.range (ν ^ k) ≤ I ^ k • (⊤ : Submodule R M) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]
      calc Submodule.map ν (LinearMap.range (ν ^ k))
          ≤ Submodule.map ν (I ^ k • (⊤ : Submodule R M)) := Submodule.map_mono ih
        _ = I ^ k • Submodule.map ν ⊤ := Submodule.map_smul'' _ _ _
        _ ≤ I ^ k • (I • (⊤ : Submodule R M)) := by
            exact Submodule.smul_mono le_rfl (by rw [← LinearMap.range_eq_map]; exact hrange)
        _ = I ^ (k + 1) • (⊤ : Submodule R M) := by
            rw [pow_succ, Submodule.mul_smul]
  have hnil : IsNilpotent ν := by
    refine ⟨n, ?_⟩
    have := hpow n
    rw [hIn, Submodule.bot_smul, le_bot_iff, LinearMap.range_eq_bot] at this
    exact this
  have hunit : IsUnit (1 + ν) := hnil.isUnit_one_add
  have hbij : Function.Bijective ⇑(1 + ν) := (Module.End.isUnit_iff _).1 hunit
  have hcomp : b' = ⇑(1 + ν) ∘ b := by
    funext i; simp [hν]
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact hli.map' (1 + ν) (LinearMap.ker_eq_bot.2 hbij.1)
  · rw [hcomp, Set.range_comp, ← Submodule.map_span, hsp, ← LinearMap.range_eq_map,
      LinearMap.range_eq_top.2 hbij.2]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BezoutEisensteinDerivativePrimePowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bezout_eisenstein_derivative_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (c : ℕ) (a b : Polynomial (Wq l bk.a)), a * bk.Ep + b * Polynomial.derivative bk.Ep = Polynomial.C ((l : Wq l bk.a) ^ c) := by
  first | exact @GlobalTheory.BSP.bezout_Ep_derivative | exact GlobalTheory.BSP.bezout_Ep_derivative | (intros; apply GlobalTheory.BSP.bezout_Ep_derivative <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BkOnLeMapOfSurjectiveStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bkOn_le_map_h1MapSubgroup_of_surjective : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Kills i A → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y₂ : Type) [AddCommGroup Y₂] [Module A Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] (f : Y →ₗ[A] Y₂), Function.Surjective f → ∀ v, bkOn bkP i (Tgl i s) κ Y₂ v ≤ (bkOn bkP i (Tgl i s) κ Y v).map (h1MapSubgroup (Tgl i s) κ (DecV N v) f) := by
  first | exact @GlobalTheory.NewPrime.bkOn_le_map_of_surjective | exact GlobalTheory.NewPrime.bkOn_le_map_of_surjective | (intros; apply GlobalTheory.NewPrime.bkOn_le_map_of_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimOfQlDimensionFormulaStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoDim_of_Ql_dimensionFormula : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), GlobalTheory.Published.BlochKato.DimFormula (P.PD K) → Formalism.MainNotions.LocalSituation.bkADim (P.PD K) := by
  first | exact @GlobalTheory.bkADim_of_dimFormula | exact GlobalTheory.bkADim_of_dimFormula | (intros; apply GlobalTheory.bkADim_of_dimFormula <;> assumption)
end

