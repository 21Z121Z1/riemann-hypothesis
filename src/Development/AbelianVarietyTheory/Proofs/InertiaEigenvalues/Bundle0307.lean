import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0199
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0261
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0250
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0293
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Decompl

namespace GlobalTheory.HWL.TensorWitt

section Coord

variable {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
  (b : Module.Basis I Z O) {W : Type} [CommRing W] [Algebra Z W]

private theorem crd_tmul_lemma (i : I) (o : O) (v : W) :
    crd b i (o ⊗ₜ[Z] v) = b.coord i o • v := by
  simp only [crd, TensorProduct.lift.tmul, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.lsmul_apply]

private theorem crd_mul_lemma_2 (i : I) (c : W) (y : O ⊗[Z] W) :
    crd b i ((1 : O) ⊗ₜ[Z] c * y) = c * crd b i y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, crd_tmul_lemma, crd_tmul_lemma]
    exact (mul_smul_comm _ _ _).symm
  | add y z hy hz => rw [mul_add, map_add, map_add, hy, hz, mul_add]

private theorem sum_basis_tmul_crd_eq (y : O ⊗[Z] W) : ∑ i, b i ⊗ₜ[Z] crd b i y = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    simp_rw [crd_tmul_lemma, Module.Basis.coord_apply, ← TensorProduct.smul_tmul,
      ← TensorProduct.sum_tmul, Module.Basis.sum_repr]
  | add y z hy hz =>
    simp_rw [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hy, hz]

private theorem crd_sum_lemma_4 (j : I) (v : I → W) : crd b j (∑ i, b i ⊗ₜ[Z] v i) = v j := by
  classical
  simp [map_sum, crd_tmul_lemma, Module.Basis.coord_apply, Finsupp.single_apply]

theorem mem_pow_iff (w : W) (n : ℕ) (x : O ⊗[Z] W) :
    x ∈ Ideal.span {((1 : O) ⊗ₜ[Z] w) ^ n} ↔ ∀ i, crd b i x ∈ Ideal.span {w ^ n} := by
  rw [Algebra.TensorProduct.tmul_pow, one_pow, Ideal.mem_span_singleton]
  simp_rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨crd b i y, crd_mul_lemma_2 b i _ y⟩
  · intro h
    choose c hc using h
    refine ⟨∑ i, b i ⊗ₜ[Z] c i, ?_⟩
    conv_lhs => rw [← sum_basis_tmul_crd_eq b x]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

include b in

theorem complete_tensor (w : W) [h : IsAdicComplete (Ideal.span {w}) W] :
    IsAdicComplete (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
  have key : ∀ (n : ℕ) (x : O ⊗[Z] W),
      x ∈ (Ideal.span {(1 : O) ⊗ₜ[Z] w} ^ n • ⊤ : Submodule (O ⊗[Z] W) (O ⊗[Z] W)) ↔
        ∀ i, crd b i x ∈ (Ideal.span {w} ^ n • ⊤ : Submodule W W) := by
    intro n x
    simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact mem_pow_iff b w n x
  have H1 : IsHausdorff (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
    refine ⟨fun x hx => ?_⟩
    have hi : ∀ i, crd b i x = 0 := fun i =>
      IsHausdorff.haus h.toIsHausdorff _ fun n => by
        rw [SModEq.sub_mem, sub_zero]
        exact (key n x).1 (by simpa [SModEq.sub_mem] using hx n) i
    rw [← sum_basis_tmul_crd_eq b x]
    simp [hi]
  have H2 : IsPrecomplete (Ideal.span {(1 : O) ⊗ₜ[Z] w}) (O ⊗[Z] W) := by
    refine ⟨fun f hf => ?_⟩
    have hfi : ∀ i, ∃ L : W, ∀ n,
        crd b i (f n) ≡ L [SMOD (Ideal.span {w} ^ n • ⊤ : Submodule W W)] := fun i =>
      IsPrecomplete.prec h.toIsPrecomplete fun {m n} hmn => by
        rw [SModEq.sub_mem, ← map_sub]
        exact (key m _).1 (SModEq.sub_mem.1 (hf hmn)) i
    choose L hL using hfi
    refine ⟨∑ i, b i ⊗ₜ[Z] L i, fun n => ?_⟩
    rw [SModEq.sub_mem, key]
    intro i
    rw [map_sub, crd_sum_lemma_4]
    exact SModEq.sub_mem.1 (hL i n)
  exact { toIsHausdorff := H1, toIsPrecomplete := H2 }

end Coord

variable {l : ℕ} [Fact l.Prime]

theorem inclW_injective : Function.Injective (inclW l) := by
  unfold inclW
  exact WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem tiltWitt_eq_zero_of_prime_mul_eq_zero (x : WCb l) (h : ((l : ℕ) : WCb l) * x = 0) : x = 0 := by
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  ext n
  have h1 := WittVector.mul_charP_coeff_succ (p := l) x n
  rw [mul_comm, h, WittVector.zero_coeff] at h1
  rw [WittVector.zero_coeff]
  exact (pow_eq_zero_iff (Fact.out : l.Prime).ne_zero).1 h1.symm

theorem ainf_saturated_in_tiltWitt_prime (a : Loc.Ainf l) (w : WCb l) (h : inclW l a = ((l : ℕ) : WCb l) * w) :
    ∃ a', inclW l a' = w := by
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  refine ⟨WittVector.mk l fun n => (frobeniusEquiv (OCb l) l).symm (a.coeff (n + 1)), ?_⟩
  ext n
  have h1 := congrArg (fun z : WCb l => z.coeff (n + 1)) h
  simp only [inclW, WittVector.map_coeff] at h1
  rw [mul_comm, WittVector.mul_charP_coeff_succ] at h1
  apply frobenius_inj (Cb l) l
  simp only [inclW, WittVector.map_coeff, WittVector.coeff_mk]
  rw [← RingHom.map_frobenius, frobenius_apply_frobeniusEquiv_symm, h1, frobenius_def]

theorem not_isUnit_teich (e : OCb l) (he : ¬ IsUnit (e - 1)) :
    ¬ IsUnit (WittVector.teichmuller l e - 1 : Loc.Ainf l) := by
  intro hu
  apply he
  have h1 := hu.map (WittVector.constantCoeff : WittVector l (OCb l) →+* OCb l)
  rwa [map_sub, map_one, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h1

private theorem crd_tensorProduct_map_eq {Z O I W W' : Type} [CommRing Z] [CommRing O] [Algebra Z O]
    [Fintype I] (b : Module.Basis I Z O) [CommRing W] [Algebra Z W] [CommRing W'] [Algebra Z W']
    (f : W →ₐ[Z] W') (i : I) (y : O ⊗[Z] W) :
    crd b i (Algebra.TensorProduct.map (AlgHom.id O O) f y) = f (crd b i y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul o v =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, crd_tmul_lemma, crd_tmul_lemma, map_smul]
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]

private theorem tensor_eq_of_crd_eq {Z O I W : Type} [CommRing Z] [CommRing O] [Algebra Z O]
    [Fintype I] (b : Module.Basis I Z O) [CommRing W] [Algebra Z W] {y y' : O ⊗[Z] W}
    (h : ∀ i, crd b i y = crd b i y') : y = y' := by
  rw [← sum_basis_tmul_crd_eq b y, ← sum_basis_tmul_crd_eq b y']
  simp_rw [h]

private theorem exists_basis_padicInt_OL (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    ∃ (I : Type) (_ : Fintype I), Nonempty (Module.Basis I ℤ_[l] ↥(OL LL)) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : IsIntegralClosure ↥(OL LL) ℤ_[l] ↥LL.1 := integralClosure.isIntegralClosure _ _
  haveI : Module.Finite ℤ_[l] ↥(OL LL) := IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  haveI : Module.IsTorsionFree ℤ_[l] ↥LL.1 := .of_smul_eq_zero fun r x h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    refine h.imp (fun h => ?_) id
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1, RingHom.comp_apply,
      map_eq_zero_iff _ (algebraMap ℚ_[l] ↥LL.1).injective] at h
    exact (map_eq_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).1 h
  haveI : Module.Free ℤ_[l] ↥(OL LL) := IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(OL LL)
  exact ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℤ_[l] ↥(OL LL)⟩⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l),
    IsAdicComplete (Ideal.span {((l : ℕ) : RW LL)}) (RW LL) ∧
    (∀ x : RW LL, ((l : ℕ) : RW LL) * x = 0 → x = 0) ∧ Function.Injective (inclR LL) ∧
    (∀ (y : RA LL) (x : RW LL), inclR LL y = ((l : ℕ) : RW LL) * x → ∃ y', inclR LL y' = x) ∧
    ∀ e : OCb l, ¬ IsUnit (e - 1) →
      IsAdicComplete (Ideal.span {(1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l e - 1)})
        (RA LL) := by
  intro l _ LL
  obtain ⟨I, _, ⟨b⟩⟩ := exists_basis_padicInt_OL l LL
  haveI : CharP (Cb l) l :=
    charP_of_injective_algebraMap (IsFractionRing.injective (OCb l) (Cb l)) l
  have hl : ((l : ℕ) : RW LL) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] ((l : ℕ) : WCb l) := by
    rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]
  have hl' : ∀ i (x : RW LL), crd b i (((l : ℕ) : RW LL) * x) = ((l : ℕ) : WCb l) * crd b i x := by
    intro i x
    rw [hl]
    exact crd_mul_lemma_2 b i _ x
  have hinc : ∀ (y : RA LL) i, crd b i (inclR LL y) = inclW l (crd b i y) := fun y i =>
    crd_tensorProduct_map_eq b (inclWA l) i y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hl]
    haveI : IsAdicComplete (Ideal.span {((l : ℕ) : WCb l)}) (WCb l) :=
      (GlobalTheory.Per.AinfComplete.witt_complete (p := l) (R := Cb l) ((l : ℕ) : WCb l)
        (fun c => ⟨c, fun n => by simp⟩)
        (fun x hx => by simpa using hx 1)).2
    exact complete_tensor b _
  · intro x hx
    refine tensor_eq_of_crd_eq b fun i => ?_
    rw [map_zero]
    exact tiltWitt_eq_zero_of_prime_mul_eq_zero _ (by rw [← hl', hx, map_zero])
  · intro y y' h
    exact tensor_eq_of_crd_eq b fun i => inclW_injective (by rw [← hinc, ← hinc, h])
  · intro y x hyx
    have hi : ∀ i, ∃ a' : Loc.Ainf l, inclW l a' = crd b i x := fun i =>
      ainf_saturated_in_tiltWitt_prime (crd b i y) (crd b i x)
        ((hinc y i).symm.trans ((congrArg (crd b i) hyx).trans (hl' i x)))
    choose a' ha' using hi
    refine ⟨∑ i, b i ⊗ₜ[ℤ_[l]] a' i, tensor_eq_of_crd_eq b fun i => ?_⟩
    exact (hinc _ i).trans ((congrArg (inclW l) (crd_sum_lemma_4 b i a')).trans (ha' i))
  · intro e he
    haveI : IsAdicComplete (Ideal.span {(WittVector.teichmuller l e - 1 : Ainf l)}) (Ainf l) :=
      (GlobalTheory.Per.AinfComplete.main l _ (not_isUnit_teich e he)).2
    exact complete_tensor b _

end GlobalTheory.HWL.TensorWitt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelCharacterEqStandard
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models.CharModel

theorem eq_chr_of_bijective {k G : Type} [Field k] [Group G] (A : Ob k G) (χ : G →* kˣ)
    (f : (Fin A.m → k) →ₗ[k] (Fin 1 → k)) (hf : IsHom A (chr χ) f) (hb : Function.Bijective f) : A = chr χ := by
  obtain ⟨m, ρ⟩ := A
  have hm : m = 1 := by
    have := (LinearEquiv.ofBijective f hb).finrank_eq
    simpa using this
  subst hm
  have : ρ = (chr χ).ρ := by
    ext1 g
    refine LinearMap.ext fun x => hb.1 ?_
    rw [hf g x]
    change (χ g : k) • f x = f ((χ g : k) • x)
    rw [map_smul]
  subst this
  rfl

theorem chr_inj {k G : Type} [Field k] [Group G] {χ χ' : G →* kˣ} (h : chr χ = chr χ') : χ = χ' := by
  have h1 : (chr χ).ρ = (chr χ').ρ := eq_of_heq (Ob.mk.inj h).2
  ext g
  have := congrArg (fun ρ : Representation k G (Fin 1 → k) => ρ g (fun _ => 1) 0) h1
  simpa using this

theorem eq_of_cast_eq {k : Type} [Field k] {l : ℕ} [CharP k l] {a b : ℤ} (h : (a : k) = b) (hab : |a - b| < l) :
    a = b := by
  have h1 : ((a - b : ℤ) : k) = 0 := by push_cast; rw [h, sub_self]
  rw [CharP.intCast_eq_zero_iff k l] at h1
  have := Int.eq_zero_of_abs_lt_dvd h1 hab
  omega

theorem resCount_single {k : Type} [Field k] [DecidableEq k] (u : ℤ) (x : k) :
    resCount {u} 0 x = if (u : k) = x then 1 else 0 := by
  unfold resCount
  rw [Multiset.filter_singleton]
  simp only [sub_zero]
  split_ifs <;> simp

theorem resCount_block {k : Type} [Field k] [DecidableEq k] (w : ℤ) (t : ℕ) (x : k) :
    resCount (block w t) w x = ∑ e : Fin t, if ((e.val : ℤ) : k) = x then 1 else 0 := by
  unfold resCount
  rw [Fin.sum_univ_eq_sum_range (fun e => if ((e : ℤ) : k) = x then 1 else 0) t, Finset.sum_boole, block,
    ← Finset.filter_val, Finset.card_val, Nat.cast_id]
  symm
  refine Finset.card_bij (fun e _ => w + e) ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at he ⊢
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [add_sub_cancel_left]; exact he.2
  · intro a _ b _ h
    omega
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_Ico] at hu
    have h : (((u - w).toNat : ℕ) : ℤ) = u - w := by omega
    refine ⟨(u - w).toNat, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [h]; exact hu.2⟩

theorem sum_eq_of_counts {k ι : Type} [Field k] [DecidableEq k] {l : ℕ} [CharP k l] (S : Finset ι) (a b : ι → ℤ)
    (lo hi : ℤ) (hl : hi - lo < l) (ha : ∀ i ∈ S, lo ≤ a i ∧ a i ≤ hi) (hb : ∀ i ∈ S, lo ≤ b i ∧ b i ≤ hi)
    (h : ∀ y : ℤ, lo ≤ y → y ≤ hi →
      (∑ i ∈ S, if (a i : k) = y then 1 else 0 : ℕ) = ∑ i ∈ S, if (b i : k) = y then 1 else 0) :
    ∑ i ∈ S, a i = ∑ i ∈ S, b i := by
  have key : ∀ c : ι → ℤ, (∀ i ∈ S, lo ≤ c i ∧ c i ≤ hi) → ∑ i ∈ S, c i =
      ∑ y ∈ Finset.Icc lo hi, y * ((∑ i ∈ S, if (c i : k) = y then 1 else 0 : ℕ) : ℤ) := by
    intro c hc
    push_cast
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi' => ?_
    rw [Finset.sum_eq_single (c i)]
    · simp
    · intro y hy hne
      rw [Finset.mem_Icc] at hy
      have := hc i hi'
      rw [if_neg, mul_zero]
      intro h'
      exact hne (eq_of_cast_eq (l := l) h' (by rw [abs_lt]; omega)).symm
    · intro h'
      exact absurd (Finset.mem_Icc.2 (hc i hi')) h'
  rw [key a ha, key b hb]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finset.mem_Icc] at hy
  rw [h y hy.1 hy.2]

theorem model_of_base {k G : Type} [Field k] [Group G] {l n : ℕ} {R : RingPG k l} {F : DFun R n G} {r : ℕ}
    {Dt : TopData n r} (M : ModTh F Dt) (B : Ob k G) (N : Lats k n B.m) (h : M.Base B N) : M.Model B N := by
  refine ⟨B, N, B, LinearMap.id, LinearMap.id, h, fun _ _ => rfl, Function.injective_id, fun _ _ => rfl,
    Function.surjective_id, ?_⟩
  funext i
  simp only [DFun.push, DFun.pre, F.map_id B (M.base_obj B N h)]
  ext x
  simp

theorem model_chr_eq : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (e : ℤ), 0 ≤ e → e < Dt.t → ∀ N : Lats k n 1, M.Model (chr (M.ω ^ (-e))) N → N = M.Nχ e := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 e he0 het N hN
  classical
  obtain ⟨κ₀, hκ₀⟩ := GlobalTheory.T.character_model_exponents_signs_senWeight F M h1 h2 h3 e he0 het N hN
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, hNe⟩ := hN
  obtain ⟨μ, hss, hsen⟩ := M.base_sen B Nb hB
  obtain ⟨s, C, L, a₀, hmod, hsimple, hss', hsum, ha₀⟩ :=
    GlobalTheory.T.exists_jordanHolder_through_line_alt F M B A₁ (M.ω ^ (-e)) j p Nb (model_of_base M B Nb hB) hj hji hp hps
  rw [← hNe] at ha₀
  obtain ⟨c, hsome, hnone, hcard⟩ := GlobalTheory.JHMatch.jh_match M.T M.ω Dt.t μ s C hsimple
    (SameFactors.trans (SameFactors.symm hss') hss)
  have hW := GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3
  have htη : ∀ i, (Dt.t : ℤ) ≤ Dt.η i := by
    intro i
    obtain ⟨-, -, hG, hBd⟩ := hW i
    cases hty : Dt.ty i
    · have := hG hty; omega
    · have := hBd hty; omega
  have hC : ∀ a e', c a = some e' → C a = chr (M.ω ^ (-(e'.val : ℤ))) := fun a e' h => by
    obtain ⟨f, hf, hb⟩ := hsome a e' h
    exact eq_chr_of_bijective _ _ f hf hb
  have hch : ∀ (A : Ob k G) (Λ : Lats k n A.m) (e' : Fin Dt.t), M.Model A Λ →
      A = chr (M.ω ^ (-(e'.val : ℤ))) → ∃ κ : ZMod n → ℤ, ∀ i, |κ i| ≤ Dt.sg l i ∧
        (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧
        ∀ x, sen ((F.D A).γ i) (Λ i) x = resCount {(e'.val : ℤ) - κ i} 0 x := by
    rintro A Λ e' hm rfl
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.character_model_exponents_signs_senWeight F M h1 h2 h3 e' (by omega) (by omega) Λ hm
    exact ⟨κ, fun i => (hκ i).2⟩
  have hex : ∀ a, ∃ κ : ZMod n → ℤ, ∀ e', c a = some e' → ∀ i, |κ i| ≤ Dt.sg l i ∧
        (Dt.ty i = LType.G → 0 ≤ κ (i - 1)) ∧ (Dt.ty i = LType.Bd → κ (i - 1) ≤ 0) ∧
        ∀ x, sen ((F.D (C a)).γ i) (L a i) x = resCount {(e'.val : ℤ) - κ i} 0 x := by
    intro a
    cases hc : c a with
    | none => exact ⟨0, fun _ h => by cases h⟩
    | some e' =>
      obtain ⟨κ, hκ⟩ := hch (C a) (L a) e' (hmod a) (hC a e' hc)
      exact ⟨κ, fun e'' h => by cases h; exact hκ⟩
  choose κ hκ using hex
  let cc : Fin s → ℤ := fun a => (c a).elim 0 fun e' => (e'.val : ℤ)
  let S : Finset (Fin s) := Finset.univ.filter fun a => c a ≠ none
  have hS : ∀ a ∈ S, ∃ e', c a = some e' ∧ cc a = e'.val := by
    intro a ha
    obtain ⟨e', he'⟩ := Option.ne_none_iff_exists'.1 (Finset.mem_filter.1 ha).2
    exact ⟨e', he', by simp [cc, he']⟩
  have hzero : ∀ i, ∀ a ∈ S, κ a i = 0 := by
    intro i
    have hT := h1 i
    have hη := htη i
    have hsumeq : ∑ a ∈ S, (cc a - κ a i) = ∑ a ∈ S, cc a := by
      refine sum_eq_of_counts (k := k) (l := l) S _ _ (-(Dt.sg l i : ℤ)) (Dt.t + Dt.sg l i) (by omega) ?_ ?_ ?_
      · intro a ha
        obtain ⟨e', he', hcc⟩ := hS a ha
        have := abs_le.1 (hκ a e' he' i).1
        have := e'.2
        omega
      · intro a ha
        obtain ⟨e', he', hcc⟩ := hS a ha
        have := e'.2
        omega
      · intro y hy1 hy2
        have hU : ∀ u ∈ Dt.U i, ((u - Dt.w i : ℤ) : k) ≠ (y : k) := by
          intro u hu h
          refine (hW i).2.1 u hu (Dt.w i + y) (by omega) (by omega) ?_
          push_cast at h ⊢
          linear_combination h
        have e1 : (∑ a ∈ S, if ((cc a - κ a i : ℤ) : k) = y then 1 else 0 : ℕ) =
            ∑ a, sen ((F.D (C a)).γ i) (L a i) (y : k) := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun a _ => ?_
          cases hc : c a with
          | none =>
            simp only [ne_eq, not_true_eq_false, if_false]
            by_contra hne
            obtain ⟨A', j', p', q1, q2, q3, q4⟩ := hnone a hc
            obtain ⟨u, hu, hux⟩ := GlobalTheory.T.senWeight_subquotient_model_mem_residues F M h1 h2 h3 A' (C a) j' p' (L a) q1 q2 q3 q4 (hmod a) i y
              (Ne.symm hne)
            exact hU u hu hux
          | some e' =>
            rw [(hκ a e' hc i).2.2.2, resCount_single, if_pos (by simp)]
            simp [cc, hc]
        have e2 : resCount (Dt.Ut i) (Dt.w i) (y : k) = resCount (block (Dt.w i) Dt.t) (Dt.w i) (y : k) := by
          unfold resCount
          rw [TopData.Ut, Multiset.filter_add, Multiset.filter_eq_nil.2 hU, zero_add]
          rfl
        rw [e1, ← hsum, hsen, e2, resCount_block, Finset.sum_filter,
          ← Finset.sum_fiberwise_of_maps_to (g := c) (t := Finset.univ) (fun _ _ => Finset.mem_univ _),
          Fintype.sum_option, Finset.mul_sum,
          Finset.sum_eq_zero (s := Finset.univ.filter fun a => c a = none), zero_add]
        · refine Finset.sum_congr rfl fun e' _ => ?_
          rw [← hcard e', ← smul_eq_mul, ← Finset.sum_const]
          refine Finset.sum_congr rfl fun a ha => ?_
          have hc := (Finset.mem_filter.1 ha).2
          simp [cc, hc]
        · intro a ha
          have hc := (Finset.mem_filter.1 ha).2
          simp [hc]
    have hs0 : ∑ a ∈ S, κ a i = 0 := by
      rw [Finset.sum_sub_distrib] at hsumeq
      linarith
    cases hty : Dt.ty (i + 1)
    · refine (Finset.sum_eq_zero_iff_of_nonneg fun a ha => ?_).1 hs0
      obtain ⟨e', he', -⟩ := hS a ha
      simpa using (hκ a e' he' (i + 1)).2.1 hty
    · refine (Finset.sum_eq_zero_iff_of_nonpos fun a ha => ?_).1 hs0
      obtain ⟨e', he', -⟩ := hS a ha
      simpa using (hκ a e' he' (i + 1)).2.2.1 hty
  have hCa : C a₀ = chr (M.ω ^ (-e)) := congrArg Sigma.fst ha₀
  have haS : a₀ ∈ S := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun hc => ?_⟩
    have := hnone a₀ hc
    rw [hCa] at this
    obtain ⟨A', j', p', q1, q2, q3, q4⟩ := this
    have hp0 := GlobalTheory.T.hom_to_characterLine_eq_zero F M h1 h2 h3 e (by omega) het A' j' p' q1 q2 q3
    obtain ⟨x, hx⟩ := q4 (fun _ => 1)
    rw [hp0] at hx
    simpa using congrFun hx 0
  obtain ⟨e', he', -⟩ := hS a₀ haS
  have hee : e = e'.val := by
    have hω := chr_inj (hCa.symm.trans (hC a₀ e' he'))
    have hT := h1 0
    have hη := htη 0
    have := e'.2
    by_contra hne
    refine M.ω_ne (e - e'.val).natAbs (by omega) (by omega) ?_
    have h : M.ω ^ (e - (e'.val : ℤ)) = 1 := by
      rw [sub_eq_add_neg, zpow_add, ← hω, ← zpow_add, add_neg_cancel, zpow_zero]
    exact pow_natAbs_eq_one.2 h
  funext i
  have hsen0 := congrArg (fun P : Σ A : Ob k G, Lats k n A.m =>
    sen ((F.D P.1).γ i) (P.2 i) ((e : ℤ) : k)) ha₀
  simp only at hsen0
  rw [(hκ a₀ e' he' i).2.2.2, (hκ₀ i).2.2.2.2, hzero i a₀ haS, resCount_single, resCount_single, ← hee,
    if_pos (by simp)] at hsen0
  have h0 : κ₀ i = 0 := by
    split_ifs at hsen0 with h
    have hT := h1 i
    have hb := abs_le.1 (hκ₀ i).2.1
    have := eq_of_cast_eq (l := l) h (by rw [abs_lt]; omega)
    omega
  rw [(hκ₀ i).1, h0, sh_zero_eq]

end GlobalTheory.Models.CharModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeFreeOfCrystallineStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_free_of_crystalline : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ (E : WEt I) (Mo : NS E) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ → Nonempty (Module.Basis (Fin (Module.finrank ↥(OL LL) ↥T.L.T)) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥(Mo.N T)) := by
  first | exact @GlobalTheory.HWL.lattice_free | exact GlobalTheory.HWL.lattice_free | (intros; apply GlobalTheory.HWL.lattice_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinfStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_sandwich_Ainf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (N : Submodule (LetA S.O S.n) (S.W.DD T)), WClauses S E T M0 h0 N → (∀ y ∈ N, (S.inclR (E.io S.W.X)) ^ M0 • E.jD T y ∈ LinearMap.range (TWincl S.inclR T)) ∧ ∀ t : ↥T.L.T, (S.inclR (E.io S.W.X)) ^ h0 • ((1 : S.RW) ⊗ₜ[S.O] t) ∈ Submodule.span S.O {z : TW S.RW T | ∃ (a : S.RA), ∃ y ∈ N, z = S.inclR a • E.jD T y} := by
  first | exact @GlobalTheory.Sandwich.sandwich | exact GlobalTheory.Sandwich.sandwich | (intros; apply GlobalTheory.Sandwich.sandwich <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeaklySmallStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weakly_small_of_not_isUnit_of_dvd_pow : ∀ {l : ℕ} [Fact l.Prime] (ϖ : OCb l), ¬ IsUnit ϖ → (∀ a : OCb l, a ≠ 0 → ∃ m : ℕ, a ∣ ϖ ^ m) → letI := wTop l; ∀ U ∈ 𝓝 (0 : WCb l), ∃ N m : ℕ, ∀ w : Ainf l, (∀ n < N, w.coeff n ∈ Ideal.span {ϖ ^ m}) → inclW l w ∈ U := by
  first | exact @GlobalTheory.WeakClosed.weakly_small | exact GlobalTheory.WeakClosed.weakly_small | (intros; apply GlobalTheory.WeakClosed.weakly_small <;> assumption)
end

