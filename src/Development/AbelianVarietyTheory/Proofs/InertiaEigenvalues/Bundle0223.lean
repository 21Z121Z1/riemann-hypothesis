import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0217
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerGeneratorMatrixPerturbation
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfinitelyManyPrimesInRayClass

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupOneCocyclesAnticommUpToCoboundary
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory

section General

variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] [TopologicalSpace LL]
  [IsTopologicalRing LL]
  {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V] [ContinuousAdd V]
  [ContinuousConstSMul LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [TopologicalSpace V'] [ContinuousAdd V']
  [ContinuousConstSMul LL V']

theorem cupAnti_cob_of_flip (χ : G →* LLˣ) (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (m : V →ₗ[LL] V' →ₗ[LL] LL) (hm : Continuous fun p : V × V' => m p.1 p.2)
    (hχ : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : LLˣ) : LL) * m x y)
    {a : G → V} (ha : a ∈ continuousCocycles ρ) {b : G → V'} (hb : b ∈ continuousCocycles ρ')
    (h : ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ m.flip b a) :
    ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ' m a b := by
  obtain ⟨f, hf, hfe⟩ := h
  obtain ⟨hac, ha⟩ := ha
  obtain ⟨hbc, hb⟩ := hb
  refine ⟨fun g => -(m (a g) (b g)) - f g, ((hm.comp (hac.prodMk hbc)).neg).sub hf, ?_⟩
  funext x
  obtain ⟨g, h⟩ := x
  have h1 := congrFun hfe (g, h)
  have h2 := hχ g (a h) (b h)
  simp only [ReciprocityTheory.Def.d1, charRep, cupL, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.flip_apply, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    ha, hb, map_add, LinearMap.add_apply] at h1 ⊢
  linear_combination -h1 + h2

theorem cupAnti_cob_of_left (χ : G →* LLˣ) (ρ : Representation LL G V) (ρ' : Representation LL G V')
    (m : V →ₗ[LL] V' →ₗ[LL] LL) (hm : Continuous fun p : V × V' => m p.1 p.2)
    (hχ : ∀ g x y, m (ρ g x) (ρ' g y) = ((χ g : LLˣ) : LL) * m x y)
    {a : G → V} (ha : a ∈ Formalism.WeaklyAdmissibleFiltrations.B1 ρ) {b : G → V'} (hb : b ∈ continuousCocycles ρ') :
    ∃ f : G → LL, Continuous f ∧ ReciprocityTheory.Def.d1 (charRep χ) f = cupL ρ' m a b := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨hbc, hb⟩ := hb
  refine ⟨fun g => m x (b g), hm.comp (continuous_const.prodMk hbc), ?_⟩
  funext y
  obtain ⟨g, h⟩ := y
  have h2 := hχ g x (b h)
  simp only [ReciprocityTheory.Def.d1, charRep, cupL, cob, LinearMap.coe_mk, AddHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul, LinearMap.pi_apply,
    hb, map_add, map_sub, LinearMap.sub_apply]
  linear_combination -h2

end General

theorem cupL_anticomm_cobL : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ a ∈ continuousCocycles A.ρ, ∀ b ∈ continuousCocycles A'.ρ, (CobL (P.PD K) (cupL A'.ρ m a b) ↔ CobL (P.PD K) (cupL A.ρ m.flip b a)) ∧ (a ∈ B1 A.ρ ∨ b ∈ B1 A'.ρ → CobL (P.PD K) (cupL A'.ρ m a b)) := by
  intro l _ P K LL _ _ _ O _ _ hO A A' m hm a ha b hb
  haveI : IsTopologicalRing LL := hO.2.2.2.1
  have hc : Continuous fun p : A.V × A'.V => m p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left m
  have hc' : Continuous fun p : A'.V × A.V => m.flip p.1 p.2 :=
    IsModuleTopology.continuous_bilinear_of_finite_left m.flip
  have hχ := hm.1
  have hχ' : ∀ g x y, m.flip (A'.ρ g x) (A.ρ g y) =
      ((cycLL (P.PD K) LL g : LLˣ) : LL) * m.flip x y := fun g x y => hχ g y x
  refine ⟨⟨fun h => cupAnti_cob_of_flip _ A'.ρ A.ρ m.flip hc' hχ' hb ha h,
    fun h => cupAnti_cob_of_flip _ A.ρ A'.ρ m hc hχ ha hb h⟩, ?_⟩
  rintro (h | h)
  · exact cupAnti_cob_of_left _ A.ρ A'.ρ m hc hχ h hb
  · exact cupAnti_cob_of_flip _ A.ρ A'.ρ m hc hχ ha hb
      (cupAnti_cob_of_left _ A'.ρ A.ρ m.flip hc' hχ' h ha)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFixedIffMemCompletedIntegersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (y : PadicComplex l), ‖y‖ ≤ 1 → ((∀ h ∈ Hinf K, act h y = y) ↔ y ∈ Ohat K) := by
  first | exact @GlobalTheory.CycInvariants.fixed_iff_mem_Ohat | exact GlobalTheory.CycInvariants.fixed_iff_mem_Ohat | (intros; apply GlobalTheory.CycInvariants.fixed_iff_mem_Ohat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerGeneratorMatrixPerturbationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_tower_generator_matrix_perturbation : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ g, IsGen χ K j g → ∀ (r : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)), (∀ a b, U g a b ∈ intC (Ks K j)) → (∀ a b, ‖(U g - 1) a b‖ < rho1 l) → ∀ i : ℤ, (∀ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) → twAct act χ i U g y = y → y = 0) ∧ ∀ ζ : PadicComplex l, IsPrimitiveRoot ζ l → ∀ w : Fin r → PadicComplex l, (∀ a, w a ∈ Xj K j) → ∃ y : Fin r → PadicComplex l, (∀ a, y a ∈ Xj K j) ∧ twAct act χ i U g y - y = (ζ - 1) • w := by
  first | exact @GlobalTheory.CycPerturb.perturbation | exact GlobalTheory.CycPerturb.perturbation | (intros; apply GlobalTheory.CycPerturb.perturbation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
section
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped Formalism.Per

namespace GlobalTheory.BdRQuot

theorem isUnit_one_add {R : Type} [CommRing R] (I : Ideal R) (z : AdicCompletion I R)
    (hz : AdicCompletion.evalₐ I 1 z = 0) : IsUnit (1 + z) := by
  have h1 : z.val 1 = 0 := by
    have h' : (I ^ 1 • ⊤ : Ideal R) = I ^ 1 := by ext x; simp
    exact (map_eq_zero_iff _ (Ideal.quotientEquivAlgOfEq R h').injective).1 hz
  have hu : ∀ n, IsUnit (1 + z.val n) := by
    intro n
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z.val (n + 1))
    have e1 := z.property (show 1 ≤ n + 1 by omega)
    have e2 := z.property (show n ≤ n + 1 by omega)
    rw [← hr, AdicCompletion.transitionMap_ideal_mk] at e1 e2
    rw [h1, Ideal.Quotient.eq_zero_iff_mem] at e1
    have hrI : r ∈ I := by simpa using e1
    refine IsNilpotent.isUnit_one_add ⟨n, ?_⟩
    rw [← e2, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    simpa using Ideal.pow_mem_pow hrI n
  let u : AdicCompletion I R := ⟨fun n => Ring.inverse (1 + z.val n), fun {m n} hmn => by
    have e := congrArg (AdicCompletion.transitionMap I R hmn) (Ring.inverse_mul_cancel _ (hu n))
    rw [AdicCompletion.transitionMap_map_mul, map_add, AdicCompletion.transitionMap_map_one,
      z.property hmn] at e
    exact left_inv_eq_right_inv e (Ring.mul_inverse_cancel _ (hu m))⟩
  refine IsUnit.of_mul_eq_one u ?_
  ext n
  exact Ring.mul_inverse_cancel _ (hu n)

variable {l : ℕ} [Fact l.Prime]

theorem one_mem_FilP_zero : (1 : Per.BdRp l) ∈ Per.FilP l 0 := by
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow, map_one, ← map_one (Ideal.Quotient.mk (Per.kerP l ^ 0)), Ideal.Quotient.eq_zero_iff_mem]
  simp

theorem mem_FilD_nat (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l n ↔ ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x := by
  constructor
  · exact fun h => GlobalTheory.RingIface.exists_of_mem_FilD_nat l h
  · rintro ⟨z, hz, rfl⟩
    exact GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem mem_filtration_zero (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  simpa using Ideal.mul_mem_left _ y one_mem_FilP_zero

variable {P : LocPrime l} {AI : LocAinf l P}

theorem eD_ιA (T : LocTied l P AI) (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = Per.pD l (algebraMap (Per.Ainf l) (Per.AinfP l) a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA, ← GlobalTheory.RingIface.pD_eq_alg] at h
  simpa using h

theorem exists_approx (T : LocTied l P AI) (n : ℕ) (x : P.R.BdR) (hx : x ∈ (P.PD (botExt l)).Fil 0) :
    ∃ (k : ℕ) (a : Ainf l), (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) := by
  obtain ⟨y, -, hy⟩ := (mem_FilD_nat 0 _).1 ((T.fil _ _ _).1 hx)
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (Per.ev l n y)
  obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj (S := Per.AinfP l) (l : Per.Ainf l) s
  refine ⟨k, a, (T.fil _ _ _).2 ((mem_FilD_nat n _).2
    ⟨(l : Per.BdRp l) ^ k * y - algebraMap (Per.AinfP l) (Per.BdRp l) (algebraMap (Per.Ainf l) _ a), ?_, ?_⟩)⟩
  · rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    have e : ∀ r : Per.AinfP l, Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) r) =
        Ideal.Quotient.mk _ r := fun r => GlobalTheory.RingIface.ev_alg l n r
    rw [map_sub, e, ← ha, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, map_natCast,
      hs, mul_comm, sub_self]
  · rw [map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, eD_ιA, hy,
      GlobalTheory.RingIface.pD_eq_alg]

theorem exists_inv (T : LocTied l P AI) (y : P.R.BdR) (hy : y ∈ (P.PD (botExt l)).Fil 1) :
    ∃ u ∈ (P.PD (botExt l)).Fil 0, (1 + y) * u = 1 := by
  obtain ⟨z, hz, e⟩ := (mem_FilD_nat 1 _).1 ((T.fil _ _ _).1 hy)
  have hU : IsUnit (1 + z : Per.BdRp l) := by
    obtain ⟨c, -, hc⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
    have h := isUnit_one_add (Per.kerP l) (c z) (by rw [hc]; exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l 1 z).1 hz)
    have h' := h.map c.symm
    rwa [map_add, map_one, RingEquiv.symm_apply_apply] at h'
  obtain ⟨v, hv'⟩ := hU.exists_right_inv
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) v), (T.fil _ _ _).2 ?_, T.eD.injective ?_⟩
  · rw [RingEquiv.apply_symm_apply]
    exact (mem_FilD_nat 0 _).2 ⟨v, mem_filtration_zero _, rfl⟩
  · rw [map_mul, map_add, map_one, RingEquiv.apply_symm_apply, ← e,
      ← map_one (algebraMap (Per.BdRp l) (Per.BdR l)), ← map_add, ← map_mul, hv']

theorem mul_mem_zero {a : ℤ} {x y : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil 0)
    (hy : y ∈ (P.PD (botExt l)).Fil a) : x * y ∈ (P.PD (botExt l)).Fil a := by
  simpa using (P.PD (botExt l)).Fil_mul 0 a x y hx hy

theorem pow_mem_Fil {a : ℤ} {x : P.R.BdR} (hx : x ∈ (P.PD (botExt l)).Fil a) (n : ℕ) :
    x ^ n ∈ (P.PD (botExt l)).Fil (n * a) := by
  induction n with
  | zero => simpa using (P.PD (botExt l)).one_mem
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ ih hx

theorem theta_pow (J : ThetaL P AI) (a : Ainf l) (k : ℕ) :
    J.θ (P.ιB (AI.ιA (a ^ k))) = J.θ (P.ιB (AI.ιA a)) ^ k := by
  induction k with
  | zero => simpa using J.θ_one
  | succ k ih => rw [pow_succ, map_mul, map_mul, J.θ_mul _ (AI.ainf_image_mem_filtration_zero _ _) _ (AI.ainf_image_mem_filtration_zero _ _), ih, pow_succ]

theorem εroot_pow (n : ℕ) : AI.εroot (n + 1) ^ l ^ n = AI.ε1 := by
  induction n with
  | zero => simp [LocAinf.εroot, LocAinf.ε1]
  | succ n ih =>
    rw [pow_succ', pow_mul, ← ih, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    rfl

theorem ζ_pow (n : ℕ) : AI.ζ (n + 1) ^ l ^ n = AI.ζ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, AI.ζ_succ, ih]

theorem theta_teich (J : ThetaL P AI) :
    J.θ (P.ιB (AI.ιA (WittVector.teichmuller l AI.ε1))) = ((AI.ζ 1 : OC l) : PadicComplex l) := by
  have key : ∀ n : ℕ, ‖J.θ (P.ιB (AI.ιA (WittVector.teichmuller l AI.ε1))) -
      ((AI.ζ 1 : OC l) : PadicComplex l)‖ ≤ ‖(l : PadicComplex l)‖ ^ (n + 1) := by
    intro n
    let c : OC l := ⟨J.θ (P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot (n + 1))))),
      (GlobalTheory.RingBasics.mem_OC _).2 (J.θ_int _)⟩
    have h1 := J.θ_teich (AI.εroot (n + 1)) (AI.ζ (n + 1)) (by
      rw [LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add, AI.ε_coeff])
    have h2 : ((l : ℕ) : OC l) ∣ c - AI.ζ (n + 1) := by
      have := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (c - AI.ζ (n + 1))).2 (by simpa using h1)
      rwa [pow_one, Ideal.mem_span_singleton] at this
    have h3 := dvd_sub_pow_of_dvd_sub h2 n
    rw [← Ideal.mem_span_singleton, ← Ideal.span_singleton_pow, GlobalTheory.RingBasics.mem_span_pow_OC, ζ_pow] at h3
    rw [← εroot_pow (AI := AI) n, map_pow, theta_pow]
    simpa using h3
  have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (l : PadicComplex l))
    GlobalTheory.RingBasics.norm_p_lt).comp (Filter.tendsto_add_atTop_nat 1)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' lim key))

theorem exists_t_eq (T : LocTied l P AI) (J : ThetaL P AI) :
    ∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧
      J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1 := by
  obtain ⟨y, hy, e⟩ := (J.fil_succ_iff_mul_t 1 _).1 J.t_μ
  obtain ⟨u, hu, hyu⟩ := exists_inv T y hy
  have hy0 : y ∈ (P.PD (botExt l)).Fil 0 := (P.PD (botExt l)).Fil_anti 0 hy
  have h1 := (P.PD (botExt l)).one_mem
  have hθu : J.θ u = 1 := by
    have := congrArg J.θ hyu
    rwa [J.θ_mul _ (add_mem h1 hy0) _ hu, J.θ_add _ h1 _ hy0, (J.θ_ker y hy0).2 hy, J.θ_one,
      add_zero, one_mul] at this
  have hπ : J.θ (P.ιB (AI.ιA AI.π₁)) = ((AI.ζ 1 : OC l) : PadicComplex l) - 1 := by
    rw [eq_sub_iff_add_eq, ← theta_teich J, ← J.θ_one, ← J.θ_add _ (AI.ainf_image_mem_filtration_zero _ _) _ h1]
    simp [LocAinf.π₁]
  refine ⟨P.ιB (AI.ιA AI.π₁) * u, mul_mem_zero (AI.ainf_image_mem_filtration_zero _ _) hu, ?_, ?_⟩
  · rw [AI.μ_eq, map_mul, map_mul] at e
    linear_combination (-u) * e - P.ιB P.tB * hyu
  · rw [J.θ_mul _ (AI.ainf_image_mem_filtration_zero _ _) _ hu, hθu, mul_one, hπ]

theorem exists_t_pow (J : ThetaL P AI) (a : ℤ) (n : ℕ) (x : P.R.BdR)
    (hx : x ∈ (P.PD (botExt l)).Fil (a + n)) :
    ∃ y ∈ (P.PD (botExt l)).Fil a, x = P.ιB P.tB ^ n * y := by
  induction n generalizing x with
  | zero => exact ⟨x, by simpa using hx, by simp⟩
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc] at hx
    obtain ⟨z, hz, rfl⟩ := (J.fil_succ_iff_mul_t _ _).1 hx
    obtain ⟨y, hy, rfl⟩ := ih z hz
    exact ⟨y, hy, by ring⟩

theorem mem_Fil_iff (T : LocTied l P AI) (J : ThetaL P AI) (n : ℕ) (a : Ainf l) :
    P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a := by
  have hξ : P.ιB (AI.ιA AI.ξ) ∈ (P.PD (botExt l)).Fil 1 :=
    (AI.ainf_image_mem_filtration_one_iff _ _).2 ⟨1, (mul_one _).symm⟩
  constructor
  · obtain ⟨w, hw, ht, -⟩ := exists_t_eq T J
    have hunit : IsUnit (P.ιB (AI.ιA AI.ξ)) := by
      have := (P.PD (botExt l)).t_unit.map P.ιB
      rw [P.period_datum_t_eq, ht] at this
      exact isUnit_of_mul_isUnit_left this
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro h
      rw [Nat.cast_succ] at h
      obtain ⟨b, rfl⟩ := ih ((P.PD (botExt l)).Fil_anti _ h)
      rw [add_comm] at h
      obtain ⟨y, hy, e⟩ := exists_t_pow J 1 n _ h
      rw [map_mul, map_mul, map_pow, map_pow, ht, mul_pow, mul_assoc] at e
      have e' := (hunit.pow n).mul_left_cancel e
      have hb : P.ιB (AI.ιA b) ∈ (P.PD (botExt l)).Fil 1 := by
        rw [e']
        exact mul_mem_zero (by simpa using pow_mem_Fil hw n) hy
      obtain ⟨c, rfl⟩ := (AI.ainf_image_mem_filtration_one_iff _ _).1 hb
      exact ⟨c, by rw [pow_succ, mul_assoc]; rfl⟩
  · rintro ⟨b, rfl⟩
    rw [map_mul, map_mul, map_pow, map_pow, mul_comm]
    exact mul_mem_zero (AI.ainf_image_mem_filtration_zero _ _) (by simpa using pow_mem_Fil hξ n)

theorem fil_quotient : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (J : ThetaL P AI) (n : ℕ),
    (∀ x ∈ (P.PD (botExt l)).Fil 0, ∃ (k : ℕ) (a : Ainf l),
      (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ)) ∧
    (∀ a : Ainf l, P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a) ∧
    (∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧
      J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1) :=
  fun _ _ _ _ T J n => ⟨exists_approx T n, mem_Fil_iff T J n, exists_t_eq T J⟩

end GlobalTheory.BdRQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DedekindZetaEulerProductMulSubOneEntireNeZeroStatement
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_entire_sub_one_mul_euler_exp_ne_zero_one : ∀ (K : Type) [Field K] [NumberField K], ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' P : HeightOneSpectrum (𝓞 K), -Complex.log (1 - 1 * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  first | exact @GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero | exact GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero | (intros; apply GlobalTheory.dedekindZeta_eulerProduct_mul_sub_one_entire_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeStableTwistedPairing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.DualLat

variable {LL O V W : Type} [Field LL] [CommRing O] [IsDomain O] [Algebra O LL] [IsFractionRing O LL]
  [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] [FiniteDimensional LL V]
  [AddCommGroup W] [Module LL W] [Module O W] [IsScalarTower O LL W] [FiniteDimensional LL W]

theorem exists_dual (m : V →ₗ[LL] W →ₗ[LL] LL)
    (h3 : ∀ y : W, (∀ x : V, m x y = 0) → y = 0)
    (h4 : finrank LL V = finrank LL W)
    (T : Submodule O V) (hfg : T.FG) (hfree : Module.Free O T)
    (hspan : Submodule.span LL (T : Set V) = ⊤) :
    ∃ T' : Submodule O W, T'.FG ∧ Module.Free O T' ∧ Submodule.span LL (T' : Set W) = ⊤ ∧
      (∀ y, y ∈ T' ↔ ∀ x ∈ T, ∃ a, m x y = algebraMap O LL a) ∧
      (∀ x, x ∈ T ↔ ∀ y ∈ T', ∃ a, m x y = algebraMap O LL a) := by
  classical
  haveI : Module.Finite O T := Module.Finite.iff_fg.mpr hfg
  let b := Module.Free.chooseBasis O T
  let bV0 : Module.Free.ChooseBasisIndex O T → V := fun i => (b i : V)
  have hTspan : Submodule.span O (Set.range bV0) = T := by
    rw [show bV0 = T.subtype ∘ b from rfl, Set.range_comp, Submodule.span_image, b.span_eq,
      Submodule.map_top, Submodule.range_subtype]
  have hliO : LinearIndependent O bV0 := b.linearIndependent.map' T.subtype (Submodule.ker_subtype T)
  have hliL : LinearIndependent LL bV0 := (LinearIndependent.iff_fractionRing O LL).mp hliO
  have hspL : ⊤ ≤ Submodule.span LL (Set.range bV0) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro x hx
    rw [← hTspan] at hx
    exact Submodule.span_le_restrictScalars O LL _ hx
  let bV := Basis.mk hliL hspL
  have hbV : ∀ i, bV i = bV0 i := fun i => Basis.mk_apply hliL hspL i
  let φ : W →ₗ[LL] Module.Dual LL V := m.flip
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact h3 y (fun x => by simpa [φ] using LinearMap.congr_fun hy x)
  have hdim : finrank LL W = finrank LL (Module.Dual LL V) := by
    rw [Subspace.dual_finrank_eq, h4]
  let e : W ≃ₗ[LL] Module.Dual LL V := LinearMap.linearEquivOfInjective φ hφ hdim
  let f' := bV.dualBasis.map e.symm
  have key1 : ∀ x j, m x (f' j) = bV.repr x j := by
    intro x j
    have h : φ (f' j) = bV.dualBasis j := by
      show e (e.symm (bV.dualBasis j)) = bV.dualBasis j
      exact e.apply_symm_apply _
    calc m x (f' j) = φ (f' j) x := rfl
      _ = bV.dualBasis j x := by rw [h]
      _ = bV.repr x j := Basis.dualBasis_apply _ _ _
  have key2 : ∀ i y, m (bV i) y = f'.repr y i := by
    intro i y
    have : m (bV i) = f'.coord i := f'.ext (fun j => by
      rw [key1, Basis.coord_apply, Basis.repr_self, Basis.repr_self, Finsupp.single_apply,
        Finsupp.single_apply]
      simp only [eq_comm])
    rw [this, Basis.coord_apply]
  haveI : IsTorsionFree O LL := inferInstance
  refine ⟨Submodule.span O (Set.range f'), Submodule.fg_span (Set.finite_range _), ?_, ?_, ?_, ?_⟩
  · exact Module.Free.of_basis (Basis.span ((LinearIndependent.iff_fractionRing O LL).mpr f'.linearIndependent))
  · rw [Submodule.span_span_of_tower, f'.span_eq]
  · intro y
    rw [Basis.mem_span_iff_repr_mem]
    constructor
    · intro hy x hx
      rw [← hTspan] at hx
      have hle : Submodule.span O (Set.range bV0) ≤
          Submodule.comap ((m.flip y).restrictScalars O) (1 : Submodule O LL) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        obtain ⟨a, ha⟩ := hy i
        exact Submodule.mem_one.mpr ⟨a, by rw [ha, ← key2, hbV]; rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hle hx)
      exact ⟨a, ha.symm⟩
    · intro hy i
      obtain ⟨a, ha⟩ := hy (bV i) (by rw [hbV, ← hTspan]; exact Submodule.subset_span ⟨i, rfl⟩)
      exact ⟨a, by rw [← key2, ha]⟩
  · intro x
    have hTeq : T = Submodule.span O (Set.range bV) := by
      rw [show (bV : _ → V) = bV0 from funext hbV, hTspan]
    refine (SetLike.ext_iff.mp hTeq x).trans ?_
    rw [Basis.mem_span_iff_repr_mem]
    constructor
    · intro hx y hy
      have hle : Submodule.span O (Set.range f') ≤
          Submodule.comap ((m x).restrictScalars O) (1 : Submodule O LL) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        obtain ⟨a, ha⟩ := hx j
        exact Submodule.mem_one.mpr ⟨a, by rw [ha, ← key1]; rfl⟩
      obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hle hy)
      exact ⟨a, ha.symm⟩
    · intro hx j
      obtain ⟨a, ha⟩ := hx (f' j) (Submodule.subset_span ⟨j, rfl⟩)
      exact ⟨a, by rw [← key1, ha]⟩

end GlobalTheory.DualLat

namespace GlobalTheory.DualLat

theorem dualLattice_exists : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL) (LA : Lattice (O := O) A.ρ), IsDual1 (P.PD K) A.ρ A'.ρ m → (∀ g, ∃ a : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL a) → ∃ LA' : Lattice (O := O) A'.ρ, IsDualLat1 (P.PD K) LA LA' m ∧ IsDualLat1 (P.PD K) LA' LA m.flip := by
  intro l _ P K LL _ _ _ O _ _ hO A A' m LA hD hc
  obtain ⟨⟨hdom, -, hfr⟩, -⟩ := hO
  obtain ⟨h1, h2, h3, h4⟩ := hD
  obtain ⟨T', hfg, hfree, hspan, hmem1, hmem2⟩ := exists_dual (O := O) m h3 h4 LA.T LA.fg LA.free LA.span
  have hstab : ∀ g, ∀ y ∈ T', (A'.ρ g) y ∈ T' := by
    intro g y hy
    rw [hmem1] at hy ⊢
    intro x hx
    obtain ⟨c, hcg⟩ := hc g
    obtain ⟨a, ha⟩ := hy (A.ρ g⁻¹ x) (LA.stable g⁻¹ x hx)
    refine ⟨c * a, ?_⟩
    have hx' : x = A.ρ g (A.ρ g⁻¹ x) := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hx', h1, ha, hcg, map_mul]
  let LA' : WeaklyAdmissibleFiltrations.Lattice (O := O) A'.ρ :=
    { T := T', stable := hstab, fg := hfg, free := hfree, span := hspan }
  refine ⟨LA', ⟨⟨h1, h2, h3, h4⟩, hmem1⟩, ⟨⟨?_, ?_, ?_, h4.symm⟩, ?_⟩⟩
  · intro g y x
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  · intro y hy
    exact h3 y (fun x => by simpa only [LinearMap.flip_apply] using hy x)
  · intro x hx
    exact h2 x (fun y => by simpa only [LinearMap.flip_apply] using hx y)
  · intro y
    simpa only [LinearMap.flip_apply] using hmem2 y

end GlobalTheory.DualLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixedMemInvariants
section
namespace GlobalTheory.FixedFinsetInvariants

theorem exists_finset_fixed_mem_invariants {G LL V : Type} [Group G] [Field LL] [AddCommGroup V]
    [Module LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) :
    ∃ s : Finset G, ∀ v : V, (∀ g ∈ s, ρ g v = v) → v ∈ Formalism.WeaklyAdmissibleFiltrations.H0V ρ := by
  classical
  let F : Finset G → Submodule LL V := fun s => ⨅ g ∈ s, LinearMap.ker (ρ g - LinearMap.id)
  have hF : ∀ (s : Finset G) (v : V), v ∈ F s ↔ ∀ g ∈ s, ρ g v = v := by
    intro s v
    simp only [F, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  obtain ⟨_, ⟨s, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule LL V)).has_min (Set.range F) ⟨F ∅, ∅, rfl⟩
  refine ⟨s, fun v hv => ?_⟩
  unfold Formalism.WeaklyAdmissibleFiltrations.H0V
  rw [Submodule.mem_iInf]
  intro g
  have hle : F (insert g s) ≤ F s := by
    intro w hw
    rw [hF] at hw ⊢
    exact fun h hh => hw h (Finset.mem_insert_of_mem hh)
  have heq : F (insert g s) = F s := by
    by_contra hne
    exact hmin _ ⟨insert g s, rfl⟩ (lt_of_le_of_ne hle hne)
  have hv' : v ∈ F (insert g s) := heq ▸ (hF s v).2 hv
  have hg := (hF _ v).1 hv' g (Finset.mem_insert_self g s)
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact hg

end GlobalTheory.FixedFinsetInvariants
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMixedSpaceNormSignCharacterStatement
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mixedSpace_norm_sign_character : ∀ (K : Type) [Field K] [NumberField K] (ε : ℂ), ε * ε = 1 → ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧ (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧ ∀ β : 𝓞 K, β ≠ 0 → φ (mixedEmbedding K β) = if 0 < Algebra.norm ℤ β then 1 else ε := by
  first | exact @GlobalTheory.NormSign.exists_normSign | exact GlobalTheory.NormSign.exists_normSign | (intros; apply GlobalTheory.NormSign.exists_normSign <;> assumption)
end

