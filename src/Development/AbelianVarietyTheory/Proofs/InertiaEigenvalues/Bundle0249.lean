import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.UnramSpan

open GlobalTheory.UnramValue

variable {l : ℕ} [Fact l.Prime]

theorem fg_rootRing {m : ℕ} (hm : 0 < m) : (rootRing l m).toSubmodule.FG := by
  classical
  have hfin : {x : Om l | x ^ m = 1}.Finite := by
    refine (Polynomial.nthRoots m (1 : Om l)).toFinset.finite_toSet.subset ?_
    intro x hx
    simpa [Polynomial.mem_nthRoots hm] using hx
  refine fg_adjoin_of_finite hfin ?_
  intro x hx
  refine IsIntegral.of_pow hm ?_
  rw [show x ^ m = 1 from hx]; exact isIntegral_one

theorem exists_mem_rootRing {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h1 : ‖x‖ ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ∈ rootRing l m := by
  have hp : l.Prime := Fact.out
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  obtain ⟨m, hm, hl, c, hc, h⟩ := exists_mul_mem hx
  refine ⟨m, hm, hl, ?_⟩
  have key : ∀ k : ℕ, (l : Om l) ^ k * x ∈ rootRing l m → x ∈ rootRing l m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      obtain ⟨z, hz, ez⟩ := exists_eq_mul hm hl hk (by
        rw [norm_mul, norm_pow, norm_l]
        have : ((l : ℝ)⁻¹) ^ (k + 1) < 1 :=
          pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hl1) (Nat.succ_ne_zero k)
        calc _ ≤ ((l : ℝ)⁻¹) ^ (k + 1) * 1 := by gcongr
          _ < 1 := by simpa using this)
      apply ih
      have : (l : Om l) ^ k * x = z := by
        apply mul_left_cancel₀ hl0
        rw [← ez]; ring
      rwa [this]
  apply key c.valuation
  have e := PadicInt.unitCoeff_spec hc
  set u := PadicInt.unitCoeff hc
  have e2 : (l : Om l) ^ c.valuation * x =
      algebraMap ℤ_[l] (Om l) (↑u⁻¹ : ℤ_[l]) * (algebraMap ℤ_[l] (Om l) c * x) := by
    rw [← mul_assoc, ← map_mul]
    congr 1
    conv_rhs => rw [e, Units.inv_mul_cancel_left]
    simp
  rw [e2]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) h

theorem norm_pow_sub_pow_le {m : ℕ} (hm : 0 < m) {k : ℕ} (hk : k ≠ 0) {a b : Om l}
    (ha : a ∈ rootRing l m) (hb : b ∈ rootRing l m) (h : ‖a - b‖ ≤ (l : ℝ)⁻¹) :
    ‖a ^ (l ^ k) - b ^ (l ^ k)‖ ≤ (l : ℝ)⁻¹ * ‖a - b‖ := by
  have hp : l.Prime := Fact.out
  have hd := sub_mem ha hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (⟨b, hb⟩ : rootRing l m) ⟨a - b, hd⟩ k
  have hr' := congrArg Subtype.val hr
  simp only [MulMemClass.coe_mul, AddMemClass.coe_add, SubmonoidClass.coe_pow,
    SubringClass.coe_natCast, add_sub_cancel] at hr'
  have e : a ^ (l ^ k) - b ^ (l ^ k) = (a - b) ^ (l ^ k) + l * (a - b) * (b * r) := by
    rw [hr']; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · obtain ⟨j, hj⟩ : ∃ j, l ^ k = j + 2 :=
      ⟨l ^ k - 2, by have := Nat.one_lt_pow hk hp.one_lt; omega⟩
    have h1 := norm_le_one hm hd
    have h2 : ‖a - b‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
    rw [hj, norm_pow, pow_add, sq]
    calc _ ≤ 1 * ((l : ℝ)⁻¹ * ‖a - b‖) := by gcongr
      _ = _ := one_mul _
  · rw [norm_mul, norm_mul, norm_l]
    have h1 := norm_le_one hm (mul_mem hb r.2)
    calc _ ≤ (l : ℝ)⁻¹ * ‖a - b‖ * 1 := by gcongr
      _ = _ := mul_one _

def part (F : IntermediateField ℚ_[l] (Om l)) (m : ℕ) : Submodule ℤ_[l] (Om l) :=
  (rootRing l m).toSubmodule ⊓ F.toSubalgebra.toSubmodule.restrictScalars ℤ_[l]

theorem mem_part {F : IntermediateField ℚ_[l] (Om l)} {m : ℕ} {x : Om l} :
    x ∈ part F m ↔ x ∈ rootRing l m ∧ x ∈ F := Iff.rfl

theorem fg_part (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) : (part F m).FG :=
  (fg_rootRing hm).of_le inf_le_left

theorem exists_teich (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m)
    {x : Om l} (hx : x ∈ part F m) :
    ∃ w ∈ part F m, w ^ (l ^ m.totient) = w ∧ ‖x - w‖ < 1 := by
  have hp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hp.one_lt
  have hli : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have : ContinuousSMul ℤ_[l] (Om l) := by
    refine continuousSMul_of_algebraMap ℤ_[l] (Om l) ?_
    exact (AddMonoidHomClass.isometry_of_norm _ norm_algebraMap_int).continuous
  have hc : IsCompact ((part F m : Set (Om l)) ∩ Metric.closedBall x (l : ℝ)⁻¹) :=
    (Submodule.isCompact_of_fg (fg_part F hm)).inter_right Metric.isClosed_closedBall
  have hstep : ∀ y ∈ rootRing l m, ‖y ^ (l ^ m.totient) - y‖ ≤ (l : ℝ)⁻¹ := by
    intro y hy
    obtain ⟨z, hz, ez⟩ := pow_sub_mem hl hy
    rw [ez, add_sub_cancel_left, norm_mul, norm_l]
    have h1 := norm_le_one hm hz
    calc _ ≤ (l : ℝ)⁻¹ * 1 := by gcongr
      _ = _ := mul_one _
  obtain ⟨w, ⟨hw, hwx⟩, hmin⟩ := hc.exists_isMinOn
    (f := fun y : Om l => ‖y ^ (l ^ m.totient) - y‖)
    ⟨x, hx, Metric.mem_closedBall_self (by positivity)⟩ (by fun_prop)
  rw [Metric.mem_closedBall, dist_eq_norm] at hwx
  have hw' := mem_part.mp hw
  refine ⟨w, hw, ?_, by rw [norm_sub_rev]; exact hwx.trans_lt hli⟩
  have hmem : w ^ (l ^ m.totient) ∈ (part F m : Set (Om l)) ∩ Metric.closedBall x (l : ℝ)⁻¹ := by
    refine ⟨mem_part.mpr ⟨pow_mem hw'.1 _, pow_mem hw'.2 _⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm,
      show w ^ (l ^ m.totient) - x = (w ^ (l ^ m.totient) - w) + (w - x) by ring]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hstep w hw'.1) hwx)
  have h1 : ‖w ^ (l ^ m.totient) - w‖ ≤ ‖(w ^ (l ^ m.totient)) ^ (l ^ m.totient) - w ^ (l ^ m.totient)‖ :=
    hmin hmem
  have h2 := norm_pow_sub_pow_le hm (Nat.totient_pos.mpr hm).ne' (pow_mem hw'.1 (l ^ m.totient))
    hw'.1 (hstep w hw'.1)
  have h3 := norm_nonneg (w ^ (l ^ m.totient) - w)
  have h4 : ‖w ^ (l ^ m.totient) - w‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp h4)

theorem part_le_span (F : IntermediateField ℚ_[l] (Om l)) {m : ℕ} (hm : 0 < m) (hl : ¬ l ∣ m) :
    part F m ≤ Submodule.span ℤ_[l]
      {w : Om l | w ∈ F ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ w ^ m = 1} := by
  have hp : l.Prime := Fact.out
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal ℤ_[l])
    (fg_part F hm) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
  intro x hx
  obtain ⟨w, hw, ew, hxw⟩ := exists_teich F hm hl hx
  have hd := mem_part.mp (sub_mem hx hw)
  obtain ⟨z, hz, ez⟩ := exists_eq_mul hm hl hd.1 hxw
  have hzF : z ∈ F := by
    have : z = (x - w) / l := by rw [ez]; field_simp
    rw [this]
    exact div_mem hd.2 (natCast_mem F l)
  have e : x = w + (l : ℤ_[l]) • z := by
    rw [Algebra.smul_def, map_natCast, ← ez]; ring
  rw [e]
  refine Submodule.add_mem_sup ?_ (Submodule.smul_mem_smul ?_ (mem_part.mpr ⟨hz, hzF⟩))
  · by_cases h0 : w = 0
    · rw [h0]; exact zero_mem _
    · have hq : 1 < l ^ m.totient := Nat.one_lt_pow (Nat.totient_pos.mpr hm).ne' hp.one_lt
      refine Submodule.subset_span ⟨(mem_part.mp hw).2, l ^ m.totient - 1, by omega, ?_, ?_⟩
      · intro hd
        have h1 : l ∣ l ^ m.totient := dvd_pow_self l (Nat.totient_pos.mpr hm).ne'
        have h2 := Nat.dvd_sub h1 hd
        rw [show l ^ m.totient - (l ^ m.totient - 1) = 1 by omega] at h2
        exact hp.not_dvd_one h2
      · apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel hq.le, ew, one_mul]
  · rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _

theorem exists_sum_rootsOfUnity : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (c : Om l), c ∈ K0 K → ‖c‖ ≤ 1 → ∃ (n : ℕ) (z : Fin n → ℤ_[l]) (ω : Fin n → Om l), (∀ i, ω i ∈ K0 K ∧ ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ ω i ^ m = 1) ∧ c = ∑ i, algebraMap ℚ_[l] (Om l) (z i : ℚ_[l]) * ω i := by
  intro l _ K c hc h1
  obtain ⟨m, hm, hl, h⟩ := exists_mem_rootRing (x := c) (show c ∈ K.1 ⊓ MaximalUnramifiedExtension l from hc).2 h1
  obtain ⟨n, z, g, e⟩ := Submodule.mem_span_set'.mp (part_le_span (K0 K) hm hl (mem_part.mpr ⟨h, hc⟩))
  refine ⟨n, z, fun i => g i, fun i => (g i).2, ?_⟩
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l)]
  rfl

end GlobalTheory.UnramSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpanRhoCharLeCocycles
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Cut

namespace GlobalTheory.Cut.Coc

theorem KOG_torsion {O : Type} [CommRing O] [IsDomain O] {k : ℕ} (t : KOG O k) :
    ∃ d : O, d ≠ 0 ∧ d • t = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) v
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  choose u hu using hb
  exact ⟨u, funext fun j => hu j⟩

theorem smul_cont {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O)) {k : ℕ} (t : KOG O k) :
    Continuous fun a : O => a • t := by
  obtain ⟨d, hd, hdt⟩ := KOG_torsion t
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  have hopen : IsOpen ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.mp hO).1 n
  have hk : ∀ a ∈ (IsLocalRing.maximalIdeal O ^ n : Ideal O), a • t = 0 := by
    intro a ha
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    have : c * ϖ ^ n = (c * ((u⁻¹ : Oˣ) : O)) * (u * ϖ ^ n) := by
      rw [mul_assoc, Units.inv_mul_cancel_left]
    rw [this, mul_smul, hdt, smul_zero]
  refine continuous_of_continuousAt_zero (LinearMap.toSpanSingleton O (KOG O k) t) ?_
  refine (continuousAt_const (y := (0 : KOG O k))).congr ?_
  filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with a ha
  exact (hk a ha).symm

theorem lin_cont {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (hO : IsAdic (IsLocalRing.maximalIdeal O)) {k n : ℕ} {X : Type} [Fintype X]
    [DecidableEq X] (φ : (X → Matrix (Fin n) (Fin n) O) →ₗ[O] KOG O k) : Continuous φ := by
  have h : ∀ y : X → Matrix (Fin n) (Fin n) O,
      φ y = ∑ x, ∑ p, ∑ q, y x p q • φ (Pi.single x (Matrix.single p q 1)) := by
    intro y
    simp only [← map_smul, ← map_sum]
    congr 1
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single x]
    · simp only [Pi.single_eq_same, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single (y x)
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb.symm]
    · simp
  rw [show (φ : _ → _) = _ from funext h]
  refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun p _ =>
    continuous_finsetSum _ fun q _ => ?_
  exact (smul_cont hO _).comp (by fun_prop : Continuous fun y : X → Matrix (Fin n) (Fin n) O => y x p q)

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (S : IdempotentChoiceData D.nd i)

def tw (g : GE D.nd) : S.X' → MatN D.nd i :=
  fun x' => (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • rO D.nd i r (S.p x') g

theorem tw_mem (g : GE D.nd) : InR' D.nd r S (tw i r S g) := by
  refine ⟨1, fun _ _ => (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i), fun _ => g,
    fun _ => S.T'.algebraMap_mem _, ?_⟩
  rw [Fin.sum_univ_one]
  rfl

theorem yg_mem (g : GE D.nd) : InY D.nd r S (yg D.nd r S g) := by
  refine ⟨1, fun _ => tw i r S 1, fun _ => g, fun _ => tw_mem i r S 1, ?_⟩
  rw [Fin.sum_univ_one]
  funext x'
  simp [tw]

theorem yg_mul (g h : GE D.nd) :
    yg D.nd r S (g * h) = yg D.nd r S g + tw i r S g * yg D.nd r S h := by
  funext x'
  simp only [yg, tw, Pi.add_apply, Pi.mul_apply, map_mul, mul_inv, Units.val_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, mul_smul, mul_assoc]
  rw [smul_comm]
  abel

theorem yg_cont (hr : GoodR D.nd i r) : Continuous fun g => yg D.nd r S g := by
  refine continuous_pi fun x' => ?_
  have hc : Continuous fun g => rO D.nd i r (S.p x') g := (hr (S.p x')).1
  have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
    (D.nd.chi_cont i 1).comp continuous_inv
  refine ((h1.smul (hc.mul (continuous_const (y := Eel D.nd S x')))).sub
    (continuous_const (y := Eel D.nd S x'))).congr fun g => ?_
  simp [yg]

theorem cocW_le (hr : GoodR D.nd i r) (Xs : Set (D.nd.X i)) {k : ℕ}
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hψ : ∀ g, ψ (tw i r S g) = M g) :
    cocW i r S Xs ψ ≤ Z1 (WKG M) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨φ, hφ, -, rfl⟩
  refine ⟨(lin_cont (D.nd.O_adic i) φ).comp (yg_cont i r S hr), fun g h => ?_⟩
  show φ _ = φ _ + WKG M g (φ _)
  rw [yg_mul, map_add, hφ _ (tw_mem i r S g) _ (yg_mem i r S h), hψ]
  rfl

theorem blocks (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hS : GoodCongruenceObjects D.nd r ρ π S) (g : GE D.nd) :
    S.ψρ (tw i r S g) = WpO D.nd i ρ π g ∧
    ∀ c : Fin D.R.t, S.ψχ c (tw i r S g) =
      (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have key : ∀ w : (Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i),
      (((S.ψρ (tw i r S g)).map (toK D.nd i)).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i (S.ψχ c (tw i r S g)) * w.2 c) =
      toK D.nd i (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * w.2 c) := by
    intro w
    obtain ⟨u, rfl⟩ := S.e.surjective w
    rw [← h2 _ (tw_mem i r S g) u, ← h1 g u, ← map_smul, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [tw, hp, mapM]
  have hinj : Function.Injective (toK D.nd i) := IsFractionRing.injective _ _
  constructor
  · ext p q
    apply hinj
    have := congrFun (congrArg Prod.fst (key (Pi.single q 1, 0))) p
    simpa [mapM, WpO, twistM] using this
  · intro c
    apply hinj
    have := congrFun (congrArg Prod.snd (key (0, 1))) c
    simpa using this

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → GoodCongruenceObjects D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  intro D i r ρ π Xs S hr hS _
  refine ⟨cocW_le i r S hr Xs _ _ fun g => (blocks i r S ρ π hS g).1, fun c =>
    cocW_le i r S hr Xs _ _ fun g => ?_⟩
  rw [(blocks i r S ρ π hS g).2 c, mul_comm]
  rfl

end GlobalTheory.Cut.Coc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatOverProductPowerSeriesRing
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.FlatLocCompl

theorem mem_pow_smul_top_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (r : R) (k : ℕ) (z : S) :
    z ∈ ((Ideal.span {r}) ^ k • ⊤ : Submodule R S) ↔ z ∈ Ideal.span {(algebraMap R S r) ^ k} := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists,
    Ideal.mem_span_singleton]
  constructor
  · rintro ⟨e, -, rfl⟩
    exact ⟨e, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e, Submodule.mem_top, by rw [Algebra.smul_def, map_pow]⟩

theorem mem_pow_smul_top_self_iff {R : Type} [CommRing R] (r : R) (k : ℕ) (z : R) :
    z ∈ ((Ideal.span {r}) ^ k • ⊤ : Submodule R R) ↔ z ∈ Ideal.span {r ^ k} := by
  rw [mem_pow_smul_top_iff]; rfl

theorem flat_of_levels {B E : Type} [CommRing B] [IsNoetherianRing B] [CommRing E] [Algebra B E] (p : B)
    (hc : IsAdicComplete (Ideal.span {algebraMap B E p}) E)
    (hinj : ∀ (b : B) (k : ℕ), algebraMap B E b ∈ Ideal.span {(algebraMap B E p) ^ k} →
      b ∈ Ideal.span {p ^ k})
    (hden : ∀ (y : E) (k : ℕ), ∃ b : B, algebraMap B E b - y ∈ Ideal.span {(algebraMap B E p) ^ k}) :
    Module.Flat B E := by
  set I : Ideal B := Ideal.span {p} with hI
  haveI : IsAdicComplete I E := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := E)]
    rwa [hI, Ideal.map_span, Set.image_singleton]
  let f : B →ₗ[B] E := Algebra.linearMap B E
  have hle : ∀ k, (I ^ k • ⊤ : Submodule B B) ≤ (I ^ k • ⊤ : Submodule B E).comap f := by
    intro k z hz
    rw [Submodule.mem_comap, mem_pow_smul_top_iff]
    rw [mem_pow_smul_top_self_iff, Ideal.mem_span_singleton] at hz
    obtain ⟨c, rfl⟩ := hz
    exact Ideal.mem_span_singleton.2 ⟨algebraMap B E c, by simp [f, map_pow]⟩
  let fk : ∀ k : ℕ, AdicCompletion I B →ₗ[B] E ⧸ (I ^ k • ⊤ : Submodule B E) := fun k =>
    (Submodule.mapQ _ _ f (hle k)) ∘ₗ AdicCompletion.eval I B k
  have hfk : ∀ {m n : ℕ} (hmn : m ≤ n), Submodule.factorPow I E hmn ∘ₗ fk n = fk m := by
    intro m n hmn
    refine LinearMap.ext fun x => ?_
    simp only [fk, LinearMap.comp_apply, AdicCompletion.eval_apply]
    rw [← AdicCompletion.transitionMap_comp_eval_apply I B hmn x]
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
    rw [← hb]
    rfl
  let G : AdicCompletion I B →ₗ[B] E := IsAdicComplete.lift I fk hfk
  have hG : ∀ k x, Submodule.Quotient.mk (p := (I ^ k • ⊤ : Submodule B E)) (G x) = fk k x :=
    fun k x => IsAdicComplete.mk_lift I hfk k x
  have hbij : Function.Bijective G := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      ext k
      have h1 := hG k x
      rw [hx, Submodule.Quotient.mk_zero] at h1
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (x.val k)
      have h2 : fk k x = Submodule.Quotient.mk (f b) := by
        simp only [fk, LinearMap.comp_apply, AdicCompletion.eval_apply, ← hb]; rfl
      rw [h2, eq_comm, Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_iff] at h1
      rw [← hb, AdicCompletion.val_zero_apply, Submodule.Quotient.mk_eq_zero, mem_pow_smul_top_self_iff]
      exact hinj b k h1
    · intro y
      choose b hb using fun k => hden y k
      have hcau : ∀ k, b k ≡ b (k + 1) [SMOD (I ^ k • ⊤ : Submodule B B)] := by
        intro k
        rw [SModEq.sub_mem, mem_pow_smul_top_self_iff]
        apply hinj
        have h3 : algebraMap B E (b k - b (k + 1)) =
            (algebraMap B E (b k) - y) - (algebraMap B E (b (k + 1)) - y) := by rw [map_sub]; ring
        rw [h3]
        refine Ideal.sub_mem _ (hb k) ?_
        refine Ideal.span_singleton_le_span_singleton.2 ?_ (hb (k + 1))
        exact pow_dvd_pow _ (Nat.le_succ k)
      refine ⟨AdicCompletion.mk I B (AdicCompletion.AdicCauchySequence.mk I B b hcau), ?_⟩
      rw [IsHausdorff.eq_iff_smodEq (I := I)]
      intro k
      rw [SModEq, hG]
      change Submodule.Quotient.mk (f (b k)) = Submodule.Quotient.mk y
      rw [← SModEq, SModEq.sub_mem, mem_pow_smul_top_iff]
      exact hb k
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective G hbij).symm

end GlobalTheory.FlatLocCompl

namespace GlobalTheory.FlatLocCompl

theorem flat_letA (O : Type) [CommRing O] [IsNoetherianRing O] (n : ℕ) [NeZero n] (E : Type) [CommRing E]
    [Algebra (LetA O n) E] (p : ℕ) (hπ : IsUnit (algebraMap (LetA O n) E letπ))
    (hc : IsAdicComplete (Ideal.span {(p : E)}) E)
    (hden : ∀ (x : E) (k : ℕ), ∃ (a : LetA O n) (m : ℕ), x * algebraMap (LetA O n) E (letπ ^ m) -
      algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k})
    (hsat : ∀ (a : LetA O n) (k : ℕ), algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} →
      ∃ b : LetA O n, a = (p : LetA O n) ^ k * b) :
    Module.Flat (LetA O n) E := by
  let B := Localization.Away (letπ : LetA O n)
  let g : B →+* E := IsLocalization.Away.lift (S := B) (letπ : LetA O n) hπ
  letI : Algebra B E := g.toAlgebra
  have hg : ∀ a : LetA O n, algebraMap B E (algebraMap (LetA O n) B a) = algebraMap (LetA O n) E a :=
    fun a => IsLocalization.Away.lift_eq (S := B) (letπ : LetA O n) hπ a
  haveI : IsScalarTower (LetA O n) B E := IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  have hp : algebraMap B E (p : B) = (p : E) := map_natCast _ _
  haveI : Module.Flat B E := by
    refine flat_of_levels (p : B) (by rwa [hp]) ?_ ?_
    · intro b k hb
      rw [hp] at hb
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (letπ : LetA O n)) b
      have h1 : IsLocalization.mk' B a s * algebraMap (LetA O n) B s = algebraMap (LetA O n) B a :=
        IsLocalization.mk'_spec B a s
      have h2 : algebraMap (LetA O n) E a ∈ Ideal.span {(p : E) ^ k} := by
        rw [← hg, ← h1, map_mul]
        exact Ideal.mul_mem_right _ _ hb
      obtain ⟨c, rfl⟩ := hsat a k h2
      refine Ideal.mem_span_singleton.2 ⟨IsLocalization.mk' B c s, ?_⟩
      show IsLocalization.mk' B ((p : LetA O n) ^ k * c) s = (p : B) ^ k * IsLocalization.mk' B c s
      rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, map_pow, map_natCast]
    · intro y k
      obtain ⟨a, m, h⟩ := hden y k
      let s : Submonoid.powers (letπ : LetA O n) := ⟨letπ ^ m, m, rfl⟩
      refine ⟨IsLocalization.mk' B a s, ?_⟩
      rw [hp]
      have h1 : IsLocalization.mk' B a s * algebraMap (LetA O n) B (letπ ^ m) = algebraMap (LetA O n) B a :=
        IsLocalization.mk'_spec B a s
      have h2 : algebraMap B E (IsLocalization.mk' B a s) * algebraMap (LetA O n) E (letπ ^ m) =
          algebraMap (LetA O n) E a := by rw [← hg, ← hg, ← map_mul, h1]
      obtain ⟨v, hv⟩ := hπ.pow m
      rw [← map_pow] at hv
      have h3 : algebraMap B E (IsLocalization.mk' B a s) - y =
          -((y * algebraMap (LetA O n) E (letπ ^ m) - algebraMap (LetA O n) E a) * ↑v⁻¹) := by
        rw [← h2, ← hv, neg_mul_eq_neg_mul, neg_sub, ← sub_mul, mul_assoc, Units.mul_inv, mul_one]
      rw [h3]
      exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ h)
  exact Module.Flat.trans (LetA O n) B E

end GlobalTheory.FlatLocCompl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussGLZero
section
noncomputable section

open Matrix

namespace GlobalTheory.FlatConj

def gaussGL {k : Type} [Field k] [Fintype k] [DecidableEq k] (ψ : AddChar k ℂ) (ξ : kˣ →* ℂˣ) (r : ℕ) : ℂ :=
  ∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) * ψ (Matrix.trace (x : Matrix (Fin r) (Fin r) k))

variable {E : Type} [Field E] [NumberField E]

def resField (PP : Formalism.L2.DIV.Pl E) : Field (Formalism.L2.DIV.kP PP) :=
  haveI := PP.isMaximal
  Ideal.Quotient.field PP.asIdeal

def resFintype (PP : Formalism.L2.DIV.Pl E) : Fintype (Formalism.L2.DIV.kP PP) :=
  haveI : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  Fintype.ofFinite _

def gaussP (PP : Formalism.L2.DIV.Pl E) (ψ : AddChar (Formalism.L2.DIV.kP PP) ℂ) (ξ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (r : ℕ) : ℂ :=
  @gaussGL (Formalism.L2.DIV.kP PP) (resField PP) (resFintype PP) (Classical.decEq _) ψ ξ r

end GlobalTheory.FlatConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H2QuotientFiniteCardStatement
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_H2_twist_quotient_pow_and_card_le : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] {G : Type} [Group G] [TopologicalSpace G], Formalism.GaloisCohomology.LocalTateDualityK → FiniteDimensional ℚ_[p] K → PadicCoeff p O → ∀ (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ k : ℕ, Finite (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ∧ Nat.card (H2 (twist ε (O ⧸ IsLocalRing.maximalIdeal O ^ k))) ≤ Nat.card (O ⧸ IsLocalRing.maximalIdeal O ^ k) := by
  first | exact @GlobalTheory.QuotientH2Count.h2_quot_card | exact GlobalTheory.QuotientH2Count.h2_quot_card | (intros; apply GlobalTheory.QuotientH2Count.h2_quot_card <;> assumption)
end

