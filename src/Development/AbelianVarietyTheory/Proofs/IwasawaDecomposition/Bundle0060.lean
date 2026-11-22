import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedOrbitHasNearbyFixedPoint
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
open Polynomial

namespace GlobalTheory.AxLemma

section General
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_taylor_coeff_le (T : Finset K) (x : K) (r : ℝ) (hr : 0 ≤ r) (h : ∀ z ∈ T, ‖z - x‖ ≤ r)
    (q : ℕ) (hq : q ≤ T.card) :
    ‖(hasseDeriv q (∏ z ∈ T, (X - C z))).eval x‖ ≤ r ^ (T.card - q) := by
  rw [← taylor_coeff]
  have h1 : taylor x (∏ z ∈ T, (X - C z)) = ∏ z ∈ T, (X + C (x - z)) := by
    rw [taylor_apply, Polynomial.prod_comp]
    refine Finset.prod_congr rfl fun z _ => ?_
    simp only [sub_comp, X_comp, C_comp, map_sub]
    ring
  rw [h1, Finset.prod_X_add_C_coeff T _ hq]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun t ht => ?_
  rw [Finset.mem_powersetCard] at ht
  rw [norm_prod, ← ht.2, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun z hz => ?_
  rw [norm_sub_rev]
  exact h z (ht.1 hz)

omit [IsUltrametricDist K] in
theorem exists_root_near [IsAlgClosed K] (p : K[X]) (hp : 0 < p.natDegree) (x : K) :
    ∃ b ∈ p.roots, ‖p.leadingCoeff‖ * ‖b - x‖ ^ p.natDegree ≤ ‖p.eval x‖ := by
  first
  | exact @_root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le
  | exact _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le
  | (apply _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RootNormPowerBound.exists_root_norm_sub_pow_le ..)

end General

variable {l : ℕ} [Fact l.Prime]

theorem norm_gal' (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := (spectralNorm_eq_of_equiv g x).symm

theorem one_le_mul_norm_choose (n q : ℕ) (hn : 0 < n) (hq : q ≤ n) :
    1 ≤ (n : ℝ) * ‖((n.choose q : ℕ) : Om l)‖ := by
  have hl : l.Prime := Fact.out
  have h0 : n.choose q ≠ 0 := (Nat.choose_pos hq).ne'
  have h1 : ((n.choose q : ℕ) : Om l) = algebraMap ℚ_[l] (Om l) ((n.choose q : ℕ) : ℚ_[l]) := by
    rw [map_natCast]
  rw [h1, norm_algebraMap', Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast h0),
    Padic.valuation_natCast, zpow_neg, zpow_natCast]
  have h2 := Nat.pow_factorization_choose_le (p := l) (k := q) hn
  rw [Nat.factorization_def _ hl] at h2
  have h3 : (0 : ℝ) < (l : ℝ) ^ padicValNat l (n.choose q) := by
    have := hl.pos
    positivity
  rw [← div_eq_mul_inv, le_div_iff₀ h3, one_mul]
  exact_mod_cast h2

noncomputable def cst (k : ℕ) : ℝ := (2 : ℝ) ^ ((4 : ℝ) - (2 * k + 4) / 2 ^ k)

noncomputable def loss (k : ℕ) : ℝ := (2 : ℝ) ^ (((k : ℝ) + 1) / 2 ^ k)

theorem cst_succ (k : ℕ) : cst (k + 1) = cst k * loss k := by
  unfold cst loss
  rw [← Real.rpow_add (by norm_num)]
  congr 1
  push_cast
  field_simp
  ring

theorem one_le_loss (k : ℕ) : 1 ≤ loss k :=
  Real.one_le_rpow (by norm_num) (by positivity)

theorem loss_pow (k : ℕ) : loss k ^ (2 ^ k) = 2 ^ (k + 1) := by
  unfold loss
  rw [← Real.rpow_mul_natCast (by norm_num), ← Real.rpow_natCast (2 : ℝ) (k + 1)]
  congr 1
  push_cast
  field_simp

theorem one_le_cst (k : ℕ) : 1 ≤ cst k := by
  induction k with
  | zero => simp [cst]
  | succ k ih => rw [cst_succ]; exact one_le_mul_of_one_le_of_one_le ih (one_le_loss k)

theorem cst_le (k : ℕ) : cst k ≤ 16 := by
  unfold cst
  have : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
  rw [this]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have : (0 : ℝ) ≤ (2 * k + 4) / 2 ^ k := by positivity
  linarith

theorem ax_step (H : Subgroup (GQ l)) (k : ℕ) : ∀ (x : Om l) (r : ℝ) (S : Finset (Om l)),
    (∀ g ∈ H, g x ∈ S) → S.card ≤ 2 ^ k → (∀ g ∈ H, ‖g x - x‖ ≤ r) →
    ∃ y : Om l, (∀ g ∈ H, g y = y) ∧ ‖x - y‖ ≤ cst k * r := by
  classical
  induction k with
  | zero =>
    intro x r S hS hc hr
    have hr0 : 0 ≤ r := by simpa using hr 1 H.one_mem
    refine ⟨x, fun g hg => ?_, ?_⟩
    · have hx : x ∈ S := by simpa using hS 1 H.one_mem
      exact Finset.card_le_one.1 (by simpa using hc) _ (hS g hg) _ hx
    · have := one_le_cst 0
      rw [sub_self, norm_zero]; positivity
  | succ k ih =>
    intro x r S hS hc hr
    have hr0 : 0 ≤ r := by simpa using hr 1 H.one_mem
    have hc1 := one_le_cst k
    have hl1 := one_le_loss k
    set T := S.filter (fun z => ∃ g ∈ H, g x = z) with hT
    have hTm : ∀ z, z ∈ T ↔ ∃ g ∈ H, g x = z := by
      intro z
      rw [hT, Finset.mem_filter]
      exact ⟨fun h => h.2, fun ⟨g, hg, h⟩ => ⟨h ▸ hS g hg, g, hg, h⟩⟩
    have hTc : T.card ≤ 2 ^ (k + 1) := (Finset.card_filter_le _ _).trans hc
    by_cases hk : T.card ≤ 2 ^ k
    · obtain ⟨y, hy, hxy⟩ := ih x r T (fun g hg => (hTm _).2 ⟨g, hg, rfl⟩) hk hr
      refine ⟨y, hy, hxy.trans ?_⟩
      rw [cst_succ]
      refine mul_le_mul_of_nonneg_right ?_ hr0
      nlinarith
    push Not at hk
    set f : (Om l)[X] := ∏ z ∈ T, (X - C z) with hf
    set q := T.card - 2 ^ k with hq
    have hq1 : T.card - q = 2 ^ k := by omega
    have hfm : f.Monic := monic_prod_of_monic _ _ fun z _ => monic_X_sub_C z
    have hfd : f.natDegree = T.card := by
      rw [hf, natDegree_prod_of_monic _ _ fun z _ => monic_X_sub_C z]; simp
    have hfg : ∀ g ∈ H, f.map (g : Om l →+* Om l) = f := by
      intro g hg
      rw [hf, Polynomial.map_prod]
      refine Finset.prod_bij (fun z _ => g z) ?_ ?_ ?_ ?_
      · intro z hz
        obtain ⟨g', hg', rfl⟩ := (hTm z).1 hz
        exact (hTm _).2 ⟨g * g', H.mul_mem hg hg', rfl⟩
      · intro a _ b _ h
        exact g.injective h
      · intro z hz
        obtain ⟨g', hg', rfl⟩ := (hTm z).1 hz
        refine ⟨(g⁻¹ * g') x, (hTm _).2 ⟨_, H.mul_mem (H.inv_mem hg) hg', rfl⟩, ?_⟩
        rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
      · intro z _
        simp
    set p := hasseDeriv q f with hp
    have hpd : p.natDegree = 2 ^ k := by rw [hp, natDegree_hasseDeriv, hfd, hq1]
    have hpl : p.leadingCoeff = ((T.card.choose q : ℕ) : Om l) := by
      have h2 : 2 ^ k + q = T.card := by omega
      rw [leadingCoeff, hpd, hp, hasseDeriv_coeff, h2]
      conv_lhs => rw [← hfd, hfm.coeff_natDegree, hfd]
      rw [mul_one]
    have hpg : ∀ g ∈ H, p.map (g : Om l →+* Om l) = p := by
      intro g hg
      ext n
      have := congrArg (fun u => coeff u (n + q)) (hfg g hg)
      simp only [coeff_map] at this
      rw [coeff_map, hp, hasseDeriv_coeff, map_mul, map_natCast, this]
    have hp0 : p ≠ 0 := by
      intro h
      rw [h, natDegree_zero] at hpd
      exact (pow_pos two_pos k).ne hpd
    obtain ⟨b, hb, hbx⟩ := exists_root_near p (by rw [hpd]; positivity) x
    have hev := norm_taylor_coeff_le T x r hr0 (fun z hz => by
      obtain ⟨g, hg, rfl⟩ := (hTm z).1 hz
      exact hr g hg) q (by omega)
    rw [← hf, ← hp, hq1] at hev
    rw [hpd, hpl] at hbx
    have hch := one_le_mul_norm_choose (l := l) T.card q (by omega) (by omega)
    have hbr : ‖b - x‖ ≤ loss k * r := by
      refine le_of_pow_le_pow_left₀ (pow_pos two_pos k).ne' (by positivity) ?_
      rw [mul_pow, loss_pow]
      have h1 : (T.card : ℝ) ≤ 2 ^ (k + 1) := by exact_mod_cast hTc
      have h2 : 0 ≤ ‖b - x‖ ^ 2 ^ k := by positivity
      have h3 : (0 : ℝ) ≤ T.card := by positivity
      calc ‖b - x‖ ^ 2 ^ k ≤ (T.card * ‖((T.card.choose q : ℕ) : Om l)‖) * ‖b - x‖ ^ 2 ^ k :=
            le_mul_of_one_le_left h2 hch
        _ ≤ T.card * r ^ 2 ^ k := by
            rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hbx.trans hev) h3
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
    have hrr : r ≤ loss k * r := le_mul_of_one_le_left hr0 hl1
    have hgb : ∀ g ∈ H, ‖g b - b‖ ≤ loss k * r := by
      intro g hg
      have e : g b - b = g (b - x) + ((g x - x) + (x - b)) := by rw [map_sub]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))
      · rw [norm_gal']; exact hbr
      · exact (hr g hg).trans hrr
      · rw [norm_sub_rev]; exact hbr
    obtain ⟨y, hy, hby⟩ := ih b (loss k * r) p.roots.toFinset (fun g hg => by
      rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def]
      have h0 : p.eval b = 0 := (mem_roots hp0).1 hb
      have h1 := eval_map_apply (g : Om l →+* Om l) (p := p) b
      rw [hpg g hg, h0, map_zero] at h1
      exact h1)
      ((Multiset.toFinset_card_le _).trans ((card_roots' p).trans hpd.le)) hgb
    refine ⟨y, hy, ?_⟩
    have e : x - y = (x - b) + (b - y) := by ring
    rw [e, cst_succ, mul_assoc]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hby)
    rw [norm_sub_rev]
    exact hbr.trans (le_mul_of_one_le_left (by positivity) hc1)

theorem ax_lemma : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (x : Om l) (r : ℝ),
    (∀ g ∈ H, ‖g x - x‖ ≤ r) → ∃ y : Om l, (∀ g ∈ H, g y = y) ∧ ‖x - y‖ ≤ c * r := by
  classical
  intro l _
  refine ⟨16, by norm_num, fun H x r hr => ?_⟩
  have hr0 : 0 ≤ r := by simpa using hr 1 H.one_mem
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  set S := ((minpoly ℚ_[l] x).aroots (Om l)).toFinset with hS
  obtain ⟨y, hy, hxy⟩ := ax_step H S.card x r S (fun g _ => by
    rw [hS, Multiset.mem_toFinset, mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]) Nat.lt_two_pow_self.le hr
  exact ⟨y, hy, hxy.trans (mul_le_mul_of_nonneg_right (cst_le _) hr0)⟩

end GlobalTheory.AxLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

open IsLocalRing

theorem exists_algEquiv_rootOfUnity_eq_pow (V K : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K]
    (hfin : Finite (V ⧸ maximalIdeal V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    [Algebra V Ω] [IsScalarTower V K Ω] :
    ∃ φ : Ω ≃ₐ[K] Ω, ∀ (x : Ω) (m : ℕ), (m : V) ∉ maximalIdeal V → x ^ m = 1 →
      φ x = x ^ Nat.card (V ⧸ maximalIdeal V) := by
  have : IsGalois K Ω := {}
  have hc : SMulCommClass (Ω ≃ₐ[K] Ω) V Ω := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    exact map_smul g _ _⟩
  let : TopologicalSpace (integralClosure V Ω) := ⊥
  have : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  have : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : Ω)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  have : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (b : Ω)).2
      fun g => congrArg Subtype.val (hb g)
    have hint : IsIntegral V k := by
      have h2 : IsIntegral V (algebraMap K Ω k) := hk ▸ b.2
      exact (isIntegral_algebraMap_iff (algebraMap K Ω).injective).1 h2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    refine ⟨v, Subtype.ext ?_⟩
    rw [← hk, ← hv, ← IsScalarTower.algebraMap_apply]
    rfl
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have : FaithfulSMul V (integralClosure V Ω) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  obtain ⟨Q, hQ, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := integralClosure V Ω) (maximalIdeal V)
  let : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  let : Field (integralClosure V Ω ⧸ Q) := Ideal.Quotient.field _
  let : Fintype (V ⧸ maximalIdeal V) := Fintype.ofFinite _
  have : Algebra.IsAlgebraic (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) := by
    have hi : Algebra.IsIntegral (V ⧸ maximalIdeal V) (integralClosure V Ω ⧸ Q) :=
      Ideal.Quotient.algebra_isIntegral_of_liesOver _ _
    exact hi.isAlgebraic
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) Q
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  have hu : Q.under V = maximalIdeal V := hQo.over.symm
  have hF : IsArithFrobAt V σ.1 Q := by
    intro x
    have h := DFunLike.congr_fun hσ (Ideal.Quotient.mk _ x)
    rw [← Ideal.Quotient.eq, map_pow, hu, Nat.card_eq_fintype_card]
    exact h
  refine ⟨σ.1, fun x m hm hx => ?_⟩
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (by simp))
  have hxi : IsIntegral V x := IsIntegral.of_pow hm0 (by rw [hx]; exact isIntegral_one)
  have hmQ : ((m : ℕ) : integralClosure V Ω) ∉ Q := by
    intro h
    apply hm
    rw [← hu, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact h
  have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF (ζ := ⟨x, hxi⟩) (m := m)
    (Subtype.ext hx) hmQ
  rw [hu] at h
  exact congrArg Subtype.val h

theorem exists_frobenius_Kur (l : ℕ) [Fact l.Prime] :
    ∃ σ : ↥(MaximalUnramifiedExtension l) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l),
      ∀ (c : ↥(MaximalUnramifiedExtension l)) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → σ c = c ^ l := by
  have e : (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) ≃+* ZMod l := PadicInt.residueField
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hcard : Nat.card (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = l := by
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  obtain ⟨φ, hφ⟩ := exists_algEquiv_rootOfUnity_eq_pow ℤ_[l] ℚ_[l]
    (Finite.of_equiv _ e.symm.toEquiv) (Om l)
  rw [hcard] at hφ
  have hφ' : ∀ (x : Om l) (m : ℕ), ¬ l ∣ m → x ^ m = 1 → φ x = x ^ l := by
    intro x m hm hx
    refine hφ x m (fun h => hm ?_) hx
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_natCast, ZMod.natCast_eq_zero_iff] at h
    exact h
  have hle : (MaximalUnramifiedExtension l).map (φ : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, ⟨m, hm, hlm, hx⟩, rfl⟩
    exact ⟨m, hm, hlm, by rw [← map_pow, hx, map_one]⟩
  refine ⟨((φ : Om l →ₐ[ℚ_[l]] Om l).comp (MaximalUnramifiedExtension l).val).codRestrict (MaximalUnramifiedExtension l).toSubalgebra
    (fun x => hle ⟨x, x.2, rfl⟩), fun c m _ hlm hc => Subtype.ext ?_⟩
  exact hφ' c m hlm (congrArg Subtype.val hc)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
section
noncomputable section
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Formalism.Per

theorem zeta_pow_iter {M : Type*} [Monoid M] {p : ℕ} {ζ : ℕ → M} (hζ : ∀ n, ζ (n + 1) ^ p = ζ n)
    (m n : ℕ) : ζ (m + n) ^ p ^ n = ζ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, hζ, ih]

theorem zeta_exists_system (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] (p : ℕ)
    [hp : Fact p.Prime] :
    ∃ ζ : ℕ → K, ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ p = ζ m) ∧ ζ 1 ≠ 1 := by
  have : NeZero (p : K) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p K)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos p K hp.out.pos))
  have hzp : IsPrimitiveRoot z p := Polynomial.isRoot_cyclotomic_iff.1 hz
  choose r hr using fun x : K => IsAlgClosed.exists_pow_nat_eq x hp.out.pos
  refine ⟨fun n => Nat.casesOn n 1 (fun m => r^[m] z), rfl, fun n => ?_,
    hzp.ne_one hp.out.one_lt⟩
  cases n with
  | zero => exact hzp.pow_eq_one
  | succ m =>
    show r^[m + 1] z ^ p = r^[m] z
    rw [Function.iterate_succ_apply', hr]

section Tilt

variable {p : ℕ} [hp : Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem zeta_coeff_root_iterate (x : PreTilt O p) (n m : ℕ) :
    PreTilt.coeff m ((frobeniusEquiv (PreTilt O p) p).symm^[n] x) = PreTilt.coeff (m + n) x := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', PreTilt.coeff_frobeniusEquiv_symm, ih]
    congr 2
    omega

theorem zeta_exists_tilt [IsAdicComplete (Ideal.span {(p : O)}) O] (x : ℕ → O)
    (hx : ∀ n, x (n + 1) ^ p = x n) :
    ∃ e : PreTilt O p, ∀ n, ((frobeniusEquiv (PreTilt O p) p).symm^[n] e).untilt = x n := by
  let e : PreTilt O p := ⟨fun n => Ideal.Quotient.mk (Ideal.span {(p : O)}) (x n), fun n => by
    show (Ideal.Quotient.mk (Ideal.span {(p : O)}) (x (n + 1))) ^ p = _
    rw [← map_pow, hx]⟩
  refine ⟨e, fun n => Perfection.teichmuller_spec fun m => ⟨x (n + m), ?_, by rw [zeta_pow_iter hx]⟩⟩
  have := zeta_coeff_root_iterate e n m
  rw [add_comm] at this
  exact this.symm

end Tilt

theorem exists_zeta_eps (l : ℕ) [hl : Fact l.Prime] :
    ∃ (ζ : ℕ → Om l) (ε : Per.Fl l), ζ 0 = 1 ∧ (∀ m, ζ (m + 1) ^ l = ζ m) ∧ ζ 1 ≠ 1 ∧
      ∀ m, (rootT ε m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (ζ m) := by
  obtain ⟨ζ, h0, hs, h1⟩ := zeta_exists_system (Om l) l
  have hmem : ∀ m, algebraMap (Om l) ℂ_[l] (ζ m) ∈ PadicComplexInt l := fun m => by
    have h : algebraMap (Om l) ℂ_[l] (ζ m) ^ l ^ m = 1 := by
      have := zeta_pow_iter hs 0 m
      rw [zero_add, h0] at this
      rw [← map_pow, this, map_one]
    have h2 : Valued.v (algebraMap (Om l) ℂ_[l] (ζ m)) ^ l ^ m ≤ 1 := by
      rw [← map_pow, h, map_one]
    exact (pow_le_one_iff_of_nonneg zero_le (pow_ne_zero _ hl.out.ne_zero)).1 h2
  obtain ⟨e, he⟩ := zeta_exists_tilt (p := l) (O := Per.OC l)
    (fun m => ⟨algebraMap (Om l) ℂ_[l] (ζ m), hmem m⟩) (fun m => Subtype.ext (by
      show algebraMap (Om l) ℂ_[l] (ζ (m + 1)) ^ l = algebraMap (Om l) ℂ_[l] (ζ m)
      rw [← map_pow, hs]))
  exact ⟨ζ, e, h0, hs, h1, fun m => congrArg Subtype.val (he m)⟩

end GlobalTheory.MemLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitPowNormVSubOne
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.OneUnitRoot

open IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

theorem exists_unit_pow_normV_sub_one (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (y : (v.adicCompletion E)ˣ) (hy : Valued.v ((y : v.adicCompletion E) - 1) < 1) :
    ∃ z : (v.adicCompletion E)ˣ, Valued.v (z : v.adicCompletion E) = 1 ∧ z ^ (normV v - 1) = y := by
  have hc := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set n := normV v - 1 with hn
  have hcard : Nat.card (ResidueField (v.adicCompletionIntegers E)) = normV v :=
    Formalism.UG.P.tjcosets_card_residue v
  haveI : Finite (ResidueField (v.adicCompletionIntegers E)) :=
    GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  haveI := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers E))
  have hq0 : ((normV v : ℕ) : ResidueField (v.adicCompletionIntegers E)) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero _
  have hq1 : 2 ≤ normV v := by
    rw [← hcard]; exact Finite.one_lt_card
  have hnres : ((n : ℕ) : ResidueField (v.adicCompletionIntegers E)) = -1 := by
    rw [hn, Nat.cast_sub (by omega), hq0]; simp
  have hnpos : 0 < n := by omega

  have hy1 : Valued.v (y : v.adicCompletion E) = 1 := by
    have e : (y : v.adicCompletion E) = ((y : v.adicCompletion E) - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · exact map_one _
    · rwa [map_one]
  set y' : v.adicCompletionIntegers E := ⟨y, by
    show Valued.v (y : v.adicCompletion E) ≤ 1; exact hy1.le⟩
  have hm : (X ^ n - C y' : (v.adicCompletionIntegers E)[X]).Monic := monic_X_pow_sub_C y' hnpos.ne'
  have hev : eval 1 (X ^ n - C y' : (v.adicCompletionIntegers E)[X]) ∈ maximalIdeal (v.adicCompletionIntegers E) := by
    simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C]
    rw [← neg_sub, Ideal.neg_mem_iff, mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact ne_of_lt hy
  have hder : IsUnit (eval 1 (derivative (X ^ n - C y' : (v.adicCompletionIntegers E)[X]))) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    rw [← isUnit_map_iff (residue (v.adicCompletionIntegers E)), map_natCast, hnres]
    exact isUnit_one.neg
  obtain ⟨r, hr, hr1⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers E))
    _ hm 1 hev (hder.map _)
  have hrn : r ^ n = y' := by
    have := hr
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  have hrv : Valued.v (r : v.adicCompletion E) = 1 := by
    have h1 : Valued.v ((r : v.adicCompletion E) - 1) < 1 := by
      have := hr1
      rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one] at this
      exact lt_of_le_of_ne (r - 1).2 this
    have e : (r : v.adicCompletion E) = ((r : v.adicCompletion E) - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · exact map_one _
    · rwa [map_one]
  have hr0 : (r : v.adicCompletion E) ≠ 0 := by
    intro h; rw [h, map_zero] at hrv; exact zero_ne_one hrv
  refine ⟨Units.mk0 _ hr0, hrv, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact congrArg Subtype.val hrn

end GlobalTheory.OneUnitRoot
end
end

