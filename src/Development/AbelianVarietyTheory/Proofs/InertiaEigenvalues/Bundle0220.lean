import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0154

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedSubfieldLeCyclotomicExt
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

noncomputable section

namespace GlobalTheory.NL.Points

variable {l : ℕ} [Fact l.Prime]

theorem exists_aut (F : IntermediateField ℚ_[l] (Om l)) (f : ↥F →ₐ[ℚ_[l]] Om l) :
    ∃ g : GQ l, ∀ x : ↥F, g (x : Om l) = f x := by
  refine ⟨AlgEquiv.ofBijective (f.liftNormal (Om l)) (AlgHom.normal_bijective _ _ _ _), fun x => ?_⟩
  exact f.liftNormal_commutes (Om l) x

theorem exists_restr {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (g : GQ l)
    (F : IntermediateField ℚ_[l] (Om l)) (hF : F ≤ Ks K s) :
    ∃ τ : ↥F →ₐ[ℚ_[l]] ↥LL.1, ∀ x : ↥F, (τ x : Om l) = g (x : Om l) :=
  ⟨(g.toAlgHom.comp F.val).codRestrict LL.1.toSubalgebra
    (fun x => h.2.2.2 (g.toAlgHom.comp (Ks K s).val) ⟨x, hF x.2⟩), fun _ => rfl⟩

theorem zeta_pow (P : LocPrime l) (m : ℕ) : P.ζQ m ^ l ^ m = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem zeta_pow_one (P : LocPrime l) (m : ℕ) : P.ζQ (m + 1) ^ l ^ m = P.ζQ 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem zeta_prim (P : LocPrime l) (s : ℕ) (hs : 1 ≤ s) : IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hnot : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [zeta_pow_one]; exact P.ζQ_one
  rw [← orderOf_eq_prime_pow hnot (zeta_pow P (m + 1))]
  exact IsPrimitiveRoot.orderOf _

theorem zeta_mem (P : LocPrime l) (K : FinExt l) (s : ℕ) : P.ζQ s ∈ Ks K s :=
  (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ (zeta_pow P s))

theorem unramifiedSubfield_le_cyclotomicExt (K : FinExt l) (s : ℕ) : K0 K ≤ Ks K s := le_sup_left

theorem card_emb {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (F : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥F] (hF : F ≤ Ks K s) :
    Nat.card (↥F →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥F := by
  have hb : Function.Bijective (fun f : ↥F →ₐ[ℚ_[l]] ↥LL.1 => LL.1.val.comp f) := by
    constructor
    · intro f f' hf
      exact AlgHom.ext fun x => Subtype.ext (DFunLike.congr_fun hf x)
    · intro f
      obtain ⟨g, hg⟩ := exists_aut F f
      obtain ⟨τ, hτ⟩ := exists_restr h g F hF
      exact ⟨τ, AlgHom.ext fun x => (hτ x).trans (hg x)⟩
  rw [Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card]
  exact AlgHom.card ℚ_[l] ↥F (Om l)

variable {P : LocPrime l} (H : LocHW l P) {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

theorem pt_of_aut (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g : GQ l)
    (h0 : ∀ c : ↥(K0 K), g (c : Om l) = ((H.W K s LL h).emb i c : ↥LL.1))
    (hζ : g (P.ζQ s) = ζ) (hτ : ∀ x : ↥K.1, g (x : Om l) = τ x) : Pt H h i ζ τ := by
  obtain ⟨τs, hτs⟩ := exists_restr h g (Ks K s) le_rfl
  refine ⟨τs, ⟨fun x y hxy => Subtype.ext ?_, fun y hy => Subtype.ext ?_⟩, fun x y hxy => Subtype.ext ?_⟩
  · rw [hτs, hxy, h0]
  · rw [hτs, hy, hζ]
  · rw [hτs, hxy, hτ]

theorem aut_of_pt (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hp : Pt H h i ζ τ) :
    ∃ g : GQ l, (∀ c : ↥(K0 K), g (c : Om l) = ((H.W K s LL h).emb i c : ↥LL.1)) ∧
      g (P.ζQ s) = ζ ∧ ∀ x : ↥K.1, g (x : Om l) = τ x := by
  obtain ⟨τs, ⟨h1, h2⟩, h3⟩ := hp
  obtain ⟨g, hg⟩ := exists_aut (Ks K s) (LL.1.val.comp τs)
  refine ⟨g, fun c => ?_, ?_, fun x => ?_⟩
  · rw [← h1 c ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩ rfl]
    exact hg ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩
  · rw [← h2 ⟨_, zeta_mem P K s⟩ rfl]
    exact hg ⟨_, zeta_mem P K s⟩
  · rw [h3 x ⟨x, h.2.2.1 x.2⟩ rfl]
    exact hg ⟨x, h.2.2.1 x.2⟩

theorem exists_pt (i : Let K) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ (l ^ s)) : ∃ τ, Pt H h i ζ τ := by
  obtain ⟨g₀, hg₀⟩ := exists_aut (K0 K) (LL.1.val.comp ((H.W K s LL h).emb i))
  have h1 : IsPrimitiveRoot (g₀.symm (ζ : Om l)) (l ^ s) :=
    (hζ.map_of_injective (f := LL.1.val) LL.1.val.toRingHom.injective).map_of_injective g₀.symm.injective
  have hconj : IsConjRoot ↥(K0 K) (g₀.symm (ζ : Om l)) (P.ζQ s) := by
    unfold IsConjRoot
    rw [GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s h.1 _ h1,
      GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s h.1 _ (zeta_prim P s h.1)]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  obtain ⟨τ, hτ⟩ := exists_restr h ((σ.restrictScalars ℚ_[l]).trans g₀) K.1 h.2.2.1
  refine ⟨τ, pt_of_aut H h i ζ τ ((σ.restrictScalars ℚ_[l]).trans g₀) (fun c => ?_) ?_
    (fun x => (hτ x).symm)⟩
  · have : σ (c : Om l) = c := σ.commutes c
    change g₀ (σ (c : Om l)) = _
    rw [this]
    exact hg₀ c
  · change g₀ (σ (P.ζQ s)) = _
    rw [hσ, AlgEquiv.apply_symm_apply]

theorem pt_props (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hp : Pt H h i ζ τ) :
    IsPrimitiveRoot ζ (l ^ s) ∧
      τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = (H.W K s LL h).emb i ∧
      ∃ ι, Comp H h i ζ τ ι := by
  obtain ⟨g, h0, hζ, hτ⟩ := aut_of_pt H h i ζ τ hp
  refine ⟨?_, ?_, (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp
    (g.symm.toAlgHom.comp LL.1.val), fun c => ?_, ?_, fun c => ?_⟩
  · have h1 := (zeta_prim P s h.1).map_of_injective g.injective
    rw [hζ] at h1
    exact IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) h1 LL.1.val.toRingHom.injective
  · refine AlgHom.ext fun c => Subtype.ext ?_
    rw [← h0 c]
    exact (hτ _).symm
  · change algebraMap (Om l) P.R.BdR (g.symm (((H.W K s LL h).emb i c : ↥LL.1) : Om l)) = _
    rw [← h0 c, AlgEquiv.symm_apply_apply]
    rfl
  · change algebraMap (Om l) P.R.BdR (g.symm (ζ : Om l)) = _
    rw [← hζ, AlgEquiv.symm_apply_apply]
  · change algebraMap (Om l) P.R.BdR (g.symm ((τ c : ↥LL.1) : Om l)) = _
    rw [← hτ c, AlgEquiv.symm_apply_apply]
    rfl

theorem exists_pt_over (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : ∃ (i : Let K) (ζ : ↥LL.1), Pt H h i ζ τ := by
  obtain ⟨g, hg⟩ := exists_aut K.1 (LL.1.val.comp τ)
  obtain ⟨i, hi⟩ := (H.W K s LL h).emb_bij.2 (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))
  refine ⟨i, ⟨g (P.ζQ s), h.2.2.2 (g.toAlgHom.comp (Ks K s).val) ⟨_, zeta_mem P K s⟩⟩,
    pt_of_aut H h i _ τ g (fun c => ?_) rfl hg⟩
  rw [hi]
  exact hg (algebraMap ↥(K0 K) ↥K.1 c)

theorem points : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; (∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ τ, Pt (HW l) h i ζ τ) ∧ (∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → IsPrimitiveRoot ζ (l ^ s) ∧ τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb i ∧ ∃ ι, Comp (HW l) h i ζ τ ι) ∧ (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ (i : Let K) (ζ : ↥LL.1), Pt (HW l) h i ζ τ) ∧ Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 ∧ Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) := by
  intro D HW l _ K s LL h
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  exact ⟨exists_pt (HW l) h, pt_props (HW l) h, exists_pt_over (HW l) h,
    card_emb h K.1 h.2.2.1, card_emb h (K0 K) (unramifiedSubfield_le_cyclotomicExt K s)⟩

end GlobalTheory.NL.Points
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLevelExpansionAtRootOfUnity
section
noncomputable section

namespace GlobalTheory.NL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace LevPt

open PowerSeries

theorem simple_zero {L : Type} [Field L] (f : PowerSeries L) (h0 : constantCoeff f = 0)
    (h1 : coeff 1 f ≠ 0) : ∃ w : PowerSeries L, IsUnit w ∧ f = X * w := by
  obtain ⟨w, rfl⟩ := X_dvd_iff.mpr h0
  refine ⟨w, ?_, rfl⟩
  rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
  simpa using h1

theorem coeff_one_pow_of_deriv {L : Type} [Field L] (U : PowerSeries L)
    (hU : derivative L U = U) (m : ℕ) : coeff 1 (U ^ m) = (m : L) * constantCoeff U ^ m := by
  have h : derivative L (U ^ m) = (m : PowerSeries L) * U ^ m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Derivation.leibniz, ih, hU]
      push_cast
      simp only [smul_eq_mul]
      ring
  have h2 := congrArg (coeff 0) h
  rw [coeff_derivative] at h2
  simpa using h2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem φA_one_add : W.φA (1 + letπ) = (1 + letπ) ^ PD.p := by
  rw [map_add, map_one, W.φA_π]
  funext i
  have := W.q₀_def
  simp only [Pi.add_apply, Pi.mul_apply, Pi.one_apply, Pi.pow_apply, letπ, LocWach.q]
  linear_combination this

theorem φA_pow_one_add (k : ℕ) : (W.φA ^ k) (1 + letπ) = (1 + letπ) ^ (PD.p ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, AlgHom.mul_apply, φA_one_add, map_pow, ih, ← pow_mul, ← pow_succ]

theorem X_eq : W.X = (1 + letπ) ^ (PD.p ^ (W.s - 1)) - 1 := by
  rw [← φA_pow_one_add W, map_add, map_one, LocWach.X]
  ring

theorem q_eq : W.q = ∑ k ∈ Finset.range PD.p, (1 + letπ : LetA O n) ^ k := by
  funext i
  have h := W.q₀_def
  have h2 := geom_sum_mul (1 + X : PowerSeries O) PD.p
  have h3 : X * (W.q₀ - ∑ k ∈ Finset.range PD.p, (1 + X : PowerSeries O) ^ k) = 0 := by
    linear_combination h - h2
  have h4 : W.q₀ - ∑ k ∈ Finset.range PD.p, (1 + X : PowerSeries O) ^ k = 0 := by
    ext m
    have := congrArg (coeff (m + 1)) h3
    rw [coeff_succ_X_mul] at this
    simpa using this
  simp only [LocWach.q, Finset.sum_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ]
  exact sub_eq_zero.mp h4

theorem Q_eq : W.Q = ∑ k ∈ Finset.range PD.p, ((1 + letπ : LetA O n) ^ (PD.p ^ (W.s - 1))) ^ k := by
  rw [LocWach.Q, q_eq, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_pow, φA_pow_one_add]

theorem lev_letE (i : ZMod n) (ζ : LL) : W.lev i ζ (letE i) = 1 := by
  have h := W.lev_letter i ζ (1 - letE i) (by simp [letE])
  rw [map_sub, map_one] at h
  exact (sub_eq_zero.mp h).symm

theorem lev_values [CharZero LL] (i : ZMod n) (ζ : LL) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) :
    (∃ w : PowerSeries LL, IsUnit w ∧ W.lev i ζ letπ = C (ζ - 1) + X * w) ∧
    (ζ ^ (PD.p ^ (W.s - 1)) = 1 → (∃ w : PowerSeries LL, IsUnit w ∧ W.lev i ζ W.X = X * w) ∧
      IsUnit (W.lev i ζ W.Q)) ∧
    (IsPrimitiveRoot ζ (PD.p ^ W.s) → (∃ w : PowerSeries LL, IsUnit w ∧ W.lev i ζ W.Q = X * w) ∧
      IsUnit (W.lev i ζ W.X)) ∧
    (constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (PD.p ^ (W.s - 1)) = 1) ∧
    (constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (PD.p ^ W.s)) ∧ W.lev i ζ W.Q ≠ 0 := by
  have hp : PD.p.Prime := PD.hp
  haveI : Fact PD.p.Prime := ⟨hp⟩
  obtain ⟨E, hE0, hE1, hE⟩ := W.lev_π i ζ hζ
  obtain ⟨j, hj⟩ := hζ
  have hζ0 : ζ ≠ 0 := hj.ne_zero (pow_ne_zero _ hp.ne_zero)
  set U : PowerSeries LL := C ζ * E with hUdef
  have hU0 : constantCoeff U = ζ := by simp [hUdef, hE0]
  have hU1 : derivative LL U = U := by
    rw [hUdef, Derivation.leibniz, hE1, derivative_C]
    simp
  have hlevU : W.lev i ζ (1 + letπ) = U := by rw [map_add, map_one, hE]
  have hc1 : ∀ m : ℕ, m ≠ 0 → coeff 1 (U ^ m - 1) ≠ 0 := by
    intro m hm
    rw [map_sub, coeff_one_pow_of_deriv U hU1, hU0, coeff_one]
    simp [hm, hζ0]
  have hc0 : ∀ m : ℕ, constantCoeff (U ^ m - 1) = ζ ^ m - 1 := by
    intro m
    simp [hU0]
  obtain ⟨r, hr⟩ : ∃ r, W.s = r + 1 := ⟨W.s - 1, by have := W.s_pos; omega⟩
  have hX : W.lev i ζ W.X = U ^ (PD.p ^ r) - 1 := by
    rw [X_eq, map_sub, map_one, map_pow, hlevU, hr, Nat.add_sub_cancel]
  have hQ : W.lev i ζ W.Q = ∑ k ∈ Finset.range PD.p, (U ^ (PD.p ^ r)) ^ k := by
    rw [Q_eq, map_sum, hr, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_pow, map_pow, hlevU]
  have hXQ : W.lev i ζ W.Q * W.lev i ζ W.X = U ^ (PD.p ^ (r + 1)) - 1 := by
    rw [hX, hQ, geom_sum_mul, ← pow_mul, ← pow_succ]
  have hQ0 : constantCoeff (W.lev i ζ W.Q) = ∑ k ∈ Finset.range PD.p, (ζ ^ (PD.p ^ r)) ^ k := by
    rw [hQ, map_sum]
    simp [hU0]
  have hprim : IsPrimitiveRoot ζ (PD.p ^ (r + 1)) ↔
      ζ ^ (PD.p ^ (r + 1)) = 1 ∧ ¬ ζ ^ (PD.p ^ r) = 1 := by
    constructor
    · intro h
      refine ⟨h.pow_eq_one, h.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hp.ne_zero) ?_⟩
      exact Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self r)
    · rintro ⟨h1, h2⟩
      rw [← orderOf_eq_prime_pow h2 h1]
      exact IsPrimitiveRoot.orderOf _
  have hQone : ζ ^ (PD.p ^ r) = 1 → constantCoeff (W.lev i ζ W.Q) ≠ 0 := by
    intro h
    rw [hQ0, h]
    simp [hp.ne_zero]
  have hX0 : constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (PD.p ^ r) = 1 := by
    rw [hX, hc0, sub_eq_zero]
  have hQiff : constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (PD.p ^ (r + 1)) := by
    have hc := congrArg constantCoeff hXQ
    rw [map_mul, hc0] at hc
    rw [hprim]
    constructor
    · intro h
      rw [h, zero_mul] at hc
      exact ⟨(sub_eq_zero.mp hc.symm), fun h' => hQone h' h⟩
    · rintro ⟨h1, h2⟩
      rw [h1, sub_self] at hc
      exact (mul_eq_zero.mp hc).resolve_right (fun h => h2 (hX0.mp h))
  rw [hr, Nat.add_sub_cancel]
  refine ⟨?_, ?_, ?_, hX0, hQiff, ?_⟩
  · obtain ⟨w, hw, hw'⟩ := simple_zero (U - C ζ) (by simp [hU0]) (by
      have := hc1 1 one_ne_zero
      rw [pow_one, map_sub, coeff_one] at this
      rw [map_sub, coeff_C]
      simpa using this)
    refine ⟨w, hw, ?_⟩
    rw [map_sub, map_one]
    linear_combination hE + hw'
  · intro h
    refine ⟨simple_zero _ (hX0.mpr h) (by rw [hX]; exact hc1 _ (pow_ne_zero _ hp.ne_zero)), ?_⟩
    rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
    exact hQone h
  · intro h
    have hXu : IsUnit (W.lev i ζ W.X) := by
      rw [isUnit_iff_constantCoeff, isUnit_iff_ne_zero]
      exact fun h' => (hprim.mp h).2 (hX0.mp h')
    refine ⟨?_, hXu⟩
    obtain ⟨w, hw, hw'⟩ := simple_zero (U ^ (PD.p ^ (r + 1)) - 1)
      (by rw [hc0, h.pow_eq_one, sub_self]) (hc1 _ (pow_ne_zero _ hp.ne_zero))
    obtain ⟨u, hu⟩ := hXu
    refine ⟨w * ↑u⁻¹, hw.mul (Units.isUnit _), ?_⟩
    rw [← mul_assoc, ← hw', ← hXQ, ← hu, Units.mul_inv_cancel_right]
  · intro h
    apply hc1 (PD.p ^ (r + 1)) (pow_ne_zero _ hp.ne_zero)
    rw [← hXQ, h, zero_mul, map_zero]

theorem exists_nonunit {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (ζ : ↥LL.1)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) :
    ∃ x : ↥(OL LL), ¬ IsUnit x ∧ (x : ↥LL.1) = ζ - 1 := by
  have hp : l.Prime := Fact.out
  obtain ⟨j, hj⟩ := hζ
  have hint : IsIntegral ℤ_[l] ζ := (hj.isIntegral (pow_pos hp.pos j)).tower_top
  let x : ↥(OL LL) := ⟨ζ - 1, (OL LL).sub_mem hint (OL LL).one_mem⟩
  refine ⟨x, fun hx => ?_, rfl⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp x 1 j
  have h1 : (x + 1) ^ (l ^ j) = 1 := by
    apply Subtype.ext
    simp [x, hj.pow_eq_one]
  have hl : IsUnit ((l : ℕ) : ↥(OL LL)) := by
    have h2 : IsUnit (x ^ (l ^ j)) := hx.pow _
    refine isUnit_of_dvd_unit ?_ h2
    rw [h1, one_pow] at hr
    exact ⟨-(x * r), by linear_combination -hr⟩
  obtain ⟨y, hy⟩ := hl.exists_right_inv
  have hy' : (l : ↥LL.1) * (y : ↥LL.1) = 1 := by
    have := congrArg (fun z : ↥(OL LL) => (z : ↥LL.1)) hy
    simpa using this
  have hv := congrArg (P.v LL) hy'
  rw [AddValuation.map_mul, P.v_l, AddValuation.map_one] at hv
  have h0 : 0 ≤ P.v LL y := (P.v_O LL y).mpr y.2
  have : (1 : WithTop ℚ) ≤ 1 + P.v LL y := le_add_of_nonneg_right h0
  rw [hv] at this
  exact absurd this (by norm_num)

end LevPt

set_option maxHeartbeats 1000000 in

theorem lev_at_root_of_unity : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (i : Let K) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) → (∃ x : ↥(OL LL), ¬ IsUnit x ∧ (x : ↥LL.1) = ζ - 1 ∧ ∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ letπ = PowerSeries.C (x : ↥LL.1) + PowerSeries.X * w) ∧ W.lev i ζ (letE i) = 1 ∧ (ζ ^ (l ^ (s - 1)) = 1 → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.X = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.Q)) ∧ (IsPrimitiveRoot ζ (l ^ s) → (∃ w : PowerSeries ↥LL.1, IsUnit w ∧ W.lev i ζ W.Q = PowerSeries.X * w) ∧ IsUnit (W.lev i ζ W.X)) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.X) = 0 ↔ ζ ^ (l ^ (s - 1)) = 1) ∧ (PowerSeries.constantCoeff (W.lev i ζ W.Q) = 0 ↔ IsPrimitiveRoot ζ (l ^ s)) ∧ W.lev i ζ W.Q ≠ 0 := by
  intro D HW l _ K s LL h W i ζ hζ
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hs : W.s = s := (HW l).W_s K s LL h
  clear_value W
  haveI : CharZero ↥LL.1 := algebraRat.charZero _
  have hζ' : ∃ j : ℕ, IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ j) := by rw [hp]; exact hζ
  obtain ⟨H1, H2⟩ := LevPt.lev_values W i ζ hζ'
  simp only [hp, hs] at H2
  obtain ⟨x, hx, hx'⟩ := LevPt.exists_nonunit (D.loc l) LL ζ hζ
  refine ⟨⟨x, hx, hx', ?_⟩, LevPt.lev_letE W i ζ, H2⟩
  rw [hx']
  exact H1

end GlobalTheory.NL
end
end

