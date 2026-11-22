import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0356
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0311
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0357
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixOfSaturated
section
open GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.StableLattice

theorem exists_matrix_of_saturated {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {n : ℕ} (L : Submodule O (Fin n → O))
    (hL : ∀ (c : O) (v : Fin n → O), c ≠ 0 → c • v ∈ L → v ∈ L) :
    ∃ (m : ℕ) (B : Matrix (Fin n) (Fin m) O) (P : Matrix (Fin m) (Fin n) O),
      P * B = 1 ∧ ∀ v, v ∈ L ↔ B.mulVec (P.mulVec v) = v := by
  have : Module.IsTorsionFree O ((Fin n → O) ⧸ L) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro c x hx
    obtain ⟨v, rfl⟩ := L.mkQ_surjective x
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hL c v hc hx
  obtain ⟨s, hs⟩ := Module.projective_lifting_property L.mkQ LinearMap.id L.mkQ_surjective
  have hs' : ∀ x, L.mkQ (s x) = x := fun x => LinearMap.congr_fun hs x
  let p : (Fin n → O) →ₗ[O] L := LinearMap.codRestrict L (LinearMap.id - s ∘ₗ L.mkQ) (by
    intro v
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hs',
      sub_self])
  have hp : ∀ x : L, p x = x := by
    intro x
    apply Subtype.ext
    have : L.mkQ (x : Fin n → O) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact x.2
    simp only [p, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.comp_apply, this, map_zero, sub_zero]
  let e := (Module.finBasis O L).equivFun
  refine ⟨Module.finrank O L, LinearMap.toMatrix' (L.subtype ∘ₗ e.symm.toLinearMap),
    LinearMap.toMatrix' (e.toLinearMap ∘ₗ p), ?_, fun v => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    apply LinearMap.ext
    intro u
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, hp, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.id_apply]
  · rw [← Matrix.toLin'_apply, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix',
      Matrix.toLin'_toMatrix']
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    constructor
    · intro hv
      exact congrArg Subtype.val (hp ⟨v, hv⟩)
    · intro hv
      rw [← hv]
      exact (p v).2

theorem exists_integral_model (O Γ : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [Group Γ] [TopologicalSpace Γ] (n a : ℕ)
    (r : Γ →* GL (Fin n) O) (hr : LatticeContinuous r)
    (W : Submodule (FractionRing O) (Fin n → FractionRing O))
    (hW : ∀ g, ∀ v ∈ W, fracRep r g v ∈ W) (ha : Module.finrank (FractionRing O) W = a) :
    ∃ (ρ : Γ →* GL (Fin a) O)
      (k : (Fin a → FractionRing O) →ₗ[FractionRing O] (Fin n → FractionRing O)),
      LatticeContinuous ρ ∧ Function.Injective k ∧ LinearMap.range k = W ∧
        ∀ g v, fracRep r g (k v) = k (fracRep ρ g v) := by
  set φ := algebraMap O (FractionRing O) with hφ
  have hφi : Function.Injective φ := IsFractionRing.injective O (FractionRing O)
  let c : (Fin n → O) →ₗ[O] (Fin n → FractionRing O) :=
    (Algebra.linearMap O (FractionRing O)).compLeft (Fin n)
  have hc : ∀ v, c v = φ ∘ v := fun v => rfl
  let L : Submodule O (Fin n → O) := (W.restrictScalars O).comap c
  have hLm : ∀ v, v ∈ L ↔ φ ∘ v ∈ W := fun v => Iff.rfl
  have hsm : ∀ (x : O) (v : Fin n → O), φ ∘ (x • v) = φ x • (φ ∘ v) := by
    intro x v; funext i; simp
  obtain ⟨m, B, P, hPB, hL⟩ := exists_matrix_of_saturated L (by
    intro x v hx hv
    rw [hLm, hsm] at hv
    rw [hLm]
    exact (W.smul_mem_iff (by simpa using (map_ne_zero_iff φ hφi).2 hx)).1 hv)
  have hfr : ∀ {b : ℕ} (σ : Γ →* GL (Fin b) O) g v, fracRep σ g v =
      (((σ g : GL (Fin b) O) : Matrix (Fin b) (Fin b) O).map φ).mulVec v := fun σ g v => rfl
  have hmv : ∀ {p q : ℕ} (A : Matrix (Fin p) (Fin q) O) (v : Fin q → O),
      φ ∘ A.mulVec v = (A.map φ).mulVec (φ ∘ v) := by
    intro p q A v; funext i; exact RingHom.map_mulVec φ A v i
  have hBL : ∀ u, B.mulVec u ∈ L := by
    intro u
    rw [hL, Matrix.mulVec_mulVec u P B, hPB, Matrix.one_mulVec]
  have hst : ∀ g, B * (P * (r g : Matrix (Fin n) (Fin n) O) * B) =
      (r g : Matrix (Fin n) (Fin n) O) * B := by
    intro g
    apply Matrix.ext_of_mulVec_single
    intro j
    have h1 : (r g : Matrix (Fin n) (Fin n) O).mulVec (B.mulVec (Pi.single j 1)) ∈ L := by
      rw [hLm, hmv, ← hfr]
      exact hW g _ ((hLm _).1 (hBL _))
    have h2 := (hL _).1 h1
    simp only [← Matrix.mulVec_mulVec]
    exact h2
  let k : (Fin m → FractionRing O) →ₗ[FractionRing O] (Fin n → FractionRing O) :=
    (B.map φ).mulVecLin
  have hk : ∀ v, k v = (B.map φ).mulVec v := fun v => rfl
  have hki : Function.Injective k := by
    apply Function.LeftInverse.injective (g := (P.map φ).mulVec)
    intro v
    rw [hk, Matrix.mulVec_mulVec, ← Matrix.map_mul, hPB, Matrix.map_one _ (map_zero φ) (map_one φ),
      Matrix.one_mulVec]
  have hkr : LinearMap.range k = W := by
    apply le_antisymm
    · rw [Matrix.range_mulVecLin, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have := (hLm _).1 (hBL (Pi.single j 1))
      rw [Matrix.mulVec_single_one] at this
      exact this
    · intro w hw
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
        (nonZeroDivisors O) (S := FractionRing O) w
      choose v hv using hd
      have hd0 : φ (d : O) ≠ 0 := (map_ne_zero_iff φ hφi).2 (nonZeroDivisors.coe_ne_zero d)
      have hvw : φ ∘ v = φ (d : O) • w := by
        funext i
        simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
        rw [hφ, hv i, Algebra.smul_def]
      have hvL : v ∈ L := by rw [hLm, hvw]; exact W.smul_mem _ hw
      rw [← (LinearMap.range k).smul_mem_iff hd0, ← hvw, ← (hL v).1 hvL, hmv]
      exact ⟨_, hk _⟩
  obtain rfl : m = a := by
    rw [← ha, ← hkr, LinearMap.finrank_range_of_inj hki, Module.finrank_fin_fun]
  let ρ₀ : Γ →* Matrix (Fin m) (Fin m) O :=
    { toFun := fun g => P * (r g : Matrix (Fin n) (Fin n) O) * B
      map_one' := by rw [map_one, Units.val_one, Matrix.mul_one, hPB]
      map_mul' := by
        intro g h
        rw [Matrix.mul_assoc (P * _) B, hst, map_mul, Units.val_mul]
        simp only [Matrix.mul_assoc] }
  refine ⟨ρ₀.toHomUnits, k, ?_, hki, hkr, fun g v => ?_⟩
  · exact (continuous_const.matrix_mul hr).matrix_mul continuous_const
  · rw [hfr, hfr, hk, hk, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul,
      ← Matrix.map_mul, ← hst g]
    rfl

end GlobalTheory.StableLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulSubPrimePowDvdEPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.BK

theorem exists_mul_sub_pow_dvd_of_dvd_sub : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (M m : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X → ∃ (N : ℕ) (r : bk.S), bk.E ^ m ∣ q * r - (l : bk.S) ^ N := by
  intro l _ K bk M m q hq
  obtain ⟨w, hw⟩ := bk.coeff_zero
  obtain ⟨t, ht⟩ := hq
  set P : bk.S := ((bk.Ep.divX : Polynomial (Wq l bk.a)) : (Wq l bk.a)⟦X⟧) with hP
  have hE : bk.E = X * P + (l : bk.S) * C (w : Wq l bk.a) := by
    have h := Polynomial.X_mul_divX_add bk.Ep
    have h2 := congrArg (fun p : Polynomial (Wq l bk.a) => (p : (Wq l bk.a)⟦X⟧)) h
    simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C, hw, map_mul,
      map_natCast] at h2
    change (bk.Ep : (Wq l bk.a)⟦X⟧) = _
    rw [← h2, hP]
    congr 2
    rw [← map_natCast (Polynomial.C (R := Wq l bk.a)), Polynomial.coe_C, map_natCast]
  have hu : C (w : Wq l bk.a) * C ((w⁻¹ : (Wq l bk.a)ˣ) : Wq l bk.a) = (1 : bk.S) := by
    rw [← map_mul, Units.mul_inv, map_one]
  set c' : bk.S := C ((w⁻¹ : (Wq l bk.a)ˣ) : Wq l bk.a)
  set a : bk.S := (l : bk.S) ^ (M + 1)
  set h₁ : bk.S := -((l : bk.S) ^ M + t * P) * c'
  set b : bk.S := bk.E * h₁
  have hqr : q * (-c' * P) = a + b := by
    simp only [a, b, h₁]
    linear_combination (-c' * P) * ht + (c' * (l : bk.S) ^ M) * hE + (l : bk.S) ^ (M + 1) * hu
  have key := geom_sum₂_mul a (-b) m
  rw [sub_neg_eq_add] at key
  refine ⟨(M + 1) * m, (-c' * P) * ∑ i ∈ Finset.range m, a ^ i * (-b) ^ (m - 1 - i), -((-h₁) ^ m), ?_⟩
  rw [pow_mul, ← mul_assoc, hqr, mul_comm (a + b), key]
  simp only [b]
  rw [neg_pow, mul_pow, neg_pow h₁]
  ring

end GlobalTheory.BSP.BK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOfPowLeOfPowLeSameAdicTopologyStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_of_pow_le_of_pow_le_same_adicTopology : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι) (I' : Ideal S) (n m : ℕ), IsHausdorff I S → 0 < n → 0 < m → I ^ n ≤ I' → I' ^ m ≤ I → ∃ TB' : TopBasis s I' ι, TB'.b = TB.b ∧ TB'.c = TB.c := by
  first | exact @GlobalTheory.BSP.TopBasis.exists_of_pow_le_of_pow_le | exact GlobalTheory.BSP.TopBasis.exists_of_pow_le_of_pow_le | (intros; apply GlobalTheory.BSP.TopBasis.exists_of_pow_le_of_pow_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOneAddPrimePowMulNotRootOfUnity
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.SmallRootCl

variable {l : ℕ} [Fact l.Prime]

theorem norm_one_add_pow_sub_one_le (x : ℂ_[l]) (hx : ‖x‖ ≤ 1) (m : ℕ) :
    ‖(1 + x) ^ m - 1‖ ≤ ‖x‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ‖1 + x‖ ≤ 1 :=
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hx)
    have e : (1 + x) ^ (m + 1) - 1 = ((1 + x) ^ m - 1) * (1 + x) + x := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    calc ‖(1 + x) ^ m - 1‖ * ‖1 + x‖ ≤ ‖x‖ * 1 :=
          mul_le_mul ih h1 (norm_nonneg _) (norm_nonneg _)
      _ = ‖x‖ := mul_one _

theorem inv_le_norm_prime (q : ℕ) (hq : q.Prime) : (l : ℝ)⁻¹ ≤ ‖(q : ℂ_[l])‖ := by
  have hl : l.Prime := Fact.out
  have h := PadicComplex.norm_extends' l (q : ℚ_[l])
  rw [map_natCast, PadicComplex.coe_natCast] at h
  rw [h]
  by_cases hql : q = l
  · subst hql; rw [Padic.norm_p]
  · have hc : Nat.Coprime l q := (Nat.coprime_primes hl hq).2 (Ne.symm hql)
    rw [(Padic.norm_natCast_eq_one_iff).2 hc]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_lt.le)

theorem not_root (x : ℂ_[l]) (hx0 : x ≠ 0) (hx : ‖x‖ < (l : ℝ)⁻¹) (i : ℕ) (hi : 1 ≤ i) :
    (1 + x) ^ i ≠ 1 := by
  intro hpow
  have hl : l.Prime := Fact.out
  have hx1 : ‖x‖ ≤ 1 := hx.le.trans (inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_lt.le))
  set ζ := 1 + x with hζ
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨i, by omega, hpow⟩
  set d := orderOf ζ with hd
  have hdpos : 0 < d := hfin.orderOf_pos
  have hd1 : d ≠ 1 := by
    intro h
    rw [hd, orderOf_eq_one_iff, hζ] at h
    exact hx0 (by linear_combination h)
  set q := d.minFac with hqdef
  have hq : q.Prime := Nat.minFac_prime hd1
  have hqd : q ∣ d := Nat.minFac_dvd d
  set η := ζ ^ (d / q) with hη
  have hηq : η ^ q = 1 := by
    rw [hη, ← pow_mul, Nat.div_mul_cancel hqd, hd]; exact pow_orderOf_eq_one ζ
  have hη1 : η ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf
    · exact (Nat.div_pos (Nat.le_of_dvd hdpos hqd) hq.pos).ne'
    · exact Nat.div_lt_self hdpos hq.one_lt
  have hsum : ∑ j ∈ Finset.range q, η ^ j = 0 := by
    have h := geom_sum_mul η q
    rw [hηq, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hη1)
  have hsmall : ∀ j, ‖η ^ j - 1‖ ≤ ‖x‖ := fun j => by
    rw [hη, ← pow_mul]; exact norm_one_add_pow_sub_one_le x hx1 _
  have hqeq : (q : ℂ_[l]) = -∑ j ∈ Finset.range q, (η ^ j - 1) := by
    rw [Finset.sum_sub_distrib, hsum]; simp
  have hle : ‖(q : ℂ_[l])‖ ≤ ‖x‖ := by
    rw [hqeq, norm_neg]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => hsmall j
  have := inv_le_norm_prime (l := l) q hq
  linarith

theorem exists_one_add_pow_mul_not_root : ∀ (l : ℕ) [Fact l.Prime] (a : ℂ_[l]), a ≠ 0 → ∃ k : ℕ, 1 + (l : ℂ_[l]) ^ k * a ≠ 0 ∧ ∀ i : ℕ, 1 ≤ i → (1 + (l : ℂ_[l]) ^ k * a) ^ i ≠ 1 := by
  intro l _ a ha
  have hl : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hnl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    have h := PadicComplex.norm_extends' l (l : ℚ_[l])
    rw [Padic.norm_p, map_natCast, PadicComplex.coe_natCast] at h
    exact h
  have ha0 : 0 < ‖a‖ := norm_pos_iff.2 ha
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos (inv_pos.2 hl0) ha0)
    (inv_lt_one_of_one_lt₀ hl1)
  set x := (l : ℂ_[l]) ^ k * a with hxdef
  have hxn : ‖x‖ < (l : ℝ)⁻¹ := by
    rw [hxdef, norm_mul, norm_pow, hnl]
    exact (lt_div_iff₀ ha0).1 hk
  have hl0' : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hx0 : x ≠ 0 := mul_ne_zero (pow_ne_zero _ hl0') ha
  refine ⟨k, ?_, fun i hi => not_root x hx0 hxn i hi⟩
  intro h
  have : x = -1 := by linear_combination h
  have h1 : ‖x‖ = 1 := by rw [this, norm_neg, norm_one]
  have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  linarith

end GlobalTheory.SmallRootCl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupTwoCocycles
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CocycleKernel

section General

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {rho : Representation R Γ M} (x : Z1 rho) {L : Subgroup Γ}

theorem cocycle_one : x.1 1 = 0 := by
  have h := x.2.2 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  exact left_eq_add.1 h

theorem cocycle_conj (hL : ∀ g ∈ L, ∀ m, rho g m = m) (k : Γ) {g : Γ} (hg : g ∈ L) :
    x.1 (k * g * k⁻¹) = rho k (x.1 g) := by
  have h := x.2.2 k k⁻¹
  rw [mul_inv_cancel, cocycle_one] at h
  rw [x.2.2, x.2.2, map_mul, Module.End.mul_apply, hL g hg, add_right_comm, ← h, zero_add]

def zeros (L : Subgroup Γ) : Subgroup Γ where
  carrier := {g | g ∈ L ∧ x.1 g = 0}
  one_mem' := ⟨L.one_mem, cocycle_one x⟩
  mul_mem' := fun {a b} ha hb => ⟨L.mul_mem ha.1 hb.1, by rw [x.2.2, ha.2, hb.2, map_zero, add_zero]⟩
  inv_mem' := fun {a} ha => ⟨L.inv_mem ha.1, by
    have h := x.2.2 a⁻¹ a
    rwa [inv_mul_cancel, cocycle_one, ha.2, map_zero, add_zero, eq_comm] at h⟩

theorem zeros_normal (hN : L.Normal) (hL : ∀ g ∈ L, ∀ m, rho g m = m) : (zeros x L).Normal :=
  ⟨fun g hg k => ⟨hN.conj_mem g hg.1 k, by rw [cocycle_conj x hL k hg.1, hg.2, map_zero]⟩⟩

theorem isOpen_zeros [DiscreteTopology M] (hO : IsOpen (L : Set Γ)) : IsOpen (zeros x L : Set Γ) :=
  hO.inter ((isOpen_discrete ({0} : Set M)).preimage x.2.1)

theorem cocycle_eq (hL : ∀ g ∈ L, ∀ m, rho g m = m) {h σ g : Γ} (hh : h ∈ L)
    (hu : g * σ * g⁻¹ * h⁻¹ ∈ zeros x L) : x.1 σ = rho g⁻¹ (x.1 h) := by
  have e : σ = g⁻¹ * (g * σ * g⁻¹ * h⁻¹ * h) * g⁻¹⁻¹ := by group
  rw [e, cocycle_conj x hL _ (L.mul_mem hu.1 hh), x.2.2, hu.2, hL _ hu.1, zero_add]

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw) (s : X.Sig i)

theorem dot_repOn {A : Type} [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ)
    {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ) (k : GE N) (a b : Fin D.R.r → A) :
    repOn (Tgl i s) κ A k a ⬝ᵥ repOn ρ κ⁻¹ A k b =
      algebraMap (X.O0 i) A ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) * a ⬝ᵥ b := by
  have e : (Tmat i s k).transpose * Tdual i s k = ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ (X.O0 i)) := by
    rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, ← Tgl_coe, ← Matrix.coe_units_inv, Units.inv_mul,
      Matrix.transpose_one]
  have e2 : ((Tmat i s k).map (algebraMap (X.O0 i) A)).transpose * (Tdual i s k).map (algebraMap (X.O0 i) A) =
      algebraMap (X.O0 i) A ((eps0 X i k : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix _ _ A) := by
    rw [← Matrix.transpose_map, ← Matrix.map_mul, e]
    ext a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  change ((κ k : A) • ((Tgl i s k : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A)).mulVec a) ⬝ᵥ
    ((((κ k)⁻¹ : Aˣ) : A) • ((ρ k : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A)).mulVec b) = _
  rw [hρ k, Tgl_coe, smul_dotProduct, dotProduct_smul, smul_smul, Units.mul_inv, one_smul, ← Matrix.vecMul_transpose,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, e2, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    smul_eq_mul]

theorem exists_open_normal : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), ∀ h ∈ L, bform (X := X) x.1 y.1 h ≠ 0 → ∃ U : Subgroup (GE N), IsOpen (U : Set (GE N)) ∧ U.Normal ∧ U ≤ L ∧ (∀ g ∈ L, x.1 g = 0 → x.1 (cConj X g) = 0 → y.1 g = 0 → y.1 (cConj X g) = 0 → g ∈ U) ∧ ∀ σ g : GE N, g * σ * g⁻¹ * h⁻¹ ∈ U → bform (X := X) x.1 y.1 σ ≠ 0 := by
  intro D N X i s hl M L z hM hS A _ _ _ _ κ ρ hK hρ hκ x y h hh hb
  have h1 : ∀ g ∈ L, ∀ m, repOn (Tgl i s) κ A g m = m := fun g hg m => by
    rw [(GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hS A κ ρ hK hρ A g hg).1, hκ g hg, Units.val_one, one_smul]
  have h2 : ∀ g ∈ L, ∀ m, repOn ρ κ⁻¹ A g m = m := fun g hg m => by
    rw [(GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hS A κ⁻¹ ρ hK hρ A g hg).2.1, MonoidHom.inv_apply, hκ g hg, inv_one,
      Units.val_one, one_smul]
  obtain ⟨⟨hO, hN, hc, -⟩, -⟩ := hS
  have hc' : ∀ g ∈ L, cConj X g ∈ L := fun g hg => (hc g _ (cConj_apply X g)).1 hg
  haveI := zeros_normal x hN h1
  haveI := zeros_normal y hN h2
  refine ⟨(zeros x L ⊓ (zeros x L).comap (cConj X)) ⊓ (zeros y L ⊓ (zeros y L).comap (cConj X)),
    ((isOpen_zeros x hO).inter (isOpen_comap_cConj X (isOpen_zeros x hO))).inter
      ((isOpen_zeros y hO).inter (isOpen_comap_cConj X (isOpen_zeros y hO))), inferInstance,
    fun g hg => hg.1.1.1, fun g hg a b c d => ⟨⟨⟨hg, a⟩, hc' g hg, b⟩, ⟨hg, c⟩, hc' g hg, d⟩, ?_⟩
  rintro σ g ⟨⟨a, b⟩, c, d⟩ h0
  have e : cConj X (g * σ * g⁻¹ * h⁻¹) = cConj X g * cConj X σ * (cConj X g)⁻¹ * (cConj X h)⁻¹ := by
    simp only [map_mul, map_inv]
  have b' : cConj X (g * σ * g⁻¹ * h⁻¹) ∈ zeros x L := b
  have d' : cConj X (g * σ * g⁻¹ * h⁻¹) ∈ zeros y L := d
  rw [e] at b' d'
  rw [bform, cocycle_eq x h1 hh a, cocycle_eq y h2 hh c, cocycle_eq x h1 (hc' h hh) b', cocycle_eq y h2 (hc' h hh) d',
    dot_repOn i s κ hρ, dot_repOn i s κ hρ, ← map_inv (cConj X), GlobalTheory.ResConjTriv.auxiliaryCharacter_complexConj_invariant, ← mul_sub] at h0
  exact hb (((Units.isUnit _).map (algebraMap (X.O0 i) A)).mul_right_eq_zero.1 h0)

end GlobalTheory.CocycleKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowInclRSmulMemStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_inclR_smul_mem' : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T), letI := twTop T b; ∀ U ∈ 𝓝 (0 : TW (RW LL) T), ∃ k : ℕ, ∀ z : RA LL, inclR LL ((((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1)) : RA LL) ^ k * z) • y ∈ U := by
  first | exact @GlobalTheory.WeakClosed.exists_pow_inclR_smul_mem | exact GlobalTheory.WeakClosed.exists_pow_inclR_smul_mem | (intros; apply GlobalTheory.WeakClosed.exists_pow_inclR_smul_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowLeSpan
section
open GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual

namespace GlobalTheory.CoeffEmbedding

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem exists_norm_le : ∃ C : ℝ, ∀ b : N.O i, ‖iotaOQ N A i b‖ ≤ C := by

  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ_[N.l i] (N.O i)).FG)
  refine ⟨∑ a ∈ s, ‖iotaOQ N A i a‖, fun b => ?_⟩
  have hb : b ∈ Submodule.span ℤ_[N.l i] (s : Set (N.O i)) := hs ▸ Submodule.mem_top
  obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hb
  rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  have hz : iotaOQ N A i (algebraMap ℤ_[N.l i] (N.O i) (c a)) =
      algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i]) := A.iotaQ_alg i (c a)
  rw [Algebra.smul_def, map_mul, norm_mul, hz]
  have h1 : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i])‖ ≤ 1 := by
    have he : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c a : ℚ_[N.l i])‖ = ‖(c a : ℚ_[N.l i])‖ :=
      PadicAlgCl.norm_extends (p := N.l i) _
    rw [he, ← PadicInt.norm_def]
    exact PadicInt.norm_le_one _
  exact mul_le_of_le_one_left (norm_nonneg _) h1

include A in

theorem exists_pow_le_span : ∃ e : ℕ, IsLocalRing.maximalIdeal (N.O i) ^ e ≤
    Ideal.span {((N.l i : ℕ) : N.O i)} := by

  have hl : ((N.l i : ℕ) : N.O i) ≠ 0 := by
    intro h
    have h' := congrArg (iotaOQ N A i) h
    rw [map_natCast, map_zero] at h'
    exact (Nat.cast_ne_zero.2 (Fact.out : (N.l i).Prime).ne_zero) h'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {((N.l i : ℕ) : N.O i)}) (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  refine ⟨n, ?_⟩
  rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

theorem continuous_iotaOQ : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂)
    (A : NAut N) (i : N.Loc), Continuous (iotaOQ N A i) := by
  intro R H what₂ N A i

  obtain ⟨C, hC⟩ := exists_norm_le N A i
  obtain ⟨e, he⟩ := exists_pow_le_span N A i
  refine continuous_of_continuousAt_zero (iotaOQ N A i) ?_
  rw [ContinuousAt, map_zero, Metric.nhds_basis_ball.tendsto_right_iff]
  intro ε hε
  set q : ℝ := ‖((N.l i : ℕ) : Qbar (N.l i))‖ with hq
  have hq1 : q < 1 := by
    have he : ‖algebraMap ℚ_[N.l i] (Qbar (N.l i)) ((N.l i : ℕ) : ℚ_[N.l i])‖ =
        ‖((N.l i : ℕ) : ℚ_[N.l i])‖ := PadicAlgCl.norm_extends (p := N.l i) _
    rw [map_natCast] at he
    rw [hq, he]
    exact Padic.norm_p_lt_one
  have hq0 : 0 ≤ q := norm_nonneg _
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hC1) hq1
  obtain ⟨hopen, -⟩ := isAdic_iff.mp (N.O_adic i)
  filter_upwards [(hopen (e * k)).mem_nhds (Ideal.zero_mem _)] with x hx
  have hx' : x ∈ Ideal.span {((N.l i : ℕ) : N.O i) ^ k} := by
    rw [← Ideal.span_singleton_pow, pow_mul] at *
    exact Ideal.pow_right_mono he k hx
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx'
  rw [Metric.mem_ball, dist_zero_right, map_mul, map_pow, map_natCast, norm_mul, norm_pow, ← hq]
  calc ‖iotaOQ N A i b‖ * q ^ k ≤ (|C| + 1) * q ^ k :=
        mul_le_mul_of_nonneg_right ((hC b).trans (by linarith [le_abs_self C])) (pow_nonneg hq0 k)
    _ < (|C| + 1) * (ε / (|C| + 1)) := mul_lt_mul_of_pos_left hk hC1
    _ = ε := by field_simp

end GlobalTheory.CoeffEmbedding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWittStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_mul_eq_theta_witt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Om l), x ∈ K.1 → x ∈ MaximalUnramifiedExtension l → ∃ (n : ℕ) (w : Wq l bk.a), ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = ((((l : Om l) ^ n * x : Om l)) : ℂ_[l]) := by
  first | exact @GlobalTheory.UnrWitt.exists_pow_mul_eq_theta | exact GlobalTheory.UnrWitt.exists_pow_mul_eq_theta | (intros; apply GlobalTheory.UnrWitt.exists_pow_mul_eq_theta <;> assumption)
end

