import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsIrrDistinctMapSurjective
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem absIrrDistinct_of_semilinearEquiv {k L Γ V V' : Type} [Field k] [Field L] [Group Γ]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module L V']
    {σ : k →+* L} {τ : L →+* k} [RingHomInvPair σ τ] [RingHomInvPair τ σ]
    (ρ : Representation k Γ V) (ρ' : Representation L Γ V') (E : V ≃ₛₗ[σ] V')
    (hE : ∀ g v, E (ρ g v) = ρ' g (E v)) (h : AbsIrrDistinct ρ) : AbsIrrDistinct ρ' := by
  obtain ⟨ι, hι, hd, Vs, hs, hint, hne, hspan, hdist⟩ := h
  have hs' : ∀ j, Stable ρ' ((Vs j).map (E : V →ₛₗ[σ] V')) := by
    rintro j g _ ⟨v, hv, rfl⟩
    exact ⟨ρ g v, hs j g v hv, hE g v⟩
  have hcomm : ∀ j g (v : Vs j), E.submoduleMap (Vs j) ((ρ g).restrict (hs j g) v)
      = (ρ' g).restrict (hs' j g) (E.submoduleMap (Vs j) v) := by
    intro j g v
    apply Subtype.ext
    exact hE g v
  refine ⟨ι, hι, hd, fun j => (Vs j).map (E : V →ₛₗ[σ] V'), hs', ?_, ?_, ?_, ?_⟩
  · rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint ⊢
    refine ⟨hint.1.map_orderIso (Submodule.orderIsoMapComap E), ?_⟩
    rw [← Submodule.map_iSup, hint.2, Submodule.map_top, LinearEquiv.range]
  · intro j hj
    exact hne j ((Submodule.orderIsoMapComap E).injective (by simpa using hj))
  · intro j
    have hc : ∀ g, (E.submoduleMap (Vs j)).conj ((ρ g).restrict (hs j g))
        = (ρ' g).restrict (hs' j g) := by
      intro g
      ext1 w
      obtain ⟨v, rfl⟩ := (E.submoduleMap (Vs j)).surjective w
      rw [← hcomm]
      simp [LinearEquiv.conj_apply]
    have h1 := congrArg (Submodule.map ((E.submoduleMap (Vs j)).conj : Module.End k (Vs j) →ₛₗ[σ]
      Module.End L ((Vs j).map (E : V →ₛₗ[σ] V')))) (hspan j)
    rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range, ← Set.range_comp] at h1
    rw [← h1]
    congr 2
    funext g
    exact (hc g).symm
  · intro j j' hjj e he
    refine hdist j j' hjj
      (((E.submoduleMap (Vs j)).trans e).trans (E.submoduleMap (Vs j')).symm) ?_
    intro g v
    apply (E.submoduleMap (Vs j')).injective
    rw [hcomm]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [hcomm, he]

theorem absIrrDistinct_matRep_mapM_of_surjective : ∀ {k Γ : Type} [Field k] [Group Γ] {L : Type} [Field L] (f : k →+* L), Function.Surjective f → ∀ {a : ℕ} (M : Γ →* Matrix (Fin a) (Fin a) k), AbsIrrDistinct (matRep M) → AbsIrrDistinct (matRep (mapM f M)) := by
  intro k Γ _ _ L _ f hf a M h
  let s : k ≃+* L := RingEquiv.ofBijective f ⟨f.injective, hf⟩
  haveI := RingHomInvPair.of_ringEquiv s
  haveI := RingHomInvPair.of_ringEquiv_symm s
  let E : (Fin a → k) ≃ₛₗ[(s : k →+* L)] (Fin a → L) :=
    { toFun := fun v i => s (v i)
      invFun := fun v i => s.symm (v i)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun c v => by ext i; simp
      left_inv := fun v => by ext i; simp
      right_inv := fun v => by ext i; simp }
  refine absIrrDistinct_of_semilinearEquiv _ _ E ?_ h
  intro g v
  ext i
  exact RingHom.map_mulVec f (M g) v i

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentFiniteFreeInvertPrime
section
open PowerSeries GlobalTheory.BK
open scoped NormedField Valued

noncomputable section

namespace GlobalTheory.ZFin

theorem isDomain_isPrincipalIdealRing (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] : IsDomain O ∧ IsPrincipalIdealRing O := by
  have hl : ‖(l : K)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap']
    exact_mod_cast Padic.norm_p_lt_one
  have hl0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  letI : NontriviallyNormedField K :=
    { ‹NormedField K› with
      non_trivial := ⟨(l : K)⁻¹, by
        rw [norm_inv]; exact one_lt_inv₀ (norm_pos_iff.2 hl0) |>.2 hl⟩ }
  haveI : ProperSpace K := FiniteDimensional.proper ℚ_[l] K
  haveI : CompactSpace 𝒪[K] := by
    have h1 : ((𝒪[K] : Set K)) = Metric.closedBall 0 1 := by
      ext x; simp [Valued.integer.mem_iff]
    have h2 : IsCompact ((𝒪[K] : Set K)) := h1 ▸ isCompact_closedBall 0 1
    exact (isCompact_iff_compactSpace (s := (𝒪[K] : Set K))).1 h2
  haveI : IsPrincipalIdealRing 𝒪[K] := Valued.integer.isPrincipalIdealRing_of_compactSpace
  let f : O →+* 𝒪[K] :=
    { toFun := fun x => ⟨algebraMap O K x, Valued.integer.mem_iff.2 ((IsUnitBall.mem_range_iff _).1 ⟨x, rfl⟩)⟩
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hf : Function.Bijective f := by
    refine ⟨fun x y h => IsUnitBall.inj (O := O) (K := K) (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := (IsUnitBall.mem_range_iff (O := O) (y : K)).2 (Valued.integer.mem_iff.1 y.2)
    exact ⟨x, Subtype.ext hx⟩
  let g := RingEquiv.ofBijective f hf
  haveI : IsDomain O := (IsUnitBall.inj (O := O) (K := K)).isDomain (algebraMap O K)
  exact ⟨inferInstance, IsPrincipalIdealRing.of_surjective (g.symm : 𝒪[K] →+* O) g.symm.surjective⟩

theorem exists_eq_add_E_pow_mul (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [NeZero e] (n : ℕ) (f : K⟦X⟧) (hf : f ∈ A O K) :
    ∃ (c : Fin (e * n) → O) (g : K⟦X⟧), g ∈ A O K ∧
      f = ∑ k : Fin (e * n), C (algebraMap O K (c k)) * X ^ (k : ℕ) + E K l e ^ n * g :=
  GlobalTheory.T.weierstrass_division_eisensteinPow_integral O K l e n f hf

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]

variable (K l e a ι) in

def gen (η : ℕ) (p : ZMod a × ι × Fin (e * η)) : Vec K a ι :=
  Pi.single p.1 (Pi.single p.2.1 (Ezpow K l e (-η) * X ^ (p.2.2 : ℕ)))

theorem gen_mem (P : PhiMod O K l e a ι) (η : ℕ) (p : ZMod a × ι × Fin (e * η)) :
    gen K l e a ι η p ∈ P.EM η := by
  rw [mem_divE]
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  simp only [Pi.smul_apply, smul_eq_mul, gen]
  by_cases hτ : τ = p.1
  · subst hτ
    rw [Pi.single_eq_same]
    by_cases hi : i = p.2.1
    · subst hi
      rw [Pi.single_eq_same, ← mul_assoc, E_pow_mul_Ezpow_neg, one_mul]
      exact pow_mem HasU.X_mem _
    · rw [Pi.single_eq_of_ne hi, mul_zero]; exact zero_mem _
  · rw [Pi.single_eq_of_ne hτ]; simp

theorem sum_gen_apply (η : ℕ) (c : ZMod a × ι × Fin (e * η) → O) (τ : ZMod a) (i : ι) :
    (∑ p, c p • gen K l e a ι η p) τ i =
      Ezpow K l e (-η) * ∑ k : Fin (e * η), C (algebraMap O K (c (τ, i, k))) * X ^ (k : ℕ) := by
  simp only [Finset.sum_apply, Pi.smul_apply, gen, Fintype.sum_prod_type, Finset.mul_sum]
  simp only [Pi.single_apply, ite_apply, Pi.zero_apply, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Fintype.sum_eq_single τ (fun x hx => by simp [Ne.symm hx]), Fintype.sum_eq_single i
    (fun x hx => by simp [Ne.symm hx])]
  simp only [if_true]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← algebraMap_smul K⟦X⟧ (c (τ, i, k)), algebraMap_eq_C, smul_eq_mul, mul_left_comm]

theorem finite_quot (P : PhiMod O K l e a ι) (η : ℕ) :
    Module.Finite O ((P.EM η).restrictScalars O ⧸
      (P.M.restrictScalars O).submoduleOf ((P.EM η).restrictScalars O)) := by
  let F : (ZMod a × ι × Fin (e * η) → O) →ₗ[O] (P.EM η).restrictScalars O :=
    LinearMap.codRestrict _ (Fintype.linearCombination O (gen K l e a ι η)) fun c => by
      rw [Fintype.linearCombination_apply]
      exact sum_mem fun p _ => Submodule.smul_mem _ _ (gen_mem P η p)
  refine Module.Finite.of_surjective ((Submodule.mkQ _).comp F) fun q => ?_
  obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hy2 : E K l e ^ η • y ∈ P.M := hy
  have hyA (τ : ZMod a) (i : ι) : E K l e ^ η * y τ i ∈ A O K := by
    have := mem_vecs.1 (mem_tot.1 hy2 τ) i
    simpa using this
  choose c g hg hfg using fun τ i => exists_eq_add_E_pow_mul O K l e η _ (hyA τ i)
  refine ⟨fun p => c p.1 p.2.1 p.2.2, ?_⟩
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  change (∑ p, c p.1 p.2.1 p.2.2 • gen K l e a ι η p) - y ∈ P.M
  refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
  rw [Pi.sub_apply, Pi.sub_apply, sum_gen_apply]
  have hy' : y τ i = Ezpow K l e (-η) * (E K l e ^ η * y τ i) := by
    rw [← mul_assoc, mul_comm (Ezpow K l e (-η)), E_pow_mul_Ezpow_neg, one_mul]
  dsimp only
  rw [hy', hfg τ i, mul_add, sub_add_cancel_left, ← mul_assoc,
    mul_comm (Ezpow K l e (-η)) (E K l e ^ η), E_pow_mul_Ezpow_neg, one_mul]
  exact neg_mem (hg τ i)

variable [TameDescentExponentData K l e a]

theorem finite_Z {η H : ℕ} (D : BKDat O K l e a ι η H) : Module.Finite O D.Z := by
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  obtain ⟨_, _⟩ := isDomain_isPrincipalIdealRing O K l
  haveI := finite_quot D.toPhiMod η
  exact Module.Finite.equiv (D.desc.quotInvEquiv η)

theorem free_Z {η H : ℕ} (D : BKDat O K l e a ι η H) : Module.Free O D.Z := by
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  obtain ⟨_, _⟩ := isDomain_isPrincipalIdealRing O K l
  haveI := finite_Z D
  haveI : NoZeroSMulDivisors O D.Z := ⟨fun {c w} h => by
    have h1 : c • (w : D.Pol) = 0 := congrArg Subtype.val h
    rw [← algebraMap_smul K c] at h1
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact Or.inl (IsUnitBall.inj (O := O) (K := K) (by rw [h2, map_zero]))
    · exact Or.inr (Subtype.ext h2)⟩
  exact Module.free_of_finite_type_torsion_free'

theorem exists_pow_smul_mem_range {η H : ℕ} (D : BKDat O K l e a ι η H) (w : D.Pol) :
    w ∈ D.PolEta η ↔
      ∃ n : ℕ, (l : K) ^ n • w ∈ LinearMap.range (Descent.quotToPol D.toPhiMod η) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ D.Mext (RpiE O K l e) := mem_tot.2 fun τ => mem_vecs.2 fun i => ⟨η, by
      have := mem_vecs.1 (mem_tot.1 hy τ) i
      simpa using this⟩
    obtain ⟨v, hv, hd⟩ := D.exists_sub_hatTot_mem_Mhat η ((D.smul_hatTot_mem_Mhat_iff η hy').2 hy)
    have hv' : v ∈ D.Mext (RpiE O K l e) := mem_tot.2 fun τ => mem_vecs.2 fun i => ⟨η, by
      have := invL_A_le_Rpi l e (mem_vecs.1 (mem_tot.1 hv τ) i)
      simpa using this⟩
    have hcls := (D.hatTot_sub_mem_Mhat_iff hy' hv').1 hd
    have hl (n : ℕ) (f : K⟦X⟧) : (l : K) ^ n • f = ((l : A O K) : K⟦X⟧) ^ n * f := by
      simp [smul_eq_C_mul]
    choose n hn using fun p : ZMod a × ι => mem_tot.1 hv p.1 p.2
    refine ⟨Finset.univ.sup n, Submodule.Quotient.mk ⟨(l : K) ^ Finset.univ.sup n • v, ?_⟩, ?_⟩
    · refine mem_tot.2 fun τ => mem_vecs.2 fun i => ?_
      obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ (τ, i)))
      rw [smul_comm, Pi.smul_apply, Pi.smul_apply, hl, hc, pow_add, mul_assoc]
      exact mul_mem (pow_mem (l : A O K).2 c) (hn (τ, i))
    · change D.cls ((l : K) ^ Finset.univ.sup n • v) = (l : K) ^ Finset.univ.sup n • D.cls y
      rw [map_smul, hcls]
  · rintro ⟨n, q, hq⟩
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have h1 : (l : K) ^ n • w ∈ D.PolEta η := by
      rw [← hq]
      exact D.cls_mem_PolEta hy
    have h2 := (D.PolEta η).smul_mem ((l : K) ^ n)⁻¹ h1
    rwa [inv_smul_smul₀ (pow_ne_zero n (l_ne_zero (K := K) l))] at h2

theorem mem_Zl_iff {η H : ℕ} (D : BKDat O K l e a ι η H) (w : D.Pol) :
    w ∈ D.Zl ↔ ∃ n : ℕ, (l : K) ^ n • w ∈ D.Z := by
  constructor
  · rintro ⟨hw1, hw2⟩
    obtain ⟨n, q, hq⟩ := (exists_pow_smul_mem_range D w).1 hw1
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨n, D.desc.mem_Z.2 ⟨⟨y, hy, hq⟩, fun g => ?_⟩⟩
    rw [map_smul, hw2 g]
  · rintro ⟨n, hn⟩
    have h2 := D.Zl.smul_mem ((l : K) ^ n)⁻¹ (D.desc.mem_Zl_of_mem_Z hn)
    rwa [inv_smul_smul₀ (pow_ne_zero n (l_ne_zero (K := K) l))] at h2

end GlobalTheory.ZFin

open GlobalTheory.ZFin in

theorem GlobalTheory.ZFin.finiteFree_and_localisation : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ)
    (D : BKDat O K l e a ι η H), GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.FiniteFree D ∧ GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Localisation D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D
  exact ⟨⟨free_Z D, finite_Z D⟩, Descent.quotToPol_injective (P := D.toPhiMod) η,
    fun w => exists_pow_smul_mem_range D w, D.desc.map_invariants_actQuot η, fun w => mem_Zl_iff D w⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilRingEqIntegralAddEisensteinFiltration
section
open PowerSeries GlobalTheory.BK

noncomputable section
namespace GlobalTheory.BK.SDec

open Filter Topology

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

omit [IsUltrametricDist K] in
theorem norm_factorial_eq_one {k : ℕ} (hk : k < l) : ‖(k.factorial : K)‖ = 1 := by
  rw [norm_natCast_eq l, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun h =>
    absurd ((Nat.Prime.dvd_factorial Fact.out).1 h) (not_le.2 hk)

omit [IsUltrametricDist K] in
theorem norm_choose_mul_le (q k : ℕ) :
    ‖((q.choose k : K) * (k.factorial : K) * (-(l : K)) ^ (q - k))‖ ≤ ‖(q.factorial : K)‖ := by
  rcases le_or_gt k q with hkq | hkq
  · have h := congrArg (Nat.cast : ℕ → K) (Nat.choose_mul_factorial_mul_factorial hkq)
    push_cast at h
    rw [← h, norm_mul, norm_mul, norm_pow, norm_neg, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le_norm_factorial l _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · simp [Nat.choose_eq_zero_of_lt hkq]

variable (K) in

def beta (e : ℕ) (c : K) (m k : ℕ) : K :=
  c * (((m / e).choose k : K) * (k.factorial : K) * (-(l : K)) ^ (m / e - k))

theorem norm_beta_le (e : ℕ) (c : K) (m k : ℕ) : ‖beta K l e c m k‖ ≤ ‖c‖ * wS K e m := by
  rw [beta, norm_mul, wS]
  exact mul_le_mul_of_nonneg_left (norm_choose_mul_le l _ _) (norm_nonneg _)

theorem beta_eq_zero {e : ℕ} (c : K) {m k : ℕ} (h : m / e < k) : beta K l e c m k = 0 := by
  simp [beta, Nat.choose_eq_zero_of_lt h]

theorem expand (e : ℕ) (c : K) (m N : ℕ) (hN : m / e < N) :
    C c * X ^ m = ∑ k ∈ Finset.range N, C (beta K l e c m k) * X ^ (m % e) * Ediv K l e k := by
  have hX : (X : K⟦X⟧) ^ m = X ^ (m % e) * (E K l e + C (-(l : K))) ^ (m / e) := by
    rw [E, map_neg, map_natCast, add_neg_cancel_right, ← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [← Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt hN)) (fun k _ hk => by
      rw [beta_eq_zero l c (by simpa using hk), map_zero, zero_mul, zero_mul])]
  rw [hX, add_pow, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : (k.factorial : K) ≠ 0 := natCast_ne_zero' l k.factorial_ne_zero
  have h1 : C (beta K l e c m k) * C ((k.factorial : K)⁻¹) =
      C (c * (((m / e).choose k : K) * (-(l : K)) ^ (m / e - k))) := by
    rw [← map_mul]; congr 1; rw [beta]; field_simp
  calc _ = C (c * (((m / e).choose k : K) * (-(l : K)) ^ (m / e - k))) * X ^ (m % e) *
        E K l e ^ k := by simp only [map_mul, map_pow, map_natCast, map_neg]; ring
    _ = _ := by rw [Ediv, ← h1]; ring

end GlobalTheory.BK.SDec

namespace GlobalTheory.BK.SDec

open Filter Topology

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

omit [Fact l.Prime] [NormedAlgebra ℚ_[l] K] in
theorem C_mem_A {c : K} (hc : ‖c‖ ≤ 1) : C c ∈ A O K := fun n => by
  rw [coeff_C]; split_ifs <;> simp [hc]

theorem term_mem_A (e : ℕ) {c : K} (hc : ‖c‖ ≤ 1) (r : ℕ) {k : ℕ} (hk : k < l) :
    C c * X ^ r * Ediv K l e k ∈ A O K := by
  rw [Ediv]
  refine (A O K).mul_mem ((A O K).mul_mem (C_mem_A hc) ((A O K).pow_mem HasU.X_mem r))
    ((A O K).mul_mem (C_mem_A ?_) ((A O K).pow_mem (E_mem l e (A O K)) k))
  rw [norm_inv, norm_factorial_eq_one l hk, inv_one]

theorem CX_mem_S {e : ℕ} {c : K} (hc : ‖c‖ ≤ 1) {r : ℕ} (hr : r < e) :
    C c * X ^ r ∈ S O K e := by
  rw [← monomial_eq_C_mul_X_pow]
  refine monomial_mem_S ?_
  rw [wS, Nat.div_eq_of_lt hr, Nat.factorial_zero, Nat.cast_one, norm_one, mul_one]
  exact hc

theorem sum_range_mul {M : Type*} [AddCommMonoid M] (F : ℕ → M) (Q e : ℕ) :
    ∑ m ∈ Finset.range (Q * e), F m = ∑ q ∈ Finset.range Q, ∑ r ∈ Finset.range e, F (q * e + r) := by
  induction Q with
  | zero => simp
  | succ Q ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem low_eq (e j Q : ℕ) (b : ℕ → ℕ → K) :
    ∑ m ∈ Finset.range (Q * e), ∑ k ∈ Finset.range j, C (b m k) * X ^ (m % e) * Ediv K l e k =
      ∑ k ∈ Finset.range j, ∑ r ∈ Finset.range e,
        C (∑ q ∈ Finset.range Q, b (q * e + r) k) * X ^ r * Ediv K l e k := by
  rw [sum_range_mul]
  simp_rw [map_sum, Finset.sum_mul]
  calc _ = ∑ q ∈ Finset.range Q, ∑ r ∈ Finset.range e, ∑ k ∈ Finset.range j,
        C (b (q * e + r) k) * X ^ r * Ediv K l e k :=
      Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl
        fun k _ => by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Finset.mem_range.1 hr)]
    _ = ∑ r ∈ Finset.range e, ∑ q ∈ Finset.range Q, ∑ k ∈ Finset.range j,
        C (b (q * e + r) k) * X ^ r * Ediv K l e k := Finset.sum_comm
    _ = ∑ r ∈ Finset.range e, ∑ k ∈ Finset.range j, ∑ q ∈ Finset.range Q,
        C (b (q * e + r) k) * X ^ r * Ediv K l e k :=
      Finset.sum_congr rfl fun r _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem coeff_head (f : K⟦X⟧) (M m : ℕ) :
    coeff m (∑ m' ∈ Finset.range M, C (coeff m' f) * X ^ m') = if m < M then coeff m f else 0 := by
  simp_rw [map_sum, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

end GlobalTheory.BK.SDec

namespace GlobalTheory.BK.SDec

open Filter Topology

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]

theorem tail_mem {e : ℕ} {f : K⟦X⟧} (hf : f ∈ S O K e) (n M : ℕ)
    (hM : ∀ m, M ≤ m → ‖coeff m f‖ * wS K e m ≤ ‖(l : K)‖ ^ n) :
    C ((l : K) ^ n)⁻¹ * (f - ∑ m ∈ Finset.range M, C (coeff m f) * X ^ m) ∈ S O K e := by
  have hl : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
  have hc : ∀ m, coeff m (C ((l : K) ^ n)⁻¹ * (f - ∑ m ∈ Finset.range M, C (coeff m f) * X ^ m)) =
      ((l : K) ^ n)⁻¹ * (if m < M then 0 else coeff m f) := fun m => by
    rw [coeff_C_mul, map_sub, coeff_head]; split_ifs <;> simp
  have key : ∀ m, ‖coeff m (C ((l : K) ^ n)⁻¹ * (f - ∑ m ∈ Finset.range M, C (coeff m f) * X ^ m))‖ *
      wS K e m ≤ (‖(l : K)‖ ^ n)⁻¹ * (‖coeff m f‖ * wS K e m) := fun m => by
    rw [hc, norm_mul, norm_inv, norm_pow, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hl.le)
    split_ifs
    · simpa using mul_nonneg (norm_nonneg _) (wS_nonneg e m)
    · exact le_rfl
  refine ⟨fun m => ?_, squeeze_zero (fun m => mul_nonneg (norm_nonneg _) (wS_nonneg e m)) key
    (by simpa using hf.2.const_mul (‖(l : K)‖ ^ n)⁻¹)⟩
  by_cases h : m < M
  · rw [hc, if_pos h]; simp
  · refine (key m).trans ?_
    rw [inv_mul_le_iff₀ hl, mul_one]
    exact hM m (not_lt.1 h)

theorem S_eq_A_add_Fil : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (j : ℕ), j < l → ∀ f ∈ S O K e,
    ∃ g ∈ A O K, ∃ φ ∈ Fil O K l e j, f = g + (φ : K⟦X⟧) := by
  intro O K _ _ _ _ _ _ l e _ _ _ j hj f hf
  have hb : ∀ m k, ‖beta K l e (coeff m f) m k‖ ≤ ‖coeff m f‖ * wS K e m := fun m k =>
    norm_beta_le l e _ m k
  have hT : Tendsto (fun m => ‖coeff m f‖ * wS K e m) atTop (𝓝 0) := hf.2
  have hle : ∀ q r, q ≤ q * e + r := fun q r =>
    (Nat.le_mul_of_pos_right q (NeZero.pos e)).trans (Nat.le_add_right _ _)
  have hs : ∀ r k, Summable fun q => beta K l e (coeff (q * e + r) f) (q * e + r) k := by
    intro r k
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [Nat.cofinite_eq_atTop]
    exact squeeze_zero_norm (fun q => hb _ _)
      (hT.comp (tendsto_atTop_mono (fun q => hle q r) tendsto_id))
  set γ : ℕ → ℕ → K := fun r k => ∑' q, beta K l e (coeff (q * e + r) f) (q * e + r) k with hγ
  have hγ1 : ∀ r k, ‖γ r k‖ ≤ 1 := fun r k =>
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun q => (hb _ _).trans (hf.1 _)
  set g : K⟦X⟧ := ∑ k ∈ Finset.range j, ∑ r ∈ Finset.range e, C (γ r k) * X ^ r * Ediv K l e k
    with hgdef
  have hg : g ∈ A O K := Subalgebra.sum_mem _ fun k hk => Subalgebra.sum_mem _ fun r _ =>
    term_mem_A l e (hγ1 r k) r ((Finset.mem_range.1 hk).trans hj)
  have hφS : f - g ∈ S O K e := Subalgebra.sub_mem _ hf (A_le_S l e hg)
  refine ⟨g, hg, ⟨f - g, hφS⟩, ?_, by simp⟩
  rw [mem_Fil]
  intro n
  have hpos : 0 < ‖(l : K)‖ ^ n := pow_pos (norm_pos_iff.2 (l_ne_zero l)) n
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 (hT.eventually (ge_mem_nhds hpos))
  have hQ' : ∀ m, Q * e ≤ m → ‖coeff m f‖ * wS K e m ≤ ‖(l : K)‖ ^ n := fun m hm =>
    hQ m ((Nat.le_mul_of_pos_right Q (NeZero.pos e)).trans hm)
  set P : K⟦X⟧ := ∑ m ∈ Finset.range (Q * e), C (coeff m f) * X ^ m with hPdef
  set T : ℕ → ℕ → K⟦X⟧ := fun m k => C (beta K l e (coeff m f) m k) * X ^ (m % e) * Ediv K l e k
    with hTdef
  have hTS : ∀ m k, C (beta K l e (coeff m f) m k) * X ^ (m % e) ∈ S O K e := fun m k =>
    CX_mem_S ((hb m k).trans (hf.1 m)) (Nat.mod_lt _ (NeZero.pos e))
  set G : S O K e := ∑ m ∈ Finset.range (Q * e), ∑ k ∈ Finset.Ico j (j + m / e + 1),
    (⟨_, hTS m k⟩ : S O K e) * ⟨Ediv K l e k, Ediv_mem_S l e k⟩ with hGdef
  have hG : G ∈ FilPre O K l e j := Ideal.sum_mem _ fun m _ => Ideal.sum_mem _ fun k hk =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, (Finset.mem_Ico.1 hk).1, rfl⟩)
  have hGc : (G : K⟦X⟧) = ∑ m ∈ Finset.range (Q * e), ∑ k ∈ Finset.Ico j (j + m / e + 1), T m k := by
    simp [hGdef, hTdef]
  set Low : K⟦X⟧ := ∑ m ∈ Finset.range (Q * e), ∑ k ∈ Finset.range j, T m k with hLowdef
  have hP : P = Low + G := by
    rw [hGc, hLowdef, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [expand l e _ m (j + m / e + 1) (by omega), Finset.sum_range_add_sum_Ico _ (Nat.le_add_right_of_le (Nat.le_add_right j (m / e)))]
  have hLow : Low = ∑ k ∈ Finset.range j, ∑ r ∈ Finset.range e,
      C (∑ q ∈ Finset.range Q, beta K l e (coeff (q * e + r) f) (q * e + r) k) * X ^ r *
        Ediv K l e k := low_eq l e j Q (fun m k => beta K l e (coeff m f) m k)
  set tl : ℕ → ℕ → K := fun r k => ∑' q, beta K l e (coeff ((q + Q) * e + r) f) ((q + Q) * e + r) k
    with htldef
  have htl : ∀ r k, γ r k - ∑ q ∈ Finset.range Q, beta K l e (coeff (q * e + r) f) (q * e + r) k =
      tl r k := fun r k => by
    simp only [hγ, htldef]
    rw [← (hs r k).sum_add_tsum_nat_add Q, add_sub_cancel_left]
  have htln : ∀ r k, ‖tl r k‖ ≤ ‖(l : K)‖ ^ n := fun r k =>
    IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hpos.le fun q => (hb _ _).trans
      (hQ' _ (Nat.le_add_right_of_le (Nat.mul_le_mul_right e (Nat.le_add_left Q q))))
  have hgL : g - Low = ∑ k ∈ Finset.range j, ∑ r ∈ Finset.range e, C (tl r k) * X ^ r * Ediv K l e k := by
    rw [hgdef, hLow, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← htl, map_sub]; ring
  set h0 : K⟦X⟧ := C ((l : K) ^ n)⁻¹ * ((f - P) - (g - Low)) with hh0
  have hh : h0 ∈ S O K e := by
    have : h0 = C ((l : K) ^ n)⁻¹ * (f - P) - ∑ k ∈ Finset.range j, ∑ r ∈ Finset.range e,
        C (((l : K) ^ n)⁻¹ * tl r k) * X ^ r * Ediv K l e k := by
      rw [hh0, hgL, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_mul]; ring
    rw [this]
    refine Subalgebra.sub_mem _ (tail_mem l hf n (Q * e) hQ') (Subalgebra.sum_mem _ fun k _ =>
      Subalgebra.sum_mem _ fun r hr => (S O K e).mul_mem (CX_mem_S ?_ (Finset.mem_range.1 hr))
        (Ediv_mem_S l e k))
    rw [norm_mul, norm_inv, norm_pow, inv_mul_le_iff₀ hpos, mul_one]
    exact htln r k
  refine ⟨G, hG, ⟨h0, hh⟩, Subtype.ext ?_⟩
  have hlC : (l : K⟦X⟧) ^ n * C ((l : K) ^ n)⁻¹ = 1 := by
    rw [← map_natCast C, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ (l_ne_zero l)),
      map_one]
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow, SubringClass.coe_natCast]
  rw [hh0, ← mul_assoc, hlC, one_mul]
  linear_combination hP

end GlobalTheory.BK.SDec
end
end

