import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0027
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0024

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DeterminantLocal
section
open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

theorem determinant_local : DetLocal := by
  intro K F V ι _ _ _ _ _ _ _ _ _ _ _ _ h X x 𝔞 hfix hstar hne hind hspan hdet 𝔭 b a h𝔭 hJ P hP
  classical
  obtain ⟨hbX, hloc, horth, hdiag, ha0⟩ := hJ
  set S : Submonoid (𝓞 K) :=
    Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} with hSdef
  have hS1 : ∀ s ∈ S, s ∉ P.asIdeal := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨t, ht, rfl⟩ := hs
      intro hmem
      apply ht
      rw [← hP]
      exact hmem
    | one => exact fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    | mul s s' _ _ h1 h2 => exact fun hm => (P.isPrime.mem_or_mem hm).elim h1 h2
  have hS2 : ∀ s ∈ S, star ((s : 𝓞 K) : K) = (s : K) := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      obtain ⟨t, ht, rfl⟩ := hs
      exact (hfix _).2 ⟨(t : F), rfl⟩
    | one => simp
    | mul s s' _ _ h1 h2 =>
      rw [show ((s * s' : 𝓞 K) : K) = (s : K) * (s' : K) from rfl, star_mul', h1, h2]

  have hcard : Fintype.card ι = finrank K X := by rw [← hspan, finrank_span_eq_card hind]
  let σ : ι ≃ Fin (finrank K X) := Fintype.equivFinOfCardEq hcard
  set b' : ι → V := fun k => b (σ k) with hb'def
  have hb'X : ∀ k, b' k ∈ Submodule.span K (Set.range x) := fun k => hspan ▸ hbX (σ k)
  choose C0 hC0 using fun k => (Submodule.mem_span_range_iff_exists_fun K).mp (hb'X k)
  set C : Matrix ι ι K := fun i k => C0 k i with hCdef
  have hC : ∀ k, b' k = ∑ i, C i k • x i := fun k => (hC0 k).symm
  have hgb : gram h b' = C.conjTranspose * gram h x * C := gram_comb h x C b' hC
  have hgdiag : gram h b' = Matrix.diagonal fun k => algebraMap F K ((a (σ k) : 𝓞 F) : F) := by
    ext k l
    by_cases hkl : k = l
    · subst hkl
      simp [gram, hb'def, hdiag]
    · rw [Matrix.diagonal_apply_ne _ hkl]
      exact horth _ _ (σ.injective.ne hkl)
  have hdetb : algebraMap F K (∏ j, ((a j : 𝓞 F) : F)) = star C.det * C.det * (gram h x).det := by
    have e1 := congrArg Matrix.det hgb
    rw [hgdiag, Matrix.det_diagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at e1
    rw [map_prod, mul_right_comm, ← e1]
    exact (Equiv.prod_comp σ (fun j => algebraMap F K ((a j : 𝓞 F) : F))).symm
  have ha0' : algebraMap F K (∏ j, ((a j : 𝓞 F) : F)) ≠ 0 := by
    rw [map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    rw [map_ne_zero_iff _ (algebraMap F K).injective]
    exact_mod_cast ha0 j
  have hCdet : C.det ≠ 0 := by
    intro h0; apply ha0'; rw [hdetb, h0]; simp
  have hsCdet : star C.det ≠ 0 := by
    intro h0; apply hCdet; rw [← star_star C.det, h0, star_zero]
  have hlocmem : ∀ v, v ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) ↔ ∃ s ∈ S, s • v ∈ pbLat x 𝔞 := by
    intro v; rw [hloc]; exact Iff.rfl
  have hlocmem2 : ∀ v, v ∈ locF 𝔭 (pbLat x 𝔞) ↔ ∃ s ∈ S, s • v ∈ Submodule.span (𝓞 K) (Set.range b) := by
    intro v; rw [← hloc]; exact Iff.rfl
  have hcoeS : ∀ o : 𝓞 K, ∀ v : V, ((o : K)) • v = o • v := fun o v => algebraMap_smul K o v

  have ht0 : ∀ k, ∃ t ∈ S, t • b' k ∈ pbLat x 𝔞 := fun k =>
    (hlocmem (b' k)).mp ⟨1, S.one_mem, by rw [one_smul]; exact Submodule.subset_span ⟨σ k, rfl⟩⟩
  choose t htS htL using ht0
  have hrow : ∀ i k, C i k * (t k : K) ∈ 𝔞 i := by
    intro i k
    obtain ⟨c, hc, hcv⟩ := pb_coords x 𝔞 (htL k)
    have e2 : t k • b' k = ∑ i, (C i k * (t k : K)) • x i := by
      rw [hC k, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hcoeS, smul_smul, mul_comm]
    rw [e2] at hcv
    have := coords_unique hind hcv
    rw [congrFun this i]
    exact hc i
  have hM : (C * Matrix.diagonal fun k => (t k : K)).det ∈ ∏ i, 𝔞 i :=
    det_mem_prod 𝔞 _ fun i k => by rw [Matrix.mul_diagonal]; exact hrow i k
  rw [Matrix.det_mul, Matrix.det_diagonal] at hM
  have hT : (∏ k, t k) ∈ S := Submonoid.prod_mem S fun k _ => htS k
  have hTc : (∏ k, (t k : K)) = ((∏ k, t k : 𝓞 K) : K) := by
    rw [← map_prod (algebraMap (𝓞 K) K)]
  have hT0 : (∏ k, (t k : K)) ≠ 0 := by
    rw [hTc]; intro h0
    apply hS1 _ hT
    have : (∏ k, t k : 𝓞 K) = 0 := by exact_mod_cast h0
    rw [this]; exact P.asIdeal.zero_mem
  have hcT : FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (∏ k, (t k : K))) = 0 := by
    rw [hTc]; exact count_span_unit P _ (hS1 _ hT)
  have hB1 : FractionalIdeal.count K P (∏ i, 𝔞 i) ≤
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) C.det) := by
    have := count_le_of_mem (K := K) P hM (mul_ne_zero hCdet hT0)
    rwa [count_span_mul P hCdet hT0, hcT, add_zero] at this
  have hB2 : FractionalIdeal.count K P (∏ i, 𝔞 i) ≤
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (star C.det)) := by
    have hsM := sStable_prod Finset.univ 𝔞 (fun i => hstar i) _ hM
    have hsT : star (∏ k, (t k : K)) = ∏ k, (t k : K) := by rw [hTc]; exact hS2 _ hT
    rw [star_mul', hsT] at hsM
    have := count_le_of_mem (K := K) P hsM (mul_ne_zero hsCdet hT0)
    rwa [count_span_mul P hsCdet hT0, hcT, add_zero] at this

  have hb'det : (gram h b').det ≠ 0 := by
    rw [hgdiag, Matrix.det_diagonal, Equiv.prod_comp σ (fun j => algebraMap F K ((a j : 𝓞 F) : F))]
    rw [← map_prod]; exact ha0'
  have hbind : LinearIndependent K b' := linearIndependent_of_det_gram h b' hb'det
  have hCinv : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C (isUnit_iff_ne_zero.mpr hCdet)
  have hx : ∀ i, x i = ∑ k, C⁻¹ k i • b' k := by
    intro i
    simp_rw [hC, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have e4 : ∀ j, ∑ k, C⁻¹ k i * C j k = (1 : Matrix ι ι K) j i := by
      intro j
      rw [← hCinv, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    simp_rw [← Finset.sum_smul, e4, Matrix.one_apply]
    simp
  have hint2 : ∀ z : ι → K, (∀ i, z i ∈ 𝔞 i) → ∃ s ∈ S,
      (C.det)⁻¹ * (s : K) * ∏ i, z i ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    intro z hz
    have h1 : ∀ i, ∃ s ∈ S, ∃ e : Fin (finrank K X) → 𝓞 K, ∑ j, e j • b j = s • (z i • x i) := by
      intro i
      have hm : z i • x i ∈ pbLat x 𝔞 := Submodule.subset_span ⟨i, z i, hz i, rfl⟩
      obtain ⟨s, hs, hsm⟩ := (hlocmem2 (z i • x i)).mp ⟨1, S.one_mem, by rw [one_smul]; exact hm⟩
      obtain ⟨e, he⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp hsm
      exact ⟨s, hs, e, he⟩
    choose s hsS e he using h1
    have hcoord : ∀ i k, ((e i (σ k) : 𝓞 K) : K) = C⁻¹ k i * ((s i : K) * z i) := by
      intro i k
      have e3 : ∑ k, ((e i (σ k) : 𝓞 K) : K) • b' k = ∑ k, (C⁻¹ k i * ((s i : K) * z i)) • b' k := by
        have l1 : ∑ k, ((e i (σ k) : 𝓞 K) : K) • b' k = ∑ j, e i j • b j := by
          rw [← Equiv.sum_comp σ (fun j => e i j • b j)]
          exact Finset.sum_congr rfl fun k _ => hcoeS _ _
        rw [l1, he i, hx i, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← hcoeS, smul_smul, smul_smul]
        congr 1
        ring
      exact congrFun (coords_unique hbind e3) k
    refine ⟨∏ i, s i, Submonoid.prod_mem S fun i _ => hsS i, ?_⟩
    set Yo : Matrix ι ι (𝓞 K) := fun k i => e i (σ k) with hYo
    have hY : Yo.map (algebraMap (𝓞 K) K) = C⁻¹ * Matrix.diagonal fun i => (s i : K) * z i := by
      ext k i
      rw [Matrix.mul_diagonal]
      exact hcoord i k
    have hdY := congrArg Matrix.det hY
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_mul, Matrix.det_diagonal,
      Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hdY
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨Yo.det, ?_⟩
    rw [hdY, Finset.prod_mul_distrib, ← map_prod (algebraMap (𝓞 K) K) s]
    ring

  choose y hyI hy0 hyc using fun i => exists_exact (K := K) P (hne i)
  have hprodc : FractionalIdeal.count K P (∏ i, 𝔞 i) = ∑ i, FractionalIdeal.count K P (𝔞 i) :=
    FractionalIdeal.count_prod K P _ _ (fun i _ => hne i)
  obtain ⟨s1, hs1, hw1⟩ := hint2 y hyI
  obtain ⟨s2, hs2, hw2⟩ := hint2 (fun i => star (y i)) (fun i => hstar i _ (hyI i))
  have hw2' : (star C.det)⁻¹ * (s2 : K) * ∏ i, y i ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    have h3 := sStable_one (K := K) _ hw2
    have hsp : star (∏ i, star (y i)) = ∏ i, y i := by
      rw [← starRingEnd_apply, map_prod]
      simp [starRingEnd_apply]
    rwa [star_mul', star_mul', star_inv₀, hS2 s2 hs2, hsp] at h3
  have hA1 := count_le_of_integral P C.det s1 y hCdet (hS1 s1 hs1) hy0 hw1
  have hA2 := count_le_of_integral P (star C.det) s2 y hsCdet (hS1 s2 hs2) hy0 hw2'
  simp_rw [hyc] at hA1 hA2
  rw [← hprodc] at hA1 hA2

  have hp0 : (∏ i, 𝔞 i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
  rw [hdetb, count_span_mul P (mul_ne_zero hsCdet hCdet) hdet, count_span_mul P hsCdet hCdet,
    FractionalIdeal.count_mul K P (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hne i))
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdet),
    Finset.prod_pow, FractionalIdeal.count_pow]
  push_cast
  linarith

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LatticeUnimodular
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Unimod

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {f : Fin D.R.rS → (VS D).V}
  {M : Submodule (𝓞 D.host.E) (WbQ D F0)}

theorem rs_mem_one_iff (x : D.host.E) :
    x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = x := by
  rw [Submodule.mem_one]
  all_goals first
    | rfl
    | exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩

theorem rs_fone_iff (x : D.host.E) :
    x ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ↔ ∃ o : 𝓞 D.host.E, (o : D.host.E) = x := by
  rw [FractionalIdeal.mem_one_iff]
  all_goals first
    | rfl
    | exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩

theorem rs_mem_dual {h : (VS D).V →ₗ⋆[D.host.E] (VS D).V →ₗ[D.host.E] D.host.E}
    {L : Submodule (𝓞 D.host.E) (VS D).V} {v : (VS D).V} :
    v ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, LinearMap.coe_restrictScalars]

theorem rs_mem_dualW {h : WbQ D F0 →ₗ⋆[D.host.E] WbQ D F0 →ₗ[D.host.E] D.host.E}
    {L : Submodule (𝓞 D.host.E) (WbQ D F0)} {v : WbQ D F0} :
    v ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y v ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, LinearMap.coe_restrictScalars]

theorem rs_inv_mul {a : Fin D.R.rS} {s x : D.host.E} (hs : s ∈ (aaI D a)⁻¹) (hx : x ∈ aaI D a) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = s * x := by
  by_cases hI : aaI D a = 0
  · rw [hI, inv_zero] at hs
    simp only [FractionalIdeal.mem_zero_iff] at hs
    exact ⟨0, by simp [hs]⟩
  · exact (rs_fone_iff _).1 ((FractionalIdeal.mem_inv_iff hI).1 hs x hx)

theorem rs_int_star {x : D.host.E} (hx : ∃ o : 𝓞 D.host.E, (o : D.host.E) = x) :
    ∃ o : 𝓞 D.host.E, (o : D.host.E) = star x := by
  obtain ⟨o, rfl⟩ := hx
  exact star_int D o

private theorem mem_lamC_iff {v : (VS D).V} : v ∈ lamC D F0 f M ↔
    ((∀ a, star ((VS D).hT (F0.e a) v) ∈ (aaI D a)⁻¹) ∧
      (∃ w : perpS (VS D) F0.X, (w : (VS D).V) = vPr D F0 f v ∧
        (Submodule.Quotient.mk w : WbQ D F0) ∈ M) ∧
      ∀ a, (VS D).hT (f a) (vPr D F0 f v) ∈ aaI D a) := Iff.rfl

private theorem hs_lemma_2 (x z : (VS D).V) : star ((VS D).hT x z) = (VS D).hT z x := by
  have h := (VS D).herm.eq x z
  first
    | exact h
    | rwa [starRingEnd_apply] at h

private theorem hT_eq_hT_vPr_right_add_sum (x z : (VS D).V) : (VS D).hT x z =
    (VS D).hT x (vPr D F0 f z) + ∑ b, (VS D).hT (F0.e b) z * (VS D).hT x (f b) := by
  simp [vPr, map_sub, map_sum, map_smul]

private theorem hT_eq_hT_vPr_left_add_sum (x z : (VS D).V) : (VS D).hT x z =
    (VS D).hT (vPr D F0 f x) z + ∑ a, star ((VS D).hT (F0.e a) x) * (VS D).hT (f a) z := by
  simp [vPr, LinearMap.map_sub₂, LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂, starRingEnd_apply]

private theorem mem_perpS_X_of_hT_e_eq_zero (z : (VS D).V) (hz : ∀ b, (VS D).hT (F0.e b) z = 0) :
    z ∈ perpS (VS D) F0.X := by
  have hK : F0.X ≤ LinearMap.ker ((VS D).hT z) := by
    rw [FlagG.X, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hs_lemma_2, hz b, star_zero]
  intro x hx
  rw [← hs_lemma_2, LinearMap.mem_ker.1 (hK hx), star_zero]

private theorem hT_e_vPr_eq_zero_of_partnerOK (hf : PartnerOK D F0 f) (z : (VS D).V) (b : Fin D.R.rS) :
    (VS D).hT (F0.e b) (vPr D F0 f z) = 0 := by
  simp [vPr, map_sub, map_sum, map_smul, hf.1]

theorem rs_lam_le_dual (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) :
    lamC D F0 f M ≤ Formalism.HermitianLatticesTheory.dual (VS D).hT (lamC D F0 f M) := by
  intro v hv
  rw [rs_mem_dual]
  intro y hy
  obtain ⟨hv1, ⟨w, hw, hwM⟩, hv3⟩ := mem_lamC_iff.1 hv
  obtain ⟨hy1, ⟨u, hu, huM⟩, hy3⟩ := mem_lamC_iff.1 hy
  have hU : Formalism.HermitianLatticesTheory.dual (hWb D F0) M = M := hM.2.1
  have hwD : (Submodule.Quotient.mk w : WbQ D F0) ∈ Formalism.HermitianLatticesTheory.dual (hWb D F0) M := by
    rw [hU]; exact hwM
  have hqp : (VS D).hT (vPr D F0 f y) (vPr D F0 f v) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    have h1 := rs_mem_dualW.1 hwD _ huM
    rw [← hu, ← hw, ← hWbFun_mk]
    exact h1
  rw [hT_eq_hT_vPr_right_add_sum (F0 := F0) (f := f) y v]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun b _ => ?_)
  · rw [hT_eq_hT_vPr_left_add_sum (F0 := F0) (f := f) y (vPr D F0 f v)]
    refine Submodule.add_mem _ hqp (Submodule.sum_mem _ fun a _ => ?_)
    exact (rs_mem_one_iff _).2 (rs_inv_mul (hy1 a) (hv3 a))
  · have e0 : (VS D).hT y (f b) = (VS D).hT (vPr D F0 f y) (f b) := by
      rw [hT_eq_hT_vPr_left_add_sum (F0 := F0) (f := f) y (f b)]
      simp [hf.2.1]
    rw [e0, ← hs_lemma_2 (f b) (vPr D F0 f y)]
    obtain ⟨o, ho⟩ := rs_int_star (rs_inv_mul (hv1 b) (hy3 b))
    refine (rs_mem_one_iff _).2 ⟨o, ?_⟩
    rw [ho, star_mul', star_star]

theorem rs_vPr_smul_f (hf : PartnerOK D F0 f) (a : Fin D.R.rS) (c : D.host.E) : vPr D F0 f (c • f a) = 0 := by
  rw [vPr_smul]
  have h0 : vPr D F0 f (f a) = 0 := by simp [vPr, hf.1]
  rw [h0, smul_zero]

theorem rs_smul_f_mem (hf : PartnerOK D F0 f) {a : Fin D.R.rS} {s : D.host.E} (hs : s ∈ (aaI D a)⁻¹) :
    star s • f a ∈ lamC D F0 f M := by
  refine mem_lamC_iff.2 ⟨fun b => ?_, ⟨0, ?_, ?_⟩, fun b => ?_⟩
  · rw [map_smul, hf.1, smul_eq_mul]
    by_cases hab : b = a
    · subst hab; rw [if_pos rfl, mul_one, star_star]; exact hs
    · rw [if_neg hab, mul_zero, star_zero]; exact fi_zero D _
  · simp [rs_vPr_smul_f hf]
  · rw [Submodule.Quotient.mk_zero]; exact M.zero_mem
  · rw [rs_vPr_smul_f hf, map_zero]; exact fi_zero D _

theorem rs_dual_le_lam (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) :
    Formalism.HermitianLatticesTheory.dual (VS D).hT (lamC D F0 f M) ≤ lamC D F0 f M := by
  intro v hv
  have hv' := rs_mem_dual.1 hv
  have hI0 : ∀ a, aaI D a ≠ 0 := by
    intro a
    have hd : ddS D ≠ 0 := by
      rw [ddS, Ne, FractionalIdeal.coeIdeal_eq_zero]
      first
        | exact Ideal.map_ne_bot_of_ne_bot differentIdeal_ne_bot
        | exact Ideal.map_ne_bot_of_ne_bot (differentIdeal_ne_bot (A := ℤ))
        | (intro h
           rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h
           exact differentIdeal_ne_bot h)
    rw [aaI]
    exact zpow_ne_zero _ hd
  have heX : ∀ a, F0.e a ∈ F0.X := by
    intro a
    rw [FlagG.X]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hfe : ∀ a b, (VS D).hT (f b) (F0.e a) = if a = b then 1 else 0 := by
    intro a b
    rw [← hs_lemma_2 (F0.e a) (f b), hf.1 a b]
    split_ifs <;> simp
  have hxe : ∀ a, ∀ x ∈ aaI D a, x • F0.e a ∈ lamC D F0 f M := by
    intro a x hx
    have hv0 : vPr D F0 f (x • F0.e a) = x • F0.e a := by
      simp [vPr, map_smul, F0.e_iso]
    have hxP : x • F0.e a ∈ perpS (VS D) F0.X :=
      Submodule.smul_mem _ x (mem_perpS_X_of_hT_e_eq_zero _ fun b => F0.e_iso b a)
    refine mem_lamC_iff.2 ⟨fun b => ?_, ⟨⟨x • F0.e a, hxP⟩, hv0.symm, ?_⟩, fun b => ?_⟩
    · rw [map_smul, F0.e_iso, smul_zero, star_zero]; exact fi_zero D _
    · rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_comap.2 (Submodule.smul_mem _ x (heX a)))]
      exact M.zero_mem
    · rw [hv0, map_smul, hfe a b, smul_eq_mul]
      split_ifs with hab
      · subst hab; simpa using hx
      · rw [mul_zero]; exact fi_zero D _
  have hPerp : vPr D F0 f v ∈ perpS (VS D) F0.X := mem_perpS_X_of_hT_e_eq_zero _ (hT_e_vPr_eq_zero_of_partnerOK hf v)
  have key : ∀ u' : perpS (VS D) F0.X, (Submodule.Quotient.mk u' : WbQ D F0) ∈ M →
      (VS D).hT (u' : (VS D).V) (vPr D F0 f v) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro u' hy
    obtain ⟨t, ht⟩ : ∃ t : (VS D).V, t = (u' : (VS D).V) - ∑ a, (VS D).hT (f a) u' • F0.e a :=
      ⟨_, rfl⟩
    have ht1 : ∀ b, (VS D).hT (F0.e b) t = 0 := by
      intro b
      rw [ht]
      simp [map_sub, map_sum, map_smul, F0.e_iso, hT_X_perp D F0 (heX b) u'.2]
    have ht3 : ∀ b, (VS D).hT (f b) t = 0 := by
      intro b
      rw [ht]
      simp [map_sub, map_sum, map_smul, hfe]
    have htP : t ∈ perpS (VS D) F0.X := mem_perpS_X_of_hT_e_eq_zero t ht1
    have hvt : vPr D F0 f t = t := by simp [vPr, ht1]
    have hq : (Submodule.Quotient.mk ⟨t, htP⟩ : WbQ D F0) = Submodule.Quotient.mk u' := by
      rw [Submodule.Quotient.eq]
      show t - (u' : (VS D).V) ∈ F0.X
      rw [ht, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (heX a))
    have htL : t ∈ lamC D F0 f M := by
      refine mem_lamC_iff.2 ⟨fun b => ?_, ⟨⟨t, htP⟩, hvt.symm, ?_⟩, fun b => ?_⟩
      · rw [ht1 b, star_zero]; exact fi_zero D _
      · rw [hq]; exact hy
      · rw [hvt, ht3 b]; exact fi_zero D _
    have htf : ∀ b, (VS D).hT t (f b) = 0 := fun b => by
      rw [← hs_lemma_2 (f b) t, ht3 b, star_zero]
    have e1 : (VS D).hT t v = (VS D).hT (u' : (VS D).V) (vPr D F0 f v) := by
      rw [hT_eq_hT_vPr_right_add_sum (F0 := F0) (f := f) t v]
      simp only [htf, mul_zero, Finset.sum_const_zero, add_zero]
      rw [ht]
      simp [LinearMap.map_sub₂, LinearMap.map_sum₂, LinearMap.map_smulₛₗ₂, hT_e_vPr_eq_zero_of_partnerOK hf]
    rw [← e1]
    exact hv' t htL
  have hWM : (Submodule.Quotient.mk ⟨vPr D F0 f v, hPerp⟩ : WbQ D F0) ∈
      Formalism.HermitianLatticesTheory.dual (hWb D F0) M := by
    rw [rs_mem_dualW]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H u' =>
      have e2 : hWb D F0 (Submodule.Quotient.mk u') (Submodule.Quotient.mk ⟨vPr D F0 f v, hPerp⟩) =
          (VS D).hT (u' : (VS D).V) (vPr D F0 f v) := hWbFun_mk D F0 u' ⟨vPr D F0 f v, hPerp⟩
      rw [e2]
      exact key u' hy
  have hU : Formalism.HermitianLatticesTheory.dual (hWb D F0) M = M := hM.2.1
  rw [hU] at hWM
  refine mem_lamC_iff.2 ⟨fun a => ?_, ⟨⟨_, hPerp⟩, rfl, hWM⟩, fun a => ?_⟩
  · rw [FractionalIdeal.mem_inv_iff (hI0 a)]
    intro x hx
    obtain ⟨o, ho⟩ := rs_int_star ((rs_mem_one_iff _).1 (hv' _ (hxe a x hx)))
    rw [rs_fone_iff]
    refine ⟨o, ?_⟩
    rw [ho, LinearMap.map_smulₛₗ₂, starRingEnd_apply, smul_eq_mul, star_mul', star_star, mul_comm]
  · have e3 : (VS D).hT (f a) (vPr D F0 f v) = (VS D).hT (f a) v := by
      rw [hT_eq_hT_vPr_right_add_sum (F0 := F0) (f := f) (f a) v]
      simp [hf.2.1]
    rw [e3, ← inv_inv (aaI D a), FractionalIdeal.mem_inv_iff (inv_ne_zero (hI0 a))]
    intro s hs
    obtain ⟨o, ho⟩ := (rs_mem_one_iff _).1 (hv' _ (rs_smul_f_mem hf hs))
    rw [rs_fone_iff]
    refine ⟨o, ?_⟩
    rw [ho, LinearMap.map_smulₛₗ₂, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]

end Unimod

theorem lamUnimod : LamUnimod := by
  intro D u F0 f M hf hM
  exact le_antisymm (rs_dual_le_lam hf hM) (rs_lam_le_dual hf hM)

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowClassHolds
section
namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem row_class_holds : RowClass := rowClass_of_zunit row_unit_condition

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end

