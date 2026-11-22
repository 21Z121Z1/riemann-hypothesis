import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0401

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PullbackKahlerOmegaBounded
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]

private theorem mapDR_smul' (b : K) (w : DR ℂ K) :
    mapDR ℂ K L (b • w) = algebraMap K L b • mapDR ℂ K L w := by
  rw [map_smul]
  exact (algebraMap_smul L b (mapDR ℂ K L w)).symm

private theorem mapDR_iMulti (q : ℕ) (v : Fin q → K) :
    mapDR ℂ K L (ExteriorAlgebra.ιMulti K q fun j => D ℂ K (v j)) =
      ExteriorAlgebra.ιMulti L q fun j => D ℂ L (algebraMap K L (v j)) := by
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext j
  simp [mapDR, map1, ExteriorAlgebra.lift_ι_apply]

private theorem mapDR_om {B : Subalgebra ℂ K} {B' : Subalgebra ℂ L}
    (h : ∀ b ∈ B, algebraMap K L b ∈ B') (q : ℕ) {w : DR ℂ K} (hw : w ∈ omB ℂ K B q) :
    mapDR ℂ K L w ∈ omB ℂ L B' q := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    rw [mapDR_smul', mapDR_iMulti]
    exact Submodule.subset_span ⟨_, h b hb, _, fun j => h _ (hv j), rfl⟩
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
  | smul c u _ hu =>
    have e := ((mapDR ℂ K L).toLinearMap.restrictScalars ℂ).map_smul c u
    have e' : mapDR ℂ K L (c • u) = c • mapDR ℂ K L u := e
    rw [e']
    exact Submodule.smul_mem _ _ hu
end

section
variable {L : Type} [Field L] [Algebra ℂ L]

private theorem iMulti_mul (p q : ℕ) (u : Fin p → L) (v : Fin q → L) :
    (ExteriorAlgebra.ιMulti L p fun j => D ℂ L (u j)) * (ExteriorAlgebra.ιMulti L q fun j => D ℂ L (v j)) =
      ExteriorAlgebra.ιMulti L (p + q) fun j => D ℂ L (Fin.append u v j) := by
  simp only [ExteriorAlgebra.ιMulti_apply]
  rw [← List.prod_append, ← List.ofFn_fin_append]
  congr 2
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

private theorem om_mul (B : Subalgebra ℂ L) {p q : ℕ} {u w : DR ℂ L} (hu : u ∈ omB ℂ L B p)
    (hw : w ∈ omB ℂ L B q) : u * w ∈ omB ℂ L B (p + q) :=
  _root_.UpperTheory.Reformulated.B.Qe48.om_mul B hu hw
end

section
variable {K K' : Type} [Field K] [Field K'] [Algebra ℂ K] [Algebra ℂ K'] (j2 : K →ₐ[ℂ] K')

private theorem pullback_kahler_smul_alg (b : K) (w : DR ℂ K) : pr2L j2 (b • w) = j2 b • pr2L j2 w := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_smul' (L := K') b w

private theorem pullback_kahler_omegaBounded {B : Subalgebra ℂ K} {B' : Subalgebra ℂ K'} (h : ∀ b ∈ B, j2 b ∈ B') (q : ℕ)
    {w : DR ℂ K} (hw : w ∈ omB ℂ K B q) : pr2L j2 w ∈ omB ℂ K' B' q := by
  letI : Algebra K K' := j2.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ K K' := IsScalarTower.of_algebraMap_eq fun c => (j2.commutes c).symm
  exact mapDR_om (L := K') h q hw
end

private theorem wd_map {ι E E' : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (f : E →ₗ[ℂ] E') (w : ι → Module.End ℂ E) (w' : ι → Module.End ℂ E')
    (h : ∀ i m, f (w i m) = w' i (f m)) (c : Finset ι → E) :
    wd w' (fun s => f (c s)) = fun s => f (wd w c s) := by
  funext t
  simp [wd, h, map_sum]

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

private theorem gS_tmul (p q : K) : gS j2 (p ⊗ₜ q) = algebraMap K K' p * j2 q := by
  simp [gS]

private theorem gY_tmul (w' w : DR ℂ K) : gY j2 (w' ⊗ₜ w) = mapDR ℂ K K' w' * pr2L j2 w := by
  simp [gY]

private theorem gS_X (a : ℕ) (i : Fin (d + 1)) :
    gS j2 (((sysZ K x a).X i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = (((sysY x j2 d).X i : K'ˣ) : K') := by
  simp [sysZ, sysY, gS, IsScalarTower.algebraMap_apply F K K']

private theorem gS_Y (a : ℕ) (i : Fin (d + 1)) :
    gS j2 (((sysZ K x a).Y i : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) = (((sysY x j2 d).Y i : K'ˣ) : K') := by
  simp [sysZ, sysY, gS]

private theorem gY_act (s : K ⊗[ℂ] K) (m : DR ℂ K ⊗[ℂ] DR ℂ K) :
    gY j2 (actZ K s m) = gS j2 s • gY j2 m := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, add_smul, hs, ht]
  | tmul p q =>
    induction m using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [map_add, smul_add, hu, hv]
    | tmul w' w =>
      have e : actZ K (p ⊗ₜ q) (w' ⊗ₜ w) = (p • w') ⊗ₜ[ℂ] (q • w) := by
        simp [actZ, Module.endTensorEndAlgHom_apply]
      rw [e, gY_tmul, gY_tmul, mapDR_smul', pullback_kahler_smul_alg, gS_tmul, smul_mul_smul_comm]

private theorem gS_prod {κ : Type} [LinearOrder κ] (a : ℕ) (n : κ → ℕ × ℕ) (i j : Fin (d + 1)) (t : Finset κ) :
    gS j2 ((∏ l ∈ t, (sysZ K x a).u n i j l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      ((∏ l ∈ t, (sysY x j2 d).u n i j l : K'ˣ) : K') := by
  simp only [Units.coe_prod, map_prod, Sys.u, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, gS_X, gS_Y]

variable {x j2}

private theorem gY_M (hb : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I ∧ j2 b ∈ R2 (xv x) j2 I)
    {a : ℕ} (ha : a ≤ d) (I J : Finset (Fin (d + 1))) {m : DR ℂ K ⊗[ℂ] DR ℂ K}
    (hm : m ∈ (sysZ K x a).M I J) : gY j2 m ∈ (sysY x j2 d).M I J := by
  have key : (sysZ K x a).M I J ≤ ((sysY x j2 d).M I J).comap (gY j2) := by
    refine Submodule.map₂_le.2 fun u hu w hw => ?_
    show gY j2 (u ⊗ₜ w) ∈ omB ℂ K' (RY (xv x) j2 I J) d
    rw [gY_tmul]
    have e : d - a + a = d := by omega
    have h := om_mul (RY (xv x) j2 I J)
      (mapDR_om (L := K') (B' := RY (xv x) j2 I J)
        (fun b h => (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (hb I b h).1) _ hu)
      (pullback_kahler_omegaBounded j2 (B' := RY (xv x) j2 I J)
        (fun b h => (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J) (hb J b h).2) _ hw)
    rwa [e] at h
  exact key hm

private theorem gY_mix (hb : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I ∧ j2 b ∈ R2 (xv x) j2 I)
    {a : ℕ} (ha : a ≤ d) (s : Finset (Two d)) {m : DR ℂ K ⊗[ℂ] DR ℂ K}
    (h : m ∈ mixF (sysZ K x a).M s) : gY j2 m ∈ mixF (sysY x j2 d).M s := by
  unfold mixF at h ⊢
  split_ifs at h ⊢ with hc
  · exact gY_M hb ha _ _ h
  · rw [Submodule.mem_bot] at h ⊢
    simp [h]

private theorem gY_wt {κ : Type} [LinearOrder κ] (a : ℕ) (z : κ → K ⊗[ℂ] K) (t : Two d ⊕ₗ κ)
    (m : DR ℂ K ⊗[ℂ] DR ℂ K) :
    gY j2 ((sysZ K x a).wt z t m) = (sysY x j2 d).wt (fun l => gS j2 (z l)) t (gY j2 m) := by
  unfold Sys.wt
  cases ofLex t with
  | inl i => rfl
  | inr l => exact gY_act j2 (z l) m
end

theorem UpperTheory.Gal.productCup_of_system.gMap_of :
    RYBasic → WdUni → GMap := by
  intro hB _ F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 h0 a ha
  have hb := (hB F K K' d x j2 h0).2.2.2.1
  refine ⟨fun l => ?_, fun s m => gY_act j2 s m, fun I J s hs => ?_, fun N t ht => ?_, ?_⟩
  · simp [Sys.mu, gS_X, gS_Y, map_sub, map_mul]
  · obtain ⟨t, rfl⟩ := hs
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv =>
      rw [map_add, map_add]
      exact add_mem hu hv
    | tmul p q =>
      have e : gS j2 (Algebra.TensorProduct.map (rB ℂ K (xv x) I).val (rB ℂ K (xv x) J).val (p ⊗ₜ q)) =
          algebraMap K K' p * j2 q := by
        rw [Algebra.TensorProduct.map_tmul, gS_tmul]
        rfl
      refine e ▸ (RY (xv x) j2 I J).mul_mem ?_ ?_
      · exact (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (hb I _ p.2).1
      · exact (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J) (hb J _ q.2).2
  · obtain ⟨y, hy, rfl⟩ := ht
    refine ⟨fun s => gY j2 (y s), fun s _ => ?_, wd_map (gY j2) _ _ (fun _ _ => rfl) y⟩
    have h := hy s (Set.mem_univ s)
    change y s ∈ (if (s.card : ℤ) = N - 1 then mixF (sysZ K x a).M s else ⊥) at h
    change gY j2 (y s) ∈ (if (s.card : ℤ) = N - 1 then mixF (sysY x j2 d).M s else ⊥)
    split_ifs at h ⊢ with hc
    · exact gY_mix hb ha s h
    · rw [Submodule.mem_bot] at h ⊢
      simp [h]
  · intro κ _ _ n z N c hc
    obtain ⟨hc1, hc2⟩ := hc
    refine ⟨fun s _ => ?_, ?_⟩
    · have h := hc1 s (Set.mem_univ s)
      change c s ∈ (if (s.card : ℤ) = N then mixF (fun I J => ((sysZ K x a).M I J).map
        ((sysZ K x a).act ((∏ l ∈ rgt s, (sysZ K x a).u n (pk I) (pk J) l : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K))) (lft s) else ⊥) at h
      change gY j2 (c s) ∈ (if (s.card : ℤ) = N then mixF (fun I J => ((sysY x j2 d).M I J).map
        ((sysY x j2 d).act ((∏ l ∈ rgt s, (sysY x j2 d).u n (pk I) (pk J) l : K'ˣ) : K'))) (lft s) else ⊥)
      split_ifs at h ⊢ with hcard
      · unfold mixF at h ⊢
        split_ifs at h ⊢ with hne
        · obtain ⟨m, hm, hmc⟩ := h
          refine ⟨gY j2 m, gY_M hb ha _ _ hm, ?_⟩
          rw [← hmc]
          have e := gY_act j2 ((∏ l ∈ rgt s, (sysZ K x a).u n (pk (lft (lft s))) (pk (rgt (lft s))) l :
            (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) m
          rw [gS_prod x j2 a] at e
          exact e.symm
        · rw [Submodule.mem_bot] at h ⊢
          simp [h]
      · rw [Submodule.mem_bot] at h ⊢
        simp [h]
    · have e := wd_map (gY j2) ((sysZ K x a).wt z) ((sysY x j2 d).wt fun l => gS j2 (z l))
        (fun t m => gY_wt a z t m) c
      have hc2' : wd ((sysZ K x a).wt z) c = 0 := hc2
      change wd ((sysY x j2 d).wt fun l => gS j2 (z l)) (fun s => gY j2 (c s)) = 0
      rw [e, hc2']
      funext s
      simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.TraceEqZeroOfBot
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem omB_eq_bot {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (a : ℕ)
    (hv : ∀ y ∈ ⋀[K]^a Ω[K⁄ℂ], y = 0) : omB ℂ K B a = ⊥ := by
  unfold omB
  rw [Submodule.span_eq_bot]
  rintro y ⟨b, -, v, -, rfl⟩
  rw [hv _ (ExteriorAlgebra.ιMulti_range K a ⟨_, rfl⟩), smul_zero]

private theorem trace_eq_zero_of_bot {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (G : Finset ι → Submodule ℂ E) (hG : ∀ I, G I = ⊥) (p : ℤ)
    (f : (cech G).H p →ₗ[ℂ] (cech G).H p) : LinearMap.trace ℂ _ f = 0 := by
  have hZ : ∀ z ∈ (cech G).Z p, z = 0 := by
    intro z hz
    have hC : z ∈ cechC G p := (Submodule.mem_inf.1 hz).1
    rw [cechC, Submodule.mem_pi] at hC
    funext s
    have h1 := hC s (Set.mem_univ s)
    split_ifs at h1 <;> simpa [hG] using h1
  haveI : Subsingleton ((cech G).Z p) :=
    ⟨fun a b => Subtype.ext ((hZ a a.2).trans (hZ b b.2).symm)⟩
  haveI : Subsingleton ((cech G).H p) :=
    (Submodule.Quotient.mk_surjective _).subsingleton
  rw [Subsingleton.elim f 0, map_zero]

private theorem coeff_det_eq_zero {d a : ℕ} (hlt : d < a) (B : Matrix (Fin d) (Fin d) ℂ) :
    (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • B.map Polynomial.C)).coeff a = 0 := by
  rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
    Finset.powersetCard_eq_empty.2 (by simpa using hlt), Finset.sum_empty]

private theorem val_div {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ)
    (c g : L) (hc : c ∈ B) (hg : g ∈ B) (hne : e ⟨c, hc⟩ ≠ 0) (t : ℂ)
    (h : e ⟨g, hg⟩ = e ⟨c, hc⟩ * t) (hc0 : c ≠ 0) : Val B e (g / c) t := by
  have hcg : c * (g / c) = g := by
    rw [mul_comm]
    exact div_mul_cancel₀ g hc0
  have hmem : c * (g / c) ∈ B := by
    rw [hcg]
    exact hg
  refine ⟨c, hc, hmem, hne, ?_⟩
  have hsub : (⟨c * (g / c), hmem⟩ : B) = ⟨g, hg⟩ := Subtype.ext hcg
  rw [hsub, h]

theorem UpperTheory.Gal.productCup_of_system.field0_of :
    FieldLe → ValBasic → Field0 := by
  intro hLe _
  intro d a F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ x j2 hK hK' hred hnf hz hfix Fx hFx hgen A hA hdet u hu hfd
  by_cases had : a ≤ d
  · have hne : ∀ i, x i ≠ 0 := hK.pd.ne
    let xu : Fin (d + 1) → Fˣ := fun i => Units.mk0 (x i) (hne i)
    have hY : Y1 xu j2 Fx A :=
      { covZ := hK
        covY := hK'
        cov := by
          intro i e
          obtain ⟨j, hj⟩ := hred i e
          refine ⟨j, fun v hv => ?_⟩
          obtain ⟨b, hb, he, hbv⟩ := hj v hv
          exact ⟨⟨b, hb⟩, he, hbv⟩
        red := hnf
        off := hz
        orig := hfix
        fx := hFx
        tan := by
          intro e he m
          obtain ⟨c, hc, g, hg, hec, hsum, hgl⟩ := hA e he m
          have hc0 : c ≠ 0 := by
            rintro rfl
            apply hec
            have h0 : (⟨0, hc⟩ : rB ℂ K' x {0}) = 0 := rfl
            rw [h0, map_zero]
          refine ⟨fun l => g l / c, fun l => val_div _ _ c (g l) hc (hg l) hec _ (hgl l) hc0, ?_⟩
          show j2 (algebraMap F K (x m.succ / x 0)) = ∑ l, g l / c * algebraMap F K' (x l.succ / x 0)
          apply mul_left_cancel₀ hc0
          rw [hsum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [← mul_assoc, mul_comm c, div_mul_cancel₀ _ hc0]
        det := hdet }
    exact hLe F K K' d xu j2 Fx A hY a had u hu
  · push_neg at had
    have hv := (GlobalTheory.T.dlog_basis_and_vanishing_above_dimension ℂ F K d x hK).2 a had
    refine (Finset.sum_eq_zero fun p _ => ?_).trans (Finset.sum_eq_zero fun e _ => ?_).symm
    · rw [trace_eq_zero_of_bot _ (fun I => omB_eq_bot _ a hv) _ (u p), mul_zero]
    · rw [coeff_det_eq_zero had, zero_div]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.TraceMemRB
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
  [IsScalarTower ℂ F K'] {d : ℕ}

private theorem tower_rA (y : Fin (d + 1) → F) : IsScalarTower (rA ℂ y {0}) K K' :=
  .of_algebraMap_eq fun r => IsScalarTower.algebraMap_apply F K K' (r : F)

private theorem map_mem_rB (y : Fin (d + 1) → F) {b : K} (hb : b ∈ rB ℂ K y {0}) :
    algebraMap K K' b ∈ rB ℂ K' y {0} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hb ⊢
  haveI := tower_rA (K := K) (K' := K') y
  exact hb.algebraMap

private theorem trace_mem_rB (y : Fin (d + 1) → F) [FiniteDimensional K K'] {v : K'}
    (hv : v ∈ rB ℂ K' y {0}) : Algebra.trace K K' v ∈ rB ℂ K y {0} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff] at hv ⊢
  haveI := tower_rA (K := K) (K' := K') y
  exact Algebra.isIntegral_trace hv

end

theorem UpperTheory.Gal.productCup_of_system.redK_of :
    RedK := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY
  haveI : FiniteDimensional F K' := hY.covY.fin
  haveI : FiniteDimensional K K' := Module.Finite.of_restrictScalars_finite F K K'
  have hred := hY.red
  unfold RedFib at hred ⊢
  constructor
  intro z hz
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨n, hn⟩ := hz
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun] at hn
  obtain ⟨c, hc⟩ := hn
  rw [Ideal.Quotient.eq_zero_iff_mem]
  set t : Fin d → F := fun j => xv x j.succ / xv x 0 with ht
  have hcK : ∑ j, (c j : K) * algebraMap F K (t j) = (a : K) ^ n := by
    have := congrArg (fun u : rB ℂ K (xv x) {0} => (u : K)) hc
    simpa only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubmonoidClass.coe_pow] using this
  let b : rB ℂ K' (xv x) {0} := ⟨algebraMap K K' a, map_mem_rB (xv x) a.2⟩
  have hb : b ∈ Ideal.span (Set.range fun j : Fin d =>
      (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0})) := by
    have hq : IsNilpotent (Ideal.Quotient.mk (Ideal.span (Set.range fun j : Fin d =>
        (⟨algebraMap F K' (t j), tco_mem ℂ K' (xv x) j⟩ : rB ℂ K' (xv x) {0}))) b) := by
      refine ⟨n, ?_⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_range_iff_exists_fun]
      refine ⟨fun j => ⟨algebraMap K K' (c j), map_mem_rB (xv x) (c j).2⟩, ?_⟩
      apply Subtype.ext
      simp only [b, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [← map_pow, ← hcK, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, ← IsScalarTower.algebraMap_apply]
    exact (Ideal.Quotient.eq_zero_iff_mem).1 (hred.eq_zero _ hq)
  rw [Ideal.mem_span_range_iff_exists_fun] at hb
  obtain ⟨e, he⟩ := hb
  have key : (Module.finrank K K' : K) * (a : K) =
      ∑ j, Algebra.trace K K' (e j : K') * algebraMap F K (t j) := by
    have h1 := congrArg (fun u : rB ℂ K' (xv x) {0} => Algebra.trace K K' (u : K')) he
    simp only [b, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, map_sum,
      Algebra.trace_algebraMap, nsmul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IsScalarTower.algebraMap_apply F K K', mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul,
      mul_comm]
  have hmem : ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a) ∈ Ideal.span (Set.range fun j : Fin d =>
      (⟨algebraMap F K (t j), tco_mem ℂ K (xv x) j⟩ : rB ℂ K (xv x) {0})) := by
    rw [Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun j => ⟨Algebra.trace K K' (e j : K'), trace_mem_rB (xv x) (e j).2⟩, ?_⟩
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul, SubringClass.coe_natCast]
    exact key.symm
  have hpos : (Module.finrank K K' : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := K')).ne'
  have hA : a = algebraMap ℂ (rB ℂ K (xv x) {0}) ((Module.finrank K K' : ℂ)⁻¹) *
      ((Module.finrank K K' : rB ℂ K (xv x) {0}) * a) := by
    rw [← mul_assoc, ← map_natCast (algebraMap ℂ (rB ℂ K (xv x) {0})), ← map_mul,
      inv_mul_cancel₀ hpos, map_one, one_mul]
  rw [hA]
  exact Ideal.mul_mem_left _ _ hmem
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ValuationMulBis
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma UpperTheory.Gal.productCup_of_system.valuation_mul_bis (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {v w : L} {a b : ℂ}
    (h : Val B e v a) (h' : Val B e w b) : Val B e (v * w) (a * b) := by
  obtain ⟨-, ⟨ev, hev⟩, -⟩ := hV L B e
  obtain ⟨h1, ha⟩ := (hev v a).1 h
  obtain ⟨h2, hb⟩ := (hev w b).1 h'
  refine (hev (v * w) (a * b)).2 ⟨Subalgebra.mul_mem _ h1 h2, ?_⟩
  rw [← ha, ← hb, ← map_mul]
  rfl

private lemma UpperTheory.Gal.productCup_of_system.valuation_unique (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {v : L} {a b : ℂ}
    (h : Val B e v a) (h' : Val B e v b) : a = b := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨h1, rfl⟩ := (hev _ _).1 h
  obtain ⟨h2, rfl⟩ := (hev _ _).1 h'
  rfl

private lemma UpperTheory.Gal.productCup_of_system.valuation_mem (hV : ValBasic) {L : Type} [Field L] [Algebra ℂ L]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) {b : L} (hb : b ∈ B) : Val B e b (e ⟨b, hb⟩) :=
  (hV L B e).2.2.1 ⟨b, hb⟩

theorem UpperTheory.Gal.productCup_of_system.ptT_of :
    LocEq → ValBasic → RYBasic → PtT := by
  intro hLoc hV hRY
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY I J i hi j hj e hv
  have hr : ∀ l, (sysY x j2 d).r n10 (gT x j2) i j l =
      algebraMap F K' (x l.succ) / algebraMap F K' (x i) := by
    intro l
    simp [Sys.r, Sys.u, gT, sysY, n10, div_eq_mul_inv]
  have hw : ∀ a b, (((sysY x j2 d).X a * ((sysY x j2 d).X b)⁻¹ : K'ˣ) : K') =
      algebraMap F K' (x a) / algebraMap F K' (x b) := by
    intro a b
    simp [sysY, div_eq_mul_inv]
  have hxne : ∀ a, algebraMap F K' (x a : F) ≠ 0 := fun a => (map_ne_zero _).2 (x a).ne_zero
  have h1 : Val (RY (xv x) j2 I J) e 1 1 := by
    have h1v := valuation_mem hV (RY (xv x) j2 I J) e (one_mem (RY (xv x) j2 I J))
    have h1' : (⟨1, one_mem _⟩ : RY (xv x) j2 I J) = 1 := rfl
    rw [h1', map_one] at h1v
    exact h1v
  have hv' : ∀ l : Fin d, Val (RY (xv x) j2 I J) e
      (algebraMap F K' (x l.succ) / algebraMap F K' (x i)) 0 := fun l => hr l ▸ hv l
  have hi0 : i = 0 := by
    by_contra h
    have hvi := hv' (i.pred h)
    rw [Fin.succ_pred, div_self (hxne i)] at hvi
    exact zero_ne_one (valuation_unique hV _ e hvi h1)
  subst hi0
  have hI : I = {0} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun i' hi' => ?_⟩
    by_contra h
    have hgood := (hRY F K K' d x j2 hY).2.1 d
    have hm := hgood.memX I J ⟨j, hj⟩ i' hi' 0
    rw [hw] at hm
    have hval := valuation_mem hV (RY (xv x) j2 I J) e hm
    have hprod := valuation_mul_bis hV _ e (hv' (i'.pred h)) hval
    rw [Fin.succ_pred, zero_mul] at hprod
    have hone : algebraMap F K' (x i') / algebraMap F K' (x 0) *
        (algebraMap F K' (x 0) / algebraMap F K' (x i')) = 1 := by
      rw [div_mul_div_comm, mul_comm (algebraMap F K' (x i')),
        div_self (mul_ne_zero (hxne 0) (hxne i'))]
    rw [hone] at hprod
    exact zero_ne_one (valuation_unique hV _ e hprod h1)
  obtain ⟨e0, hloc, hval⟩ := hLoc F K K' d x j2 hY I J 0 hi e
  refine ⟨⟨e0, fun l => ?_⟩, hI, hloc, hval⟩
  have ht := tco_mem ℂ K' (xv x) l
  have h0 := (hval _ _).1 (hv' l)
  rw [← map_div₀] at h0
  have hm := valuation_mem hV _ e0 ht
  exact valuation_unique hV _ e0 hm h0
end

