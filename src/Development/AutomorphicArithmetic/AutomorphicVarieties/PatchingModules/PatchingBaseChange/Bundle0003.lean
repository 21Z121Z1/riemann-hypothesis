import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
import Mathlib.RingTheory.MvPowerSeries.Equiv

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.SsDescend
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem eq_bot_of_forall_isNilpotent_of_isSemisimple {R : Type*} [Ring R] [IsSemisimpleRing R] (L : Submodule R R)
    (h : ∀ z ∈ L, IsNilpotent z) : L = ⊥ := by
  obtain ⟨C, hC⟩ := exists_isCompl L
  have h1 : (1 : R) ∈ L ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  have key : ∀ l ∈ L, l * f = 0 := by
    intro l hl
    have hl1 : l * e ∈ L := L.smul_mem l he
    have hl2 : l * f ∈ C := C.smul_mem l hf
    have hsub : l * f = l - l * e := by
      rw [eq_sub_iff_add_eq, add_comm, ← mul_add, hef, mul_one]
    have hL : l * f ∈ L := by rw [hsub]; exact L.sub_mem hl hl1
    exact (Submodule.disjoint_def.mp hC.disjoint) _ hL hl2
  have hee : IsIdempotentElem e := by
    show e * e = e
    calc e * e = e * (e + f) := by rw [mul_add, key e he, add_zero]
      _ = e := by rw [hef, mul_one]
  have he0 : e = 0 := hee.eq_zero_of_isNilpotent (h e he)
  rw [eq_bot_iff]
  intro l hl
  have hl' : l = l * e + l * f := by rw [← mul_add, hef, mul_one]
  rw [Submodule.mem_bot, hl', key l hl, he0, mul_zero, add_zero]

theorem UpperTheory.V.Pa.BC.ss_descend :
    ∀ (κ κ' E : Type) [Field κ] [Field κ'] [Algebra κ κ'] [Ring E] [Algebra κ E] [Module.Finite κ E], IsSemisimpleRing (κ' ⊗[κ] E) → IsSemisimpleRing E := by
  intro κ κ' E _ _ _ _ _ _ hT
  haveI : IsArtinianRing E := IsArtinianRing.of_finite κ E
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := E)
  set J := Ring.jacobson E with hJ
  let S : ℕ → Submodule κ (κ' ⊗[κ] E) := fun k =>
    Submodule.span κ {z | ∃ c : κ', ∃ a ∈ J ^ k, z = c ⊗ₜ[κ] a}
  have hgen : ∀ k (c : κ') (a : E), a ∈ J ^ k → c ⊗ₜ[κ] a ∈ S k :=
    fun k c a ha => Submodule.subset_span ⟨c, a, ha, rfl⟩
  have hmul : ∀ a (z w : κ' ⊗[κ] E), z ∈ S a → w ∈ S 1 → z * w ∈ S (a + 1) := by
    intro a z w hz hw
    induction hz using Submodule.span_induction with
    | mem z hz =>
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨c, u, hu, rfl⟩ := hz
        obtain ⟨c', v, hv, rfl⟩ := hw
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        refine hgen _ _ _ ?_
        rw [Submodule.pow_succ]
        rw [Submodule.pow_one] at hv
        exact Ideal.mul_mem_mul hu hv
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add w₁ w₂ _ _ h₁ h₂ => rw [mul_add]; exact Submodule.add_mem _ h₁ h₂
      | smul r w _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ r h
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add z₁ z₂ _ _ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
    | smul r z _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r h
  have hbot : S n = ⊥ := by
    rw [eq_bot_iff, Submodule.span_le]
    rintro z ⟨c, a, ha, rfl⟩
    rw [hn, Ideal.zero_eq_bot, Submodule.mem_bot] at ha
    show _ ∈ (⊥ : Submodule κ (κ' ⊗[κ] E))
    rw [Submodule.mem_bot, ha, TensorProduct.tmul_zero]
  have h1 : ∀ t : κ' ⊗[κ] E, t * ((1 : κ') ⊗ₜ[κ] x) ∈ S 1 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | tmul c a =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      refine hgen 1 c _ ?_
      rw [Submodule.pow_one]
      exact J.mul_mem_left a hx
    | add t₁ t₂ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  have hpow : ∀ z ∈ S 1, ∀ k, z ^ k ∈ S k := by
    intro z hz k
    induction k with
    | zero =>
      rw [pow_zero, Algebra.TensorProduct.one_def]
      exact hgen 0 1 1 (Submodule.one_le.mp fun _ h => h)
    | succ k ih => rw [pow_succ]; exact hmul k _ _ ih hz
  have hL : Submodule.span (κ' ⊗[κ] E) {(1 : κ') ⊗ₜ[κ] x} = ⊥ := by
    apply eq_bot_of_forall_isNilpotent_of_isSemisimple
    intro z hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨n, ?_⟩
    have hz' := hpow _ (h1 t) n
    rw [hbot, Submodule.mem_bot] at hz'
    rw [smul_eq_mul]
    exact hz'
  have hy : (1 : κ') ⊗ₜ[κ] x = 0 := by
    have hm : (1 : κ') ⊗ₜ[κ] x ∈ Submodule.span (κ' ⊗[κ] E) {(1 : κ') ⊗ₜ[κ] x} :=
      Submodule.mem_span_singleton_self _
    rw [hL, Submodule.mem_bot] at hm
    exact hm
  apply Algebra.TensorProduct.includeRight_injective (R := κ) (A := κ') (B := E)
    (algebraMap κ κ').injective
  rw [Algebra.TensorProduct.includeRight_apply, map_zero, hy]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilCo
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.til_co :
    ∀ (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O'] [IsLocalRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Module.Finite O O'] (R : Type) [CommRing R] [Algebra O R] [IsCO O R], ∃ _ : IsCO O' (Til O O' R), IsLocalHom (Til.ι O O' R) ∧ Til.s O O' R ∈ maximalIdeal (Til O O' R) := by
  intro O O' _ _ _ _ _ _ _ R _ _ _
  haveI hT := UpperTheory.V.CA.cl_bc O O' R
  let f : R →+* O' ⊗[O] R := (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).toRingHom
  have hint : f.IsIntegral := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact f.isIntegralElem_zero
    | tmul o r =>
      have ho : IsIntegral O ((Algebra.TensorProduct.includeLeft : O' →ₐ[O] O' ⊗[O] R) o) :=
        (Algebra.IsIntegral.isIntegral (R := O) o).map _
      rw [Algebra.TensorProduct.includeLeft_apply] at ho
      obtain ⟨p, hp, hpe⟩ := ho
      have h1 : f.IsIntegralElem (o ⊗ₜ[O] (1 : R)) := by
        refine ⟨p.map (algebraMap O R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map]
        have hc : f.comp (algebraMap O R) = algebraMap O (O' ⊗[O] R) :=
          (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R).comp_algebraMap
        rw [hc]
        exact hpe
      have he : o ⊗ₜ[O] r = (o ⊗ₜ[O] (1 : R)) * f r := by
        show _ = _ * ((1 : O') ⊗ₜ[O] r)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [he]
      exact RingHom.IsIntegralElem.mul f h1 f.isIntegralElem_map
    | add x y hx hy => exact RingHom.IsIntegralElem.add f hx hy
  have hloc : IsLocalHom f := by
    refine ((IsLocalRing.local_hom_TFAE f).out 0 4).mpr ?_
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hint (maximalIdeal (O' ⊗[O] R))
    exact IsLocalRing.eq_maximalIdeal this
  haveI hco : IsCO O' (Til O O' R) := UpperTheory.V.Alg.co_mvps O' (O' ⊗[O] R) Unit
  refine ⟨hco, ?_, ?_⟩
  · refine ⟨fun r hr => ?_⟩
    have hr' : IsUnit (PowerSeries.C ((1 : O') ⊗ₜ[O] r) : PowerSeries (O' ⊗[O] R)) := hr
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C] at hr'
    exact hloc.map_nonunit r hr'
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    show ¬ IsUnit (PowerSeries.X : PowerSeries (O' ⊗[O] R))
    rw [PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
    exact not_isUnit_zero
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilEv
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

section
variable {R : Type} [CommRing R] {ι : Type} (N : Type) [AddCommGroup N] [Module R N]

private theorem UpperTheory.V.Pa.BC.ev_nat {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (x : M ⊗[R] (ι → N)) (k : ι) :
    TensorProduct.piRightHom R R M' (fun _ : ι => N) (f.rTensor _ x) k =
      f.rTensor N (TensorProduct.piRightHom R R M (fun _ : ι => N) x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

private theorem UpperTheory.V.Pa.BC.ev_free (n : ℕ) :
    Function.Bijective (TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N)) := by
  classical
  let e1 : (Fin n → R) ⊗[R] (ι → N) ≃ₗ[R] (Fin n → ι → N) :=
    TensorProduct.piLeft R (ι → N) (fun _ : Fin n => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R (ι → N))
  let e2 : (ι → (Fin n → R) ⊗[R] N) ≃ₗ[R] (ι → Fin n → N) :=
    LinearEquiv.piCongrRight (fun _ => TensorProduct.piLeft R N (fun _ : Fin n => R) ≪≫ₗ
      LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R N))
  have key : ∀ x, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) x =
      e2.symm (Equiv.piComm _ (e1 x)) := by
    intro x
    apply e2.injective
    rw [LinearEquiv.apply_symm_apply]
    induction x using TensorProduct.induction_on with
    | zero =>
      ext k i
      simp
      rfl
    | tmul v f =>
      ext k i
      simp [e1, e2, TensorProduct.piRightHom_tmul, Function.swap, LinearEquiv.piCongrRight_apply]
    | add a b ha hb =>
      ext k i
      have h1 := congrFun (congrFun ha k) i
      have h2 := congrFun (congrFun hb k) i
      simp only [map_add, Pi.add_apply, Equiv.piComm_apply] at h1 h2 ⊢
      rw [h1, h2]
      rfl
  have hfun : ⇑(TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N)) =
      e2.symm ∘ (Equiv.piComm _) ∘ e1 := funext key
  rw [hfun]
  exact e2.symm.bijective.comp ((Equiv.piComm _).bijective.comp e1.bijective)

private theorem UpperTheory.V.Pa.BC.ev_surj (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (TensorProduct.piRightHom R R M (fun _ : ι => N)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  intro z
  choose w hw using fun k => LinearMap.rTensor_surjective N hp (z k)
  obtain ⟨y, hy⟩ := (UpperTheory.V.Pa.BC.ev_free (R := R) (ι := ι) N n).2 w
  refine ⟨p.rTensor _ y, ?_⟩
  funext k
  rw [UpperTheory.V.Pa.BC.ev_nat, hy, hw]

private theorem UpperTheory.V.Pa.BC.ev_bij [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Bijective (TensorProduct.piRightHom R R M (fun _ : ι => N)) := by
  haveI := Module.finitePresentation_of_finite R M
  refine ⟨?_, UpperTheory.V.Pa.BC.ev_surj N M⟩
  obtain ⟨n, m, f, g, hf, hfg⟩ := Module.FinitePresentation.exists_fin' R M
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective (ι → N) hf x
  have hex := rTensor_exact N hfg hf
  have hk : ∀ k, TensorProduct.piRightHom R R (Fin n → R) (fun _ : ι => N) y k ∈
      Set.range (g.rTensor N) := by
    intro k
    have h1 := congrFun hx k
    rw [UpperTheory.V.Pa.BC.ev_nat, Pi.zero_apply] at h1
    exact (hex _).1 h1
  choose z hz using hk
  obtain ⟨w, hw⟩ := (UpperTheory.V.Pa.BC.ev_free N m).2 z
  have hy : y = g.rTensor _ w := by
    apply (UpperTheory.V.Pa.BC.ev_free N n).1
    funext k
    rw [UpperTheory.V.Pa.BC.ev_nat, hw, hz]
  rw [hy, ← LinearMap.rTensor_comp_apply, hfg.linearMap_comp_eq_zero, LinearMap.rTensor_zero,
    LinearMap.zero_apply]

end

theorem UpperTheory.V.Pa.BC.til_ev :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower O R M] [Module.Finite R M], ∃ e : Til O O' R ⊗[R] M ≃+ (ℕ → O' ⊗[O] M), ∀ a m k, e (a ⊗ₜ m) k = Til.act O' m (Til.coeff O O' R k a) := by
  intro O O' _ _ _ _ R _ _ _ M _ _ _ _ _
  let N := R ⊗[O] O'
  let tc : O' ⊗[O] R ≃ₗ[O] N := TensorProduct.comm O O' R
  have hadd : ∀ (k : ℕ) (a b : Til O O' R),
      Til.coeff O O' R k (a + b) = Til.coeff O O' R k a + Til.coeff O O' R k b := by
    intro k a b
    unfold Til.coeff
    exact map_add (PowerSeries.coeff k) (show PowerSeries (O' ⊗[O] R) from a)
      (show PowerSeries (O' ⊗[O] R) from b)
  have hmulC : ∀ (k : ℕ) (r : R) (a : Til O O' R),
      Til.coeff O O' R k (algebraMap R (Til O O' R) r * a) = ((1 : O') ⊗ₜ[O] r) * Til.coeff O O' R k a := by
    intro k r a
    unfold Til.coeff
    exact PowerSeries.coeff_C_mul k (show PowerSeries (O' ⊗[O] R) from a) ((1 : O') ⊗ₜ[O] r)
  have hsm : ∀ (r : R) (c : O' ⊗[O] R), tc (((1 : O') ⊗ₜ[O] r) * c) = r • tc c := by
    intro r c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul o s =>
      simp only [tc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [TensorProduct.comm_tmul, TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => rw [mul_add, map_add, hx, hy, map_add, smul_add]
  let cf : Til O O' R →ₗ[R] (ℕ → N) :=
    { toFun := fun a k => tc (Til.coeff O O' R k a)
      map_add' := fun a b => by
        funext k
        simp only [hadd, map_add, Pi.add_apply]
      map_smul' := fun r a => by
        funext k
        simp only [RingHom.id_apply, Pi.smul_apply]
        rw [Algebra.smul_def, hmulC, hsm] }
  have hcf : Function.Bijective cf := by
    constructor
    · intro a b hab
      apply PowerSeries.ext
      intro k
      have h1 := congrFun hab k
      exact tc.injective h1
    · intro f
      refine ⟨PowerSeries.mk (fun k => tc.symm (f k)), ?_⟩
      funext k
      change tc (PowerSeries.coeff k (PowerSeries.mk (fun k => tc.symm (f k)))) = f k
      rw [PowerSeries.coeff_mk, LinearEquiv.apply_symm_apply]
  let cfe : Til O O' R ≃ₗ[R] (ℕ → N) := LinearEquiv.ofBijective cf hcf
  have hev := UpperTheory.V.Pa.BC.ev_bij (R := R) (ι := ℕ) N M
  let eve : M ⊗[R] (ℕ → N) ≃ₗ[R] (ℕ → M ⊗[R] N) :=
    LinearEquiv.ofBijective (TensorProduct.piRightHom R R M (fun _ : ℕ => N)) hev
  let cb : M ⊗[R] N ≃+ O' ⊗[O] M :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange O R R M O').toAddEquiv.trans
      (TensorProduct.comm O M O').toAddEquiv
  have hcb : ∀ (m : M) (c : O' ⊗[O] R), cb (m ⊗ₜ[R] tc c) = Til.act O' m c := by
    intro m c
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul o s =>
      simp [cb, tc, Til.act, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      rw [TensorProduct.comm_tmul, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
        TensorProduct.comm_tmul]
    | add x y hx hy => rw [map_add, TensorProduct.tmul_add, map_add, hx, hy, map_add]
  refine ⟨(TensorProduct.comm R (Til O O' R) M).toAddEquiv.trans
    ((cfe.lTensor M).toAddEquiv.trans (eve.toAddEquiv.trans (AddEquiv.piCongrRight (fun _ => cb)))), ?_⟩
  intro a m k
  simp only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv, TensorProduct.comm_tmul,
    LinearEquiv.lTensor_tmul, AddEquiv.piCongrRight_apply]
  rw [← hcb]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.TilLam
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private noncomputable def UpperTheory.V.Pa.BC.tlHom (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (σ : Type) :
    O' ⊗[O] MvPowerSeries σ O →ₐ[O'] MvPowerSeries σ O' :=
  Algebra.TensorProduct.lift (Algebra.ofId O' _) (MvPowerSeries.mapAlgHom (Algebra.ofId O O'))
    (fun _ _ => Commute.all _ _)

private theorem UpperTheory.V.Pa.BC.tlHom_tmul (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] (σ : Type)
    (o : O') (f : MvPowerSeries σ O) :
    UpperTheory.V.Pa.BC.tlHom O O' σ (o ⊗ₜ f) = MvPowerSeries.C o * MvPowerSeries.map (algebraMap O O') f := by
  rw [UpperTheory.V.Pa.BC.tlHom, Algebra.TensorProduct.lift_tmul]
  rfl

private theorem UpperTheory.V.Pa.BC.tlHom_bij (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O']
    [Module.Finite O O'] [Module.Free O O'] (σ : Type) :
    Function.Bijective (UpperTheory.V.Pa.BC.tlHom O O' σ) := by
  classical
  let b := Module.Free.chooseBasis O O'
  have hsum : ∀ (c : Module.Free.ChooseBasisIndex O O' → MvPowerSeries σ O) (m : σ →₀ ℕ),
      MvPowerSeries.coeff m (UpperTheory.V.Pa.BC.tlHom O O' σ (∑ i, b i ⊗ₜ c i)) =
        ∑ i, MvPowerSeries.coeff m (c i) • b i := by
    intro c m
    simp only [map_sum, UpperTheory.V.Pa.BC.tlHom_tmul, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_map,
      Algebra.smul_def]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨c, rfl⟩ := TensorProduct.eq_repr_basis_left b x
    rw [Finsupp.sum_fintype _ _ (by simp)] at hx ⊢
    have hc : ∀ i, c i = 0 := by
      intro i
      ext m
      have hm := congrArg (MvPowerSeries.coeff m) hx
      rw [hsum, map_zero] at hm
      rw [MvPowerSeries.coeff_zero]
      exact Fintype.linearIndependent_iff.1 b.linearIndependent (fun j => MvPowerSeries.coeff m (c j)) hm i
    simp [hc]
  · intro F
    let c : Module.Free.ChooseBasisIndex O O' → MvPowerSeries σ O :=
      fun i m => b.repr (MvPowerSeries.coeff m F) i
    refine ⟨∑ i, b i ⊗ₜ c i, ?_⟩
    ext m
    rw [hsum]
    exact b.sum_repr _

private theorem UpperTheory.V.Pa.BC.tl_option {σ R : Type} [CommRing R] (p : MvPowerSeries σ R) :
    MvPowerSeries.optionEquivLeft σ R (MvPowerSeries.rename (Function.Embedding.some : σ ↪ Option σ) p) =
      PowerSeries.C p := by
  classical
  ext k x
  rw [MvPowerSeries.coeff_coeff_optionEquivLeft, PowerSeries.coeff_C]
  split_ifs with hk
  · subst hk
    have hx : x.optionElim 0 = Finsupp.embDomain Function.Embedding.some x := by
      ext a
      cases a with
      | none =>
        rw [Finsupp.embDomain_notin_range _ _ _ (by simp)]
        simp
      | some v =>
        rw [show (some v : Option σ) = Function.Embedding.some v from rfl, Finsupp.embDomain_apply_self]
        simp
    rw [hx, MvPowerSeries.coeff_embDomain_rename]
  · rw [MvPowerSeries.coeff_zero]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hk
    have hn := congrArg (fun z : Option σ →₀ ℕ => z none) hy
    simpa [Finsupp.mapDomain_notin_range] using hn.symm

private theorem UpperTheory.V.Pa.BC.tl_map_bij {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Function.Bijective (PowerSeries.map (e : A →+* B)) := by
  refine ⟨fun p q h => ?_, fun q => ⟨PowerSeries.map (e.symm : B →+* A) q, ?_⟩⟩
  · ext n
    have hn := congrArg (PowerSeries.coeff n) h
    simpa using hn
  · ext n
    simp

theorem UpperTheory.V.Pa.BC.til_lam :
    ∀ (O O' : Type) [CommRing O] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] (D : ℕ), ∃ τ : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] abelian₂ O' Unit D, (∀ a, τ (Til.ι O O' _ a) = lamEmb O O' D a) ∧ τ (Til.s O O' _) = MvPowerSeries.X (.inl ()) := by
  intro O O' _ _ _ _ _ D
  let ε : Option (Empty ⊕ Fin D) ≃ Unit ⊕ Fin D :=
    { toFun := fun o => Option.elim o (Sum.inl ()) (Sum.map Empty.elim id)
      invFun := fun s => Sum.elim (fun _ => none) (fun i => some (Sum.inr i)) s
      left_inv := by
        rintro (_ | (e | i))
        · rfl
        · exact e.elim
        · rfl
      right_inv := by
        rintro (⟨⟩ | i) <;> rfl }
  have hb := UpperTheory.V.Pa.BC.tl_map_bij
    (RingEquiv.ofBijective (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D))
      (UpperTheory.V.Pa.BC.tlHom_bij O O' (Empty ⊕ Fin D)))
  let e1 : Til O O' (abelian₂ O Empty D) ≃ₐ[O'] PowerSeries (MvPowerSeries (Empty ⊕ Fin D) O') :=
    AlgEquiv.ofBijective (PowerSeries.mapAlgHom (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D))) hb
  let φ : O' ⊗[O] abelian₂ O Empty D →+* MvPowerSeries (Empty ⊕ Fin D) O' :=
    (UpperTheory.V.Pa.BC.tlHom O O' (Empty ⊕ Fin D) : O' ⊗[O] abelian₂ O Empty D →+* MvPowerSeries (Empty ⊕ Fin D) O')
  refine ⟨e1.trans ((MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm.trans
    (MvPowerSeries.renameEquiv O' ε)), ?_, ?_⟩
  · intro a
    have h1 : e1 (Til.ι O O' _ a) = PowerSeries.C (MvPowerSeries.map (algebraMap O O') a) := by
      show PowerSeries.map φ (PowerSeries.C ((1 : O') ⊗ₜ[O] a)) = _
      rw [PowerSeries.map_C]
      show PowerSeries.C (UpperTheory.V.Pa.BC.tlHom O O' _ ((1 : O') ⊗ₜ[O] a)) = _
      rw [UpperTheory.V.Pa.BC.tlHom_tmul, map_one, one_mul]
    have h2 : (MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm
        (PowerSeries.C (MvPowerSeries.map (algebraMap O O') a)) =
        MvPowerSeries.rename (Function.Embedding.some : (Empty ⊕ Fin D) ↪ _)
          (MvPowerSeries.map (algebraMap O O') a) := by
      rw [AlgEquiv.symm_apply_eq, UpperTheory.V.Pa.BC.tl_option]
    rw [AlgEquiv.trans_apply, h1, AlgEquiv.trans_apply, h2]
    show MvPowerSeries.rename (⇑ε) _ = _
    rw [MvPowerSeries.rename_rename]
    rfl
  · have h1 : e1 (Til.s O O' _) = PowerSeries.X := by
      show PowerSeries.map φ PowerSeries.X = _
      exact PowerSeries.map_X _
    have h2 : (MvPowerSeries.optionEquivLeft (Empty ⊕ Fin D) O').symm PowerSeries.X =
        MvPowerSeries.X none := by
      rw [AlgEquiv.symm_apply_eq, MvPowerSeries.optionEquivLeft_X_none]
    rw [AlgEquiv.trans_apply, h1, AlgEquiv.trans_apply, h2]
    show MvPowerSeries.rename (⇑ε) _ = _
    rw [MvPowerSeries.rename_X]
    rfl
end

