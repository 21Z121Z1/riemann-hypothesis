import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.BcChiTmul
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem bc_D {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (S : Type) [CommRing S] [Algebra B S] [inst : Algebra A S] [h : IsScalarTower A B S]
    (y : S ⊗[B] (B ⊗[A] E)) : (D.baseChange B).D S y = D.D S (Det.cancel A E B S y) := by
  have e : inst = ((algebraMap B S).comp (algebraMap A B)).toAlgebra :=
    Algebra.algebra_ext _ _ fun a => IsScalarTower.algebraMap_apply A B S a
  subst e
  rfl

private theorem cancel_one {A E : Type} [CommRing A] [Ring E] [Algebra A E] (B : Type)
    [CommRing B] [Algebra A B] (S : Type) [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S]
    (y : B ⊗[A] E) : Det.cancel A E B S (1 ⊗ₜ y) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B S) (AlgHom.id A E) y := by
  induction y with
  | zero => simp
  | tmul b z => simp [Det.cancel_tmul]
  | add a b ha hb => simp only [tmul_add, map_add, ha, hb]

private theorem bc_chi {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (y : B ⊗[A] E) : (D.baseChange B).chi y = D.chiS B y := by
  unfold Det.chi Det.chiS
  rw [bc_D, map_sub, cancel_one, Algebra.TensorProduct.one_def, Det.cancel_tmul, map_one, mul_one]

private theorem bc_chi_tmul {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type)
    [CommRing B] [Algebra A B] (x : E) : (D.baseChange B).chi (1 ⊗ₜ x) = (D.chi x).map (algebraMap A B) := by
  rw [bc_chi]
  have h := D.nat A[X] B[X] (Polynomial.mapAlgHom (Algebra.ofId A B)) (X ⊗ₜ 1 - 1 ⊗ₜ x)
  unfold Det.chi Det.chiS
  refine Eq.trans ?_ (h.trans ?_)
  · congr 1
    simp
  · rfl

theorem UpperTheory.V.CA.d_bc :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (B : Type) [CommRing B] [Algebra A B], (∀ (S : Type) [CommRing S] [Algebra B S] [Algebra A S] [IsScalarTower A B S] (y : S ⊗[B] (B ⊗[A] E)), (D.baseChange B).D S y = D.D S (Det.cancel A E B S y)) ∧ (∀ y, (D.baseChange B).val y = D.D B y) ∧ (∀ y, (D.baseChange B).chi y = D.chiS B y) ∧ ∀ x : E, (D.baseChange B).chi (1 ⊗ₜ x) = (D.chi x).map (algebraMap A B) ∧ ∀ i, (D.baseChange B).lam i (1 ⊗ₜ x) = algebraMap A B (D.lam i x) := by
  intro n A E _ _ _ D B _ _
  refine ⟨fun S _ _ _ _ y => bc_D D B S y, fun y => ?_, bc_chi D B, fun x => ⟨bc_chi_tmul D B x, fun i => ?_⟩⟩
  · change (D.baseChange B).D B (1 ⊗ₜ y) = _
    rw [bc_D, cancel_one]
    congr 1
    induction y with
    | zero => simp
    | tmul b z => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  · unfold Det.lam
    rw [bc_chi_tmul, Polynomial.coeff_map]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClFin
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, mem_smul_top_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hπ y
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I (Fin r → R) z
  exact ⟨π w, (AdicCompletion.map_of I π w).symm⟩

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k))
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h := hf (Nat.mul_le_mul_left (e + 1) hmn)
      rw [pow_mul] at h
      exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h)
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e))
  simpa using (I ^ n).add_mem h2 (Ideal.pow_right_mono hJI n h1)⟩

theorem UpperTheory.V.CA.cl_fin :
    ∀ (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] (R' : Type) [CommRing R'] [Algebra O R'] [IsLocalRing R'] [Algebra R R'] [IsScalarTower O R R'] [Module.Finite R R'], IsCL O R → IsCL O R' := by
  intro O _ R _ _ _ R' _ _ _ _ _ _ h
  haveI := h.noeth
  haveI := h.complete
  haveI := h.isLocalHom
  haveI := h.res_fin
  haveI hN : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  have hcomap : (maximalIdeal R').comap (algebraMap R R') = maximalIdeal R :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal R'))
  have hle : (maximalIdeal R).map (algebraMap R R') ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 hcomap.ge
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP => ?_
    obtain ⟨h1, h2⟩ := hP
    have h3 : P.comap (algebraMap R R') = maximalIdeal R :=
      ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ h2.ne_top)
        (Ideal.map_le_iff_le_comap.1 h1)).symm
    have h4 : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (h3 ▸ maximalIdeal.isMaximal R)
    exact (eq_maximalIdeal h4).ge
  obtain ⟨e, he⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  have hP : IsPrecomplete (maximalIdeal R') R' :=
    prec_cofinal hle he (IsPrecomplete.map_algebraMap_iff.2 (isPrecomplete_finite _))
  haveI hloc : IsLocalHom (algebraMap R R') := ⟨fun a ha => by
    by_contra hn
    have h1 : a ∈ maximalIdeal R := hn
    rw [← hcomap, Ideal.mem_comap] at h1
    exact h1 ha⟩
  haveI hT : IsScalarTower O (ResidueField R) (ResidueField R') :=
    IsScalarTower.of_algebraMap_eq fun a => by
      rw [IsScalarTower.algebraMap_apply O R (ResidueField R),
        ← IsScalarTower.algebraMap_apply R (ResidueField R) (ResidueField R'),
        IsScalarTower.algebraMap_apply O R' (ResidueField R'),
        IsScalarTower.algebraMap_apply R R' (ResidueField R'),
        IsScalarTower.algebraMap_apply O R R']
  exact
    { noeth := hN
      complete := { toIsHausdorff := inferInstance, toIsPrecomplete := hP }
      isLocalHom := by
        rw [IsScalarTower.algebraMap_eq O R R']
        infer_instance
      res_fin := Module.Finite.trans (ResidueField R) (ResidueField R') }
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClQuot
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem maximalIdeal_map_eq_of_surjective {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (f : R →+* R') (hf : Function.Surjective f) : (maximalIdeal R).map f = maximalIdeal R' := by
  have hk : RingHom.ker f ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top f)
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (f := f) hf (I := maximalIdeal R)
      (maximalIdeal.isMaximal R) with h | h
  · exfalso
    have h1 : (1 : R') ∈ (maximalIdeal R).map f := h ▸ Submodule.mem_top
    obtain ⟨y, hy, hy1⟩ := (Ideal.mem_map_iff_of_surjective f hf).1 h1
    have hker : 1 - y ∈ RingHom.ker f := by simp [RingHom.mem_ker, hy1]
    have h2 := Ideal.add_mem _ (hk hker) hy
    rw [sub_add_cancel] at h2
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  · exact IsLocalRing.eq_maximalIdeal h

private theorem isLocalHom_of_surjective {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (f : R →+* R') (hf : Function.Surjective f) : IsLocalHom f := by
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have hx' : x ∈ maximalIdeal R := h
  have : f x ∈ maximalIdeal R' := by
    rw [← maximalIdeal_map_eq_of_surjective f hf]
    exact Ideal.mem_map_of_mem f hx'
  exact this hx

private theorem smodEq_ideal_pow_smul_univ_iff_sub_mem {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (a b : A) :
    a ≡ b [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ a - b ∈ I ^ n := by
  simp [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem UpperTheory.V.CA.cl_quot :
    ∀ (O : Type) [CommRing O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] (R' : Type) [CommRing R'] [Algebra O R'] [IsLocalRing R'] (p : R →ₐ[O] R'), Function.Surjective p → IsCL O R → IsCL O R' := by
  intro O _ R _ _ _ R' _ _ _ p hp hR
  have hpr : Function.Surjective (p : R →+* R') := hp
  haveI : IsLocalHom (p : R →+* R') := isLocalHom_of_surjective _ hpr
  haveI := hR.noeth
  haveI : IsNoetherianRing R' := isNoetherianRing_of_surjective R R' (p : R →+* R') hpr
  haveI := hR.complete
  have hm : maximalIdeal R' = (maximalIdeal R).map (p : R →+* R') := (maximalIdeal_map_eq_of_surjective _ hpr).symm
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · haveI : IsHausdorff (maximalIdeal R') R' := inferInstance
    refine { toIsHausdorff := inferInstance, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
    have hd : ∀ n, ∃ d ∈ maximalIdeal R ^ n, p d = f (n + 1) - f n := by
      intro n
      have h0 := (smodEq_ideal_pow_smul_univ_iff_sub_mem _ _ _ _).1 (hf (Nat.le_succ n))
      rw [hm, ← Ideal.map_pow] at h0
      obtain ⟨d, hd, hd'⟩ := (Ideal.mem_map_iff_of_surjective _ hpr).1 (neg_mem h0)
      refine ⟨d, hd, ?_⟩
      rw [neg_sub] at hd'
      exact hd'
    choose d hdm hdp using hd
    obtain ⟨y0, hy0⟩ := hp (f 0)
    have hy : ∀ n, p (y0 + ∑ k ∈ Finset.range n, d k) = f n := by
      intro n
      induction n with
      | zero => simp [hy0]
      | succ n ih =>
        rw [Finset.sum_range_succ, ← add_assoc, map_add, ih, hdp]
        ring
    have hcauchy : ∀ {m n : ℕ}, m ≤ n →
        (y0 + ∑ k ∈ Finset.range m, d k) ≡ (y0 + ∑ k ∈ Finset.range n, d k)
          [SMOD (maximalIdeal R ^ m • ⊤ : Submodule R R)] := by
      intro m n hmn
      rw [smodEq_ideal_pow_smul_univ_iff_sub_mem]
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have e : (y0 + ∑ k ∈ Finset.range m, d k) - (y0 + ∑ k ∈ Finset.range (n + 1), d k) =
            ((y0 + ∑ k ∈ Finset.range m, d k) - (y0 + ∑ k ∈ Finset.range n, d k)) - d n := by
          rw [Finset.sum_range_succ]
          ring
        rw [e]
        exact Ideal.sub_mem _ ih (Ideal.pow_le_pow_right hmn (hdm n))
    obtain ⟨L, hL⟩ := (inferInstance : IsPrecomplete (maximalIdeal R) R).prec'
      (fun n => y0 + ∑ k ∈ Finset.range n, d k) hcauchy
    refine ⟨p L, fun n => ?_⟩
    rw [smodEq_ideal_pow_smul_univ_iff_sub_mem, hm, ← Ideal.map_pow, ← hy n, ← map_sub]
    exact Ideal.mem_map_of_mem (p : R →+* R') ((smodEq_ideal_pow_smul_univ_iff_sub_mem _ _ _ _).1 (hL n))
  · refine ⟨fun x hx => ?_⟩
    have e : algebraMap O R' x = (p : R →+* R') (algebraMap O R x) := (p.commutes x).symm
    rw [e] at hx
    exact hR.isLocalHom.map_nonunit _ (IsLocalHom.map_nonunit _ hx)
  · let L : ResidueField R →ₗ[O] ResidueField R' :=
      { toFun := IsLocalRing.ResidueField.map (p : R →+* R')
        map_add' := map_add _
        map_smul' := by
          intro o x
          obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
          simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
          congr 1
          rw [IsScalarTower.algebraMap_apply O R (ResidueField R),
            IsScalarTower.algebraMap_apply O R' (ResidueField R')]
          change IsLocalRing.ResidueField.map _ (residue R _) = residue R' _
          rw [IsLocalRing.ResidueField.map_residue]
          simp }
    have hL : Function.Surjective L := by
      intro z
      obtain ⟨y', rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨y, rfl⟩ := hpr y'
      exact ⟨IsLocalRing.residue R y, IsLocalRing.ResidueField.map_residue _ _⟩
    haveI := hR.res_fin
    exact Module.Finite.of_surjective L hL
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplIs
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private lemma mem_pow_iff (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (x : AdicCompletion (maximalIdeal L) L) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n ↔
      AdicCompletion.eval (maximalIdeal L) L n x = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]
  rfl

private lemma strict_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (a : L) (h : algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n) : a ∈ maximalIdeal L ^ n := by
  rw [mem_pow_iff, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
  have h' : Submodule.Quotient.mk (p := (maximalIdeal L ^ n • ⊤ : Submodule L L)) a = 0 := by
    simpa [AdicCompletion.eval] using h
  rw [Submodule.Quotient.mk_eq_zero] at h'
  simpa using h'

private lemma dense_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (b : AdicCompletion (maximalIdeal L) L) :
    ∃ a : L, b - algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)
  refine ⟨a, ?_⟩
  rw [mem_pow_iff, map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, sub_eq_zero, ← ha]
  simp [AdicCompletion.eval]

theorem UpperTheory.V.CA.cpl_is :
    ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (x : Ideal C) [x.IsMaximal], ∃ _ : IsLocalRing (Cpl x), IsCplAt x (Cpl x) := by
  intro C _ _ x hx
  refine ⟨inferInstance, ?_⟩
  have hL : ∀ (n : ℕ) (a : Localization.AtPrime x),
      a ∈ maximalIdeal (Localization.AtPrime x) ^ n →
      algebraMap (Localization.AtPrime x) (Cpl x) a ∈ maximalIdeal (Cpl x) ^ n := by
    intro n a ha
    rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  refine
    { noeth := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
      complete := inferInstance
      comap_pow := fun n => ?_
      dense := fun n r => ?_ }
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [IsScalarTower.algebraMap_eq C (Localization.AtPrime x) (Cpl x), ← Ideal.comap_comap]
    have e : Ideal.comap (algebraMap (Localization.AtPrime x) (Cpl x)) (maximalIdeal (Cpl x) ^ n) =
        maximalIdeal (Localization.AtPrime x) ^ n := by
      ext a
      exact ⟨strict_loc _ n a, hL n a⟩
    rw [e, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    refine IsLocalization.comap_map_of_isPrimary_disjoint x.primeCompl _ ?_ ?_
    · apply Ideal.isPrimary_of_isMaximal_radical
      rw [Ideal.radical_pow _ hn.ne', (inferInstance : x.IsPrime).radical]
      infer_instance
    · exact Set.disjoint_left.mpr fun s hs hs' => hs (Ideal.pow_le_self hn.ne' hs')
  · obtain ⟨a, ha⟩ := dense_loc _ n r
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective x.primeCompl a
    have hsx : Ideal.span {(s : C)} ⊔ x = ⊤ := by
      rw [sup_comm]
      have hm : (s : C) ∈ x ⊔ Ideal.span {(s : C)} :=
        Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      refine hx.out.2 _ (lt_of_le_of_ne le_sup_left fun e => s.2 ?_)
      rwa [← e] at hm
    have h1 : (1 : C) ∈ Ideal.span {(s : C)} ⊔ x ^ n := by
      rw [Ideal.sup_pow_eq_top hsx]
      trivial
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    refine ⟨c * t, ?_⟩
    have key : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) =
        IsLocalization.mk' (Localization.AtPrime x) c s * algebraMap C _ z := by
      have hs := IsLocalization.mk'_spec (Localization.AtPrime x) c s
      have hz' : z = 1 - t * s := by
        rw [← hyz]
        ring
      rw [hz', map_sub, map_one, map_mul, map_mul, ← hs]
      ring
    have hmem : IsLocalization.mk' (Localization.AtPrime x) c s - algebraMap C _ (c * t) ∈
        maximalIdeal (Localization.AtPrime x) ^ n := by
      rw [key, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hz)
    have hsum := Ideal.add_mem _ ha (hL n _ hmem)
    rw [map_sub, ← IsScalarTower.algebraMap_apply C (Localization.AtPrime x) (Cpl x)] at hsum
    convert hsum using 1
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DComm
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.d_comm :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (S : Type) [CommRing S] [Algebra A S] (x y : S ⊗[A] E), D.D S (1 + x * y) = D.D S (1 + y * x) := by
  intro n A E _ _ _ D S _ _ x y
  let i : S →ₐ[A] S[X] := IsScalarTower.toAlgHom A S S[X]
  let ι := Algebra.TensorProduct.map i (AlgHom.id A E)
  let ev : S → (S[X] →ₐ[A] S) := fun c => (Polynomial.aeval c : S[X] →ₐ[S] S).restrictScalars A
  let π := fun c => Algebra.TensorProduct.map (ev c) (AlgHom.id A E)
  have hπι : ∀ c z, π c (ι z) = z := by
    intro c z
    induction z with
    | zero => simp
    | tmul s e => simp [π, ι, ev, i]
    | add a b ha hb => simp only [map_add, ha, hb]
  let t : S[X] ⊗[A] E := X ⊗ₜ 1
  have ht : ∀ c, π c t = c ⊗ₜ 1 := by
    intro c
    simp [π, t, ev]
  let u : S[X] ⊗[A] E := 1 + t * ι (x - 1)
  have hu0 : π 0 u = 1 := by
    simp only [u, map_add, map_mul, map_one, hπι, ht]
    simp
  have hu1 : π 1 u = x := by
    simp only [u, map_add, map_mul, map_one, hπι, ht]
    rw [← Algebra.TensorProduct.one_def]
    simp
  have hc : (D.D S[X] u).coeff 0 = 1 := by
    have h := D.nat S[X] S (ev 0) u
    change D.D S (π 0 u) = _ at h
    rw [hu0, map_one] at h
    rw [h]
    simp [ev, Polynomial.coeff_zero_eq_eval_zero]
  have hnz : D.D S[X] u ∈ nonZeroDivisors S[X] :=
    Polynomial.mem_nonzeroDivisors_of_coeff_mem 0 (by rw [hc]; exact one_mem _)
  have key : D.D S[X] (1 + u * ι y) = D.D S[X] (1 + ι y * u) := by
    have h : (1 + u * ι y) * u = u * (1 + ι y * u) := by noncomm_ring
    have h2 := congrArg (D.D S[X]) h
    rw [map_mul, map_mul, mul_comm (D.D S[X] u)] at h2
    exact (mul_cancel_right_mem_nonZeroDivisors hnz).1 h2
  have h := congrArg (ev 1) key
  rw [← D.nat, ← D.nat] at h
  change D.D S (π 1 _) = D.D S (π 1 _) at h
  simpa only [map_add, map_mul, map_one, hπι, hu1] using h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section
variable {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E']
  (f : E →ₐ[A] E')

private theorem map_eq_lTensor (S : Type) [CommRing S] [Algebra A S] (z : S ⊗[A] E) :
    Algebra.TensorProduct.map (AlgHom.id S S) f z = f.toLinearMap.lTensor S z := by
  induction z with
  | zero => simp
  | tmul s x => simp
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem map_surj (hf : Function.Surjective f) (S : Type) [CommRing S] [Algebra A S] :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  intro y
  obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective S (g := f.toLinearMap) hf y
  exact ⟨x, (map_eq_lTensor f S x).trans hx⟩

private theorem eq_of_map_eq (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → x ∈ D.ker)
    (S : Type) [CommRing S] [Algebra A S] (x y : S ⊗[A] E)
    (h : Algebra.TensorProduct.map (AlgHom.id S S) f x = Algebra.TensorProduct.map (AlgHom.id S S) f y) :
    D.D S x = D.D S y := by
  have hex := lTensor_exact S (LinearMap.exact_subtype_ker_map f.toLinearMap) hf
  have h0 : f.toLinearMap.lTensor S (x - y) = 0 := by
    rw [← map_eq_lTensor, map_sub, h, sub_self]
  obtain ⟨w, hw⟩ := (hex _).1 h0
  have key : ∀ (w : S ⊗[A] (LinearMap.ker f.toLinearMap)) (y : S ⊗[A] E),
      D.D S (y + (LinearMap.ker f.toLinearMap).subtype.lTensor S w) = D.D S y := by
    intro w
    induction w with
    | zero => simp
    | tmul s k =>
      intro y
      have := (D.mem_ker.1 (hk k.1 k.2)) S y (s ⊗ₜ 1) 1
      simpa using this
    | add a b ha hb => intro y; rw [LinearMap.map_add, ← add_assoc, hb, ha]
  rw [← key w y, hw, add_sub_cancel]

private theorem map_map_swap (B B' : Type) [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B'] (g : B →ₐ[A] B')
    (x : B ⊗[A] E) :
    Algebra.TensorProduct.map (AlgHom.id B' B') f (Algebra.TensorProduct.map g (AlgHom.id A E) x) =
      Algebra.TensorProduct.map g (AlgHom.id A E') (Algebra.TensorProduct.map (AlgHom.id B B) f x) := by
  induction x with
  | zero => simp
  | tmul s x => simp
  | add a b ha hb => simp only [map_add, ha, hb]

end

theorem UpperTheory.V.CA.d_factor :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {E' : Type} [Ring E'] [Algebra A E'] (f : E →ₐ[A] E'), Function.Surjective f → (∀ x, f x = 0 → x ∈ D.ker) → ∃! D' : Det n A E', D'.pull f = D := by
  intro n A E _ _ _ D E' _ _ f hf hk
  have hs := map_surj f hf
  have he := eq_of_map_eq D f hf hk
  have hσ : ∀ (S : Type) [CommRing S] [Algebra A S] (x : S ⊗[A] E),
      D.D S (Function.surjInv (hs S) (Algebra.TensorProduct.map (AlgHom.id S S) f x)) = D.D S x :=
    fun S _ _ x => he S _ _ (Function.surjInv_eq _ _)
  let D' : Det n A E' :=
    { D := fun S _ _ =>
        { toFun := fun y => D.D S (Function.surjInv (hs S) y)
          map_one' := by
            rw [← map_one (Algebra.TensorProduct.map (AlgHom.id S S) f), hσ, map_one]
          map_mul' := fun x y => by
            obtain ⟨x, rfl⟩ := hs S x
            obtain ⟨y, rfl⟩ := hs S y
            rw [← map_mul (Algebra.TensorProduct.map (AlgHom.id S S) f), hσ, hσ, hσ, map_mul] }
      nat := fun B B' _ _ _ _ g x => by
        obtain ⟨x, rfl⟩ := hs B x
        change D.D B' (Function.surjInv (hs B') _) = g (D.D B (Function.surjInv (hs B) _))
        rw [← map_map_swap, hσ, hσ, D.nat]
      homog := fun B _ _ b x => by
        obtain ⟨x, rfl⟩ := hs B x
        change D.D B (Function.surjInv (hs B) _) = b ^ n * D.D B (Function.surjInv (hs B) _)
        rw [← map_smul, hσ, hσ, D.homog] }
  refine ⟨D', Det.ext' fun S _ _ x => hσ S x, fun D'' h => Det.ext' fun S _ _ y => ?_⟩
  obtain ⟨x, rfl⟩ := hs S y
  refine Eq.trans ?_ (hσ S x).symm
  rw [← h]
  rfl
end

