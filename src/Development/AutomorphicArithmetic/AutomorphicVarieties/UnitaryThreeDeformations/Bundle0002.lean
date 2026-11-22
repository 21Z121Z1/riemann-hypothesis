import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0003

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsSmallExtensionFactorizationOfFunctional
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem isCO_of_surj {O : Type} [CommRing O] [IsLocalRing O] {R S : Type} [CommRing R] [Algebra O R]
    [IsCO O R] [Finite R] [CommRing S] [Algebra O S] [Nontrivial S] (f : R →ₐ[O] S)
    (hf : Function.Surjective f) :
    ∃ _ : IsCO O S, ∀ x : R, f x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := by
  haveI : IsLocalRing S := IsLocalRing.of_surjective' (f : R →+* S) hf
  haveI : Finite S := Finite.of_surjective f hf
  haveI hl : IsLocalHom (f : R →+* S) := IsLocalHom.of_surjective (f : R →+* S) hf
  have hm : ∀ x : R, f x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := fun x =>
    ⟨fun h hu => h (hu.map f), fun h hu => h (hl.map_nonunit x hu)⟩
  haveI : IsArtinianRing S := inferInstance
  refine ⟨{ complete := inferInstance, isLocalHom := ⟨fun a ha => ?_⟩, res_surj := fun y => ?_ }, hm⟩
  · rw [← f.commutes] at ha
    exact IsLocalHom.map_nonunit (f := algebraMap O R) a (hl.map_nonunit _ ha)
  · obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
    refine ⟨a, ?_⟩
    rw [← f.commutes, ← map_sub]
    exact (hm _).2 ha

theorem UpperTheory.exists_small_extension_factorization_of_functional :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [CommRing R'] [Algebra O R'] (p : R →ₐ[O] R'), maximalIdeal R * RingHom.ker p = ⊥ → RingHom.ker p ≤ maximalIdeal R → ∀ φ : RingHom.ker p →ₗ[O] ResidueField O, φ ≠ 0 →
     ∃ (R'' : Type) (_ : CommRing R'') (_ : Algebra O R'') (_ : IsCO O R'') (p₁ : R →ₐ[O] R'') (q : R'' →ₐ[O] R') (ε : ResidueField O →ₗ[O] R''), Function.Surjective p₁ ∧ q.comp p₁ = p ∧ ¬ Function.Injective q ∧ (∀ x : RingHom.ker p, p₁ x = ε (φ x)) ∧ (∀ y, q (ε y) = 0) ∧ (∀ y, ε y ∈ maximalIdeal R'') ∧ ∀ x ∈ maximalIdeal R'', ∀ y, x * ε y = 0 := by
  intro O _ _ R R' _ _ _ _ _ _ p hmul hle φ hφ
  have hz : ∀ m ∈ maximalIdeal R, ∀ x ∈ RingHom.ker p, m * x = 0 := fun m hm x hx => by
    have := Ideal.mul_mem_mul hm hx
    rwa [hmul, Ideal.mem_bot] at this
  let J : Ideal R :=
    { carrier := {x | ∃ h : x ∈ RingHom.ker p, φ ⟨x, h⟩ = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, ?_⟩
        have : (⟨a + b, add_mem ha hb⟩ : RingHom.ker p) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
        rw [this, map_add, ha', hb', add_zero]
      zero_mem' := ⟨zero_mem _, map_zero φ⟩
      smul_mem' := by
        rintro r x ⟨hx, hx'⟩
        refine ⟨Ideal.mul_mem_left _ r hx, ?_⟩
        obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) r
        have : (⟨r • x, Ideal.mul_mem_left _ r hx⟩ : RingHom.ker p) = a • ⟨x, hx⟩ := by
          apply Subtype.ext
          have h := hz _ ha x hx
          rw [sub_mul, sub_eq_zero] at h
          show r * x = a • x
          rw [h, Algebra.smul_def]
        rw [this, map_smul, hx', smul_zero] }
  have hJ : ∀ x : RingHom.ker p, (x : R) ∈ J ↔ φ x = 0 := fun x =>
    ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩
  have hJp : ∀ x ∈ J, p x = 0 := fun x ⟨h, _⟩ => h
  obtain ⟨x0, hx0⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨a, ha⟩ := residue_surjective (y * (φ x0)⁻¹)
    refine ⟨a • x0, ?_⟩
    rw [map_smul, Algebra.smul_def, ResidueField.algebraMap_eq, ha, inv_mul_cancel_right₀ hx0]
  have hJtop : J ≠ ⊤ := fun h => hx0 ((hJ x0).1 (h ▸ Submodule.mem_top))
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
  have hp1 : Function.Surjective (Ideal.Quotient.mkₐ O J) := Ideal.Quotient.mkₐ_surjective O J
  obtain ⟨inst, hm⟩ := isCO_of_surj (Ideal.Quotient.mkₐ O J) hp1
  let ψ : RingHom.ker p →ₗ[O] R ⧸ J :=
    (Ideal.Quotient.mkₐ O J).toLinearMap ∘ₗ ((RingHom.ker p).subtype.restrictScalars O)
  have hψ : ∀ x : RingHom.ker p, ψ x = Ideal.Quotient.mkₐ O J x := fun _ => rfl
  have hker : LinearMap.ker φ ≤ LinearMap.ker ψ := fun x hx =>
    Ideal.Quotient.eq_zero_iff_mem.2 ((hJ x).2 hx)
  let ε : ResidueField O →ₗ[O] R ⧸ J :=
    (LinearMap.ker φ).liftQ ψ hker ∘ₗ (φ.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  have hε : ∀ x : RingHom.ker p, ε (φ x) = Ideal.Quotient.mkₐ O J x := fun x => by
    have : (φ.quotKerEquivOfSurjective hsurj).symm (φ x) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    show (LinearMap.ker φ).liftQ ψ hker ((φ.quotKerEquivOfSurjective hsurj).symm (φ x)) = _
    rw [this, Submodule.liftQ_apply, hψ]
  have hq : ∀ x : R, Ideal.Quotient.liftₐ J p hJp (Ideal.Quotient.mkₐ O J x) = p x := fun _ => rfl
  refine ⟨R ⧸ J, inferInstance, inferInstance, inst, Ideal.Quotient.mkₐ O J, Ideal.Quotient.liftₐ J p hJp, ε,
    hp1, AlgHom.ext hq, fun hinj => ?_, fun x => (hε x).symm, fun y => ?_, fun y => ?_, fun x hx y => ?_⟩
  · have h : Ideal.Quotient.mkₐ O J (x0 : R) = 0 := hinj (by rw [hq, map_zero]; exact x0.2)
    exact hx0 ((hJ x0).1 (Ideal.Quotient.eq_zero_iff_mem.1 h))
  · obtain ⟨x, rfl⟩ := hsurj y
    rw [hε, hq]; exact x.2
  · obtain ⟨x, rfl⟩ := hsurj y
    rw [hε]; exact (hm _).2 (hle x.2)
  · obtain ⟨z, rfl⟩ := hsurj y
    obtain ⟨w, rfl⟩ := hp1 x
    rw [hε, ← map_mul, hz w ((hm w).1 hx) _ z.2, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsUniqueIsPtHom
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem gg_ext {R : Type} [CommRing R] {x y : GG 3 R} (h1 : x.right = y.right) (h2 : x.mat = y.mat) :
    x = y := SemidirectProduct.ext (Units.ext h2) h1

private theorem exists_weight_inv_det_left_mem_weight_piece {O R Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] (u : Γ →* GG 3 R) (g : Γ) : ∃ j : ℤ, (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ wpart O u j := by
  have hth : ∀ {R' : Type} [CommRing R'] (k : GL (Fin 3) R'), GeneralLinearGroup.det (thetaAut 3 R' k) = (GeneralLinearGroup.det k)⁻¹ := by
    intro R' _ k
    have hJ : GeneralLinearGroup.det (Jgl R' 3) * GeneralLinearGroup.det (Jgl R' 3) = 1 := by
      rw [← map_mul]
      have : Jgl R' 3 * Jgl R' 3 = 1 := Units.ext (Jgl R' 3).val_inv
      rw [this, map_one]
    have hT : GeneralLinearGroup.det (trInv k) = (GeneralLinearGroup.det k)⁻¹ := by
      rw [← map_inv]
      apply Units.ext
      simp [GeneralLinearGroup.val_det_apply, trInv, Matrix.det_transpose]
    show GeneralLinearGroup.det (theta k) = _
    simp only [theta, map_mul, hT]
    rw [mul_right_comm, hJ, one_mul]
  have htor : ∀ {R' : Type} [CommRing R'] (t : R'ˣ), GeneralLinearGroup.det (tor R' t) = t ^ (wt1 0 + wt1 1 + wt1 2) := by
    intro R' _ t
    apply Units.ext
    simp [GeneralLinearGroup.val_det_apply, tor, torGL, Matrix.det_diagonal, Fin.prod_univ_three, _root_.zpow_add]
  refine ⟨if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2)), ?_⟩
  intro R' _ _ _ f f' t h
  have hg := congrArg (fun φ => GeneralLinearGroup.det (φ g).left) h
  simp only [push, conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, GG.ofGL, SemidirectProduct.left_inl, SemidirectProduct.right_inl, GG.map, SemidirectProduct.map_left, SemidirectProduct.map_right, map_mul, GeneralLinearGroup.map_det] at hg
  simp only [map_one, inv_one, MulAut.one_apply, SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.map_right, MonoidHom.id_apply, one_mul, map_inv, htor] at hg
  have key : (Units.map (f' : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ = t ^ (if (u g).right = 1 then 0 else -(2 * (wt1 0 + wt1 1 + wt1 2))) * (Units.map (f : R →+* R')) (GeneralLinearGroup.det (u g).left)⁻¹ := by
    rw [map_inv, map_inv]
    split_ifs with hs
    · rw [hs, map_one, MulAut.one_apply, GeneralLinearGroup.map_det, htor] at hg
      rw [hg, mul_right_comm, mul_inv_cancel, one_mul, zpow_zero, one_mul]
    · have : sgnAct 3 R' (u g).right = thetaAut 3 R' := by simp [sgnAct, hs]
      rw [this, hth, inv_inv, htor, GeneralLinearGroup.map_det] at hg
      rw [hg]
      generalize wt1 0 + wt1 1 + wt1 2 = w
      rw [show -(2 * w) = -w + -w by ring, _root_.zpow_add, _root_.zpow_neg]
      simp only [_root_.mul_inv_rev]
      ac_rfl
  have e : ∀ φ : R →ₐ[O] R', φ (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) = ((Units.map (φ : R →+* R') (GeneralLinearGroup.det (u g).left)⁻¹ : R'ˣ) : R') := fun φ => rfl
  rw [e f', e f, key, Units.val_mul]

theorem UpperTheory.V.UnitaryThreeInertia.existsUnique_isPtHom :
    ∀ {O R Γ K : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [Group Γ] [CommRing K] [Algebra O K] (u : Γ →* GG 3 R) (ξ : Sring O u →ₐ[O] K), ∃! r, IsPtHom u ξ r := by
  intro O R Γ K _ _ _ _ _ _ _ u ξ
  have hmem : ∀ g a b, (u g).mat a b ∈ Sring O u := fun g a b => ptMat._proof_1 u g a b
  have hinv : ∀ g a b, (((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b ∈ Sring O u := by
    intro g a b
    obtain ⟨j, hj⟩ := exists_weight_inv_det_left_mem_weight_piece (O := O) u g
    have hd : (((GeneralLinearGroup.det (u g).left)⁻¹ : Rˣ) : R) ∈ Sring O u := by
      show _ ∈ (⨆ j, wpart O u j)
      exact Submodule.mem_iSup_of_mem j hj
    let M' : Matrix (Fin 3) (Fin 3) (Sring O u) := fun a b => ⟨(u g).mat a b, hmem g a b⟩
    have hM : ((Sring O u).val : Sring O u →+* R).mapMatrix M' = ((u g).left : Matrix (Fin 3) (Fin 3) R) := by
      ext a b; rfl
    have hdet : ((u g).left : Matrix (Fin 3) (Fin 3) R).det = ((GeneralLinearGroup.det (u g).left : Rˣ) : R) :=
      (GeneralLinearGroup.val_det_apply _).symm
    rw [Matrix.coe_units_inv, Matrix.inv_def, hdet, Ring.inverse_unit, ← hM, ← RingHom.map_adjugate]
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (Sring O u).mul_mem hd (M'.adjugate a b).2
  have hinj : Function.Injective (((Sring O u).val : Sring O u →+* R).mapMatrix (m := Fin 3)) := by
    intro x y h
    ext a b
    exact congrFun (congrFun h a) b
  let large₂ : Γ → GL (Fin 3) (Sring O u) := fun g =>
    { val := Matrix.of fun a b => ⟨(u g).mat a b, hmem g a b⟩
      inv := Matrix.of fun a b => ⟨(((u g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b, hinv g a b⟩
      val_inv := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.val_inv using 2 <;> ext a b <;> rfl
      inv_val := by
        apply hinj
        rw [map_mul, map_one]
        convert (u g).left.inv_val using 2 <;> ext a b <;> rfl }
  have gmap_inj : Function.Injective (GG.map (m := 3) ((Sring O u).val : Sring O u →+* R)) := by
    intro x y h
    apply gg_ext
    · have := congrArg (fun z => z.right) h
      simpa [GG.map_right] using this
    · ext a b
      have := congrArg (fun z => z.mat a b) h
      simpa [GG.map_mat] using this
  let vf : Γ → GG 3 (Sring O u) := fun g => SemidirectProduct.mk (large₂ g) (u g).right
  have hv : ∀ g, GG.map ((Sring O u).val : Sring O u →+* R) (vf g) = u g := by
    intro g
    apply gg_ext
    · rw [GG.map_right]
    · ext a b
      rw [GG.map_mat]
      rfl
  let v : Γ →* GG 3 (Sring O u) :=
    { toFun := vf
      map_one' := gmap_inj (by rw [hv, map_one, map_one])
      map_mul' := fun x y => gmap_inj (by rw [map_mul, hv, hv, hv, map_mul]) }
  have h0 : IsPtHom u ξ ((GG.map (ξ : Sring O u →+* K)).comp v) := by
    intro g
    constructor
    · show (GG.map _ (vf g)).right = _
      rw [GG.map_right]
    · show (GG.map _ (vf g)).mat = _
      rw [GG.map_mat]
      ext a b
      rfl
  refine ⟨_, h0, fun r hr => MonoidHom.ext fun g => gg_ext ((hr g).1.trans (h0 g).1.symm) ((hr g).2.trans (h0 g).2.symm)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsWeightedEquationsPresentingKer
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private theorem coeff_single_mul {O σ : Type} [CommRing O] (i : σ) (a g : MvPowerSeries σ O)
    (hg : constantCoeff g = 0) :
    coeff (Finsupp.single i 1) (a * g) = constantCoeff a * coeff (Finsupp.single i 1) g := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, hg]

private noncomputable def pad {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) (n : ℕ) (k : Fin n) : FA O wt :=
  if h : k.val < b then mkF (f ⟨k.val, h⟩) (hf _) else 0

private theorem pad_ind {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) (n : ℕ) (k : Fin n)
    (P : FA O wt → Prop) (h0 : P 0) (h1 : ∀ i, P (mkF (f i) (hf i))) : P (pad f hf n k) := by
  unfold pad
  split_ifs
  · exact h1 _
  · exact h0

private theorem pad_range {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) {n : ℕ} (h : b ≤ n) (i : Fin b) :
    mkF (f i) (hf i) ∈ Set.range (pad f hf n) :=
  ⟨⟨i.val, lt_of_lt_of_le i.2 h⟩, by simp [pad]⟩

private theorem der_zero {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R) (ho : W.HasOrigin)
    (b : ℤ → ℕ) (f : (j : ℤ) → Fin (b j) → MvPowerSeries W.σ O) (hf : ∀ j i, f j i ∈ wtPart O W.wt j)
    (hk : RingHom.ker W.π = Ideal.span (⋃ j, Set.range (f j))) (j0 : ℤ) (n : ℕ) (hn : b j0 ≤ n)
    (N : Type) [AddCommGroup N] [Module O N] (d : W.σ → N) (hd : ∀ i, W.wt i ≠ j0 → d i = 0)
    (hF : ∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (pad (f j0) (hf j0) n k)) • d i = 0)
    (g : MvPowerSeries W.σ O) (hg : W.π g = 0) : ∑ i, coeff (Finsupp.single i 1) g • d i = 0 := by
  have hg' : g ∈ Ideal.span (⋃ j, Set.range (f j)) := hk ▸ hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, i, rfl⟩ := Set.mem_iUnion.1 hx
    by_cases hj : j = j0
    · subst hj
      obtain ⟨k, e⟩ := pad_range (f j) (hf j) hn i
      have := hF k
      rwa [e] at this
    · refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : W.wt v = j0
      · rw [hf j i _ (by simpa [Finsupp.weight_single, hv] using Ne.symm hj), zero_smul]
      · rw [hd v hv, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, add_smul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul a x hx ih =>
    have h0 : constantCoeff x = 0 := ho x (hk.ge hx)
    simp only [smul_eq_mul, coeff_single_mul _ a x h0, mul_smul, ← Finset.smul_sum, ih, smul_zero]

theorem UpperTheory.exists_weighted_equations_presenting_ker :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R), W.HasOrigin →
        ∀ (b : ℤ → ℕ) (f : (j : ℤ) → Fin (b j) → MvPowerSeries W.σ O), (∀ j i, f j i ∈ wtPart O W.wt j) →
        RingHom.ker W.π = Ideal.span (⋃ j, Set.range (f j)) → ∀ r s r' s' m : ℕ,
        b (-1) ≤ r + 1 → b (-2) ≤ s → b 1 ≤ r' → b 2 ≤ s' → b 0 ≤ m → (∀ j, j < -2 ∨ 2 < j → b j = 0) →
        ∃ Q : Eqns (Fgr O W.wt) (x0 O W.wt) r s r' s' m, Q.ideal = RingHom.ker (toA W) ∧
          ∀ (N : Type) [AddCommGroup N] [Module O N] (d : W.σ → N),
            (((∀ i, W.wt i ≠ -1 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.F k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0) ∧
            ((∀ i, W.wt i ≠ -2 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.G k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0) ∧
            ((∀ i, W.wt i ≠ 0 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.Z k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0)) := by
  intro O R _ _ _ W ho b f hf hk r s r' s' m h1 h2 h3 h4 h5 h6
  have hker : ∀ j i, W.π (f j i) = 0 := fun j i => by
    have : f j i ∈ RingHom.ker W.π := hk ▸ Ideal.subset_span (Set.mem_iUnion.2 ⟨j, i, rfl⟩)
    exact this
  have hmem : ∀ j n k, pad (f j) (hf j) n k ∈ Fgr O W.wt j := fun j n k =>
    pad_ind _ _ n k (· ∈ Fgr O W.wt j) (zero_mem _) fun i => mkF_mem _ _
  have hkA : ∀ j n, Set.range (pad (f j) (hf j) n) ⊆ RingHom.ker (toA W) := by
    rintro j n _ ⟨k, rfl⟩
    exact pad_ind _ _ n k (· ∈ RingHom.ker (toA W)) (zero_mem _) fun i => Subtype.ext (hker j i)
  refine ⟨⟨pad (f (-1)) (hf _) _, pad (f (-2)) (hf _) _, pad (f 1) (hf _) _, pad (f 2) (hf _) _,
    pad (f 0) (hf _) _, hmem _ _, hmem _ _, hmem _ _, hmem _ _, fun k => ⟨hmem _ _ _, ?_⟩⟩, ?_,
    fun N _ _ d => ⟨der_zero W ho b f hf hk _ _ h1 N d, der_zero W ho b f hf hk _ _ h2 N d,
      der_zero W ho b f hf hk _ _ h5 N d⟩⟩
  · exact pad_ind _ _ m k (fun y => x0 O W.wt y = 0) (map_zero _) fun i => by
      rw [weightedSeriesOrigin_apply]; exact ho _ (hker 0 i)
  · refine le_antisymm (Ideal.span_le.2 ?_) fun x hx => ?_
    · simp only [Set.union_subset_iff]
      exact ⟨⟨⟨⟨hkA _ _, hkA _ _⟩, hkA _ _⟩, hkA _ _⟩, hkA _ _⟩
    · have hx1 : ser x ∈ RingHom.ker W.π := congrArg Subtype.val (show toA W x = 0 from hx)
      rw [hk] at hx1
      have H := (homog_span O _ ℤ (WPres.free O W.wt) (Σ j : Finset.Icc (-2 : ℤ) 2, Fin (b j))
        (fun p => mkF (f p.1 p.2) (hf _ _)) (fun p => p.1) (fun p => mkF_mem _ _)).2 x
      refine Ideal.span_mono ?_ (H.1 (Ideal.span_mono ?_ hx1))
      · rintro _ ⟨⟨⟨j, hj⟩, i⟩, rfl⟩
        have hj' := Finset.mem_Icc.1 hj
        have : j = -1 ∨ j = -2 ∨ j = 1 ∨ j = 2 ∨ j = 0 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (Or.inl (Or.inl (Or.inl (pad_range _ _ h1 i))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr (pad_range _ _ h2 i))))
        · exact Or.inl (Or.inl (Or.inr (pad_range _ _ h3 i)))
        · exact Or.inl (Or.inr (pad_range _ _ h4 i))
        · exact Or.inr (pad_range _ _ h5 i)
      · intro y hy
        obtain ⟨j, i, rfl⟩ := Set.mem_iUnion.1 hy
        have hj : j ∈ Finset.Icc (-2 : ℤ) 2 := by
          by_contra hc
          have := h6 j (by rw [Finset.mem_Icc] at hc; omega)
          have := i.2
          omega
        exact ⟨⟨⟨j, hj⟩, i⟩, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.GradedMatrixMulInv
section
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section
variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜]

private theorem gr_mul {X Y : Matrix (Fin 3) (Fin 3) R} (hX : GrMat 𝒜 X) (hY : GrMat 𝒜 Y) :
    GrMat 𝒜 (X * Y) := by
  intro a b
  simp only [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have h := SetLike.GradedMul.mul_mem (hX a c) (hY c b)
  have e : wt a c + wt c b = wt a b := by simp only [wt]; ring
  rwa [e] at h

private theorem gr_one : GrMat 𝒜 (1 : Matrix (Fin 3) (Fin 3) R) := by
  intro a b
  by_cases h : a = b
  · subst h
    rw [Matrix.one_apply_eq]
    have e : wt a a = 0 := by simp [wt]
    rw [e]
    exact SetLike.GradedOne.one_mem
  · rw [Matrix.one_apply_ne h]
    exact zero_mem _

private theorem gr_pow {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) (n : ℕ) :
    GrMat 𝒜 ((g ^ n : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  induction n with
  | zero => rw [pow_zero]; exact gr_one 𝒜
  | succ n ih => rw [pow_succ, Units.val_mul]; exact gr_mul 𝒜 ih hg

private theorem gr_inv [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((g⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  have hn := orderOf_pos g
  have e : g⁻¹ = g ^ (orderOf g - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel hn, pow_orderOf_eq_one]
  rw [e]
  exact gr_pow 𝒜 hg _

private theorem gr_theta [Finite R] {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((theta g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rw [theta_val]
  have hi := gr_inv 𝒜 hg
  have key : ∀ (M : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
      (Jmat R 3 * Mᵀ * Jmat R 3) a b = M b.rev a.rev := by
    intro M a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Jmat, Fin.sum_univ_three, Fin.rev]
  intro a b
  rw [key]
  have e : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
  rw [← e]
  exact hi _ _

private theorem gr_act [Finite R] (s : ℤˣ) {g : GL (Fin 3) R} (hg : GrMat 𝒜 (g : Matrix (Fin 3) (Fin 3) R)) :
    GrMat 𝒜 ((sgnAct 3 R s g : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
  rcases Int.units_eq_one_or s with rfl | rfl
  · rw [sgnAct_one]; exact hg
  · rw [sgnAct_neg_one]; exact gr_theta 𝒜 hg

end

theorem UpperTheory.graded_matrix_mul_inv :
    ∀ {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [Finite R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (x y : GG 3 R), GrMat 𝒜 x.mat → GrMat 𝒜 y.mat → GrMat 𝒜 (x * y).mat ∧ GrMat 𝒜 (x⁻¹).mat := by
  intro O R _ _ _ _ 𝒜 _ x y hx hy
  unfold GG.mat at *
  constructor
  · rw [SemidirectProduct.mul_left, Units.val_mul]
    exact gr_mul 𝒜 hx (gr_act 𝒜 _ hy)
  · rw [SemidirectProduct.inv_left]
    exact gr_act 𝒜 _ (gr_inv 𝒜 hx)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LengthLeCotLenOfInjectiveTangentMap
section
open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private theorem coeff_single_mul' {O σ : Type} [CommRing O] (i : σ) (f g : MvPowerSeries σ O) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g + constantCoeff g * coeff (Finsupp.single i 1) f := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ]
  ring

private noncomputable def lin {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] : (σ → Q) →+ (FA O wt →ₗ[O] Q) where
  toFun v :=
    { toFun := fun f => ∑ i, coeff (Finsupp.single i 1) (ser f) • v i
      map_add' := fun f g => by
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a f => by
        simp [Finset.smul_sum, mul_smul] }
  map_zero' := by ext f; simp
  map_add' v w := by ext f; simp [Finset.sum_add_distrib]

private theorem lin_apply {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] (v : σ → Q) (f : FA O wt) :
    lin wt Q v f = ∑ i, coeff (Finsupp.single i 1) (ser f) • v i := rfl

private theorem lin_zA {O : Type} [CommRing O] {σ : Type} [Fintype σ] (wt : σ → ℤ)
    (Q : Type) [AddCommGroup Q] [Module O Q] (v : σ → Q) (i : σ) :
    lin wt Q v ((WPres.free O wt).zA i) = v i := by
  classical
  rw [lin_apply]
  have : ser ((WPres.free O wt).zA i) = (X i : MvPowerSeries σ O) := rfl
  rw [this, Finset.sum_eq_single i]
  · simp [coeff_X]
  · intro b _ hb
    rw [coeff_X, if_neg, zero_smul]
    intro h
    exact hb (Finsupp.single_left_injective one_ne_zero h)
  · simp

theorem UpperTheory.length_le_cotLen_of_injective_tangent_map :
    LemmaM' → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (ResidueField O)] (σ : Type) [Fintype σ] (wt : σ → ℤ) (j : ℤ), j ≠ 0 →
        ∀ (κ : Type) (F : κ → FA O wt), (∀ k, F k ∈ Fgr O wt j) → ∀ c : O, c ≠ 0 →
        ∀ (M : Type) [AddCommGroup M] [Module O M] (d : M →+ (σ → O ⧸ Ideal.span {c})), Function.Injective d →
        (∀ μ i, wt i ≠ j → d μ i = 0) → (∀ μ k, ∑ i, coeff (Finsupp.single i 1) (ser (F k)) • d μ i = 0) →
        Module.length O M ≤ cotLen (x0 O wt) (Fgr O wt) j F := by
  intro hM O _ _ _ _ σ _ wt j hj κ F hF c hc M _ _ d hd hwt hker
  classical
  let D : M →+ (FA O wt →ₗ[O] O ⧸ Ideal.span {c}) := (lin wt (O ⧸ Ideal.span {c})).comp d
  have hD : ∀ μ f, D μ f = ∑ i, coeff (Finsupp.single i 1) (ser f) • d μ i :=
    fun μ f => lin_apply wt _ (d μ) f
  have hwsingle : ∀ i : σ, (Finsupp.weight wt) (Finsupp.single i 1) = wt i := by
    intro i
    simp [Finsupp.weight_apply]
  refine hM O (FA O wt) ℤ (Fgr O wt) (x0 O wt) j ?_ κ F hF c hc M D ?_ ?_ ?_
  · intro f hf
    rw [weightedSeriesOrigin_apply, ← coeff_zero_eq_constantCoeff_apply]
    exact (mem_Fgr.mp hf) 0 (by simpa using hj.symm)
  · intro μ ν h
    apply hd
    funext i
    have h2 := congrArg (fun L : FA O wt →ₗ[O] O ⧸ Ideal.span {c} => L ((WPres.free O wt).zA i))
      (congrArg (fun T => T) h)
    simpa [D, lin_zA] using h2
  · intro μ k
    rw [hD]
    exact hker μ k
  · intro μ
    choose e he using fun i => Ideal.Quotient.mk_surjective (d μ i)
    let e' : σ → O := fun i => if wt i = j then e i else 0
    have he' : ∀ i, Ideal.Quotient.mk (Ideal.span {c}) (e' i) = d μ i := by
      intro i
      by_cases h : wt i = j
      · simp [e', h, he]
      · simp [e', h, hwt μ i h]
    refine ⟨lin wt O e', ?_, ?_, ?_⟩
    · intro f g
      have hs : ser (f * g) = ser f * ser g := rfl
      rw [lin_apply, lin_apply, lin_apply, weightedSeriesOrigin_apply, weightedSeriesOrigin_apply, hs]
      simp only [coeff_single_mul', smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    · intro i' hi' f hf
      rw [lin_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_cases h : wt i = j
      · have h0 : coeff (Finsupp.single i 1) (ser f) = 0 := by
          refine (mem_Fgr.mp hf) _ ?_
          rw [hwsingle, h]
          exact fun e => hi' e.symm
        rw [h0, zero_smul]
      · simp [e', h]
    · intro f
      rw [hD, lin_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← he' i, smul_eq_mul, map_mul, Algebra.smul_def]
      rfl
end

