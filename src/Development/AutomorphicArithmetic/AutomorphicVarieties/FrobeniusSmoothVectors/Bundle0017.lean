import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0008
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle0010

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCocv
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_gl {C : Type} [CommRing C] {n : ℕ} (a b c : GL (Fin n) C)
    (ha : UpT (a : Matrix (Fin n) (Fin n) C)) (hb : UpT (b : Matrix (Fin n) (Fin n) C))
    (hc : UpT (c : Matrix (Fin n) (Fin n) C)) :
    UpT (((a * b * c⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) - 1) := by
  have ha' : (a : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => ha i j h
  have hb' : (b : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => hb i j h
  have hc' : (c : Matrix (Fin n) (Fin n) C).BlockTriangular id := fun i j h => hc i j h
  letI : Invertible (c : Matrix (Fin n) (Fin n) C) := c.invertible
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hc'
  rw [← Matrix.coe_units_inv] at hi
  intro i j h
  have h1 := ((ha'.mul hb').mul hi) (show id j < id i from h)
  rw [Matrix.sub_apply, Units.val_mul, Units.val_mul, h1, Matrix.one_apply_ne (ne_of_gt h), sub_zero]

private theorem ring_id {R : Type} [Ring R] (o c x a w : R) (h : (1 + o) * (1 + c) = (1 + x) * (1 + a) * (1 + w))
    (h1 : o * c = 0) (h2 : x * a = 0) (h3 : x * w = 0) (h4 : a * w = 0) : o - (x - c + a) = w := by
  have e1 : (1 + o) * (1 + c) = 1 + o + c + o * c := by noncomm_ring
  have e2 : (1 + x) * (1 + a) * (1 + w) = 1 + x + a + w + x * a + x * w + a * w + x * a * w := by noncomm_ring
  rw [e1, e2, h1, h2, h3, h4] at h
  simp only [add_zero, zero_mul] at h
  have : o = 1 + x + a + w - c - 1 := by rw [← h]; abel
  rw [this]; abel

theorem UpperTheory.V.Fr.pr_cocv :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (u : RingHom.ker p →ₗ[O] ResidueField O), maximalIdeal C' * RingHom.ker p = ⊥ → ∀ v s t, (D.co u).1 (F.loc v s, F.loc v t) - dOne ((B.bar O).ad.comp (F.loc v)) ((D.co u).2 v) (s, t) ∈ (B.bar O).b v := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D u hK v s t
  obtain ⟨hom, ha, -, -⟩ := pr_omk hF O C' C p B D hK
  have hle : RingHom.ker p ≤ maximalIdeal C' := fun x hx => by
    rw [← res_eq_zero_iff O, ← res_map p, (RingHom.mem_ker).1 hx, map_zero]
  have ev := pr_evk O C' n (RingHom.ker p) u hK hle
  have hdel : ∀ s, F.del (F.loc v s) = 1 := fun s => (F.loc0 v s).2
  have hright : ∀ s, (B.r (F.loc v s)).right = 1 := fun s => (B.nu _).trans (hdel s)
  have hres : ∀ x : GL (Fin n) C', GeneralLinearGroup.map (res O C : C →+* ResidueField O)
      (GeneralLinearGroup.map (p : C' →+* C) x) = GeneralLinearGroup.map (res O C' : C' →+* ResidueField O) x := by
    intro x
    ext i j
    exact res_map p _
  have hval : ∀ x : GL (Fin n) C', (x : Matrix (Fin n) (Fin n) C').map (res O C') =
      ((GeneralLinearGroup.map (res O C' : C' →+* ResidueField O) x : GL (Fin n) (ResidueField O)) :
        Matrix (Fin n) (Fin n) (ResidueField O)) := fun x => rfl

  set T : Matrix (Fin n) (Fin n) C' :=
    ((D.t v s * D.t v t * (D.t v (s * t))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') - 1 with hT
  have hTup : UpT T := upT_gl _ _ _ (D.t_tri v s) (D.t_tri v t) (D.t_tri v _)
  have hTK : ∀ i j, T i j ∈ RingHom.ker p := by
    have e : GeneralLinearGroup.map (p : C' →+* C) (D.t v s * D.t v t * (D.t v (s * t))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, D.t_map, D.t_map, D.t_map, map_mul, map_mul, SemidirectProduct.mul_left,
        hright, sgnAct_one]
      group
    intro i j
    have e2 := congrArg (fun x : GL (Fin n) C => (x : Matrix (Fin n) (Fin n) C) i j) e
    rw [RingHom.mem_ker, hT, Matrix.sub_apply, map_sub]
    refine sub_eq_zero.2 (Eq.trans e2 ?_)
    by_cases h : i = j <;> simp [h, Matrix.one_apply]
  set gi : Matrix (Fin n) (Fin n) C' := (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hgi
  set g : Matrix (Fin n) (Fin n) C' := ((D.g v : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hg
  set ri : Matrix (Fin n) (Fin n) C' := (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hri
  set r : Matrix (Fin n) (Fin n) C' := ((D.r (F.loc v s) : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') with hr
  have hW1 : ∀ i j, (gi * T) i j ∈ RingHom.ker p := fun i j => (((ev T hTK).2.1 gi).1 i j).1
  have hW : ∀ i j, (gi * T * g) i j ∈ RingHom.ker p := fun i j => (((ev _ hW1).2.1 g).1 i j).2
  have hX1 : ∀ i j, (r * D.a v t) i j ∈ RingHom.ker p := fun i j => (((ev _ (ha v t)).2.1 r).1 i j).1
  have hX : ∀ i j, (r * D.a v t * ri) i j ∈ RingHom.ker p := fun i j => (((ev _ hX1).2.1 ri).1 i j).2
  have key : D.om (F.loc v s, F.loc v t) - (r * D.a v t * ri - D.a v (s * t) + D.a v s) = gi * T * g := by
    refine ring_id _ _ _ _ _ ?_ ((ev _ (hom _)).1 _ (ha v _)).1 ((ev _ hX).1 _ (ha v _)).1
      ((ev _ hX).1 _ hW).1 ((ev _ (ha v _)).1 _ hW).1
    have e1 : 1 + r * D.a v t * ri = ((D.r (F.loc v s) * (D.r (F.loc v t) * ((D.g v)⁻¹ * D.t v t * D.g v)⁻¹) *
        (D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') := by
      rw [SetLift.a, mul_sub, sub_mul, mul_one, hr, hri, Units.mul_inv, add_sub_cancel]
      rfl
    have e2 : 1 + gi * T * g = (((D.g v)⁻¹ * (D.t v s * D.t v t * (D.t v (s * t))⁻¹) * D.g v : GL (Fin n) C') :
        Matrix (Fin n) (Fin n) C') := by
      rw [hT, mul_sub, sub_mul, mul_one, hg, hgi, Units.inv_mul, add_sub_cancel]
      rfl
    rw [e1, e2]
    simp only [SetLift.om, SetLift.a, add_sub_cancel, hdel, sgnAct_one, ← Units.val_mul, map_mul]
    congr 1
    group
  have hXc : ∀ i j, (r * D.a v t * ri - D.a v (s * t)) i j ∈ RingHom.ker p := fun i j =>
    sub_mem (hX i j) (ha v _ i j)
  have hXca : ∀ i j, (r * D.a v t * ri - D.a v (s * t) + D.a v s) i j ∈ RingHom.ker p := fun i j =>
    add_mem (hXc i j) (ha v _ i j)
  have k2 := congrArg (fun M : Matrix (Fin n) (Fin n) C' => M.map (evK (RingHom.ker p) u)) key
  rw [((ev _ (hom _)).1 _ hXca).2.2, ((ev _ hXc).1 _ (ha v _)).2.1, ((ev _ hX).1 _ (ha v _)).2.2,
    ((ev _ hX1).2.1 ri).2.2, ((ev _ (ha v t)).2.1 r).2.1, ((ev _ hW1).2.1 g).2.2, ((ev _ hTK).2.1 gi).2.1,
    hr, hri, hg, hgi, hval, hval, hval, hval, map_inv, map_inv, ← hres, ← hres (D.g v), D.r_map, D.g_map] at k2
  have k3 : (D.co u).1 (F.loc v s, F.loc v t) - dOne ((B.bar O).ad.comp (F.loc v)) ((D.co u).2 v) (s, t) =
      ((((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) : Matrix (Fin n) (Fin n) (ResidueField O)) *
        T.map (evK (RingHom.ker p) u) * ((B.bar O).g v : Matrix (Fin n) (Fin n) (ResidueField O)) := by
    refine Eq.trans ?_ k2
    have e : ((B.bar O).ad.comp (F.loc v)) s ((D.co u).2 v t) =
        ((B.bar O).r (F.loc v s)).adFun ((D.a v t).map (evK (RingHom.ker p) u)) := rfl
    have e' : ((B.bar O).r (F.loc v s)).right = 1 := hright s
    simp only [dOne]
    rw [e, GG.adFun, if_pos e', add_sub_assoc, add_comm]
    rfl
  rw [k3]
  intro i j h
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
    Matrix.mul_one, Matrix.map_apply, hTup i j h, evK_of_mem u (zero_mem _)]
  exact map_zero u
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrCorrect
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem upT_mul {C : Type} [CommRing C] {n : ℕ} {M N : Matrix (Fin n) (Fin n) C} (hM : UpT M) (hN : UpT N) :
    UpT (M * N) := fun i j h => by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : c < i
  · rw [hM i c hc, zero_mul]
  · rw [hN c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]

theorem UpperTheory.V.Fr.pr_correct :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (B : Box F n C) (D : SetLift p B) (μ : ResidueField O →+ C'), IsSq O μ → (∀ c, p (μ c) = 0) → ∀ (β : F.Γ → Matrix (Fin n) (Fin n) (ResidueField O)) (Y : F.V → Matrix (Fin n) (Fin n) (ResidueField O)) (a : ∀ v, F.Gv v → Matrix (Fin n) (Fin n) (ResidueField O)), IsLocallyConstant β → (∀ x, D.om x = (dOne (B.bar O).ad β x).map μ) → (∀ v s, D.a v s = (a v s).map μ) → (∀ v s, a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v)) ∈ (B.bar O).b v) → ∃ B' : Box F n C', B'.Cont (maximalIdeal C') ∧ B'.map (p : C' →+* C) = B ∧ ∀ s, (B'.r s).mat = (1 - (β s).map μ) * (D.r s : Matrix (Fin n) (Fin n) C') := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p B D μ hμ hpμ β Y a hβ hom ha hb
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := pr_sqz O C' n μ hμ
  have hres : ∀ z : C', res O C (p z) = res O C' z := fun z => res_map p z
  let x : F.Γ → GG n C' := fun s => SemidirectProduct.mk (D.r s) (F.del s)
  have hK1 : ∀ s, GG.map (res O C' : C' →+* ResidueField O) (x s) = (B.bar O).r s := by
    intro s
    apply SemidirectProduct.ext
    · ext i j
      simp [x, GG.map, Box.map, hres, ← D.r_map s]
    · simp [x, GG.map, Box.map, B.nu]
  have hdl : ∀ v (s : F.Gv v), F.del (F.loc v s) = 1 := fun v s => MonoidHom.mem_ker.1 (F.loc0 v s).2
  have hAd : ∀ v (s : F.Gv v) M, (B.bar O).ad (F.loc v s) M =
      (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C').map (res O C') * M *
        (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') := by
    intro v s M
    show GG.adFun ((B.bar O).r (F.loc v s)) M = _
    rw [← hK1]
    clear hom ha hb he5 he4 he3 he2 he1 hβ hpμ hμ
    simp [GG.adFun, GG.mat, GG.map, x, hdl]
    congr 1
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.coe_units_inv]
    calc (((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') *
          (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C').map (res O C')
        = ((((D.r (F.loc v s))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C') *
            (D.r (F.loc v s) : Matrix (Fin n) (Fin n) C')).map (res O C') :=
          (Matrix.map_mul (f := (res O C').toRingHom)).symm
      _ = 1 := by
          rw [Units.inv_mul]
          exact Matrix.map_one _ (map_zero _) (map_one _)
  have hxmul : ∀ s t, x s * x t = GG.ofGL (e (dOne (B.bar O).ad β (s, t))) * x (s * t) := by
    intro s t
    have hu : D.r s * sgnAct n C' (F.del s) (D.r t) * (D.r (s * t))⁻¹ = e (dOne (B.bar O).ad β (s, t)) := by
      apply Units.ext
      rw [he1, ← hom (s, t)]
      simp [SetLift.om]
    apply SemidirectProduct.ext
    · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_left, ← hu]
      simp [x]
    · simp [x]
  have hcomm : ∀ s X, x s * GG.ofGL (e X) = GG.ofGL (e ((B.bar O).ad s X)) * x s := by
    intro s X
    rw [he5 (x s) X, hK1 s]
    rfl
  let R' : F.Γ → GG n C' := fun s => GG.ofGL (e (-β s)) * x s
  have hmul : ∀ s t, R' (s * t) = R' s * R' t := by
    intro s t
    symm
    calc R' s * R' t = GG.ofGL (e (-β s)) * (x s * GG.ofGL (e (-β t))) * x t := by
          simp only [R', mul_assoc]
      _ = GG.ofGL (e (-β s)) * GG.ofGL (e ((B.bar O).ad s (-β t))) * (x s * x t) := by
          rw [hcomm]
          simp only [mul_assoc]
      _ = GG.ofGL (e (-β s)) * GG.ofGL (e ((B.bar O).ad s (-β t))) *
            GG.ofGL (e (dOne (B.bar O).ad β (s, t))) * x (s * t) := by
          rw [hxmul]
          simp only [mul_assoc]
      _ = GG.ofGL (e (-β s + (B.bar O).ad s (-β t) + dOne (B.bar O).ad β (s, t))) * x (s * t) := by
          rw [he2, he2, map_mul, map_mul]
      _ = R' (s * t) := by
          simp only [R']
          congr 3
          simp only [dOne, map_neg]
          abel
  let rr : F.Γ →* GG n C' := MonoidHom.mk' R' hmul
  have hneg : ∀ Z : Matrix (Fin n) (Fin n) (ResidueField O), (-Z).map μ = -(Z.map μ) := by
    intro Z
    ext i j
    simp
  have hpe : ∀ X, GeneralLinearGroup.map (p : C' →+* C) (e X) = 1 := by
    intro X
    ext i j
    simp only [GeneralLinearGroup.map_apply, he1, Matrix.add_apply, Matrix.map_apply, Units.val_one, map_add]
    have h0 : (p : C' →+* C) (μ (X i j)) = 0 := hpμ _
    rw [h0, add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hconj : ∀ (A : GL (Fin n) C') X, A * e X * A⁻¹ =
      e ((A : Matrix (Fin n) (Fin n) C').map (res O C') * X * ((A⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) := by
    intro A X
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, he1, he1, mul_add, mul_one, add_mul, Units.mul_inv, (he4 _ X).1, (he4 _ _).2]
  have hGbar : ∀ v, ((B.bar O).g v : Matrix (Fin n) (Fin n) (ResidueField O)) =
        (D.g v : Matrix (Fin n) (Fin n) C').map (res O C') ∧
      (((B.bar O).g v)⁻¹ : GL (Fin n) (ResidueField O)) =
        (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C') := by
    intro v
    constructor
    · ext i j
      simp [Box.map, ← D.g_map v, hres]
    · ext i j
      simp [Box.map, ← D.g_map v, hres, ← map_inv]
  refine ⟨{ r := rr, nu := ?_, g := fun v => D.g v * e (-(Y v)), tri := ?_ }, ?_, ?_, ?_⟩
  · intro s
    show (GG.ofGL (e (-β s)) * x s).right = F.del s
    simp [x]
  · intro v s
    show UpT ((↑(D.g v * e (-(Y v))) : Matrix (Fin n) (Fin n) C') * (R' (F.loc v s)).mat *
      (((D.g v * e (-(Y v)))⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C'))
    have hr : D.r (F.loc v s) = e (a v s) * ((D.g v)⁻¹ * D.t v s * D.g v) := by
      rw [← mul_inv_eq_iff_eq_mul]
      apply Units.ext
      rw [he1, ← ha v s]
      simp [SetLift.a]
    have hmat : (R' (F.loc v s)).mat = ↑(e (-β (F.loc v s)) * D.r (F.loc v s)) := by
      simp [R', GG.mat, x]
    have h1 : D.r (F.loc v s) * e (Y v) * (D.r (F.loc v s))⁻¹ = e ((B.bar O).ad (F.loc v s) (Y v)) := by
      rw [hconj, hAd]
    have hX : e (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) =
        e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) * e (a v s) := by
      rw [← he2, ← he2, ← he2]
      congr 1
      abel
    have key : D.g v * e (-(Y v)) * (e (-β (F.loc v s)) * D.r (F.loc v s)) * (D.g v * e (-(Y v)))⁻¹ =
        e ((D.g v : Matrix (Fin n) (Fin n) C').map (res O C') *
          (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) *
          (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) * D.t v s := by
      rw [← hconj, hX]
      calc D.g v * e (-(Y v)) * (e (-β (F.loc v s)) * D.r (F.loc v s)) * (D.g v * e (-(Y v)))⁻¹
          = D.g v * e (-(Y v)) * e (-β (F.loc v s)) *
              (D.r (F.loc v s) * e (Y v) * (D.r (F.loc v s))⁻¹) * D.r (F.loc v s) * (D.g v)⁻¹ := by
            rw [_root_.mul_inv_rev, he3, neg_neg]
            group
        _ = D.g v * e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) *
              (e (a v s) * ((D.g v)⁻¹ * D.t v s * D.g v)) * (D.g v)⁻¹ := by
            rw [h1, ← hr]
        _ = D.g v * (e (-(Y v)) * e (-β (F.loc v s)) * e ((B.bar O).ad (F.loc v s) (Y v)) * e (a v s)) *
              (D.g v)⁻¹ * D.t v s := by
            group
    have hW : UpT ((D.g v : Matrix (Fin n) (Fin n) C').map (res O C') *
          (a v s - (β (F.loc v s) - ((B.bar O).ad (F.loc v s) (Y v) - Y v))) *
          (((D.g v)⁻¹ : GL (Fin n) C') : Matrix (Fin n) (Fin n) C').map (res O C')) := by
      rw [← (hGbar v).1, ← (hGbar v).2]
      exact hb v s
    rw [hmat, ← Units.val_mul, ← Units.val_mul, key, Units.val_mul, he1]
    apply upT_mul _ (D.t_tri v s)
    intro i j hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij), Matrix.map_apply, hW i j hij, map_zero, add_zero]
  · intro i j N
    have hB : IsLocallyConstant fun s =>
        (D.r s : Matrix (Fin n) (Fin n) C').map (Ideal.Quotient.mk (maximalIdeal C' ^ N)) := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro s0
      have hall : ∀ᶠ s in nhds s0, ∀ a b,
          Ideal.Quotient.mk (maximalIdeal C' ^ N) ((D.r s : Matrix (Fin n) (Fin n) C') a b) =
            Ideal.Quotient.mk (maximalIdeal C' ^ N) ((D.r s0 : Matrix (Fin n) (Fin n) C') a b) :=
        Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b =>
          (IsLocallyConstant.iff_eventually_eq _).1 (D.r_cont a b N) s0
      filter_upwards [hall] with s hs
      ext a b
      exact hs a b
    have hA := hβ.comp (fun Z =>
      ((1 : Matrix (Fin n) (Fin n) C') + (-Z).map μ).map (Ideal.Quotient.mk (maximalIdeal C' ^ N)))
    have hM := (IsLocallyConstant.comp₂ hA hB (· * ·)).comp (fun M => M i j)
    convert hM using 1
    funext s
    simp only [Function.comp_apply]
    rw [← Matrix.map_mul, Matrix.map_apply]
    congr 1
    show (R' s).mat i j = _
    simp [R', GG.mat, x, he1]
  · apply Box.ext
    · apply MonoidHom.ext
      intro s
      apply SemidirectProduct.ext
      · show GeneralLinearGroup.map (p : C' →+* C) (R' s).left = (B.r s).left
        simp [R', x, hpe, D.r_map]
      · show (R' s).right = (B.r s).right
        simp [R', x, B.nu]
    · funext v
      show GeneralLinearGroup.map (p : C' →+* C) (D.g v * e (-(Y v))) = B.g v
      rw [map_mul, hpe, mul_one, D.g_map]
  · intro s
    show (R' s).mat = _
    simp [R', GG.mat, x, he1, hneg, sub_eq_add_neg]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrNorm
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Fr

section SlopeTestRemainingChoices

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {C C' : Type} [CommRing C] [CommRing C']

private theorem conj_left {G : Type} [Group G] (h : GL (Fin n) C) (r : G →* GG n C) (s : G) :
    (conjBy h r s).left = h * (r s).left * sgnAct n C (r s).right h⁻¹ := by
  simp [conjBy, GG.ofGL, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.mul_right, mul_assoc]

private theorem conj_right {G : Type} [Group G] (h : GL (Fin n) C) (r : G →* GG n C) (s : G) :
    (conjBy h r s).right = (r s).right := by
  simp [conjBy, GG.ofGL, MulAut.conj_apply, SemidirectProduct.mul_right]

private theorem conj_mat {G : Type} [Group G] (h : GL (Fin n) C) (r : G →* GG n C) (s : G) (hs : (r s).right = 1) :
    (conjBy h r s).mat = (h : Matrix (Fin n) (Fin n) C) * (r s).mat *
      ((h⁻¹ : GL (Fin n) C) : Matrix (Fin n) (Fin n) C) := by
  unfold GG.mat
  rw [conj_left, hs, sgnAct_one, Units.val_mul, Units.val_mul]

private theorem conj_mul {G : Type} [Group G] (h h' : GL (Fin n) C) (r : G →* GG n C) :
    conjBy (h * h') r = conjBy h (conjBy h' r) := by
  apply MonoidHom.ext
  intro s
  simp [conjBy, MulAut.conj_apply, _root_.mul_inv_rev, mul_assoc]

private theorem frame_right_eq_one_of_G0 (B : Box F n C) (s : F.G0) : (B.r s).right = 1 := by
  exact (B.nu s).trans (MonoidHom.mem_ker.mp s.2)

private noncomputable def cj (h : GL (Fin n) C) (B : Box F n C) : Box F n C where
  r := conjBy h B.r
  nu s := (conj_right h B.r s).trans (B.nu s)
  g v := B.g v * h⁻¹
  tri v s := by
    have e : B.g v * h⁻¹ * (conjBy h B.r (F.loc v s)).left * (B.g v * h⁻¹)⁻¹ =
        B.g v * (B.r (F.loc v s)).left * (B.g v)⁻¹ := by
      have : (B.r (F.loc v s)).right = 1 := frame_right_eq_one_of_G0 B (F.loc0 v s)
      rw [conj_left, this, sgnAct_one]
      group
    have e' := congrArg Units.val e
    simp only [Units.val_mul] at e'
    have := B.tri v s
    unfold GG.mat at this ⊢
    rw [← e'] at this
    simpa only [Units.val_mul] using this

private theorem cj_map (f : C →+* C') (h : GL (Fin n) C) (B : Box F n C)
    (hh : (h : Matrix (Fin n) (Fin n) C).map f = 1) : (cj h B).map f = B.map f := by
  have hh' : Matrix.GeneralLinearGroup.map f h = 1 := Units.ext (by simpa using hh)
  have hg : GG.map f (GG.ofGL h) = 1 := by
    simp [GG.map, GG.ofGL, hh']
  apply Box.ext
  · apply MonoidHom.ext
    intro s
    show GG.map f (conjBy h B.r s) = GG.map f (B.r s)
    simp [conjBy, MulAut.conj_apply, map_mul, map_inv, hg]
  · funext v
    show Matrix.GeneralLinearGroup.map f (B.g v * h⁻¹) = Matrix.GeneralLinearGroup.map f (B.g v)
    simp [map_mul, map_inv, hh']

private theorem cj_cont (hd : IsOpen (F.del.ker : Set F.Γ)) (I : Ideal C) (h : GL (Fin n) C) (B : Box F n C)
    (hB : B.Cont I) : (cj h B).Cont I := by
  intro i j N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hdel : ∀ᶠ y in nhds x, F.del y = F.del x := by
    have hopen : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (F.del.ker : Set F.Γ)) :=
      hd.preimage (continuous_const.mul continuous_id)
    filter_upwards [hopen.mem_nhds (by simp)] with y hy
    have e : F.del (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at e
    exact e.symm
  have hM : ∀ᶠ y in nhds x, ∀ a b : Fin n,
      Ideal.Quotient.mk (I ^ N) ((B.r y).mat a b) = Ideal.Quotient.mk (I ^ N) ((B.r x).mat a b) := by
    rw [Filter.eventually_all]
    intro a
    rw [Filter.eventually_all]
    intro b
    exact (hB a b N).eventually_eq x
  filter_upwards [hdel, hM] with y hy hMy
  show Ideal.Quotient.mk (I ^ N) ((conjBy h B.r y).mat i j) = Ideal.Quotient.mk (I ^ N) ((conjBy h B.r x).mat i j)
  simp only [GG.mat] at hMy ⊢
  simp only [conj_left, B.nu, hy, Units.val_mul, Matrix.mul_apply, map_sum, map_mul, hMy]

private theorem of_unique {B : Box F n C} {ρ ρ' : NRep F n C} (h : B.Of ρ) (h' : B.Of ρ') : ρ = ρ' := by
  have e : ρ.r = ρ'.r := MonoidHom.ext fun s => (h.res s).symm.trans (h'.res s)
  apply NRep.ext e
  funext v i
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [← h.psi, ← h'.psi, e]

private theorem star_mat (hc : F.del F.c = -1) (B : Box F n C) (h1 : (B.r F.c).mat = 1) (g : F.G0) :
    (B.r (F.star g)).mat = Jmat C n * (B.r g).matᵀ * Jmat C n := by
  have t1 : theta (1 : GL (Fin n) C) = 1 := by
    simpa [sgnAct_neg_one] using map_one (sgnAct n C (-1))
  have hX : B.r F.c = ⟨1, -1⟩ := SemidirectProduct.ext (Units.ext (by simpa [GG.mat] using h1)) ((B.nu _).trans hc)
  have hY : B.r (g : F.Γ) = ⟨(B.r g).left, 1⟩ := SemidirectProduct.ext rfl (frame_right_eq_one_of_G0 B g)
  rw [show ((F.star g : F.G0) : F.Γ) = F.c * (g : F.Γ)⁻¹ * F.c⁻¹ from rfl, map_mul, map_mul, map_inv, map_inv, hX, hY]
  simp [GG.mat, SemidirectProduct.mul_left, SemidirectProduct.inv_left, map_inv, sgnAct_neg_one, sgnAct_one, theta_inv_val]
  rw [t1, t1, Units.val_one, mul_one, ← Matrix.coe_units_inv, theta_inv_val]

end SlopeTestRemainingChoices

end UpperTheory.V.Fr

theorem UpperTheory.V.Fr.pr_norm :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → ∀ (O : Type) [CommRing O] [IsLocalRing O], ∀ (C' : Type) [CommRing C'] [Algebra O C'] [IsCO O C'] (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (p : C' →ₐ[O] C) (ρ : NRep F n C) (B' : Box F n C'), maximalIdeal C' * RingHom.ker p = ⊥ → (ρ.bar O).Good → (B'.map (p : C' →+* C)).Of ρ → B'.Cont (maximalIdeal C') → ∃ (h : GL (Fin n) C') (ρ' : NRep F n C'), (h : Matrix (Fin n) (Fin n) C').map p = 1 ∧ ρ'.map (p : C' →+* C) = ρ ∧ ρ'.Cont (maximalIdeal C') ∧ (conjBy h B'.r F.c).mat = 1 ∧ ∀ s : F.G0, (conjBy h B'.r s).mat = ρ'.r s := by
  intro l _ k _ _ F C₀ n hF O _ _ C' _ _ _ C _ _ _ p ρ B' hmk hgood hof hcont
  have hkp : RingHom.ker p ≤ maximalIdeal C' := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [← res_eq_zero_iff O C', ← res_map p x, hx, map_zero]
  have hmat : ∀ (B : Box F n C') (s : F.Γ), ((B.map (p : C' →+* C)).r s).mat = (B.r s).mat.map p := fun B s => rfl
  have hx1 : (B'.r F.c).mat.map p = 1 := by
    rw [← hmat]
    exact hof.atc
  obtain ⟨h1, hh1, hc1⟩ := pr_norm1 O C' C p n (B'.r F.c) hmk hkp hgood.two
    (by rw [← map_mul, hF.c_sq, map_one]) ((B'.nu _).trans hF.del_c) hx1
  set B1 := cj h1 B' with hB1
  have hB1c : (B1.r F.c).mat = 1 := hc1
  have hB1map : B1.map (p : C' →+* C) = B'.map (p : C' →+* C) := cj_map _ h1 B' hh1
  have hB1cont : B1.Cont (maximalIdeal C') := cj_cont hF.del_open _ h1 B' hcont
  have hstar : ∀ g : F.G0, (B1.r (F.star g)).mat = Jmat C' n * (B1.r g).matᵀ * Jmat C' n :=
    star_mat hF.del_c B1 hB1c
  set Z := (B1.r F.g0).mat - (B1.r (F.star F.g0)).mat with hZ
  have hJ : ∀ X : Matrix (Fin n) (Fin n) C', Jmat C' n * (Jmat C' n * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
  have hθ : thetaLie Z = Z := by
    rw [hZ, hstar]
    simp only [thetaLie, Matrix.transpose_sub, Matrix.transpose_mul, Jmat_transpose, Matrix.transpose_transpose,
      Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hJ, Jmat_mul_Jmat, Matrix.mul_one]
    abel
  have hZp : Z.map p = ρ.r F.g0 - ρ.r (F.star F.g0) := by
    rw [hZ, Matrix.map_sub _ (fun a b => map_sub p a b), ← hmat, ← hmat, hB1map, hof.res, hof.res]
  have hoff : ∀ i j : Fin n, i ≠ j → p (Z i j) = 0 := by
    intro i j hij
    have e := congrFun (congrFun hZp i) j
    rw [Matrix.map_apply] at e
    rw [e]
    exact ρ.diag i j hij
  have hdist : ∀ i j : Fin n, i ≠ j → res O C' (Z i i) ≠ res O C' (Z j j) := by
    intro i j hij
    have e : ∀ a, p (Z a a) = (ρ.r F.g0 - ρ.r (F.star F.g0)) a a := fun a => by
      rw [← hZp, Matrix.map_apply]
    rw [← res_map p, ← res_map p, e i, e j]
    convert hgood.zd i j hij using 1 <;> simp [NRep.bar, NRep.map]
  obtain ⟨h2', hh2, hθ2, hdiag2⟩ := pr_norm2 O C' C p n Z hmk hkp hθ hoff hdist
  set B2 := cj h2' B1 with hB2
  have hB2c : (B2.r F.c).mat = 1 := by
    show (conjBy h2' B1.r F.c).mat = 1
    have hl : (B1.r F.c).left = 1 := Units.ext hB1c
    unfold GG.mat
    rw [conj_left, B1.nu, hF.del_c, hl, mul_one, map_inv, sgnAct_neg_one, hθ2, mul_inv_cancel, Units.val_one]
  have hB2diag : ∀ i j : Fin n, i ≠ j → ((B2.r F.g0).mat - (B2.r (F.star F.g0)).mat) i j = 0 := by
    intro i j hij
    have e1 := conj_mat h2' B1.r (F.g0 : F.Γ) (frame_right_eq_one_of_G0 B1 F.g0)
    have e2 := conj_mat h2' B1.r ((F.star F.g0 : F.G0) : F.Γ) (frame_right_eq_one_of_G0 B1 (F.star F.g0))
    show ((conjBy h2' B1.r F.g0).mat - (conjBy h2' B1.r (F.star F.g0)).mat) i j = 0
    rw [e1, e2, ← Matrix.sub_mul, ← Matrix.mul_sub]
    exact hdiag2 i j hij
  have hB2cont : B2.Cont (maximalIdeal C') := cj_cont hF.del_open _ h2' B1 hB1cont
  obtain ⟨ρ', hof', hcont'⟩ := pr_ofbox hF C' (maximalIdeal C') B2 hB2c hB2diag hB2cont
  refine ⟨h2' * h1, ρ', ?_, ?_, hcont', ?_, ?_⟩
  · show ((h2' : Matrix (Fin n) (Fin n) C') * h1).map (p : C' →+* C) = 1
    rw [Matrix.map_mul]
    exact (congrArg₂ (· * ·) hh2 hh1).trans (Matrix.one_mul 1)
  · have e := hof'.map (p : C' →+* C)
    rw [show B2.map (p : C' →+* C) = B'.map (p : C' →+* C) from (cj_map _ h2' B1 hh2).trans hB1map] at e
    exact of_unique e hof
  · rw [conj_mul]
    exact hB2c
  · intro s
    rw [conj_mul]
    exact hof'.res s
end

