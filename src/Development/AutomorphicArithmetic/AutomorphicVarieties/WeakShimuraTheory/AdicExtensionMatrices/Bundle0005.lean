import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0007

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.CoprodOpt
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private structure SxCOb (O : Type) [CommRing O] [IsLocalRing O] : Type 1 where
  R : Type
  [ring : CommRing R]
  [alg : Algebra O R]
  [co : IsCO O R]

attribute [local instance] SxCOb.ring SxCOb.alg SxCOb.co

theorem UpperTheory.V.Ws.sxCoprodOpt :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] (T : Type) [Finite T] (A : Type) [CommRing A] [Algebra Λ A] [IsCO Λ A] (B : T → Type) [∀ t, CommRing (B t)] [∀ t, Algebra Λ (B t)] [∀ t, IsCO Λ (B t)], ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (i : A →ₐ[Λ] R) (j : ∀ t, B t →ₐ[Λ] R), ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (fa : A →ₐ[Λ] R') (f : ∀ t, B t →ₐ[Λ] R'), ∃! g : R →ₐ[Λ] R', g.comp i = fa ∧ ∀ t, g.comp (j t) = f t := by
  intro Λ _ _ _ _ T _ A _ _ _ B _ _ _
  let F : Option T → Type := fun o => Option.elim o A B
  letI iR : ∀ o, CommRing (F o) := fun o =>
    match o with
    | none => (inferInstance : CommRing A)
    | some t => (inferInstance : CommRing (B t))
  letI iA : ∀ o, Algebra Λ (F o) := fun o =>
    match o with
    | none => (inferInstance : Algebra Λ A)
    | some t => (inferInstance : Algebra Λ (B t))
  have iC : ∀ o, IsCO Λ (F o) := fun o =>
    match o with
    | none => (inferInstance : IsCO Λ A)
    | some t => (inferInstance : IsCO Λ (B t))
  obtain ⟨R, iRR, iAl, iCO, j, hj⟩ := UpperTheory.V.CA.co_coprod Λ (Option T) F
  refine ⟨R, iRR, iAl, iCO, (j none : A →ₐ[Λ] R), fun t => (j (some t) : B t →ₐ[Λ] R), ?_⟩
  intro R' _ _ _ fa f
  let h : ∀ o, F o →ₐ[Λ] R' := fun o =>
    match o with
    | none => fa
    | some t => f t
  obtain ⟨g, hg, hu⟩ := hj R' h
  refine ⟨g, ⟨hg none, fun t => hg (some t)⟩, ?_⟩
  rintro g' ⟨h1, h2⟩
  apply hu
  intro o
  cases o with
  | none => exact h1
  | some t => exact h2 t
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PreLine
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem preLine_desc {Λ A T S : Type} [CommRing Λ] [CommRing A] [CommRing T] [CommRing S] [Algebra Λ A]
    [Algebra Λ T] [Algebra Λ S] (f : A →ₐ[Λ] S) (j : T →ₐ[Λ] S) (hj : Function.Injective j)
    (h : ∀ x, f x ∈ j.range) : ∃ g : A →ₐ[Λ] T, ∀ x, j (g x) = f x := by
  refine ⟨(AlgEquiv.ofInjective j hj).symm.toAlgHom.comp (f.codRestrict j.range h), fun x => ?_⟩
  have := congrArg Subtype.val ((AlgEquiv.ofInjective j hj).apply_symm_apply ⟨f x, h x⟩)
  exact this

theorem UpperTheory.V.Ws.sxPreLine :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a), Y.Line := by
  intro O Γ _ _ _ Φ Λ _ _ a Y Q hQ
  haveI h0 : IsCO Λ (ResidueField Λ) := (co_res Λ).1
  haveI hS : IsCO Λ (PowerSeries (ResidueField Λ)) := co_mvps Λ (ResidueField Λ) Unit
  obtain ⟨h1, h2⟩ := sxResLift Q hQ
  obtain ⟨f, hf⟩ := Y.univ _ _ _ h1 h2
  let j : (ResidueField Λ)[X] →ₐ[Λ] PowerSeries (ResidueField Λ) :=
    { (Polynomial.coeToPowerSeries.ringHom : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) with
      commutes' := fun x => by
        simp [Polynomial.algebraMap_apply, PowerSeries.algebraMap_apply] }
  have hj : Function.Injective j := Polynomial.coe_injective _
  have hf' : Y.P.map (f : Y.A →+* PowerSeries (ResidueField Λ)) = Q.map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) := hf
  have hr : ∀ g i l, f (Y.P.r g i l) = j (Q.r g i l) := fun g i l =>
    congrArg (fun P : PD Φ.ι Γ _ => P.r g i l) hf'
  have hn : ∀ v i l, f (Y.P.n v i l) = j (Q.n v i l) := fun v i l =>
    congrArg (fun P : PD Φ.ι Γ _ => P.n v i l) hf'
  have hB : f.comp (IsScalarTower.toAlgHom Λ Y.B Y.A) = (j.comp Polynomial.CAlgHom).comp (res Λ Y.B) := by
    refine Y.genB _ _ _ (fun g n => ?_) (fun v i s hs => ?_)
    · show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) =
        (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) ((C : ResidueField Λ →+* (ResidueField Λ)[X]) ((res Λ Y.B : Y.B →+* ResidueField Λ) _))
      rw [← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, ← coeff_map, Y.cp_map, Y.cp_red,
        ← Matrix.charpoly_map]
      have e : (Y.P.r g).map (f : Y.A →+* PowerSeries (ResidueField Λ)) = (Q.r g).map (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) := by
        ext1 i l
        exact hr g i l
      rw [e, Matrix.charpoly_map, sxCpRes _ Q hQ.res g]
      simp [Polynomial.map_prod]
    · show (f : Y.A →+* PowerSeries (ResidueField Λ)) (algebraMap Y.B Y.A _) = (j : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) (C (res Λ Y.B _))
      rw [Y.ψ_map v i s hs, Y.ψ_red v i s hs, ← (sxPdMap ((algebraMap Λ Y.A).comp a) _ Y.P).1, hf',
        (sxPdMap (C.comp ((residue Λ).comp a)) _ Q).1, hQ.res.char v s hs]
      rfl
  have hB' : ∀ b, f (algebraMap Y.B Y.A b) = j (C (res Λ Y.B b)) := fun b => DFunLike.congr_fun hB b
  have hrange : ∀ x, f x ∈ j.range := by
    intro x
    have hx : x ∈ Algebra.adjoin Y.B _ := Y.gen ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨_, (hr _ _ _).symm⟩
      · exact ⟨_, (hn _ _ _).symm⟩
    | algebraMap b => exact ⟨_, (hB' b).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨g, hg⟩ := preLine_desc f j hj hrange
  refine ⟨g, ?_, fun b hb => hj ?_⟩
  · refine PD.ext (MonoidHom.ext fun s => Matrix.ext fun i l => hj ?_) (funext fun v => Matrix.ext fun i l => hj ?_)
    · exact (hg _).trans (hr s i l)
    · exact (hg _).trans (hn v i l)
  · rw [hg, hB', (res_eq_zero_iff Λ Y.B b).2 hb, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PreOfCore
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isGSp_map' {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {ν : R} {X : M4 R}
    (h : IsGSp ν X) : IsGSp (f ν) (X.map f) := by
  unfold IsGSp at *
  ext i j
  have := congrArg f (congrFun (congrFun h i) j)
  simpa [Matrix.mul_apply, adj_apply, Matrix.one_apply, map_sum, apply_ite f] using this

open Classical in
theorem UpperTheory.V.Ws.sxPreOfCore :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ}, (∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v) → Core Φ a → Nonempty (Pre Φ a) := by
  intro O Γ _ _ _ Φ Λ _ _ a hMu X
  obtain ⟨A, cA, aA, n, hft, hgen, hfl, huniv⟩ := sxChart X.D
  letI aBA : Algebra X.B A := ((algebraMap X.A A).comp (algebraMap X.B X.A)).toAlgebra
  letI aLA : Algebra Λ A := ((algebraMap X.A A).comp (algebraMap Λ X.A)).toAlgebra
  have hB : ∀ b, algebraMap X.B A b = algebraMap X.A A (algebraMap X.B X.A b) := fun _ => rfl
  have hL : ∀ b, algebraMap Λ A b = algebraMap X.A A (algebraMap Λ X.A b) := fun _ => rfl
  haveI t1 : IsScalarTower X.B X.A A := IsScalarTower.of_algebraMap_eq hB
  haveI t2 : IsScalarTower Λ X.B A := IsScalarTower.of_algebraMap_eq fun x => by
    rw [hB, hL, ← IsScalarTower.algebraMap_apply Λ X.B X.A]
  let P : PD Φ.ι Γ A := ⟨mapRep (algebraMap X.A A) X.D.r, n⟩
  have hr : ∀ g, P.r g = (X.D.r g).map (algebraMap X.A A) := fun _ => rfl
  have hψ : ∀ v i (s : Φ.Gv v), P.ψ v i s = algebraMap X.A A (X.D.ψ v i s) := fun v i s => hfl.char v i s
  refine ⟨{ A := A, B := X.B, ft := X.ft.trans hft, P := P, pair := ?_, cont := ?_, gen := ?_, cp := X.cp,
            cp_map := ?_, cp_cont := X.cp_cont, cp_red := X.cp_red,
            ψ := fun v i s => if h : s ∈ Φ.Gv v then X.ψ v i ⟨s, h⟩ else 0,
            ψ_map := ?_, ψ_cont := ?_, ψ_red := ?_, genB := ?_, univ := ?_ }⟩
  · refine ⟨fun g => isGSp_map' (algebraMap X.A A) (X.rep.mult g), fun g hg => ?_, ?_, hfl.low, hfl.flag,
      fun v s hs i => ?_⟩
    · rw [hr, X.rep.kill g hg, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [hr]
      exact X.rep.nrm.map (map_zero _)
    · exact (hfl.char v i ⟨s, hMu v s hs⟩).trans (hfl.mu v i ⟨s, hMu v s hs⟩ hs)
  · intro i j
    refine adicCont_map (algebraMap X.A A) ?_ (X.cont i j)
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    exact Ideal.mem_map_of_mem (algebraMap X.B A) hb
  · rw [eq_top_iff]
    set S := Algebra.adjoin X.B ((Set.range fun x : Γ × Fin 4 × Fin 4 => P.r x.1 x.2.1 x.2.2) ∪
      Set.range fun x : Φ.ι × Fin 4 × Fin 4 => P.n x.1 x.2.1 x.2.2) with hS
    have h0 : ∀ x : X.A, algebraMap X.A A x ∈ S := by
      intro x
      have hx : x ∈ Algebra.adjoin X.B (Set.range fun x : Γ × Fin 4 × Fin 4 => X.D.r x.1 x.2.1 x.2.2) := by
        rw [X.gen]; trivial
      induction hx using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        exact Algebra.subset_adjoin (Or.inl ⟨y, rfl⟩)
      | algebraMap b => exact S.algebraMap_mem b
      | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact S.mul_mem hx hy
    rintro x -
    have hx : x ∈ Algebra.adjoin X.A (Set.range fun x : Φ.ι × Fin 4 × Fin 4 => n x.1 x.2.1 x.2.2) := by
      rw [hgen]; trivial
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Or.inr hx)
    | algebraMap b => exact h0 b
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | mul x y _ _ hx hy => exact S.mul_mem hx hy
  · intro g
    rw [hr, Matrix.charpoly_map, ← X.cp_map, Polynomial.map_map]
    rfl
  · intro v i s hs
    rw [dif_pos hs, hB, X.ψ_map]
    exact (hψ v i ⟨s, hs⟩).symm
  · intro v i
    simpa using X.ψ_cont v i
  · intro v i s hs
    rw [dif_pos hs]
    exact X.ψ_red v i ⟨s, hs⟩
  · intro R _ _ _ f f' h1 h2
    refine X.genB R f f' h1 fun v i s => ?_
    simpa using h2 v i s s.2
  · intro R _ _ _ c Q hc hQ
    obtain ⟨τ, D', hN, hDr, hF⟩ := sxPairNear c Q hc hQ
    obtain ⟨f, hf⟩ := X.univ R τ D' hN
    obtain ⟨F, hF1, hF2⟩ := huniv R (f : X.A →+* R) Q.n (hf ▸ hF)
    have hF3 : ∀ x, F (algebraMap X.A A x) = f x := fun x => RingHom.congr_fun hF1 x
    refine ⟨{ F with commutes' := fun x => ?_ }, ?_⟩
    · exact (hF3 _).trans (f.commutes x)
    · refine PD.ext ?_ (funext hF2)
      rw [← hDr, ← hf]
      ext g i j
      exact hF3 _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.QuotPowNil
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] {x y : R}
    (h : ∀ N : ℕ, x - y ∈ maximalIdeal R ^ (N + 1)) : x = y := by
  rw [IsHausdorff.eq_iff_smodEq (I := maximalIdeal R)]
  intro n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ N => exact h N

private theorem nontrivial_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ) :
    Nontrivial (R ⧸ maximalIdeal R ^ (N + 1)) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  apply (maximalIdeal.isMaximal R).ne_top
  exact top_le_iff.mp (h ▸ Ideal.pow_le_self (Nat.succ_ne_zero N))

private theorem isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ {R : Type} [CommRing R] [IsLocalRing R] (N : ℕ)
    [IsLocalRing (R ⧸ maximalIdeal R ^ (N + 1))] :
    IsNilpotent (maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1))) := by
  refine ⟨N + 1, ?_⟩
  have hle : maximalIdeal (R ⧸ maximalIdeal R ^ (N + 1)) ≤
      (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1))) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hu => hx (hu.map _)
  rw [Ideal.zero_eq_bot, eq_bot_iff]
  calc _ ≤ ((maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (N + 1)))) ^ (N + 1) :=
        Ideal.pow_right_mono hle _
    _ = ⊥ := by rw [← Ideal.map_pow, Ideal.map_quotient_self]

theorem UpperTheory.V.Ws.sxNearA :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {a : O →+* Λ} {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] {D : RD Φ R} {W : WPres Λ (ℤ × ℤ) R}, Φ.RUniv a D → D.Graded W → ∀ (D' : RD Φ W.A), D'.map (W.A.val : W.A →+* R) = D → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (τ : ℤ × ℤ →+ ℤ) (Q : RD Φ R'), Φ.Near a τ Q → ∃ f : W.A →ₐ[Λ] R', D'.map (f : W.A →+* R') = Q := by
  intro O Γ _ _ _ Φ Λ _ _ _ _ a R _ _ _ D W hU hG D' hD' R' _ _ _ τ Q hQ
  classical
  have hlev : ∀ N : ℕ, ∃ f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1),
      D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) := by
    intro N
    haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
    haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
      co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
    exact sxNearArt hU hG D' hD' _ τ _ (isNilpotent_maxIdeal_quotient_maxIdeal_pow_succ N)
      (sxNearMap (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))) hQ)
  have hval : ∀ s : W.σ, ∃ y : R', ∀ (N : ℕ) (f : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
      D'.map (f : W.A →+* _) = Q.map (Ideal.Quotient.mk (maximalIdeal R' ^ (N + 1))) →
      f (W.zA s) = Ideal.Quotient.mk _ y := by
    intro s
    rcases hG.var s with ⟨g, i, j, c, hz, -, -⟩ | ⟨v, i, t, c, hz, -⟩
    · refine ⟨Q.r g i j - algebraMap Λ R' c, fun N f hf => ?_⟩
      have e1 : D.r g i j = ((D'.r g i j : W.A) : R) := by rw [← hD']; rfl
      have hA : W.zA s = D'.r g i j - algebraMap Λ W.A c := by
        apply Subtype.ext
        change W.z s = _
        rw [hz, e1]
        rfl
      have e2 : f (D'.r g i j) = Ideal.Quotient.mk _ (Q.r g i j) :=
        congrArg (fun E => E.r g i j) hf
      rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
    · refine ⟨Q.ψ v i t - algebraMap Λ R' c, fun N f hf => ?_⟩
      have e1 : D.ψ v i t = ((D'.ψ v i t : W.A) : R) := by rw [← hD']; rfl
      have hA : W.zA s = D'.ψ v i t - algebraMap Λ W.A c := by
        apply Subtype.ext
        change W.z s = _
        rw [hz, e1]
        rfl
      have e2 : f (D'.ψ v i t) = Ideal.Quotient.mk _ (Q.ψ v i t) :=
        congrArg (fun E => E.ψ v i t) hf
      rw [hA, map_sub, AlgHom.commutes, e2, map_sub, Ideal.Quotient.mk_algebraMap]
  choose y hy using hval
  choose fN hfN using hlev
  have huniq : ∀ (N : ℕ) (f f' : W.A →ₐ[Λ] R' ⧸ maximalIdeal R' ^ (N + 1)),
      (∀ s, f (W.zA s) = f' (W.zA s)) → f = f' := by
    intro N f f' h
    haveI : Nontrivial (R' ⧸ maximalIdeal R' ^ (N + 1)) := nontrivial_quotient_maxIdeal_pow_succ N
    haveI : IsCO Λ (R' ⧸ maximalIdeal R' ^ (N + 1)) :=
      co_quot Λ R' _ (Ideal.Quotient.mkₐ Λ _) (Ideal.Quotient.mkₐ_surjective Λ _)
    exact sxExtA W hG.max _ f f' h
  haveI : IsAdicComplete (maximalIdeal R') R' := IsCO.complete (O := Λ)
  obtain ⟨F, hF⟩ := sxLimPt (Λ := Λ) (maximalIdeal R') W.zA y
    (fun N => ⟨fN N, fun s => hy s N (fN N) (hfN N)⟩) huniq
  have hcomp : ∀ N, (Ideal.Quotient.mkₐ Λ (maximalIdeal R' ^ (N + 1))).comp F = fN N := by
    intro N
    apply huniq
    intro s
    rw [AlgHom.comp_apply, hF s, hy s N (fN N) (hfN N)]
    rfl
  have hpt : ∀ (x : W.A) (q : R'), (∀ N, fN N x = Ideal.Quotient.mk _ q) → F x = q := by
    intro x q hx
    apply eq_of_forall_sub_mem_maxIdeal_pow_of_adicComplete
    intro N
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← hx N, ← hcomp N]
    rfl
  refine ⟨F, ?_⟩
  apply RD.ext
  · ext g i j
    exact hpt _ _ (fun N => congrArg (fun E => E.r g i j) (hfN N))
  · funext v i
    ext t
    exact hpt _ _ (fun N => congrArg (fun E => E.ψ v i t) (hfN N))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.UnivRep
section
open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem gsp_map_iff {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (ν : R) (X : M4 R) :
    IsGSp (f ν) (X.map f) ↔ ∀ i j, f ((adj X * X - ν • (1 : M4 R)) i j) = 0 := by
  unfold IsGSp
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  have h1 : (adj (X.map f) * X.map f) i j = f ((adj X * X) i j) := by
    simp only [Matrix.mul_apply, adj_apply, Matrix.map_apply, map_sum, map_mul, map_zsmul]
  have h2 : (f ν • (1 : M4 R')) i j = f ((ν • (1 : M4 R)) i j) := by
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_mul]
    split_ifs <;> simp
  rw [h1, h2, Matrix.sub_apply, map_sub, sub_eq_zero]

private theorem one_map_iff {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (X : M4 R) :
    X.map f = 1 ↔ ∀ i j, f ((X - 1) i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  have h2 : (1 : M4 R') i j = f ((1 : M4 R) i j) := by
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  rw [h2, Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]

private theorem gsp_diag {R : Type} [CommRing R] (ν : R) (d : Fin 4 → R) (h : ∀ i, d i * d i.rev = ν) :
    IsGSp ν (Matrix.diagonal d) := by
  have e : adj (Matrix.diagonal d) = Matrix.diagonal fun i => d i.rev := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.diagonal_apply]
  unfold IsGSp
  rw [e, Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · rw [mul_comm, h, mul_one]
  · simp

private theorem rep_closed {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {Λ : Type}
    [CommRing Λ] [IsLocalRing Λ] (a : O →+* Λ) (rbar : Γ →* M4 (ResidueField Λ)) :
    Cond.IsClosed (rbar := rbar) fun R' _ _ _ s => Φ.IsRep ((algebraMap Λ R').comp a) s.hom := by
  intro R _ _ _ r
  let S : Set R := {x | (∃ g i j, (adj (r.hom g) * r.hom g - algebraMap Λ R (a (Φ.ν g)) • (1 : M4 R)) i j = x) ∨
    (∃ g ∈ Φ.N, ∃ i j, (r.hom g - 1) i j = x) ∨ ∃ i j, i ≠ j ∧ r.hom Φ.g0 i j = x}
  refine ⟨Ideal.span S, fun R' _ _ _ f => ?_⟩
  have hs : (∀ x ∈ Ideal.span S, f x = 0) ↔ ∀ x ∈ S, f x = 0 :=
    ⟨fun h x hx => h x (Ideal.subset_span hx), fun h _ hx =>
      (Ideal.span_le (I := RingHom.ker f)).2 (fun y hy => h y hy) hx⟩
  have e1 : ∀ g, IsGSp (((algebraMap Λ R').comp a) (Φ.ν g)) ((r.map f).hom g) ↔
      ∀ i j, f ((adj (r.hom g) * r.hom g - algebraMap Λ R (a (Φ.ν g)) • (1 : M4 R)) i j) = 0 := fun g => by
    have := gsp_map_iff (f : R →+* R') (algebraMap Λ R (a (Φ.ν g))) (r.hom g)
    rw [RingHom.comp_apply, ← f.commutes]
    exact this
  have e2 : ∀ g, (r.map f).hom g = 1 ↔ ∀ i j, f ((r.hom g - 1) i j) = 0 := fun g =>
    one_map_iff (f : R →+* R') (r.hom g)
  rw [hs]
  constructor
  · rintro H x (⟨g, i, j, rfl⟩ | ⟨g, hg, i, j, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · exact (e1 g).1 (H.mult g) i j
    · exact (e2 g).1 (H.kill g hg) i j
    · exact H.nrm hij
  · intro H
    exact ⟨fun g => (e1 g).2 fun i j => H _ (Or.inl ⟨g, i, j, rfl⟩),
      fun g hg => (e2 g).2 fun i j => H _ (Or.inr (Or.inl ⟨g, hg, i, j, rfl⟩)),
      fun i j hij => H _ (Or.inr (Or.inr ⟨i, j, hij, rfl⟩))⟩

theorem UpperTheory.V.Ws.sxUnivRep :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {Φ : Fr O Γ} (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] {a : O →+* Λ}, Φ.Std l a → ∃ (R : Type) (_ : CommRing R) (_ : Algebra Λ R) (_ : IsCO Λ R) (r : Lift Λ (Φ.splitRD ((residue Λ).comp a)).r R), Represents (fun R' _ _ _ s => Φ.IsRep ((algebraMap Λ R').comp a) s.hom) r := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a h
  haveI := h.char
  have hd : ∀ g, (Φ.splitRD ((residue Λ).comp a)).r g =
      Matrix.diagonal fun i => ((residue Λ).comp a) (Φ.χ i g) := fun g => by
    show (Matrix.diagonal fun i => (Φ.χ i g : O)).map ((residue Λ).comp a) = _
    exact Matrix.diagonal_map (map_zero _)
  have hlc : IsLocallyConstant (Φ.splitRD ((residue Λ).comp a)).r := by
    have h4 : IsLocallyConstant fun g => fun i => ((residue Λ).comp a) (Φ.χ i g) := by
      have := (((h.ok.lc 0).prodMk (h.ok.lc 1)).prodMk ((h.ok.lc 2).prodMk (h.ok.lc 3))).comp
        fun x => ![x.1.1, x.1.2, x.2.1, x.2.2]
      convert this using 1
      funext g i
      fin_cases i <;> rfl
    have := h4.comp Matrix.diagonal
    convert this using 1
    funext g
    exact hd g
  have hk : ∀ n ∈ Φ.N, (Φ.splitRD ((residue Λ).comp a)).r n = 1 := fun n hn => by
    rw [hd]
    simp only [h.ok.kill n hn, Matrix.diagonal_one]
  obtain ⟨R, _, _, _, r, hr⟩ := sxUnivKill l (Φ.splitRD ((residue Λ).comp a)).r Φ.N h.phi hlc hk
  haveI := (co_res Λ).1
  let r₁ : Lift Λ (Φ.splitRD ((residue Λ).comp a)).r (ResidueField Λ) :=
    { hom := (Φ.splitRD ((residue Λ).comp a)).r
      cont := fun i j N => hlc.comp fun X => Ideal.Quotient.mk _ (X i j)
      red := fun g i j => by
        obtain ⟨x, hx⟩ := residue_surjective ((Φ.splitRD ((residue Λ).comp a)).r g i j)
        rw [← hx]
        exact (res Λ (ResidueField Λ)).commutes x }
  have h1 : Φ.IsRep ((algebraMap Λ (ResidueField Λ)).comp a) r₁.hom := by
    refine ⟨fun g => ?_, hk, ?_⟩
    · show IsGSp (((residue Λ).comp a) (Φ.ν g)) ((Φ.splitRD ((residue Λ).comp a)).r g)
      rw [hd]
      refine gsp_diag _ _ fun i => ?_
      rw [← map_mul, ← Units.val_mul, h.ok.mul]
    · show ((Φ.splitRD ((residue Λ).comp a)).r Φ.g0).IsDiag
      rw [hd]
      exact Matrix.isDiag_diagonal _
  obtain ⟨R', _, _, _, p, -, hp⟩ := univ_cond Λ Γ (Fin 4) _ R r _ _ hr (rep_closed Φ a _)
    ⟨ResidueField Λ, inferInstance, inferInstance, inferInstance, r₁, hk, h1⟩
  refine ⟨R', inferInstance, inferInstance, inferInstance, r.map p, fun C _ _ _ =>
    ⟨fun f => ((hp C).1 f).2, fun s hs => (hp C).2 s ⟨hs.kill, hs⟩⟩⟩
end

