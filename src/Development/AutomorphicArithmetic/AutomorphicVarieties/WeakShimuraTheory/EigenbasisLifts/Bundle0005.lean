import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0016
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0007
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0010
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0009
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0012
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0014
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Bundle0004

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.ConstOf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem res_iff {K : Type} [Field K] (a b : DualNumber K) :
    residue (DualNumber K) a = residue (DualNumber K) b ↔ a.fst = b.fst := by
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero, not_not, TrivSqZeroExt.fst_sub, sub_eq_zero]

private theorem flag_const {K H : Type} [Field K] [Infinite K] [Group H] {n : ℕ} (ρ : H →* GL (Fin n) K)
    (ρ' : H →* GL (Fin n) (DualNumber K)) (Q : GL (Fin n) (DualNumber K))
    (hQ : ∀ g, ρ' g = Q * W.pushRep (algebraMap _ (DualNumber K)) ρ g * Q⁻¹) (ψ : Fin n → H →* (DualNumber K)ˣ)
    (hinj : Function.Injective fun i => W.pushCh (dF K) (ψ i)) (h0 : W.HasFlag ρ fun i => W.pushCh (dF K) (ψ i))
    (h1 : W.HasFlag ρ' ψ) (i : Fin n) (s : H) : (ψ i s : DualNumber K).snd = 0 := by
  obtain ⟨g, hg⟩ := h0
  obtain ⟨g', hg'⟩ := h1
  let ι : K →+* DualNumber K := algebraMap _ _
  have hinf : Infinite (ResidueField (DualNumber K)) :=
    Infinite.of_injective _ ((residue (DualNumber K)).comp ι).injective
  have e : ∀ s, GeneralLinearGroup.map ι g * Q⁻¹ * ρ' s * (GeneralLinearGroup.map ι g * Q⁻¹)⁻¹ =
      GeneralLinearGroup.map ι (g * ρ s * g⁻¹) := fun s => by
    rw [hQ, map_mul, map_mul, map_inv]
    show _ * (_ * GeneralLinearGroup.map ι (ρ s) * _) * _ = _
    group
  have := (AlgebraTools.flag_chars_unique ρ' ψ (fun i => W.pushCh ι (W.pushCh (dF K) (ψ i))) g'
    (GeneralLinearGroup.map ι g * Q⁻¹) ((Cardinal.natCast_lt_aleph0).le.trans (Cardinal.aleph0_le_mk _))
    (fun a b hab => hinj (MonoidHom.ext fun t => Units.ext ((res_iff _ _).1 (DFunLike.congr_fun hab t))))
    (fun a t => (res_iff _ _).2 rfl) hg' (fun t => by
      rw [e]
      refine ⟨fun a b hab => ?_, fun a => ?_⟩
      · show ι ((g * ρ t * g⁻¹ : GL (Fin n) K) a b) = 0
        rw [(hg t).1 a b hab, map_zero]
      · show ι ((g * ρ t * g⁻¹ : GL (Fin n) K) a a) = _
        rw [(hg t).2 a]
        rfl)).1
  rw [congrFun this i]
  rfl

theorem UpperTheory.V.Ws.Eb.constOf :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x' : B.B →ₐ[c.O] DualNumber (PadicAlgCl l)) (ρ : F.G₀ →* GL (Fin n) (PadicAlgCl l)) (ρ' : F.G₀ →* GL (Fin n) (DualNumber (PadicAlgCl l))) (Q : GL (Fin n) (DualNumber (PadicAlgCl l))), B.u.D.map (x' : B.B →+* DualNumber (PadicAlgCl l)) = W.GDet.ofRep (W.mat ρ') → (∀ g, ρ' g = Q * W.pushRep (algebraMap _ (DualNumber (PadicAlgCl l))) ρ g * Q⁻¹) →
        (∀ v, Function.Injective fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i)) → (∀ v, W.HasFlag (ρ.comp (F.φ v)) fun i => W.pushCh ((dF _).comp (x' : B.B →+* DualNumber (PadicAlgCl l))) (B.u.ψ v i)) →
        (∀ v, W.HasFlag (ρ'.comp (F.φ v)) fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i)) → ∀ b, (x' b).snd = 0 := by
  intro l hl F c n r B x' ρ ρ' Q hD hQ hinj h0 h1
  obtain ⟨-, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  refine derZero c B.B x' _ (CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B) ?_
  rintro a (⟨i, g, -, -, rfl⟩ | ⟨v, i, g, rfl⟩)
  · have e1 := (AlgebraTools.Det.mapApi B.u.D (x' : B.B →+* DualNumber (PadicAlgCl l))).2.2.1 i g
    have e2 : W.GDet.ofRep (W.mat ρ') =
        (W.GDet.ofRep (W.mat ρ)).map (algebraMap _ (DualNumber (PadicAlgCl l))) := by
      rw [(AlgebraTools.Det.repApi _).2.2.2.2.2.1]
      refine (AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ Q⁻¹ fun y => ?_
      have : Q⁻¹ * ρ' y = W.pushRep (algebraMap _ (DualNumber (PadicAlgCl l))) ρ y * Q⁻¹ := by
        rw [hQ]; group
      exact congrArg Units.val this
    rw [hD, e2, (AlgebraTools.Det.mapApi _ _).2.2.1] at e1
    exact (congrArg TrivSqZeroExt.snd e1).symm
  · exact flag_const (ρ.comp (F.φ v)) (ρ'.comp (F.φ v)) Q (fun g => hQ _)
      (fun i => W.pushCh (x' : B.B →+* DualNumber (PadicAlgCl l)) (B.u.ψ v i)) (hinj v) (h0 v) (h1 v) i g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DerLam
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem derLam_dense {O : Type} [CommRing O] [IsLocalRing O] {σ : Type} [Finite σ] (n : ℕ)
    (a : MvPowerSeries σ O) :
    ∃ b ∈ Algebra.adjoin O (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)),
      a - b ∈ maximalIdeal (MvPowerSeries σ O) ^ n := by
  have hX : ∀ i : σ, (AlgHom.id O (MvPowerSeries σ O)) (MvPowerSeries.X i) ∈ maximalIdeal (MvPowerSeries σ O) := by
    intro i
    rw [AlgHom.id_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have key := GlobalTheory.algHom_sub_aeval_truncTotal_mem (AlgHom.id O (MvPowerSeries σ O)) hX n a
  simp only [AlgHom.id_apply] at key
  refine ⟨_, ?_, key⟩
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨_, rfl⟩

private theorem ptDer_eq_zero_of_vanish_on_X {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ)
    (x : MvPowerSeries (Fin N) c.O →ₐ[c.O] PadicAlgCl l)
    (D : MvPowerSeries (Fin N) c.O →ₗ[c.O] PadicAlgCl l) (hD : D ∈ PtDer x (PadicAlgCl l))
    (h0 : ∀ i, D (MvPowerSeries.X i) = 0) (a : MvPowerSeries (Fin N) c.O) : D a = 0 := by
  have hmul : ∀ f g, D (f * g) = x f • D g + x g • D f := hD
  have h1 : D 1 = 0 := by
    have h := hmul 1 1
    simp only [mul_one, map_one, one_smul] at h
    linear_combination (-1 : PadicAlgCl l) * h
  let y : MvPowerSeries (Fin N) c.O →ₐ[c.O] DualNumber (PadicAlgCl l) :=
    { toFun := fun f => TrivSqZeroExt.inl (x f) + TrivSqZeroExt.inr (D f)
      map_one' := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h1]
      map_mul' := by
        intro f g
        refine TrivSqZeroExt.ext ?_ ?_
        · simp
        · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
            add_zero, zero_add, hmul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
          ring
      map_zero' := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp
      map_add' := by
        intro f g
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp <;> ring
      commutes' := by
        intro r
        refine TrivSqZeroExt.ext ?_ ?_
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
            AlgHom.commutes]
          rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r]
          rfl
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
          rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r, map_smul, h1,
            smul_zero]
          show (0 : PadicAlgCl l) = r • (0 : PadicAlgCl l)
          rw [smul_zero] }
  haveI := co_mvps c.O c.O (Fin N)
  have key := derZero c (MvPowerSeries (Fin N) c.O) y (Set.range MvPowerSeries.X)
    (fun n b => derLam_dense n b) (by rintro _ ⟨i, rfl⟩; simp [y, h0]) a
  simpa [y] using key

theorem UpperTheory.V.Ws.Eb.derLam :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (x : MvPowerSeries (Fin N) c.O →ₐ[c.O] PadicAlgCl l), Module.rank (PadicAlgCl l) (PtDer x (PadicAlgCl l)) ≤ N := by
  intro l _ c N x
  let Φ : PtDer x (PadicAlgCl l) →ₗ[PadicAlgCl l] (Fin N → PadicAlgCl l) :=
    { toFun := fun D i => (D : MvPowerSeries (Fin N) c.O →ₗ[c.O] PadicAlgCl l) (MvPowerSeries.X i)
      map_add' := by
        intro D D'
        rfl
      map_smul' := by
        intro k D
        rfl }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro D hD
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    exact ptDer_eq_zero_of_vanish_on_X c N x D D.2 (fun i => congrFun hD i) a
  calc Module.rank (PadicAlgCl l) (PtDer x (PadicAlgCl l))
      ≤ Module.rank (PadicAlgCl l) (Fin N → PadicAlgCl l) := LinearMap.rank_le_of_injective Φ hinj
    _ = N := by simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DetAlg
section
section

open TensorProduct Polynomial UpperTheory.V.W UpperTheory.V.CA

private theorem da_ev {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E) (r : ℕ)
    (h : D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r) (b : A[X]) : D.D A[X] (1 + (b - 1) ⊗ₜ e) = b ^ r := by
  have h2 := D.nat A[X] A[X] (aeval (b - 1)) (1 + X ⊗ₜ e)
  rw [h] at h2
  simpa using h2

private theorem da_chi {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (e : E)
    (he : IsIdempotentElem e) (r s : ℕ) (h : D.D A[X] (1 + X ⊗ₜ e) = (1 + X) ^ r)
    (h' : D.D A[X] (1 + X ⊗ₜ (1 - e)) = (1 + X) ^ s) : D.chi e = X ^ s * (X - 1) ^ r := by
  rw [← da_ev D e r h, ← da_ev D (1 - e) s h', ← map_mul, Det.chi]
  congr 1
  rw [add_mul, mul_add, mul_add, Algebra.TensorProduct.tmul_mul_tmul, he.one_sub_mul_self, tmul_zero]
  simp only [one_mul, mul_one, tmul_sub, sub_tmul, ← Algebra.TensorProduct.one_def]
  abel

private theorem da_one {k : Type} [Field k] {r s m : ℕ} (h : (X : k[X]) ^ s * (X - 1) ^ r = (X - 1) * X ^ m) :
    r = 1 := by
  rcases r with _ | _ | r
  · simpa using congrArg (eval 1) h
  · rfl
  · have h0 : (X - 1 : k[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : k)
    rw [pow_succ' _ (r + 1), mul_left_comm] at h
    simpa using congrArg (eval 1) (mul_left_cancel₀ h0 h)

private theorem da_single {k : Type} [Field k] {n : ℕ} (i : Fin n) :
    ∃ m, (Matrix.single i i (1 : k)).charpoly = (X - 1) * X ^ m := by
  refine ⟨(Finset.univ.erase i).card, ?_⟩
  rw [← Matrix.diagonal_single, Matrix.charpoly_diagonal, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      Finset.prod_congr rfl (g := fun _ => X) (fun j hj => by
        simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj)]), Finset.prod_const]
  simp

private theorem da_coi {k : Type} [Field k] {n : ℕ} :
    CompleteOrthogonalIdempotents (fun i : Fin n => Matrix.single i i (1 : k)) := by
  refine ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩
  · simp [IsIdempotentElem]
  · simp [hij]
  · exact Matrix.sum_single_one

end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.detAlg :
    ∀ {A E k : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [Ring E] [Algebra A E] [Field k] [Algebra A k] [IsLocalHom (algebraMap A k)] {n : ℕ} (D : W.Det n A E) (π : E →ₐ[A] Matrix (Fin n) (Fin n) k), 1 ≤ n → D.IsCH → Function.Surjective π → (∀ x, (D.chi x).map (algebraMap A k) = (π x).charpoly) →
        ∃ φ : E →ₐ[A] Matrix (Fin n) (Fin n) A, (∀ x, (φ x).map (algebraMap A k) = π x) ∧ ∀ x, D.chi x = (φ x).charpoly := by
  intro A E k _ _ _ _ _ _ _ _ _ n D π hn hD hs hchi
  obtain ⟨hu, hint⟩ := CA.d_unit D hD
  have hunit : ∀ x, π x = 1 → IsUnit x := by
    intro x hx
    rw [hu, ← (CA.d_chi D x).2.2.2.1, W.Det.lam, Nat.sub_self]
    refine (isUnit_one.neg.pow n).mul ?_
    refine (isUnit_map_iff (algebraMap A k) _).1 ?_
    rw [← coeff_map, hchi, hx, coeff_zero_eq_eval_zero, isUnit_iff_ne_zero, Matrix.charpoly_one]
    simp
  have hk : ∀ x, π x = 0 → x ∈ Ring.jacobson E := by
    intro x hx
    rw [← Ideal.jacobson_bot, Ideal.mem_jacobson_iff]
    intro y
    obtain ⟨u, hu'⟩ := hunit (y * x + 1) (by simp [hx])
    refine ⟨↑u⁻¹, ?_⟩
    rw [Ideal.mem_bot, sub_eq_zero, ← u.inv_mul, hu', mul_add, mul_one, mul_assoc]
  obtain ⟨e, he, he'⟩ := CA.d_lift_idem π hs hk (fun i => Matrix.single i i (1 : k)) da_coi
  have hrank : ∀ i, D.D A[X] (1 + X ⊗ₜ e i) = 1 + X := by
    intro i
    obtain ⟨r, -, hr⟩ := CA.d_idem_rank D (e i) (he.idem i)
    obtain ⟨s, -, hs'⟩ := CA.d_idem_rank D (1 - e i) (he.idem i).one_sub
    obtain ⟨m, hm⟩ := da_single (k := k) i
    have h1 := hchi (e i)
    rw [da_chi D _ (he.idem i) r s hr hs', he', hm] at h1
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_X, Polynomial.map_one] at h1
    rw [hr, da_one h1, pow_one]
  have hc := fun i => CA.d_corner D (e i) hD (he.idem i) (hrank i) hn
  obtain ⟨φ, hφ, hφ'⟩ := matUnits π e hs he he' (fun i x => ⟨_, (hc i).1 x⟩) (fun i => (hc i).2.2.1)
  refine ⟨φ, hφ', fun x => ?_⟩
  have h := CA.d_gma_det D e hD he hrank A φ hφ A[X] ![X, -1] ![1, x]
  simp only [Fin.sum_univ_two, cons_val_zero, cons_val_one, TensorProduct.neg_tmul, map_one,
    ← sub_eq_add_neg] at h
  rw [W.Det.chi, h, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases hij : i = j
  · subst hij; simp [sub_eq_add_neg]
  · simp [hij]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DimLow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.dimLow :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] B) (J : Ideal B), ((Ideal.Quotient.mk J).comp (f : MvPowerSeries (Fin N) c.O →+* B)).Finite → (∀ a, a ≠ 0 → ∀ b, f a * b ∈ J → b ∈ J) →
        ∀ (x : B →ₐ[c.O] PadicAlgCl l) (p : Ideal B) [p.IsPrime], p = RingHom.ker x → J ≤ p → (N : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p ⧸ J.map (algebraMap B (Localization.AtPrime p))) := by
  intro l _ c N B _ _ _ f J hfin hreg x p _ hpx hJp
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_minimalPrimes_le hJp
  haveI hPprime : P.IsPrime := hP.1.1
  have hJP : J ≤ P := hP.1.2
  haveI : IsCO c.O (B ⧸ P) :=
    co_quot c.O B (B ⧸ P) (Ideal.Quotient.mkₐ c.O P) Ideal.Quotient.mk_surjective
  set g : MvPowerSeries (Fin N) c.O →ₐ[c.O] B ⧸ P := (Ideal.Quotient.mkₐ c.O P).comp f with hg
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    have hmem : f a ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    obtain ⟨y, hyJ, hy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hmem
    exact hyJ (hreg a hne y hy)
  have hfinP : (g : MvPowerSeries (Fin N) c.O →+* B ⧸ P).Finite := by
    have h2 := (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJP)).comp hfin
    convert h2 using 1
    exact RingHom.ext fun a => rfl
  have hxP : ∀ a ∈ P, x a = 0 := fun a ha => by
    have h3 : a ∈ RingHom.ker x := hpx ▸ hPp ha
    exact h3
  set xb : B ⧸ P →ₐ[c.O] PadicAlgCl l := Ideal.Quotient.liftₐ P x hxP with hxb
  have hxbmk : ∀ b, xb (Ideal.Quotient.mk P b) = x b := fun b => rfl
  have hht := htLow c N (B ⧸ P) g hinj hfinP xb
  set q : Ideal (B ⧸ P) := RingHom.ker xb with hq
  haveI : q.IsPrime := RingHom.ker_isPrime _
  have hpq : p = Ideal.comap (Ideal.Quotient.mk P) q := by
    ext b
    rw [hpx, Ideal.mem_comap, hq, RingHom.mem_ker, RingHom.mem_ker, hxbmk]
  let φ := Localization.localRingHom p q (Ideal.Quotient.mk P) hpq
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (s : B ⧸ P)
    have hs'p : s' ∈ p.primeCompl := by
      intro h
      apply s.2
      rw [hpq] at h
      rw [← hs']
      exact h
    refine ⟨IsLocalization.mk' (Localization.AtPrime p) r' ⟨s', hs'p⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  have hker : ∀ a ∈ J.map (algebraMap B (Localization.AtPrime p)), φ a = 0 := by
    intro a ha
    have hle : J.map (algebraMap B (Localization.AtPrime p)) ≤ RingHom.ker φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [Localization.localRingHom_to_map]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hJP hb), map_zero]
    exact hle ha
  have hψ := Ideal.Quotient.lift_surjective_of_surjective _ hker hφ
  have hdim := ringKrullDim_le_of_surjective _ hψ
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at hdim
  calc (N : WithBot ℕ∞) ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht
    _ ≤ _ := hdim
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.Factor
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem factor_chi {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (h : H) : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp

private theorem factor_abs {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : H →* GL (Fin n) A) (hn : 1 ≤ n) (hF : Full ρ)
    (hD : D.comap φ = W.GDet.ofRep (W.mat ρ)) :
    ∃ ρ₀ : G →* GL (Fin n) A, ρ₀.comp φ = ρ ∧ Full ρ₀ ∧ D = W.GDet.ofRep (W.mat ρ₀) := by
  have hchi : ∀ h, D.chi (MonoidAlgebra.single (φ h) 1) = (W.GDet.ofRep (W.mat ρ)).chi (MonoidAlgebra.single h 1) :=
    fun h => by rw [← hD, factor_chi]
  have hker : φ.ker ≤ ρ.ker := fun g hg => by
    have h0 := (trPlus ρ hF).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun h => by
      have e : (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single (h * g) 1) =
          (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn] at e
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, mul_sub, map_sub, Matrix.trace_sub,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at h0
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using h0
  let ρ₀ : G →* GL (Fin n) A := φ.liftOfSurjective hφ ⟨ρ, hker⟩
  have h0 : ∀ h, ρ₀ (φ h) = ρ h := fun h => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ h
  have hm : ∀ h, W.mat ρ₀ (φ h) = W.mat ρ h := fun h => congrArg Units.val (h0 h)
  refine ⟨ρ₀, MonoidHom.ext h0, ?_, CA.d_gext _ _ fun g i _ _ => ?_⟩
  · refine top_le_iff.1 (le_trans (le_of_eq (Eq.symm hF)) (Submodule.span_mono ?_))
    rintro _ ⟨h, rfl⟩
    exact ⟨φ h, hm h⟩
  · obtain ⟨h, rfl⟩ := hφ g
    unfold W.GDet.lam
    rw [hchi, (AlgebraTools.Det.repApi _).2.1, (AlgebraTools.Det.repApi _).2.1, hm]

theorem UpperTheory.V.Ws.Eb.factor :
    ∀ {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} (B : W.UniversalOrdinaryDeterminantRing r) (x : B.Pt) (ρ : G L Ω →* GL (Fin n) (PadicAlgCl l)), 1 ≤ n → x.IsRep ρ → Af.IsIrr (ρ.comp (cycBar L Ω l).ker.subtype) →
        ∃ ρ₀ : V.frame.G₀ →* GL (Fin n) (PadicAlgCl l), ρ₀.comp V.pr = ρ ∧ Full ρ₀ ∧ B.u.D.map (x : B.B →+* PadicAlgCl l) = W.GDet.ofRep (W.mat ρ₀) := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B x ρ hn hx hirr
  have hs : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hF : Full ρ := (AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => hirr.2.2 N le_top fun g v hv => hN g v hv
  exact factor_abs x.D V.pr hs ρ hn hF hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.RelKill
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem UpperTheory.V.Ws.Eb.relKill_single {A G : Type} [CommRing A] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) A)
    (g : G) (a : A) : W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.single g a) = a • W.mat ρ g := by
  ext i j
  simp [W.GDet.repAlg]

private theorem UpperTheory.V.Ws.Eb.relKill_push {R A G : Type} [CommRing R] [CommRing A] [Group G] {n : ℕ}
    (D : W.GDet n R G) (f : R →+* A) (ρ : G →* GL (Fin n) A) (hρ : Full ρ) (hD : D.map f = W.GDet.ofRep (W.mat ρ))
    (z : MonoidAlgebra R G) (hz : ∀ h : G, D.tr (MonoidAlgebra.single h 1 * z) = 0) :
    W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.mapRingHom G f z) = 0 := by
  refine (trPlus ρ hρ).1 (MonoidAlgebra.mapRingHom G f z) (fun g' => ?_)
  rw [← hD]
  have e : MonoidAlgebra.single g' (1 : A) * MonoidAlgebra.mapRingHom G f z =
      MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g' 1 * z) := by
    rw [map_mul]
    congr 1
    simp [MonoidAlgebra.mapRingHom]
  rw [e, W.GDet.tr.eq_1, (AlgebraTools.Det.mapApi D f).2.1 1, ← W.GDet.tr.eq_1, hz g', map_zero]

theorem UpperTheory.V.Ws.Eb.relKill :
    ∀ {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {c : Coef l} {n : ℕ} {r : W.Resid F c.O n} (B : W.UniversalOrdinaryDeterminantRing r) {A : Type} [CommRing A] [Algebra c.O A] (f : B.B →ₐ[c.O] A) (ρ : F.G₀ →* GL (Fin n) A), Full ρ → B.u.D.map (f : B.B →+* A) = W.GDet.ofRep (W.mat ρ) →
        (∀ v (g : Fin n → F.Gv v), (List.ofFn fun i => W.mat ρ (F.φ v (g i)) - algebraMap A _ (f (B.u.ψ v i (g i) : B.Bˣ))).prod = 0) ∧ ∀ u, ∀ g ∈ r.Ip u, ρ g = 1 := by
  intro l _ F c n r B A _ _ f ρ hρ hD
  have key : ∀ z : MonoidAlgebra B.B F.G₀, (∀ h : F.G₀, B.u.D.tr (MonoidAlgebra.single h 1 * z) = 0) →
      W.GDet.repAlg (W.mat ρ) A (MonoidAlgebra.mapRingHom F.G₀ (f : B.B →+* A) z) = 0 :=
    fun z hz => relKill_push B.u.D (f : B.B →+* A) ρ hρ hD z hz
  have hsing : ∀ (x : F.G₀) (b : B.B), W.GDet.repAlg (W.mat ρ) A
      (MonoidAlgebra.mapRingHom F.G₀ (f : B.B →+* A) (MonoidAlgebra.single x b)) = (f b) • W.mat ρ x := by
    intro x b
    rw [← relKill_single]
    congr 1
    simp [MonoidAlgebra.mapRingHom]
  refine ⟨fun v g => ?_, fun u g hg => ?_⟩
  · have h0 := key _ (B.u.Ord v g)
    rw [W.GFrame.oEl.eq_1, map_list_prod, map_list_prod, List.map_map, List.map_ofFn] at h0
    simpa only [Function.comp_def, map_sub, hsing, map_one, one_smul,
      Algebra.algebraMap_eq_smul_one] using h0
  · have h0 := key _ (fun h => B.u.I u g hg h)
    simp only [map_sub, hsing, map_one, one_smul, sub_eq_zero] at h0
    exact Units.ext h0
end

