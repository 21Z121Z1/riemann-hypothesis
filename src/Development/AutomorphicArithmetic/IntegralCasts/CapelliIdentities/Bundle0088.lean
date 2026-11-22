import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0028
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0029
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsLevi
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem sigma_sq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨_, _, _, hs⟩ := h
  let t : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply t.injective
  rw [hs, hs, star_star]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem sigR_sq {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (x : TensorProduct F A E) :
    sigR A σ (sigR A σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, h]
  | add a b ha hb => simp [ha, hb]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem sigR_incl {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) (e : E) : sigR A σ (inclR A e) = inclR A (σ e) := by
  simp [sigR, inclR]

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
private theorem dual_map {F E : Type} [Field F] [Field E] [Algebra F E] (A : Type) [CommRing A] [Algebra F A]
    (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E) :
    (Formalism.UG.cT (↑σ : E →+* E) X * J).map (inclR A) =
      ((X.map (inclR A)).map (sigR A σ)).transpose * JR A J := by
  rw [Matrix.map_mul]
  congr 1

theorem UpperTheory.Reformulated.B.Gka3.exists_levi :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : NumberField E]
      [inst_4 : Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}
      {X Y : Matrix (Fin n) (Fin r) E},
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
        Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J →
          GlobalTheory.SiegelSet.IsWittFrame σ J X Y →
            ∀ (A : Type) [inst_5 : CommRing A] [inst_6 : Algebra F A] [TopologicalSpace A] (p : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J)
              (B : Matrix (Fin r) (Fin r) (TensorProduct F A E)),
              B.BlockTriangular id →
                (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) p) :
                                 Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                      X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                    X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * B →
                  ∃ (m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J),
                    (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) m) :
                          Matrix (Fin n) (Fin n) (TensorProduct F A E)) =
                        GlobalTheory.CompanionTheory.KFin.leviMat σ J A X Y
                          (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) p) :
                            Matrix (Fin n) (Fin n) (TensorProduct F A E)) ∧
                      (∃ (d : Fin r → TensorProduct F A E),
                          (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E)) m) :
                                Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                              X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                            X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * Matrix.diagonal d) ∧
                        (∃ (d' : Fin r → TensorProduct F A E),
                            (↑((GlobalTheory.AdelicU.matHom A σ J : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                               m) :
                                  Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                                Y.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                              Y.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * Matrix.diagonal d') ∧
                          (∃ (B' : Matrix (Fin r) (Fin r) (TensorProduct F A E)),
                              B'.BlockTriangular id ∧
                                (∀ (i : Fin r), B' i i = (1 : TensorProduct F A E)) ∧
                                  (↑((GlobalTheory.AdelicU.matHom A σ J :
                                                       Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                                     (m⁻¹ * p)) :
                                        Matrix (Fin n) (Fin n) (TensorProduct F A E)) *
                                      X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) =
                                    X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E) * B') ∧
                            ∀ (z : Fin n → TensorProduct F A E),
                              ((Formalism.UG.cT (↑σ : E →+* E) X * J).map
                                              (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E)).mulVec
                                          z =
                                  (0 : Fin r → TensorProduct F A E) →
                                ∃ (a : Fin r → TensorProduct F A E),
                                  ((↑((GlobalTheory.AdelicU.matHom A σ J :
                                                           Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J → GL (Fin n) (TensorProduct F A E))
                                                         (m⁻¹ * p)) :
                                                     Matrix (Fin n) (Fin n) (TensorProduct F A E)) -
                                                   (1 : Matrix (Fin n) (Fin n) (TensorProduct F A E))).mulVec
                                      z =
                                    (X.map (⇑(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR A) : E → TensorProduct F A E)).mulVec a := by
  intro F E _ _ _ _ _ σ n J r X Y hCM hH hW A _ _ _ p B hB hpX
  obtain ⟨hXX, hYY, hXY, -⟩ := hW
  have hτ := sigR_sq A (sigma_sq hCM)
  let τ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR A σ
  let ι := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) A
  let JA := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) A J
  let Xa := X.map ι
  let Ya := Y.map ι
  let Xd := (Formalism.UG.cT (↑σ : E →+* E) X * J).map ι
  let Yd := (Formalism.UG.cT (↑σ : E →+* E) Y * J).map ι
  let g : Matrix (Fin n) (Fin n) (TensorProduct F A E) := ↑(GlobalTheory.AdelicU.matHom A σ J p)
  have hXd : Xd = (Xa.map τ).transpose * JA := dual_map A σ J X
  have hYd : Yd = (Ya.map τ).transpose * JA := dual_map A σ J Y
  have hJh : (JA.map τ).transpose = JA := by
    ext i j
    simp only [JA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR, Matrix.transpose_apply, Matrix.map_apply, τ]
    rw [sigR_incl]
    exact congrArg _ (hH.1 i j)
  have hJu : IsUnit JA.det := by
    have h1 : JA.det = ι J.det := (RingHom.map_det ι J).symm
    rw [h1]
    exact (isUnit_iff_ne_zero.mpr hH.2).map ι
  have hXX' : Xd * Xa = 0 := by
    simp only [Xd, Xa]
    rw [← Matrix.map_mul, hXX]
    simp
  have hYY' : Yd * Ya = 0 := by
    simp only [Yd, Ya]
    rw [← Matrix.map_mul, hYY]
    simp
  have hXY' : Xd * Ya = 1 := by
    simp only [Xd, Ya]
    rw [← Matrix.map_mul, hXY]
    simp
  have hgJ : (g.map τ).transpose * JA * g = JA := p.2
  obtain ⟨hYX, hYgX, hXg, hdiag⟩ := UpperTheory.hermitian_block_triangular τ hτ JA g Xa Ya B Xd Yd hJh hXd hYd hXY' hgJ hB hpX
  let d : Fin r → TensorProduct F A E := fun i => (Yd * g * Xa) i i
  let e : Fin r → TensorProduct F A E := fun i => (Xd * g * Ya) i i
  let P := 1 - Xa * Yd - Ya * Xd
  let M := GlobalTheory.CompanionTheory.KFin.leviMat σ J A X Y g
  have hM : M = (Xa * Matrix.diagonal d) * Yd + (Ya * Matrix.diagonal e) * Xd + P * g * P := rfl
  have hdB : ∀ i, d i = B i i := fun i => by simp only [d, hYgX]
  have hde : ∀ i, τ (e i) * d i = 1 := fun i => by rw [hdB]; exact hdiag i
  have hdu : ∀ i, IsUnit (d i) := fun i => IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hde i)
  obtain ⟨hu, hun, hmX, hmY⟩ := UpperTheory.hermitian_block_diagonal τ hτ JA g P M Xa Ya (Xd * g * Ya) Xd Yd d e hJh hJu hXd hYd
    hXX' hYY' hXY' hgJ hXg hde rfl hM
  obtain ⟨⟨B', hB1, hB2, hB3⟩, hz⟩ := UpperTheory.hermitian_projection_eq g P M Xa Ya B (Xd * g * Ya) Xd Yd d e hXX' hYY' hXY' hYX
    hB hpX hXg hdB hdu rfl hM hu
  let m : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA A σ J := ⟨Matrix.nonsingInvUnit M hu, hun⟩
  have hmv : (↑(GlobalTheory.AdelicU.matHom A σ J m) : Matrix (Fin n) (Fin n) (TensorProduct F A E)) = M := rfl
  have hinv : (↑(GlobalTheory.AdelicU.matHom A σ J (m⁻¹ * p)) : Matrix (Fin n) (Fin n) (TensorProduct F A E)) = M⁻¹ * g := by
    rw [map_mul, map_inv, Units.val_mul, Matrix.coe_units_inv, hmv]
  refine ⟨m, rfl, ⟨d, hmX⟩, ⟨e, hmY⟩, ⟨B', hB1, hB2, ?_⟩, ?_⟩
  · rw [hinv]
    exact hB3
  · intro z hzz
    rw [hinv]
    exact hz z hzz
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HasFixedVector
section
private lemma sum_shift {H M : Type} [Group H] [AddCommMonoid M] (K : Subgroup H)
    [Fintype (H ⧸ K)] (φ : H → M) (hφ : ∀ g, ∀ k ∈ K, φ (g * k) = φ g) (h : H) :
    ∑ q : H ⧸ K, φ (h * (q.out : H)) = ∑ q : H ⧸ K, φ (q.out : H) := by
  have key : ∀ q : H ⧸ K, φ (h * (q.out : H)) = φ ((h • q : H ⧸ K).out : H) := by
    intro q
    have e : ((h * (q.out : H) : H) : H ⧸ K) = h • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hk : (h * (q.out : H))⁻¹ * ((h • q : H ⧸ K).out : H) ∈ K := by
      apply QuotientGroup.eq.mp
      rw [QuotientGroup.out_eq']
      exact e
    have := hφ (h * (q.out : H)) _ hk
    rw [mul_inv_cancel_left] at this
    exact this.symm
  simp_rw [key]
  exact Equiv.sum_comp (MulAction.toPerm h) (fun q : H ⧸ K => φ (q.out : H))

private lemma core {G W V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup W] [_root_.Module ℂ W] [AddCommGroup V] [_root_.Module ℂ V]
    (σ : Representation ℂ G W) (τ : Representation ℂ G V)
    (hsm : ∀ x : W, IsOpen {g : G | σ g x = x})
    (hsup : ⨆ f : {f : W →ₗ[ℂ] V // ∀ (g : G) (x : W), f (σ g x) = τ g (f x)},
      LinearMap.range (f : W →ₗ[ℂ] V) = ⊤)
    {U : Subgroup G} (hU : IsCompact (U : Set G))
    {v : V} (hv : v ≠ 0) (hfix : ∀ u ∈ U, τ u v = v) :
    ∃ x : W, x ≠ 0 ∧ ∀ u ∈ U, σ u x = x := by
  classical
  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hvt : v ∈ ⨆ f : {f : W →ₗ[ℂ] V // ∀ (g : G) (x : W), f (σ g x) = τ g (f x)},
      LinearMap.range (f : W →ₗ[ℂ] V) := by rw [hsup]; trivial
  obtain ⟨c, hc, hcs⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hvt
  choose x hx using fun i => LinearMap.mem_range.mp (hc i)
  let stab : W → OpenSubgroup U := fun y =>
    { toSubgroup :=
       { carrier := {h : U | σ (h : G) y = y}
         mul_mem' := by
           intro a b ha hb
           simp only [Set.mem_setOf_eq] at ha hb ⊢
           simp [map_mul, Module.End.mul_apply, ha, hb]
         one_mem' := by simp
         inv_mem' := by
           intro a ha
           simp only [Set.mem_setOf_eq] at ha ⊢
           have : σ ((a : G)⁻¹) (σ (a : G) y) = y := by
             rw [← Module.End.mul_apply, ← map_mul]; simp
           rw [ha] at this
           simpa using this }
      isOpen' := (hsm y).preimage continuous_subtype_val }
  let K : OpenSubgroup U := c.support.inf (fun i => stab (x i))
  haveI : Finite (U ⧸ (K : Subgroup U)) := Subgroup.quotient_finite_of_isOpen _ K.isOpen
  haveI := Fintype.ofFinite (U ⧸ (K : Subgroup U))
  have hK : ∀ i ∈ c.support, ∀ k ∈ (K : Subgroup U), σ ((k : U) : G) (x i) = x i := by
    intro i hi k hk
    have hle : K ≤ stab (x i) := Finset.inf_le hi
    exact hle hk
  let A : W → W := fun y => ∑ q : U ⧸ (K : Subgroup U), σ (((q.out : U)) : G) y
  have hAfix : ∀ i ∈ c.support, ∀ u ∈ U, σ u (A (x i)) = A (x i) := by
    intro i hi u hu
    have := sum_shift (K : Subgroup U) (fun h : U => σ (h : G) (x i))
      (by
        intro g k hk
        simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
        rw [hK i hi k hk]) ⟨u, hu⟩
    simp only [A, map_sum]
    simpa [Subgroup.coe_mul, map_mul, Module.End.mul_apply] using this
  have hsum : ∑ i ∈ c.support, (i : {f : W →ₗ[ℂ] V // ∀ (g : G) (x : W), f (σ g x) = τ g (f x)}).1 (A (x i))
      = (Fintype.card (U ⧸ (K : Subgroup U)) : ℂ) • v := by
    have h1 : ∀ i ∈ c.support, i.1 (A (x i)) = ∑ q : U ⧸ (K : Subgroup U), τ (((q.out : U)) : G) (c i) := by
      intro i _
      simp only [A, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [i.2, hx i]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    have h2 : ∀ q : U ⧸ (K : Subgroup U), ∑ i ∈ c.support, τ (((q.out : U)) : G) (c i) = v := by
      intro q
      have hcs' : ∑ i ∈ c.support, c i = v := hcs
      rw [← map_sum, hcs']
      exact hfix _ (q.out : U).2
    simp only [h2, Finset.sum_const, Finset.card_univ]
    rw [Nat.cast_smul_eq_nsmul]
  have hne : (Fintype.card (U ⧸ (K : Subgroup U)) : ℂ) • v ≠ 0 := by
    refine smul_ne_zero ?_ hv
    exact_mod_cast Fintype.card_ne_zero
  rw [← hsum] at hne
  obtain ⟨i, hi, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  refine ⟨A (x i), ?_, hAfix i hi⟩
  intro h0
  exact hne' (by rw [h0, map_zero])

theorem UpperTheory.Reformulated.B.HasFixedVector.hasFixed :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {n : ℕ} {V : Type} [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module ℂ V] {ρ : Representation ℂ (GL (Fin n) (GlobalTheory.CuspRep.Af F)) V}
      {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)}
      {σ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w))},
      UpperTheory.V.Af.LocIsotypic ρ w σ →
        ∀ {U : Subgroup (GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w))},
          IsCompact (↑U : Set (GL (Fin n) (IsDedekindDomain.HeightOneSpectrum.adicCompletion F w))) →
            UpperTheory.V.Af.HasFixed (MonoidHom.comp ρ (GlobalTheory.CuspRep.locGL F n w)) U → UpperTheory.V.Af.HasFixed σ.ρ U := by
  intro F _ _ n V _ _ ρ w σ hiso U hU hfix
  obtain ⟨v, hv, hvfix⟩ := hfix
  obtain ⟨x, hx, hxfix⟩ := core σ.ρ (MonoidHom.comp ρ (GlobalTheory.CuspRep.locGL F n w))
    (by
      cases σ with
      | mk W ρ' hs hi => exact hs)
    (by simpa using hiso.2) hU hv hvfix
  exact ⟨x, hx, hxfix⟩
end

