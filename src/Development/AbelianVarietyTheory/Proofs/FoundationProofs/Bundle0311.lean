import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryThetaConstantEqInverseDeterminantPhase
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfGaussSign
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardMulCardOrth
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0307
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0219
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0075
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0076
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0284
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0055

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConstOfEquivariant
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui GlobalTheory.InertParity
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.EquivConst

theorem const_of_equivariant : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → (∀ (b : 𝓞 D.host.E), ∀ x ∈ A, scal D N N' (b : D.host.E) x ∈ A) → (∀ (b : D.host.E) x, u (scal D N N' b x) = scal D N N' b (u x)) → ∀ th ∈ ThSp D (tor0 D cc δ) A, (fun z => th (u.symm z)) = (sgn D ((A.map (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')).toAddMonoidHom).relIndex A) * ((‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ : ℂ) / LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')))) • Iop D (tor0 D cc δ) A A₁ th :=
  fun D => const_of_gaussSign D (GlobalTheory.HermGauss.gauss_sum_sign D)

end GlobalTheory.EquivConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetColumnOperationsModelParameter
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
namespace GlobalTheory.FrobStick

theorem det_column_alg {R : Type*} [CommRing R] (x e w q : Fin 3 → R) (ε r a₁ a₃ S D1 D2 D3 : R)
    (hq : ∀ i, q i * w i = 1) (hu : IsUnit (2 * ε ^ 4))
    (h : Matrix.det (Matrix.of fun i j => (![ε ^ 3 * x i ^ 3 * e i ^ 3,
      ε * e i ^ 3 * (x i * q i + ε ^ 2 * r * x i ^ 3),
      e i ^ 3 * q i * (a₁ * x i + a₃ * x i ^ 3 * w i - 2)] : Fin 3 → R) j) =
      2 * (ε * S) * (ε * D1) * (ε * D2) * (ε * D3)) :
    (x 0 ^ 3 * w 0 * (x 2 - x 1) + x 1 ^ 3 * w 1 * (x 0 - x 2) + x 2 ^ 3 * w 2 * (x 1 - x 0))
      * e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 = w 0 * w 1 * w 2 * S * D1 * D2 * D3 := by
  have hrow : ∀ i, e i ^ 3 * q i * (a₁ * x i + a₃ * x i ^ 3 * w i - 2)
      = e i ^ 3 * (a₁ * x i * q i + a₃ * x i ^ 3 - 2 * q i) := fun i => by
    linear_combination e i ^ 3 * a₃ * x i ^ 3 * hq i
  simp only [hrow] at h
  rw [Matrix.det_fin_three] at h
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
  have h2 : 2 * ε ^ 4 * (e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 *
      (x 0 ^ 3 * (q 1 * q 2) * (x 2 - x 1) + x 1 ^ 3 * (q 0 * q 2) * (x 0 - x 2)
        + x 2 ^ 3 * (q 0 * q 1) * (x 1 - x 0))) = 2 * ε ^ 4 * (S * D1 * D2 * D3) := by
    linear_combination h
  have h3 := hu.mul_left_cancel h2
  have h12 : q 1 * q 2 * (w 1 * w 2) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  have h02 : q 0 * q 2 * (w 0 * w 2) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  have h01 : q 0 * q 1 * (w 0 * w 1) = 1 := by
    rw [mul_mul_mul_comm, hq, hq, one_mul]
  linear_combination w 0 * w 1 * w 2 * h3
    - e 0 ^ 3 * e 1 ^ 3 * e 2 ^ 3 * (x 0 ^ 3 * w 0 * (x 2 - x 1) * h12
      + x 1 ^ 3 * w 1 * (x 0 - x 2) * h02 + x 2 ^ 3 * w 2 * (x 1 - x 0) * h01)

theorem det_column_ops : ∀ (p : ℕ) [Fact p.Prime] (E wq : PowerSeries ℂ_[p]) (ε r a₁ a₃ : ℂ_[p]) (s d₁ d₂ d₃ : MvPowerSeries (Fin 3) ℂ_[p]), ε ≠ 0 → PowerSeries.constantCoeff wq = 1 → MvPowerSeries.constantCoeff s = 0 → MvPowerSeries.constantCoeff d₁ = 0 → MvPowerSeries.constantCoeff d₂ = 0 → MvPowerSeries.constantCoeff d₃ = 0 → Matrix.det (Matrix.of fun i j => (PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) (![PowerSeries.C (ε ^ 3) * PowerSeries.X ^ 3 * E ^ 3, PowerSeries.C ε * E ^ 3 * (PowerSeries.X * wq⁻¹ + PowerSeries.C (ε ^ 2 * r) * PowerSeries.X ^ 3), E ^ 3 * wq⁻¹ * (PowerSeries.C a₁ * PowerSeries.X + PowerSeries.C a₃ * PowerSeries.X ^ 3 * wq - 2)] j) : MvPowerSeries (Fin 3) ℂ_[p])) = 2 * PowerSeries.subst s (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₁ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₂ (PowerSeries.C ε * PowerSeries.X * E) * PowerSeries.subst d₃ (PowerSeries.C ε * PowerSeries.X * E) → ((GL3Theta.Xv 0) ^ 3 * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 2 - GL3Theta.Xv 1) + (GL3Theta.Xv 1) ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 0 - GL3Theta.Xv 2) + (GL3Theta.Xv 2) ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (GL3Theta.Xv 1 - GL3Theta.Xv 0)) * PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) E ^ 3 = PowerSeries.subst (GL3Theta.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) wq * PowerSeries.subst (GL3Theta.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) wq * (s * PowerSeries.subst s E) * (d₁ * PowerSeries.subst d₁ E) * (d₂ * PowerSeries.subst d₂ E) * (d₃ * PowerSeries.subst d₃ E) := by
  intro p _ E wq ε r a₁ a₃ s d₁ d₂ d₃ hε hw hs h1 h2 h3 h
  have hC : ∀ (a : MvPowerSeries (Fin 3) ℂ_[p]), HasSubst a → ∀ c : ℂ_[p],
      PowerSeries.subst a (PowerSeries.C c : PowerSeries ℂ_[p]) = MvPowerSeries.C c := by
    intro a ha c
    rw [← coe_substAlgHom ha]
    exact (substAlgHom ha).commutes c
  have hlin : ∀ (a : MvPowerSeries (Fin 3) ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (PowerSeries.C ε * PowerSeries.X * E) =
        MvPowerSeries.C ε * (a * PowerSeries.subst a E) := by
    intro a ha
    have ha' : HasSubst a := HasSubst.of_constantCoeff_zero ha
    rw [subst_mul ha', subst_mul ha', hC a ha', subst_X ha', mul_assoc]
  have hX : ∀ i : Fin 3, HasSubst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) := fun i =>
    HasSubst.of_constantCoeff_zero (by simp [GL3Theta.Xv])
  rw [hlin s hs, hlin d₁ h1, hlin d₂ h2, hlin d₃ h3] at h
  refine det_column_alg (fun i => (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]))
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) E)
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) wq)
    (fun i => PowerSeries.subst (GL3Theta.Xv i : MvPowerSeries (Fin 3) ℂ_[p]) wq⁻¹)
    (MvPowerSeries.C ε) (MvPowerSeries.C r) (MvPowerSeries.C a₁) (MvPowerSeries.C a₃) _ _ _ _
    ?_ ?_ ?_
  · intro i
    rw [← subst_mul (hX i), PowerSeries.inv_mul_cancel _ (by rw [hw]; exact one_ne_zero),
      ← coe_substAlgHom (hX i), map_one]
  · have : (2 * MvPowerSeries.C ε ^ 4 : MvPowerSeries (Fin 3) ℂ_[p]) =
        MvPowerSeries.C (2 * ε ^ 4) := by
      rw [map_mul, map_pow, map_ofNat]
    rw [this]
    exact (IsUnit.mk0 _ (mul_ne_zero two_ne_zero (pow_ne_zero _ hε))).map _
  · rw [← h]
    congr 1
    ext1 i j
    have hCi := hC _ (hX i)
    have hXi := subst_X (R := ℂ_[p]) (hX i)
    rw [← coe_substAlgHom (hX i)] at hCi hXi
    simp only [Matrix.of_apply]
    rw [← coe_substAlgHom (hX i)]
    fin_cases j
    all_goals
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, map_mul, map_pow, map_add, map_sub, map_ofNat, hCi, hXi]

end GlobalTheory.FrobStick
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicUnitaryOfLocalFamilyAlmostAllTrivial
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalUnitaryGlue

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem exists_on_finset (γ : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ k : HA (Af F) σ J, (∀ v ∈ S, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = γ v) ∧
      ∀ v ∉ S, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => map_one _⟩
  | insert a S ha ih =>
    obtain ⟨k, h1, h2⟩ := ih
    have s1 : mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F a) (extH σ J (sgV a) (sgV_mul a) (γ a)) = γ a :=
      mapH_extH_self σ J _ _ _ (fun y => Pi.single_eq_same a y) _
    have s2 : ∀ w, w ≠ a →
        mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w) (extH σ J (sgV a) (sgV_mul a) (γ a)) = 1 :=
      fun w hw => mapH_extH_zero σ J _ _ _ (fun y => Pi.single_eq_of_ne hw y) _
    refine ⟨extH σ J (sgV a) (sgV_mul a) (γ a) * k, fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [s1, h2 _ ha, mul_one]
      · rw [s2 v (fun e => ha (e ▸ hv)), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, s2 v hv.1, h2 v hv.2, one_mul]

theorem exists_of_finite (γ : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (h : {v | γ v ≠ 1}.Finite) :
    ∃ k : HA (Af F) σ J, ∀ v, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = γ v := by
  obtain ⟨k, h1, h2⟩ := exists_on_finset σ J γ h.toFinset
  refine ⟨k, fun v => ?_⟩
  by_cases hv : v ∈ h.toFinset
  · exact h1 v hv
  · rw [h2 v hv]
    simpa [eq_comm] using hv

end Gen

theorem exists_finite_adelic : ∀ (D : D7) (V : HSp D) (γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram), {v | γ v ≠ 1}.Finite → ∃ k ∈ GfC V, ∀ v : HeightOneSpectrum (𝓞 D.host.F), (finMat D.sp.cm.sig V.gram k).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) = (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1 := by
  intro D V γ h
  obtain ⟨k, hk⟩ := exists_of_finite D.sp.cm.sig V.gram γ h
  refine ⟨ofFin D.sp.cm V k, ?_, fun v => ?_⟩
  · exact congrArg (HA.mat _ _ _) (projInf_ofFin D.sp.cm V k)
  · have e : finMat D.sp.cm.sig V.gram (ofFin D.sp.cm V k) = (HA.mat _ _ _ k).1 :=
      congrArg (fun x => (HA.mat _ _ _ x).1) (projFin_ofFin D.sp.cm V k)
    rw [e, ← hk v]
    rfl

end GlobalTheory.LocalUnitaryGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFiniteIdeleCharAtDeterminantRoots
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetRootChar

theorem circle_hom_factor {G B : Type} [Group G] [CommGroup B] (δ : G →* B) (m : G →* Circle)
    (h : ∀ g, δ g = 1 → m g = 1) : ∃ χ : B →* Circle, ∀ g, χ (δ g) = m g := by
  have hker : δ.rangeRestrict.ker ≤ m.ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    exact h g (congrArg Subtype.val hg)
  obtain ⟨χ, hχ⟩ := GlobalTheory.circle_hom_extend_of_injective δ.range.subtype Subtype.val_injective
    (δ.rangeRestrict.liftOfSurjective δ.rangeRestrict_surjective ⟨m, hker⟩)
  refine ⟨χ, fun g => ?_⟩
  have := hχ (δ.rangeRestrict g)
  rw [MonoidHom.liftOfSurjective, MonoidHom.liftOfRightInverse_comp_apply] at this
  exact this

theorem finPart_sigR (D : D7) (x : AE D) :
    finPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [finPart, sigR]
  | add x y hx hy => simp only [RingHom.map_add, hx, hy]

theorem finPart_det (D : D7) (V : HSp D) (g : GA D V) :
    finPart D ((matHom V g).1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)).det =
      ((Matrix.GeneralLinearGroup.det (finHom V g) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        Af D.host.F ⊗[D.host.F] D.host.E) := by
  rw [RingHom.map_det]
  rfl

theorem exists_idF_mul (D : D7) (x : (AE D)ˣ)
    (hx : sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) = finPart D (x : AE D)) :
    ∃ (a : (AF D.host.F)ˣ) (y : (AE D)ˣ), finPart D (y : AE D) = 1 ∧ x = y * idF D a := by
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add, hσ, add_comm]
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom x) hx
  have hb' : algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F) =
      finPart D (x : AE D) := congrArg Units.val hb
  let a : (AF D.host.F)ˣ :=
    ⟨((1 : Ainf D.host.F), (b : Af D.host.F)), ((1 : Ainf D.host.F), ((b⁻¹ : (Af D.host.F)ˣ) : Af D.host.F)),
      Prod.ext (mul_one _) b.mul_inv, Prod.ext (mul_one _) b.inv_mul⟩
  have ha : Units.map (finPart D).toMonoidHom (idF D a) = Units.map (finPart D).toMonoidHom x := by
    apply Units.ext
    change finPart D ((a : AF D.host.F) ⊗ₜ 1) = finPart D (x : AE D)
    rw [← hb']
    rfl
  refine ⟨a, x * (idF D a)⁻¹, ?_, by simp⟩
  have : Units.map (finPart D).toMonoidHom (x * (idF D a)⁻¹) = 1 := by
    rw [map_mul, map_inv, ha, mul_inv_cancel]
  exact congrArg Units.val this

theorem exists_finite_char : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle), (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → ∃ xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ, ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) = ((c x : Circle) : ℂ) := by
  intro D V c hF hinf
  obtain ⟨hex, huniq, -, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D V
  choose r hr using hex
  have hval : ∀ g x, IsDetRoot V g x → c (r g) = c x := by
    intro g x hx
    obtain ⟨a, ha⟩ := huniq g _ _ (hr g) hx
    rw [ha, map_mul, hF, mul_one]
  have hm : ∀ g g', c (r (g * g')) = c (r g) * c (r g') := by
    intro g g'
    rw [hval _ _ (hmul _ _ _ _ (hr g) (hr g')), map_mul]
  let m : GA D V →* Circle := MonoidHom.mk' (fun g => c (r g)) hm
  obtain ⟨χ, hχ⟩ := circle_hom_factor (Matrix.GeneralLinearGroup.det.comp (finHom V)) m (by
    intro g hg
    have hg' : Matrix.GeneralLinearGroup.det (finHom V g) = 1 := hg
    have h1 := congrArg (finPart D) (hr g)
    rw [map_mul, finPart_det, hg', Units.val_one, one_mul, finPart_sigR] at h1
    obtain ⟨a, y, hy, hxy⟩ := exists_idF_mul D (r g) h1.symm
    change c (r g) = 1
    rw [hxy, map_mul, hF, hinf y hy, mul_one])
  refine ⟨Circle.toUnits.comp χ, fun g x hx => ?_⟩
  have : χ (Matrix.GeneralLinearGroup.det (finHom V g)) = c x := (hχ g).trans (hval g x hx)
  rw [MonoidHom.comp_apply, this]
  simp

end GlobalTheory.DetRootChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleSubquotient
section
noncomputable section

namespace GlobalTheory.SmoothStabilizerQuotient

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def stab (π : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem exists_maximal (π : Representation ℂ G V) {v : V} (hv : v ≠ 0) :
    ∃ T : Subrepresentation π, Maximal (fun U : Subrepresentation π => v ∉ U.toSubmodule) T := by
  have := zorn_le_nonempty₀ {U : Subrepresentation π | v ∉ U.toSubmodule} ?_ ⊥
    (by
      intro h
      exact hv h)
  · obtain ⟨T, -, hT⟩ := this
    exact ⟨T, hT⟩
  intro c hc hch y hy
  haveI : Nonempty c := ⟨⟨y, hy⟩⟩
  have hdir : Directed (· ≤ ·) (fun U : c => U.1.toSubmodule) := by
    intro a b
    rcases hch.total a.2 b.2 with h | h
    · exact ⟨b, h, le_rfl⟩
    · exact ⟨a, le_rfl, h⟩
  refine ⟨⟨⨆ U : c, U.1.toSubmodule, ?_⟩, ?_, ?_⟩
  · intro g x hx
    rw [Submodule.mem_iSup_of_directed _ hdir] at hx ⊢
    obtain ⟨U, hU⟩ := hx
    exact ⟨U, U.1.apply_mem_toSubmodule g hU⟩
  · intro hx
    obtain ⟨U, hU⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hx
    exact hc U.2 hU
  · intro U hU x hx
    exact (Submodule.mem_iSup_of_directed _ hdir).2 ⟨⟨U, hU⟩, hx⟩

def hull {π : Representation ℂ G V} (T : Subrepresentation π) (v : V) : Subrepresentation π where
  toSubmodule :=
    { carrier := {x | ∀ U : Subrepresentation π, T ≤ U → v ∈ U.toSubmodule → x ∈ U.toSubmodule}
      add_mem' := fun ha hb U h1 h2 => add_mem (ha U h1 h2) (hb U h1 h2)
      zero_mem' := fun U _ _ => zero_mem _
      smul_mem' := fun c _ hx U h1 h2 => U.toSubmodule.smul_mem c (hx U h1 h2) }
  apply_mem_toSubmodule := fun g _ hx U h1 h2 => U.apply_mem_toSubmodule g (hx U h1 h2)

def lift {π : Representation ℂ G V} {σ : Representation ℂ G W} (S : Subrepresentation π)
    (f : S.toRepresentation.IntertwiningMap σ) (R : Subrepresentation σ) : Subrepresentation π where
  toSubmodule := (R.toSubmodule.comap f.toLinearMap).map S.toSubmodule.subtype
  apply_mem_toSubmodule := by
    rintro g _ ⟨x, hx, rfl⟩
    refine ⟨S.toRepresentation g x, ?_, rfl⟩
    have hx' : f x ∈ R.toSubmodule := hx
    show f (S.toRepresentation g x) ∈ R.toSubmodule
    rw [f.isIntertwining]
    exact R.apply_mem_toSubmodule g hx'

theorem mem_lift {π : Representation ℂ G V} {σ : Representation ℂ G W} (S : Subrepresentation π)
    (f : S.toRepresentation.IntertwiningMap σ) (R : Subrepresentation σ) (x : S.toSubmodule) :
    x.1 ∈ (lift S f R).toSubmodule ↔ f x ∈ R.toSubmodule := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain rfl : y = x := Subtype.ext hxy
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

end GlobalTheory.SmoothStabilizerQuotient
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostFieldStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normOne_root_congruent_odd_hostField : ∀ (D : D7) (N : ℕ), Odd N → ∀ u z : (Af D.host.F ⊗[D.host.F] D.host.E), z ∈ intAE D → u - 1 = N • z → u * sigR (Af D.host.F) D.sp.cm.sig u = 1 → ∃ x y : (Af D.host.F ⊗[D.host.F] D.host.E), x ∈ intAE D ∧ y ∈ intAE D ∧ x * y = 1 ∧ x = u * sigR (Af D.host.F) D.sp.cm.sig x ∧ ∃ p ∈ intAE D, x - 1 = N • p := by
  first | exact @GlobalTheory.OddRoot.exists_root_odd | exact GlobalTheory.OddRoot.exists_root_odd | (intros; apply GlobalTheory.OddRoot.exists_root_odd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNthRootIdeleFinitePartOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdeleDiv

theorem exists_infAdele_pow_eq (D : D7) (n : ℕ) (hn : 0 < n)
    (z : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E) :
    ∃ w : InfiniteAdeleRing D.host.F ⊗[D.host.F] D.host.E, w ^ n = z := by
  obtain ⟨⟨θ, hθ⟩, H⟩ := GlobalTheory.Member.infiniteAdele_bijective D
  obtain ⟨-, -, hb⟩ := H θ hθ
  choose r hr using fun τ : {τ : D.host.E →+* ℂ // τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD} =>
    IsAlgClosed.exists_pow_nat_eq (θ τ.1 z) hn
  obtain ⟨w, hw⟩ := hb.2 r
  refine ⟨w, hb.1 ?_⟩
  funext τ
  have h1 : θ τ.1 w = r τ := congrFun hw τ
  change θ τ.1 (w ^ n) = θ τ.1 z
  rw [map_pow, h1, hr]

theorem exists_pow_eq_of_finPart_eq_one : ∀ (D : D7) (n : ℕ), 0 < n → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → ∃ y : (AE D)ˣ, y ^ n = x := by
  intro D n hn x hx
  obtain ⟨e, he, -, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨w, hw⟩ := exists_infAdele_pow_eq D n hn (e (x : AE D)).1
  have h2 : (e (x : AE D)).2 = 1 := (he _).2.trans hx
  have hy : (e.symm (w, 1)) ^ n = (x : AE D) := by
    apply e.injective
    rw [map_pow, RingEquiv.apply_symm_apply]
    exact Prod.ext hw (by rw [h2]; exact one_pow n)
  have hu : IsUnit (e.symm (w, 1)) := (isUnit_pow_iff hn.ne').1 (hy ▸ x.isUnit)
  obtain ⟨y, hy'⟩ := hu
  refine ⟨y, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, hy']
  exact hy

end GlobalTheory.IdeleDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOtherHalfPeriodStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_half_period_sub_not_mem_of_isLat : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ, 2 * P ∈ Λ → P ∉ Λ → ∃ P' : ℂ, 2 * P' ∈ Λ ∧ P' ∉ Λ ∧ P - P' ∉ Λ := by
  first | exact @GlobalTheory.HalfPeriod.exists_other_half_period | exact GlobalTheory.HalfPeriod.exists_other_half_period | (intros; apply GlobalTheory.HalfPeriod.exists_other_half_period <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilOfVacuum
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in

theorem exists_weil_of_vacuum (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (N N' : ℕ)
    (e0 : VC D N N' → ℂ) (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N')) (h0 : e0 ≠ 0) (χ : HeckeU D N) (χ' : HeckeU D N') :
    ∃ W : WeilO D cc δ N N' e0, W.chV = χ ∧ W.chV' = χ' ∧ W.ep = 1 ∧ W.ep' = 1 := by
  have hg : admG1 D := (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1
  obtain ⟨w, γ, WA, hM⟩ := GlobalTheory.T.exists_adelicWeilRepresentationModel D hg cc δ hc N N'
  obtain ⟨hT, hfix, hspan⟩ := GlobalTheory.T.adelicWeil_vacuum_fixed_and_translates_span D hg cc δ hc N N' w γ WA hM e0 he h0
  obtain ⟨lam, hlam, hsq⟩ := GlobalTheory.T.exists_goodIndexNormalization_negative_inert D
  obtain ⟨c', hc1', hc2'⟩ := GlobalTheory.T.exists_split_character_unitary_group D N χ N'
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_split_character_unitary_group D N' χ' N
  have hidx := GlobalTheory.T.heisenbergRelativeIndex_translate_completed_lattice D hg cc δ hc N N'
  have hM' := hM
  obtain ⟨hH, hSD, hinv, hrat, hcont⟩ := hM'
  obtain ⟨Om, hOm1, hOm2⟩ := GlobalTheory.T.exists_weil_representation_heisenberg hH lam hlam _ hSD ⟨e0, hT⟩ (fun h => h0 (congrArg Subtype.val h)) hfix hspan
    (actA D N N') hinv (fun u => (hidx u.1 u.2).1)
  let O : GA D N → GA D N' → (VC D N N' → ℂ) → (VC D N N' → ℂ) := fun g g' F =>
    if h : F ∈ TTs D (tor0 D cc δ) N N' then
      ((((c' g' * c g : ℂˣ) : ℂ) • Om (g, g') ⟨F, h⟩ : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) else 0
  have hO : ∀ g g' (F : TTs D (tor0 D cc δ) N N'), O g g' F =
      ((((c' g' * c g : ℂˣ) : ℂ) • Om (g, g') F : TTs D (tor0 D cc δ) N N') : VC D N N' → ℂ) := fun g g' F => dif_pos F.2
  refine ⟨{ nz := h0, chV := χ, chV' := χ', ep := 1, ep' := 1, ep_pm := ⟨Or.inl rfl, Or.inl rfl⟩, Om := O,
            maps := ?_, add := ?_, smul := ?_, one := ?_, mul := ?_, lift := ?_, inert := ?_, split := ?_ }, rfl, rfl, rfl, rfl⟩
  · intro g g' F hF
    rw [hO g g' ⟨F, hF⟩]
    exact Subtype.property _
  · intro g g' F hF F' hF'
    have := hO g g' (⟨F, hF⟩ + ⟨F', hF'⟩)
    rw [map_add, smul_add, Submodule.coe_add, Submodule.coe_add, ← hO, ← hO] at this
    exact this
  · intro g g' a F hF
    have := hO g g' (a • ⟨F, hF⟩)
    rw [map_smul, smul_comm, Submodule.coe_smul, Submodule.coe_smul a, ← hO] at this
    exact this
  · intro F hF
    rw [hO 1 1 ⟨F, hF⟩, map_one, map_one, mul_one, Units.val_one, one_smul, Prod.mk_one_one, map_one]
    rfl
  · intro g₁ g₂ g₁' g₂' F hF
    rw [hO _ _ ⟨F, hF⟩, hO g₂ g₂' ⟨F, hF⟩, hO, map_smul, smul_smul, ← Prod.mk_mul_mk, map_mul Om, map_mul, map_mul,
      ← Units.val_mul, mul_mul_mul_comm]
    rfl
  · intro g g' z F hF
    obtain ⟨m, hm, h⟩ := hcont (actA D N N' (g, g') (z.map (inc D))) (Om (g, g') ⟨F, hF⟩)
    refine ⟨m, hm, fun z' hz' => ?_⟩
    choose a ha1 ha2 using hz'
    have h1 : z'.map (inc D) = actA D N N' (g, g') (z.map (inc D)) + m • (Matrix.of a : XA D N N') := by
      rw [← sub_eq_iff_eq_add']
      ext i j
      rw [actA_apply, ha2 i j, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    have h2 := hrat z ⟨F, hF⟩
    rw [← h2, hO, hO g g' ⟨F, hF⟩, ← hrat, map_smul, hOm1, h1, h (Matrix.of a) ha1]
  · intro k k' hk hk' hs hs'
    have h3 := (GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le hH _ _ (hOm2 (k, k')).1).2.2 ((hidx k k').2.2 hk hk')
    rw [hO k k' ⟨e0, hT⟩, hc1 k hs, hc1' k' hs', mul_one, Units.val_one, one_smul, (hOm2 (k, k')).2, normOp, h3.1,
      h3.2 _ hfix, map_one, inv_one, one_smul]
  · intro g g' x x' L₁ L₁' hs hs' hx h1 h1' hL hL'
    have h3 := GlobalTheory.T.thetaIntertwiner_eq_normalisedAdelicSum D hg cc δ hc N N' w γ WA hM g g' L₁ L₁' hL hL' (hOm2 (g, g')).1 ⟨e0, hT⟩ hfix
    have h4 := hsq _ (hidx g g').1 fun q hq hi => (hidx g g').2.1 q hq (hs q hq hi) (hs' q hq hi)
    rw [hO g g' ⟨e0, hT⟩, hc2 g x (fun q hq hi => (hx q hq hi).1) h1, hc2' g' x' (fun q hq hi => (hx q hq hi).2) h1',
      (hOm2 (g, g')).2, normOp, h4, Submodule.coe_smul, Submodule.coe_smul, ← h3, zpow_one, zpow_one]
    rfl

theorem exists_weil : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ N N' : ℕ, Even N → Even N' → ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), e0 ≠ 0 → ∀ (χ : HeckeU D N) (χ' : HeckeU D N'), ∃ W : WeilO D cc δ N N' e0, W.chV = χ ∧ W.chV' = χ' ∧ W.ep = 1 ∧ W.ep' = 1 :=
  fun D cc δ hc N N' _ _ e0 he h0 χ χ' => exists_weil_of_vacuum D cc δ hc N N' e0 he h0 χ χ'

end GlobalTheory.FinWeil
end

