import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormGivesRealNormalForm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0044
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoprimeScaledIsometrySameSignature
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0417
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0046
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0020
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0011
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdaptedNormalFormGivesRealNormalFormStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedNormalForm_gives_real_normal_form : GlobalTheory.TypeAsm.FrameC := by
  first | exact @GlobalTheory.TypeAsm.frameC_holds | exact GlobalTheory.TypeAsm.frameC_holds | (intros; apply GlobalTheory.TypeAsm.frameC_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordEquivSymmApply
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDomGrp

variable {D : D7} (X : HidaSetting D)

theorem vecOf_apply (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    vecOf X c = ∑ i, c i • X.bas (ci X i) := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.funCongrLeft_apply, Module.Basis.equivFun_symm_apply]
  rw [← (ci X).sum_comp]
  simp

theorem crdH_vecOf (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) : crdH X (vecOf X c) = c := by
  funext i
  simp only [crdH, vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply, LinearEquiv.funCongrLeft_apply]
  simp

theorem vecOf_crdH (y : (VS D).V) : vecOf X (crdH X y) = y := by
  simp only [vecOf, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  conv_rhs => rw [← X.bas.equivFun.symm_apply_apply y]
  congr 1

variable {X} in
theorem n_vecOf {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E}
    (hγ : ∀ y, crdH X (n y) = γ *ᵥ crdH X y) (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    n (vecOf X c) = vecOf X (γ *ᵥ c) := by
  conv_lhs => rw [← vecOf_crdH X (n (vecOf X c)), hγ, crdH_vecOf]

theorem crdH_eq_crd (y : (VS D).V) (i : Fin (2 * D.R.rS + D.R.k + 1)) :
    crdH X y i = X.ιE (X.crd y (ci X i)) := by
  simp [crdH, HidaSetting.crd, crdOf]

theorem sig_apply (a : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) a = star a := rfl

theorem hT_vecOf (a b : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) :
    (VS D).hT (vecOf X a) (vecOf X b) = GlobalTheory.SgAlg.form (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) b a := by
  rw [vecOf_apply, vecOf_apply]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    GlobalTheory.SgAlg.form, dotProduct, Matrix.mulVec, sig_apply, Jc, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [starRingEnd_apply]
  ring

theorem Jc_det_ne_zero : (Jc X).det ≠ 0 := by
  have h : Jc X = (X.B.I.J.map X.ιE).submatrix (ci X) (ci X) := by
    ext i j
    simp [Jc, X.J_eq]
  rw [h, Matrix.det_submatrix_equiv_self]
  intro h0
  apply X.B.I.J_det
  apply X.ιE.injective
  rw [map_zero]
  exact (RingHom.map_det X.ιE.toRingHom X.B.I.J).trans h0

def coordEquiv : (Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) ≃ₗ[D.host.E] (VS D).V :=
  (LinearEquiv.funCongrLeft D.host.E D.host.E (ci X).symm).trans X.bas.equivFun.symm

theorem coordEquiv_apply (c : Fin (2 * D.R.rS + D.R.k + 1) → D.host.E) : coordEquiv X c = vecOf X c := rfl

theorem coordEquiv_symm_apply (y : (VS D).V) : (coordEquiv X).symm y = crdH X y := by
  apply (coordEquiv X).injective
  rw [LinearEquiv.apply_symm_apply, coordEquiv_apply, vecOf_crdH]

theorem exists_mat (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, ∀ y, crdH X (n y) = γ *ᵥ crdH X y := by
  refine ⟨LinearMap.toMatrix' (((coordEquiv X).symm.toLinearMap ∘ₗ n.toLinearMap) ∘ₗ (coordEquiv X).toLinearMap), fun y => ?_⟩
  rw [LinearMap.toMatrix'_mulVec]
  simp [coordEquiv_symm_apply, coordEquiv_apply, vecOf_crdH]

theorem exists_equiv (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E) (hU : GlobalTheory.SgAlg.IsUn (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) γ) :
    ∃ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, ∀ y, crdH X (n y) = γ *ᵥ crdH X y := by
  have hdet : IsUnit γ.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    apply Jc_det_ne_zero X
    have := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  have h1 : γ⁻¹ * γ = 1 := Matrix.nonsing_inv_mul γ hdet
  have h2 : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hdet
  refine ⟨(coordEquiv X).symm.trans ((Matrix.toLin'OfInv h1 h2).trans (coordEquiv X)), fun y => ?_⟩
  simp only [LinearEquiv.trans_apply, coordEquiv_symm_apply, coordEquiv_apply, Matrix.toLin'OfInv_apply,
    Matrix.toLin'_apply, crdH_vecOf]
  rfl

end GlobalTheory.CovDomGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryOfUnimodularLatticesAtPlace
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.HermitianLatticesTheory
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.GenusSelfDual GlobalTheory.LocalIsomAt

namespace GlobalTheory.Mass.UnimodLoc

section Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
  (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)))

theorem exists_factor [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    {A N : Matrix (Fin n) (Fin n) E} (hA : ∀ a b, cc (A a b) = A b a)
    (h1 : ∀ i j, A i j ∈ semiLoc v) (h2 : ∀ i j, N i j ∈ semiLoc v) (hAN : A * N = 1) :
    ∃ P : GL (Fin n) (LocAlg v), P.1 ∈ (locOrder v).toSubring.matrix ∧
      (P⁻¹).1 ∈ (locOrder v).toSubring.matrix ∧ A.map (locEmb v) = P.1ᵀ * P.1.map (locConj v) :=
  exists_eq_transpose_mul_map_locConj v (N := N.map (locEmb v))
    (fun i j => (locEmb_mem_locOrder_iff v _).2 (h1 i j))
    (fun i j => (locEmb_mem_locOrder_iff v _).2 (h2 i j))
    (by rw [← Matrix.map_mul, hAN, Matrix.map_one _ (map_zero _) (map_one _)])
    (fun i j => by
      change locConj v (locEmb v (A i j)) = locEmb v (A j i)
      rw [locConj_locEmb, hA])

theorem exists_unitary [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)]
    {A N A' N' : Matrix (Fin n) (Fin n) E} (hA : ∀ a b, cc (A a b) = A b a) (hA' : ∀ a b, cc (A' a b) = A' b a)
    (h1 : ∀ i j, A i j ∈ semiLoc v) (h2 : ∀ i j, N i j ∈ semiLoc v) (hAN : A * N = 1)
    (h1' : ∀ i j, A' i j ∈ semiLoc v) (h2' : ∀ i j, N' i j ∈ semiLoc v) (hAN' : A' * N' = 1)
    (T : GL (Fin n) E) (hT : A' = T.1ᵀ * A * T.1.map cc) :
    ∃ γ : Matrix (Fin n) (Fin n) E, γᵀ * A * γ.map cc = A ∧ ∀ i j, ((T⁻¹).1 * γ) i j ∈ semiLoc v := by
  obtain ⟨P, hP, hPi, hPA⟩ := exists_factor v hA h1 h2 hAN
  obtain ⟨Q, hQ, hQi, hQA⟩ := exists_factor v hA' h1' h2' hAN'
  have hd : A.det ≠ 0 := (Matrix.isUnit_det_of_right_inverse hAN).ne_zero
  obtain ⟨p, hp0, hp⟩ : ∃ p : ℕ, 0 < p ∧ (p : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal :=
    ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)), Ideal.absNorm_mem _⟩
  let T' : GL (Fin n) (LocAlg v) := Matrix.GeneralLinearGroup.map (locEmb v) T
  have hT' : T'.1ᵀ * A.map (locEmb v) * T'.1.map (locConj v) = Q.1ᵀ * 1 * Q.1.map (locConj v) := by
    rw [Matrix.mul_one, ← hQA, hT, Matrix.map_mul, Matrix.map_mul]
    rfl
  let u : GL (Fin n) (LocAlg v) := T' * Q⁻¹ * P
  have hu : u.1ᵀ * A.map (locEmb v) * u.1.map (locConj v) = A.map (locEmb v) := by
    have e : (T' * Q⁻¹).1ᵀ * A.map (locEmb v) * (T' * Q⁻¹).1.map (locConj v) = 1 := by
      rw [Units.val_mul, UnramifiedHermitian.congr_mul, hT', ← UnramifiedHermitian.congr_mul, Units.mul_inv]
      simp
    rw [Units.val_mul, UnramifiedHermitian.congr_mul, e, Matrix.mul_one, ← hPA]
  haveI : IsArtinianRing (LocAlg v) := IsArtinianRing.of_finite (v.adicCompletion (maximalRealSubfield E)) _
  obtain ⟨lam, hlam, hlu⟩ := (infinite_norm_one E).exists_notMem_finite
    (finite_not_isUnit_one_add_smul (locEmb v) u.1)
  obtain ⟨γ, hγ, hγX⟩ := exists_unitary_congr_pi (T := Unit) (A := fun _ => LocAlg v) (fun _ => locEmb v)
    (IsCMField.complexConj E : E →+* E) (fun _ => locConj v) (fun _ => locConj_locEmb v)
    (IsCMField.complexConj_apply_apply E) (fun _ => locConj_locConj v) A
    (Matrix.ext fun a b => hA b a) hd (fun _ => (locOrder v).toSubring) (fun _ z => locConj_mem v)
    (fun z => by
      obtain ⟨x, hx⟩ := exists_sub_mem_locOrder ({v} : Finset _)
        (fun w => (Finset.mem_singleton.1 w.2).symm ▸ z ())
      exact ⟨x, fun _ => hx ⟨v, Finset.mem_singleton_self v⟩⟩)
    (fun x => by
      obtain ⟨k, s, hk, hx⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
        (Algebra.IsAlgebraic.isAlgebraic x)).exists_nsmul_eq (𝓞 E)
      exact ⟨k, Nat.pos_of_ne_zero hk, fun _ => by rw [← map_nsmul, hx]; exact locEmb_mem_locOrder v s⟩)
    p hp0 (fun _ => exists_inv_one_add v hp) (fun _ => u) (fun _ => T') (fun _ => hu) lam hlam
    (fun _ => not_not.1 hlu)
  refine ⟨γ, hγ, fun i j => (locEmb_mem_locOrder_iff v _).1 ?_⟩
  have h3 : (T'⁻¹).1 * (γ.map (locEmb v) * (u⁻¹).1) * T'.1 ∈ (locOrder v).toSubring.matrix := hγX ()
  have h4 := mul_mem (mul_mem h3 hQi) hP
  have e : (T'⁻¹).1 * (γ.map (locEmb v) * (u⁻¹).1) * T'.1 * (Q⁻¹).1 * P.1 = ((T⁻¹).1 * γ).map (locEmb v) := by
    have e1 : (u⁻¹).1 * (T'.1 * (Q⁻¹).1 * P.1) = 1 := Units.inv_mul u
    have e2 : (T'⁻¹).1 = (T⁻¹).1.map (locEmb v) := rfl
    rw [Matrix.map_mul, ← e2]
    calc _ = (T'⁻¹).1 * γ.map (locEmb v) * ((u⁻¹).1 * (T'.1 * (Q⁻¹).1 * P.1)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [e1, Matrix.mul_one]
  rw [e] at h4
  exact h4 i j

end Mat

section Lat

variable {K V : Type} [Field K] [NumberField K] [IsCMField K] [StarRing K] (hst : ∀ x : K, star x = cc x)
  (v : HeightOneSpectrum (𝓞 (maximalRealSubfield K))) {P : Ideal (𝓞 K)} (hP : P.IsPrime)
  (hPv : P.comap (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) = v.asIdeal)

include hst hP hPv

theorem mem_loc_iff {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ loc (K := K) P L ↔ ∃ s ∉ v.asIdeal, algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) s • x ∈ L := by
  constructor
  · rintro ⟨s, hs, hx⟩
    have key : ∀ s ∈ hcompl (K := K) P, s ∉ P ∧ IsCMField.ringOfIntegersComplexConj K s ∉ P := by
      intro s hs
      induction hs using Submonoid.closure_induction with
      | mem s h => exact ⟨h.1, h.2 _ (hst _).symm⟩
      | one => rw [map_one, and_self]; exact (Ideal.ne_top_iff_one _).1 hP.ne_top
      | mul a b _ _ ha hb =>
        rw [map_mul]
        exact ⟨fun h => (hP.mem_or_mem h).elim ha.1 hb.1, fun h => (hP.mem_or_mem h).elim ha.2 hb.2⟩
    obtain ⟨m, hm⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff K
      (IsCMField.ringOfIntegersComplexConj K s * s)).1 (by ext; simp [mul_comm])
    refine ⟨m, ?_, ?_⟩
    · rw [← hPv, Ideal.mem_comap, hm]
      exact fun h => (hP.mem_or_mem h).elim (key s hs).2 (key s hs).1
    · rw [hm, mul_smul]
      exact L.smul_mem _ hx
  · rintro ⟨s, hs, hx⟩
    rw [← hPv, Ideal.mem_comap] at hs
    refine ⟨_, Submonoid.subset_closure ⟨hs, fun t ht => ?_⟩, hx⟩
    have : t = algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) s :=
      RingOfIntegers.ext (ht.trans ((hst _).trans (cc_algebraMap s)))
    rwa [this]

theorem mem_locR_iff (z : K) : z ∈ locR (K := K) P ↔ z ∈ semiLoc v := by
  rw [locR, mem_loc_iff hst v hP hPv, mem_semiLoc_iff]
  simp only [GlobalTheory.LocalLattice.mem_one_ringOfIntegers_iff]
  rfl

variable [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_basis (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) :
    ∃ b : Module.Basis (Fin (Module.finrank K V)) K V,
      ∀ x, x ∈ loc (K := K) P L ↔ ∀ i, b.repr x i ∈ semiLoc v := by
  let e := (Module.finBasis K V).equivFun
  let L₀ : Submodule (𝓞 K) (Fin (Module.finrank K V) → K) := L.map (e.toLinearMap.restrictScalars (𝓞 K))
  have hL₀ : ReciprocityTheory.MultiplicativeHeights.IsLattice L₀ := by
    refine ⟨hL.fg.map _, ?_⟩
    have : (L₀ : Set _) = e.toLinearMap '' (L : Set V) := rfl
    rw [this, Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]
  obtain ⟨g, hg⟩ := exists_frame v hL₀
  refine ⟨Module.Basis.ofEquivFun (e.trans (Matrix.toLin'OfInv (Units.mul_inv g) (Units.inv_mul g))), fun x => ?_⟩
  rw [mem_loc_iff hst v hP hPv]
  refine Iff.trans ?_ (hg (e x))
  refine exists_congr fun s => and_congr_right fun _ => ⟨fun h => ⟨_, h, ?_⟩, ?_⟩
  · exact map_smul (e.toLinearMap.restrictScalars (𝓞 K)) _ _
  · rintro ⟨y, hy, h⟩
    have := e.injective (h.trans (map_smul (e.toLinearMap.restrictScalars (𝓞 K)) _ x).symm)
    exact this ▸ hy

omit hP hPv [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem form_eq (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ} (b : Module.Basis (Fin n) K V) (x y : V) :
    h y x = herm (Matrix.of fun i j => h (b j) (b i)) (b.equivFun x) (b.equivFun y) := by
  conv_lhs => rw [← b.sum_equivFun x, ← b.sum_equivFun y]
  simp only [herm, map_sum, LinearMap.sum_apply, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    smul_eq_mul, Matrix.of_apply, Finset.mul_sum, starRingEnd_apply, hst]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit hst hP hPv [IsCMField K] [FiniteDimensional K V] in
theorem mem_dualAt (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ dualAt h P L ↔ ∀ y ∈ L, h y x ∈ locR (K := K) P := by
  simp [dualAt, Submodule.mem_iInf]

omit [FiniteDimensional K V] in
theorem gram (h : V →ₗ⋆[K] V →ₗ[K] K) (hn : h.Nondegenerate) {n : ℕ} (b : Module.Basis (Fin n) K V)
    (L : Submodule (𝓞 K) V) (hb : ∀ x, x ∈ loc (K := K) P L ↔ ∀ i, b.repr x i ∈ semiLoc v)
    (hu : IsUnimodularAt h P L) :
    (∀ i j, h (b j) (b i) ∈ semiLoc v) ∧ ∃ N : Matrix (Fin n) (Fin n) K, (∀ i j, N i j ∈ semiLoc v) ∧
      (Matrix.of fun i j => h (b j) (b i)) * N = 1 := by
  have hm : ∀ x, x ∈ loc (K := K) P L ↔ ∀ y ∈ loc (K := K) P L, h y x ∈ semiLoc v := fun x => by
    conv_lhs => rw [← hu, mem_dualAt]
    simp only [mem_locR_iff hst v hP hPv]
  have hbi : ∀ i, b i ∈ loc (K := K) P L := fun i => (hb _).2 fun j => by
    rw [b.repr_self, Finsupp.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨fun i j => (hm _).1 (hbi i) _ (hbi j), ?_⟩
  set A : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => h (b j) (b i) with hA
  have hd : A.det ≠ 0 := fun h0 => by
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    refine hc0 (b.equivFun.symm.map_eq_zero_iff.1 (hn.2 _ fun y => ?_))
    rw [form_eq hst h b, ← hA, LinearEquiv.apply_symm_apply, herm_eq_dotProduct, hc, zero_dotProduct]
  refine ⟨A⁻¹, fun i j => ?_, Matrix.mul_nonsing_inv _ hd.isUnit⟩
  have := (hb _).1 ((hm (b.equivFun.symm (Pi.single i 1 ᵥ* A⁻¹))).2 fun y hy => by
    rw [form_eq hst h b, ← hA, LinearEquiv.apply_symm_apply, herm_eq_dotProduct, Matrix.vecMul_vecMul,
      Matrix.nonsing_inv_mul _ hd.isUnit, Matrix.vecMul_one, single_dotProduct, one_mul]
    exact cc_mem_semiLoc v ((hb y).1 hy i)) j
  rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply] at this
  simpa using this

theorem exists_isom [Algebra.Unramified (𝓞 (maximalRealSubfield K)) (𝓞 K)]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate) (L L' : Submodule (𝓞 K) V)
    (hL : Submodule.IsLattice K L) (hL' : Submodule.IsLattice K L')
    (hu : IsUnimodularAt h P L) (hu' : IsUnimodularAt h P L') :
    ∃ g ∈ isom h, gmap g (loc (K := K) P L) = loc (K := K) P L' := by
  obtain ⟨b, hb⟩ := exists_basis hst v hP hPv L hL
  obtain ⟨b', hb'⟩ := exists_basis hst v hP hPv L' hL'
  obtain ⟨h1, N, h2, hN⟩ := gram hst v hP hPv h hn b L hb hu
  obtain ⟨h1', N', h2', hN'⟩ := gram hst v hP hPv h hn b' L' hb' hu'
  let T : GL (Fin (Module.finrank K V)) K :=
    ⟨b.toMatrix b', b'.toMatrix b, b.toMatrix_mul_toMatrix_flip b', b'.toMatrix_mul_toMatrix_flip b⟩
  obtain ⟨γ, hγ, hγT⟩ := exists_unitary v (A := Matrix.of fun i j => h (b j) (b i))
    (A' := Matrix.of fun i j => h (b' j) (b' i)) (fun i j => (hst _).symm.trans (hs.eq _ _))
    (fun i j => (hst _).symm.trans (hs.eq _ _)) h1 h2 hN h1' h2' hN' T (by
      ext i j
      rw [← Published.herm_col, Matrix.of_apply, form_eq hst h b]
      rfl)
  have hγd : γ.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det hγ
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at this
    exact (Matrix.isUnit_det_of_right_inverse hN).ne_zero this.symm
  let g : V ≃ₗ[K] V := (b.equivFun.trans
    (Matrix.toLinearEquiv' γ (Matrix.invertibleOfIsUnitDet γ hγd.isUnit))).trans b.equivFun.symm
  have hg : ∀ x, b.equivFun (g x) = γ *ᵥ b.equivFun x := fun x => b.equivFun.apply_symm_apply _
  have hgi : ∀ x y, h (g x) (g y) = h x y := fun x y => by
    rw [form_eq hst h b, form_eq hst h b y x, hg, hg, herm_mulVec, hγ]
  have hle : ∀ x ∈ loc (K := K) P L, g x ∈ loc (K := K) P L' := fun x hx => (hb' _).2 fun i => by
    have e : b'.repr (g x) i = ((b'.toMatrix b * γ) *ᵥ b.equivFun x) i := by
      rw [← Matrix.mulVec_mulVec, ← hg]
      exact (congrFun (b.toMatrix_mulVec_repr b' (g x)) i).symm
    rw [e, Matrix.mulVec, dotProduct]
    exact Subalgebra.sum_mem _ fun j _ => mul_mem (hγT i j) ((hb x).1 hx j)
  refine ⟨g, hgi, le_antisymm ?_ fun z hz => ⟨g.symm z, ?_, g.apply_symm_apply z⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hle x hx
  · rw [← hu, SetLike.mem_coe, mem_dualAt]
    intro y hy
    rw [← hgi, g.apply_symm_apply]
    rw [← hu', mem_dualAt] at hz
    exact hz _ (hle y hy)

end Lat

theorem exists_isom_of_isUnimodularAt : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (L L' : Submodule (𝓞 K) V), Submodule.IsLattice K L → Submodule.IsLattice K L' → ∀ P : Ideal (𝓞 K), P.IsMaximal → IsUnimodularAt h P L → IsUnimodularAt h P L' → ∃ g ∈ isom h, gmap g (loc (K := K) P L) = loc (K := K) P L' := by
  intro K V _ _ _ _ _ _ _ _ h hc hs hn L L' hL hL' P hP hu hu'
  obtain ⟨_, hst⟩ := (GlobalTheory.LeastExponentCompare.conj_iff K star).1 ⟨hc.2.1, by
    obtain ⟨θ, t, e1, e2⟩ := hc.2.2 P hP
    refine ⟨algebraMap (𝓞 K) K θ, fun e => e2 ?_⟩
    rw [show t = θ from RingOfIntegers.ext (e1.trans e), sub_self]
    exact zero_mem _⟩
  have hst' : ∀ x : K, star x = cc x := congrFun hst
  haveI := Formalism.L2.Pj.unramBridge_holds K fun Q hQ => by
    obtain ⟨θ, t, e1, e2⟩ := hc.2.2 Q hQ
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ = t :=
      RingOfIntegers.ext (e1.trans (hst' _)).symm
    rwa [this]
  let w : HeightOneSpectrum (𝓞 K) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)⟩
  exact exists_isom hst' (w.under (𝓞 (maximalRealSubfield K))) hP.isPrime rfl h hs hn L L' hL hL' hu hu'

end GlobalTheory.Mass.UnimodLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapHypothesisOfLargenessConstantGe
section
noncomputable section
namespace GlobalTheory.TypeAsm
open Formalism.BasicNotions

theorem gap_hypothesis_of_kernel_bound_large_constant {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cw cT CT C0 : ℝ} (hCl : 1801 ≤ Cl)
    (h : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0) : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  obtain ⟨⟨hS, -, -⟩, -⟩ := h
  obtain ⟨-, -, hmf, hfk, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hgap, -, -, hClm, -⟩ := hS
  have hL : 1 < large₂.sc.L := Formalism.MainNotions.S.one_lt_scL large₂
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hf16 : 16 ≤ D.R.f := le_trans (by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4) hmf
  have hf : (16 : ℝ) ≤ D.R.f := by exact_mod_cast hf16
  have hmn : D.R.m ≤ D.R.r := by
    have h1 : 1 ≤ D.R.k := by omega
    show D.R.m ≤ D.R.k + D.R.m - 1
    omega
  have hmR : (1801 : ℝ) ≤ D.R.m := le_trans hCl hClm
  have hm1801 : 1801 ≤ D.R.m := by exact_mod_cast hmR
  refine ⟨le_trans hm1801 hmn, fun τ j hj => ?_⟩
  have g := hgap τ (j.1 + 1) (by omega) (by omega)
  rw [Formalism.MainNotions.S.bOne_succ τ (j.1 + 1) hj, Formalism.MainNotions.S.bOne_succ τ j.1 j.2] at g
  have hn0 : (0 : ℝ) ≤ (D.R.r : ℝ) ^ 19 := by positivity
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ (by linarith)
  have h16 : 16 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
    have a1 : 16 * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 := by nlinarith
    have a2 : Cl * (D.R.r : ℝ) ^ 19 ≤ Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) :=
      le_mul_of_one_le_right (by positivity) (by nlinarith)
    linarith [show Cl * (D.R.r : ℝ) ^ 19 * ((D.R.f : ℝ) ^ 5 * large₂.sc.L) =
      Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L by ring]
  have hR : ((16 * (D.R.r : ℚ) ^ 19 : ℚ) : ℝ) ≤ (((D.hc τ).b ⟨j.1 + 1, hj⟩ - (D.hc τ).b j : ℚ) : ℝ) := by
    push_cast
    have e : ((D.hc τ).b ⟨j.1, j.2⟩ : ℝ) = ((D.hc τ).b j : ℝ) := rfl
    linarith
  exact_mod_cast hR

theorem gapC : GapC :=
  ⟨1801, fun _ _ _ _ _ _ _ _ _ _ hCl h => gap_hypothesis_of_kernel_bound_large_constant hCl h⟩

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalInnerDatumEqIffLocalDataEqStatement
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalInnerDatum_eq_iff_local_data_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ₁ Λ₂ : LV D) (y₁ y₂ : Dat Z FP), LocOver Λ₁ y₁ → LocOver Λ₂ y₂ → (gdat F F' Λ₁ = gdat F F' Λ₂ ↔ y₁ = y₂) := by
  first | exact @GlobalTheory.Unfold.InnerDict.gdat_eq_iff | exact GlobalTheory.Unfold.InnerDict.gdat_eq_iff | (intros; apply GlobalTheory.Unfold.InnerDict.gdat_eq_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLoUniMul
section
universe u_1

namespace GlobalTheory.LowerUnipotentMul

open Matrix

theorem isLoUni_mul {R : Type*} [CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R}
    (hl : Formalism.MainNotions.S.IsLoUni l) (hl' : Formalism.MainNotions.S.IsLoUni l') : Formalism.MainNotions.S.IsLoUni (l * l') := by
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with hik | hki
    · rw [(hl i k).1 hik, zero_mul]
    · rw [(hl' k j).1 (lt_of_le_of_lt hki hij), mul_zero]
  · intro hij
    subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hl i i).2 rfl, (hl' i i).2 rfl, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hl' k i).1 h, mul_zero]
      · rw [(hl i k).1 h, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem main : ∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R},
    Formalism.MainNotions.S.IsLoUni l → Formalism.MainNotions.S.IsLoUni l' → Formalism.MainNotions.S.IsLoUni (l * l') :=
  fun hl hl' => isLoUni_mul hl hl'

end GlobalTheory.LowerUnipotentMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreimageReindexScaleComplexLeStatement
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_preimage_reindex_scale_complex_le : ∀ (ι ι' κ κ' : Type) [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ'] (e : ι ≃ ι') (f : κ ≃ κ') (ρ c : ℝ) (d : κ → ℕ), 1 ≤ ρ → c ≤ 1 → ∀ A : Set (ι → κ → ℂ), MeasurableSet A → (MeasureTheory.Measure.pi fun _ : ι' => MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) ((fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
  first | exact @GlobalTheory.CoordScale.measure_preimage_reindex_scale_le | exact GlobalTheory.CoordScale.measure_preimage_reindex_scale_le | (intros; apply GlobalTheory.CoordScale.measure_preimage_reindex_scale_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericCorankOneTermsFamilyCutByDefect
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.SnFam

namespace GlobalTheory.SnFam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem famNG_holds : FamNG := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y u u' hC => ?_⟩
  have hT : ConcTie X Y := hC.2.2
  exact ⟨rfl, GlobalTheory.T.nonGeneric_term_classes_eq_rows_in_double_coset D X Y u u' hT, (GlobalTheory.NGClass.ngClass_rows D X Y u u' hT).2.1⟩

end GlobalTheory.SnFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NonGenericFamilyClassesDetermineRowsStatement
section
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermOp NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonGeneric_family_classes_determine_rows : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ConcTie X Y → (∀ t ∈ (Y.tO u u').ngSet, t.G ≠ 0) ∧ (∀ t ∈ (Y.tO u u').ngSet, ∀ t' ∈ (Y.tO u u').ngSet, clsOf Y u u' t = clsOf Y u u' t' → (Y.tO u u').rowOf t = (Y.tO u u').rowOf t') ∧ ∀ t : TauC Y u u', (Y.tO u u').vec t ≠ 0 → t.relevant := by
  first | exact @GlobalTheory.NGClass.ngClass_rows | exact GlobalTheory.NGClass.ngClass_rows | (intros; apply GlobalTheory.NGClass.ngClass_rows <;> assumption)
end

