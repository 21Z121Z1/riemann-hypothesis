import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0161
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0035
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0350
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0146
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0010
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0056

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseThetaTensorPowerTranslatesIntegral
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomN

theorem contDiff_opU_of_analytic {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Formalism.L2.Th1.H.Sesq V) (x : V) {F : V → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ) :
    ContDiff ℂ ⊤ (Formalism.L2.Th1.H.opU H x F) := by
  have h1 : ContDiff ℂ ⊤ F := contDiffOn_univ.1 (hF.contDiffOn uniqueDiffOn_univ)
  let f : V →ₗ[ℂ] ℂ :=
    { toFun := fun z => H z x
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hl : ContDiff ℂ ⊤ (fun z => H z x) := (LinearMap.toContinuousLinearMap f).contDiff
  have h2 : ContDiff ℂ ⊤ (fun z => F (z + x)) := h1.comp (contDiff_id.add contDiff_const)
  have h3 : ContDiff ℂ ⊤ (fun z => Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)) :=
    ((contDiff_const.mul hl).sub contDiff_const).cexp
  exact h2.mul h3

theorem latInt_U_thZero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → ∀ (N N' : ℕ) (s : VC D N N'), TorsPrime D q (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) s → LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (U D B.tor s (B.thZero N N')) := by
  intro D cc δ B hcc hδ q _ hq2 hsplit hcop ι δ₀ θ Ω hP N N' s hs
  have hS := B.stdOK hcc hδ
  have han : AnalyticOnNhd ℂ B.thMM Set.univ := (B.thMM_spec hS).1.1
  have hLat : La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N' := B.lat0OK N N'
  have hA : area (lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := B.areaOK
  set G : Fin N' → Fin N → (D.what₂.Tau → ℂ) → ℂ := fun i j =>
    Formalism.L2.Th1.H.opU (Formalism.L2.Th1.H.matH (hOne B.L D.what₂.Tau)) (fun τ => s τ i j) B.thMM with hG
  have hU : U D B.tor s (B.thZero N N') = fun z => ∏ i, ∏ j, G i j (entry D.what₂.Tau N N' i j z) := by
    funext z
    rw [U_eq]
    show Formalism.L2.Th1.H.opU (formV (area (lamOf D cc δ)) D.what₂.Tau N N') s (tensPow B.thMM N N') z = _
    rw [hA, opU_tensPow]
    rfl
  have hGc : ∀ i j, ContDiff ℂ ⊤ (G i j) := fun i j => contDiff_opU_of_analytic _ _ han
  have hEc : ∀ i j, ContDiff ℂ ⊤ (fun z : VC D N N' => G i j (entry D.what₂.Tau N N' i j z)) :=
    fun i j => (hGc i j).comp (entry D.what₂.Tau N N' i j).contDiff
  obtain ⟨n, -, hnq, hns⟩ := hs
  rw [hLat] at hns
  have hF : ∀ i j, LatInt ι (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (fun z => G i j (entry D.what₂.Tau N N' i j z)) := by
    intro i j
    have hm : LatInt ι (Ω / ι δ₀) B.lamM (G i j) := by
      refine GlobalTheory.T.cmTheta_baseVector_translates_integral D cc δ B hcc hδ q hq2 hsplit hcop ι δ₀ θ Ω hP (fun τ => s τ i j) n hnq ?_
      have := hns i j
      convert this using 1
      funext τ
      simp [nsmul_eq_mul]
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι (D.what₂.Tau → ℂ) (VC D N N') (Ω / ι δ₀) B.lamM
      (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (entry D.what₂.Tau N N' i j) (G i j) (hGc i j) ?_ hm
    intro x hx
    rw [hLat] at hx
    exact ⟨1, Nat.coprime_one_left q, by rw [one_smul]; exact hx i j⟩
  rw [hU]
  refine (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).1 (Fin N')
    (fun i z => ∏ j, G i j (entry D.what₂.Tau N N' i j z)) (fun i => ?_) (fun i => ?_)
  · exact contDiff_prod fun j _ => hEc i j
  · exact (GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum q ι (VC D N N') (Ω / ι δ₀) (La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))).1 (Fin N)
      (fun j z => G i j (entry D.what₂.Tau N N' i j z)) (hEc i) (hF i)

end GlobalTheory.MomN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DetNeZeroOfHasSignature
section
noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.LandherrSignature

theorem det_ne_zero_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature A p q) : A.det ≠ 0 := by
  obtain ⟨e, P, hP⟩ := h
  intro h0
  have h1 := congrArg det hP
  rw [det_mul, det_mul, det_reindex_self, h0, mul_zero, zero_mul, Formalism.UG.Jpq, det_fromBlocks_zero₂₁, det_neg] at h1
  simp at h1
  exact pow_ne_zero q (neg_ne_zero.2 one_ne_zero) h1.symm

theorem congr_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ} {p q : ℕ}
    (hA : Formalism.UG.HasSignature A p q) (hB : Formalism.UG.HasSignature B p q) :
    ∃ Q : Matrix n n ℂ, Q.det ≠ 0 ∧ Qᴴ * A * Q = B := by
  obtain ⟨e, -⟩ := id hA
  have key : ∀ C : Matrix n n ℂ, Formalism.UG.HasSignature C p q →
      ∃ R : Matrix n n ℂ, R.det ≠ 0 ∧ Rᴴ * C * R = (Formalism.UG.Jpq p q).submatrix e e := by
    rintro C ⟨e', P, hP⟩
    have hP' : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * C.submatrix e'.symm e'.symm *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hP
    refine ⟨P.val.submatrix e' e, ?_, ?_⟩
    · refine IsUnit.ne_zero (isUnit_det_of_right_inverse (B := P.inv.submatrix e e') ?_)
      rw [submatrix_mul_equiv, P.val_inv, submatrix_one_equiv]
    · have : C = (C.submatrix e'.symm e'.symm).submatrix e' e' := by simp
      rw [this, conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hP']
  obtain ⟨R, hR, h1⟩ := key A hA
  obtain ⟨S, hS, h2⟩ := key B hB
  have hu : IsUnit S.det := hS.isUnit
  refine ⟨R * S⁻¹, ?_, ?_⟩
  · rw [det_mul]
    exact mul_ne_zero hR (isUnit_nonsing_inv_det _ hu).ne_zero
  · calc (R * S⁻¹)ᴴ * A * (R * S⁻¹) = S⁻¹ᴴ * (Rᴴ * A * R) * S⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (S * S⁻¹)ᴴ * B * (S * S⁻¹) := by
          rw [h1, ← h2]
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = B := by rw [mul_nonsing_inv _ hu]; simp

theorem form_eq {E V n : Type} [Field E] [StarRing E] [AddCommGroup V] [Module E V] [Fintype n]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (b : Module.Basis n E V) (x y : n → E) :
    h (b.equivFun.symm x) (b.equivFun.symm y) = star x ⬝ᵥ ((Matrix.of fun i j => h (b i) (b j)) *ᵥ y) := by
  simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, starRingEnd_apply, dotProduct, mulVec, Matrix.of_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem congr_of_det_norm {n : ℕ} (G G' : Matrix (Fin n) (Fin n) E) (hG : Gᴴ = G) (hG' : G'ᴴ = G')
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) (hn : ∃ z : E, G.det = z * star z * G'.det)
    (hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ Qᴴ * G.map τ * Q = G'.map τ) :
    ∃ P : Matrix (Fin n) (Fin n) E, P.det ≠ 0 ∧ Pᴴ * G * P = G' := by
  obtain ⟨z, hz⟩ := hn
  obtain ⟨P, hP, h⟩ := GlobalTheory.QNorm.landherr_and_landherrSt.1 E n G G'
    (fun a b => congrFun (congrFun hG b) a) (fun a b => congrFun (congrFun hG' b) a) hd hd'
    (fun τ => by
      obtain ⟨Q, hQ, h⟩ := hs τ
      refine ⟨Q.map (starRingEnd ℂ), ?_, ?_⟩
      · have : (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det := (RingHom.map_det (starRingEnd ℂ) Q).symm
        rw [this]
        exact (map_ne_zero _).mpr hQ
      · rw [← h]
        congr 1
        ext a b
        simp)
    ⟨z, by rw [div_eq_iff hd']; exact hz⟩
  refine ⟨P.map ReciprocityTheory.ChartRestriction.G.FD.cc, ?_, ?_⟩
  · rw [GlobalTheory.Published.det_map_cc]
    exact GlobalTheory.Published.cc_ne_zero hP
  · rw [h]
    congr 2
    ext a b
    exact star_star (P b a)

theorem exists_isometry (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W₁ W₂ : HSpace E) (h₁ : W₁.SigOK) (h₂ : W₂.SigOK)
    (hr : W₁.rank = W₂.rank) (hs : ∀ τ, W₁.sig τ = W₂.sig τ) :
    ∃ φ : W₁.V ≃ₗ[E] W₂.V, ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y := by
  obtain ⟨z, hz⟩ := GlobalTheory.T.det_eq_norm_mul_of_selfDual_same_signature E hc W₁ W₂ h₁ h₂ hr hs
  let c : Fin W₁.rank ≃ Fin W₂.rank := finCongr hr
  have hH : ∀ W : HSpace E, W.gramᴴ = W.gram := fun W => by
    ext a b
    exact W.herm.eq _ _
  have hd : ∀ W : HSpace E, W.SigOK → W.gram.det ≠ 0 := fun W hW h0 => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine det_ne_zero_of_hasSignature (hW τ) ?_
    have : (W.gram.map τ).det = τ W.gram.det := (RingHom.map_det τ W.gram).symm
    rw [this, h0, map_zero]
  obtain ⟨P, hP0, hP⟩ := congr_of_det_norm (W₂.gram.submatrix c c) W₁.gram
    (by rw [conjTranspose_submatrix, hH]) (hH W₁) (by rw [det_submatrix_equiv_self]; exact hd W₂ h₂) (hd W₁ h₁)
    ⟨z, by rw [det_submatrix_equiv_self]; exact hz⟩
    (fun τ => by
      refine congr_of_hasSignature ?_ (h₁ τ)
      rw [hs τ]
      obtain ⟨e, Q, hQ⟩ := h₂ τ
      refine ⟨c.trans e, Q, ?_⟩
      rw [← hQ]
      congr 2)
  let b₂ := W₂.frame.reindex c.symm
  have e₂ : (Matrix.of fun i j => W₂.hT (b₂ i) (b₂ j)) = W₂.gram.submatrix c c := by
    ext i j
    simp [b₂, HSpace.gram]
  refine ⟨(W₁.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit))).trans
    b₂.equivFun.symm, fun x y => ?_⟩
  obtain ⟨u, rfl⟩ := W₁.frame.equivFun.symm.surjective x
  obtain ⟨v, rfl⟩ := W₁.frame.equivFun.symm.surjective y
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [form_eq, form_eq, e₂]
  change star (P *ᵥ u) ⬝ᵥ (_ *ᵥ (P *ᵥ v)) = star u ⬝ᵥ (W₁.gram *ᵥ v)
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hP]

end CM

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isometry_host : ∀ (D : D7) (W₁ W₂ : HSpace D.host.E), W₁.SigOK → W₂.SigOK → W₁.rank = W₂.rank →
    (∀ τ, W₁.sig τ = W₂.sig τ) →
    ∃ φ : W₁.V ≃ₗ[D.host.E] W₂.V, ∀ x y, W₂.hT (φ x) (φ y) = W₁.hT x y := fun D =>
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W₁ W₂ => exists_isometry (E := D.host.E) D.sp.cm.cmUnram W₁ W₂

end GlobalTheory.LandherrSignature
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GenusMassAtTwo
section
namespace GlobalTheory

theorem genusMassAt_two : ∀ D : Formalism.BasicNotions.D7, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2 :=
  fun D => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.genusMassAt_of D (genusMassStd_all D) 2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianClassNumberItemsAllRanks
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem classItemsAt_all : ∀ (D : D7) (n : ℕ), ClassItemsAt D n := fun D n =>
  have h := GlobalTheory.T.classNumber_finite_and_genusMass D
  ⟨genusMassAt_of D (GlobalTheory.genusMassStd_all D) n, classFinAt_of D h.1 n, classMassAt_of D h.2 n⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolIndep
section
namespace GlobalTheory.VolIndepClosed

theorem volIndep (D : Formalism.BasicNotions.D7) : GlobalTheory.IndefiniteRowSideFullHecke.IsometryTransportFrames.VolIndep D :=
  (GlobalTheory.VolIndepCompare.volumeIndependence_iff D).1 (GlobalTheory.VolumeIndep.volumeIndependence D)

end GlobalTheory.VolIndepClosed
end

