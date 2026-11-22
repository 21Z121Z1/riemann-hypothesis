import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import GroundTheory.AutomorphicForms.AnisotropicUnitaryHeight
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0525
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdeleBoundOfJointAnisotropic
section
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact.FormHeight

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

section Forms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {n : ℕ}

theorem sigR_conj (R : Type) [CommRing R] [Algebra F R] :
    sigR R (conj F E).toAlgHom = conjBase F E R := by
  refine RingHom.ext fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem hermValue_eq_hR (R : Type) [CommRing R] [Algebra F R] (H : Matrix (Fin n) (Fin n) E)
    (x : Fin n → R ⊗[F] E) : hermValue F H R x = hR R (conj F E).toAlgHom H x x := by
  rw [hR, sigR_conj]
  simp only [hermValue, Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc]
  rfl

theorem coords_algebraMap_mul_inclR (s : AF F) (z : E) :
    coords (Module.finBasis F E) (AF F)
        (algebraMap (AF F) (AF F ⊗[F] E) s * inclR (F := F) (AF F) z) =
      s • Reduction.ratVec (fun k => (Module.finBasis F E).repr z k) := by
  have e : algebraMap (AF F) (AF F ⊗[F] E) s * inclR (F := F) (AF F) z = s • ((1 : AF F) ⊗ₜ[F] z) := by
    simp [inclR, Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul']
  rw [e, map_smul]
  congr 1
  funext k
  simp [coords, Reduction.ratVec, Algebra.TensorProduct.basis_repr_tmul]

theorem exists_adelicNorm_hermPoly_le (H : Matrix (Fin n) (Fin n) E) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Fin (Bridge.dimN F E n) → AF F, Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent
        (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) ≤
        C * Reduction.adelicNorm y ^ 2 :=
  exists_adelicNorm_aeval_le (K := F) (d := 2) two_pos (hermPoly H (Module.finBasis F E))
    (fun v t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)
    (fun w t y k => by
      rw [aeval_hermPoly, aeval_hermPoly, hermCoords_smul]
      rfl)

theorem one_le_mul_hgt_sq (J H : Matrix (Fin n) (Fin n) E) {C : ℝ}
    (hCb : ∀ y : Fin (Bridge.dimN F E n) → AF F, Reduction.HasFiniteContent y →
      Reduction.HasFiniteContent
        (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) →
      Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H (Module.finBasis F E) k)) ≤
        C * Reduction.adelicNorm y ^ 2)
    (g : GAd (conj F E).toAlgHom J) {ξ : Fin n → E} (hξ : ξ ≠ 0)
    (s : GroundTheory.Global.IdeleGroup F) (hs : 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ))
    {z : E} (hz : z ≠ 0)
    (he : hR (AF F) (conj F E).toAlgHom H
        ((matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ)
        ((matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ) =
      algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) z) :
    1 ≤ C * hgt (conj F E).toAlgHom J g ξ ^ 2 := by
  set b := Module.finBasis F E with hb
  set v := (matHom _ (conj F E).toAlgHom J g⁻¹).1 *ᵥ ratV F ξ with hv
  set y : Fin (Bridge.dimN F E n) → AF F := resVec (ι := Fin n) b (AF F) v with hy
  have ey : Reduction.ratVec (Bridge.cvec F ξ) ᵥ*
      (Bridge.trG (conj F E).toAlgHom J g : Matrix _ _ (AF F)) = y := by
    rw [Bridge.ratVec_cvec, Bridge.trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hy, hv, map_inv]
  have hfy : Reduction.HasFiniteContent y := by
    rw [← ey]
    exact Reduction.hasFiniteContent_height _ (Bridge.cvec_ne_zero hξ)
  have hz' : (fun k => b.repr z k) ≠ 0 := by
    intro h0
    apply hz
    apply b.repr.injective
    ext k
    simpa using congrFun h0 k
  have e : (fun k => MvPolynomial.aeval y (hermPoly H b k)) =
      (s : AF F) • Reduction.ratVec (fun k => b.repr z k) := by
    funext k
    rw [aeval_hermPoly, hermCoords, hy, ofResVec_resVec, hermValue_eq_hR, he,
      coords_algebraMap_mul_inclR]
  have hfz : Reduction.HasFiniteContent (fun k => MvPolynomial.aeval y (hermPoly H b k)) := by
    rw [e]
    exact (Reduction.hasFiniteContent_ratVec hz').smul s
  have h1 : 1 ≤ Reduction.adelicNorm (fun k => MvPolynomial.aeval y (hermPoly H b k)) := by
    rw [e, Reduction.adelicNorm_smul (Reduction.hasFiniteContent_ratVec hz')]
    exact one_le_mul_of_one_le_of_one_le hs (Reduction.one_le_adelicNorm_ratVec hz')
  exact h1.trans (hCb y hfy hfz)

end Forms

theorem min_le_of_one_le_mul_sq {D t : ℝ} (hD : 0 < D) (ht : 0 ≤ t) (h : 1 ≤ D * t ^ 2) :
    min 1 D⁻¹ ≤ t := by
  by_cases h1 : 1 ≤ t
  · exact (min_le_left _ _).trans h1
  · replace h1 := not_le.1 h1
    have h3 : 1 ≤ D * t := by
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hD.le)
      nlinarith
    refine (min_le_right _ _).trans ?_
    rw [inv_le_iff_one_le_mul₀ hD, mul_comm]
    exact h3

theorem exists_pos_le_hgt_of_forms : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (H : M → Matrix (Fin n) (Fin n) E) (L : Set (GAd σ J)), (∀ ξ : Fin n → E, (∀ j, hE σ (H j) ξ ξ = 0) → ξ = 0) → (∀ g ∈ L, ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (H j) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J g⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (H j) ξ ξ)) → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ := by
  intro F E _ _ _ _ _ σ hCM n J _ M _ H L hzero hL
  obtain ⟨hF, hEc, h2, hc⟩ := hCM
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  cases nonempty_fintype M
  choose C hC hCb using fun j => exists_adelicNorm_hermPoly_le (F := F) (H j)
  have hsum : 0 ≤ ∑ j, C j := Finset.sum_nonneg fun j _ => (hC j).le
  have hD : 0 < 1 + ∑ j, C j := by linarith
  refine ⟨min 1 (1 + ∑ j, C j)⁻¹, lt_min one_pos (inv_pos.2 hD), fun g hg ξ hξ => ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, hE (conj F E).toAlgHom (H j) ξ ξ ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hξ (hzero ξ hno)
  obtain ⟨s, hs, he⟩ := hL g hg j
  have h1 := one_le_mul_hgt_sq J (H j) (hCb j) g hξ s hs hj (he ξ)
  have ht : 0 ≤ hgt (conj F E).toAlgHom J g ξ := Reduction.adelicNorm_nonneg _
  have hle : C j ≤ 1 + ∑ j, C j := by
    have := Finset.single_le_sum (f := C) (fun i _ => (hC i).le) (Finset.mem_univ j)
    linarith
  exact min_le_of_one_le_mul_sq hD ht
    (h1.trans (mul_le_mul_of_nonneg_right hle (sq_nonneg _)))

end GlobalTheory.CompanionTheory.ParCocompact.FormHeight

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImageZMCoordIdealOfEq
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

section Alg

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  {Ω₀ Ω : Type*} [Field Ω₀] [Field Ω]

def scaleT (c : K → Ω) : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω :=
  aeval fun k => C (c k) * X k

theorem scaleT_injective (c : K → Ω) (hc : ∀ k, c k ≠ 0) : Function.Injective (scaleT c) := by
  have h : (scaleT (fun k => (c k)⁻¹)).comp (scaleT c) = AlgHom.id Ω _ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    simp only [scaleT, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [MvPolynomial.algebraMap_eq, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact Function.LeftInverse.injective (g := scaleT fun k => (c k)⁻¹) fun f => by
    simpa using congrArg (fun g => g f) h

theorem imageZ_mCoordIdeal_of_eq (κ : K → K') (hκ : Function.Injective κ) (v : (Σ k, ι k) → (Σ k', ι' k'))
    (hv : ∀ p, (v p).1 = κ p.1) (φ : Ω₀ →+* Ω) (b : K → Ω) (hb : ∀ k, b k ≠ 0)
    (y₀ : (Σ k, ι k) → Ω₀) (y : (Σ k', ι' k') → Ω) (h : ∀ p, φ (y₀ p) = b p.1 * y (v p)) :
    imageZ v (Geo.mCoordIdeal y) = Geo.mCoordIdeal y₀ := by
  let ψ : MvPolynomial K Ω₀ →+* MvPolynomial K' Ω :=
    ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).toRingHom.comp
      (scaleT fun k => (b k)⁻¹).toRingHom).comp (MvPolynomial.map φ)
  have hψ : Function.Injective ψ :=
    (rename_injective κ hκ).comp ((scaleT_injective _ fun k => inv_ne_zero (hb k)).comp
      (map_injective φ φ.injective))
  have key : ∀ f : Geo.MRing ι, ψ (Geo.mConeMap y₀ f) = Geo.mConeMap y (rename v f) := by
    intro f
    have e : ψ.comp (Geo.mConeMap y₀ : Geo.MRing ι →ₐ[ℤ] MvPolynomial K Ω₀).toRingHom =
        ((Geo.mConeMap y : Geo.MRing ι' →ₐ[ℤ] MvPolynomial K' Ω).toRingHom.comp
          (rename v : Geo.MRing ι →ₐ[ℤ] Geo.MRing ι').toRingHom) := by
      refine MvPolynomial.ringHom_ext (fun r => ?_) (fun p => ?_)
      · simp
      · simp only [ψ, Geo.mConeMap, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
          rename_X, map_mul, map_C, map_X, scaleT, algHom_C, rename_C]
        rw [hv p, h p]
        simp only [MvPolynomial.algebraMap_eq, rename_C]
        rw [← mul_assoc, ← C_mul, mul_comm (b p.1), mul_assoc, mul_inv_cancel₀ (hb p.1), mul_one]
    exact congrArg (fun g => g f) e
  ext f
  simp only [imageZ, Geo.mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← key, map_eq_zero_iff ψ hψ]

end Alg

end GlobalTheory.CompanionTheory.MPDict.ProjImage

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

theorem evaluation_resG {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (x : X) (hx : x ∈ V) (s : Γ(X, U)) :
    X.evaluation V x hx (resG X h s) = X.evaluation U x (h hx) s := by
  show X.residue x (X.presheaf.germ V x hx (X.presheaf.map (homOfLE h).op s)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

theorem ptCoord_qpSnd (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) (k : Fin (m + 1)) :
    ∃ b : (MP ℤ (m + 1) (consN n' n)).residueField x, b ≠ 0 ∧ ∀ i : Bk n k,
      (qpSnd n' m n).residueFieldMap x (ptCoord (qpSnd n' m n x) ⟨k, i⟩) = b * ptCoord x ⟨k.succ, i⟩ := by
  let F : MP ℤ (m + 1) (consN n' n) ⟶ MP ℤ m n := qpSnd n' m n
  let P : MP ℤ (m + 1) (consN n' n) ⟶ PSpace ℤ (n k) := prB (consN n' n) k.succ
  have hP : F ≫ prB n k = P := rfl
  let c₀ := ptChart (F x) k
  let c₁ := ptChart x k.succ
  have hx₀ : F x ∈ blockChart n k c₀ := mem_ptChart _ _
  have hx₁ : x ∈ blockChart (consN n' n) k.succ c₁ := mem_ptChart _ _
  let W₀ : (MP ℤ (m + 1) (consN n' n)).Opens := F ⁻¹ᵁ blockChart n k c₀
  let W₁ : (MP ℤ (m + 1) (consN n' n)).Opens := blockChart (consN n' n) k.succ c₁
  have h₀ : W₀ ≤ P ⁻¹ᵁ chart ℤ (n k) c₀ := le_rfl
  have h₁ : W₁ ≤ P ⁻¹ᵁ chart ℤ (n k) c₁ := le_rfl
  let V := W₀ ⊓ W₁
  have hxV : x ∈ V := ⟨hx₀, hx₁⟩
  have hV₀ : V ≤ P ⁻¹ᵁ chart ℤ (n k) c₀ := inf_le_left.trans h₀
  have hV₁ : V ≤ P ⁻¹ᵁ chart ℤ (n k) c₁ := inf_le_right.trans h₁
  have e₀ : ∀ i : Bk n k, F.residueFieldMap x (ptCoord (F x) ⟨k, i⟩) =
      (MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₀ hV₀ i) := by
    intro i
    show F.residueFieldMap x ((MP ℤ m n).evaluation (blockChart n k c₀) (F x) hx₀
      (pullRatio (prB n k) _ c₀ le_rfl i)) = _
    rw [Scheme.evaluation_naturality_apply, Scheme.Hom.app_eq_appLE, appLE_pullRatio,
      ← evaluation_resG (inf_le_left : V ≤ W₀) x hxV, resG_pullRatio]
    rfl
  have e₁ : ∀ i : Bk n k, ptCoord x ⟨k.succ, i⟩ =
      (MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₁ hV₁ i) := by
    intro i
    show (MP ℤ (m + 1) (consN n' n)).evaluation W₁ x hx₁ (pullRatio P W₁ c₁ h₁ i) = _
    rw [← evaluation_resG (inf_le_right : V ≤ W₁) x hxV]
    exact congrArg _ (resG_pullRatio (φ := P) (hi := h₁) inf_le_right)
  refine ⟨(MP ℤ (m + 1) (consN n' n)).evaluation V x hxV (pullRatio P V c₀ hV₀ c₁), ?_, fun i => ?_⟩
  · intro h0
    have e := congrArg ((MP ℤ (m + 1) (consN n' n)).evaluation V x hxV)
      ((pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := c₀)).trans pullRatio_self)
    rw [map_mul, h0, zero_mul, map_one] at e
    exact zero_ne_one e
  · refine (e₀ i).trans ?_
    rw [e₁ i, ← map_mul]
    exact congrArg _ (pullRatio_mul_pullRatio (φ := P) (hi := hV₀) (hj := hV₁) (k := i)).symm

end GlobalTheory.CompanionTheory.MPDict.ProjImage

namespace GlobalTheory.CompanionTheory.MPDict.ProjImage

theorem imageZ_ptIdeal (n' m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ (m + 1) (consN n' n)) :
    imageZ (sv n' n) (ptIdeal x) = ptIdeal (qpSnd n' m n x) := by
  choose b hb h using ptCoord_qpSnd n' m n x
  exact imageZ_mCoordIdeal_of_eq Fin.succ (Fin.succ_injective _) (sv n' n) (fun _ => rfl)
    ((qpSnd n' m n).residueFieldMap x).hom b hb (ptCoord (qpSnd n' m n x)) (ptCoord x) fun p => h p.1 p.2

end GlobalTheory.CompanionTheory.MPDict.ProjImage
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectivePairingFiniteFamily
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WSum.Sep

variable {D : D7} {r : ℕ}

theorem theta_incA {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (x : D.host.E) :
    θ τ (infPart D (incA D x)) = tauE D τ x := by
  have h : infPart D (incA D x) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] x := by
    simp [infPart, incA, inclR]
  rw [h]
  exact (hθ τ).1 x

theorem pairF_eq {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (a β : HermE D r) :
    pairF θ α a β =
      -∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (β.1 * a.1))).re := by
  unfold pairF lam
  simp only [← map_mul, theta_incA hθ]

def hermQ (D : D7) (r : ℕ) : Submodule ℚ (Matrix (Fin r) (Fin r) D.host.E) where
  carrier := {b | (b.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose = b}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    ext i j
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h1 h2 ⊢
    simp only [Matrix.add_apply, map_add, h1, h2]
  zero_mem' := by
    ext i j
    simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    ext i j
    have h1 := congrFun (congrFun ha i) j
    simp only [Matrix.transpose_apply, Matrix.map_apply] at h1 ⊢
    simp only [Matrix.smul_apply, map_rat_smul, h1]

theorem tau_nonempty (D : D7) : Nonempty D.what₂.Tau := by
  obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace D.host.F) := inferInstance
  obtain ⟨τ, -⟩ := (GlobalTheory.CMTypePlaces.places_bijective D).2 w
  exact ⟨τ⟩

theorem mem_hermQ {b : Matrix (Fin r) (Fin r) D.host.E} :
    b ∈ hermQ D r ↔ ∀ i j, D.sp.cm.sig (b j i) = b i j := by
  constructor
  · intro h i j
    exact congrFun (congrFun h i) j
  · intro h
    exact Matrix.ext fun i j => h i j

def formH (α : D.host.F) (δ : Matrix (Fin r) (Fin r) D.host.E) : hermQ D r →+ ℝ :=
  AddMonoidHom.mk'
    (fun a => ∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (δ * a.1))).re)
    (by
      intro a b
      simp only [Submodule.coe_add, mul_add, Matrix.trace_add, map_add, Complex.add_re,
        Finset.sum_add_distrib])

theorem formH_apply (α : D.host.F) (δ : Matrix (Fin r) (Fin r) D.host.E) (a : hermQ D r) :
    formH α δ a =
      ∑ τ, (tauE D τ (algebraMap D.host.F D.host.E α * Matrix.trace (δ * a.1))).re := rfl

theorem formH_eq_zero {d : ℕ} (b : Module.Basis (Fin d) ℚ (hermQ D r)) {α : D.host.F}
    {δ : Matrix (Fin r) (Fin r) D.host.E} (h : ∀ k, formH α δ (b k) = 0) (a : hermQ D r) :
    formH α δ a = 0 := by
  have e : (formH α δ).toRatLinearMap = 0 := b.ext (fun k => by simpa using h k)
  simpa using LinearMap.congr_fun e a

theorem formH_sub_left (α : D.host.F) (b b' : Matrix (Fin r) (Fin r) D.host.E) (a : hermQ D r) :
    formH α (b - b') a = formH α b a - formH α b' a := by
  simp only [formH_apply, sub_mul, Matrix.trace_sub, mul_sub, map_sub, Complex.sub_re,
    Finset.sum_sub_distrib]

theorem pairF_eq_formH {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (β : HermE D r)
    (a : hermQ D r) : pairF θ α ⟨a.1, a.2⟩ β = -formH α β.1 a :=
  pairF_eq hθ α ⟨a.1, a.2⟩ β

theorem formH_sub {θ : InfFam D} (hθ : IsInfFam θ) (α : D.host.F) (β β' : HermE D r)
    (a : hermQ D r) :
    formH α (β.1 - β'.1) a = pairF θ α ⟨a.1, a.2⟩ β' - pairF θ α ⟨a.1, a.2⟩ β := by
  have e := pairF_eq_formH hθ α β a
  have e' := pairF_eq_formH hθ α β' a
  have e'' := formH_sub_left α β.1 β'.1 a
  linarith

theorem trace_sq_ne_zero {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) (h0 : δ ≠ 0) :
    Matrix.trace (δ * δ) ≠ 0 := by
  intro hn
  obtain ⟨τ⟩ := tau_nonempty D
  have hm := mem_hermQ.1 hδ
  have hcm := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hc : ∀ i j, tauE D τ (δ j i) = starRingEnd ℂ (tauE D τ (δ i j)) := by
    intro i j
    rw [← hm j i]
    exact hcm.2.2.2 _ _
  have hs : ((∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j)) : ℝ) : ℂ) = 0 := by
    have e : tauE D τ (Matrix.trace (δ * δ)) =
        ((∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j)) : ℝ) : ℂ) := by
      push_cast
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hc i j, Complex.mul_conj]
    rw [← e, hn, map_zero]
  have hs' : (∑ i, ∑ j, Complex.normSq (tauE D τ (δ i j))) = 0 := by exact_mod_cast hs
  apply h0
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)).1 hs' i (Finset.mem_univ i)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg _)).1 h1 j (Finset.mem_univ j)
  have h3 : tauE D τ (δ i j) = 0 := Complex.normSq_eq_zero.1 h2
  simpa using h3

theorem sig_trace_sq {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) :
    D.sp.cm.sig (Matrix.trace (δ * δ)) = Matrix.trace (δ * δ) := by
  have hm := mem_hermQ.1 hδ
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum, map_mul, hm]
  rw [Finset.sum_comm]

theorem inv_smul_mem {δ : Matrix (Fin r) (Fin r) D.host.E} (hδ : δ ∈ hermQ D r) {x : D.host.E}
    (hx : D.sp.cm.sig x = x) : x⁻¹ • δ ∈ hermQ D r := by
  have hm := mem_hermQ.1 hδ
  refine mem_hermQ.2 fun i j => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hx, hm]

theorem exists_separating : ∀ (D : D7) (r : ℕ) (θ : InfFam D), IsInfFam θ → ∀ α : D.host.F, α ≠ 0 →
    ∃ (d : ℕ) (a : Fin d → HermE D r),
      Function.Injective (fun (β : HermE D r) (k : Fin d) => pairF θ α (a k) β) := by
  intro D r θ hθ α hα
  let b := Module.finBasis ℚ (hermQ D r)
  refine ⟨_, fun k => ⟨(b k).1, (b k).2⟩, ?_⟩
  intro β β' h
  by_contra hne
  have hδ : β.1 - β'.1 ∈ hermQ D r :=
    sub_mem (show β.1 ∈ hermQ D r from β.2) (show β'.1 ∈ hermQ D r from β'.2)
  have hδ0 : β.1 - β'.1 ≠ 0 := sub_ne_zero.2 fun e => hne (Subtype.ext e)
  have hz : ∀ a, formH α (β.1 - β'.1) a = 0 := by
    refine formH_eq_zero b fun k => ?_
    rw [formH_sub hθ]
    have := congrFun h k
    exact sub_eq_zero.2 this.symm
  set δ := β.1 - β'.1 with hδdef
  have hn := trace_sq_ne_zero hδ hδ0
  have hαE : algebraMap D.host.F D.host.E α ≠ 0 := by
    simpa using hα
  set x := algebraMap D.host.F D.host.E α * Matrix.trace (δ * δ) with hx
  have hx0 : x ≠ 0 := mul_ne_zero hαE hn
  have hxs : D.sp.cm.sig x = x := by
    rw [hx, map_mul, sig_trace_sq hδ, AlgHom.commutes]
  have hv := hz ⟨x⁻¹ • δ, inv_smul_mem hδ hxs⟩
  rw [formH_apply] at hv
  have h1 : algebraMap D.host.F D.host.E α * Matrix.trace (δ * (x⁻¹ • δ)) = 1 := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc, mul_comm _ x⁻¹, mul_assoc,
      ← hx, inv_mul_cancel₀ hx0]
  simp only [h1, map_one, Complex.one_re, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hv
  haveI := tau_nonempty D
  have : (Fintype.card D.what₂.Tau : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact this hv

end GlobalTheory.CompanionTheory.WSum.Sep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LaplacianMonicAnnihilatorMeasureStatement
section
set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laplacian_monic_annihilator_measure : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ψ : AutomorphicForm.archSmooth K n) (d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra K n).lieSubalgebra) (P : Polynomial ℂ),
    P.Monic → 0 < P.natDegree →
    (∀ g, Polynomial.aeval ((AutomorphicForm.isExpLieAlgebra K n).laplacian (F := ℂ) b) P
      (AutomorphicForm.sliceL g ψ) = 0) →
    ∀ [MeasurableSpace (AutomorphicForm.archGroup K n)] [BorelSpace (AutomorphicForm.archGroup K n)]
      (μ : MeasureTheory.Measure (AutomorphicForm.archGroup K n)) [μ.IsHaarMeasure]
      (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim K n)),
      ∃ D : AutomorphicForm.archGroup K n → ℂ, Continuous D ∧ HasCompactSupport D ∧
        ∀ g : AdelicGLn.AdelicGL K n,
          ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := K) (n := n) k J) ψ :
            ↥(AutomorphicForm.archSmooth K n)) : AdelicGLn.AdelicGL K n → ℂ) g =
            ∫ y, (ψ : AdelicGLn.AdelicGL K n → ℂ) (g * AutomorphicForm.infEmb K n y) * D y ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.ConvLap.exists_conv_uJ_of_aeval_laplacian | exact GlobalTheory.CompanionTheory.HCRep.ConvLap.exists_conv_uJ_of_aeval_laplacian | (intros; apply GlobalTheory.CompanionTheory.HCRep.ConvLap.exists_conv_uJ_of_aeval_laplacian <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthVanishingStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_depth_vanishing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → IsSmooth T → TwInv T T' B s → ∀ (b : Fin (n + 1) → k) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V'), valuation k (b (Fin.last n)) < 1 → T (levi k (n + 1) (shearGL n b)) v = v → (∀ x, ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ M ↔ x ∈ M) → ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = JJ ν ψ T B M v (T' (levi k (n + 1) (shearGL n b)) v') := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear | exact GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear | (intros; apply GlobalTheory.CompanionTheory.MirPair.twist_integral_eq_JJ_shear <;> assumption)
end

