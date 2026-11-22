import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0254
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarPosAllPlacesOfConjugateIdentity
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualBesselCoreVertexLattice
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.CoreSelfDual

variable {D : D7}

theorem form_eq (S : HSp D) (x y : Fin S.rank → D.host.E) :
    ∑ i, ∑ j, star (x i) * S.gram i j * y j = star x ⬝ᵥ S.gram *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

variable {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem wittHyperbolicRankZero_proj_mul_emb (y : Fin S₀.rank → D.host.E) : d.q0 *ᵥ (d.i₀ *ᵥ y) = y := by
  have hq : d.q0 * d.i₀ = 1 := by
    calc d.q0 * d.i₀ = S₀.gram⁻¹ * (d.i₀ᴴ * S.gram * d.i₀) := by
          simp only [HypDec.q0, Matrix.mul_assoc]
      _ = 1 := by rw [d.iso]; exact Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det S₀)
  rw [Matrix.mulVec_mulVec, hq, Matrix.one_mulVec]

theorem wittCoreProjection_adjoint_coreEmbedding (x : Fin S.rank → D.host.E) (y : Fin S₀.rank → D.host.E) :
    star (d.q0 *ᵥ x) ⬝ᵥ S₀.gram *ᵥ y = star x ⬝ᵥ S.gram *ᵥ (d.i₀ *ᵥ y) := by
  have hM : d.q0ᴴ * S₀.gram = S.gram * d.i₀ := by
    simp only [HypDec.q0, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      GlobalTheory.MixModel.gram_conjTranspose, GlobalTheory.MixModel.gramInv_conjTranspose, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det S₀), Matrix.mul_one]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, hM]

theorem isSelfDualC_comap {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (hΛ : IsSelfDualC S Λ)
    (hP : ∀ x ∈ Λ, d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ Λ) :
    IsSelfDualC S₀ (Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E))) := by
  unfold IsSelfDualC at hΛ ⊢
  obtain ⟨hlat, hdual⟩ := hΛ
  have hq : ∀ y, d.q0 *ᵥ (d.i₀ *ᵥ y) = y := GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb d
  have hmem : ∀ y, y ∈ Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) ↔ d.i₀ *ᵥ y ∈ Λ :=
    fun y => Iff.rfl
  have heq : Λ.comap ((Matrix.mulVecLin d.i₀).restrictScalars (𝓞 D.host.E)) =
      Λ.map ((Matrix.mulVecLin d.q0).restrictScalars (𝓞 D.host.E)) := by
    ext y
    rw [hmem, Submodule.mem_map]
    constructor
    · intro hy
      exact ⟨_, hy, hq y⟩
    · rintro ⟨x, hx, rfl⟩
      exact hP x hx
  refine ⟨?_, fun y => ?_⟩
  · rw [heq]
    refine ⟨hlat.fg.map _, ?_⟩
    rw [Submodule.map_coe]
    change Submodule.span D.host.E ((Matrix.mulVecLin d.q0) '' (Λ : Set (Fin S.rank → D.host.E))) = ⊤
    rw [Submodule.span_image, hlat.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact fun y => ⟨d.i₀ *ᵥ y, hq y⟩
  · rw [hmem]
    constructor
    · intro hy x hx
      rw [hmem] at hx
      obtain ⟨b, hb⟩ := (hdual (d.i₀ *ᵥ y)).1 hy (d.i₀ *ᵥ x) hx
      refine ⟨b, ?_⟩
      rw [hb, GlobalTheory.AscFin.CoreSelfDual.form_eq, GlobalTheory.AscFin.CoreSelfDual.form_eq, ← d.iso,
        Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · intro hy
      refine (hdual (d.i₀ *ᵥ y)).2 fun w hw => ?_
      obtain ⟨b, hb⟩ := hy (d.q0 *ᵥ w) (hP w hw)
      refine ⟨b, ?_⟩
      rw [hb, GlobalTheory.AscFin.CoreSelfDual.form_eq, GlobalTheory.AscFin.CoreSelfDual.form_eq,
        GlobalTheory.AscFin.CoreSelfDual.wittCoreProjection_adjoint_coreEmbedding]

theorem mulVec_col_eq_zero {n k c r : ℕ} {q : Matrix (Fin k) (Fin n) D.host.E} {a : Matrix (Fin n) (Fin c) D.host.E}
    {f : Fin r → Fin c} {s : Fin r → D.host.E} (h : q * colsOf a f s = 0) {p : Fin r} (hs : s p ≠ 0) :
    q *ᵥ (fun i => a i (f p)) = 0 := by
  funext i
  have h1 := congrFun (congrFun h i) p
  simp only [Matrix.mul_apply, colsOf, Matrix.zero_apply] at h1
  have h2 : s p * (q *ᵥ (fun i => a i (f p))) i = 0 := by
    rw [← h1]
    simp only [mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  exact (mul_eq_zero.mp h2).resolve_left hs

theorem wittCoreProjection_kills_offMiddle_auxiliaryVectors {A : HSp D} {c : ℕ} (a : HermitianOrthogonalExtensionData A S c (-1)) (h : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ + 1) (p : Fin c) (hp : p.1 ≠ ρ) :
    d.q0 *ᵥ (fun i => a.a i p) = 0 := by
  subst hc
  obtain ⟨h2, he, s, he'⟩ := h
  have hqe : d.q0 * d.e = 0 := by
    simp only [HypDec.q0, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc d.i₀ᴴ, d.i₀e, Matrix.mul_zero]
  have hqe' : d.q0 * d.e' = 0 := by
    simp only [HypDec.q0, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc d.i₀ᴴ, d.i₀e', Matrix.mul_zero]
  rw [he] at hqe
  rw [he'] at hqe'
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · have := GlobalTheory.AscFin.CoreSelfDual.mulVec_col_eq_zero hqe (p := ⟨p.1, hlt⟩) (pow_ne_zero _ (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero))
    rw [show p = Fin.castLE (by omega) (⟨p.1, hlt⟩ : Fin ρ) from Fin.ext rfl]
    exact this
  · have hk : 2 * ρ - p.1 < ρ := by omega
    have hsk : s ⟨2 * ρ - p.1, hk⟩ ≠ 0 := by
      intro h0
      have h1 := congrFun (congrFun d.e'e ⟨2 * ρ - p.1, hk⟩) ⟨2 * ρ - p.1, hk⟩
      rw [he'] at h1
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, colsOf, h0] at h1
    have := GlobalTheory.AscFin.CoreSelfDual.mulVec_col_eq_zero hqe' hsk
    rw [show p = (Fin.castLE (by omega) (⟨2 * ρ - p.1, hk⟩ : Fin ρ) : Fin (2 * ρ + 1)).rev from
      Fin.ext (by simp only [Fin.val_rev, Fin.coe_castLE]; omega)]
    exact this

private theorem mulVec_eq_sum_smul_col {R : Type} [CommRing R] {n c : ℕ} (M : Matrix (Fin n) (Fin c) R) (u : Fin c → R) :
    M *ᵥ u = ∑ p, u p • (fun i => M i p) := by
  funext i
  simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem proj_mem {A : HSp D} {c : ℕ} (a : HermitianOrthogonalExtensionData A S c (-1)) (h : IsAuxiliaryVectorWittDec a d) (hc : c = 2 * ρ + 1)
    {N : Matrix (Fin S₀.rank) (Fin A.rank) D.host.E} (hN : d.i₀ * N = frameMat S A a.ι) {z : Fin S₀.rank → D.host.E}
    (hz : d.i₀ *ᵥ z = fun i => a.a i ⟨ρ, by omega⟩) {Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)}
    {𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {x : Fin S.rank → D.host.E} (hx : x ∈ a.lat Λ 𝔟) :
    d.i₀ *ᵥ (d.q0 *ᵥ x) ∈ a.lat Λ 𝔟 := by
  obtain ⟨y, hy, u, hu, rfl⟩ := hx
  have hcol : ∀ p : Fin c, d.q0 *ᵥ (fun i => a.a i p) =
      if p = (⟨ρ, by omega⟩ : Fin c) then z else 0 := by
    intro p
    split_ifs with hp
    · have hpz : (fun i => a.a i p) = d.i₀ *ᵥ z := by rw [hz, hp]
      rw [hpz, GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb]
    · exact GlobalTheory.AscFin.CoreSelfDual.wittCoreProjection_kills_offMiddle_auxiliaryVectors d a h hc p (fun e => hp (Fin.ext e))
  have h1 : d.i₀ *ᵥ (d.q0 *ᵥ (frameMat S A a.ι *ᵥ y)) = frameMat S A a.ι *ᵥ y := by
    rw [← hN, ← Matrix.mulVec_mulVec, GlobalTheory.AscFin.CoreSelfDual.wittHyperbolicRankZero_proj_mul_emb]
  have h2 : d.q0 *ᵥ (a.a *ᵥ u) = u ⟨ρ, by omega⟩ • z := by
    rw [mulVec_eq_sum_smul_col a.a u, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hcol, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  show ∃ y' ∈ Λ, ∃ u' : Fin c → D.host.E, (∀ p, u' p ∈ 𝔟 p) ∧
    d.i₀ *ᵥ (d.q0 *ᵥ (frameMat S A a.ι *ᵥ y + a.a *ᵥ u)) = frameMat S A a.ι *ᵥ y' + a.a *ᵥ u'
  refine ⟨y, hy, fun p => if p = (⟨ρ, by omega⟩ : Fin c) then u p else 0, fun p => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hu p
    · exact (𝔟 p).zero_mem
  · rw [Matrix.mulVec_add, Matrix.mulVec_add, h1, h2, Matrix.mulVec_smul, hz, mulVec_eq_sum_smul_col a.a]
    congr 1
    simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GlobalTheory.AscFin.CoreSelfDual

namespace GlobalTheory.AscFin

theorem isSelfDualC_lat0 {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G) (hF : Std F)
    (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) : IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) := by
  have h1 : 1 ≤ 2 * ρ + 2 := by omega
  have e : G.Λ (.grid (2 * ρ + 2) 0) =
      (G.colDec (2 * ρ + 2) h1 h).lat (G.Λ (.core (2 * ρ + 2))) (stairId _ _ _) :=
    G.sp.colLat (2 * ρ + 2) h1 h
  have hc : 2 * ρ + 2 - 1 = 2 * ρ + 1 := by omega
  show IsSelfDualC (F.V₀ ρ) ((G.Λ (.grid (2 * ρ + 2) 0)).comap
    ((Matrix.mulVecLin (F.dB ρ h).i₀).restrictScalars (𝓞 D.host.E)))
  refine CoreSelfDual.isSelfDualC_comap (F.dB ρ h) (G.sp.V_is (2 * ρ + 2) 0 h1 h (Nat.zero_le _)).sd ?_
  intro x hx
  rw [e] at hx ⊢
  refine CoreSelfDual.proj_mem (F.dB ρ h) _ (hF.hB ρ h) hc (N := (F.oB ρ h).iA) (hF.aB ρ h)
    (z := (F.oB ρ h).iB *ᵥ F.ζ 0) ?_ hx
  rw [Matrix.mulVec_mulVec]
  exact hF.zB' ρ h

end GlobalTheory.AscFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualFractionalIdealSmulLatticeOfNormOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.IdLatDual

variable {D : D7}

def hp (S : HSp D) (x y : Fin S.rank → D.host.E) : D.host.E :=
  ∑ i, ∑ j, star (x i) * S.gram i j * y j

def IsO (z : D.host.E) : Prop := ∃ b : 𝓞 D.host.E, (b : D.host.E) = z

lemma isO_zero : IsO (0 : D.host.E) := ⟨0, by simp⟩
lemma isO_add {z w : D.host.E} (hz : IsO z) (hw : IsO w) : IsO (z + w) := by
  obtain ⟨b, rfl⟩ := hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b + c, by push_cast; rfl⟩
lemma isO_mul {z w : D.host.E} (hz : IsO z) (hw : IsO w) : IsO (z * w) := by
  obtain ⟨b, rfl⟩ := hz; obtain ⟨c, rfl⟩ := hw; exact ⟨b * c, by push_cast; rfl⟩
lemma isO_coe (a : 𝓞 D.host.E) : IsO (a : D.host.E) := ⟨a, rfl⟩
lemma isO_star (a : 𝓞 D.host.E) : IsO (star (a : D.host.E)) := by
  refine ⟨⟨star (a : D.host.E), ?_⟩, rfl⟩
  exact (RingOfIntegers.isIntegral_coe a).map (starRingEnd D.host.E).toIntAlgHom
lemma isO_of_mem_one {z : D.host.E} (h : z ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) : IsO z := by
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 h
  exact ⟨b, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hb⟩

lemma osmul {n : ℕ} (a : 𝓞 D.host.E) (x : Fin n → D.host.E) : a • x = (a : D.host.E) • x := by
  ext i; simp [Algebra.smul_def, RingOfIntegers.coe_eq_algebraMap]

variable (S : HSp D)

lemma hp_add_left (x x' y) : hp S (x + x') y = hp S x y + hp S x' y := by
  simp only [hp, Pi.add_apply, star_add, add_mul, Finset.sum_add_distrib]
lemma hp_add_right (x y y') : hp S x (y + y') = hp S x y + hp S x y' := by
  simp only [hp, Pi.add_apply, mul_add, Finset.sum_add_distrib]
lemma hp_zero_left (y) : hp S 0 y = 0 := by simp [hp]
lemma hp_zero_right (x) : hp S x 0 = 0 := by simp [hp]
lemma hp_smul_left (s : D.host.E) (x y) : hp S (s • x) y = star s * hp S x y := by
  simp only [hp, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
lemma hp_smul_right (t : D.host.E) (x y) : hp S x (t • y) = t * hp S x y := by
  simp only [hp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.IdLatDual

open GlobalTheory.IdLatDual in
lemma GlobalTheory.IdLatDual.idLat_fg {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hΛ : Λ.FG)
    (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : (idLat I Λ).FG := by
  obtain ⟨a, ha, hint⟩ := I.isFractional
  let f : (Fin n → D.host.E) →ₗ[𝓞 D.host.E] (Fin n → D.host.E) := LinearMap.lsmul (𝓞 D.host.E) (Fin n → D.host.E) a
  have hle : (idLat I Λ).map f ≤ Λ := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨s, hs, y, hy, rfl⟩
    obtain ⟨r, hr⟩ := hint s hs
    show a • (s • y) ∈ Λ
    rw [← smul_assoc, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ hy
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hinj : Function.Injective f := by
    intro x x' h
    have h' : a • x = a • x' := h
    rw [osmul, osmul] at h'
    have : (a : D.host.E) ≠ 0 := fun h0 => ha0 (RingOfIntegers.coe_eq_zero_iff.1 h0)
    exact smul_right_injective _ this h'
  have hfg : ((idLat I Λ).map f).FG := Submodule.FG.of_le hΛ hle
  exact Submodule.fg_of_fg_map_injective f hinj hfg

open GlobalTheory.IdLatDual in

theorem GlobalTheory.idLat_isSelfDualC : ∀ {D : D7} (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (I I' : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), IsSelfDualC S Λ → I * I' = 1 →
    (∀ x : D.host.E, x ∈ I' ↔ star x ∈ I) → IsSelfDualC S (idLat I Λ) := by
  intro D S Λ I I' hΛ hII' hconj
  obtain ⟨hlat, hdual⟩ := hΛ
  have intL : ∀ x ∈ Λ, ∀ y ∈ Λ, IsO (hp S x y) := fun x hx y hy => (hdual y).1 hy x hx
  have gen : ∀ s ∈ I, ∀ y ∈ Λ, s • y ∈ idLat I Λ := fun s hs y hy =>
    Submodule.subset_span ⟨s, hs, y, hy, rfl⟩
  have one_mem : (1 : D.host.E) ∈ I * I' := by rw [hII']; exact FractionalIdeal.one_mem_one _

  have hspan : ∀ y ∈ Λ, y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E)) := by
    intro y hy
    have key : ∀ z ∈ I * I', z • y ∈ Submodule.span D.host.E (idLat I Λ : Set (Fin S.rank → D.host.E)) := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun i hi c _ => ?_) (fun a b ha hb => ?_)
      · rw [mul_comm, mul_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (gen i hi y hy))
      · rw [add_smul]; exact Submodule.add_mem _ ha hb
    simpa using key 1 one_mem
  have hfg : (idLat I Λ).FG := idLat_fg Λ hlat.fg I
  refine ⟨⟨hfg, ?_⟩, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · rw [eq_top_iff, ← hlat.span_eq_top, Submodule.span_le]
    exact hspan
  ·
    have stepA : ∀ s ∈ I, ∀ x₀ ∈ Λ, ∀ y ∈ idLat I Λ, IsO (hp S (s • x₀) y) := by
      intro s hs x₀ hx₀ y hy
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨t, ht, y₀, hy₀, rfl⟩ := hz
        rw [hp_smul_left, hp_smul_right, ← mul_assoc]
        refine isO_mul (isO_of_mem_one ?_) (intL x₀ hx₀ y₀ hy₀)
        rw [← hII', mul_comm I]
        exact FractionalIdeal.mul_mem_mul ((hconj _).2 (by rwa [star_star])) ht
      | zero => rw [hp_zero_right]; exact isO_zero
      | add a b _ _ ha hb => rw [hp_add_right]; exact isO_add ha hb
      | smul c z _ hz => rw [osmul, hp_smul_right]; exact isO_mul (isO_coe c) hz
    intro x hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, hs, x₀, hx₀, rfl⟩ := hz
      obtain ⟨b, hb⟩ := stepA s hs x₀ hx₀ y hy
      exact ⟨b, hb⟩
    | zero => exact ⟨0, by rw [← hp, hp_zero_left]; simp⟩
    | add a b _ _ ha hb =>
      have h : IsO (hp S a y + hp S b y) := isO_add ha hb
      rw [← hp_add_left] at h
      exact h
    | smul c z _ hz =>
      obtain ⟨u, hu⟩ := isO_mul (isO_star c) hz
      exact ⟨u, by rw [← hp, osmul, hp_smul_left]; exact hu⟩
  · have hint : ∀ x ∈ idLat I Λ, IsO (hp S x y) := fun x hx => hy x hx
    have key : ∀ z ∈ I * I', z • y ∈ idLat I Λ := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz (fun i hi c hc => ?_) (fun a b ha hb => ?_)
      · rw [mul_smul]
        refine gen i hi _ ((hdual _).2 fun x' hx' => ?_)
        have hsc : star c ∈ I := (hconj c).1 hc
        obtain ⟨b, hb⟩ := hint _ (gen _ hsc x' hx')
        refine ⟨b, ?_⟩
        rw [hb]
        show hp S (star c • x') y = hp S x' (c • y)
        rw [hp_smul_left, hp_smul_right, star_star]
      · rw [add_smul]; exact Submodule.add_mem _ ha hb
    simpa using key 1 one_mem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicConditionLastTorusDiagonalIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
noncomputable section

namespace GlobalTheory.AscFin.IsoDiag

set_option maxHeartbeats 1000000 in

theorem last_diag_int_iso : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → (0 < ρ → ∀ a ∈ idAt D (· = v), dW.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v)) → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∀ ξ ∈ p.B₁, ∀ ξ' : Mx D ρ V₀.rank, MxAt (· = v) ξ → mt W (dW.levi t) ⬝ dW.incX V₀ ξ = dW.incX V₀ ξ' → ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ')) = ψ (symplO V₀ W (dW.incAdj V₀ (yZero V₀ ρ z)) (dW.incX V₀ ξ))) → ∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ hstd V V₀ W W₀ ρ dV dW p z LV LV₀ LW LW₀ v hG hS hlast t ht htG hiso i hi
  obtain ⟨eV, heV_int, heV_act, heV_cA, -⟩ := GlobalTheory.FinPl.LastDiag.exists_idemAt D v
  have heV_id : eV ∈ idAt D (· = v) := heV_int.1
  have hcA : ∀ c ∈ idAt D (· = v), cA D c ∈ idAt D (· = v) := fun c hc => by
    rw [← heV_act c hc, map_mul, heV_cA]; exact Ideal.mul_mem_left _ _ heV_id
  have hMx : ∀ c ∈ idAt D (· = v), MxAt (· = v) (dW.incAdj V₀ (c • yZero V₀ ρ z)) :=
    fun c hc k l => by
      rw [GlobalTheory.FinPl.LastDiag.incAdj_smul, Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (hcA c hc)
  have hcong := (GlobalTheory.IwaPlace.mem_congGrp_iff W (idAt D (· = v)) _).1 htG
  have hM : MxAt (· = v) (mt W (dW.levi t) - 1) := fun k l => by rw [Matrix.sub_apply]; exact hcong k l
  have htM : t.1 - 1 = dW.pX ⬝ (mt W (dW.levi t) - 1) ⬝ dW.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, dW.pX_levi t, Matrix.mul_one, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
  have ha : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := GlobalTheory.FinPl.LastDiag.mxAt_mul_right (GlobalTheory.FinPl.LastDiag.mxAt_mul_left dW.pX hM) dW.jX i i
    rwa [← htM, Matrix.sub_apply, Matrix.one_apply_eq] at this
  have hρ : 0 < ρ := by omega
  rw [← hlast hρ _ ha]
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hstd V₀ W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ ha)).2 fun u' hu' => ?_
  obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = dW.pX ⬝ u' := ⟨_, rfl⟩
  have hξ : MxAt (· = v) ξ := hξdef ▸ GlobalTheory.FinPl.LastDiag.mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu')
  have hu : dV.ext0 W (dW.incX V₀ ξ) ∈ latO V W (LV : Set _) (LW : Set _) (· = v) :=
    hξdef ▸ GlobalTheory.FinPl.LastDiag.wittExtZero_inclusionX_mem_homLatticeCompletion dV dW hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hu'
  have hB : ξ ∈ p.B₁ := (hS.b ξ hξ).2 hu
  have hact : mt W (dW.levi t) ⬝ dW.incX V₀ ξ = dW.incX V₀ (t.1 ⬝ ξ) := by
    rw [HypDec.incX_apply, HypDec.incX_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, HypDec.levi_jX]
  have hχ := hiso ξ hB (t.1 ⬝ ξ) hξ hact
  rw [GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj, ← Matrix.mul_assoc,
    GlobalTheory.FinPl.LastDiag.yZero_mul_diag _ _ t.1 ht i hi, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj] at hχ
  rw [GlobalTheory.FinPl.LastDiag.symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, sub_mul, one_mul,
    map_sub, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, hχ, ← AddChar.map_add_eq_mul]
  rw [add_neg_cancel, AddChar.map_zero_eq_one]

end GlobalTheory.AscFin.IsoDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicDualMiddlePartsSymplecticOrthogonal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistFormsOrth

local infixl:70 " ⬝ " => HMul.hMul

variable {D : D7}

theorem hO_mul_rat_eq_zero (V W : HSp D) {r s : ℕ} (a : Mx D W.rank r) (b : Mx D W.rank s)
    (R : Matrix (Fin r) (Fin V.rank) D.host.E) (Q : Matrix (Fin s) (Fin V.rank) D.host.E)
    (h : R * V.gram⁻¹ * Qᴴ = 0) :
    hO V W (a ⬝ GlobalTheory.MixModel.rat R) (b ⬝ GlobalTheory.MixModel.rat Q) = 0 := by
  rw [GlobalTheory.MixModel.hO_eq_trace, GlobalTheory.MixModel.adj_mul, ← GlobalTheory.MixModel.rat_conjTranspose]
  have hz : GlobalTheory.MixModel.rat R * (GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Qᴴ) = 0 := by
    rw [GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, ← Matrix.mul_assoc, h,
      GlobalTheory.MixModel.rat_zero]
  have e : GlobalTheory.MixModel.giA V * (GlobalTheory.MixModel.rat Qᴴ * GlobalTheory.MixModel.adj b * (GlobalTheory.MixModel.gA W * (a * GlobalTheory.MixModel.rat R)))
      = GlobalTheory.MixModel.giA V * GlobalTheory.MixModel.rat Qᴴ * (GlobalTheory.MixModel.adj b * (GlobalTheory.MixModel.gA W * a)) * GlobalTheory.MixModel.rat R := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.trace_zero]

theorem symplO_mul_rat_eq_zero (V W : HSp D) {r s : ℕ} (a : Mx D W.rank r) (b : Mx D W.rank s)
    (R : Matrix (Fin r) (Fin V.rank) D.host.E) (Q : Matrix (Fin s) (Fin V.rank) D.host.E)
    (h : R * V.gram⁻¹ * Qᴴ = 0) :
    symplO V W (a ⬝ GlobalTheory.MixModel.rat R) (b ⬝ GlobalTheory.MixModel.rat Q) = 0 := by
  rw [GlobalTheory.MixModel.symplO_eq, hO_mul_rat_eq_zero V W a b R Q h, mul_zero, map_zero]

theorem frame_pair (V : HSp D) {r s : ℕ} (C₁ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (C₂ : Matrix (Fin V.rank) (Fin s) D.host.E) :
    adj D C₁ * V.gram * V.gram⁻¹ * (adj D C₂ * V.gram)ᴴ = adj D C₁ * V.gram * C₂ := by
  have hG := GlobalTheory.MixModel.gram_isUnit_det V
  simp only [adj, GlobalTheory.MixModel.cT_sig, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    GlobalTheory.MixModel.gram_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hG]

theorem frame_mid (V V' : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (h : adj D C * V.gram * B = 0) :
    adj D C * V.gram * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
  have hG := GlobalTheory.MixModel.gram_isUnit_det V
  simp only [adj, GlobalTheory.MixModel.cT_sig] at h ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    GlobalTheory.MixModel.gramInv_conjTranspose]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hG]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.zero_mul]

theorem orthogonal : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → (∀ a b, symplO V W (isoPart V W C a) (isoPart V W C b) = 0) ∧ (∀ a x, symplO V W (isoPart V W C a) (midPart V V' W B x) = 0) ∧ (∀ a x, symplO V W (isoPart V W C' a) (midPart V V' W B x) = 0) ∧ (∀ a b, symplO V W (isoPart V W C' a) (isoPart V W C' b) = 0) := by
  intro D V V' W r C B hs C' _ hC' hC'B
  have hC : adj D C * V.gram * C = 0 := hs.frame.2.2
  refine ⟨fun a b => ?_, fun a x => ?_, fun a x => ?_, fun a b => ?_⟩
  · exact symplO_mul_rat_eq_zero V W a b (adj D C * V.gram) (adj D C * V.gram) ((frame_pair V C C).trans hC)
  · exact symplO_mul_rat_eq_zero V W a x (adj D C * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (frame_mid V V' C B hs.orth)
  · exact symplO_mul_rat_eq_zero V W a x (adj D C' * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (frame_mid V V' C' B hC'B)
  · exact symplO_mul_rat_eq_zero V W a b (adj D C' * V.gram) (adj D C' * V.gram) ((frame_pair V C' C').trans hC')

end GlobalTheory.TwistFormsOrth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicStabilizerSplitPlaceInConjParabolicsStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicStabilizer_splitPlace_inConjParabolics : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v)
    (W : Submodule D.host.E V.V), GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V W →
    InConjParabolic ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) W).map
        (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) (Module.finrank D.host.E W) ∧
      InConjParabolic ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v) W).map
        (s.equiv : GLoc D.sp.cm.sig V.gram v →* GL (Fin V.rank) (Fv D.host.F v))) (V.rank - Module.finrank D.host.E W) := by
  first | exact @GlobalTheory.SplitStab.splitStab | exact GlobalTheory.SplitStab.splitStab | (intros; apply GlobalTheory.SplitStab.splitStab <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftScalarPosAllPlacesOfConjugateIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftScalar_pos_allPlaces_of_conjugateIdentity : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → (R.toCx3 F).GalD F.cr false → R.toRealDat.LUnif → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → R.PGEquiv F → R.PPos := by
  first | exact @GlobalTheory.PosScalRed.posScal_of_galD | exact GlobalTheory.PosScalRed.posScal_of_galD | (intros; apply GlobalTheory.PosScalRed.posScal_of_galD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixCoefficientDerivativeFormulaStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_derivative_formula : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → ∀ u : H, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ u → ∀ (w : H) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ g, Formalism.REAL.inUJ ε g → f g = ⟪w, ρ g u⟫_ℂ) → ∀ (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g → Formalism.REAL.Eab ε a b f g = ⟪w, ρ g (PI.DSInfCharCap.dsigC ε ρ (Matrix.single a b 1) u)⟫_ℂ := by
  first | exact @GlobalTheory.MatCoefDeriv.Eab_coef | exact GlobalTheory.MatCoefDeriv.Eab_coef | (intros; apply GlobalTheory.MatCoefDeriv.Eab_coef <;> assumption)
end

