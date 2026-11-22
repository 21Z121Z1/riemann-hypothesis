import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqZeroOfReal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0069
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0313
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1495
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistFactorCompare

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

theorem eq_one_of_chrEq_one {D : D7} {χ : (AE D)ˣ →* Circle} (h : ChrEq χ 1) (x : (AE D)ˣ) : χ x = 1 := by
  refine HeckeFinTrivial.eq_one_of_trivial_on_finite D χ h.1 (fun y hy => ?_) x
  obtain ⟨j, h1, h2, h3⟩ := HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := CharLocProd.char_eq_prod_locK D j h1 h2 (PlaceIdem.exists_isPlIdem D j h1 h2 h3) χ 1 h
  obtain ⟨S, k, hS, hS'⟩ := finiteIdele_exists_local_approx D.host.E N hN
    (Units.map ((j : _ →+* _).comp (finPart D)).toMonoidHom y)
  exact Subtype.ext ((hprod y hy S k (fun P hP => ⟨(hS P hP).1, (hS P hP).2.1⟩) hS').trans
    (Finset.prod_eq_one fun P _ => rfl))

section Row

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

theorem weilTwist_iff :
    WeilTwistColumns.WeilTwist R i ↔ (R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ t, FrameConstantVectors.WeilTwist R i t) := Iff.rfl

def ConstRel (cx : T0 → GA D (Wc D i) → ℂ) : Prop :=
  ∀ t : T0, ∃ ζ : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ FrameConstantVectors.ConstTwist R i t (D.what₂.embLL ζ) (cx t)

def FrameRel (cx : T0 → GA D (Wc D i) → ℂ) : Prop :=
  ∀ t : T0, ∃ ζ : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ ∀ h,
    cx A.μ0 h • FrameConstantVectors.frameVec (R.ωP i t) (R.vacP i) h =
      (D.what₂.embLL ζ * cx t h) • FrameConstantVectors.frameVec (R.ωP i A.μ0) (R.vacP i) h

def BaseIn {X : Type} (f : X → ℂ) : Prop :=
  ∃ ζ : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ ∀ h, f h = D.what₂.embLL ζ

theorem root_mul_inv {K : Type} [Field K] {a b : K} (ha : ∃ m : ℕ, 0 < m ∧ a ^ m = 1) (hb : ∃ m : ℕ, 0 < m ∧ b ^ m = 1) :
    b ≠ 0 ∧ ∃ m : ℕ, 0 < m ∧ (a * b⁻¹) ^ m = 1 := by
  obtain ⟨m, hm, ha⟩ := ha
  obtain ⟨n, hn, hb⟩ := hb
  refine ⟨fun h => by simp [h, hn.ne'] at hb, m * n, mul_pos hm hn, ?_⟩
  rw [mul_pow, pow_mul, ha, one_pow, inv_pow, mul_comm m, pow_mul, hb, one_pow, inv_one, one_mul]

variable {R i}

theorem vac_theta (hv : R.thP_vP) (i : Fin D.R.m) :
    IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) ∧ R.vacP i ≠ 0 := by
  obtain ⟨-, h⟩ := (hv i A.μ0).1
  refine ⟨h.theta, fun h0 => ?_⟩
  obtain ⟨p, hp⟩ := h.norm.1
  have := h.norm.2 p hp
  simp [nrm2, h0] at this

theorem constTwist_iff (hv : R.thP_vP) (t : T0) (z : ℂ) (f : GA D (Wc D i) → ℂ) :
    FrameConstantVectors.ConstTwist R i t z f ↔ ∀ h, FrameConstantVectors.frameVec (R.ωP i t) (R.vacP i) h =
      (z * f h) • FrameConstantVectors.frameVec (R.ωP i A.μ0) (R.vacP i) h :=
  forall_congr' fun h => FrameConstantVectors.const_iff_frame _ _ (vac_theta hv i).2 h z (f h)

theorem base_eq_one (hv : R.thP_vP) {z : ℂ} {f : GA D (Wc D i) → ℂ} (H : FrameConstantVectors.ConstTwist R i A.μ0 z f)
    (h : GA D (Wc D i)) : z * f h = 1 :=
  smul_left_injective ℂ (FrameConstantVectors.frameVec_ne_zero _ (vac_theta hv i).2 h)
    (((constTwist_iff hv _ z f).1 H h).symm.trans (one_smul ℂ _).symm)

theorem constRel_iff (hv : R.thP_vP) (cx : T0 → GA D (Wc D i) → ℂ) :
    ConstRel R i cx ↔ FrameRel R i cx ∧ BaseIn (D := D) (cx A.μ0) := by
  have one : ∃ m : ℕ, 0 < m ∧ (1 : D.what₂.LL) ^ m = 1 := ⟨1, one_pos, one_pow _⟩
  constructor
  · intro H
    obtain ⟨z, hz, Hz⟩ := H A.μ0
    have hz0 : D.what₂.embLL z ≠ 0 := (map_ne_zero _).2 (root_mul_inv one hz).1
    have hb : ∀ h, cx A.μ0 h = (D.what₂.embLL z)⁻¹ := fun h => eq_inv_of_mul_eq_one_right (base_eq_one hv Hz h)
    refine ⟨fun t => ?_, 1 * z⁻¹, (root_mul_inv one hz).2, fun h => by rw [hb, one_mul, map_inv₀]⟩
    obtain ⟨ζ, hζ, Hζ⟩ := H t
    refine ⟨ζ * z⁻¹, (root_mul_inv hζ hz).2, fun h => ?_⟩
    rw [(constTwist_iff hv _ _ _).1 Hζ h, smul_smul, hb, map_mul, map_inv₀]
    congr 1
    ring
  · rintro ⟨H, z, hz, hb⟩ t
    obtain ⟨ζ, hζ, Hζ⟩ := H t
    have hz0 : D.what₂.embLL z ≠ 0 := (map_ne_zero _).2 (root_mul_inv one hz).1
    refine ⟨ζ * z⁻¹, (root_mul_inv hζ hz).2, (constTwist_iff hv _ _ _).2 fun h => ?_⟩
    rw [← inv_smul_smul₀ hz0 (FrameConstantVectors.frameVec (R.ωP i t) (R.vacP i) h), ← hb h, Hζ h, smul_smul, hb, map_mul, map_inv₀]
    congr 1
    ring

theorem frameRel_of_free (hv : R.thP_vP) {cx : T0 → GA D (Wc D i) → ℂ} {κ : ℂ}
    (H : ∀ t, FrameConstantVectors.ConstTwist R i t κ (cx t)) : FrameRel R i cx := fun t =>
  ⟨1, ⟨1, one_pos, one_pow _⟩, fun h => by
    rw [(constTwist_iff hv _ _ _).1 (H t) h, smul_smul, ← mul_assoc, mul_comm (cx A.μ0 h), base_eq_one hv (H A.μ0) h,
      map_one]⟩

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {σ : c.F →+* ℂ}
  {U : Unf Xo c σ D.R.r} {dict : GA D (Wc D i) → Σ k, Frame (U.X k).Ψ D.R.r}
  {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)} {g : ℕ}
  {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
  {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
  {dδ : T0 → DeltaDat Xo c (Vc D i).rank}
  {U₂ : ∀ t, Unf (dδ t).Xo₂ (dδ t).c₂ (σ.comp ((dδ t).eF.symm : (dδ t).c₂.F →+* c.F)) D.R.r}
  {dict₂ : ∀ t, GA D (Wc D i) → Σ k, Frame ((U₂ t).X k).Ψ D.R.r}
  {xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ}

theorem cXi_eq (t : T0) :
    WeilTwistColumns.cXi (dδ t) (U₂ t) (dict₂ t) = FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t) := rfl

theorem ties_iff {Fc : Face D A} (hR : R.Char Fc) :
    WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi ↔
      (VStd D i ∧ (∀ k, ModelW (Wc D i) (rank_Wc i) (U.X k)) ∧
        (∀ k (τ : D.host.E →+* ℂ), τ ∈ (U.X k).Ψ ↔ ∃ ρ, τ = tauE D ρ) ∧
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) x₀ ∧
        DictLat U (Wc D i) (rank_Wc i) dict ι e F ik φ th x₀) ∧
      CovPin Xo c dδ ∧ LatEmb (Wc D i) ι ∧ (∀ t, XiIs R i t (xi t)) ∧
        CXiVal (Wc D i) (rank_Wc i) σ dδ U₂ dict₂ ι x₀ xi :=
  ⟨fun ⟨_, _, _, a, b, c, d, e, f, g, h, k, m⟩ => ⟨⟨a, b, c, d, e, g⟩, h, f, k, m⟩,
    fun ⟨⟨a, b, c, d, e, g⟩, h, f, k, m⟩ => ⟨hR.lev, hR.thP.ωP, hR.thP.vP, a, b, c, d, e, f, g, h, k, m⟩⟩

theorem frame_iff_constOf (hT : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi) {t t' : T0}
    {cst cst' : GA D (Wc D i) → ℂ} (hc : WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t cst)
    (hc' : WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t' cst') (h : GA D (Wc D i)) (a b : ℂ) :
    a • FrameConstantVectors.frameVec (R.ωP i t') (R.vacP i) h = b • FrameConstantVectors.frameVec (R.ωP i t) (R.vacP i) h ↔
      a * cst' h = b * cst h := by
  obtain ⟨-, hω, hv, -, -, hΨ, hth, -⟩ := hT
  exact frame_iff_const (fun k => ⟨_, (hΨ k _).2 ⟨D.eTau.symm 1, rfl⟩⟩) hth (hω i t) (hω i t')
    (vac_theta hv i).1 (vac_theta hv i).2 hc hc' h a b

theorem cXi_ne_zero (hC : CXiVal (Wc D i) (rank_Wc i) σ dδ U₂ dict₂ ι x₀ xi) (t : T0) (h : GA D (Wc D i)) :
    WeilTwistColumns.cXi (dδ t) (U₂ t) (dict₂ t) h ≠ 0 := by
  obtain ⟨c0, hc, H⟩ := cXi_value hC
  obtain ⟨γ, -, e⟩ := H t h
  rw [e]
  exact mul_ne_zero (root_mul_inv hc hc).1 (Units.ne_zero _)

theorem twistFactorAt_of_frameRel
    (H : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi →
      FrameRel R i fun t => WeilTwistColumns.cXi (dδ t) (U₂ t) (dict₂ t)) :
    WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi := by
  intro hT c0 cb h0 hb t ct ht
  obtain ⟨ζ, hζ, Hζ⟩ := H hT t
  refine ⟨ζ, hζ, fun h => mul_left_cancel₀ (cXi_ne_zero hT.2.2.2.2.2.2.2.2.2.2.2.2 A.μ0 h) ?_⟩
  rw [(frame_iff_constOf hT h0 ht h _ _).1 (Hζ h), hb]
  ring

theorem frameRel_of_twistFactorAt (hT : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi)
    (hex : ∀ t, ∃ ct, WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t ct)
    (H : WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi) :
    FrameRel R i fun t => WeilTwistColumns.cXi (dδ t) (U₂ t) (dict₂ t) := by
  intro t
  obtain ⟨c0, h0⟩ := hex A.μ0
  obtain ⟨ct, ht⟩ := hex t
  have hne := cXi_ne_zero hT.2.2.2.2.2.2.2.2.2.2.2.2 A.μ0
  obtain ⟨ζ, hζ, Hζ⟩ := H hT c0 (fun h => c0 h / WeilTwistColumns.cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h) h0
    (fun h => (div_mul_cancel₀ _ (hne h)).symm) t ct ht
  refine ⟨ζ, hζ, fun h => (frame_iff_constOf hT h0 ht h _ _).2 ?_⟩
  have := hne h
  rw [Hζ h]
  field_simp

theorem baseIn_iff (hL : R.toLevCh.Is A.μ0) (hX : XiIs R i A.μ0 (xi A.μ0))
    (hC : CXiVal (Wc D i) (rank_Wc i) σ dδ U₂ dict₂ ι x₀ xi) :
    BaseIn (D := D) (WeilTwistColumns.cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0)) ↔
      ∀ h, ∃ a : D.what₂.LL, WeilTwistColumns.cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h = D.what₂.embLL a := by
  refine ⟨fun ⟨z, _, hz⟩ h => ⟨z, hz h⟩, fun hv => ?_⟩
  obtain ⟨c0, ⟨m, hm, hc⟩, H⟩ := cXi_value hC
  have hb : ∀ h, WeilTwistColumns.cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h = c0 := fun h => by
    obtain ⟨γ, -, e⟩ := H A.μ0 h
    obtain ⟨x, hx⟩ := RecDict.exists_isDetRoot D (Wc D i) (γ * h)
    rw [e, hX _ x hx, eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x, Circle.coe_one, mul_one]
  obtain ⟨a, ha⟩ := hv 1
  rw [hb] at ha
  exact ⟨a, ⟨m, hm, D.what₂.embLL.injective (by rw [map_pow, ← ha, hc, map_one])⟩, fun h => (hb h).trans ha⟩

theorem constRel_iff_twistFactorAt (hT : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi)
    (hex : ∀ t, ∃ ct, WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t ct) :
    ConstRel R i (fun t => FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t)) ↔
      WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi ∧
        ∀ h, ∃ a : D.what₂.LL, FrameConstantVectors.cXi (Wc D i) σ (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h = D.what₂.embLL a :=
  (constRel_iff hT.2.2.1 _).trans (and_congr
    ⟨fun h => twistFactorAt_of_frameRel fun _ => h, frameRel_of_twistFactorAt hT hex⟩
    (baseIn_iff hT.1 (hT.2.2.2.2.2.2.2.2.2.2.2.1 A.μ0) hT.2.2.2.2.2.2.2.2.2.2.2.2))

theorem constRel_iff_norm (hT : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi)
    (hex : ∀ t, ∃ ct, WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t ct)
    (h1 : ∀ h, WeilTwistColumns.cXi (dδ A.μ0) (U₂ A.μ0) (dict₂ A.μ0) h = 1) :
    (ConstRel R i (fun t => FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t)) ↔
      WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi) ∧
    (WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi ↔
      WeilTwistColumns.TwistFactorNormAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi) :=
  ⟨(constRel_iff_twistFactorAt hT hex).trans (and_iff_left fun h => ⟨1, (h1 h).trans (map_one _).symm⟩),
    fun H => H.norm, fun H _ c0 cb h0 hb t ct ht => by
      obtain rfl : c0 = cb := funext fun h => by rw [hb, h1, mul_one]
      exact H hT h1 c0 h0 t ct ht⟩

theorem twistFactorAt_of_closed (H : FrameConstantVectors.TwistFactor) {Fc : Face D A} (hR : R.Char Fc) (jL : D.what₂.LL →+* c.F)
    (hj : σ.comp jL = D.what₂.embLL) (hI : LatIsom (Wc D i) Dw.EF ι)
    (hv : ∀ t h, ∃ a : D.what₂.LL, FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t) h = D.what₂.embLL a) :
    WeilTwistColumns.TwistFactorAt R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi :=
  twistFactorAt_of_frameRel fun ⟨_, _, hvP, _, _, _, _, _, a, _, b, d, f⟩ => ((constRel_iff hvP _).1
    (H D G Pl0 T0 A Ks R Fc i _ Dw l Xo c σ jL _ (rank_Wc i) dδ U₂ dict₂ ι x₀ xi hR hj b a hI d f hv)).1

theorem twistFactor_of_free (H : FrameConstantVectors.TwistFactorFree) {Fc : Face D A} (hR : R.Char Fc) : WeilTwistColumns.TwistFactor R :=
  fun i H' Dw l Xo c σ _ _ ι _ _ _ _ _ _ x₀ dδ U₂ dict₂ xi =>
    twistFactorAt_of_frameRel fun ⟨_, _, hvP, _, _, _, _, _, _, _, _, d, f⟩ =>
      frameRel_of_free hvP
        (H D G Pl0 T0 A Ks R Fc i H' Dw l Xo c σ _ (rank_Wc i) dδ U₂ dict₂ ι x₀ xi hR d f).choose_spec.2

theorem constRel_of_twistFactor (H : WeilTwistColumns.TwistFactor R)
    (hT : WeilTwistColumns.Ties R i U dict ι e F ik φ th x₀ dδ U₂ dict₂ xi)
    (hex : ∀ t, ∃ ct, WeilTwistColumns.IsConstOf R i U dict ι e F ik φ th x₀ t ct)
    (hv : ∀ t h, ∃ a : D.what₂.LL, FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t) h = D.what₂.embLL a) :
    ConstRel R i fun t => FrameConstantVectors.cXi (Wc D i) σ (dδ t) (U₂ t) (dict₂ t) :=
  (constRel_iff_twistFactorAt hT hex).2 ⟨H i _ Dw l Xo c σ U dict ι g e F ik φ th x₀ dδ U₂ dict₂ xi, hv A.μ0⟩

end Row

end GlobalTheory.TwistFactorCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveModelRationalDegree
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RatFibreClosure

theorem isPullback_spec_ringOfIntegers (F : Type) [Field F] [NumberField F] :
    IsPullback (spMap (algebraMap (𝓞 F) F)) (spMap (algebraMap ℚ F))
      (spMap (Int.castRingHom (𝓞 F))) (spMap (Int.castRingHom ℚ)) := by
  have h : Algebra.IsPushout ℤ (𝓞 F) ℚ F :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors ℤ) ℚ).1 inferInstance
  have h' := (CommRingCat.isPushout_iff_isPushout (R := ℤ) (R' := 𝓞 F) (S := ℚ) (S' := F)).2 h
  exact isPullback_SpecMap_of_isPushout _ _ _ _ h'

theorem ratDeg_eq_finrank_mul_interNumRed : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (P : TrueGeo.Model Y) (Z : Closeds Y.X), IsCompleteCurve F Z → ∀ (W : Scheme.{0}) (w : W ⟶ P.X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsArithVar (w ≫ P.p) 1 → z ≫ w = redι Z ≫ P.j → IsPullback z (redι Z ≫ Y.str) (w ≫ P.p) (spMap (algebraMap (𝓞 F) F)) → ∀ M : LB P.X, M.IsLB → ratDeg (w ≫ P.p) (M.pull w) = (Module.finrank ℚ F : ℤ) * interNumRed F Z ![M.pull P.j] := by
  intro F _ _ Y P Z hZ W w z hW hzw H M hM
  letI iF : Algebra F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := algebraΓOfHom (redι Z ≫ Y.str)
  letI iQ : Algebra ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := ((algebraMap F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤)).comp (algebraMap ℚ F)).toAlgebra
  haveI : IsScalarTower ℚ F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) := .of_algebraMap_eq fun _ ↦ rfl
  have hi : ∀ r : F, (redι Z).appTop (algebraMap F Γ(Y.X, ⊤) r) = algebraMap F Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r :=
    fun _ ↦ rfl
  haveI : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := isIntegral_red hZ.isIrreducible
  have hC : VB.IsProjCurve F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
    refine ⟨inferInstance, (topologicalKrullDim_red Z).trans hZ.dim_eq, ?_⟩
    rw [strHom_eq (f := redι Z ≫ Y.str) fun _ ↦ rfl]
    obtain ⟨n, f, hf, hs⟩ := Y.isProjOver
    exact ⟨n, redι Z ≫ f, inferInstance, by rw [Category.assoc, hs]⟩

  have H' := H.paste_vert (isPullback_spec_ringOfIntegers F)
  set R := ratFibre (w ≫ P.p)
  set e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ R := H'.isoIsPullback _ _ (ratFibre.isPullback (w ≫ P.p)) with he
  have efst : e.hom ≫ ratFibre.fst (w ≫ P.p) = z := IsPullback.isoIsPullback_hom_fst _ _ H' (ratFibre.isPullback _)
  have hf : ∀ r : ℚ, e.hom.appTop (algebraMap ℚ Γ(R, ⊤) r) = algebraMap ℚ Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r ↦
    RingHom.congr_fun (RingHom.ext_rat (e.hom.appTop.hom.comp (algebraMap ℚ _)) (algebraMap ℚ _)) r

  set L := (M.pull w).pull (ratFibre.fst (w ≫ P.p)) with hLdef
  set N := (M.pull P.j).pull (redι Z) with hNdef
  have hL : L.IsLB := Semi.LB.isLB_pull (Semi.LB.isLB_pull hM _) _
  have hN : N.IsLB := Semi.LB.isLB_pull (Semi.LB.isLB_pull hM _) _
  have hLe : (L.pull e.hom).IsLB := Semi.LB.isLB_pull hL _
  have hcls : cls (L.pull e.hom) hLe = cls N hN := by
    rw [cls_pull hL, cls_pull (Semi.LB.isLB_pull hM _), cls_pull hM, cls_pull (Semi.LB.isLB_pull hM _),
      cls_pull hM]
    simp only [← pull_comp, ← Category.assoc, efst, hzw]

  have h₁ : chi ℚ (structureModule R) = chi ℚ (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) :=
    (chi_congr ℚ (asIso (unitToPush e.hom))).trans (chi_pushforward_of_isClosedImmersion hf _)
  have h₂ : chi ℚ (toMod L) = chi ℚ (twist (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) N) := by
    refine (chi_congr ℚ (Twist.unitTwistIso L)).symm.trans ?_
    refine (chi_congr ℚ ((twistFunctor L).mapIso (asIso (unitToPush e.hom)))).trans ?_
    refine (chi_twist_pushforward_of_isClosedImmersion hf _ L).trans ?_
    exact (nonempty_twist_iso_of_cls_eq _ hLe hN hcls).elim (chi_congr ℚ)

  have h₃ : interNumRed F Z ![M.pull P.j] = chi F (twist (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) N) - chi F (structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    have e₁ := interNumOn_eq_interNum_pull (k := F) (L := ![M.pull P.j]) hi
      (fun i ↦ by fin_cases i; exact Semi.LB.isLB_pull hM _)
    have e₂ := hC.degLB_eq_interNum hN
    rw [VB.degLB_eq hN, ← chi_congr F (Twist.unitTwistIso N)] at e₂
    rw [interNumRed_def, interNumSub_def]
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    congr 1
    funext i
    fin_cases i
    rfl
  rw [ratDeg, degOfRank, h₁, h₂, h₃, GroundFieldChange.chi_fieldChange ℚ F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme,
    GroundFieldChange.chi_fieldChange ℚ F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme]
  push_cast
  ring

end GlobalTheory.RatFibreClosure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationsCommuteDistinctPlaces
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.LeviHC.PlaceComm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {w w' : InfinitePlace F} {τ : EmbOver E w} {τ' : EmbOver E w'} {Z Z' : Matrix (Fin n) (Fin n) ℂ}
  {γ δ : ℝ → GAd σ J}

theorem line_commute (hw : w ≠ w') (hγ : IsLineOf σ J τ Z γ) (hδ : IsLineOf σ J τ' Z' δ) (s t : ℝ) :
    γ s * δ t = δ t * γ s := by
  obtain ⟨y, e, -⟩ := hγ s
  obtain ⟨y', e', -⟩ := hδ t
  rw [e, e']
  exact (commute_embArch σ J y (projArch_embArch_ne σ J hw y')).eq

theorem lineDer_comm (h : IsCMExt F E σ) (hw : w ≠ w') (hγ : IsLineOf σ J τ Z γ) (hδ : IsLineOf σ J τ' Z' δ)
    {φ : GAd σ J → ℂ} (hφ : IsSm σ J φ) :
    GlobalTheory.SiegelSet.lineDer γ (GlobalTheory.SiegelSet.lineDer δ φ) = GlobalTheory.SiegelSet.lineDer δ (GlobalTheory.SiegelSet.lineDer γ φ) := by
  funext g
  have hu := GlobalTheory.UAut.CentralComm.isSmFamily_translate hφ (hγ.isRealLine h)
  have e := hu.deriv_lineDer (hδ.isRealLine h) g
  refine Eq.trans ?_ e
  simp only [GlobalTheory.SiegelSet.lineDer]
  congr 1; funext s; congr 1; funext t
  rw [mul_assoc, mul_assoc, line_commute hw hγ hδ]

theorem der_comm_lines (h : IsCMExt F E σ) (hw : w ≠ w')
    {D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)} (hD : IsDer σ J τ D)
    {D' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)} (hD' : IsDer σ J τ' D')
    (hγ : IsLineOf σ J τ Z γ) (hδ : IsLineOf σ J τ' Z' δ) : Commute (D Z) (D' Z') := by
  refine LinearMap.ext fun f => Subtype.ext ?_
  simp only [Module.End.mul_apply]
  rw [hD.2 Z γ hγ, hD'.2 Z' δ hδ, hD'.2 Z' δ hδ, hD.2 Z γ hγ]
  exact lineDer_comm h hw hγ hδ f.2

end GlobalTheory.LeviHC.PlaceComm

namespace GlobalTheory.LeviHC

theorem der_comm_of_ne : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (w : InfinitePlace F) (τ : EmbOver E w) (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)), IsDer σ J τ D →
    ∀ (w' : InfinitePlace F) (τ' : EmbOver E w') (D' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)),
    IsDer σ J τ' D' → w ≠ w' → ∀ X X', D X * D' X' = D' X' * D X := by
  intro F E _ _ _ _ _ σ h n J hJ w τ D hD w' τ' D' hD' hw X X'
  obtain ⟨γ₁, γ₂, e1, e2, hX⟩ := exists_lines h hJ τ X
  obtain ⟨δ₁, δ₂, f1, f2, hX'⟩ := exists_lines h hJ τ' X'
  have c : ∀ {Z Z' : Matrix (Fin n) (Fin n) ℂ} {γ δ : ℝ → GAd σ J}, IsLineOf σ J τ Z γ → IsLineOf σ J τ' Z' δ →
      Commute (D Z) (D' Z') := fun hγ hδ => PlaceComm.der_comm_lines h hw hD hD' hγ hδ
  have key : Commute (D X) (D' X') := by
    rw [hX, hX']
    rw [map_add, map_add, LinearMap.map_smul D Complex.I _, LinearMap.map_smul D' Complex.I _]
    exact ((c e1 f1).add_right ((c e1 f2).smul_right Complex.I)).add_left
      (((c e2 f1).add_right ((c e2 f2).smul_right Complex.I)).smul_left Complex.I)
  exact key.eq

end GlobalTheory.LeviHC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetOmegaEqConstMulDet
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifDet

theorem detOmega_eq_const_mul_det :
    ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetOmega), ∃ C : ℂ,
    ∀ (v : Fin (Module.finrank ℚ F) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ j, u.IsDiff (W j) (v j).hom) → δ v = C * W.det := by
  intro F _ _ 𝔠 X L u δ
  obtain ⟨-, h2⟩ := UnifTangent.tangent_bijection u X.dim

  have he : ∀ k : Fin (Module.finrank ℚ F), ∃ t : X.Lie, u.IsDiff (Pi.single k 1) t.hom := fun k => by
    obtain ⟨t, ⟨ht, hd⟩, -⟩ := h2 (Pi.single k 1)
    exact ⟨Serre.Lie.mk X.rm t ht, hd⟩
  choose e he using he
  let T : (Fin (Module.finrank ℚ F) → ℂ) →ₗ[ℂ] X.Lie := Fintype.linearCombination ℂ e
  have hT : ∀ w : Fin (Module.finrank ℚ F) → ℂ, u.IsDiff w (T w).hom := fun w => by
    have hc : IsLieComb w (fun k => (e k).hom) (T w).hom := by
      rw [Serre.Lie.isLieComb_iff]
      simp [T, Fintype.linearCombination_apply]
    have := UnifDifferential.isDiff_of_isLieComb X.A L _ _ u (fun k => Pi.single k 1) (fun k => (e k).hom) w
      (T w).hom (fun k => (e k).isTangent) he hc
    convert this using 1
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  refine ⟨δ.compLinearMap T (Pi.basisFun ℂ (Fin (Module.finrank ℚ F))), fun v W hW => ?_⟩
  have hv : v = fun j => T (W j) := funext fun j =>
    Serre.Lie.ext ((h2 (W j)).unique ⟨(v j).isTangent, hW j⟩ ⟨(T (W j)).isTangent, hT (W j)⟩)
  have key := DFunLike.congr_fun
    (AlternatingMap.eq_smul_basis_det (Pi.basisFun ℂ (Fin (Module.finrank ℚ F))) (δ.compLinearMap T)) W
  rw [hv]
  refine key.trans ?_
  rw [Pi.basisFun_det]
  rfl

end GlobalTheory.UnifDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaNsmul
section
noncomputable section

namespace GlobalTheory.UPel.HeckeImage

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

variable {F : Type} [Field F] [NumberField F] [IsCMField F] {S : Scheme.{0}}

theorem eta_zero {D : Datum F} {p N : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)

theorem eta_neg {D : Datum F} {p N : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (x : D.La) :
    o.eta (-x) = (o.eta x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← o.eta_add, add_neg_cancel, eta_zero]

theorem eta_nsmul {D : Datum F} {p N : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N s) (m : ℕ) (x : D.La) :
    o.eta (m • x) = o.eta x ^ m := by
  induction m with
  | zero => simp [eta_zero]
  | succ m ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

def sub {D : Datum F} {p N' : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s) (g : IntSim D p) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ a, h = o.eta ((N' / g.k) • g.g N' a)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add, smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, eta_neg]⟩

theorem mem_sub {D : Datum F} {p N' : ℕ} {s : S ⟶ Sp (D.OEp p)} (o : Obj D p N' s) (g : IntSim D p) (a : D.La) :
    o.eta ((N' / g.k) • g.g N' a) ∈ sub o g := ⟨a, rfl⟩

end GlobalTheory.UPel.HeckeImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFibreEmbeddingsCardStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_fibre_embeddings_card : ∀ (A B : Type) [CommRing A] [IsDomain A] [CommRing B] (f : A →+* B), f.Finite → f.Etale → ∀ φ : A →+* ℂ, {ψ : B →+* ℂ | ψ.comp f = φ}.encard = (letI := f.toAlgebra; Module.finrank A B : ℕ) := by
  first | exact @GlobalTheory.EtaleFibre.encard_points_eq_finrank | exact GlobalTheory.EtaleFibre.encard_points_eq_finrank | (intros; apply GlobalTheory.EtaleFibre.encard_points_eq_finrank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDimensionalSpaceAutomorphicSmoothingStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_space_automorphic_smoothings : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (φ : Sm E a), IsAutForm φ → ∃ V : Submodule ℂ (Sm E a), FiniteDimensional ℂ V ∧ V ≤ tame E a ∧ ∀ α, IsTest (invSet E a) α → KInv α → ∃ h : smoothing ν α φ.1 ∈ Sm E a, (⟨smoothing ν α φ.1, h⟩ : Sm E a) ∈ V := by
  first | exact @GlobalTheory.AutGrowth.SmoothFinite.exists_finite_space | exact GlobalTheory.AutGrowth.SmoothFinite.exists_finite_space | (intros; apply GlobalTheory.AutGrowth.SmoothFinite.exists_finite_space <;> assumption)
end

