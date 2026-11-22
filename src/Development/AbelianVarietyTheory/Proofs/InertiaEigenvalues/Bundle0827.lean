import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0813
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0820
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0811
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Formalism.LocalToGlobal.Columns.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKills
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0815
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0705
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFormSupLatticeFullGroupStableOfEqRational

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesTranslationLatticeBoundedNorm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LatCmpQ

theorem nsmul_mulVec_eq {R : Type*} [CommRing R] {n : ℕ} (N m : ℕ) (g w : Matrix (Fin n) (Fin n) R)
    (hwe : ∀ i j, (N : R) * (g i j - (1 : Matrix (Fin n) (Fin n) R) i j) = (m : R) * w i j) (y : Fin n → R) :
    N • (g *ᵥ y) = N • y + m • (w *ᵥ y) := by
  have e1 : (N : R) • (g - 1) = (m : R) • w := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    exact hwe i j
  have e2 : ((N : R) • (g - 1)) *ᵥ y = N • (g *ᵥ y) - N • y := by
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, smul_sub]
  have e3 : ((m : R) • w) *ᵥ y = m • (w *ᵥ y) := by
    rw [Matrix.smul_mulVec, Nat.cast_smul_eq_nsmul]
  rw [← e3, ← e1, e2]
  abel

set_option maxHeartbeats 1000000 in

theorem step {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (a N : ℕ)
    (h1 : ∀ x ∈ Formalism.L2.Pj.stdLat D.host.E n, (a : 𝓞 D.host.E) • x ∈ Λ) (h2 : ∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E n)
    (g : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hg : ∀ i j, ∃ w ∈ intAE D, ((N : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * (g i j - (1 : Matrix (Fin n) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) i j) =
        ((a ^ 2 : ℕ) : Af D.host.F ⊗[D.host.F] D.host.E) * w)
    {y : Fin n → Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E))) :
    N • (g *ᵥ y) ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  choose w hw hwe using hg
  have key := nsmul_mulVec_eq N (a ^ 2) g (Matrix.of w) hwe y
  rw [key]
  exact add_mem (AddSubgroup.nsmul_mem _ hy N) (GlobalTheory.HatIntSmul.sq_smul_mulVec_mem_hat D n Λ a h1 h2 _ hw y hy)

set_option maxHeartbeats 1000000 in

theorem latAt_translate_bounded : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)) (h hQ : GA D (Vc D j)), SplitSet Q → SuppAt (idem Q) (Vc D j) hQ → ∃ c : ℕ, (∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ))) ∧ ∀ x ∈ (ρ.B i j b).latAt (finPt (Vc D j) (h * hQ)), ((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x ∈ (ρ.B i j b).latAt (finPt (Vc D j) h) := by
  intro D ρ hρ i j b Q h hQ hS hsupp
  have hΛ : ∀ x, x ∈ (ρ.B i j b).F.ΛS ↔ x ∈ L0c D (Vc D j) := by
    obtain ⟨_, _, _, h1, h2⟩ := hρ.latS i j b
    intro x
    constructor
    · intro hx; simpa using h2 x hx
    · intro hx; simpa using h1 x hx
  obtain ⟨a, ha, hs1, hs2⟩ := GlobalTheory.LatSandwich.sandwich D (Vc D j) (ρ.B i j b).F.ΛS hΛ
  obtain ⟨c, hc⟩ := GlobalTheory.SuppIntCong.cong_one_of_suppAt D (Vc D j) Q hQ a ha hS hsupp
  have ev : ∀ x : Fin (Vc D j).rank → D.host.E, (fun k => (1 : Af D.host.F) ⊗ₜ[D.host.F] ((((normProd Q ^ c : ℕ) : 𝓞 D.host.E) • x) k)) =
      (normProd Q ^ c) • (fun k => (1 : Af D.host.F) ⊗ₜ[D.host.F] x k) := by
    intro x
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, Nat.cast_smul_eq_nsmul]
    exact map_nsmul ((TensorProduct.mk D.host.F (Af D.host.F) D.host.E) 1) _ _
  have hmul : ((finPt (Vc D j) (h * hQ)).1⁻¹).val = (finHom (Vc D j) hQ)⁻¹.val * ((finPt (Vc D j) h).1⁻¹).val := by
    have e : (finPt (Vc D j) (h * hQ)).1 = finHom (Vc D j) h * finHom (Vc D j) hQ := map_mul (finHom (Vc D j)) h hQ
    rw [e, _root_.mul_inv_rev, Units.val_mul]
    rfl
  have hmul' : ((finPt (Vc D j) h).1⁻¹).val = (finHom (Vc D j) hQ).val * ((finPt (Vc D j) (h * hQ)).1⁻¹).val := by
    rw [hmul, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  refine ⟨c, fun x hx => ?_, fun x hx => ?_⟩
  · rw [GlobalTheory.LatAtHLat.mem_latAt_iff_hat] at hx ⊢
    rw [ev x, Matrix.mulVec_smul, hmul, ← Matrix.mulVec_mulVec]
    exact step _ a _ hs1 hs2 _ (fun i j => (hc i j).2) hx
  · rw [GlobalTheory.LatAtHLat.mem_latAt_iff_hat] at hx ⊢
    have hst := step _ a _ hs1 hs2 _ (fun i j => (hc i j).1) hx
    rw [Matrix.mulVec_mulVec, ← hmul'] at hst
    rw [ev x, Matrix.mulVec_smul]
    exact hst

end GlobalTheory.LatCmpQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarMulSelfOfPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.CoefUniq

open GlobalTheory.CoefModel

theorem schur_scalar : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 c0' : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W), IsInfFam θ → c.Is →
    Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → Bridge.CoefMapTie V c.coef c0' (rhoVr (labLL D) lam) →
    ∃ ζ : ℂ, ∀ F, c0' F = ζ • c0 F := by
  intro D V θ c lam c0 c0' hθ hc ht ht'
  obtain ⟨E, hE, hEρ⟩ := GlobalTheory.CoefReal.exists_real_model V θ c lam c0 hθ hc ht
  obtain ⟨E', hE', hEρ'⟩ := GlobalTheory.CoefReal.exists_real_model V θ c lam c0' hθ hc ht'
  let ψ : Module.End ℂ c.W := E'.toLinearMap ∘ₗ E.symm.toLinearMap
  have hψ : ∀ u ∈ GinfC V, ∀ w, ψ (c.ρ u w) = c.ρ u (ψ w) := fun u hu w => by
    obtain ⟨v, rfl⟩ := E.surjective w
    change E' (E.symm (c.ρ u (E v))) = c.ρ u (E' (E.symm (E v)))
    rw [hEρ u hu, E.symm_apply_apply, E.symm_apply_apply, hEρ' u hu]
  haveI := hc.2.2.2.1
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue ψ
  have hU := GlobalTheory.GenRealSchur.irr_real c hc (Module.End.eigenspace ψ μ) fun u hu => by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : ψ w = μ • w := Module.End.mem_eigenspace_iff.1 hw
    exact Module.End.mem_eigenspace_iff.2 (by rw [hψ u hu, hw', map_smul])
  rcases hU with h0 | h0
  · exact absurd h0 hμ
  refine ⟨μ, fun F => ?_⟩
  have h1 : E (mapVV D.what₂.embLL lam F) ∈ Module.End.eigenspace ψ μ := h0 ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at h1
  rw [← hE, ← hE']
  exact (congrArg E' (E.symm_apply_apply _)).symm.trans h1

theorem scalar_of_basis : ∀ {K V W ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    [Fintype ι] [Nonempty ι] (σ : K →+* ℂ) (b : Module.Basis ι K V) (c : V →ₛₗ[σ] W),
    LinearIndependent ℂ (fun i => c (b i)) → ∀ (φ : V →ₗ[K] V) (ζ : ℂ), (∀ v, c (φ v) = ζ • c v) →
    ∃ a : K, σ a = ζ ∧ ∀ v, φ v = a • v := by
  intro K V W ι _ _ _ _ _ _ _ σ b c hli φ ζ hφ
  classical
  have key : ∀ i k, σ (b.repr (φ (b i)) k) = if k = i then ζ else 0 := by
    intro i
    have e1 : c (φ (b i)) = ∑ k, σ (b.repr (φ (b i)) k) • c (b k) := by
      conv_lhs => rw [← b.sum_repr (φ (b i))]
      rw [map_sum]
      simp only [LinearMap.map_smulₛₗ]
    have e2 : ∑ k, (if k = i then ζ else 0) • c (b k) = ζ • c (b i) := by
      simp [ite_smul]
    have h1 : ∑ k, (σ (b.repr (φ (b i)) k) - if k = i then ζ else 0) • c (b k) = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← e1, e2, hφ, sub_self]
    intro k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h1 k)
  obtain ⟨i0⟩ := ‹Nonempty ι›
  set a := b.repr (φ (b i0)) i0 with ha
  have hd : ∀ i, b.repr (φ (b i)) i = a := fun i => σ.injective (by rw [key, key, if_pos rfl, if_pos rfl])
  have ho : ∀ i k, k ≠ i → b.repr (φ (b i)) k = 0 := fun i k hk => σ.injective (by rw [key, if_neg hk, map_zero])
  have hb : ∀ i, φ (b i) = a • b i := by
    intro i
    refine b.repr.injective (Finsupp.ext fun k => ?_)
    rw [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, smul_eq_mul]
    by_cases hk : i = k
    · subst hk
      rw [if_pos rfl, mul_one, hd]
    · rw [if_neg hk, mul_zero, ho i k (Ne.symm hk)]
  have hφa : φ = a • LinearMap.id := b.ext fun i => by rw [hb i]; rfl
  refine ⟨a, (key i0 i0).trans (if_pos rfl), fun v => ?_⟩
  rw [hφa]
  rfl

theorem pow_eq_one_of_cmMax {K : Type} [Field K] [NumberField K] [StarRing K] {a : K} (hm : a ∈ Formalism.DivisionValues.cmMax K)
    (hs : star a * a = 1) (hi : IsIntegral ℤ a) : ∃ n : ℕ, n ≠ 0 ∧ a ^ n = 1 := by
  obtain ⟨n, hn, h⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hi (fun φ => by
    have h1 := congrArg φ hs
    rw [map_mul, map_one, show φ (star a) = starRingEnd ℂ (φ a) from hm φ, Complex.conj_mul'] at h1
    have h2 : ‖φ a‖ ^ 2 = 1 := by exact_mod_cast h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2)
  exact ⟨n, hn.ne', h⟩

theorem mem_of_coords {K V ι : Type} [Field K] [AddCommGroup V] [Module K V] (K0 : Subfield K) (b : Module.Basis ι K V)
    {y : V} (a : K) (hy : y ≠ 0) (h1 : ∀ k, b.repr (a • y) k ∈ K0) (h2 : ∀ k, b.repr y k ∈ K0) : a ∈ K0 := by
  obtain ⟨k, hk⟩ : ∃ k, b.repr y k ≠ 0 := by
    by_contra hc
    exact hy (b.repr.injective (Finsupp.ext fun k => by simpa using not_not.1 (fun h => hc ⟨k, h⟩)))
  have e1 : a = b.repr (a • y) k * (b.repr y k)⁻¹ := by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_inv_cancel_right₀ hk]
  rw [e1]
  exact K0.mul_mem (h1 k) (K0.inv_mem (h2 k))

theorem star_mul_self_of_pair {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (pair : V →ₗ⋆[K] V →ₗ[K] K) (a : K) {y : V} (hy : pair y y ≠ 0) (h : pair (a • y) (a • y) = pair y y) :
    star a * a = 1 := by
  have e1 : pair (a • y) (a • y) = star a * a * pair y y := by
    rw [map_smul, LinearMap.map_smulₛₗ₂, smul_eq_mul, smul_eq_mul, starRingEnd_apply]
    ring
  rw [e1] at h
  exact mul_right_cancel₀ hy (h.trans (one_mul _).symm)

theorem pair_ne_zero {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (σ : K →+* ℂ) (coef : V →ₛₗ[σ] W) (hinj : Function.Injective coef) (q : V → V → K)
    (hq : ∀ x x', inner ℂ (coef x) (coef x') = σ (q x x')) {x : V} (hx : x ≠ 0) : q x x ≠ 0 := fun h0 => by
  have h1 := hq x x
  rw [h0, map_zero] at h1
  exact hx (hinj ((inner_self_eq_zero.1 h1).trans (map_zero coef).symm))

theorem isIntegral_of_keeps {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (hne : L ≠ ⊥) (hfg : L.FG) (a : K) (h : ∀ n ∈ L, a • n ∈ L) :
    IsIntegral ℤ a := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 (isIntegral_of_smul_mem_submodule L hne hfg a h)
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

theorem exists_root_of_unity : ∀ (D : D7) (X : RealSide D) (c c₂ : ∀ j : Fin D.R.m, VV D.what₂.LL (FWT.lamV D j) →ₛₗ[D.what₂.embLL] (X.R.cV j).W), IsCoef X c → IsCoef X c₂ → ∀ j, ∃ (ζ : ℂ) (n : ℕ), n ≠ 0 ∧ ζ ^ n = 1 ∧ ∀ F, c₂ j F = ζ • c j F := by
  intro D X c c₂ hc hc₂ j
  obtain ⟨g, c0R, h⟩ := hc
  obtain ⟨g₂, c0R₂, h₂⟩ := hc₂
  obtain ⟨ζ, hζ⟩ := schur_scalar D (Vc D j) X.R.θ (X.R.cV j) (FWT.lamV D j) (c j) (c₂ j) X.char.models.inf
    (X.char.models.cV j) (h.mapL j) (h₂.mapL j)
  rcases subsingleton_or_nontrivial (VV D.what₂.LL (FWT.lamV D j)) with hs | hs
  · refine ⟨1, 1, one_ne_zero, one_pow _, fun F => ?_⟩
    rw [Subsingleton.elim F 0, map_zero, map_zero, smul_zero]
  obtain ⟨e, hrat, hco, hpa, hnab, -⟩ := h.coefL j X.A3.A.μ0
  obtain ⟨e₂, hrat₂, hco₂, hpa₂, hnab₂, -⟩ := h₂.coefL j X.A3.A.μ0

  have hφ : ∀ v, c j ((e₂.symm.trans e) v) = ζ • c j v := fun v =>
    (hco (e₂.symm v)).symm.trans ((hco₂ _).trans ((congrArg (c₂ j) (e₂.apply_symm_apply v)).trans (hζ v)))
  haveI : Nonempty _ := (bVV D.what₂.LL (FWT.lamV D j)).index_nonempty
  obtain ⟨a, hζa, ha⟩ := scalar_of_basis D.what₂.embLL (bVV D.what₂.LL (FWT.lamV D j)) (c j) (h.mapL j).2.1
    (e₂.symm.trans e).toLinearMap ζ hφ
  have hea : ∀ x, e x = a • e₂ x := fun x =>
    (congrArg e (e₂.symm_apply_apply x)).symm.trans (ha (e₂ x))
  haveI := e.toEquiv.nontrivial
  obtain ⟨i0⟩ := (X.A3.A.MtCSD j X.A3.A.μ0).bV.index_nonempty
  have hx0 := (X.A3.A.MtCSD j X.A3.A.μ0).bV.ne_zero i0
  have hy0 : e₂ ((X.A3.A.MtCSD j X.A3.A.μ0).bV i0) ≠ 0 := fun h0 => hx0 (e₂.injective (h0.trans (map_zero e₂).symm))
  have hm : a ∈ Formalism.DivisionValues.cmMax D.what₂.LL :=
    mem_of_coords _ (bVV D.what₂.LL (FWT.lamV D j)) a hy0 (fun k => hea _ ▸ hrat i0 k) (hrat₂ i0)
  have hs : star a * a = 1 := by
    have hinj := GlobalTheory.GalLift.rescale_inj _ D.what₂.embLL _ (X.R.B.L j X.A3.A.μ0).pres.coef_li
    have hp0 := pair_ne_zero D.what₂.embLL _ hinj _ (X.R.B.L j X.A3.A.μ0).pres.coef_pair hx0
    refine star_mul_self_of_pair _ a ((hpa₂ _ _).trans_ne hp0) ?_
    rw [← hea, hpa, hpa₂]
  have hi : IsIntegral ℤ a := by
    obtain ⟨cl, -⟩ := ((X.R.B.L j X.A3.A.μ0).pres.reps 1).exists
    have hL := nabAtr_isLattice (labLL D) (FWT.lamV D j) _
      (GlobalTheory.RepsCompare.isLattice_hLat (Vc D j) ((X.R.B.L j X.A3.A.μ0).pres.y cl))
    refine isIntegral_of_keeps _ (fun h0 => ?_) hL.fg a (fun n hn => ?_)
    · have h1 := hL.span_eq_top
      rw [h0, Submodule.bot_coe, Submodule.span_zero_singleton] at h1
      exact bot_ne_top h1
    · rw [← hnab₂ cl] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      rw [← hnab cl]
      exact ⟨m, hm, hea m⟩
  obtain ⟨n, hn, han⟩ := pow_eq_one_of_cmMax hm hs hi
  exact ⟨ζ, n, hn, by rw [← hζa, ← map_pow, han, map_one], hζ⟩

end GlobalTheory.CoefUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThFEqIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.LiftClassSum

theorem exists_low (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (j : Fin D.R.m) :
    ∃ u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ, (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) = X.geo.v₀ j (sg0 D X.A3.A) := by
  have h := (Y.Z.vec j).1
  exact ⟨fun ρ => ⟨X.geo.v₀ j _ ρ, (h ρ).2.1⟩, rfl⟩

open Classical in

theorem sum_eq_classSum_ωP (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (t : X.T) (hxi : X.R.xi t = (Y.Z.ρ.B i j b).de.chi) (hQ : X.R.Q t = (Y.Z.ρ.B i j b).de.Q) :
    Y.Z.ρ.sum i j b 0 ∅ 1 = (Y.Z.ρ.B i j b).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) := by
  have hB : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) :=
    GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hG : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have htup : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Twist.triv Circle ∅) t := by
    classical
    exact
      ⟨by rw [hxi]; exact (mul_one _).symm, by rw [hQ]; exact (Finset.union_empty _).symm⟩
  have h1 : IsWeilDatumO X.R.toRealDat.ψ (Vc D j) (Wc D j) (Lift.chrTh (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta ((j : ℕ) + 1)).1
      (Lift.chrTh (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta ((j : ℕ) + 1)).2 (Y.Z.ρ.om i j b 1) := by
    have := Y.Z.good.weil_base i j b
    rw [Base.IsWeil, show (1 : (AE D)ˣ →* Circle) = (Twist.triv Circle ∅ : Twist D Circle).chi from rfl,
      hB.mu_mul htup, hB.ψ, hB.eta] at this
    exact this
  have hu := (GlobalTheory.SplitChange.change_of_splitting D X.R.toRealDat.ψ (Vc D j) (Wc D j) (X.R.toRealDat.toLevCh.mu t) X.R.toRealDat.eta (Y.Z.ρ.B i j b).mu0
    ((j : ℕ) + 1) (X.R.ωP j t) (X.char.thP.ωP j t) hG.hecke hG.real).2.2 _ h1
  have key : ∀ τ : Twist D Circle, τ.Q = ∅ → τ.chi = 1 → ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      series (Y.Z.ρ.B i j b).F (Y.Z.ρ.om i j b τ.chi) ((Y.Z.ρ.B i j b).vecFlat τ) h P =
        series (Y.Z.ρ.B i j b).F (X.R.ωP j t) ((Y.Z.ρ.B i j b).vecFlat τ) h P := by
    rintro ⟨Q0, c0, r0⟩ hq hc h P
    dsimp only at hq hc
    subst hq hc
    funext g
    rw [series_apply, series_apply]
    have ht := Base.isThetaFunO_fock_vecAt hG (Base.admissible_empty_of_good hG) (fun _ _ => (1 : ℂ)) P
    rw [hB.ψ] at ht
    exact congrFun (hu (h, g) _ ht) 0
  apply LinearMap.ext
  intro F
  rw [Setup.sum, Base.classSum_apply, Base.classSum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [key _ (half_empty _) (charOf_one _ _)]

end GlobalTheory.LiftClassSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralOfIsSphericalLocProd
section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT GlobalTheory.UnitaryBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCSupport

variable {E : Type} [Field E] [NumberField E]

abbrev clsOf {w : HeightOneSpectrum (𝓞 E)} {a : ℕ} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    IrrGL (w.adicCompletion E) :=
  IrrGL.of σ.ρ σ.smooth σ.irred

theorem good_of_good_locProd {c n : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (hi : (locProd h w σ).IsIrreducible)
    (hG : Good (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi)) : ∀ i, Good (clsOf (σ i)) := by
  have hs : IsSubquotient (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi).rep
      (prodIrr (fun i => clsOf (σ i)) h) := by
    let e := prodIrrEquiv (k := w.adicCompletion E) h (fun i => (σ i).ρ) (fun i => (σ i).smooth) (fun i => (σ i).irred)
    let f := e.symm.trans (IrrGL.equivOf (locProd h w σ) (isSmooth_parInd _ _) hi)
    exact IsSubquotient.of_surjective f.toIntertwiningMap f.toLinearEquiv.surjective
  exact (GlobalTheory.RecT.good_toral_of_isSubquotient_prodIrr _ c (fun i => clsOf (σ i)) (IrrGL.of (locProd h w σ) (isSmooth_parInd _ _) hi) h hs).1 hG

theorem isSpherical_of_equiv {G X Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {τ : Representation ℂ G Y} (e : ρ.Equiv τ) {K : Subgroup G}
    (h : GlobalTheory.LGrp.IsSpherical ρ K) : GlobalTheory.LGrp.IsSpherical τ K := by
  obtain ⟨x, hx, h0⟩ := (Submodule.ne_bot_iff _).1 h
  refine (Submodule.ne_bot_iff _).2 ⟨e.toIntertwiningMap x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, ?_⟩
  · rw [← Representation.IntertwiningMap.isIntertwining ρ τ e.toIntertwiningMap k x, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
  · intro h1
    exact h0 (e.toLinearEquiv.injective (by simpa using h1))

theorem isSphericalFor_of_eq {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    {K K' : Subgroup G} (e : K = K') (h : GlobalTheory.SmGL.IsSphericalFor ρ K) : GlobalTheory.SmGL.IsSphericalFor ρ K' := e ▸ h

variable [IsCMField E]

end GlobalTheory.BCSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterEqGaloisOfLadicUnitaryHeckeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistCharacter_eq_galois_of_ladic_unitaryHecke : ∀ {D : D7} {N : NData D.R D.host D.what₂} {T : TwR D.LL0 N} {art : Ideles D.host.E →* Gab D.host.E N.Om}, IsGlobalArtin art → ∀ {i : T.Tw} (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ), (∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) → ∀ (b : Bool) (embO : ↥D.LL0 →+* FractionRing (T.O i)), (∀ (x : ↥D.LL0) (y : T.O0 i), algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = (if b then T.emb0 i else T.emb0b i) x → embO x = algebraMap (T.O i) (FractionRing (T.O i)) (algebraMap (T.O0 i) (T.O i) y)) → ∀ (χ : HChar D.host.E), χ.IsUnitary → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), (∀ P ∉ S, χ.UnrAt P ∧ ∃ y : ↥D.LL0, embLL0 D y = ((χ.val P : ℂˣ) : ℂ)) → ∀ (H : Formalism.L2.NC.HC D.host.E), (∀ x, H.χ x = χ.1 x) → ∀ {n : (D.host.E →+* ℂ) → ℤ} {r : G D.host.E N.Om →* (T.O0 i)ˣ}, IsGal art κ (sideIso ι b) χ n r → Formalism.L2.NC.Read N.plOm.1 ((Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) (algebraMap (T.O i) (FractionRing (T.O i))) embO (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D) H 0 := by
  first | exact @GlobalTheory.HeckeRead.read_of_isGal_side | exact GlobalTheory.HeckeRead.read_of_isGal_side | (intros; apply GlobalTheory.HeckeRead.read_of_isGal_side <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterIsLadicOfFiniteOrderHeckeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_character_is_ladic_of_finite_order_hecke : GlobalTheory.Published.ChebotarevDegreeOne → ∀ {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)} {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}, IsGlobalArtin art → ∀ (i : T.Tw) (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ), (∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) → IsGal art κ ι (cf.delAt (T.l i)) 0 (T.delta i) := by
  first | exact @GlobalTheory.DeltaGal.delta_isGal | exact GlobalTheory.DeltaGal.delta_isGal | (intros; apply GlobalTheory.DeltaGal.delta_isGal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFormSupLatticeFullGroupStableOfEqRationalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedFormSupLattice_full_groupStable_of_eq_rational : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS R cG S), (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b) → R.toRealDat.LIntegral → SupG D ∧ SupFull D := by
  first | exact @GlobalTheory.SupEq.supG_supFull_of_eq | exact GlobalTheory.SupEq.supG_supFull_of_eq | (intros; apply GlobalTheory.SupEq.supG_supFull_of_eq <;> assumption)
end

