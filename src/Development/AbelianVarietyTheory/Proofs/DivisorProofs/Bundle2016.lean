import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1359
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0531
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0378
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0324
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0514
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0366
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0396
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsSchwartz
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1994
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0530
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaOfIsWeilSch
section
noncomputable section

open scoped Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.FirstTermIsoCst
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory GlobalTheory.RegSch
open Filter Topology

namespace GlobalTheory.RegSch.JointCont

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model in

theorem levi_weyl_rel {R : Type} [CommRing R] {n : ℕ} {b c : Matrix (Fin n) (Fin n) R} (h1 : b * c = 1) (h2 : c * b = 1) :
    blk4 b 0 0 c * blk4 0 1 (-1) 0 = blk4 1 b 0 1 * blk4 0 1 (-1) 0 * blk4 1 c 0 1 *
      (blk4 0 1 (-1) 0 * blk4 0 1 (-1) 0 * blk4 0 1 (-1) 0) * blk4 1 b 0 1 := by
  simp [submatrix_fromBlocks_mul, h1, h2]

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model in

theorem resEta_of_isWeilSch {D : D7} {n : ℕ} (hn : 0 < n) {V : HSp D} {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ) {χ : (AE D)ˣ →* Circle}
    {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω) : ResEta D χ V.rank := by
  obtain ⟨χ₀, h1, h2, -⟩ := GlobalTheory.PlaceCompare.Spherical.exists_unram_char D V.rank
  obtain ⟨ψ₀, h₀, lam, hlam, hψeq⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hsh : ψ = shift ψ₀ lam := by
    ext x
    rw [hψeq]
    rfl
  obtain ⟨ω₀, hω₀⟩ := Inhab.weil_exists D n V ψ₀ h₀ lam hlam χ₀ h1 h2 θ hθ μ 𝓕 hμ
  rw [← hsh] at hω₀
  suffices h : ∀ t, χ (idF D t) = χ₀ (idF D t) from ⟨h2.1, fun η hη a => (h a).trans (h2.2 η hη a)⟩
  intro t
  let i₀ : Fin n := ⟨0, hn⟩
  let dg : (AF D.host.F)ˣ → Mx D n n := fun u => Matrix.diagonal (Function.update 1 i₀ (idF D u : AE D))
  have hmul : ∀ u u', dg u * dg u' = dg (u * u') := fun u u' => by
    simp only [dg, Matrix.diagonal_mul_diagonal, map_mul, Units.val_mul]
    congr 1
    funext i
    by_cases hi : i = i₀
    · subst hi; simp
    · simp [Function.update_of_ne hi]
  have hone : dg 1 = 1 := by simp [dg]
  have hadj : ∀ u, adj (dg u) = dg u := fun u => by
    ext i j
    simp only [adj, dg, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = i₀
      · subst hi
        simp only [if_true, Function.update_self]
        exact GlobalTheory.HermTransversal.cA_algebraMap _
      · simp [Function.update_of_ne hi]
    · simp [hij, Ne.symm hij]
  have e1 : dg t * dg t⁻¹ = 1 := by rw [hmul, mul_inv_cancel, hone]
  have e2 : dg t⁻¹ * dg t = 1 := by rw [hmul, inv_mul_cancel, hone]
  let a : GL (Fin n) (AE D) := ⟨dg t, dg t⁻¹, e1, e2⟩
  have hdet : Matrix.GeneralLinearGroup.det a = idF D t := by
    ext
    simp [a, dg, Finset.prod_update_of_mem]
  obtain ⟨g, hg⟩ := exists_levi (D := D) (n := n) a
  obtain ⟨u, hu⟩ := (exists_unip (dg t)).2 (hadj t)
  obtain ⟨u', hu'⟩ := (exists_unip (dg t⁻¹)).2 (hadj t⁻¹)
  obtain ⟨w, hw⟩ := exists_weyl (D := D) (n := n)
  have hinj : ∀ x y : StdUnn.G D n, mat x = mat y → x = y := fun x y h => Subtype.ext (Units.ext h)
  have hrel : g * w = u * w * u' * (w * w * w) * u := by
    refine hinj _ _ ?_
    have e4 : (adj (a⁻¹).1 : Mx D n n) = dg t⁻¹ := hadj t⁻¹
    rw [e4] at hg
    change mat g * mat w = mat u * mat w * mat u' * (mat w * mat w * mat w) * mat u
    rw [hg, hw, hu, hu']
    exact levi_weyl_rel e1 e2
  let S := ω.toHomUnits.eqLocus ω₀.toHomUnits
  have hU : ∀ (x : StdUnn.G D n) (b : Mx D n n), mat x = blk4 1 b 0 1 → x ∈ S := fun x b hx =>
    Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun y => (hω.unip x b hx Φ y).trans (hω₀.unip x b hx Φ y).symm))
  have hW : w ∈ S :=
    Units.ext (LinearMap.ext fun Φ => Subtype.ext (funext fun y => (hω.weyl w hw Φ y).trans (hω₀.weyl w hw Φ y).symm))
  have hgS : g ∈ S := by
    rw [← S.mul_mem_cancel_right hW, hrel]
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (hU _ _ hu) hW) (hU _ _ hu')) (S.mul_mem (S.mul_mem hW hW) hW)) (hU _ _ hu)
  have hge : ω g = ω₀ g := congrArg Units.val hgS
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.Published.ThetaConvModel.exists_schwartz θ V.rank n
  have k1 := hω.levi g a hg Φ 0
  rw [hge, hω₀.levi g a hg Φ 0, hdet] at k1
  have z1 : ((0 : Mx D V.rank n) ⬝ a.1 : Mx D V.rank n) = 0 := Matrix.zero_mul _
  rw [z1] at k1
  have hp : npow (absA D (idF D t)) ((V.rank : ℂ) / 2) ≠ 0 := by
    have : absA D (idF D t) ≠ 0 := ((Group.isUnit _).map (absA D)).ne_zero
    rw [npow, Complex.cpow_def_of_ne_zero (by exact_mod_cast this)]
    exact Complex.exp_ne_zero _
  exact Circle.ext (mul_right_cancel₀ hp (mul_right_cancel₀ hΦ k1)).symm

end GlobalTheory.RegSch.JointCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrArchPairAdeleJoin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section
open MeasureTheory
namespace GlobalTheory.WeilL2Words
variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem adeleJoin_archPart (a : κ → AdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F (archPart F a) (fun i => (a i).2) = a := by
  funext i
  simp only [GlobalTheory.WeilCont.adeleJoin, archPart, RingEquiv.symm_apply_apply]
  rfl

theorem adeleJoin_add_arch (x v : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y + arch F v = GlobalTheory.WeilCont.adeleJoin F (x + v) y := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i) + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (v i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i + v i)
    rw [map_add]
  · exact add_zero (y i)

theorem adeleJoin_dot_arch (x u : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilCont.adeleJoin F x y ⬝ᵥ arch F u = arch1 F (∑ i, x i * u i) := by
  rw [dotProduct, adeleOfMixedSpaceComponent_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [arch, mul_arch1']
  congr 2
  exact RingEquiv.apply_symm_apply _ _

theorem arch_dot_arch (v u : κ → mixedEmbedding.mixedSpace F) :
    arch F v ⬝ᵥ arch F u = arch1 F (∑ i, v i * u i) := by
  rw [dotProduct, adeleOfMixedSpaceComponent_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [arch, arch, mul_arch1']
  congr 2
  exact RingEquiv.apply_symm_apply _ _

theorem schA_exists_sum {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ} (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    ∃ (n : ℕ) (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ Φ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  rw [GlobalTheory.WeilM.schA, Submodule.mem_span_set'] at hΦ
  obtain ⟨n, c, s, rfl⟩ := hΦ
  choose f g hg hfg using fun i => (s i).2
  refine ⟨n, fun i => c i • f i, g, hg, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hfg i]
  ext a
  simp [GlobalTheory.WeilM.pureA, mul_assoc]

variable [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem ell_half (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (z : mixedEmbedding.mixedSpace F) :
    ℓ (InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1 * z) = ℓ z / 2 := by
  set c := InfiniteAdeleRing.ringEquiv_mixedSpace F (⅟(2 : AdeleRing (𝓞 F) F)).1
  have hc : c + c = 1 := by
    rw [← map_add]
    have : (⅟(2 : AdeleRing (𝓞 F) F)).1 + (⅟(2 : AdeleRing (𝓞 F) F)).1 = (⅟(2 : AdeleRing (𝓞 F) F) + ⅟2).1 := rfl
    rw [this, invOf_two_add_invOf_two]
    exact map_one _
  have h2 : ℓ (c * z) + ℓ (c * z) = ℓ z := by rw [← map_add, ← add_mul, hc, one_mul]
  linarith

theorem schr_archPair_adeleJoin (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.schr ψ (archPair F h) Φ (GlobalTheory.WeilCont.adeleJoin F x y) =
      Complex.exp (2 * Real.pi * Complex.I * ((ℓ (∑ i, x i * h.2 i) : ℂ) + (ℓ (∑ i, h.1 i * h.2 i) : ℂ) / 2)) *
        Φ (GlobalTheory.WeilCont.adeleJoin F (x + h.1) y) := by
  simp only [GlobalTheory.WeilM.schr, archPair]
  rw [adeleJoin_add_arch, adeleJoin_dot_arch, arch_dot_arch, mul_arch1', ← adeleOfMixedSpaceComponent_add, hℓ, map_add, ell_half]
  congr 2
  push_cast
  ring

theorem hasDerivAt_schr_pureA (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F f g) (GlobalTheory.WeilCont.adeleJoin F x y))
      ((2 * Real.pi * Complex.I * (ℓ (∑ i, x i * h.2 i) : ℂ) * f x + fderiv ℝ f x h.1) * g y) 0 := by
  set A : ℝ := ℓ (∑ i, x i * h.2 i)
  set B : ℝ := ℓ (∑ i, h.1 i * h.2 i) / 2
  have key : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F f g) (GlobalTheory.WeilCont.adeleJoin F x y)) =
      fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * ((t * A + t ^ 2 * B : ℝ) : ℂ)) * (f (x + t • h.1) * g y) := by
    funext t
    rw [schr_archPair_adeleJoin F ψ ℓ hℓ, GlobalTheory.WeilCont.pureA_adeleJoin]
    congr 2
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, A, B]
    have e1 : ∑ i, x i * (t • h.2 i) = t • ∑ i, x i * h.2 i := by
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _
    have e2 : ∑ i, (t • h.1 i) * (t • h.2 i) = (t ^ 2) • ∑ i, h.1 i * h.2 i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
    rw [e1, e2, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [key]
  have hφ := ((((hasDerivAt_id (0:ℝ)).mul_const A).fun_add ((hasDerivAt_pow 2 (0:ℝ)).mul_const B)).ofReal_comp).const_mul
    (2 * (Real.pi : ℂ) * Complex.I)
  have hS := ((f.hasFDerivAt (x + (0:ℝ) • h.1)).comp_hasDerivAt (0:ℝ)
      (((hasDerivAt_id (0:ℝ)).smul_const h.1).const_add x)).mul_const (g y)
  have hT := hφ.cexp.fun_mul hS
  refine hT.congr_deriv ?_
  simp only [id, Function.comp, zero_smul, add_zero, one_smul, zero_mul, mul_zero, Complex.ofReal_zero, Complex.exp_zero,
    one_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one, Complex.ofReal_pow]
  ring

omit [Invertible (2 : AdeleRing (𝓞 F) F)] in
theorem schr_sum' [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (w : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F)) {n : ℕ} (Φ : Fin n → (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.schr ψ w (∑ i, Φ i) = ∑ i, GlobalTheory.WeilM.schr ψ w (Φ i) := by
  funext x
  simp [GlobalTheory.WeilM.schr, Finset.sum_apply, Finset.mul_sum]

theorem hasDerivAt_schr_sum (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {n : ℕ}
    (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
        (GlobalTheory.WeilCont.adeleJoin F x y))
      (∑ i, (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * f i x + fderiv ℝ (f i) x h.1) * g i y) 0 := by
  have e : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i))
      (GlobalTheory.WeilCont.adeleJoin F x y)) = fun t => ∑ i, GlobalTheory.WeilM.schr ψ (archPair F (t • h)) (GlobalTheory.WeilM.pureA F (f i) (g i))
      (GlobalTheory.WeilCont.adeleJoin F x y) := by
    funext t
    rw [schr_sum', Finset.sum_apply]
  rw [e]
  exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hasDerivAt_schr_pureA F ψ ℓ hℓ h (f i) (g i) x y

theorem differentiableAt_schr {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsStdInf F ψ)
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) (a : κ → AdeleRing (𝓞 F) F) :
    DifferentiableAt ℝ (fun t : ℝ => GlobalTheory.WeilM.schr ψ (archPair F (t • h)) Φ a) 0 := by
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  obtain ⟨n, f, g, -, rfl⟩ := schA_exists_sum F hΦ
  rw [← adeleJoin_archPart F a]
  exact (hasDerivAt_schr_sum F ψ ℓ hℓ h f g _ _).differentiableAt

theorem dS_sum_adeleJoin (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {n : ℕ}
    (f : Fin n → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    dS F ψ h (∑ i, GlobalTheory.WeilM.pureA F (f i) (g i)) (GlobalTheory.WeilCont.adeleJoin F x y) =
      ∑ i, (2 * Real.pi * Complex.I * (ℓ (∑ k, x k * h.2 k) : ℂ) * f i x + fderiv ℝ (f i) x h.1) * g i y :=
  (hasDerivAt_schr_sum F ψ ℓ hℓ h f g x y).deriv

theorem dS_mem_schA {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsStdInf F ψ)
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) {Φ : (κ → AdeleRing (𝓞 F) F) → ℂ}
    (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) : dS F ψ h Φ ∈ GlobalTheory.WeilM.schA F κ := by
  obtain ⟨n, f, g, hg, rfl⟩ := schA_exists_sum F hΦ
  obtain ⟨f', hf'⟩ := dS_sum_pureA F κ ψ hψ n g f h
  rw [hf']
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, g i, hg i, rfl⟩

end GlobalTheory.WeilL2Words
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEisensteinSiegelConvergence
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec)

namespace GlobalTheory.WeilEisConv

theorem weilEisensteinSiegelConvergence : GlobalTheory.Published.WeilEisensteinSiegelConvergence := by
  intro D n V hn hV ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω Φ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, _, _, hκ, hW, hT⟩ :=
    GlobalTheory.StdUnn.SchDatum.exists_datum D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ).2.1 Φ.1 Φ.2
  have key : ∀ g : G D n, (ω g Φ).1 0 = swSec A V omh μ 𝓕 f (κ.symm g) := by
    intro g
    have h := hT (κ.symm g) f hf Φ hfΦ.symm
    have e : κ (κ.symm g) = g := κ.apply_symm_apply g
    rw [e] at h
    exact (congrFun h 0).trans (mixS_dblDec_zero A V ψ₀ μ 𝓕 _ 0)
  obtain ⟨a, ha⟩ := exists_isMaj A
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D A a ha
  obtain ⟨C, hC, h₁⟩ := GlobalTheory.SWAbsGrowth.norm_swSec_le hW hμ hf a ha
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hs : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hc.2.2.2, hc.2.2.2, star_star])
  have hP := GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P D A μ' hsk κ hκ
  have hG := GlobalTheory.StdUnn.chart_mem_GF_iff D A μ' hsk κ hκ
  have hb : (A.rank : ℝ) < (V.rank : ℝ) / 2 := by
    have : (2 * n : ℝ) < V.rank := by exact_mod_cast hV
    change (n : ℝ) < _
    linarith
  have hsum : Summable fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) =>
      (hgt A a (κ.symm (Subtype.val (q.out : GF D n))) : ℝ) ^ ((V.rank : ℝ) / 2) := by
    refine GlobalTheory.Eis.Conv.summable_hgt hc hs (GlobalTheory.Doubling.gram_hdbl A) (GlobalTheory.Doubling.isHermND_gram A)
      (GlobalTheory.Doubling.isCompact_Khat A a) hI (γ := fun q : GlobalTheory.Eis.Cosets (P D n) (GF D n) => κ.symm (Subtype.val (q.out : GF D n)))
      (fun q => (hG _).2 (by rw [MulEquiv.apply_symm_apply]; exact q.out.2)) (fun q q' h => ?_) hb
    have h' := (hP _).1 h
    rw [map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'
    rw [← q.out_eq, ← q'.out_eq]
    exact GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.2 ⟨⟨q'.out * q.out⁻¹, h'⟩, inv_mul_cancel_right _ _⟩
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => ?_) (hsum.mul_left C)
  simp only [GlobalTheory.Eis.term, mul_one]
  rw [key]
  exact h₁ _

end GlobalTheory.WeilEisConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationUnitaryCompat
section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.RealLift

namespace GlobalTheory.ConjLineSecond

theorem actsD_conj : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M.IsWeil B.ψ χX χW om →
    ∀ g ∈ UAt σ X (evI F), ∀ h ∈ UAt σ W (evI F), ∀ T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g, h)) f (T f)) → (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (g⁻¹, h⁻¹)) f (T.symm f)) →
    ∀ γ ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
      ActsD (evI F) (fun t => om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹)) (T f) (T f₁) := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hb hX hW _hM hw g _hg h _hh T hT hTs γ hγ f hf f₁ hf₁
  have hder := GlobalTheory.RealLift.Main.i_derex
  have hvl := GlobalTheory.RealLift.Main.i_vacline hder
  have hfe := GlobalTheory.RealLift.Main.i_fockex hder
  choose A hA hAθ using fun w => GlobalTheory.RealLift.Main.i_frameex _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.RealLift.Main.i_frameex _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [GlobalTheory.RealLift.Main.incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [GlobalTheory.RealLift.Main.incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := GlobalTheory.RealLift.Main.i_polrange GlobalTheory.RealLift.actsLaws hder hvl F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm
    hb.std fr hAθ hCθ hΦ
  have hsp : IsUSplitting (adeleClass F) B.ψ M.co (actAB (cA σ)) om := IsUWeilPair.isUSplitting hw
  have hsp2 := GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp
  obtain ⟨c, hc⟩ := GlobalTheory.RealLift.Main.i_liescalar hK.base hder hvl F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _
    hb.cm hb.std fr hΦ hsp2
  obtain ⟨Yg, -, hY⟩ := GlobalTheory.RealLift.Main.i_genex F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C hb.cm hC1 γ hγ
  obtain ⟨T0, rfl⟩ := GlobalTheory.RealLift.Main.pol_eq B M Φ hr hf
  obtain ⟨D, hSD⟩ : ∃ D, SD (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T0) D := ⟨_, hc γ hγ Yg hY T0⟩
  have hAD : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T0) D :=
    (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T0) D D).1 _ (fun t => map_zero _) hSD
  have e0 : f₁ = D := (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T0) f₁ D).2.2.1 _ hf₁ hAD
  subst e0
  have hSD2 : SD (fun t => om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹)) (T (Φ T0)) (T f₁) := by
    intro g' hg' l hl
    have hl' : l ∘ₗ om (g, h) ∈ (adeleClass F).adm (Fin n × Fin d) := hsp.adm (g, h) l hl
    have hrest : ∀ f0 : SInf F (Fin n × Fin d), Rest (evI F) (⇑f0) (fun x => g' fun i => (x i).2) := fun f0 =>
      ⟨fun x z hz => by
        show g' (fun i => (x i + z i).2) = g' (fun i => (x i).2)
        congr 1
        funext i
        show (x i).2 + (z i).2 = (x i).2
        rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz i, add_zero], Submodule.subset_span ⟨f0, g', hg', rfl⟩⟩
    have hpure : ∀ f0 : SInf F (Fin n × Fin d), pureA F (⇑f0) g' = tens (evI F) (⇑f0) (fun x => g' fun i => (x i).2) :=
      fun _ => rfl
    have e1 : om (g⁻¹, h⁻¹) (pureA F (⇑(T (Φ T0))) g') = pureA F (⇑(Φ T0)) g' := by
      rw [hpure, hTs _ _ (hrest _), LinearEquiv.symm_apply_apply]
      rfl
    have e2 : om (g, h) (pureA F (⇑f₁) g') = pureA F (⇑(T f₁)) g' := by
      rw [hpure, hT _ _ (hrest _)]
      rfl
    have e3 : ∀ t : ℝ, om (1, h * γ (Multiplicative.ofAdd t) * h⁻¹) (pureA F (⇑(T (Φ T0))) g') =
        om (g, h) (om (1, γ (Multiplicative.ofAdd t)) (pureA F (⇑(Φ T0)) g')) := by
      intro t
      have hp : ((1 : UA σ X.J), h * γ (Multiplicative.ofAdd t) * h⁻¹) = (g, h) * (1, γ (Multiplicative.ofAdd t)) * (g⁻¹, h⁻¹) :=
        Prod.ext (by simp) (by simp)
      rw [hp, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e1]
    simp only [e3]
    have := hSD g' hg' _ hl'
    simpa only [LinearMap.comp_apply, e2] using this
  exact (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (T (Φ T0)) (T f₁) (T f₁)).1 _ (fun t => map_zero _) hSD2

end GlobalTheory.ConjLineSecond
end
end

