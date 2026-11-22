import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange
import GroundTheory.GlobalFields.Adele.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MemSpanCentreTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0373

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToIdeleESymm
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeckeAbsArch

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem archUnitF_add (c d : ℝ) : archUnitF F (c + d) = archUnitF F c * archUnitF F d := by
  refine Units.ext (Prod.ext ?_ (mul_one _).symm)
  change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ =
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
  rw [← map_mul]
  congr 1
  refine Prod.ext (funext fun _ => ?_) (funext fun _ => ?_)
  · simp [Real.exp_add]
  · simp [Real.exp_add]

theorem archUnit_add (c d : ℝ) : archUnit F E (c + d) = archUnit F E c * archUnit F E d := by
  rw [archUnit, archUnitF_add, map_mul]
  rfl

theorem continuous_mixed_symm : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  have h : ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm = (homeomorphMixedSpace F).symm := funext fun p => by
    apply (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
    rw [RingEquiv.apply_symm_apply, ← homeomorphMixedSpace_apply, Homeomorph.apply_symm_apply]
  rw [h]
  exact (homeomorphMixedSpace F).symm.continuous

theorem continuous_archUnitF : Continuous (archUnitF F) := by
  have hp : ∀ s : ℝ, Continuous fun c : ℝ => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (fun _ => Real.exp (s * c), fun _ => ((Real.exp (s * c) : ℝ) : ℂ)) := fun s =>
    continuous_mixed_symm.comp ((continuous_pi fun _ => by fun_prop).prodMk (continuous_pi fun _ => by fun_prop))
  rw [Units.continuous_iff]
  constructor
  · refine ((hp 1).prodMk (continuous_const (y := (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))).congr fun c => ?_
    simp only [one_mul]
    rfl
  · refine ((hp (-1)).prodMk (continuous_const (y := (1 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))).congr fun c => ?_
    simp only [neg_one_mul]
    rfl

theorem continuous_archUnit : Continuous (archUnit F E) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have h : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  exact (Continuous.units_map _ h).comp continuous_archUnitF

def toIdeleE : (AF F ⊗[F] E)ˣ ≃* IdeleGroup E :=
  Units.mapEquiv (adeleTensorAlgEquivLeft F E).toRingEquiv.toMulEquiv

theorem continuous_toIdeleE : Continuous (toIdeleE (F := F) (E := E)) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have h : Continuous (adeleTensorAlgEquivLeft F E) :=
    IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).toLinearEquiv.toLinearMap
  exact Continuous.units_map ((adeleTensorAlgEquivLeft F E).toRingEquiv.toMulEquiv.toMonoidHom) h

theorem continuous_toIdeleE_symm : Continuous (toIdeleE (F := F) (E := E)).symm := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI := isModuleTopology_adeleRing (K := F) (L := E)
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have h : Continuous (adeleTensorAlgEquivLeft F E).symm :=
    IsModuleTopology.continuous_of_linearMap (adeleTensorAlgEquivLeft F E).symm.toLinearEquiv.toLinearMap
  exact Continuous.units_map ((adeleTensorAlgEquivLeft F E).symm.toRingEquiv.toMulEquiv.toMonoidHom) h

theorem toIdeleE_inclR (e : Eˣ) :
    toIdeleE (Units.map (inclR (F := F) (AF F)).toMonoidHom e) = IdeleGroup.diagonal E e := by
  apply Units.ext
  change adeleTensorAlgEquivLeft F E ((1 : AF F) ⊗ₜ[F] (e : E)) = _
  rw [adeleTensorAlgEquivLeft_tmul, map_one, mul_one, IdeleGroup.coe_diagonal]

theorem eq_zero_of_normOne (g : (AF F ⊗[F] E)ˣ → ℝ) (hg : Continuous g) (hmul : ∀ a b, g (a * b) = g a + g b)
    (hprin : ∀ e : Eˣ, g (Units.map (inclR (F := F) (AF F)).toMonoidHom e) = 0) (y : (AF F ⊗[F] E)ˣ)
    (hy : toIdeleE y ∈ IdeleGroup.normOneSubgroup E) : g y = 0 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  obtain ⟨B, hB⟩ := hD.exists_bound_of_continuousOn (hg.comp continuous_toIdeleE_symm).continuousOn
  have h1 : g 1 = 0 := by have := hmul 1 1; rw [mul_one] at this; linarith
  have hpow : ∀ n : ℕ, g (y ^ n) = n * g y := by
    intro n
    induction n with
    | zero => simp [h1]
    | succ n ih => rw [pow_succ, hmul, ih]; push_cast; ring
  have key : ∀ n : ℕ, |(n : ℝ) * g y| ≤ B := by
    intro n
    obtain ⟨k, hk⟩ := hxD (toIdeleE (y ^ n)) (by rw [map_pow]; exact pow_mem hy n)
    have e1 : toIdeleE.symm (IdeleGroup.diagonal E k * toIdeleE (y ^ n)) =
        Units.map (inclR (F := F) (AF F)).toMonoidHom k * y ^ n := by
      rw [map_mul, MulEquiv.symm_apply_apply, ← toIdeleE_inclR (F := F) k, MulEquiv.symm_apply_apply]
    have := hB _ hk
    rw [Function.comp_apply, e1, hmul, hprin, zero_add, hpow, Real.norm_eq_abs] at this
    exact this
  by_contra hne
  have hpos : 0 < |g y| := abs_pos.2 hne
  obtain ⟨n, hn⟩ := exists_nat_gt (B / |g y|)
  have h2 := key n
  rw [abs_mul, Nat.abs_cast] at h2
  have h3 := (div_lt_iff₀ hpos).1 hn
  linarith

theorem absE_archUnit {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (c : ℝ) :
    (absE F E (archUnit F E c) : ℝ) = Real.exp (2 * Module.finrank ℚ F * c) := by
  haveI := hσ.1
  have hN : Algebra.norm (AF F) ((archUnit F E c : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((archUnitF F c : (AF F)ˣ) : AF F) ^ 2 := by
    change Algebra.norm (AF F) (algebraMap (AF F) (AF F ⊗[F] E) (archUnitF F c : AF F)) = _
    rw [Algebra.norm_algebraMap, Module.finrank_baseChange, hσ.2.2.1]
  have hinf : ∀ w : InfinitePlace F, ‖evInf F w ((archUnitF F c : (AF F)ˣ) : AF F)‖ = Real.exp c := by
    intro w
    have hw : w.IsReal := IsTotallyReal.isReal w
    have h := congrArg (fun p => p.1 ⟨w, hw⟩) ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply
      (fun _ => Real.exp c, fun _ => ((Real.exp c : ℝ) : ℂ)))
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply] at h
    change ‖(InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (fun _ => Real.exp c, fun _ => ((Real.exp c : ℝ) : ℂ)) w‖ = _
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _), h,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos c)]
  have hfin : ∀ v, evFin F v ((archUnitF F c : (AF F)ˣ) : AF F) = 1 := fun v => rfl
  rw [GlobalTheory.Doubling.absE_apply]
  simp only [GlobalTheory.Doubling.absEw_unitInf, GlobalTheory.Doubling.absEv_unitFin, hN, map_pow, hfin, one_pow, nnnorm_one,
    finprod_one, mul_one, NNReal.coe_prod, NNReal.coe_pow, coe_nnnorm, norm_pow, hinf]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← pow_mul, ← Real.exp_nat_mul]
  push_cast
  ring_nf

end GlobalTheory.HeckeAbsArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalInvTransposeStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_inv_transpose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsCuspidal π → IsCuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  first | exact @GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose | exact GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose | (intros; apply GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutPMulCutP
section
noncomputable section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CentreFin

variable {n r : ℕ}

def cutP (J : Matrix (Fin n) (Fin n) ℂ) (X Y : Matrix (Fin n) (Fin r) ℂ) (k : Fin r) : Matrix (Fin n) (Fin n) ℂ :=
  X * diagonal (fun i => if i ≤ k then (1 : ℂ) else 0) * (Yᴴ * J)

variable {J : Matrix (Fin n) (Fin n) ℂ} {X Y : Matrix (Fin n) (Fin r) ℂ}

theorem dual_swap (hJ : Jᴴ = J) (hxy : Xᴴ * J * Y = 1) : Yᴴ * J * X = 1 := by
  have := congrArg conjTranspose hxy
  rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ, conjTranspose_one, ← Matrix.mul_assoc] at this

section Global

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem map_cT_emb (h : IsCMExt F E σ) (τ : E →+* ℂ) {a b : ℕ} (C : Matrix (Fin a) (Fin b) E) :
    (Formalism.UG.cT (σ : E →+* E) C).map τ = (C.map τ)ᴴ :=
  Matrix.ext fun i j => h.2.2.2 τ (C j i)

theorem frame_emb (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} {X Y : Matrix (Fin n) (Fin r) E}
    (hW : IsWittFrame σ J X Y) (τ : E →+* ℂ) :
    (X.map τ)ᴴ * J.map τ * X.map τ = 0 ∧ (Y.map τ)ᴴ * J.map τ * Y.map τ = 0 ∧ (X.map τ)ᴴ * J.map τ * Y.map τ = 1 := by
  simp only [← map_cT_emb h, ← Matrix.map_mul]
  rw [hW.xx, hW.yy, hW.xy]
  exact ⟨Matrix.map_zero _ (map_zero _), Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)⟩

end Global

end GlobalTheory.CentreFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefinitePairsRatioLocallyRationalTimesNormStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definitePairs_ratio_locally_rational_times_norm : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω →
    ∀ (P₁ : GlobalTheory.LKDef.DPair G) (L : Type) [Field L] [NumberField L] (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
    Function.Injective ι → (∀ z : G.C, z * P₁.γ = P₁.γ * z ↔ ∃ w, ι w = z) →
    (∀ x, ι (c x) = P₁.β * sh G (ι x) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum ℤ), ∀ (P : GlobalTheory.LKDef.DPair G), P.γ = P₁.γ → P.c = P₁.c →
      (∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.toAf x t hx P.self ∈ Ω) →
      ∀ a : L, ι a = ((P.β * P₁.β⁻¹ : G.Cˣ) : G.C) → ∀ v ∉ S,
        ∃ (r : (v.adicCompletion ℚ)ˣ) (y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ),
          (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a = algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) (r : v.adicCompletion ℚ) *
            ((y : v.adicCompletion ℚ ⊗[ℚ] L) * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c y) := by
  first | (exact @GlobalTheory.LocTriv.ratio_local_norm_dpair) | (exact GlobalTheory.LocTriv.ratio_local_norm_dpair) | (intros; apply GlobalTheory.LocTriv.ratio_local_norm_dpair  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockSymbolMatrixNeZero
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem det_blockSymbolMatrix_ne_zero (E : Type) [Field E] (J : Type) [Fintype J] [DecidableEq J]
    (δ e : ℕ) (g : Fin δ → E) (R : Matrix (Fin δ) (Fin δ) E) (hg : ∀ p, g p ≠ 0) (hR : R.det ≠ 0) :
    (Matrix.of fun i i' : J × Fin δ => if i.1 = i'.1 then g i.2 ^ e * R i.2 i'.2 else 0).det ≠ 0 := by
  set A : Matrix (J × Fin δ) (J × Fin δ) E :=
    Matrix.of fun i i' : J × Fin δ => if i.1 = i'.1 then g i.2 ^ e * R i.2 i'.2 else 0 with hA
  have key : Matrix.reindex (Equiv.prodComm J (Fin δ)) (Equiv.prodComm J (Fin δ)) A =
      Matrix.blockDiagonal (fun _ : J => Matrix.diagonal (fun p => g p ^ e) * R) := by
    ext ⟨p, j⟩ ⟨p', j'⟩
    simp [A, Matrix.blockDiagonal_apply, Matrix.diagonal_mul]
  rw [← Matrix.det_reindex_self (Equiv.prodComm J (Fin δ)) A, key, Matrix.det_blockDiagonal]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  rw [Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ (hg p)) hR

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetIsMultiHomogeneous
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSShort.DetHom

section MH

variable {R : Type} [CommSemiring R] {B n : ℕ}

theorem mh_zero (a : Fin B → ℕ) : IsMultiHomogeneous a (0 : MvPolynomial (Fin B × Fin n) R) := by
  intro s hs; simp at hs

theorem mh_C (r : R) : IsMultiHomogeneous (0 : Fin B → ℕ) (C r : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [mem_support_iff, coeff_C] at hs
  have : (0 : Fin B × Fin n →₀ ℕ) = s := by
    by_contra h; exact hs (if_neg h)
  subst this; simp

theorem mh_X (i : Fin B) (j : Fin n) :
    IsMultiHomogeneous (Pi.single i 1) (X (i, j) : MvPolynomial (Fin B × Fin n) R) := by
  classical
  intro s hs b
  rw [mem_support_iff, coeff_X'] at hs
  have : Finsupp.single (i, j) 1 = s := by
    by_contra h; exact hs (if_neg h)
  subst this
  by_cases hb : b = i
  · subst hb; simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, hb, Pi.single_apply]

theorem mh_add {a : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous a g) : IsMultiHomogeneous a (f + g) := by
  classical
  intro s hs
  rcases Finset.mem_union.1 (support_add hs) with h | h
  exacts [hf s h, hg s h]

theorem mh_sum {ι : Type} (t : Finset ι) {a : Fin B → ℕ} (f : ι → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ t, IsMultiHomogeneous a (f i)) : IsMultiHomogeneous a (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using mh_zero (R := R) (n := n) a
  | insert x t hx ih =>
    rw [Finset.sum_insert hx]
    exact mh_add (hf x (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem mh_smul {S : Type} [SMulZeroClass S R] {a : Fin B → ℕ} (c : S) {f : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) : IsMultiHomogeneous a (c • f) :=
  fun s hs => hf s (support_smul hs)

theorem mh_mul {a b : Fin B → ℕ} {f g : MvPolynomial (Fin B × Fin n) R}
    (hf : IsMultiHomogeneous a f) (hg : IsMultiHomogeneous b g) : IsMultiHomogeneous (a + b) (f * g) := by
  classical
  intro s hs i
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 (support_mul f g hs)
  simp [Finset.sum_add_distrib, hf u hu i, hg v hv i]

theorem mh_prod {ι : Type} (t : Finset ι) (a : ι → Fin B → ℕ) (f : ι → MvPolynomial (Fin B × Fin n) R)
    (hf : ∀ i ∈ t, IsMultiHomogeneous (a i) (f i)) : IsMultiHomogeneous (∑ i ∈ t, a i) (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using mh_C (R := R) (B := B) (n := n) 1
  | insert x t hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    exact mh_mul (hf x (Finset.mem_insert_self _ _)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end MH

def cnt {B t : ℕ} (β : Fin t → Fin B) (b : Fin B) : ℕ := (Finset.univ.filter fun q => β q = b).card

theorem sum_cnt {B t : ℕ} (β : Fin t → Fin B) : ∑ b, cnt β b = t := by
  classical
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (β x))]
  simp

theorem sum_single_eq_cnt {B t : ℕ} (β : Fin t → Fin B) :
    (∑ i, (Pi.single (β i) 1 : Fin B → ℕ)) = cnt β := by
  classical
  funext b
  simp only [Finset.sum_apply, Pi.single_apply, cnt]
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : β i = b
  · simp [h]
  · simp [h, Ne.symm h]

theorem mh_coordP {K A : Type} [Field K] [AddCommGroup A] [Module K A] {N B t : ℕ}
    (mul : (Fin N → K) →ₗ[K] Module.End K A) (c : A →ₗ[K] K) (β : Fin t → Fin B) (m : A) :
    IsMultiHomogeneous (cnt β) (coordP mul c β m) := by
  classical
  unfold coordP
  refine mh_sum _ _ fun e _ => ?_
  have h := mh_mul (mh_C (R := K) (B := B) (n := N) (c (word mul (fun i => Pi.single (e i) 1) m)))
    (mh_prod Finset.univ (fun i => (Pi.single (β i) 1 : Fin B → ℕ)) (fun i => (X (β i, e i) : MvPolynomial (Fin B × Fin N) K))
      fun i _ => mh_X (β i) (e i))
  rwa [zero_add, sum_single_eq_cnt] at h

end GlobalTheory.HSShort.DetHom

open GlobalTheory.HSShort.DetHom in

theorem GlobalTheory.HSShort.det_isMultiHomogeneous : ∀ (F A : Type) [Field F] [NumberField F] [AddCommGroup A] [Module F A] [Module (𝓞 F) A] [IsScalarTower (𝓞 F) F A] (S : Sys F A) (d : ℕ) (c : Fin d → A →ₗ[F] F) (col : Fin d → S.Col), ∃ a : Fin (S.D + 1) → ℕ, IsMultiHomogeneous a (S.det c col) ∧ ∑ i, a i = ∑ k, (col k).t := by
  intro F A _ _ _ _ _ _ S d c col
  classical
  refine ⟨∑ k, cnt (col k).β, ?_, ?_⟩
  · unfold Sys.det
    rw [Matrix.det_apply]
    refine mh_sum _ _ fun σ _ => mh_smul _ ?_
    have h := mh_prod Finset.univ (fun k => cnt (col k).β)
      (fun k => (Matrix.of fun i k => coordP S.mul (c i) (col k).β ((col k).x : A)) (σ k) k)
      fun k _ => by simpa using mh_coordP S.mul (c (σ k)) (col k).β ((col k).x : A)
    exact h
  · simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => sum_cnt (col k).β
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetSpanCommonDenominator
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

open NumberField MvPolynomial in

theorem _root_.GlobalTheory.det_span_common_denominator : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (d : ℕ) (β : Module.Basis (Fin d) F V) (M : Submodule (𝓞 F) V), M.FG → ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ y ∈ Submodule.span (𝓞 F) {y | ∃ w : Fin d → V, (∀ i, w i ∈ M) ∧ y = β.det w}, c • y ∈ (1 : Submodule (𝓞 F) F) := by
  intro F V _ _ _ _ _ _ d β M hM
  obtain ⟨S, hS⟩ := hM
  obtain ⟨c₀, hc₀⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F))
    (Finset.univ ×ˢ S) (fun p : Fin d × V => β.repr p.2 p.1)
  have hcoord : ∀ x ∈ M, ∀ i, (c₀ : 𝓞 F) • β.repr x i ∈ (1 : Submodule (𝓞 F) F) := by
    intro x hx i
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨r, hr⟩ := hc₀ (i, g) (Finset.mem_product.mpr ⟨Finset.mem_univ _, hg⟩)
      exact Submodule.mem_one.mpr ⟨r, hr⟩
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, Finsupp.add_apply, smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      convert Submodule.smul_mem _ a hx using 1
      rw [← algebraMap_smul F a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def]
      ring
  refine ⟨(c₀ : 𝓞 F) ^ d, pow_ne_zero _ (nonZeroDivisors.ne_zero c₀.2), ?_⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    choose B hB using fun i j => Submodule.mem_one.mp (hcoord (w j) (hw j) i)
    rw [Submodule.mem_one]
    refine ⟨(Matrix.of B).det, ?_⟩
    have hmat : (algebraMap (𝓞 F) F).mapMatrix (Matrix.of B) =
        algebraMap (𝓞 F) F (c₀ : 𝓞 F) • β.toMatrix w := by
      ext i j
      simp [Module.Basis.toMatrix_apply, hB, Algebra.smul_def]
    rw [RingHom.map_det, hmat, Matrix.det_smul, Fintype.card_fin, Module.Basis.det_apply,
      Algebra.smul_def, map_pow]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylModuleLeSpanExtremalTranslates
section
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

namespace GlobalTheory

theorem sqAct_sqAct_nabla (K : Type) [Field K] (n : ℕ) (lam : DomWeight n) (g h : GL (Fin n) K)
    (f : MvPolynomial (Fin n × Fin n) K) :
    sqAct K n lam g (sqAct K n lam h f) = sqAct K n lam (g * h) f := by
  unfold sqAct
  have hm := congrArg (fun φ => φ f) (Formalism.GradedWeylDivisibility.rowActMul K n n
    ((g : Matrix (Fin n) (Fin n) K)ᵀ) ((h : Matrix (Fin n) (Fin n) K)ᵀ))
  simp only [AlgHom.comp_apply] at hm
  rw [map_smul, hm, smul_smul, ← Matrix.transpose_mul]
  congr 1
  unfold detPow
  rw [map_mul, mul_zpow, Units.val_mul]

theorem sqAct_one_nabla (K : Type) [Field K] (n : ℕ) (lam : DomWeight n)
    (f : MvPolynomial (Fin n × Fin n) K) : sqAct K n lam 1 f = f := by
  unfold sqAct detPow
  simp only [Matrix.GeneralLinearGroup.coe_one, Matrix.transpose_one, map_one, one_zpow, Units.val_one, one_smul]
  have h1 : Formalism.GradedWeylDivisibility.rowAct K (n := n) (1 : Matrix (Fin n) (Fin n) K) = AlgHom.id K _ := by
    apply MvPolynomial.algHom_ext
    intro v
    unfold Formalism.GradedWeylDivisibility.rowAct
    rw [aeval_X]
    simp [Matrix.one_apply, ite_mul]
  rw [h1]; rfl

theorem nablaSq_le_span_extremal : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (lam : DomWeight n),
    nablaSq K n lam ≤ Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) := by
  intro K _ _ n lam
  set M := Submodule.span K (Set.range fun g : GL (Fin n) K => sqAct K n lam g (extremal K n lam)) with hM
  have hanti : Antitone lam.natW := by
    intro i j hij
    have := lam.anti hij
    unfold DomWeight.natW
    omega
  have hext : extremal K n lam ∈ nablaSq K n lam :=
    Formalism.GradedWeylDivisibility.hwMem K n n le_rfl lam.natW hanti
  have hstab : ∀ g : GL (Fin n) K, ∀ f ∈ nablaSq K n lam, sqAct K n lam g f ∈ nablaSq K n lam := by
    intro g f hf
    unfold sqAct
    exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable K n n lam.natW _ f hf)
  have hle : M ≤ nablaSq K n lam := by
    rw [hM, Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hstab g _ hext
  have hlin : ∀ g : GL (Fin n) K, ∀ (c : K) (f₁ f₂ : MvPolynomial (Fin n × Fin n) K),
      sqAct K n lam g (c • f₁ + f₂) = c • sqAct K n lam g f₁ + sqAct K n lam g f₂ := by
    intro g c f₁ f₂
    unfold sqAct
    rw [map_add, map_smul, smul_add, smul_comm]
  have hMstab : ∀ g : GL (Fin n) K, ∀ f ∈ M, sqAct K n lam g f ∈ M := by
    intro g f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [sqAct_sqAct_nabla]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero =>
      have h0 : sqAct K n lam g 0 = 0 := by unfold sqAct; simp
      rw [h0]; exact M.zero_mem
    | add x y _ _ hx hy =>
      have := hlin g 1 x y
      rw [one_smul, one_smul] at this
      rw [this]; exact M.add_mem hx hy
    | smul c x _ hx =>
      have hs : sqAct K n lam g (c • x) = c • sqAct K n lam g x := by
        unfold sqAct; rw [map_smul, smul_comm]
      rw [hs]; exact M.smul_mem c hx
  rcases GlobalTheory.T.dualWeylModule_simple_charZero K n lam M hle hMstab with h0 | h1
  · exfalso
    have hmem : extremal K n lam ∈ M := by
      have : sqAct K n lam 1 (extremal K n lam) ∈ M := Submodule.subset_span ⟨1, rfl⟩
      rwa [sqAct_one_nabla] at this
    rw [h0, Submodule.mem_bot] at hmem
    exact Formalism.GradedWeylDivisibility.hwNe K n n le_rfl lam.natW hmem
  · rw [h1]

end GlobalTheory
end
end

