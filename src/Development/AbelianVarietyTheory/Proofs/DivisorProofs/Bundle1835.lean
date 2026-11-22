import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1772
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1194
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1780
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1803
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1761
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalSubgroupFirstProjEqAnnihilatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLocalSubgroup_firstProj_eq_annihilator : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    [DecidableEq κ] (ψk : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψk (x * y) = 1) ↔ x ∈ v.adicCompletionIntegers F) →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψk (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψk (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  first | exact @GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator | exact GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator | (intros; apply GlobalTheory.SelfDualFirstProj.exists_pair_of_annihilator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralConjugateScaledUnitaryGroupEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ConjUIntegral

theorem setIntegral_conjU_eq : ∀ {D : D7} (V : HSp D) {J : Matrix (Fin V.rank) (Fin V.rank) D.host.E} (c : D.host.E), c ≠ 0 →
    ∀ (h : J = c • V.gram) (ν : Measure (GA D V)) (fd : Set (GA D V)), ν.IsHaarMeasure → IsFundamentalDomain (GQ V) fd ν →
    ∀ dom : Set (UB J), IsFundamentalDomain (ratU D.sp.cm.sig J) dom (ν.map (conjU V c h)) →
    ∀ f : UB J → ℂ, (∀ γ ∈ ratU D.sp.cm.sig J, ∀ x, f (γ * x) = f x) →
      ∫ u in fd, f (conjU V c h u) ∂ν = ∫ x in dom, f x ∂(ν.map (conjU V c h)) := by
  intro D V J c hc h ν fd hν hfd dom hdom f hf
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : IsTopologicalRing (AE D) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing
  have : BorelSpace (UB J) := ⟨rfl⟩
  let φ := GlobalTheory.ConjUTransport.conjEquiv V c hc h
  have c1 : Continuous φ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU V c h
  have c2 : Continuous φ.symm := GlobalTheory.ConjUTransport.continuous_conjUInv V c hc h
  let H : GA D V ≃ₜ UB J := ⟨φ.toEquiv, c1, c2⟩
  have hme : MeasurableEmbedding (conjU V c h) := H.measurableEmbedding
  obtain ⟨hH, hfd'⟩ := GlobalTheory.ConjUTransport.map_isHaar_isFundamentalDomain V c hc h ν fd hν hfd
  have e1 : ∫ x in conjU V c h '' fd, f x ∂(ν.map (conjU V c h)) = ∫ u in fd, f (conjU V c h u) ∂ν := by
    rw [hme.setIntegral_map, Set.preimage_image_eq _ hme.injective]
  rw [← e1]
  haveI := GlobalTheory.UnitaryVol.countable_ratU D.sp.cm.sig J
  haveI := hH
  haveI : SMulInvariantMeasure (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (UB J) (ν.map (conjU V c h)) :=
    ⟨fun γ A _ => measure_preimage_mul (ν.map (conjU V c h)) γ.1 A⟩
  exact hfd'.setIntegral_eq hdom fun γ x => hf γ.1 γ.2 x

end GlobalTheory.ConjUIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicChartLeviBlock
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.SWLit
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (UA incM ratU)
open GlobalTheory.WeilM (Darboux symp schA thetaSum UG)
open GlobalTheory.SiegelFormula (coord)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SWLink

namespace GlobalTheory.SWLink.Sieg

def blkC {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) : Matrix (Fin n) (Fin n) R :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

theorem exists_blockMatrixTwoByTwoFin_eq {R : Type} {n : ℕ} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    ∃ a b c d, M = StdUnn.blk4 a b c d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  unfold StdUnn.blk4
  rw [Matrix.fromBlocks_toBlocks]
  simp

theorem submatrix_sum_equiv_fromBlocks {R : Type} {n : ℕ} (a b c d : Matrix (Fin n) (Fin n) R) :
    (StdUnn.blk4 a b c d).submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks a b c d := by
  simp [StdUnn.blk4]

theorem key {R : Type} [CommRing R] {n : ℕ} (M N : Matrix (Fin (n + n)) (Fin (n + n)) R) (Z Z' : Matrix (Fin n) (Fin n) R)
    (hZ : Z' * Z = 1) (h2 : ∀ z : Matrix (Fin n) (Fin n) R, z + z = 0 → z = 0)
    (h : M * StdUnn.blk4 1 Z 1 (-Z) = StdUnn.blk4 1 Z 1 (-Z) * N) :
    (KeepsDiag finSumFinEquiv M ↔ blkC N = 0) ∧ (blkC N = 0 → StdUnn.blkA N = leviMat finSumFinEquiv M) := by
  obtain ⟨a, b, c, d, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq N
  obtain ⟨p, q, r, s, rfl⟩ := exists_blockMatrixTwoByTwoFin_eq M
  rw [StdUnn.Model.submatrix_fromBlocks_mul, StdUnn.Model.submatrix_fromBlocks_mul] at h
  obtain ⟨h1, -, h3, -⟩ := StdUnn.Model.blockMatrixTwoByTwoFin_injective h
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul] at h1 h3
  simp only [KeepsDiag, leviMat, blkC, StdUnn.blkA, submatrix_sum_equiv_fromBlocks, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, h1, h3]
  refine ⟨⟨fun h4 => ?_, fun h4 => by simp [h4]⟩, fun h4 => by simp [h4]⟩
  have h5 : Z * c = 0 := h2 _ (neg_eq_iff_add_eq_zero.1 (add_left_cancel h4))
  rw [← Matrix.one_mul c, ← hZ, Matrix.mul_assoc, h5, Matrix.mul_zero]

theorem mulVec_upper {R : Type} [CommRing R] {n : ℕ} {N : Matrix (Fin (n + n)) (Fin (n + n)) R} (hN : blkC N = 0)
    (x : Fin (n + n) → R) (hx : ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0) (i : Fin n) :
    (N *ᵥ x) (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0 := by
  have h : ∀ j : Fin n, N (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) = 0 :=
    fun j => congrFun (congrFun hN i) j
  simp only [Matrix.mulVec, dotProduct]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [h, hx, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

variable {D : D7} {n : ℕ}

theorem mem_upperHalf {x : Fin (n + n) → AE D} :
    x ∈ StdUnn.upperHalf D n ↔ ∀ i : Fin n, x (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) = 0 :=
  funext_iff

theorem mem_siegelParabolic_of {g : StdUnn.G D n} (h : blkC (StdUnn.mat g) = 0) (h' : blkC (StdUnn.mat g⁻¹) = 0) :
    g ∈ StdUnn.P D n := by
  refine fun x => ⟨fun hx => mem_upperHalf.2 (mulVec_upper h x (mem_upperHalf.1 hx)), fun hx => ?_⟩
  have : (StdUnn.mat g⁻¹).mulVec ((StdUnn.mat g).mulVec x) ∈ StdUnn.upperHalf D n :=
    mem_upperHalf.2 (mulVec_upper h' _ (mem_upperHalf.1 hx))
  rwa [Matrix.mulVec_mulVec, show StdUnn.mat g⁻¹ * StdUnn.mat g = StdUnn.mat (g⁻¹ * g) from rfl, inv_mul_cancel,
    show StdUnn.mat (1 : StdUnn.G D n) = 1 from rfl, Matrix.one_mulVec] at this

theorem blkC_of_mem_P {g : StdUnn.G D n} (h : g ∈ StdUnn.P D n) : blkC (StdUnn.mat g) = 0 := by
  funext i j
  exact StdUnn.Model.lower_eq_zero h i j

theorem siegel_chart : ∀ (D : D7) (n : ℕ) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E) (T : GL (Fin (n + n)) D.host.E) (κ : UD D J₂ ≃* GlobalTheory.StdUnn.G D n), IsChartW T κ → ∀ J : Matrix (Fin n) (Fin n) D.host.E, IsWittBasis D.sp.cm.sig J 1 T → (∀ g : UD D J₂, g ∈ siegelOf finSumFinEquiv (uinc D J₂) ↔ κ g ∈ GlobalTheory.StdUnn.P D n) ∧ ∀ p : siegelOf finSumFinEquiv (uinc D J₂), GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat (κ p)) = (leviOf finSumFinEquiv (uinc D J₂) p).1 := by
  intro D n J₂ T κ hκ J hT
  obtain ⟨Z, hZ, hT⟩ := hT
  rw [one_smul, ← Matrix.smul_mul] at hZ
  have h1 : (rat ((2 : D.host.E) • J) : Mx D n n) * cj (rat Z) = 1 := by rw [cj_rat, ← rat_mul, hZ, rat_one]
  have h2 : (cj (rat ((2 : D.host.E) • J)) : Mx D n n) * rat Z = 1 := by
    have := congrArg cj h1
    rwa [cj_mul, cj_cj, cj_one] at this
  have hm : (rat T.1 : Mx D (n + n) (n + n)) = StdUnn.blk4 1 (rat Z) 1 (-rat Z) := by
    rw [hT, blk_eq, rat_fromBlocks_map, rat_one, rat_neg]
  have hk : ∀ g : UD D J₂, (KeepsDiag finSumFinEquiv (umat g) ↔ blkC (StdUnn.mat (κ g)) = 0) ∧
      (blkC (StdUnn.mat (κ g)) = 0 → StdUnn.blkA (StdUnn.mat (κ g)) = leviMat finSumFinEquiv (umat g)) := fun g =>
    key _ _ _ _ h2 (fun _ => eq_zero_of_add_self) (by rw [← hm]; exact hκ.mul_eq g)
  have hs : ∀ g : UD D J₂, g ∈ siegelOf finSumFinEquiv (uinc D J₂) ↔ blkC (StdUnn.mat (κ g)) = 0 := fun g =>
    mem_siegelOf.trans (hk g).1
  refine ⟨fun g => ⟨fun hg => mem_siegelParabolic_of ((hs g).1 hg) ?_, fun hg => (hs g).2 (blkC_of_mem_P hg)⟩,
    fun p => (hk p).2 ((hs p).1 p.2)⟩
  rw [← map_inv]
  exact (hs _).1 (inv_mem hg)

end GlobalTheory.SWLink.Sieg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianSelfDualLatticeHyperbolicPlaneSplit
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (splitPrime IsSplitBasis)

section Helpers
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}

theorem sigma_sigma (h : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem form_smul_left (J : Matrix (Fin n) (Fin n) E) (c : E) (a b : Fin n → E) :
    form σ J (c • a) b = c * form σ J a b := by
  simp only [form, smul_dotProduct, smul_eq_mul]

theorem form_smul_right (J : Matrix (Fin n) (Fin n) E) (c : E) (a b : Fin n → E) :
    form σ J a (c • b) = σ c * form σ J a b := by
  have : (fun i => σ ((c • b) i)) = σ c • fun i => σ (b i) := funext fun i => by simp
  simp only [form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) (J : Matrix (Fin n) (Fin n) E) (a b : Fin n → E) :
    (fun i => τ (a i)) ⬝ᵥ (Complex.I • J.map τ) *ᵥ star (fun i => τ (b i)) = Complex.I * τ (form σ J a b) := by
  simp only [form, dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.map_apply, Pi.star_apply, smul_eq_mul,
    map_sum, map_mul, hτ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Finset.mul_sum, mul_assoc, mul_left_comm]

end Helpers

end GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (splitPrime IsSplitBasis)

section Helpers2
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}

theorem gram_skew (h : IsCMExt F E σ) {J : Matrix (Fin n) (Fin n) E} (hJ : ∀ i j, σ (J j i) = -J i j)
    (ι : Matrix (Fin n) (Fin n₁) E) (i j : Fin n₁) :
    σ ((ιᵀ * J * ι.map σ) j i) = -(ιᵀ * J * ι.map σ) i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, sigma_sigma h, hJ,
    Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) :
    (ι.map τ)ᵀ * (Complex.I • J.map τ) * (ι.map τ).map star = Complex.I • (ιᵀ * J * ι.map σ).map τ := by
  have e : (ι.map σ).map τ = (ι.map τ).map star := Matrix.ext fun i j => by simp [hτ]
  rw [Matrix.map_mul, Matrix.map_mul, e, Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]

theorem herm_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) : (Complex.I • J.map τ).conjTranspose = Complex.I • J.map τ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← hτ, hJ,
    map_neg, Complex.star_def, Complex.conj_I]
  ring

theorem orth_map (τ : E →+* ℂ) (hτ : ∀ a, τ (σ a) = star (τ a)) (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (a : Fin n → E) (h : ∀ u, form σ J (ι *ᵥ u) a = 0) (u : Fin n₁ → ℂ) :
    (ι.map τ *ᵥ u) ⬝ᵥ (Complex.I • J.map τ) *ᵥ star (fun i => τ (a i)) = 0 := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec]
  have hz : ((Complex.I • J.map τ) *ᵥ star (fun i => τ (a i))) ᵥ* ι.map τ = 0 := by
    funext j
    have e := form_map τ hτ J (ι *ᵥ Pi.single j 1) a
    rw [h, map_zero, mul_zero, Matrix.mulVec_single_one] at e
    rw [Pi.zero_apply, ← e, dotProduct_comm]
    simp [Matrix.vecMul, dotProduct, Matrix.col, mul_comm]
  rw [hz, zero_dotProduct]

theorem inj_map (τ : E →+* ℂ) (ι : Matrix (Fin n) (Fin n₁) E) (h : Function.Injective ι.mulVec) :
    Function.Injective (ι.map τ).mulVec := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin ι)
    (LinearMap.ker_eq_bot.2 h)
  set K := LinearMap.toMatrix' g
  have hK : K * ι = 1 := by
    rw [← LinearMap.toMatrix'_toLin' ι, ← LinearMap.toMatrix'_comp, Matrix.toLin'_apply', hg,
      LinearMap.toMatrix'_id]
  intro u u' e
  have := congrArg (fun z => (K.map τ) *ᵥ z) e
  simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, hK, Matrix.map_one _ (map_zero τ) (map_one τ),
    Matrix.one_mulVec] at this
  exact this

end Helpers2
end GlobalTheory.PlaneSkew

namespace GlobalTheory.PlaneSkew
open GlobalTheory.AdelicU (splitPrime IsSplitBasis)

theorem plane_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ), n = n₁ + 2 → 1 ≤ n₁ → ∀ (Y : Spc F E n) (r s : ℕ), 1 ≤ r → 1 ≤ s →
    Y.IsSkew σ B r s → ∀ i₀ i₁ : ℕ, i₀ < i₁ → i₁ < n → ∃ (Y' : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁),
      (GlobalTheory.ThK.reS Y Y').IsSkew σ B r s ∧ Y₁.IsSkew σ B (r - 1) (s - 1) ∧
        H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') Y₁ i₀ i₁ := by
  intro F E _ _ _ _ _ σ B hB n n₁ hn hn₁ Y r s hr hs hY i₀ i₁ h01 h1n
  classical
  subst hn
  have hCM : IsCMExt F E σ := hB.cm
  have hτσ : ∀ (τ : E →+* ℂ) (a : E), τ (σ a) = star (τ a) := hCM.2.2.2
  obtain ⟨θ, hθ⟩ := GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood σ B hB
  obtain ⟨x₀, hx₀, hxx₀⟩ := GlobalTheory.T.exists_isotropic_indefinite_skewHermitian_cm F E σ B hCM (n₁ + 2) Y.J r s hY.skew hY.sig hr hs (by omega)
  obtain ⟨y₀, ι, hxy₀, hyy₀, horth₀, hind₀, hsplit₀⟩ :=
    GlobalTheory.T.selfDualSkewHermitianLattice_splits_hyperbolicPlane F E σ hCM θ hθ n₁ Y.J Y.L hY.skew hY.lat hY.dual x₀ hx₀ hxx₀
  have hy₀ : y₀ ≠ 0 := by
    rintro rfl
    rw [show (0 : Fin (n₁ + 2) → E) = (0 : E) • x₀ by simp, form_smul_right, map_zero, zero_mul] at hxy₀
    exact zero_ne_one hxy₀
  obtain ⟨c, hc, hprim⟩ := GlobalTheory.T.exists_rescale_primitive_in_lattice_at_split_primes F E σ hCM (n₁ + 2) Y.L hY.lat x₀ y₀ hx₀ hy₀ B.P B.τ
  have hσc : σ c ≠ 0 := fun h => hc (by simpa [sigma_sigma hCM] using congrArg σ h)
  set x := c • x₀ with hxdef
  set y := (σ c)⁻¹ • y₀ with hydef
  have hxx : form σ Y.J x x = 0 := by rw [form_smul_left, form_smul_right, hxx₀, mul_zero, mul_zero]
  have hyy : form σ Y.J y y = 0 := by rw [form_smul_left, form_smul_right, hyy₀, mul_zero, mul_zero]
  have hxy : form σ Y.J x y = 1 := by
    rw [form_smul_left, form_smul_right, hxy₀, map_inv₀, sigma_sigma hCM, mul_one, mul_inv_cancel₀ hc]
  have horth : ∀ u, form σ Y.J (ι *ᵥ u) x = 0 ∧ form σ Y.J (ι *ᵥ u) y = 0 := fun u => by
    rw [form_smul_right, form_smul_right, (horth₀ u).1, (horth₀ u).2, mul_zero, mul_zero]; exact ⟨rfl, rfl⟩
  have hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ ι *ᵥ u ∈ Y.L ∧
      z = s • x + ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨s', t, u, h1, h2, h3, rfl⟩ := hsplit₀ z hz
    have e1 : (s' / c) • x = s' • x₀ := by rw [hxdef, smul_smul, div_mul_cancel₀ _ hc]
    have e2 : (t * σ c) • y = t • y₀ := by rw [hydef, smul_smul, mul_assoc, mul_inv_cancel₀ hσc, mul_one]
    exact ⟨s' / c, t * σ c, u, e1 ▸ h1, e2 ▸ h2, h3, by rw [e1, e2]⟩
  have hind : ∀ (s t : E) (u : Fin n₁ → E), s • x + ι *ᵥ u + t • y = 0 → s = 0 ∧ t = 0 ∧ u = 0 := by
    intro s' t u h
    rw [hxdef, hydef, smul_smul, smul_smul] at h
    obtain ⟨h1, h2, h3⟩ := hind₀ _ _ _ h
    exact ⟨(mul_eq_zero.1 h1).resolve_right hc, (mul_eq_zero.1 h2).resolve_right (inv_ne_zero hσc), h3⟩
  have hinjι : Function.Injective ι.mulVec := fun u u' h => by
    have := hind₀ 0 0 (u - u') (by simp [Matrix.mulVec_sub, h])
    exact sub_eq_zero.1 this.2.2
  obtain ⟨𝔟, h𝔟⟩ := GlobalTheory.T.exists_fractionalIdeal_mem_iff_smul_mem_lattice E (n₁ + 2) Y.L hY.lat x (smul_ne_zero hc hx₀)
  haveI hlat1 : (lowLat ι Y.L).IsLattice E := GlobalTheory.T.isLattice_sublatticePullbackAlongEmbedding E (n₁ + 2) n₁ Y.L ι hY.lat hinjι

  have hXX : ∀ w, (fun i => (B.emb w).1 (x i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (x i)) = 0 := fun w => by rw [form_map _ (hτσ _), hxx, map_zero, mul_zero]
  have hYY : ∀ w, (fun i => (B.emb w).1 (y i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = 0 := fun w => by rw [form_map _ (hτσ _), hyy, map_zero, mul_zero]
  have hXY : ∀ w, (fun i => (B.emb w).1 (x i)) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = Complex.I := fun w => by rw [form_map _ (hτσ _), hxy, map_one, mul_one]
  have hO : ∀ w (u : Fin n₁ → ℂ), (ι.map (B.emb w).1 *ᵥ u) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (x i)) = 0 ∧ (ι.map (B.emb w).1 *ᵥ u) ⬝ᵥ (Complex.I • Y.J.map (B.emb w).1) *ᵥ
      star (fun i => (B.emb w).1 (y i)) = 0 := fun w u =>
    ⟨orth_map _ (hτσ _) Y.J ι x (fun u => (horth u).1) u, orth_map _ (hτσ _) Y.J ι y (fun u => (horth u).2) u⟩
  have hsig1 : ∀ w, HasSig (Complex.I • (ιᵀ * Y.J * ι.map σ).map (B.emb w).1) (r - 1) (s - 1) := fun w => by
    rw [← gram_map _ (hτσ _)]
    exact GlobalTheory.T.hasHermitianSignature_hyperbolicPlane_orthComplement n₁ _ _ _ _ r s (hY.sig w) hr hs (hXX w) (hYY w) (by rw [hXY w]; exact Complex.I_ne_zero) (hO w)
      (inj_map _ ι hinjι)
  choose θ₁ hθ₁ using fun w => GlobalTheory.T.exists_cartanInvolution_hermitianSignature n₁ _ (r - 1) (s - 1) (hsig1 w)
  choose θW hθW using fun w => GlobalTheory.T.exists_cartanInvolution_hyperbolicSwap_extension n₁ (Complex.I • Y.J.map (B.emb w).1) _ _ (ι.map (B.emb w).1) (θ₁ w)
    (herm_map _ (hτσ _) hY.skew) (hXX w) (hYY w) (hXY w) (hO w) (inj_map _ ι hinjι)
    (by rw [gram_map _ (hτσ _)]; exact hθ₁ w)

  choose β₁ hβ₁ using fun v : B.P => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) (lowLat ι Y.L) hCM
  choose βY hβY using fun v : B.P => GlobalTheory.T.exists_splitPlace_localLatticeBasis_hyperbolicPlane F E σ hCM v.1 (B.τ v) n₁ Y.L x y ι (β₁ v) i₀ i₁ h01 h1n hsplit hind
    (hprim v).1 (hprim v).2 (hβ₁ v)
  let Y₁ : Spc F E n₁ :=
    { J := ιᵀ * Y.J * ι.map σ
      L := lowLat ι Y.L
      θ := θ₁
      bas := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else 1 }
  let Y' : Spc F E (n₁ + 2) :=
    { J := Y.J
      L := Y.L
      θ := θW
      bas := fun v => if h : v ∈ B.P then βY ⟨v, h⟩ else 1 }
  refine ⟨Y', Y₁, ⟨x, y, ι, 𝔟⟩, ?_, ?_, ?_⟩
  · exact
      { skew := hY.skew
        sig := hY.sig
        lat := hY.lat
        dual := hY.dual
        cartan := fun w => (hθW w).1
        bas := fun v => by
          show IsSplitBasis (B.τ v) Y.L (if h : v.1 ∈ B.P then βY ⟨v.1, h⟩ else 1)
          rw [dif_pos v.2]
          exact (hβY v).1 }
  · exact
      { skew := gram_skew hCM hY.skew ι
        sig := hsig1
        lat := hlat1
        dual := GlobalTheory.T.orthogonalComplement_hyperbolicPlane_lattice_selfDual F E σ n₁ Y.J Y.L x y ι hY.dual horth hsplit
        cartan := hθ₁
        bas := fun v => by
          show IsSplitBasis (B.τ v) (lowLat ι Y.L) (if h : v.1 ∈ B.P then β₁ ⟨v.1, h⟩ else 1)
          rw [dif_pos v.2]
          exact hβ₁ v }
  · exact
      { rank := rfl
        xx := hxx
        yy := hyy
        xy := hxy
        orth := horth
        gram := rfl
        low := fun u => Iff.rfl
        split := hsplit
        ideal := h𝔟
        cartan := fun w => ⟨(hθW w).2.1, (hθW w).2.2⟩
        bas := fun v i => by
          have e1 : (GlobalTheory.ThK.reS Y Y').bas v = βY v := dif_pos v.2
          have e2 : Y₁.bas v = β₁ v := dif_pos v.2
          rw [e1, e2]
          exact (hβY v).2 i }

end GlobalTheory.PlaneSkew
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewIdealLatticePointRationalNormKills
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.SkewPoints

theorem absNorm_galois_smul {E : Type} [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (B : Ideal (𝓞 E)) :
    Ideal.absNorm (c • B) = Ideal.absNorm B := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv B (c • B) (MulSemiringAction.toRingEquiv _ _ c) rfl).toEquiv).symm

theorem points : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ}, ∀ y ∈ (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), ∃ z : Matrix (Fin d) (Fin a) D.host.E, y = pt D (tor0 D ⊤ δ) δ z ∧ Ideal.absNorm 𝔪 • pt D (tor0 D ⊤ δ) δ z ∈ (La0 D (tor0 D ⊤ δ) a d) := by
  intro D δ _ 𝔪 h𝔪 a d y hy
  have hrange : La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ≤ (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d).range := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, -, rfl⟩
    obtain ⟨c, -, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
    exact ⟨((c : D.host.K) : D.host.E) • A, GlobalTheory.ThetaLatticePoints.ptHom_smul D ⊤ δ a d c A⟩
  obtain ⟨z, hz⟩ := hrange hy
  rw [GlobalTheory.ThetaLatticePoints.ptHom_apply] at hz
  refine ⟨z, hz.symm, ?_⟩
  rw [hz, ← absNorm_galois_smul (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E) 𝔪]
  exact GlobalTheory.FunObj.CosetTheta.absNormConj_smul_mem_stdThetaLattice h𝔪 hy

end GlobalTheory.FunObj.StdDatum.SkewPoints

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryLiftTendstoOneStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_unitary_lift_tendsto_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F} {n : ℕ} (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (J : Matrix (Fin n) (Fin n) E) (ε : F) (herm : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (hJ : IsUnit (J.map τ).det), Tendsto (GlobalTheory.SplitUnitLift.liftU h τ J ε herm hJ) (𝓝 1) (𝓝 1) := by
  first | exact @GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one | exact GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one | (intros; apply GlobalTheory.SplitUnitLiftCont.tendsto_liftU_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterTrivialImpliesIntegralTraceStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_character_trivial_implies_integral_trace : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ x : F, (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ 1) → ψ (algebraMap F (AF F) x * t) = 1) → ∃ z : ℤ, Algebra.trace ℚ F x = z := by
  first | exact @GlobalTheory.TraceIntStd.trace_int_of_isStd | exact GlobalTheory.TraceIntStd.trace_int_of_isStd | (intros; apply GlobalTheory.TraceIntStd.trace_int_of_isStd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAdelicAddCharApplyEqAdelicCharStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct FourierTransform
open MeasureTheory GroundTheory.Automorphic.GJMatrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardTraceAdelicAddChar_apply_eq_adelicChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ x : AF F, ψ x = (GroundTheory.Global.adelicChar F x : ℂ) := by
  first | exact @GlobalTheory.StdCharEq.eq_adelicChar | exact GlobalTheory.StdCharEq.eq_adelicChar | (intros; apply GlobalTheory.StdCharEq.eq_adelicChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementaryStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_group_generated_by_elementary : ∀ (K : Type) [Field K] [CharZero K] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix (κ ⊕ κ) (κ ⊕ κ) K),
    GlobalTheory.SympChange.IsSymp G → G ∈ Submonoid.closure (GlobalTheory.SympChange.gens (F := K) (κ := κ)) := by
  first | exact @GlobalTheory.SympChangeGen.mem_closure_gens | exact GlobalTheory.SympChangeGen.mem_closure_gens | (intros; apply GlobalTheory.SympChangeGen.mem_closure_gens <;> assumption)
end

