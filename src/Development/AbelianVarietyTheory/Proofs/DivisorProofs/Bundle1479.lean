import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntegralHermitianCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open Formalism.UG (cT)

namespace GlobalTheory.EisCT

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def StabL (x : Matrix (Fin n) (Fin 1) E) (g : GAd σ J) : Prop :=
  ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J g).1 * adMat F x = l.1 • adMat F x

def IsTransv (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Prop :=
  ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ StabL σ J x (γ * t⁻¹ : ratPts σ J).1

def OrthL (x : Matrix (Fin n) (Fin 1) E) (g : GAd σ J) : Prop :=
  adMat F (cT (σ : E →+* E) x * J) * (matHom _ σ J g⁻¹).1 * adMat F x = 0

def lineSet (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Set (ratPts σ J) :=
  {t | t ∈ T ∧ StabL σ J x t.1}

def midSet (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Set (ratPts σ J) :=
  {t | t ∈ T ∧ ¬ StabL σ J x t.1 ∧ OrthL σ J x t.1}

def bigSet (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) : Set (ratPts σ J) :=
  {t | t ∈ T ∧ ¬ OrthL σ J x t.1}

def fs (h : GAd σ J → ℝ) (s : ℂ) (g : GAd σ J) : ℂ := (h g : ℂ) ^ (s + ((n : ℂ) - 1) / 2)

def lineSum (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) (h : GAd σ J → ℝ) (s : ℂ) (g : GAd σ J) : ℂ :=
  ∑' t : lineSet σ J x T, fs σ J h s (t.1.1 * g)

def midSum (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) (h : GAd σ J → ℝ) (s : ℂ) (g : GAd σ J) : ℂ :=
  ∑' t : midSet σ J x T, fs σ J h s (t.1.1 * g)

def bigSum (x : Matrix (Fin n) (Fin 1) E) (T : Set (ratPts σ J)) (h : GAd σ J → ℝ) (s : ℂ) (g : GAd σ J) : ℂ :=
  ∑' t : bigSet σ J x T, fs σ J h s (t.1.1 * g)

end GlobalTheory.EisCT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IndLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d d₁ : ℕ} {Y : Spc F E n} {W : Spc F E d}

def PGen (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (V : Submodule ℂ P) : Prop :=
  ∀ N : Submodule ℂ P, V ≤ N →
    (∀ γ ∈ Lines σ W, (∀ s, γ s ∈ unip σ W H') → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    (∀ γ ∈ Lines σ W, (∃ (t : Multiplicative ℝ →* (AE F E)ˣ) (γ₁ : Multiplicative ℝ →* UA σ W₁.J), γ₁ ∈ Lines σ W₁ ∧
        ∀ s, IsLevi H' (t s) (γ₁ s) (γ s)) → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ N → p f₁ ∈ N) →
    N = ⊤

def KStab (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (V : Submodule ℂ P) : Prop :=
  (∀ k ∈ KInf σ W B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, k)) f f₁ → p f ∈ V → p f₁ ∈ V) ∧
    ∀ γ ∈ Lines σ W, (∀ s, γ s ∈ KInf σ W B.emb) → ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : SInf F (Fin n × Fin d),
      ActsD (evI F) (fun s => om (1, γ (Multiplicative.ofAdd s))) f f₁ → p f ∈ V → p f₁ ∈ V

end GlobalTheory.IndLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaProductPowAlgebraicModulusOneAllStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappaProduct_pow_algebraicModulusOneAll : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (m : ℕ), StandardLatticesGL3.Mod1All (B.kappa ^ m) := by
  first | exact @GlobalTheory.KappaPowMod.kappa_pow_mod1All | exact GlobalTheory.KappaPowMod.kappa_pow_mod1All | (intros; apply GlobalTheory.KappaPowMod.kappa_pow_mod1All <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianDimensionBound
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory

theorem finrank_le_card_of_isotropic_prod_pi (F : Type) [Field F] (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F)))
    (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) :
    Module.finrank F L ≤ Fintype.card κ := by
  classical
  let ω : ((κ → F) × (κ → F)) →ₗ[F] Module.Dual F ((κ → F) × (κ → F)) :=
    LinearMap.mk₂ F (fun b a => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)
      (by intro b b' a; simp [dotProduct_add, add_dotProduct]; ring)
      (by intro c b a; simp [dotProduct_smul, smul_dotProduct]; ring)
      (by intro b a a'; simp [dotProduct_add, add_dotProduct]; ring)
      (by intro c b a; simp [dotProduct_smul, smul_dotProduct]; ring)
  have hω : ∀ b a, ω b a = a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 := fun b a => rfl
  have hinj : Function.Injective ω := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have h1 : ∀ i, b.2 i = 0 := by
      intro i
      have := congrArg (fun f => f (Pi.single i 1, 0)) hb
      simpa [hω, single_dotProduct] using this
    have h2 : ∀ i, b.1 i = 0 := by
      intro i
      have := congrArg (fun f => f (0, Pi.single i 1)) hb
      simpa [hω, dotProduct_single] using this
    exact Prod.ext (funext h2) (funext h1)
  let g : L →ₗ[F] L.dualAnnihilator :=
    ((ω.domRestrict L).codRestrict L.dualAnnihilator (by
      intro b
      rw [Submodule.mem_dualAnnihilator]
      intro a ha
      simp only [LinearMap.domRestrict_apply, hω]
      rw [hL a ha b b.2, sub_self]))
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hinj
    have := congrArg Subtype.val hxy
    simpa [g] using this
  have h1 := LinearMap.finrank_le_finrank_of_injective hg
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq L
  have h3 : Module.finrank F ((κ → F) × (κ → F)) = 2 * Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]; ring
  omega

end GlobalTheory

example : ∀ (F : Type) [Field F] (κ : Type) [Fintype κ] (L : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L ≤ Fintype.card κ :=
  GlobalTheory.finrank_le_card_of_isotropic_prod_pi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeApproximationUpwardIdele
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.SiegelSet

theorem isRealLine_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : ℝ → GAd σ J), IsRealLine σ J γ →
      ∀ s t, γ (s + t) = γ s * γ t := by
  intro F E _ _ _ _ _ σ hCM n J γ hγ s t
  obtain ⟨w, τ, Z, -, hγ⟩ := hγ
  obtain ⟨y1, e1, f1⟩ := hγ (s + t)
  obtain ⟨y2, e2, f2⟩ := hγ s
  obtain ⟨y3, e3, f3⟩ := hγ t
  rw [e1, e2, e3, ← map_mul]
  congr 1
  apply (archEquiv J hCM τ).injective
  apply Subtype.ext
  apply Units.ext
  rw [← GlobalTheory.Orb.archMat_eq_archEquiv, ← GlobalTheory.Orb.archMat_eq_archEquiv, map_mul, f1, f2, f3, add_smul]
  exact Matrix.exp_add_of_commute _ _ ((Commute.refl Z).smul_left s |>.smul_right t)

end GlobalTheory.SiegelSet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCountSumBoundOfRationalDiagonalisingStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCount_sum_bound_of_rational_diagonalising : ∀ (D : D7) (κ : Type) [Fintype κ] [DecidableEq κ] (m n : ℕ) (T : Matrix κ (Fin m) D.host.E) (S : Matrix (Fin m) κ D.host.E), S * T = 1 → ∀ L : ℕ, 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (s : κ → ℝ), (∀ k, 0 < s k) → ∀ B : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ τ, T.map (tauE D τ) * B τ = Matrix.diagonal (fun k => ((s k : ℝ) : ℂ)⁻¹) * T.map (tauE D τ)) → ∑' ξ : Matrix (Fin m) (Fin n) D.host.E, {ξ : Matrix (Fin m) (Fin n) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator (fun ξ => ENNReal.ofReal (((1 + ∑ τ, ∑ i, ∑ j, ‖(B τ * ξ.map (tauE D τ)) i j‖) ^ N)⁻¹)) ξ ≤ ENNReal.ofReal (C * ∏ k, max 1 (s k) ^ (Module.finrank ℚ D.host.F * (2 * n))) := by
  first | exact @GlobalTheory.lattice_count_diag_mul | exact GlobalTheory.lattice_count_diag_mul | (intros; apply GlobalTheory.lattice_count_diag_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeGeHeightPolynomialVectorsDetStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_degree_ge_height_polynomialVectors_det : ∀ (F V : Type) [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (nm : HermFam F V) (M : Submodule (𝓞 F) V) (d : ℕ) (b : Module.Basis (Fin d) F V), IsFull M → ∀ (B N n : ℕ) (w : Matrix (Fin N) (Fin n) F) (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (Λ : ℝ), Lat w A Λ → ∀ (P : Matrix (Fin d) (Fin d) (MvPolynomial (Fin B × Fin N) F)) (a : Fin B → ℕ) (Bd : Fin d → ℝ), P.det ≠ 0 → IsMultiHomogeneous a P.det → (∀ k, 0 < Bd k) → (∀ k m, ∑ i, coeff m (linSubst w (P i k)) • b i ∈ M) → (∀ k σ (u : Fin B × Fin N → ℂ), (∀ i, frameNorm (A σ) (fun j => u (i, j)) = 1) → cnrm nm σ (fun i => eval₂ σ u (P i k)) b ≤ Bd k) → ht w A P.det - ∑ k, Real.log (Bd k) ≤ deg nm M := by
  first | exact @GlobalTheory.HSShort.deg_ge_ht_det | exact GlobalTheory.HSShort.deg_ge_ht_det | (intros; apply GlobalTheory.HSShort.deg_ge_ht_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntegralHermitianCompletionStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_integral_hermitian_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) → (∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)) → ∀ L : Submodule K.O B.A, GlobalTheory.UnitLemma.IsLat K.O K.E L → (∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) → ∃ g ∈ UL n w, pullLat w B ψ g = L := by
  first | exact @GlobalTheory.KapOrb.SelfDualPull.exists_unitary_pullLat_eq | exact GlobalTheory.KapOrb.SelfDualPull.exists_unitary_pullLat_eq | (intros; apply GlobalTheory.KapOrb.SelfDualPull.exists_unitary_pullLat_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelsStandardFramesConjugateStandardGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levels_standardFrames_conjugate_standardGroup : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → ∀ (i : Fin D.R.m) {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : principalLevelFrame.RowPsi (Wc D i) n), StdPsi hF PY → StdPsi hF PW → ∀ P : LevelP R.Pg D.R.r ℂ, ∃ h : Formalism.AUTREP.GAf D.host.E n, ∀ κ, PW.ψ κ ∈ levS _ (R.βW i) (R.datWp i P) → PY.ψ (h⁻¹ * κ * h) ∈ levS _ (R.βY 0) (R.dat0 P) ∧ levChi _ (R.βW i) (R.datWp i P) (PW.ψ κ) = levChi _ (R.βY 0) (R.dat0 P) (PY.ψ (h⁻¹ * κ * h)) := by
  first | exact @GlobalTheory.FrameMove.frame_move | exact GlobalTheory.FrameMove.frame_move | (intros; apply GlobalTheory.FrameMove.frame_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUnique
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin

noncomputable section

namespace GlobalTheory.LeviUniq

theorem levi_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (t : (AE F E)ˣ) (m m' : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 m → IsLevi (W₁ := W₁) H' t 1 m' → m = m' := by
  intro F E _ _ _ _ _ σ B d r s W hW d₁ W₁ H' i₀ i₁ hH t m m' hm hm'

  let S : Submodule E (Fin d → E) :=
    { carrier := {e | mat m *ᵥ incV F e = mat m' *ᵥ incV F e}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        have : incV F (a + b) = incV F a + incV F b := by
          funext i; simp [incV, map_add]
        rw [this, Matrix.mulVec_add, Matrix.mulVec_add, ha, hb]
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        have : incV F (0 : Fin d → E) = 0 := by funext i; simp [incV]
        rw [this, Matrix.mulVec_zero, Matrix.mulVec_zero]
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at *
        have : incV F (c • a) = inclR (F := F) (AF F) c • incV F a := by
          funext i; simp [incV, map_mul]
        rw [this, Matrix.mulVec_smul, Matrix.mulVec_smul, ha] }
  have hone : mat (1 : UA σ W₁.J) = 1 := rfl
  have hι : ∀ (g : UA σ W.J), IsLevi (W₁ := W₁) H' t 1 g → ∀ u : Fin d₁ → E,
      mat g *ᵥ incV F (H'.ι *ᵥ u) = incV F (H'.ι *ᵥ u) := by
    intro g hg u
    have hv : incV F (H'.ι *ᵥ u) = incM F H'.ι *ᵥ incV F u := by
      funext i; simp [incV, incM, Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [hv, Matrix.mulVec_mulVec, hg.2.2, hone, Matrix.mul_one]
  have hx : H'.x ∈ S := by
    show mat m *ᵥ incV F H'.x = mat m' *ᵥ incV F H'.x
    rw [hm.1, hm'.1]
  have hy : H'.y ∈ S := by
    show mat m *ᵥ incV F H'.y = mat m' *ᵥ incV F H'.y
    rw [hm.2.1, hm'.2.1]
  have hιS : ∀ u, H'.ι *ᵥ u ∈ S := by
    intro u
    show mat m *ᵥ incV F (H'.ι *ᵥ u) = mat m' *ᵥ incV F (H'.ι *ᵥ u)
    rw [hι m hm, hι m' hm']
  have hL : ∀ z ∈ W.L, z ∈ S := by
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hH.split z hz
    exact S.add_mem (S.add_mem (S.smul_mem a hx) (hιS u)) (S.smul_mem b hy)
  have htop : S = ⊤ := by
    have h1 : Submodule.span E (W.L : Set (Fin d → E)) ≤ S := Submodule.span_le.2 hL
    rw [hW.lat.span_eq_top] at h1
    exact top_le_iff.1 h1
  have hall : ∀ e, mat m *ᵥ incV F e = mat m' *ᵥ incV F e := fun e => by
    have : e ∈ S := htop ▸ Submodule.mem_top
    exact this
  have hmat : mat m = mat m' := by
    ext i j
    have h := congrFun (hall (Pi.single j 1)) i
    have hs : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
      funext k; by_cases hk : k = j
      · subst hk; simp [incV]
      · simp [incV, Pi.single_apply, hk]
    rw [hs, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    simpa using h
  exact Subtype.ext (Units.ext hmat)

end GlobalTheory.LeviUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviIsoPlaneUnique
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviUniqueCartan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n' : ℕ}

theorem det_ne_zero_of_isCartan {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (e : E →+* ℂ) (θ : Matrix (Fin n) (Fin n) ℂ)
    (h : IsCartan (Complex.I • J.map e) θ) : J.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hx : star (fun i => e (v i)) ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 i
    simpa using this
  have hpos := h.2.2 _ hx
  have hz : (Complex.I • J.map e) *ᵥ star (star (fun i => e (v i))) = 0 := by
    rw [star_star, Matrix.smul_mulVec]
    have : J.map e *ᵥ (fun i => e (v i)) = 0 := by
      funext i
      have := RingHom.map_mulVec e J v i
      rw [hJv] at this
      simpa [Function.comp_def] using this.symm
    rw [this, smul_zero]
  rw [hz] at hpos
  simp at hpos

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : σ (form σ J a b) = -form σ J b a := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem incV_add (a b : Fin n' → E) : incV F (a + b) = incV F a + incV F b := by
  funext i; simp [incV]

theorem incV_smul (s : E) (a : Fin n' → E) : incV F (s • a) = inclR (F := F) (AF F) s • incV F a := by
  funext i; simp [incV]

theorem incV_mulVec {k : ℕ} (M : Matrix (Fin n') (Fin k) E) (u : Fin k → E) :
    incV F (M *ᵥ u) = incM F M *ᵥ incV F u := by
  funext i
  exact RingHom.map_mulVec (inclR (F := F) (AF F)) M u i

theorem incV_single (j : Fin n') : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [incV]
  · simp [incV, Pi.single_apply, hk]

theorem levi_unique {σ : E →ₐ[F] E} (B : Base F E) {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁)
    (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (Y.J j i) = -Y.J i j) (hP : IsIsoPlane σ B H Y Y₁)
    (t : (AE F E)ˣ) (h₁ : UA σ Y₁.J) (m m' : UA σ Y.J)
    (hm : IsLevi (W₁ := Y₁) H t h₁ m) (hm' : IsLevi (W₁ := Y₁) H t h₁ m') : m = m' := by
  obtain ⟨hn, hxx, hyy, hxy, horth, hgram, -, hcart⟩ := hP
  subst hn
  have hadd : ∀ a b c, form σ Y.J (a + b) c = form σ Y.J a c + form σ Y.J b c := fun a b c => by
    simp [form, add_dotProduct]
  have hsmul : ∀ (s : E) a c, form σ Y.J (s • a) c = s * form σ Y.J a c := fun s a c => by
    simp [form, smul_dotProduct]
  have hzero : ∀ c, form σ Y.J 0 c = 0 := fun c => by simp [form]
  have hyx : form σ Y.J H.y H.x = -1 := by
    have := form_swap σ hσ Y.J hJ H.x H.y
    rw [hxy, map_one] at this
    linear_combination this
  have hdet : Y₁.J.det ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact det_ne_zero_of_isCartan _ _ _ (hcart w)
  let Φ : E × (Fin n₁ → E) × E →ₗ[E] (Fin (n₁ + 2) → E) :=
    (LinearMap.smulRight LinearMap.id H.x).comp (LinearMap.fst E E ((Fin n₁ → E) × E)) +
    (Matrix.mulVecLin H.ι).comp ((LinearMap.fst E (Fin n₁ → E) E).comp (LinearMap.snd E E ((Fin n₁ → E) × E))) +
    (LinearMap.smulRight LinearMap.id H.y).comp ((LinearMap.snd E (Fin n₁ → E) E).comp (LinearMap.snd E E ((Fin n₁ → E) × E)))
  have hΦ : ∀ s u r, Φ (s, u, r) = s • H.x + H.ι *ᵥ u + r • H.y := fun s u r => by
    simp [Φ]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, u, r⟩ h
    rw [hΦ] at h
    have e1 := congrArg (fun z => form σ Y.J z H.y) h
    simp only [hadd, hsmul, hxy, hyy, (horth u).2, hzero] at e1
    have hs : s = 0 := by simpa using e1
    subst hs
    have e2 := congrArg (fun z => form σ Y.J z H.x) h
    simp only [hadd, hsmul, hxx, hyx, (horth u).1, hzero] at e2
    have hr : r = 0 := by simpa using e2
    subst hr
    have hu0 : H.ι *ᵥ u = 0 := by simpa using h
    have hu : u ᵥ* Y₁.J = 0 := by
      rw [← hgram, Matrix.mul_assoc, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hu0, Matrix.zero_vecMul]
    have : u = 0 := by
      by_contra hne
      exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨u, hne, hu⟩)
    subst this
    rfl
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp; omega)).mp hinj
  have key : ∀ z, mat m *ᵥ incV F z = mat m' *ᵥ incV F z := by
    intro z
    obtain ⟨⟨s, u, r⟩, rfl⟩ := hsurj z
    rw [hΦ, incV_add, incV_add, incV_smul, incV_smul, incV_mulVec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hm.1, hm.2.1, hm.2.2, hm'.1, hm'.2.1, hm'.2.2]
  have hmat : mat m = mat m' := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    rw [incV_single, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
    simpa using this
  exact Subtype.ext (Units.ext hmat)

end GlobalTheory.LeviUniqueCartan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSectionEtaleOfSquarefreeChowFormStatement
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSection_etale_of_squarefree_chowForm : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → ∀ (δ : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), IsChowForm T.imageIdeal T.D δ f → (δ : ℤ) = T.del → ∀ (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E), ((T.linSection E s).support : Set (T.toLinSys.baseChange E).Y).Finite → T.InOpen E (T.linSection E s) → NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) → SimpleAt T δ f E s := by
  first | exact @GlobalTheory.HSShort.EtaleSection.simpleAt_of_noSquare | exact GlobalTheory.HSShort.EtaleSection.simpleAt_of_noSquare | (intros; apply GlobalTheory.HSShort.EtaleSection.simpleAt_of_noSquare <;> assumption)
end

