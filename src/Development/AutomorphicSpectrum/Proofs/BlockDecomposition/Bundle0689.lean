import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0272
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1348
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1520
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0654
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0062
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0678
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InversePointTorusScaling
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.TorusCoord

variable {K : Type} [CommRing K] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) K} {Rx Ry : Matrix (Fin r) (Fin n) K}

theorem left_proj (h1 : Rx * X = 0) (h3 : Rx * Y = 1) : Rx * (1 - X * Ry - Y * Rx) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h1, h3, Matrix.zero_mul, Matrix.one_mul, sub_zero,
    sub_self]

theorem left_proj' (h2 : Ry * Y = 0) (h4 : Ry * X = 1) : Ry * (1 - X * Ry - Y * Rx) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h2, h4, Matrix.zero_mul, Matrix.one_mul, sub_zero,
    sub_self]

theorem lin (h1 : Rx * X = 0) (h2 : Ry * Y = 0) (h3 : Rx * Y = 1) (h4 : Ry * X = 1)
    {A B : Matrix (Fin n) (Fin n) K} (hAB : A * B = 1) {T S : Matrix (Fin r) (Fin r) K} (hTS : T * S = 1)
    (hST : S * T = 1) (hX : B * X = X * T) (hY : B * Y = Y * S) (ξ : Matrix (Fin n) (Fin 1) K)
    (hq : B * ((1 - X * Ry - Y * Rx) * ξ) = (1 - X * Ry - Y * Rx) * ξ) :
    Ry * (A * ξ) = S * (Ry * ξ) ∧ Rx * (A * ξ) = T * (Rx * ξ) ∧
      (1 - X * Ry - Y * Rx) * (A * ξ) = (1 - X * Ry - Y * Rx) * ξ := by
  have hRxQ := left_proj (Ry := Ry) h1 h3
  have hRyQ := left_proj' (Rx := Rx) h2 h4
  have e : ∀ {m : ℕ} (M : Matrix (Fin n) (Fin m) K),
      (1 - X * Ry - Y * Rx) * M = M - X * (Ry * M) - Y * (Rx * M) := fun M => by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  generalize hQ : 1 - X * Ry - Y * Rx = Q at hq hRxQ hRyQ ⊢
  have eQ : ∀ {m : ℕ} (M : Matrix (Fin n) (Fin m) K), Q * M = M - X * (Ry * M) - Y * (Rx * M) := fun M => by
    rw [← hQ]; exact e M
  have hAX : A * X = X * S := by
    have h : A * (B * X) = X := by rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
    rw [hX, ← Matrix.mul_assoc] at h
    calc A * X = A * X * (T * S) := by rw [hTS, Matrix.mul_one]
      _ = (A * X * T) * S := by simp only [Matrix.mul_assoc]
      _ = X * S := by rw [h]
  have hAY : A * Y = Y * T := by
    have h : A * (B * Y) = Y := by rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
    rw [hY, ← Matrix.mul_assoc] at h
    calc A * Y = A * Y * (S * T) := by rw [hST, Matrix.mul_one]
      _ = (A * Y * S) * T := by simp only [Matrix.mul_assoc]
      _ = Y * T := by rw [h]
  have hAQ : A * (Q * ξ) = Q * ξ := by
    conv_lhs => rw [← hq]
    rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
  have hQX : Q * X = 0 := by rw [eQ, h1, h4]; simp
  have hQY : Q * Y = 0 := by rw [eQ, h2, h3]; simp
  have hQQ : Q * Q = Q := by rw [eQ, hRxQ, hRyQ]; simp
  have hdec : ξ = X * (Ry * ξ) + Y * (Rx * ξ) + Q * ξ := by rw [eQ]; abel
  have hu : A * ξ = X * (S * (Ry * ξ)) + Y * (T * (Rx * ξ)) + Q * ξ := by
    conv_lhs => rw [hdec]
    rw [Matrix.mul_add, Matrix.mul_add, hAQ, ← Matrix.mul_assoc A X, ← Matrix.mul_assoc A Y, hAX, hAY,
      Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hu]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Ry X, ← Matrix.mul_assoc Ry Y, ← Matrix.mul_assoc Ry Q, h4, h2,
      hRyQ]
    simp
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Rx X, ← Matrix.mul_assoc Rx Y, ← Matrix.mul_assoc Rx Q, h3, h1,
      hRxQ]
    simp
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Q X, ← Matrix.mul_assoc Q Y, ← Matrix.mul_assoc Q Q, hQX, hQY,
      hQQ]
    simp

theorem mt_inv_mul {D : D7} (V : HSp D) (a : GA D V) : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
  have h := congrArg Units.val (map_mul (Formalism.L2.Theta.matHom V) a⁻¹ a)
  rw [inv_mul_cancel, map_one] at h
  exact h.symm

theorem map_mt_eq_archMat {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (ρ : D.what₂.Tau) (a : GA D V) :
    (Formalism.L2.Theta.mt V a).map (fun x => θ ρ (infPart D x)) =
      GlobalTheory.Orb.archMat D.sp.cm.sig V.gram (embOverOf D ρ) (projArch D.sp.cm.sig V.gram (placeOf D ρ) a) := by
  have e := eq_infProj hθ (embOverOf D ρ) rfl
  have h := infMat_infProj (J := V.gram) (isCMExt_host D) (embOverOf D ρ) a
  rw [← e] at h
  refine Eq.trans ?_ (h.trans (GlobalTheory.Orb.archMat_eq_archEquiv V.gram (isCMExt_host D) _ _).symm)
  ext i j
  rfl

theorem torus_coords : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ (ξ : Matrix (Fin V.rank) (Fin 1) D.host.E), (invPt V a ξ).map (finPart D) = ξ.map (fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) ∧ ∀ ρ, (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => ((t i : ℂ))⁻¹) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ξ).map (tauE D ρ)) ∧ (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => (t i : ℂ)) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ξ).map (tauE D ρ)) ∧ (((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ).map (tauE D ρ)) := by
  intro D θ hθ V r Xf Yf hW t ht a ha ξ
  have hcm := isCMExt_host D
  have hJ := isHermND_gram V
  refine ⟨?_, fun ρ => ?_⟩
  · have h1 : (Formalism.L2.Theta.mt V a⁻¹).map (finPart D) = 1 :=
      GlobalTheory.CompanionTheory.SiegelArch.map_matHom_fin V.gram (inv_mem ha.1)
    change (HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D))).map (finPart D) = _
    rw [Matrix.map_mul, h1, Matrix.one_mul, Matrix.map_map]
    ext i j
    exact GlobalTheory.LatVac.finPart_incA _
  · have hhτ : ∀ x, θ ρ (infPart D (incA D x)) = tauE D ρ x := fun x => (hθ ρ).1 x
    let φ : AE D →+* ℂ := (θ ρ).comp (infPart D)
    have hAB : (Formalism.L2.Theta.mt V a⁻¹).map φ * (Formalism.L2.Theta.mt V a).map φ = 1 := by
      rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have hB : (Formalism.L2.Theta.mt V a).map φ = _ := map_mt_eq_archMat hθ V ρ a
    have hcomp : compAt θ ρ (invPt V a ξ) = (Formalism.L2.Theta.mt V a⁻¹).map φ * ξ.map (tauE D ρ) := by
      change (HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D))).map φ = _
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hhτ _
    obtain ⟨hX, hY, hZ⟩ := ha.2 (placeOf D ρ) (embOverOf D ρ)
    rw [← hB] at hX hY hZ
    simp only [embOverOf_val] at hX hY hZ
    obtain ⟨-, -, hxy⟩ := GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)
    have hxx := (GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)).1
    have hyy := (GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)).2.1
    have hJc : (V.gram.map (tauE D ρ))ᴴ = V.gram.map (tauE D ρ) := by
      ext i j
      rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hJ.1]
    have hyx := GlobalTheory.CentreFin.dual_swap hJc hxy
    have hR : ∀ C : Matrix (Fin V.rank) (Fin r) D.host.E,
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (tauE D ρ) =
          (C.map (tauE D ρ))ᴴ * V.gram.map (tauE D ρ) := fun C => by
      rw [Matrix.map_mul, GlobalTheory.CentreFin.map_cT_emb hcm]
    have h1 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * Xf.map (tauE D ρ) = 0 := by
      rw [hR]; exact hxx
    have h2 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * Yf.map (tauE D ρ) = 0 := by
      rw [hR]; exact hyy
    have h3 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * Yf.map (tauE D ρ) = 1 := by
      rw [hR]; exact hxy
    have h4 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * Xf.map (tauE D ρ) = 1 := by
      rw [hR]; exact hyx
    have h4E : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * Xf = 1 := by
      refine Matrix.map_injective (tauE D ρ).injective ?_
      beta_reduce
      rw [Matrix.map_mul, h4, Matrix.map_one _ (map_zero _) (map_one _)]
    have hQm : (1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ) =
        1 - Xf.map (tauE D ρ) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ) -
          Yf.map (tauE D ρ) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ) := by
      change (tauE D ρ).mapMatrix _ = _
      rw [map_sub, map_sub, map_one]
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul]
    have hxq := left_proj (X := Xf) (Y := Yf) (Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)
      (Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) hW.xx hW.xy
    have hyq := left_proj' (X := Xf) (Y := Yf) (Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)
      (Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) hW.yy h4E
    have hq := hZ (fun i => ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ :
            Matrix (Fin V.rank) (Fin 1) D.host.E) i 0)
      (by
        funext i
        have e : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ) = 0 := by
          rw [← Matrix.mul_assoc, hxq, Matrix.zero_mul]
        exact congrFun (congrFun e i) 0)
      (by
        funext i
        have e : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ) = 0 := by
          rw [← Matrix.mul_assoc, hyq, Matrix.zero_mul]
        exact congrFun (congrFun e i) 0)
    have hq' := by
      refine lin h1 h2 h3 h4 hAB (T := diagonal fun i => (t i : ℂ)) (S := diagonal fun i => (t i : ℂ)⁻¹) ?_ ?_ hX hY
        (ξ.map (tauE D ρ)) ?_
      · rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        exact mul_inv_cancel₀ (by exact_mod_cast (ht i).ne')
      · rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        exact inv_mul_cancel₀ (by exact_mod_cast (ht i).ne')
      · rw [← hQm, ← Matrix.map_mul]
        ext i j
        obtain rfl : j = 0 := Subsingleton.elim _ _
        exact congrFun hq i
    obtain ⟨c1, c2, c3⟩ := hq'
    have m : ∀ {a : ℕ} (M : Matrix (Fin a) (Fin V.rank) D.host.E),
        (M * ξ).map (tauE D ρ) = M.map (tauE D ρ) * ξ.map (tauE D ρ) := fun M => Matrix.map_mul
    rw [hcomp, m, m, m, hQm]
    exact ⟨c1, c2, c3⟩

end GlobalTheory.CompanionTheory.TorusCoord
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdmissibleDegenerate
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DegenSeries

theorem isAdmissible_degenerate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ →
    IsAdmissible (parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) := by
  intro k _ _ _ _ a b χ₁ χ₂ _ _
  exact GlobalTheory.SmGL.ParIndAdm.isAdmissible_parInd _ _

end GlobalTheory.CompanionTheory.DegenSeries
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CtS

def IsInt {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {r s : Type}
    (M : Matrix r s (w.adicCompletion E)) : Prop :=
  ∀ i j, M i j ∈ Ov E w

def coef (q : ℕ) (c : ℂˣ) (a b i j : ℕ) : ℂ :=
  (c : ℂ) ^ (i * b + j * a) * (q : ℂ) ^ (((i : ℂ) * b + (j : ℂ) * a) / 2 - (i : ℂ) * j)

def pairs (a b k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.HasAntidiagonal.antidiagonal k).filter fun p => p.1 ≤ a ∧ p.2 ≤ b

theorem mem_pairs {a b k : ℕ} {p : ℕ × ℕ} : p ∈ pairs a b k ↔ p.1 + p.2 = k ∧ p.1 ≤ a ∧ p.2 ≤ b := by
  simp [pairs, Finset.mem_filter]

theorem IsInt.add {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s : Type}
    {M N : Matrix r s (w.adicCompletion E)} (hM : IsInt w M) (hN : IsInt w N) : IsInt w (M + N) :=
  fun i j => (Ov E w).add_mem (hM i j) (hN i j)

theorem IsInt.neg {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {r s : Type}
    {M : Matrix r s (w.adicCompletion E)} (hM : IsInt w M) : IsInt w (-M) :=
  fun i j => (Ov E w).neg_mem (hM i j)

theorem isInt_zero {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r s : Type) :
    IsInt w (0 : Matrix r s (w.adicCompletion E)) :=
  fun _ _ => (Ov E w).zero_mem

def intSub {E : Type} [Field E] [NumberField E] (a b : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | IsInt w X}
  zero_mem' := isInt_zero w _ _
  add_mem' := fun h h' => h.add h'
  neg_mem' := fun h => h.neg

def latM {E : Type} [Field E] [NumberField E] {a b : ℕ} {w : HeightOneSpectrum (𝓞 E)} (ϖ : w.adicCompletion E)
    (m : GL (Fin a) (w.adicCompletion E) × GL (Fin b) (w.adicCompletion E)) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {X | IsInt w (m.1.val * X) ∧ IsInt w (ϖ • (X * (m.2⁻¹).val))}
  zero_mem' := by
    refine ⟨?_, ?_⟩ <;> simpa using isInt_zero w _ _
  add_mem' := by
    rintro X Y ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_add]; exact h1.add h3
    · rw [Matrix.add_mul, smul_add]; exact h2.add h4
  neg_mem' := by
    rintro X ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.mul_neg]; exact h1.neg
    · rw [Matrix.neg_mul, smul_neg]; exact h2.neg

def latD {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} (ϖ : w.adicCompletion E) (a b i j : ℕ) :
    AddSubgroup (Matrix (Fin a) (Fin b) (w.adicCompletion E)) where
  carrier := {W | ∀ (r : Fin a) (s : Fin b), (if (r : ℕ) < i ∧ j ≤ (s : ℕ) then ϖ * W r s else W r s) ∈ Ov E w}
  zero_mem' := by
    intro r s
    simp only [Matrix.zero_apply, mul_zero, ite_self]
    exact (Ov E w).zero_mem
  add_mem' := by
    intro X Y h1 h2 r s
    have e1 := h1 r s
    have e2 := h2 r s
    simp only [Matrix.add_apply]
    split_ifs at e1 e2 ⊢
    · rw [mul_add]; exact (Ov E w).add_mem e1 e2
    · exact (Ov E w).add_mem e1 e2
  neg_mem' := by
    intro X h1 r s
    have e1 := h1 r s
    simp only [Matrix.neg_apply]
    split_ifs at e1 ⊢
    · rw [mul_neg]; exact (Ov E w).neg_mem e1
    · exact (Ov E w).neg_mem e1

end GlobalTheory.CompanionTheory.CtS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEigenfunctionEquicontinuousStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernel_eigenfunction_equicontinuous : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∀ η : ℝ≥0∞, 0 < η → ∃ U ∈ 𝓝 (1 : GA E N), ∀ ψ : GA E N → ℂ, Continuous ψ →
  (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) → (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) →
  (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 → ∀ y ∈ U, ∫⁻ x in F, ‖ψ (x * y) - ψ x‖ₑ ^ 2 ∂μ ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close | exact GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close | (intros; apply GlobalTheory.CompanionTheory.Conc.translate_sq_mean_close <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFreeStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.langlands_socle_of_order_free : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GKLocal k → LOrderFree k → LSocleGL k := by
  first | exact @GlobalTheory.CompanionTheory.LSocle.lSocleGL | exact GlobalTheory.CompanionTheory.LSocle.lSocleGL | (intros; apply GlobalTheory.CompanionTheory.LSocle.lSocleGL <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelOpenCompact
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem latN_isOpen_isCompact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M N : ℕ), 0 < N →
    IsOpen (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ∧
    IsCompact (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ _ d b n M N hN
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  obtain ⟨u, hu⟩ : IsUnit (N : Af F) := by
    have h1 : IsUnit (algebraMap F (Af F) (N : F)) := (IsUnit.mk0 _ hNF).map _
    rwa [map_natCast] at h1
  have hSo : IsOpen {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have hpre : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun y => (↑u⁻¹ : Af F) * y) ⁻¹' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        show (↑u⁻¹ : Af F) * ((N : Af F) * z) ∈ Oh F
        rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
        exact hz
      · intro hy
        exact ⟨(↑u⁻¹ : Af F) * y, hy, by rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]⟩
    rw [hpre]
    exact (AfTop.isOpen_Oh F).preimage (continuous_const_mul _)
  have hSc : IsCompact {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} := by
    have himg : {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z} = (fun z => (N : Af F) * z) '' Oh F := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [himg]
    exact (AfTop.isCompact_Oh F).image (continuous_const_mul _)
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  let Bs := Algebra.TensorProduct.basis (Af F) b
  let e : (Af F ⊗[F] E) ≃ₜ (Fin d → Af F) :=
    { Bs.equivFun.toEquiv with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap Bs.equivFun.symm.toLinearMap }
  have hT : {x : Af F ⊗[F] E | InNOh b N x} =
      e ⁻¹' Set.univ.pi (fun _ => {y : Af F | ∃ z ∈ Oh F, y = (N : Af F) * z}) := by
    ext x
    rw [Set.mem_preimage, Set.mem_univ_pi]
    exact Iff.rfl
  have hlat : (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) =
      Set.univ.pi (fun _ => Set.univ.pi (fun _ => {x : Af F ⊗[F] E | InNOh b N x})) := by
    ext X
    simp only [Set.mem_univ_pi]
    exact Iff.rfl
  have hTo : IsOpen {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact (isOpen_set_pi Set.finite_univ fun _ _ => hSo).preimage e.continuous
  have hTc : IsCompact {x : Af F ⊗[F] E | InNOh b N x} := by
    rw [hT]
    exact e.isCompact_preimage.mpr (isCompact_univ_pi fun _ => hSc)
  rw [hlat]
  exact ⟨isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hTo,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hTc⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeLevelsNeighbourhoodBasis
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem exists_cube_subset_of_mem_nhds_zero {ι X : Type*} [Finite ι] [TopologicalSpace X] [Zero X]
    {V : Set (ι → X)} (hV : V ∈ nhds (0 : ι → X)) :
    ∃ W ∈ nhds (0 : X), ∀ Y : ι → X, (∀ i, Y i ∈ W) → Y ∈ V := by
  rw [nhds_pi, Filter.mem_pi] at hV
  obtain ⟨I, -, t, ht, hsub⟩ := hV
  refine ⟨⋂ i, t i, Filter.iInter_mem.mpr (fun i => by simpa using ht i), fun Y hY => hsub ?_⟩
  intro i _
  exact Set.mem_iInter.mp (hY i) i

theorem latN_small : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ),
    ∀ U ∈ nhds (0 : Fin n → Fin M → Af F ⊗[F] E), ∃ N : ℕ, 0 < N ∧
      (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ⊆ U := by
  intro F E _ _ _ _ _ σ _ d b n M U hU
  let bb := Algebra.TensorProduct.basis (Af F) b
  obtain ⟨W1, hW1, hW1U⟩ := exists_cube_subset_of_mem_nhds_zero hU
  obtain ⟨W, hW, hWW1⟩ := exists_cube_subset_of_mem_nhds_zero hW1
  have hcont : Continuous (fun c : Fin d → Af F => ∑ k, c k • bb k) :=
    continuous_finsetSum _ (fun k _ => (continuous_apply k).smul continuous_const)
  have hV : (fun c : Fin d → Af F => ∑ k, c k • bb k) ⁻¹' W ∈ nhds (0 : Fin d → Af F) := by
    apply hcont.continuousAt.preimage_mem_nhds
    simpa using hW
  obtain ⟨V0, hV0, hV0V⟩ := exists_cube_subset_of_mem_nhds_zero hV
  obtain ⟨-, -, -, -, -, -, -, hN, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  obtain ⟨N, hNpos, hNV0⟩ := hN V0 hV0
  refine ⟨N, hNpos, fun X hX => hW1U X fun a => hWW1 (X a) fun i => ?_⟩
  have hXai : InNOh b N (X a i) :=
    (show ∀ (a : Fin n) (i : Fin M), InNOh b N (X a i) from hX) a i
  have hmem : (⇑(bb.repr (X a i))) ∈ (fun c : Fin d → Af F => ∑ k, c k • bb k) ⁻¹' W := by
    apply hV0V
    intro k
    obtain ⟨y, hy, hk⟩ := hXai k
    rw [hk]
    exact hNV0 y hy
  simp only [Set.mem_preimage] at hmem
  rwa [bb.sum_repr] at hmem

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalContentZetaSeriesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_content_zeta_series : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ (ι : Type) (_ : Countable ι) (c : ι → Fv F v ⊗[F] E) (w : ι → ℕ), IsContent σ b v c w ∧ ∀ s : ℕ, 1 ≤ s → HasSum (fun i => (((qv v : ℝ) ^ w i)⁻¹) ^ s) (zetaV E v s) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content.content | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content.content | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.Content.content <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGoodReductionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_good_reduction : PositivityTheory.Rg.BcB.G8.Fin.LocGood := by
  first | exact @GlobalTheory.CompanionTheory.LocGoodProof.locGood | exact GlobalTheory.CompanionTheory.LocGoodProof.locGood | (intros; apply GlobalTheory.CompanionTheory.LocGoodProof.locGood <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMatrixIntegralStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_integral : PositivityTheory.SiegelWeilFormula.Gunr.LocMat := by
  first | exact @GlobalTheory.CompanionTheory.Gunr.locMat | exact GlobalTheory.CompanionTheory.Gunr.locMat | (intros; apply GlobalTheory.CompanionTheory.Gunr.locMat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MinimalParabolicRationalCompactStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minimal_parabolic_rational_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ minParOne σ J X ∧ ∀ p ∈ minParOne σ J X, ∃ δ ∈ ratPts σ J, δ ∈ minPar σ J X ∧ ∃ ω ∈ Ω, p = δ * ω := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact | exact GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.minParOne_cocompact <;> assumption)
end

