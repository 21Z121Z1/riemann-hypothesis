import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1715
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0393
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0220
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0458
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0481

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingPairingMemCoefficientField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim

noncomputable section

namespace GlobalTheory.BrRat

open MvPolynomial Formalism.L2.Col Formalism.L2.Ker

section General

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem projVV_of_mem {K : Type} [Field K] [CharZero K] (sg : ι → DomWeight n) (x : VV K sg) :
    Br.projVV sg x.1 = x := by
  have h := GlobalTheory.Proof.TensorMapDescent.eq_zero_of_fockB sg (Br.projVV sg x.1 - x) fun i => by
    rw [← fockBL_apply, Submodule.coe_sub, map_sub, fockBL_apply, fockBL_apply,
      GlobalTheory.Proof.TensorMapDescent.fockB_projVV_basis, sub_self]
  exact sub_eq_zero.mp h

theorem exists_map_eq {K : Type} [Field K] (φ : K →+* ℂ) {σ : Type} (P : MvPolynomial σ ℂ)
    (h : ∀ m, coeff m P ∈ Set.range φ) : ∃ P₀ : MvPolynomial σ K, map φ P₀ = P := by
  classical
  choose c hc using h
  refine ⟨∑ m ∈ P.support, monomial m (c m), ?_⟩
  conv_rhs => rw [P.as_sum]
  simp [map_sum, map_monomial, hc]

theorem descend {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (sg : ι → DomWeight n) (x : VV ℂ sg)
    (h : ∀ m, coeff m x.1 ∈ Set.range φ) : ∃ y : VV K sg, map φ y.1 = x.1 := by
  obtain ⟨P₀, hP⟩ := exists_map_eq φ x.1 h
  refine ⟨Br.projVV sg P₀, ?_⟩
  rw [← GlobalTheory.Proof.TensorMapDescent.projVV_map φ sg P₀, hP, projVV_of_mem]

theorem map_frDet {K : Type} [Field K] (φ : K →+* ℂ) (τ : ι) : map φ (frDet K n τ) = frDet ℂ n τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext a s
  simp

theorem map_dualSubst {K : Type} [Field K] (φ : K →+* ℂ) (P : Pol K ι n) :
    map φ (dualSubst K ι n P) = dualSubst ℂ ι n (map φ P) := by
  have e : (map φ : Pol K ι n →+* Pol ℂ ι n).comp (dualSubst K ι n).toRingHom =
      (dualSubst ℂ ι n).toRingHom.comp (map φ) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [dualSubst]
    · intro v
      have hm : (Matrix.of fun a s : Fin n => (X (v.1, a, s) : Pol ℂ ι n)) =
          (map φ : Pol K ι n →+* Pol ℂ ι n).mapMatrix (Matrix.of fun a s : Fin n => (X (v.1, a, s) : Pol K ι n)) := by
        ext a s
        simp
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, dualSubst, aeval_X, map_X]
      rw [hm, ← RingHom.map_adjugate]
      rfl
  exact DFunLike.congr_fun e P

theorem isFunForm_map {K : Type} [Field K] (φ : K →+* ℂ) (σ : ι → DomWeight n) {F : VV K σ}
    {f : VV K fun τ => (σ τ).dual} (h : IsFunForm σ F f) :
    IsFunForm σ ⟨map φ F.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ σ _ F.2⟩
      ⟨map φ f.1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ _ _ f.2⟩ := by
  unfold IsFunForm at h ⊢
  have h1 := congrArg (map φ) h
  simp only [map_mul, map_prod, map_pow, map_frDet, map_dualSubst] at h1
  exact h1

theorem covOf_eq (σ : ι → DomWeight n) (f : VV ℂ fun τ => (σ τ).dual) : covOf σ f = (funEquiv σ).symm f := by
  have hex : ∃ φ : (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] VV ℂ σ, ∀ f, IsFunForm σ (φ f) f :=
    ⟨(funEquiv σ).symm.toLinearMap, fun f => (isFunForm_iff_eq σ _ f).2 (by simp)⟩
  have e : covOf σ f = hex.choose f := by rw [covOf, dif_pos hex]
  rw [e]
  apply (funEquiv σ).injective
  rw [LinearEquiv.apply_symm_apply]
  exact ((isFunForm_iff_eq σ _ f).1 (hex.choose_spec f)).symm

theorem covOf_desc {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (σ : ι → DomWeight n)
    (f : VV ℂ fun τ => (σ τ).dual) (hf : ∀ m, coeff m f.1 ∈ Set.range φ) :
    ∃ F₀ : VV K σ, map φ F₀.1 = (covOf σ f).1 := by
  obtain ⟨f₀, hf₀⟩ := descend φ _ f hf
  refine ⟨(funEquiv σ).symm f₀, ?_⟩
  have h1 : IsFunForm σ ((funEquiv σ).symm f₀) f₀ := by
    have := isFunForm_funEquiv σ ((funEquiv σ).symm f₀)
    rwa [LinearEquiv.apply_symm_apply] at this
  have h2 := isFunForm_map φ σ h1
  have h4 : f = funEquiv σ ⟨map φ ((funEquiv σ).symm f₀).1, GlobalTheory.Proof.TensorMapDescent.map_mem_VV φ σ _ ((funEquiv σ).symm f₀).2⟩ := by
    rw [← (isFunForm_iff_eq σ _ _).1 h2]
    exact Subtype.ext hf₀.symm
  rw [covOf_eq, h4, LinearEquiv.symm_apply_apply]

theorem brPair_mem_range {K : Type} [Field K] [CharZero K] (φ : K →+* ℂ) (σ : ι → DomWeight n) {N : ℕ}
    (hN : N = n + 1) (Λ : ι → DomWeight N) (U : VV ℂ Λ) (V : VV ℂ fun τ => (σ τ).dual)
    (hU : ∀ m, coeff m U.1 ∈ Set.range φ) (hV : ∀ m, coeff m V.1 ∈ Set.range φ) :
    brPair σ hN Λ U V ∈ Set.range φ := by
  obtain ⟨U₀, hU₀⟩ := exists_map_eq φ U.1 hU
  obtain ⟨F₀, hF₀⟩ := covOf_desc φ σ V hV
  refine ⟨(extNormB K σ)⁻¹ * fockB (Br.brStdP hN Λ σ U₀ : Pol K ι n) F₀.1, ?_⟩
  rw [brPair, LinearMap.compl₁₂_apply, pairBK_apply, pairB_apply, ← hF₀, Br.brStd, LinearMap.comp_apply,
    Submodule.subtype_apply, ← hU₀, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map, GlobalTheory.Proof.TensorMapDescent.fockB_map, map_mul, map_inv₀]
  congr 2
  unfold extNormB
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← GlobalTheory.Proof.TensorMapDescent.fockB_map, Formalism.L2.DIV.map_extremal]

end General

end GlobalTheory.BrRat

namespace GlobalTheory.RowClaim

theorem brPair_mem_coefField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A), HidaSetting large₂ R F → ch.Is → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ (U : VV ℂ (wt ch.G (.top D.R.m))) (V : VV ℂ (wt ch.G (.grid D.R.m D.R.m))), (∀ m, MvPolynomial.coeff m U.1 ∈ Set.range D.what₂.embLL) → (∀ m, MvPolynomial.coeff m V.1 ∈ Set.range D.what₂.embLL) → brPair (listedWt ch.G (.grid D.R.m D.R.m)) ch.G.sp.topDec.rank.symm (wt ch.G (.top D.R.m)) U V ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F _ _ _ t Φ _ U V hU hV
  haveI : CharZero D.what₂.LL := (RingHom.charZero_iff D.what₂.embLL.injective).mpr inferInstance
  exact GlobalTheory.BrRat.brPair_mem_range D.what₂.embLL _ _ _ U V hU hV

end GlobalTheory.RowClaim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesMoveRealPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PoinConj

variable {D : D7}

theorem cmp_mul' (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (a b : GA D V) :
    cmp θ τ (a * b) = cmp θ τ a * cmp θ τ b := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  show infMat D.sp.cm.sig V.gram (θ τ) (a * b) = infMat D.sp.cm.sig V.gram (θ τ) a * infMat D.sp.cm.sig V.gram (θ τ) b
  rw [e, e, e, map_mul, Units.val_mul, Matrix.map_mul]

theorem cmp_one' (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) : cmp θ τ (1 : GA D V) = 1 := by
  have e : ∀ h : GA D V, infMat D.sp.cm.sig V.gram (θ τ) h = (infHom V h).1.map (θ τ) := fun _ => rfl
  show infMat D.sp.cm.sig V.gram (θ τ) 1 = 1
  rw [e, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

theorem frConj_mem (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.MainNotions.S.UJset (M.ε τ) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  rw [← M.fr_gram τ] at hg'
  change _ * _ * _ = _
  calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
        simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
        rw [hg']; simp only [Matrix.conjTranspose_mul, mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

theorem rep_one' (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ) : M.rep τ 1 w = w := by
  have h1 : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1
  rw [DSModel.rep, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), h1]
  rfl

theorem rep_mul'' (M : DSModel V S) (τ : D.what₂.Tau) {g g' : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (hg' : g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (w : M.H τ) :
    M.rep τ (g * g') w = M.rep τ g (M.rep τ g' w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h := (M.ds τ).2.2.1.1.2 _ (frConj_mem M τ hg) _ (frConj_mem M τ hg')
  have e : M.fr τ * (g * g') * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [DSModel.rep, e, h]
  rfl

theorem rep_inner' (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (a b : M.H τ) : ⟪M.rep τ g a, M.rep τ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
  (⟨(M.rep τ g : M.H τ →ₗ[ℂ] M.H τ), fun v => (M.ds τ).2.2.1.2.1 _ (frConj_mem M τ hg) v⟩ :
    M.H τ →ₗᵢ[ℂ] M.H τ).inner_map_map a b

end GlobalTheory.PoinConj

namespace GlobalTheory.PoinConj

variable {D : D7}

theorem poin_conj : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (v₀ : ∀ τ, M.H τ) (g₀ : GA D V), g₀ ∈ GinfC V → ∀ c g : GA D V, poin θ M K v₀ (g₀⁻¹ * c) v₀ (g * g₀) = poin θ M K (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) c (fun τ => M.rep τ (cmp θ τ g₀) (v₀ τ)) g := by
  intro D θ hθ V S M K v₀ g₀ hg₀ c g
  unfold poin
  congr 1
  funext γ
  have ez : g₀⁻¹ * c * γ * (g * g₀) = g₀⁻¹ * (c * γ * g) * g₀ := by group
  rw [ez]
  set z := c * γ * g
  have h1 : Lev.finE V g₀ = 1 := by
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom V g₀ = 1 from hg₀, map_one]
  have hf : Lev.finE V (g₀⁻¹ * z * g₀) = Lev.finE V z := by
    rw [map_mul, map_mul, map_inv, h1, inv_one, one_mul, mul_one]
  unfold coef
  rw [hf]
  split_ifs with hK
  · unfold coefR
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hU : ∀ x : GA D V, cmp θ τ x ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun x => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V x τ
    rw [cmp_mul', cmp_mul', rep_mul'' M τ (by rw [← cmp_mul']; exact hU _) (hU _),
      rep_mul'' M τ (hU _) (hU _), ← rep_inner' M τ (hU g₀), ← rep_mul'' M τ (hU g₀) (hU g₀⁻¹), ← cmp_mul',
      mul_inv_cancel, cmp_one', rep_one']
  · rfl

end GlobalTheory.PoinConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateUnitaryAdelicIsoMapHaarFundamentalDomai
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.HaarConjImage

theorem map_isHaarFD : ∀ (D : D7) (S : HSp D) (c : D.host.E) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (hJ : J = c • S.gram), c ≠ 0 →
    ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), IsHaarFD S ν 𝓕 →
      (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ '' 𝓕)
        (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)) := by
  intro D S c J hJ hc ν 𝓕 h
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig S.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig S.gram
  have : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  have c1 : Continuous (GlobalTheory.HaarConj.conjE S c hc hJ) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU S c hJ
  have c2 : Continuous (GlobalTheory.HaarConj.conjE S c hc hJ).symm := GlobalTheory.HaarConj.continuous_conjInv S c hc hJ
  haveI := h.1
  exact ⟨MulEquiv.isHaarMeasure_map ν (GlobalTheory.HaarConj.conjE S c hc hJ) c1 c2,
    GlobalTheory.HaarConj.isFundamentalDomain_image (GlobalTheory.HaarConj.conjE S c hc hJ) c1.measurable c2.measurable (GQ S) _
      (GlobalTheory.HaarConj.mem_ratU_iff S c hc hJ) ν 𝓕 h.2⟩

end GlobalTheory.HaarConjImage

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBoundMultiplicityValueExceedsHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SupVal

theorem tprod_ne_zero' {κ : Type} [Fintype κ] {E : κ → Type} [∀ j, AddCommGroup (E j)] [∀ j, Module ℂ (E j)]
    {v : ∀ j, E j} (hv : ∀ j, v j ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  choose l hl using fun j => Module.Projective.exists_dual_eq_one ℂ (hv j)
  intro h
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap l)) h
  simp [hl] at this

theorem exists_bound_half_lt : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)), GlobalTheory.Unf.Vol V → ∀ t ∈ MultT θ M J 1, t ≠ 0 →
    ∀ w : M.Vec, (∀ τ, (w τ : M.H τ) ≠ 0) → ∃ b : ℝ, ∃ x : GA D V,
      (∀ h, ‖t (PiTensorProduct.tprod ℂ w) h‖ ≤ b) ∧ b / 2 < ‖t (PiTensorProduct.tprod ℂ w) x‖ := by
  intro hP D θ hθ V S M J vol t ht ht0 w hw
  have hw' : PiTensorProduct.tprod ℂ w ≠ 0 :=
    tprod_ne_zero' fun τ h => hw τ (by simp [h])
  have hS := GlobalTheory.T.schurMult_multiplicitySpaces_of_rapidDecay hP D θ hθ V S M J 1 vol.μ vol.𝓕 vol.haar vol.fund
  set φ := t (PiTensorProduct.tprod ℂ w) with hφ
  have hφ0 : φ ≠ 0 := fun h => ht0 (GlobalTheory.T.multiplicitySpace_eq_zero_of_apply_nonzero_tensor_zero θ M J 1 vol.μ vol.𝓕 hθ vol.haar vol.fund hS t ht _ hw' h)
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (funext h)
  have hR := (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J 1 t ht
    (PiTensorProduct.tprod ℂ w)).2.2
  obtain ⟨C, hC⟩ := hR.2.2 0
  have hbdd : BddAbove (Set.range fun g => ‖φ g‖) := ⟨C, by
    rintro _ ⟨g, rfl⟩
    simpa using hC g⟩
  have hle : ∀ h, ‖φ h‖ ≤ sSup (Set.range fun g => ‖φ g‖) := fun h => le_csSup hbdd ⟨h, rfl⟩
  have hpos : 0 < sSup (Set.range fun g => ‖φ g‖) := lt_of_lt_of_le (norm_pos_iff.2 hx₀) (hle x₀)
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) (half_lt_self hpos)
  exact ⟨_, x, hle, hx⟩

end GlobalTheory.SupVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReductionEqFlagBasisOtherInstanceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_reduction_eq_flagBasis_otherInstance : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∃ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) ∧ ∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP) := by
  first | exact @GlobalTheory.SeeConjRead.exists_frame_redIs | exact GlobalTheory.SeeConjRead.exists_frame_redIs | (intros; apply GlobalTheory.SeeConjRead.exists_frame_redIs <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeIsogenyFamilyPullbackCorrespondence
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.HeckePoint GlobalTheory.HeckeFrCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem isHkIsog_hkMap (Z : Corr Xo P p i) (hA : admitted l P p) {k : Type} [Field k] [IsAlgClosed k]
    (z : Sp k ⟶ Z.Hk) (C : Subgroup (Over.mk (z ≫ Z.π₁) ⟶ Xo.univ.t.G))
    (hC : Z.toKerScheme.Carries z (z ≫ Z.π₁) C) :
    ∃ ψp, IsHkIsog p (z ≫ Z.π₁) (z ≫ Z.π₂) C ((conj _ _).symm (hkMap Z (h := z) rfl rfl)) ψp := by
  obtain ⟨-, hC⟩ := hC
  have hp : p.Prime := hA.2.2.1
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨⟨hom, hfin, het, hsur, hlin, hiso⟩, hlev⟩ := Z.isog
  have := Xo.smooth
  have := Z.et₁
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth Dw.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  have : IsLocallyNoetherian Z.Hk := LocallyOfFiniteType.isLocallyNoetherian Z.π₁
  obtain ⟨ρ, e₂, e₃, e₄, e₅, e₆⟩ := exists_transfer_pts Z.m₁ z
  obtain ⟨ρ₁, f₂, f₃, f₄, f₅, f₆⟩ := exists_transfer_pts Z.m₂ z
  let σ : (Over.mk z ⟶ Z.o₁.t.G) →* (Over.mk z ⟶ Z.o₂.t.G) :=
    MonoidHom.mk' (fun x => x ≫ Z.ψ) fun a c => MonObj.mul_comp a c Z.ψ
  let ψp := ρ₁.toMonoidHom.comp (σ.comp ρ.symm.toMonoidHom)
  have hψ : ∀ x, ψp (ρ x) = ρ₁ (x ≫ Z.ψ) := fun x => congrArg (fun u => ρ₁ (u ≫ Z.ψ)) (ρ.symm_apply_apply x)
  have c₁ := Z.m₁.cart.1
  let α : pullback Xo.univ.t.G.hom (z ≫ Z.π₁) ⟶ Z.o₁.t.G.left := (swap _).inv ≫ hkLift Z z rfl
  have α₁ : α ≫ Z.m₁.cm.F = pullback.fst _ _ := by
    simp only [α, Category.assoc, hkLift_φ, swap_inv_snd]
  have α₂ : α ≫ Z.o₁.t.G.hom = pullback.snd _ _ ≫ z := by
    simp only [α, Category.assoc, hkLift_hom, swap_inv_fst_assoc]
  have hα : ∀ x, fibPt _ (ρ x) ≫ α = x.left := fun x => c₁.hom_ext
    (by rw [Category.assoc, α₁, fibPt, pullback.lift_fst, e₂])
    (by rw [Category.assoc, α₂, fibPt, pullback.lift_snd_assoc, Over.w x]; exact Category.id_comp _)
  have q₁ : (conj _ _).symm (hkMap Z (h := z) rfl rfl) ≫ pullback.fst _ _ = α ≫ Z.ψ.left ≫ Z.m₂.cm.F := by
    show ((swap _).inv ≫ hkMap Z (h := z) rfl rfl ≫ (swap _).hom) ≫ pullback.fst _ _ = _
    simp only [α, Category.assoc, swap_hom_fst, hkMap_snd, hkMap_snd_assoc]
  have q₂ : (conj _ _).symm (hkMap Z (h := z) rfl rfl) ≫ pullback.snd _ _ = pullback.snd _ _ := by
    show ((swap _).inv ≫ hkMap Z (h := z) rfl rfl ≫ (swap _).hom) ≫ pullback.snd _ _ = _
    simp only [Category.assoc, swap_hom_snd, hkMap_fst, hkMap_fst_assoc, swap_inv_fst]
  refine ⟨ψp, by rw [Category.assoc, Category.assoc, Z.base₂], q₂,
    fun x => ?_, fun a x => ?_, fun v => ?_, Subgroup.ext fun x => ?_, fun n x x' c hn h => ?_, fun p' hp' a => ?_⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    apply pullback.hom_ext
    · rw [Category.assoc, q₁, reassoc_of% hα x, hψ, fibPt, pullback.lift_fst, f₂, Over.comp_left,
        Category.assoc]
    · rw [Category.assoc, q₂, fibPt, fibPt, pullback.lift_snd, pullback.lift_snd]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [← e₃, hψ, hψ, ← f₃, Category.assoc, hlin, Category.assoc]
  · obtain ⟨v, rfl⟩ := ρ₁.surjective v
    obtain ⟨x, rfl⟩ := exists_lift_pt Z.ψ z v
    exact ⟨ρ x, hψ x⟩
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ ρ₁.injective, Z.ker k z x, hC x _ (e₂ x)]
  · obtain ⟨x, rfl⟩ := ρ.surjective x
    obtain ⟨x', rfl⟩ := ρ.surjective x'
    rw [hψ, hψ]
    refine (f₄ _ _ _ _).1 ?_
    replace h := (e₄ _ _ _ _).2 h
    let P₁ := polOf Z.o₁.t Z.o₁.proper Z.o₁.ample Z.o₁.ktriv (ObjDim.smoothOfRelativeDimension Z.o₁)
    let P₂ := polOf Z.o₂.t Z.o₂.proper Z.o₂.ample Z.o₂.ktriv (ObjDim.smoothOfRelativeDimension Z.o₂)
    have hn₀ : 0 < n := Nat.pos_of_ne_zero (by
      rintro rfl
      exact hp.one_lt.ne' ((Nat.coprime_zero_left p).1 hn))
    have : Unique (Over.mk z).left := inferInstanceAs (Unique (PrimeSpectrum k))
    obtain ⟨t₁, t₂⟩ := pow_eq_one_of_weilIs hL.kerPow P₁ hn₀ h
    obtain ⟨c', hc', -⟩ := (hL.weil _ P₂ n _).1 (x ≫ Z.ψ) (x' ≫ Z.ψ)
      (by rw [← MonObj.pow_comp, t₁, MonObj.one_comp]) (by rw [← MonObj.pow_comp, t₂, MonObj.one_comp])
    have e := (weilIs_along_hom hL.globalFns _ _ _ Z.ψ _ _ (p ^ 2) n _ x x' _ _ P₁.isAb P₂.isAb P₁.isLB P₂.isLB hom
      hiso hc').2 h
    rw [unitOn_pow]
    exact e ▸ hc'
  · rw [← e₅, ← e₆, hψ, hψ, Category.assoc, Category.assoc, (hlev p' hp' a).1, (hlev p' hp' a).2, f₅, f₆]
    exact ⟨rfl, rfl⟩

theorem exists_isHeckeFam_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i), admitted l P p → ∀ (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X), x = h ≫ Z.π₁ → x' = h ≫ Z.π₂ → ∃ Ψ : Gx x ⟶ Gx x', IsHeckeFam P p i Ψ ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ Ψ Ψ₁ → Z.toKerScheme.Carries (spMap χ ≫ h) x₁ (transKer Xo.univ.t.G Ψ₁) := by
  intro E _ _ _ H Dw l Xo P p i Z hA T _ h x x' hx hx'
  have hcop : p.Coprime l.M' := (Nat.Prime.coprime_iff_not_dvd hA.2.2.1).2 hA.2.2.2.2
  have hfib : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X)
      (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ (hkMap Z hx hx') Ψ₁ →
        Xo.univ.t.HeckeKer (Over.mk x₁) Dw P p i (transKer Xo.univ.t.G Ψ₁) ∧
          IsHeckeIsog p (transKer Xo.univ.t.G Ψ₁) Ψ₁ ∧
            Z.toKerScheme.Carries (spMap χ ≫ h) x₁ (transKer Xo.univ.t.G Ψ₁) := by
    intro Ω _ _ χ x₁ x₁' Ψ₁ hΨ
    obtain ⟨h₁, h₂, rfl⟩ := isFib_hkMap Z χ hx hx' hΨ
    subst h₁ h₂
    obtain ⟨C, hCk, hCc⟩ := exists_carried Z.toKerScheme (spMap χ ≫ h) _ rfl
    obtain ⟨ψp, hψ⟩ := isHkIsog_hkMap Z hA (spMap χ ≫ h) C ((hCc C).2 rfl)
    have hK := GlobalTheory.ThetaTrace.transKer_of_isHkIsog hψ
    have hH := (isog_iff hcop _ _ C _).1 ⟨ψp, hψ⟩
    rw [Equiv.apply_symm_apply] at hK hH
    rw [hK]
    exact ⟨hCk, hH, (hCc C).2 rfl⟩
  refine ⟨hkMap Z hx hx', ⟨GlobalTheory.T.heckeUniversalIsogenyOnFibres_linear_at_ringPoint E H Dw l Xo P p i Z T h x x' hx hx', hkMap_etale Z hx hx',
    hkMap_surjective Z hx hx', ?_, fun Ω _ _ χ x₁ x₁' Ψ₁ hΨ =>
      ⟨(hfib Ω χ x₁ x₁' Ψ₁ hΨ).1, (hfib Ω χ x₁ x₁' Ψ₁ hΨ).2.1⟩⟩,
    fun Ω _ _ χ x₁ x₁' Ψ₁ hΨ => (hfib Ω χ x₁ x₁' Ψ₁ hΨ).2.2⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_generator_heckeIsogeny_lineBundle_quotient E H Dw l Xo P p i Z T h x x' hx hx'
  exact exists_isRigIso_of_isGen _ _ _ _ _ _ _ _ β ⟨hkMap_fst Z hx hx', GlobalTheory.T.heckeUniversalIsogenyOnFibres_preserves_origin E H Dw l Xo P p i Z T h x x' hx hx'⟩ hβ

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLastStepThetaLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.LastStepLift

theorem exists_lastStep_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels →
    R.IsChainW → R.ex_ioX := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hlev hfam hmod hc
  have hIt : R.chain_ItX := hc.ItX.1 (GlobalTheory.T.exists_lastStep_intertwiner_chain D G Pl0 T A Ks R hlev hfam hmod hc)
  obtain ⟨io, hio⟩ := GlobalTheory.T.exists_multiplicityLift_lastChainStep D G Pl0 T A Ks R hlev hfam hmod hc.ωX hc.vX hc.ptX hIt
  exact fun t => ⟨io t, hio t⟩

end GlobalTheory.Twist.LastStepLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLowestKTypeCoeffSpaceFockMapStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowestKType_coeffSpace_fockMap : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → R.ex_ioP := by
  first | exact @GlobalTheory.IndefLinks.exists_ioP_of_realDat | exact GlobalTheory.IndefLinks.exists_ioP_of_realDat | (intros; apply GlobalTheory.IndefLinks.exists_ioP_of_realDat <;> assumption)
end

