import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0016
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0652
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0647
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0625
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0409
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1474

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanOneParamEqProdCmTypeLines
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.ConjLineSplit

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (conjU continuous_conjU)
open GlobalTheory.ConjUTransport (conjUInv conjEquiv continuous_conjUInv)

theorem exists_lie_eq_exp {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (M : ℝ → Matrix (Fin n) (Fin n) ℂ) (hc : Continuous M)
    (h0 : M 0 = 1) (hm : ∀ s t, M (s + t) = M s * M t) (hU : ∀ t, (M t)ᴴ * H * M t = H) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, Yᴴ * H + H * Y = 0 ∧ ∀ t : ℝ, NormedSpace.exp (t • Y) = M t := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  obtain ⟨Y, hY⟩ := GlobalTheory.banach_oneParamGroup_eq_exp M hc h0 hm
  refine ⟨Y, ?_, hY⟩
  have hd : HasDerivAt M Y 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul, funext hY] at h
    exact h
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun c A => by rw [Matrix.conjTranspose_smul]; simp }
  have hT : HasDerivAt (fun t => (M t)ᴴ) Yᴴ 0 :=
    (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt 0 hd
  have hF := (hT.mul_const H).fun_mul hd
  rw [funext hU] at hF
  have huniq := hF.unique (hasDerivAt_const (0 : ℝ) H)
  rwa [h0, Matrix.conjTranspose_one, mul_one, one_mul] at huniq

variable {D : D7}

theorem finTens_eq_zero {z : AE D} (h : ∀ u : AF D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F u = 0 → u • z = 0) :
    GlobalTheory.LFun.finTens D.host.F D.host.E z = 0 := by
  let e : AF D.host.F := ((0, 1) : Ainf D.host.F × Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)
  have he : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F e = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
  have h1 := congrArg (GlobalTheory.LFun.finTens D.host.F D.host.E) (h e he)
  rw [Algebra.smul_def, map_mul, map_zero] at h1
  have h2 : GlobalTheory.LFun.finTens D.host.F D.host.E (algebraMap (AF D.host.F) (AE D) e) = 1 := rfl
  rwa [h2, one_mul] at h1

theorem cA_smul (u : AF D.host.F) (z : AE D) : cA D (u • z) = u • cA D z :=
  map_smul (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig) u z

theorem smul_cA_sub (u : AF D.host.F) {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) (i j : Fin n) :
    (u • (A.map (cA D) - 1)) i j = cA D ((u • (A - 1)) i j) := by
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, cA_smul, map_sub, Matrix.one_apply]
  split_ifs <;> simp

theorem conjU_mem_UAt_iff (W : HSp D) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank)
    (hJ : Wd.J = (1 : D.host.E) • W.gram) (g : GA D W) :
    conjU W 1 hJ g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) ↔ g ∈ GinfC W := by
  have hone : ∀ a b : Fin W.rank, GlobalTheory.LFun.finTens D.host.F D.host.E ((1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) a b) =
      (1 : Matrix (Fin W.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) a b := by
    intro a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · intro h
    show finHom W g = 1
    refine Units.ext (Matrix.ext fun a b => ?_)
    have h1 : GlobalTheory.LFun.finTens D.host.F D.host.E ((Formalism.L2.Theta.mt W g - 1) a b) = 0 := by
      refine finTens_eq_zero fun u hu => ?_
      have h2 : (u • ((Formalism.L2.Theta.mt W g).map (cA D) - 1)) a b = 0 := congrFun (congrFun (h u hu) a) b
      rw [smul_cA_sub] at h2
      have h3 := congrArg (cA D) h2
      rw [Formalism.L2.Theta.cA_cA, map_zero] at h3
      exact h3
    rw [Matrix.sub_apply, map_sub, hone, sub_eq_zero] at h1
    exact h1
  · intro hg u hu
    have hf : finHom W g = 1 := hg
    refine Matrix.ext fun a b => ?_
    show (u • ((Formalism.L2.Theta.mt W g).map (cA D) - 1)) a b = 0
    rw [smul_cA_sub, Matrix.smul_apply, GlobalTheory.KapXLine.smul_eq_zero_of_finTens hu, map_zero]
    rw [Matrix.sub_apply, map_sub, hone, sub_eq_zero]
    exact congrArg (fun k : GL (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => k.1 a b) hf

theorem ext_of_infMat {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) {g h : GA D W} (hg : g ∈ GinfC W) (hh : h ∈ GinfC W)
    (e : ∀ τ, infMat D.sp.cm.sig W.gram (θ τ) g = infMat D.sp.cm.sig W.gram (θ τ) h) : g = h := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have a : (finHom W g).1 = (finHom W h).1 := by
    rw [show finHom W g = 1 from hg, show finHom W h = 1 from hh]
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => sub_eq_zero.1 (hσ.ext _ ?_ fun τ => ?_)))
  · rw [RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun a i) j
  · rw [RingHom.map_sub, RingHom.map_sub, sub_eq_zero]
    exact congrFun (congrFun (e τ) i) j

open Classical in

theorem infMat_prod {θ : InfFam D} (W : HSp D) (m : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (x : D.what₂.Tau → GA D W) (hx : ∀ τ, IsAtTau θ W τ (m τ) (x τ)) (τ : D.what₂.Tau) (l : List D.what₂.Tau)
    (hl : l.Nodup) : infMat D.sp.cm.sig W.gram (θ τ) (l.map x).prod = if τ ∈ l then m τ else 1 := by
  induction l with
  | nil => simpa using GlobalTheory.PointAtPlaceHom.infMat_one W (θ τ)
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, GlobalTheory.PointAtPlaceHom.infMat_mul, ih hl.2]
    by_cases c : τ = a
    · subst c
      rw [(hx τ).2.1, if_neg hl.1, if_pos List.mem_cons_self, Matrix.mul_one]
    · rw [(hx a).2.2 τ c, Matrix.one_mul]
      simp only [List.mem_cons, c, false_or]

theorem exists_eq_prod_oneP {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (g : ℝ → GA D W) (hc : Continuous g)
    (h0 : g 0 = 1) (hm : ∀ s t, g (s + t) = g s * g t) (hg : ∀ t, g t ∈ GinfC W) :
    ∃ Y : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ, (∀ τ, Y τ ∈ lieAt W τ) ∧
      ∀ t, g t = ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => oneP θ W τ (Y τ) t).prod := by
  have h1 : Continuous (matHom W) := continuous_subtype_val
  choose Y hY hexp using fun τ => exists_lie_eq_exp (gramAt D W τ) (fun t => infMat D.sp.cm.sig W.gram (θ τ) (g t))
    (continuous_matrix fun i j => (GlobalTheory.FockCompare.continuous_comp hθ τ).comp
      ((Units.continuous_val.comp (h1.comp hc)).matrix_elem i j))
    (by rw [h0, GlobalTheory.PointAtPlaceHom.infMat_one]) (fun s t => by rw [hm, GlobalTheory.PointAtPlaceHom.infMat_mul])
    (fun t => GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ W (g t) τ)
  refine ⟨Y, hY, fun t => ext_of_infMat hθ W (hg t) ?_ fun τ => ?_⟩
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact GlobalTheory.PointAtPlaceHom.atTau_mem W τ _
  · rw [infMat_prod W _ _ (fun τ' => GlobalTheory.Mem.Lift.isAtTau_oneP hθ (hY τ') t) τ _ (Finset.nodup_toList _),
      if_pos (Finset.mem_toList.2 (Finset.mem_univ τ)), hexp]

theorem line_eq_prod : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (W : HSp D) (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank)
    (hJ : Wd.J = (1 : D.host.E) • W.gram), ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd,
    ∃ (Y : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
      (γs : D.what₂.Tau → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J)),
      (∀ τ, Y τ ∈ lieAt W τ) ∧ (∀ τ, γs τ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd) ∧
      (∀ τ t, γs τ (Multiplicative.ofAdd t) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hJ (oneP θ W τ (Y τ) t)) ∧
      ∀ t, γ t = ((Finset.univ : Finset D.what₂.Tau).toList.map fun τ => γs τ t).prod := by
  intro D θ hθ W Wd hJ γ hγ
  let φ := conjEquiv W 1 one_ne_zero hJ
  obtain ⟨Y, hY, hprod⟩ := exists_eq_prod_oneP hθ W (fun t => φ.symm (γ (Multiplicative.ofAdd t)))
    ((continuous_conjUInv W 1 one_ne_zero hJ).comp (hγ.1.comp continuous_ofAdd))
    (by rw [ofAdd_zero, map_one, map_one]) (fun s t => by rw [ofAdd_add, map_mul, map_mul])
    (fun t => (conjU_mem_UAt_iff W Wd hJ _).1 (by
      have e : conjU W 1 hJ (φ.symm (γ (Multiplicative.ofAdd t))) = γ (Multiplicative.ofAdd t) := φ.apply_symm_apply _
      rw [e]
      exact hγ.2 _))
  let p : D.what₂.Tau → (Multiplicative ℝ →* GA D W) := fun τ =>
    { toFun := fun t => oneP θ W τ (Y τ) (Multiplicative.toAdd t)
      map_one' := GlobalTheory.Mem.Lift.oneP_zero hθ
      map_mul' := fun s t => GlobalTheory.Mem.Lift.oneP_add hθ (hY τ) _ _ }
  refine ⟨Y, fun τ => φ.toMonoidHom.comp (p τ), hY, fun τ => ⟨?_, fun t => ?_⟩, fun τ t => rfl, fun t => ?_⟩
  · exact (continuous_conjU W 1 hJ).comp ((GlobalTheory.Mem.Lift.continuous_oneP hθ (hY τ)).comp continuous_toAdd)
  · exact (conjU_mem_UAt_iff W Wd hJ _).2 (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _)
  · have e := congrArg φ (hprod (Multiplicative.toAdd t))
    rw [φ.apply_symm_apply, map_list_prod, List.map_map] at e
    exact e

end GlobalTheory.ConjLineSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineCmModelAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SchwartzSlope

open Filter Topology
open scoped SchwartzMap RealInnerProductSpace

theorem lintegral_of_integral (l : Type) [Fintype l] (f g : GlobalTheory.RealWeil.Sch l)
    (h : ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2) : ∫⁻ x, ‖f x‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have key : ∀ u : GlobalTheory.RealWeil.Sch l, ∫ x, ‖u x‖ ^ 2 = (∫⁻ x, ‖u x‖ₑ ^ 2).toReal := by
    intro u
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖u x‖ ^ 2) (Eventually.of_forall fun x => sq_nonneg ‖u x‖)
      ((by fun_prop : Continuous fun x => ‖u x‖ ^ 2).aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have fin : ∀ u : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖u x‖ₑ ^ 2 ≠ ⊤ := by
    intro u
    rw [GlobalTheory.MetaplecticScalarDeriv.lintegral_sq_eq]
    exact ENNReal.pow_ne_top (Lp.eLpNorm_ne_top _)
  rw [key, key] at h
  exact (ENNReal.toReal_eq_toReal_iff' (fin f) (fin g)).1 h

theorem coordSlope (hP : GlobalTheory.FunPr.Hypotheses₂) (l : Type) [Fintype l] [DecidableEq l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l)
    (hA : ∀ w, Continuous fun t => A t w) (hT : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hI : ∀ t w (f f₁ : GlobalTheory.RealWeil.Sch l), ⇑f₁ = GlobalTheory.RealWeil.rhoFun w ⇑f →
      ⇑(T t f₁) = GlobalTheory.RealWeil.rhoFun (A t w) ⇑(T t f))
    (hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) (hpt : ∀ f y, Continuous fun t => T t f y) :
    ∀ f, ∃ g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 g) := by
  obtain ⟨hs, hgrp, h0⟩ := GlobalTheory.T.symplectic_and_flow_of_intertwining_unitary l A T hT hT0 hI hiso
  have hT0' : T 0 = LinearMap.id := LinearMap.ext hT0
  have hTadd : ∀ s t, T (s + t) = T s ∘ₗ T t := fun s t => LinearMap.ext (hT s t)
  have hiso' : ∀ t h, ∫⁻ x, ‖T t h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2 := fun t h =>
    lintegral_of_integral l _ _ (hiso t h)
  obtain ⟨X, hsp, hB⟩ : ∃ X : Matrix (l ⊕ l) (l ⊕ l) ℝ, X ∈ LieAlgebra.Symplectic.sp l ℝ ∧
      ∀ t w, NormedSpace.exp (t • X) *ᵥ w = A t w := by
    cases isEmpty_or_nonempty l with
    | inl hl => exact ⟨0, zero_mem _, fun t w => Subsingleton.elim _ _⟩
    | inr hl =>
      let M : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => LinearMap.toMatrix' (A t)
      have hM : ∀ t w, M t *ᵥ w = A t w := fun t w => LinearMap.toMatrix'_mulVec (A t) w
      have hMc : Continuous M := by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        simp only [M, LinearMap.toMatrix'_apply]
        exact (continuous_apply i).comp (hA _)
      have hM0 : M 0 = 1 := by
        have : A 0 = LinearMap.id := LinearMap.ext h0
        simp only [M, this, LinearMap.toMatrix'_id]
      have hMm : ∀ s t, M (s + t) = M s * M t := by
        intro s t
        have : A (s + t) = (A s).comp (A t) := LinearMap.ext (hgrp s t)
        simp only [M, this, LinearMap.toMatrix'_comp]
      obtain ⟨X, hX⟩ := GlobalTheory.T.continuous_matrix_oneParameterGroup_eq_exp _ M hMc hM0 hMm
      have hsp : X ∈ LieAlgebra.Symplectic.sp l ℝ := by
        refine GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup l X fun t => ?_
        obtain ⟨N, hN⟩ := GlobalTheory.exists_symplecticGroup_of_sympl l (A t) (hs t)
        have e : Matrix.toLin' (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = A t := LinearMap.ext fun w => by
          rw [Matrix.toLin'_apply, hN]
        have e2 : (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = M t := by
          simp only [M, ← e, LinearMap.toMatrix'_toLin']
        rw [← hX t, ← e2]
        exact N.2
      exact ⟨X, hsp, fun t w => by rw [← hX, hM]⟩
  obtain ⟨a, ha⟩ := GlobalTheory.T.schwartz_one_parameter_group_formula hP l X hsp T hT0' hTadd
    (fun t w h h₁ hh => by rw [hI t w h h₁ hh, hB]) hiso' hpt
  exact fun f => ⟨_, ha f⟩

open GlobalTheory.ArchUniq GlobalTheory.RealWeil in

theorem slope (hP : GlobalTheory.FunPr.Hypotheses₂) (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (P : V → V → ℝ) (hPp : IsPairing P)
    (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ))
    (hAc : ∀ v, Continuous fun t => A t v) (hTadd : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hTi : ∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f))
    (hTl2 : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) (hTc : ∀ f y, Continuous fun t => T t f y) :
    ∀ f, ∃ g, Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[≠] 0) (𝓝 g) := by
  obtain ⟨C, φ, hp, hq⟩ := SchrTransport.coords P hPp (Module.finrank ℝ V) rfl
  have hS := SchrTransport.schr_coords P C φ hp hq
  let toE : 𝓢(V, ℂ) →L[ℂ] Sch (Fin (Module.finrank ℝ V)) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C.symm
  let toV : Sch (Fin (Module.finrank ℝ V)) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) C
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑C.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑C := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  let T' : ℝ → Sch (Fin (Module.finrank ℝ V)) →ₗ[ℂ] Sch (Fin (Module.finrank ℝ V)) :=
    fun t => toE.toLinearMap ∘ₗ T t ∘ₗ toV.toLinearMap
  let A' : ℝ → (Fin (Module.finrank ℝ V) ⊕ Fin (Module.finrank ℝ V) → ℝ) →ₗ[ℝ]
      (Fin (Module.finrank ℝ V) ⊕ Fin (Module.finrank ℝ V) → ℝ) :=
    fun t => φ.toLinearMap ∘ₗ A t ∘ₗ φ.symm.toLinearMap
  have hT' : ∀ t h, T' t h = toE (T t (toV h)) := fun t h => rfl
  obtain ⟨k, hk, hint⟩ := SchrTransport.haar_coords μ C
  have c1 : ∀ w, Continuous fun t => A' t w := by
    intro w
    exact (φ.toLinearMap.continuous_of_finiteDimensional).comp (hAc (φ.symm w))
  have c2 : ∀ s t f, T' (s + t) f = T' s (T' t f) := by
    intro s t h
    simp only [hT', hVE, hTadd]
  have c3 : ∀ f, T' 0 f = f := by
    intro h
    simp [hT', hT0, hEV]
  have c4 : ∀ t w (f f₁ : Sch (Fin (Module.finrank ℝ V))), ⇑f₁ = rhoFun w ⇑f →
      ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f) := by
    intro t w f f₁ hf
    have e1 : ⇑(toV f₁) = schrF P (φ.symm w) ⇑(toV f) := by
      funext x
      have := congrFun (hS (φ.symm w) ⇑f) x
      simp only [Function.comp_apply, LinearEquiv.apply_symm_apply] at this
      simp only [htoV, Function.comp_apply, hf]
      exact this.symm
    have e2 := hTi t _ _ _ e1
    rw [hT' t f₁, hT' t f, htoE, htoE, e2]
    obtain ⟨G, hG⟩ : ∃ G : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ, ⇑(T t (toV f)) = G ∘ ⇑C :=
      ⟨⇑(T t (toV f)) ∘ ⇑C.symm, by ext x; simp⟩
    have hGC : (G ∘ ⇑C) ∘ ⇑C.symm = G := by funext x; simp
    rw [hG, hS, hGC]
    funext x
    simp [A']
  have c5 : ∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    intro t h
    have e := hTl2 t (toV h)
    rw [hint, hint] at e
    simp only [htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] at e
    exact mul_left_cancel₀ hk.ne' e
  have c6 : ∀ f y, Continuous fun t => T' t f y := by
    intro h y
    exact hTc (toV h) (C.symm y)
  have hlim := coordSlope hP (Fin (Module.finrank ℝ V)) A' T' c1 c2 c3 c4 c5 c6
  intro f
  obtain ⟨g, hg⟩ := hlim (toE f)
  refine ⟨toV g, ?_⟩
  have e : (fun t : ℝ => t⁻¹ • (T t f - f)) =
      fun t : ℝ => (toV.restrictScalars ℝ) (t⁻¹ • (T' t (toE f) - toE f)) := by
    funext t
    rw [map_smul, map_sub]
    simp only [ContinuousLinearMap.coe_restrictScalars', hT', hVE]
  rw [e]
  exact ((toV.restrictScalars ℝ).continuous.tendsto g).comp hg

theorem main : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W,
    ∀ T : ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) →
    (∀ s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) →
    (∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), T 0 f = f) →
    ∀ f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), ∃ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (nhdsWithin 0 {0}ᶜ) (nhds g) := by
  classical
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ T hT hadd h0
  obtain ⟨A, hAc, hA⟩ := GlobalTheory.T.archimedeanLine_intertwines_realSchrodinger M ψ χX χW om hψ hW γ hγ T hT
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Measure.addHaar
  have hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := fun t f =>
    GlobalTheory.T.weil_representation_integral_action M ψ χX χW om hW μ inferInstance (γ (Multiplicative.ofAdd t)) f (T t f) (hT t f)
  obtain ⟨hc1, -⟩ := GlobalTheory.T.archimedeanOneParameterFamily_continuous M ψ χX χW om hW γ hγ T hT
  exact slope hP (Fin n × Fin d → mixedEmbedding.mixedSpace F) μ _ (GlobalTheory.ArchUniq.Coord.isPairing_trP (F := F) (Fin n × Fin d)) A T hAc hadd h0 hA hiso hc1

end GlobalTheory.SchwartzSlope

end
end

