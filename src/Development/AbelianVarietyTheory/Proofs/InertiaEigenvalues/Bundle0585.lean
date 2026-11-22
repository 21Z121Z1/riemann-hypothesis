import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0572
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivOfNotLinearIndependent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0089
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0573
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleSaturatedExactnessCrystalline
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0220
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeGradedOfLevelLe
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmithFormCoefficientRingImageOrPrimeDvdRow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SmithOE

theorem pid_dichotomy {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] (d : ℕ)
    (P : Matrix (Fin d) (Fin d) O) :
    ∃ U W : Matrix (Fin d) (Fin d) O, W * U = 1 ∧ U * W = 1 ∧
      ∀ j, (∃ w : Fin d → O, (fun i => U i j) = P *ᵥ w) ∨ (∀ k, ¬ IsUnit ((W * P) j k)) := by
  classical
  obtain ⟨n, snf⟩ := (LinearMap.range (Matrix.mulVecLin P)).smithNormalForm (Pi.basisFun O (Fin d))
  set U : Matrix (Fin d) (Fin d) O := (Pi.basisFun O (Fin d)).toMatrix snf.bM with hUdef
  set W : Matrix (Fin d) (Fin d) O := snf.bM.toMatrix (Pi.basisFun O (Fin d)) with hWdef
  have hWU : W * U = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  have hUW : U * W = 1 := Module.Basis.toMatrix_mul_toMatrix_flip _ _
  refine ⟨U, W, hWU, hUW, fun j => ?_⟩
  have hUcol : (fun i => U i j) = (snf.bM j : Fin d → O) := by
    funext i
    simp [hUdef, Module.Basis.toMatrix_apply]
  have hmem : ∀ k, (fun i => P i k) ∈ LinearMap.range (Matrix.mulVecLin P) := fun k =>
    ⟨Pi.single k 1, by funext i; simp⟩
  have hWP : ∀ k, (W * P) j k = snf.bM.repr (fun i => P i k) j := by
    intro k
    have h := Module.Basis.toMatrix_mulVec_repr (Pi.basisFun O (Fin d)) snf.bM (fun i => P i k)
    rw [← h, ← hWdef]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
  by_cases h : ∃ i, snf.f i = j ∧ IsUnit (snf.a i)
  · obtain ⟨i, rfl, u, hu⟩ := h
    left
    have hN : (snf.bM (snf.f i) : Fin d → O) ∈ LinearMap.range (Matrix.mulVecLin P) := by
      have h1 : (snf.bM (snf.f i) : Fin d → O) = (↑u⁻¹ : O) • (snf.bN i : Fin d → O) := by
        rw [snf.snf, ← hu, smul_smul, Units.inv_mul, one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (snf.bN i).2
    obtain ⟨w, hw⟩ := hN
    exact ⟨w, by rw [hUcol, ← hw]; rfl⟩
  · right
    intro k
    rw [hWP k]
    by_cases hj : j ∈ Set.range snf.f
    · obtain ⟨i, rfl⟩ := hj
      have h2 := congrFun (snf.repr_comp_embedding_eq_smul ⟨_, hmem k⟩) i
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h2
      have h3 : snf.bM.repr (fun i => P i k) (snf.f i) = snf.a i * snf.bN.repr ⟨_, hmem k⟩ i := h2
      rw [h3]
      intro hu
      exact h ⟨i, rfl, isUnit_of_mul_isUnit_left hu⟩
    · have h0 := snf.repr_eq_zero_of_notMem_range ⟨_, hmem k⟩ hj
      have h0' : snf.bM.repr (fun i => P i k) j = 0 := h0
      rw [h0']
      exact not_isUnit_zero

end GlobalTheory.SmithOE

namespace GlobalTheory.SmithOE

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), IsDiscreteValuationRing ↥bk.OE → ∀ (d' : ℕ) (P : Matrix (Fin d') (Fin d') (WCb l)), (∀ i j, P i j ∈ bk.OE) → ∃ U Uinv : Matrix (Fin d') (Fin d') (WCb l), (∀ i j, U i j ∈ bk.OE) ∧ (∀ i j, Uinv i j ∈ bk.OE) ∧ Uinv * U = 1 ∧ U * Uinv = 1 ∧ ∀ j, (∃ w : Fin d' → WCb l, (fun i => U i j) = P *ᵥ w) ∨ (∀ k, (l : WCb l) ∣ (Uinv * P) j k) := by
  intro l _ K bk _ d' P hP
  have hfac := (GlobalTheory.OEDvr.main l K bk).2.2.2.1
  let P' : Matrix (Fin d') (Fin d') ↥bk.OE := Matrix.of fun i j => ⟨P i j, hP i j⟩
  obtain ⟨U', W', hWU, hUW, hdich⟩ := pid_dichotomy d' P'
  have hP'map : P'.map bk.OE.subtype = P := by ext; rfl
  refine ⟨U'.map bk.OE.subtype, W'.map bk.OE.subtype, fun i j => (U' i j).2, fun i j => (W' i j).2,
    ?_, ?_, fun j => ?_⟩
  · rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [← Matrix.map_mul, hUW, Matrix.map_one _ (map_zero _) (map_one _)]
  · rcases hdich j with ⟨w, hw⟩ | hnu
    · left
      refine ⟨fun i => (w i : WCb l), ?_⟩
      rw [← hP'map]
      funext i
      have := congrArg Subtype.val (congrFun hw i)
      rw [Matrix.mulVec, dotProduct] at this ⊢
      simpa using this
    · right
      intro k
      have heq : ((W'.map bk.OE.subtype) * P) j k = (((W' * P') j k : ↥bk.OE) : WCb l) := by
        rw [← hP'map, ← Matrix.map_mul]; rfl
      rw [heq]
      have hk := hnu k
      generalize (W' * P') j k = x at hk ⊢
      by_cases hx : (x : WCb l) = 0
      · rw [hx]; exact dvd_zero _
      obtain ⟨m, v, v', hv, hv', hvv, hxe⟩ := hfac x x.2 hx
      cases m with
      | zero =>
        exfalso
        apply hk
        refine isUnit_iff_exists_inv.2 ⟨⟨v', hv'⟩, Subtype.ext ?_⟩
        change (x : WCb l) * v' = 1
        rw [hxe, pow_zero, one_mul, hvv]
      | succ m =>
        exact ⟨(l : WCb l) ^ m * v, by rw [hxe, pow_succ]; ring⟩

end GlobalTheory.SmithOE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCoordinatesOfPrismCover
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.SiteCoord

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ}

theorem comp_assoc {R : Type} [CommRing R] {P₁ P₂ P₃ P₄ : Obj l R} (a : Hom P₃ P₄) (b : Hom P₂ P₃)
    (c : Hom P₁ P₂) : (a.comp b).comp c = a.comp (b.comp c) := Hom.ext' rfl

theorem map_mulVec (S : Strat bk d) {Y Y' : Obj l ↥(OL K)} (k : Hom Y Y') (g₁ g₂ : Hom bk.prism Y)
    (w : Fin d → Y.A) :
    (fun i => k.f ((S.ε g₁ g₂).mulVec w i)) = (S.ε (k.comp g₁) (k.comp g₂)).mulVec fun i => k.f (w i) := by
  funext i
  rw [RingHom.map_mulVec, S.ε_nat]
  rfl

theorem mulVec_map_add {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (M : Matrix (Fin d) (Fin d) A')
    (w w' : Fin d → A) :
    M.mulVec (fun i => φ ((w + w') i)) = M.mulVec (fun i => φ (w i)) + M.mulVec (fun i => φ (w' i)) := by
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp

theorem mulVec_map_smul {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (M : Matrix (Fin d) (Fin d) A')
    (c : A) (w : Fin d → A) : M.mulVec (fun i => φ ((c • w) i)) = φ c • M.mulVec (fun i => φ (w i)) := by
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp

theorem coords_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (h : Hom B C) (f : Hom bk.prism C), Cover h → ∀ (P : Type) [AddCommGroup P] [Module B.A P] (u : P →ₛₗ[h.f] (Fin d → C.A)), (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → ∀ x, (fun i => p.f (u x i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (u x i)) → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ v : P →ₛₗ[a.f] (Fin d → Q.A), ∀ (Q' : Obj l ↥(OL K)) (h' : Hom Q Q') (a' : Hom C Q'), a'.comp h = h'.comp a → ∀ x, (fun i => h'.f (v x i)) = (S.ε (h'.comp g) (a'.comp f)).mulVec fun i => a'.f (u x i) := by
  intro l _ K bk d S B C h f hC P _ _ u hu Q a g
  obtain ⟨Q₀, a₀, h₀, hpo⟩ := hC.stable.po Q a
  have hc₀ : Cover h₀ := (GlobalTheory.T.stable_and_cover_prismHom_of_pushout l _ B C Q Q₀ h a a₀ h₀ hpo).2 hC
  obtain ⟨hinj, hsh⟩ := GlobalTheory.T.prism_cover_injective_and_descent l _ Q Q₀ h₀ hc₀
  obtain ⟨D, p, q, hpq⟩ := hc₀.stable.po Q₀ h₀
  have hcf : ∀ b, a₀.f (h.f b) = h₀.f (a.f b) := fun b => congrArg (fun k : Hom B Q₀ => k.f b) hpo.comm
  obtain ⟨z, hzdef⟩ : ∃ z : P → Fin d → Q₀.A,
      z = fun x => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := ⟨_, rfl⟩
  have hpa : (p.comp a₀).comp h = (q.comp a₀).comp h := by
    rw [comp_assoc p a₀ h, comp_assoc q a₀ h, hpo.comm, ← comp_assoc p h₀ a, ← comp_assoc q h₀ a, hpq.comm]
  have hg : p.comp (h₀.comp g) = q.comp (h₀.comp g) := by rw [← comp_assoc p h₀ g, hpq.comm, comp_assoc q h₀ g]
  have key : ∀ x, (fun i => p.f (z x i)) = fun i => q.f (z x i) := by
    intro x
    have e1 := hu D (p.comp a₀) (q.comp a₀) hpa x
    simp only [comp_assoc] at e1
    have e1' : (fun i => p.f (a₀.f (u x i))) = (S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec
        fun i => q.f (a₀.f (u x i)) := e1
    have e2 := map_mulVec S p (h₀.comp g) (a₀.comp f) (fun i => a₀.f (u x i))
    have e3 := map_mulVec S q (h₀.comp g) (a₀.comp f) (fun i => a₀.f (u x i))
    have hzx : z x = (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := by rw [hzdef]
    calc (fun i => p.f (z x i))
        = fun i => p.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) :=
          congrArg (fun w : Fin d → Q₀.A => fun i => p.f (w i)) hzx
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec fun i => p.f (a₀.f (u x i)) := e2
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec
            ((S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i))) :=
          congrArg (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f))).mulVec e1'
      _ = (S.ε (p.comp (h₀.comp g)) (p.comp (a₀.comp f)) * S.ε (p.comp (a₀.comp f)) (q.comp (a₀.comp f))).mulVec
            fun i => q.f (a₀.f (u x i)) := Matrix.mulVec_mulVec _ _ _
      _ = (S.ε (p.comp (h₀.comp g)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i)) :=
          congrArg (fun M => Matrix.mulVec M fun i => q.f (a₀.f (u x i))) (S.ε_trans _ _ _)
      _ = (S.ε (q.comp (h₀.comp g)) (q.comp (a₀.comp f))).mulVec fun i => q.f (a₀.f (u x i)) :=
          congrArg (fun k => Matrix.mulVec (S.ε k (q.comp (a₀.comp f))) fun i => q.f (a₀.f (u x i))) hg
      _ = fun i => q.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) := e3.symm
      _ = fun i => q.f (z x i) := (congrArg (fun w : Fin d → Q₀.A => fun i => q.f (w i)) hzx).symm
  have hz : ∀ x i, ∃ y, h₀.f y = z x i := fun x i => by
    obtain ⟨y, hy⟩ := hsh D p q hpq (z x i) (congrFun (key x) i)
    exact ⟨y, hy⟩
  choose y hy using hz
  have hzx : ∀ x, z x = (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (u x i) := fun x => congrFun hzdef x
  have z_add : ∀ x x', z (x + x') = z x + z x' := fun x x' =>
    calc z (x + x') = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u (x + x') i)) := hzx _
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f ((u x + u x') i)) :=
          congrArg (fun w : Fin d → C.A => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (w i)) (map_add u x x')
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) +
            (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x' i)) := mulVec_map_add a₀.f _ _ _
      _ = z x + z x' := congrArg₂ (· + ·) (hzx x).symm (hzx x').symm
  have z_smul : ∀ (b : B.A) x, z (b • x) = h₀.f (a.f b) • z x := fun b x =>
    calc z (b • x) = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u (b • x) i)) := hzx _
      _ = (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f ((h.f b • u x) i)) :=
          congrArg (fun w : Fin d → C.A => (S.ε (h₀.comp g) (a₀.comp f)).mulVec fun i => a₀.f (w i))
            (LinearMap.map_smulₛₗ u b x)
      _ = a₀.f (h.f b) • (S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) := mulVec_map_smul a₀.f _ _ _
      _ = h₀.f (a.f b) • z x := congrArg₂ (· • ·) (hcf b) (hzx x).symm
  let v : P →ₛₗ[a.f] (Fin d → Q.A) :=
    { toFun := y
      map_add' := fun x x' => by
        funext i
        apply hinj
        exact calc h₀.f (y (x + x') i) = z (x + x') i := hy _ i
          _ = z x i + z x' i := congrFun (z_add x x') i
          _ = h₀.f (y x i) + h₀.f (y x' i) := congrArg₂ (· + ·) (hy x i).symm (hy x' i).symm
          _ = h₀.f (y x i + y x' i) := (map_add h₀.f _ _).symm
      map_smul' := fun b x => by
        funext i
        apply hinj
        exact calc h₀.f (y (b • x) i) = z (b • x) i := hy _ i
          _ = h₀.f (a.f b) * z x i := congrFun (z_smul b x) i
          _ = h₀.f (a.f b) * h₀.f (y x i) := congrArg (h₀.f (a.f b) * ·) (hy x i).symm
          _ = h₀.f (a.f b * y x i) := (map_mul h₀.f _ _).symm }
  refine ⟨v, ?_⟩
  intro Q' h' a' hcomm x
  have hU := GlobalTheory.T.prismPushoutModAdicPow_universal l _ B C Q Q₀ h a a₀ h₀ hpo Q' a' h' hcomm
  obtain ⟨c, hc, -⟩ := hU
  have e : (fun i => h'.f (v x i)) = fun i => (c.comp h₀).f (y x i) :=
    congrArg (fun k : Hom Q Q' => fun i => k.f (y x i)) hc.2.symm
  have e' : (fun i => (c.comp h₀).f (y x i)) = fun i => c.f (z x i) := by
    funext i
    exact congrArg c.f (hy x i)
  exact calc (fun i => h'.f (v x i)) = fun i => c.f (z x i) := e.trans e'
    _ = fun i => c.f ((S.ε (h₀.comp g) (a₀.comp f)).mulVec (fun i => a₀.f (u x i)) i) :=
        congrArg (fun w : Fin d → Q₀.A => fun i => c.f (w i)) (hzx x)
    _ = (S.ε (c.comp (h₀.comp g)) (c.comp (a₀.comp f))).mulVec fun i => c.f (a₀.f (u x i)) :=
        map_mulVec S c _ _ _
    _ = (S.ε ((c.comp h₀).comp g) ((c.comp a₀).comp f)).mulVec fun i => (c.comp a₀).f (u x i) :=
        congrArg₂ (fun k k' => (S.ε k k').mulVec fun i => c.f (a₀.f (u x i)))
          (comp_assoc c h₀ g).symm (comp_assoc c a₀ f).symm
    _ = (S.ε (h'.comp g) (a'.comp f)).mulVec fun i => a'.f (u x i) :=
        congrArg₂ (fun (k : Hom Q Q') (k' : Hom C Q') => (S.ε (k.comp g) (k'.comp f)).mulVec fun i => k'.f (u x i))
          hc.2 hc.1

end GlobalTheory.BSP.SiteCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumUniversalDeterminantDatumCoeffEqPrimitive
section
open Matrix GlobalTheory.ExportSeries

namespace GlobalTheory.ExportSeries

theorem sum_univCoef_eq_prim : ∀ (k C : Type) [Field k] [Finite k] [AddCommGroup C] [Fintype C] (r n : ℕ), r ≤ n →
    ∀ (β : DetBases k r n) (κ : kˣ →* Multiplicative C) (y : Matrix (Fin r) (Fin n) k), ∑ c, univCoef β κ c y = prim y := by
  intro k C _ _ _ _ r n hrn β κ y
  classical
  letI := Fintype.ofFinite (Planes k r n)

  have hterm : ∀ U : Planes k r n, ∑ c, (univTerm β κ y U).coeff c = if Compl U.1 y then 1 else 0 := by
    intro U
    unfold univTerm
    by_cases h : Compl U.1 y
    · rw [dif_pos h, if_pos h]
      simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    · rw [dif_neg h, if_neg h]
      simp
  have hsum : ∑ c, univCoef β κ c y = ((Nat.card k : ℚ) ^ (r * (n - r)))⁻¹ *
      (Nat.card {U : Planes k r n // Compl U.1 y} : ℚ) := by
    simp only [univCoef, univ, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, AddMonoidAlgebra.coeff_sum,
      Finsupp.finset_sum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl fun U _ => hterm U, Finset.sum_boole]
    congr 2
    rw [Nat.card_eq_fintype_card (α := {U : Planes k r n // Compl U.1 y}), Fintype.card_subtype]
  rw [hsum]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrn
  have ht : r + t - r = t := by omega
  rw [ht]
  set R := Submodule.span k (Set.range y.row) with hR
  have hRle : Module.finrank k R ≤ r := by
    have := finrank_range_le_card (R := k) y.row
    rw [Fintype.card_fin] at this
    exact this
  have hcard : Nat.card {U : Planes k r (r + t) // Compl U.1 y} =
      Nat.card {U : Submodule k (Fin (r + t) → k) // Module.finrank k U = t ∧ R ⊔ U = ⊤} := by
    refine Nat.card_congr ((Equiv.subtypeSubtypeEquivSubtypeInter _ (fun U => Compl U y)).trans
      (Equiv.subtypeEquivRight fun U => ?_))
    simp only [Compl, hR]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  rw [hcard, GlobalTheory.card_subspaces_sup_eq_top k r t R hRle]
  have hq : ((Nat.card k : ℚ) ^ (r * t)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.card_pos.ne')
  have hli : LinearIndependent k y.row ↔ Module.finrank k R = r := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank, eq_comm]
  unfold prim
  by_cases h : Module.finrank k R = r
  · rw [if_pos h, if_pos (hli.2 h)]
    push_cast
    exact inv_mul_cancel₀ hq
  · rw [if_neg h, if_neg (fun h' => h (hli.1 h'))]
    simp

end GlobalTheory.ExportSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaExtensionToCompleteStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_extension_to_complete : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ ψ : GlobalTheory.AcrisK.BK K →+* ℂ_[l],
    ∀ x : AK K, ψ (toB K (ofA K x)) = ((thetaK K x : OC l) : ℂ_[l]) := by
  first | exact @GlobalTheory.AcrisK.exists_thetaB | exact GlobalTheory.AcrisK.exists_thetaB | (intros; apply GlobalTheory.AcrisK.exists_thetaB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfTiltCompatibleSequenceStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_of_tilt_compatible_sequence : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π → ∀ (v : ℕ → OC l) (ω : ℕ → AK K),
    (∀ n, intToOC K π * v (n + 1) + v (n + 1) ^ l ^ fK K = v n) →
    GlobalTheory.LTTilt.IsTiltOf (fK K) (intToOC K π) (red K (ω 0)) v → (∀ n, frobq K (ω (n + 1)) = ω n) →
    frobq K (ω 0) = inO K π * ω 0 + ω 0 ^ l ^ fK K → ∀ n, thetaK K (ω n) = v n := by
  first | exact @GlobalTheory.FrobRoots.thetaK_eq | exact GlobalTheory.FrobRoots.thetaK_eq | (intros; apply GlobalTheory.FrobRoots.thetaK_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLatticeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_expansions_span_full_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → Full (Di (HW l) h T i) (Lat C h T i ζ) := by
  first | exact @GlobalTheory.NL.FullLevel.full_lat | exact GlobalTheory.NL.FullLevel.full_lat | (intros; apply GlobalTheory.NL.FullLevel.full_lat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleSaturatedExactnessCrystallineStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachModule_saturated_exactness_crystalline : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), P6 D HW F := by
  first | exact @GlobalTheory.NL.Exact.exactness_of_N | exact GlobalTheory.NL.Exact.exactness_of_N | (intros; apply GlobalTheory.NL.Exact.exactness_of_N <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNInvQPowGammaStable
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.GamQ

theorem isUnit_one_add {O : Type} [CommRing O] (f : PowerSeries O)
    (hf : PowerSeries.constantCoeff f = 0) : IsUnit (1 + f) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hf]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in

theorem gam_Q_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; let u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)); ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ k : ℕ, (∀ x : W.DD T, W.Q ^ k • x ∈ W.N T → W.Q ^ k • W.γ T x ∈ W.N T) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ w : PowerSeries ↥LL.1, PowerSeries.constantCoeff w = u ^ (-(k : ℤ)) ∧ ∀ (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T) (hγ : W.Q ^ k • W.γ T x ∈ W.N T) (j : ℤ), ex C h T i ζ ⟨W.Q ^ k • W.γ T x, hγ⟩ j = conv w (fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m) j := by
  intro D HW F Cm l _ K s LL h W C u T hT k
  obtain ⟨χ, -, -, hγ₀, -, hQ, -, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨b, hb⟩ := ((GlobalTheory.Cyc.XX_QQ_properties l ↥(OL LL) s h.1).2.2.2.2.2.1 (χ W.gam)).2
  let U : AA K LL := fun _ => 1 + GlobalTheory.Cyc.XX l ↥(OL LL) s * b
  have hγQ : W.γA W.gam W.Q = W.Q * U := by
    funext i
    show W.γ₀ W.gam (W.Q i) = W.Q i * U i
    rw [hγ₀, hQ]
    exact hb
  have hUu : IsUnit U := Pi.isUnit_iff.2 fun _ => isUnit_one_add _ (by simp [GlobalTheory.Cyc.XX])
  have hγs : ∀ (a : AA K LL) (y : W.DD T), W.γ T (a • y) = W.γA W.gam a • W.γ T y := by
    intro a y
    have := W.γD_smul T W.gam (algebraMap (AA K LL) W.EE a) y
    rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
    exact this
  let v : AA K LL := ((hUu.unit ^ k)⁻¹ : (AA K LL)ˣ)
  have hvU : v * U ^ k = 1 := by
    show (((hUu.unit ^ k)⁻¹ : (AA K LL)ˣ) : AA K LL) * U ^ k = 1
    have e : U ^ k = ((hUu.unit ^ k : (AA K LL)ˣ) : AA K LL) := by
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rw [e, Units.inv_mul]
  have key : ∀ y : W.DD T, W.Q ^ k • W.γ T y = v • W.γ T (W.Q ^ k • y) := by
    intro y
    rw [hγs, map_pow, hγQ, mul_pow, smul_smul, mul_left_comm, hvU, mul_one]
  refine ⟨fun x hx => ?_, fun i ζ hζ => ?_⟩
  · rw [key]
    exact (W.N T).smul_mem v (W.N_Γ T W.gam _ hx)
  have hfull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ
  have hlev := (GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hζ⟩ hfull).1
  refine ⟨W.lev i ζ v, ?_, fun x hx hγ j => ?_⟩
  · have hg := W.gam_gen
    rw [(HW l).W_s] at hg
    have hΓ := ((Cm l).C K s LL h).tie.lev_Γ W.gam i ζ ζ s 1
      (by rw [(D.loc l).PD_p]; exact hζ) (by rw [Nat.cast_one]; exact hg.ge) (pow_one ζ).symm W.Q
    have hΓ' : W.lev i ζ W.Q * W.lev i ζ U = PowerSeries.rescale u (W.lev i ζ W.Q) := by
      rw [← map_mul, ← hγQ]; exact hΓ
    obtain ⟨w0, hw0, hQw⟩ := ((GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hζ⟩).2.2.2.1 hζ).1
    rw [hQw, map_mul, PowerSeries.rescale_X] at hΓ'
    have h1 : w0 * W.lev i ζ U = PowerSeries.C u * PowerSeries.rescale u w0 := by
      apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ↥LL.1))
      linear_combination hΓ'
    have h2 := congrArg (PowerSeries.coeff 0) h1
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_mul] at h2
    have hw0c : PowerSeries.constantCoeff w0 ≠ 0 := (hw0.map PowerSeries.constantCoeff).ne_zero
    have hUc : PowerSeries.constantCoeff (W.lev i ζ U) = u := by
      apply mul_left_cancel₀ hw0c
      rw [h2, mul_comm]
    have h3 := congrArg PowerSeries.constantCoeff (congrArg (W.lev i ζ) hvU)
    rw [map_mul, map_pow, map_one, map_mul, map_pow, map_one, hUc] at h3
    rw [zpow_neg, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left h3
  · have e1 : (⟨W.Q ^ k • W.γ T x, hγ⟩ : ↥(W.N T)) =
        v • (⟨W.γD T W.gam (W.Q ^ k • x), W.N_Γ T W.gam _ hx⟩ : ↥(W.N T)) :=
      Subtype.ext (key x)
    have e2 : ex C h T i ζ ⟨W.γD T W.gam (W.Q ^ k • x), W.N_Γ T W.gam _ hx⟩ =
        fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m :=
      funext fun m => GlobalTheory.NL.GradedLat.ex_gam C h T hT i ζ hζ.pow_eq_one ⟨W.Q ^ k • x, hx⟩ m
    rw [e1, hlev, e2]

end GlobalTheory.NL.GamQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionCuspidalGreenDegreeEqOneStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerDimension_cuspidal_greenDegree_eq_one : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (d : ℕ) (χ : Gn g d → ℂ), IsCusp χ → χ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) → wh ψ χ = 1 := by
  first | exact @GlobalTheory.GLq.wh_cusp_eq_one | exact GlobalTheory.GLq.wh_cusp_eq_one | (intros; apply GlobalTheory.GLq.wh_cusp_eq_one <;> assumption)
end

