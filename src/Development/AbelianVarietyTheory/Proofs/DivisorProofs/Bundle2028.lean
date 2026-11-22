import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.ExtEmbEquivComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2022
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0061

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
section
set_option autoImplicit false

noncomputable section

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC

namespace GlobalTheory.DeepLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isGalois_of_aut (K L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ L] (j : K →+* L)
    (hj : ∀ a : K, ((j a : L) : ℂ) = a)
    (hs : ∀ s : ℂ ≃+* ℂ, (∀ a ∈ K, s a = a) → ∀ a ∈ L, s a ∈ L) :
    letI : Algebra K L := j.toAlgebra
    IsGalois K L := by
  letI : Algebra K L := j.toAlgebra
  haveI : IsScalarTower K L ℂ := IsScalarTower.of_algebraMap_eq fun a => (hj a).symm
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun a => by simp
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  have : Normal K L := by
    refine normal_iff.2 fun x => ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
    refine Polynomial.Splits.of_splits_map (algebraMap L ℂ) (IsAlgClosed.splits _) fun a ha => ?_
    have hroot : a ∈ (minpoly K x).rootSet ℂ := by
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at ha
      exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 ha)
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hroot
    obtain ⟨φ, rfl⟩ := hroot
    obtain ⟨s, hsφ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.extendEmb_holds L inferInstance (φ.restrictScalars ℚ)
    have hfix : ∀ a ∈ K, s a = a := by
      intro a ha
      have h1 := hsφ (j ⟨a, ha⟩)
      rw [hj] at h1
      refine h1.trans ?_
      exact φ.commutes (⟨a, ha⟩ : K)
    have hmem : s (x : ℂ) ∈ L := hs s hfix _ x.2
    refine ⟨⟨s (x : ℂ), hmem⟩, ?_⟩
    exact hsφ x
  exact IsGalois.mk

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l}

theorem frPt_eq {S : Type} [CommRing S] [Algebra c.F S] {y z : FrPt Xo c S} (hx : y.x = z.x) (hu : y.u = z.u)
    (hs : HEq y.s z.s) : y = z := by
  obtain ⟨x, xo, u, t, e, b, s, g⟩ := y
  obtain ⟨x', xo', u', t', e', b', s', g'⟩ := z
  obtain rfl : x = x' := hx
  obtain rfl : u = u' := hu
  obtain rfl : s = s' := eq_of_heq hs
  rfl

theorem laws_galois_pull : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → (∀ σ, GoodEmb Y.d.c₂ σ → ∀ g τ k, ‖dmin ((Y.U σ).X (Y.dict σ g).1).Gm (Y.dict σ g).2 τ k‖ = 1) → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((Y.U σ).X k)) → Laws D j Y.d.Xo₂ Y.d.c₂ Y.U Y.dict ∧ (letI : Algebra T.Q.c.F Y.d.c₂.F := ((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle)).toAlgebra; IsGalois T.Q.c.F Y.d.c₂.F) ∧ ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec (T.Q.Xo j) T.Q.c a n, ∀ g, Y.Pull f g ↔ Pull Y.d (rulBC Y.hle f) g := by
  intro D T j Y e o hJ hj hG hdm hmod
  refine ⟨?_, ?_, ?_⟩
  · exact
      { inR := hj
        host := hJ.pins.1
        dat := hJ.pins.2.2.2 j hj
        levA := hG.lev.2
        unf := hG.unf
        chiTriv := hG.chiTriv
        dictU := fun σ hσ => by
          obtain ⟨th, hr, h1, h2⟩ := hG.dictU σ hσ
          refine ⟨Y.Kf, th, hr, ?_, h1, h2, hdm σ hσ⟩
          have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by
            rw [hG.lev.1.2.1, hJ.pins.2.1.1]
          rw [hM]
          exact hG.levelK
        modelW := hmod }
  · haveI := Y.d.c₂.fin
    refine isGalois_of_aut T.Q.c.F Y.d.c₂.F _ (fun a => rfl) fun s hs a ha => ?_
    have hF := Y.d.hF
    rw [hF] at ha ⊢
    exact hG.normal s hs a ha
  · intro a n f hf g
    have hV := (rulBC_sec_val_linear D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c Y.c' Y.hle).1 a n f hf
    constructor
    · intro hP k _ _ _ _ hk y₂ y hO
      letI : Algebra T.Q.c.F k := resAlg Y.hle k
      have hA : AlgOver T.Q.c Y.c' Y.hle k := fun _ => rfl
      rw [hV.2 k hA y]
      exact hP k hA hk y₂ y (y.res Y.hle hA) hO rfl rfl HEq.rfl
    · intro hP k _ _ _ _ _ hA hk y₂ y' y hO hx hu hs
      have hy : y = y'.res Y.hle hA := frPt_eq hx hu hs
      rw [hy, ← hV.2 k hA y']
      exact hP k hk y₂ y' hO

end GlobalTheory.DeepLaws

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledStabilizerWeilOperatorTransportsLatticeEi
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacTransport

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cols_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : Pl F)
    (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))
    (hh : ∀ z ∈ GlobalTheory.DblVac.latD X v, h *ᵥ z ∈ GlobalTheory.DblVac.latD X v)
    {w₁ w₂ : Matrix (Fin n) (Fin d) (AE F E)} (hw₁ : w₁ ∈ latAtV X Y v) (hw₂ : w₂ ∈ latAtV X Y v) :
    ((Matrix.fromCols w₁ᵀ w₂ᵀ * hᵀ).toCols₁)ᵀ ∈ latAtV X Y v ∧
      ((Matrix.fromCols w₁ᵀ w₂ᵀ * hᵀ).toCols₂)ᵀ ∈ latAtV X Y v := by
  let T₁ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => ((γ * hᵀ).toCols₁)ᵀ
      map_zero' := by ext i j; simp [Matrix.toCols₁]
      map_add' := fun γ γ' => by ext i j; simp [Matrix.toCols₁, Matrix.add_mul] }
  let T₂ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => ((γ * hᵀ).toCols₂)ᵀ
      map_zero' := by ext i j; simp [Matrix.toCols₂]
      map_add' := fun γ γ' => by ext i j; simp [Matrix.toCols₂, Matrix.add_mul] }
  let S := (latAtV X Y v).comap T₁ ⊓ (latAtV X Y v).comap T₂
  have key : ∀ y ∈ Y.L, ∀ z ∈ GlobalTheory.DblVac.latD X v,
      Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z ∈ S := by
    intro y hy z hz
    have hz' := hh z hz
    refine ⟨?_, ?_⟩
    · show ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₁)ᵀ ∈ latAtV X Y v
      have e : ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₁)ᵀ =
          Matrix.vecMulVec ((h *ᵥ z) ∘ Sum.inl) (fun i => inclR (F := F) (AF F) (y i)) := by
        rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
        ext i j
        simp [Matrix.toCols₁, Matrix.vecMulVec_apply, mul_comm]
      rw [e]
      exact GlobalTheory.VacTransportLeft.vecMulVec_mem_left X Y v hy hz'.1
    · show ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₂)ᵀ ∈ latAtV X Y v
      have e : ((Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i)) z * hᵀ).toCols₂)ᵀ =
          Matrix.vecMulVec ((h *ᵥ z) ∘ Sum.inr) (fun i => inclR (F := F) (AF F) (y i)) := by
        rw [Matrix.vecMulVec_mul, Matrix.vecMul_transpose]
        ext i j
        simp [Matrix.toCols₂, Matrix.vecMulVec_apply, mul_comm]
      rw [e]
      exact GlobalTheory.VacTransportLeft.vecMulVec_mem_left X Y v hy hz'.2
  let A₁ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    { toFun := fun w => Matrix.fromCols wᵀ 0
      map_zero' := by ext i j; cases j <;> simp
      map_add' := fun w w' => by ext i j; cases j <;> simp }
  let A₂ : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) :=
    { toFun := fun w => Matrix.fromCols 0 wᵀ
      map_zero' := by ext i j; cases j <;> simp
      map_add' := fun w w' => by ext i j; cases j <;> simp }
  have hA₁ : latAtV X Y v ≤ S.comap A₁ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    have e : A₁ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i))
        (Sum.elim (a • fun i => inclR (F := F) (AF F) (x i)) 0) := by
      ext i j
      cases j with
      | inl j =>
        simp only [A₁, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.fromCols_apply_inl, Matrix.transpose_apply,
          Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, Sum.elim_inl, Pi.smul_apply, map_mul,
          Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
        ring
      | inr j => simp [A₁, Matrix.vecMulVec_apply]
    show A₁ _ ∈ S
    rw [e]
    refine key y hy _ ⟨?_, ?_⟩
    · rw [Sum.elim_comp_inl]; exact AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
    · rw [Sum.elim_comp_inr]; exact zero_mem _
  have hA₂ : latAtV X Y v ≤ S.comap A₂ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    have e : A₂ (a • incM F (Matrix.vecMulVec x y)) = Matrix.vecMulVec (fun i => inclR (F := F) (AF F) (y i))
        (Sum.elim 0 (a • fun i => inclR (F := F) (AF F) (x i))) := by
      ext i j
      cases j with
      | inl j => simp [A₂, Matrix.vecMulVec_apply]
      | inr j =>
        simp only [A₂, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.fromCols_apply_inr, Matrix.transpose_apply,
          Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, Sum.elim_inr, Pi.smul_apply, map_mul,
          Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
        ring
    show A₂ _ ∈ S
    rw [e]
    refine key y hy _ ⟨?_, ?_⟩
    · rw [Sum.elim_comp_inl]; exact zero_mem _
    · rw [Sum.elim_comp_inr]; exact AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
  have hsum : Matrix.fromCols w₁ᵀ w₂ᵀ = A₁ w₁ + A₂ w₂ := by
    ext i j; cases j <;> simp [A₁, A₂]
  have hm : Matrix.fromCols w₁ᵀ w₂ᵀ ∈ S := hsum ▸ add_mem (hA₁ hw₁) (hA₂ hw₂)
  exact ⟨hm.1, hm.2⟩

theorem transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (cA σ) (-1 : AE F E) (incM F G.W.J) (incM F G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V.J) (incM F G.W.J) γ γ) • G.M.vac v)) →
    ∀ (omd : GlobalTheory.DblVac.UD σ G.V →* Module.End ℂ (((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → AF F) → ℂ)),
    IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1 : AE F E) (incM F G.W.J) (dbl (incM F G.V.J)) dd (X.β / X.α) (diagCols (Fin a)) omd →
    ∀ g ∈ GlobalTheory.DblVac.KD σ G.V v, ∀ φ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v), ∀ φ₁ ∈ SB ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')) → Fv F v),
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ)) → Acts (evFin F v) (omd g) φ φ₁ →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) φ₁
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J) (dbl (incM F G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' _ v w _ _ d' _ dd _ θ _ _ omd hsp g hg φ hφ φ₁ _ hfix hact w₁ hw₁ w₂ hw₂ r hr
  by_cases h0 : φ₁ = 0
  · subst h0
    funext x
    simp [Darboux.rho, schr, tens]
  have hr' : Rest (evFin F v) φ r := GlobalTheory.RestCofactor.rest_of_rest v φ₁ φ r h0 hφ hr
  obtain ⟨h1m, h2m⟩ := cols_mem G.V G.W v (GlobalTheory.DblVac.matD g⁻¹) (fun z hz => (hg.2 z hz).2) hw₁ hw₂
  have hsplit : Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ =
      Matrix.fromCols (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₁)ᵀ)ᵀ
        (((Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ).toCols₂)ᵀ)ᵀ := by
    rw [Matrix.transpose_transpose, Matrix.transpose_transpose, Matrix.fromCols_toCols]
  have hback : actB (cA σ) g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) = Matrix.fromCols w₁ᵀ w₂ᵀ := by
    change Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ * (GlobalTheory.DblVac.matD g)ᵀ = _
    have e : GlobalTheory.DblVac.matD g * GlobalTheory.DblVac.matD g⁻¹ = 1 := Units.mul_inv g.1
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, e, Matrix.transpose_one, Matrix.mul_one]
  have hsy := GlobalTheory.VacTransport.symp_mul_transpose (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.W.J)
    (dbl (incM F G.V.J)) (GlobalTheory.DblVac.matD g⁻¹) (g⁻¹).2 (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)
  have hf := hfix _ h1m _ h2m r hr'
  rw [← hsplit, hsy] at hf
  have h1 := hsp.2.1.impl g (Matrix.fromCols w₁ᵀ w₂ᵀ * (GlobalTheory.DblVac.matD g⁻¹)ᵀ) _ hr'.2
  rw [hback, hf, GlobalTheory.VacTransport.tens_smul, map_smul, hact r hr'] at h1
  rw [← h1, GlobalTheory.VacTransport.tens_smul]

end GlobalTheory.DblVacTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingIntegrandIntegrableOfCoefficientConstCom
section
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section
namespace GlobalTheory.RatioConst

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont Formalism.L2.Pj in

theorem rcoef_one_const {D : D7} {A : HSp D} (m : Measure (GA D A)) (g : GA D A) :
    GlobalTheory.Core.Rk.IP.rcoef m (fun _ => (1 : ℂ)) (fun _ => 1) g = (volQ A m : ℂ) := by
  simp [GlobalTheory.Core.Rk.IP.rcoef, petersson, pet, rTr, AutomorphicL2Unitary.descend, volQ, autMeasure, integral_const]

theorem integral_const_coef : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  IsSelfDualC X.A (stdLat X.A) → (∀ x, x ∈ intG D P.a ↔ X.ιA x ∈ openOff X.A (stdLat X.A) ∅) →
  ∀ (a : GL (Fin X.A.rank) (AE D)) (ν : Measure (WO X.A X.B)) (𝓕 : Set (WO X.A X.B)), GlobalTheory.Doubling.IsMaj X.A a →
  ∀ (Sf : Finset (FinPl D)) (Φ : WO X.A X.B → ℂ) (c : ℂ),
    (∀ x ∈ intG D P.a, ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = c) →
    (∀ x, x ∉ intG D P.a → X.ιA x ∈ openOff X.A (stdLat X.A) Sf → ∀ k ∈ GinfC X.A, wcoef X.om ν 𝓕 Φ Φ (X.ιA x * k) = 0) →
    (∀ s : ℂ, IntegrableOn (integrand X.om X.m ν 𝓕 (stdLat X.A) a Φ Φ (fun _ => 1) (fun _ => 1) s) (openOff X.A (stdLat X.A) Sf) X.m) ∧
      ∫ g in openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g ∂X.m = c := by
  intro D cc δ t0 Q P X hX hL hint a ν 𝓕 ha Sf Φ c hc h0
  have hF := hX.1
  haveI := hF.haarA
  set K : Set (GA D X.A) := openOff X.A (stdLat X.A) ∅ with hKdef
  have hdec : ∀ g : GA D X.A, ∃ x k, k ∈ GinfC X.A ∧ g = X.ιA x * k := by
    intro g
    obtain ⟨h, hh, k, hk, rfl⟩ := Formalism.IndefR.TopMult.ga_decomp g
    rw [← hF.rangeA] at hh
    obtain ⟨x, rfl⟩ := hh
    exact ⟨x, k, hk, rfl⟩
  have hproj : ∀ k ∈ GinfC X.A, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v k = 1 := by
    intro k hk v
    show GlobalTheory.AdelicU.proj D.sp.cm.sig X.A.gram v ((⟨k, hk⟩ : GinfC X.A) : GA D X.A) = 1
    rw [← GlobalTheory.AutMult.toInf_coe (⟨k, hk⟩ : GinfC X.A)]
    exact GlobalTheory.AdelicU.proj_ofInf _ _ v _
  have hfin : ∀ k ∈ GinfC X.A, Lev.finE X.A k = 1 := by
    intro k hk
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom X.A k = 1 from hk, map_one]
  have hmem : ∀ x k S, k ∈ GinfC X.A →
      (X.ιA x * k ∈ openOff X.A (stdLat X.A) S ↔ X.ιA x ∈ openOff X.A (stdLat X.A) S) := by
    intro x k S hk
    simp only [GlobalTheory.Core.Rk.IP.openOff, Set.mem_setOf_eq, map_mul, hproj k hk, mul_one]
  have hw : ∀ g ∈ openOff X.A (stdLat X.A) Sf, wcoef X.om ν 𝓕 Φ Φ g = K.indicator (fun _ => c) g := by
    intro g hg
    obtain ⟨x, k, hk, rfl⟩ := hdec g
    by_cases hx : x ∈ intG D P.a
    · rw [Set.indicator_of_mem ((hmem x k ∅ hk).2 ((hint x).1 hx)), hc x hx k hk]
    · rw [Set.indicator_of_notMem (fun h => hx ((hint x).2 ((hmem x k ∅ hk).1 h))),
        h0 x hx ((hmem x k Sf hk).1 hg) k hk]
  have hKsub : K ⊆ openOff X.A (stdLat X.A) Sf := fun g hg v _ => hg v (Finset.notMem_empty v)
  have hKm : MeasurableSet K := (GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL ∅).measurableSet
  have hSm : MeasurableSet (openOff X.A (stdLat X.A) Sf) :=
    (GlobalTheory.Core.Rk.IP.isOpen_openOff X.A (stdLat X.A) hL Sf).measurableSet
  have hKeq : K = ((X.KA.comap (Lev.finE X.A) : Subgroup (GA D X.A)) : Set (GA D X.A)) := by
    ext g
    obtain ⟨x, k, hk, rfl⟩ := hdec g
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one, hF.levA_iff, hint, hKdef, hmem x k ∅ hk]
  have hKvol : X.m K = 1 := by
    rw [hKeq]; exact GlobalTheory.Mass.Levels.measure_comap_finE hF.measA.choose_spec.1
  have hKc : IsCompact K := by
    have hG : IsCompact (GinfC X.A : Set (GA D X.A)) :=
      GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one D X.A hF.gramA
    refine (hF.levA.2.mul hG).of_isClosed_subset ?_ ?_
    · rw [hKeq]; exact Subgroup.isClosed_of_isOpen _ hF.levA.1
    · intro g hg
      obtain ⟨x, k, hk, rfl⟩ := hdec g
      rw [hKeq, SetLike.mem_coe, Subgroup.mem_comap, map_mul, hfin k hk, mul_one] at hg
      refine Set.mul_mem_mul ?_ hk
      exact Formalism.IndefR.Lev.mem_levA.2 ⟨hF.rangeA ▸ ⟨x, rfl⟩, hg⟩
  obtain ⟨hcont, hpos, -⟩ := GlobalTheory.Core.Rk.IP.hgtL_props D X.A (stdLat X.A) a hL ha
  refine ⟨fun s => ?_, ?_⟩
  · let F : GA D X.A → ℂ := fun g => c * GlobalTheory.Doubling.npow (GlobalTheory.Core.Rk.IP.hgtL X.A (stdLat X.A) a g)
        (s - GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero X.A X.B) * (volQ X.A X.m : ℂ)
    have hFc : Continuous F := by
      refine (continuous_const.mul ?_).mul continuous_const
      simp only [GlobalTheory.Doubling.npow]
      refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp hcont)).cpow continuous_const fun g => ?_
      exact Complex.ofReal_mem_slitPlane.2 (by exact_mod_cast (hpos g).1)
    have hI : Integrable (K.indicator F) X.m :=
      (integrable_indicator_iff hKm).2 (hFc.continuousOn.integrableOn_compact' hKc hKm)
    refine hI.integrableOn.congr_fun (fun g hg => ?_) hSm
    have hr : GlobalTheory.Core.Rk.IP.rcoef X.m (fun _ : GA D X.A => (1 : ℂ)) (fun _ => 1) g = (volQ X.A X.m : ℂ) := by
      exact rcoef_one_const X.m g
    simp only [integrand, hr, hw g hg]
    by_cases hgK : g ∈ K
    · simp [Set.indicator_of_mem hgK, F]
    · simp [Set.indicator_of_notMem hgK]
  · rw [setIntegral_congr_fun hSm hw, integral_indicator hKm, Measure.restrict_restrict hKm,
      Set.inter_eq_left.2 hKsub, setIntegral_const, measureReal_def, hKvol]
    simp

end GlobalTheory.RatioConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenlatticeLocalContainmentAtPairs
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OnRankAlg

section Gen

variable {K : Type} [Field K] [NumberField K]
variable {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

theorem exists_smul_mem_of_mem_span {A : Submodule (𝓞 K) Z} {x : Z} (hx : x ∈ Submodule.span K (A : Set Z)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.TargetLemmaCollection.target
  | exact _root_.GlobalTheory.TargetLemmaCollection.target
  | (apply _root_.GlobalTheory.TargetLemmaCollection.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetLemmaCollection.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetLemmaCollection.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetLemmaCollection.target ..)

theorem span_cut {A : Submodule (𝓞 K) Z} (hA : Submodule.span K (A : Set Z) = ⊤) (W : Submodule K Z) :
    Submodule.span K (Formalism.EigenvalueLevelCeiling.cut W A : Set Z) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.1 hx).2
  · intro w hw
    obtain ⟨d, hd, hm⟩ := exists_smul_mem_of_mem_span (A := A) (x := w) (by rw [hA]; trivial)
    have hd' : algebraMap (𝓞 K) K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd
    have hmem : d • w ∈ Formalism.EigenvalueLevelCeiling.cut W A := by
      refine Submodule.mem_inf.2 ⟨hm, ?_⟩
      show d • w ∈ W
      rw [← algebraMap_smul K d w]
      exact W.smul_mem _ hw
    have hw' : w = (algebraMap (𝓞 K) K d)⁻¹ • (d • w) := by
      rw [← algebraMap_smul K d w, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hw']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem span_le_span_sc {a : K} (ha : a ≠ 0) (A : Submodule (𝓞 K) Z) :
    Submodule.span K (A : Set Z) ≤ Submodule.span K (Formalism.EigenvalueLevelCeiling.sc a A : Set Z) := by
  rw [Submodule.span_le]
  intro y hy
  have hm : a • y ∈ Formalism.EigenvalueLevelCeiling.sc a A := Submodule.mem_map.2 ⟨y, hy, rfl⟩
  have hy' : y = a⁻¹ • (a • y) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hy']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem locP_subset_span (v : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) Z) :
    (Formalism.HermitianLatticesTheory.localization₂ v.asIdeal L : Set Z) ⊆ Submodule.span K (L : Set Z) := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.asIdeal.zero_mem)
  have hs' : algebraMap (𝓞 K) K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hs0
  have hx' : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
    rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs', one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)

variable {P : Type} [Group P]

theorem mem_eig_iff (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (x : Z) :
    x ∈ Formalism.EigenvalueLevelCeiling.eig ρ U ψ ↔ ∀ u : U, ρ u x = ((ψ u : 𝓞 K) : K) • x := by
  unfold Formalism.EigenvalueLevelCeiling.eig
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem map_eig (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (e : Z →ₗ[K] Z) (V₀ : Submodule K Z)
    (hp : e ∘ₗ e = e ∧ LinearMap.range e = V₀) (hc : ∀ g : P, e ∘ₗ ρ g = ρ g ∘ₗ e) :
    (Formalism.EigenvalueLevelCeiling.eig ρ U ψ).map e = Formalism.EigenvalueLevelCeiling.eig ρ U ψ ⊓ V₀ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.2 ⟨(mem_eig_iff ρ U ψ _).2 fun u => ?_, by rw [← hp.2]; exact LinearMap.mem_range_self e x⟩
    have h := congrArg (fun f : Z →ₗ[K] Z => f x) (hc u)
    simp only [LinearMap.comp_apply] at h
    rw [← h, (mem_eig_iff ρ U ψ x).1 hx u, map_smul]
  · intro x hx
    obtain ⟨hx, hv⟩ := Submodule.mem_inf.1 hx
    rw [← hp.2] at hv
    obtain ⟨y, rfl⟩ := hv
    exact ⟨e y, hx, congrArg (fun f : Z →ₗ[K] Z => f y) hp.1⟩

theorem isLatIn_map (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (e : Z →ₗ[K] Z) (V₀ : Submodule K Z)
    (hp : e ∘ₗ e = e ∧ LinearMap.range e = V₀) (hc : ∀ g : P, e ∘ₗ ρ g = ρ g ∘ₗ e) {A : Submodule (𝓞 K) Z}
    (hfg : A.FG) (hle : A ≤ (Formalism.EigenvalueLevelCeiling.eig ρ U ψ).restrictScalars (𝓞 K))
    (hge : (Formalism.EigenvalueLevelCeiling.eig ρ U ψ : Set Z) ⊆ Submodule.span K (A : Set Z)) :
    Formalism.EigenvalueLevelCeiling.IsLatIn (Formalism.EigenvalueLevelCeiling.eig ρ U ψ ⊓ V₀) (A.map (e.restrictScalars (𝓞 K))) := by
  refine ⟨hfg.map _, ?_⟩
  have hs : Submodule.span K (A : Set Z) = Formalism.EigenvalueLevelCeiling.eig ρ U ψ :=
    le_antisymm (Submodule.span_le.2 fun x hx => hle hx) hge
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hs, map_eig ρ U ψ e V₀ hp hc]

end Gen

theorem rankAtPlaces_alg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (c : OnConst) (O : OnObj S P c), LeafSpan O → LeafData O → LeafProj O → (∀ j (g : P), O.e j ∘ₗ O.ρ j g = O.ρ j g ∘ₗ O.e j) → (AtPair S fun v => ∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) → RankAtPlaces O := by
  intro K _ _ _ Bs Df S P _ _ c O hSp hD hPr hc hJ w hw
  have one : ∀ v : HeightOneSpectrum (𝓞 K),
      (∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Th v j) ∧ Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.ThK v j)) →
      (∀ j, (O.Th0 v j).FG ∧ O.Th0 v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
        Formalism.EigenvalueLevelCeiling.sc ((Nat.card O.U : ℕ) : K) (Formalism.EigenvalueLevelCeiling.cut (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ) (O.ThK v j)) ≤ O.Th0 v j) →
      (∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
        Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) →
      ∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
        Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j) := by
    intro v hs hd hj j
    have hU : ((Nat.card O.U : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have h0 : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ : Set (Fin (O.nZ j) → K)) ⊆ (Submodule.span K (O.Th0 v j : Set (Fin (O.nZ j) → K)) : Set (Fin (O.nZ j) → K)) := by
      intro x hx
      have h1 : x ∈ Submodule.span K (Formalism.EigenvalueLevelCeiling.cut (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ) (O.ThK v j) : Set (Fin (O.nZ j) → K)) := by
        rw [span_cut (hs j).2.2]; exact hx
      exact Submodule.span_mono (fun y hy => (hd j).2.2 hy) (span_le_span_sc hU _ h1)
    have hJs : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ : Set (Fin (O.nZ j) → K)) ⊆ (Submodule.span K (O.ThJ v j : Set (Fin (O.nZ j) → K)) : Set (Fin (O.nZ j) → K)) := by
      intro x hx
      exact Submodule.span_le.2 (fun y hy => locP_subset_span v _ ((hj j).2.2 (Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hy))) (h0 hx)
    exact ⟨isLatIn_map (O.ρ j) O.U O.ψ (O.e j) (O.V₀ j) (hPr j) (hc j) (hd j).1 (hd j).2.1 h0,
      isLatIn_map (O.ρ j) O.U O.ψ (O.e j) (O.V₀ j) (hPr j) (hc j) (hj j).1 (hj j).2.1 hJs, (hj j).2.2⟩
  exact ⟨one w (hSp w hw).1 (hD w hw).1 (hJ w hw).1, one _ (hSp w hw).2 (hD w hw).2 (hJ w hw).2⟩

end GlobalTheory.OnRankAlg

end
end

