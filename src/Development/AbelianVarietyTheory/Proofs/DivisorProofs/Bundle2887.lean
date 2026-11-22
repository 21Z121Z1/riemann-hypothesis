import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2832
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1272
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2687

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGeneratorPullbackRule
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult

theorem tensorEval_includeRight_comp {R₀ A B : Type} [CommRing R₀] [CommRing A] [CommRing B] (ρ : A →+* B)
    (d : R₀ ⊗[ℤ] A) :
    tensorEval ((Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := B)).toRingHom.comp ρ) d =
      TensorProduct.comm ℤ B R₀
        (LinearMap.rTensor R₀ ρ.toAddMonoidHom.toIntLinearMap (TensorProduct.comm ℤ R₀ A d)) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    simp [tensorEval_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isChartFun_unique : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {N : ℕ} {M : Scheme.{0}}
    {s : M ⟶ Sp (Localization.Away (N : ℤ))} {U : Obj F 𝔠 M} {α : U.Level N} {V : M.Opens},
    IsDPModel N s U α V → ∀ {R₀ : Type} [CommRing R₀] {k : ℕ} (r₀ : Rule (rapObj 𝔠) R₀ k)
    {W : M.Opens} (hW : IsAffineOpen W) {Y : Obj F 𝔠 (Sp Γ(M, W))} {φY : Y.A.left ⟶ U.A.left}, Y.IsPullBy U hW.fromSpec φY →
    ∀ {δY : Y.DetGen} {h h' : R₀ ⊗[ℤ] Γ(M, W)}, IsChartFun r₀ Y δY h → IsChartFun r₀ Y δY h' → h = h' := by
  intro F _ _ 𝔠 N M s U α V hDP R₀ _ k r₀ W hW Y φY hY δY h h' hh hh'
  obtain ⟨-, -, hflat, hV, hnorm, hcod⟩ := hDP
  rw [← sub_eq_zero]
  have key := rTensor_eq_zero_of_restrict_affine_inf N M s V hflat hnorm hcod W hW R₀
    (TensorProduct.comm ℤ R₀ Γ(M, W) (h - h')) ?_
  · exact (TensorProduct.comm ℤ R₀ Γ(M, W)).map_eq_zero_iff.1 key
  intro W' hW' hle
  let ρ : Γ(M, W) →+* Γ(M, W') := (M.presheaf.map (homOfLE (hle.trans inf_le_left)).op).hom
  let ψ : Γ(M, W) →+* R₀ ⊗[ℤ] Γ(M, W') :=
    (Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := Γ(M, W'))).toRingHom.comp ρ
  obtain ⟨X, φ, hX⟩ := Obj.exists_isPullBy Y (spMap ψ)
  obtain ⟨δ, hδ, -⟩ := hX.existsUnique_detGen ψ δY

  have hmap : spMap ψ ≫ hW.fromSpec =
      spMap (Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := Γ(M, W'))).toRingHom ≫ hW'.fromSpec := by
    rw [← hW.map_fromSpec hW' (homOfLE (hle.trans inf_le_left)).op]
    simp [ψ, ρ, spMap, Spec.map_comp]
  have hXr : X.IsRapoport := by
    rw [Obj.isRapoport_iff]
    refine Set.eq_univ_of_forall fun x K _ t hx Z χ hZ ↦ ?_
    have hZU : Z.IsPullBy U (t ≫ spMap ψ ≫ hW.fromSpec) (χ ≫ φ ≫ φY) := hZ.comp (hX.comp hY)
    obtain ⟨z, rfl⟩ := hx
    have hmem : (t ≫ spMap ψ ≫ hW.fromSpec) z ∈ (V : Set M) := by
      rw [hmap]
      have : (hW'.fromSpec) ((t ≫ spMap (Algebra.TensorProduct.includeRight (R := ℤ) (A := R₀) (B := Γ(M, W'))).toRingHom) z) ∈ (W' : Set M) := by
        rw [← hW'.range_fromSpec]; exact ⟨_, rfl⟩
      exact (hle.trans inf_le_right) (by simpa using this)
    rw [hV] at hmem
    exact hmem K _ ⟨z, rfl⟩ Z _ hZU
  have e1 := hh _ ψ X φ hXr δ hX hδ
  have e2 := hh' _ ψ X φ hXr δ hX hδ
  have e : tensorEval ψ (h - h') = 0 := by rw [map_sub, ← e1, ← e2, sub_self]
  rw [tensorEval_includeRight_comp, LinearEquiv.map_eq_zero_iff] at e
  exact e

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantGeneratorLocallyExists
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.RealMult.LocalGen

theorem exists_basis_away {A : Type} [CommRing A] (L : Type) [AddCommGroup L] [Module A L] [Module.Finite A L]
    [Module.Projective A L] (p : PrimeSpectrum A) (n : ℕ) (hn : Module.rankAtStalk (R := A) L p = n) :
    ∃ g : A, g ∉ p.asIdeal ∧ ∀ (B : Type) [CommRing B] [Algebra A B], IsUnit (algebraMap A B g) →
      Nonempty (Module.Basis (Fin n) B (B ⊗[A] L)) := by
  haveI : Module.FinitePresentation A L := Module.finitePresentation_of_projective A L
  haveI : Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl L) :=
    Module.free_of_flat_of_isLocalRing
  let b : Module.Basis (Fin n) (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl L) :=
    Module.finBasisOfFinrankEq _ _ hn
  obtain ⟨g, hg, b', -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl L) (Localization.AtPrime p.asIdeal) b
  refine ⟨g, hg, fun B _ _ hu ↦ ?_⟩
  letI : Algebra (Localization (Submonoid.powers g)) B := (IsLocalization.Away.lift g hu).toAlgebra
  haveI : IsScalarTower A (Localization (Submonoid.powers g)) B :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq g hu a).symm
  let e := (IsLocalizedModule.isBaseChange (Submonoid.powers g) (Localization (Submonoid.powers g))
    (LocalizedModule.mkLinearMap (Submonoid.powers g) L)).equiv
  exact ⟨((b'.map e.symm).baseChange B).map
    (AlgebraTensorModule.cancelBaseChange A (Localization (Submonoid.powers g)) B B L)⟩

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

theorem nonempty_detGen_of_basis {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R))
    (b : Module.Basis (Fin (Module.finrank ℚ F)) R X.Lie) : Nonempty X.DetGen := by
  refine ⟨⟨b.det, Submodule.eq_top_iff'.2 fun f ↦ ?_⟩⟩
  rw [f.eq_smul_basis_det b]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem exists_detGen_away {A : Type} [CommRing A] (Y : Obj F 𝔠 (Sp A)) (p : PrimeSpectrum A) :
    ∃ g : A, g ∉ p.asIdeal ∧ ∀ (B : Type) [CommRing B] (σ : A →+* B), IsUnit (σ g) →
      ∀ (X : Obj F 𝔠 (Sp B)) (φ : X.A.left ⟶ Y.A.left), X.IsPullBy Y (spMap σ) φ → Nonempty X.DetGen := by
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.lie_algebra_finite_projective_rank Y
  obtain ⟨g, hg, H⟩ := exists_basis_away Y.Lie p _ (hrk p)
  refine ⟨g, hg, fun B _ σ hu X φ h ↦ ?_⟩
  letI := σ.toAlgebra
  obtain ⟨b⟩ := H B hu
  obtain ⟨e, -⟩ := Obj.exists_lieEquiv (R' := B) h
  exact nonempty_detGen_of_basis X (b.map e)

theorem exists_affine_detGen (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (M : Scheme.{0}) (U : Obj F 𝔠 M)
    (R₀ : Type) [CommRing R₀] (m : M) : ∃ (W : M.Opens) (hW : IsAffineOpen W), m ∈ W ∧
      ∀ (X : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (φ : X.A.left ⟶ U.A.left),
        X.IsPullBy U (coefSpecMap hW R₀) φ → Nonempty X.DetGen := by
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hm, -⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ m) isOpen_univ
  replace hW₀ : IsAffineOpen W₀ := hW₀
  obtain ⟨Y, ψ, hY⟩ := Obj.exists_isPullBy (S' := Sp Γ(M, W₀)) U hW₀.fromSpec
  obtain ⟨g, hg, H⟩ := exists_detGen_away Y (hW₀.primeIdealOf ⟨m, hm⟩)
  refine ⟨M.basicOpen g, hW₀.basicOpen g, ?_, fun X φ h ↦ ?_⟩
  · have h1 : hW₀.primeIdealOf ⟨m, hm⟩ ∈ hW₀.fromSpec ⁻¹ᵁ M.basicOpen g := by
      rw [hW₀.fromSpec_preimage_basicOpen]; exact hg
    have h2 : hW₀.fromSpec (hW₀.primeIdealOf ⟨m, hm⟩) ∈ M.basicOpen g := h1
    rwa [hW₀.fromSpec_primeIdealOf] at h2
  · let ρ : Γ(M, W₀) ⟶ Γ(M, M.basicOpen g) := M.presheaf.map (homOfLE (M.basicOpen_le g)).op
    let j := (Algebra.TensorProduct.includeRight :
      Γ(M, M.basicOpen g) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, M.basicOpen g)).toRingHom
    have e : coefSpecMap (hW₀.basicOpen g) R₀ = spMap (j.comp ρ.hom) ≫ hW₀.fromSpec := by
      rw [coefSpecMap, ← hW₀.map_fromSpec (hW₀.basicOpen g) (homOfLE (M.basicOpen_le g)).op, ← Category.assoc]
      congr 1
      exact (Spec.map_comp ρ (CommRingCat.ofHom j)).symm
    rw [e] at h
    obtain ⟨χ, hχ, -⟩ := h.cancel hY
    exact H _ (j.comp ρ.hom) ((M.toRingedSpace.isUnit_res_basicOpen g).map j) X χ hχ

end GlobalTheory.RealMult.LocalGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantGeneratorRuleBaseChange
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult

theorem Rule.eq_of_eq_extScalars : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (A : Type) [CommRing A] (Y : Obj F 𝔠 (Sp A)), Nonempty Y.DetGen →
    (∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] A))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : A →ₐ[ℤ] R₀ ⊗[ℤ] A).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] A)) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ) →
    IsUnit ((6 : ℕ) : A) → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : A →+* B) (Y' : Obj F 𝔠 (Sp B)) (φ : Y'.A.left ⟶ Y.A.left),
    Y'.IsPullBy Y (spMap σ) φ → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y'.DetGen), s.val B Y' h δ = t.val B Y' h δ) := by
  intro F _ _ 𝔠 R₀ _ k s t A _ Y ⟨δ₀⟩ hst h6 B _ _ σ Y' φ hY' h δ
  let inr : A →ₐ[ℤ] R₀ ⊗[ℤ] A := Algebra.TensorProduct.includeRight
  let τ : R₀ ⊗[ℤ] A →ₐ[R₀] B :=
    Algebra.TensorProduct.lift (Algebra.ofId R₀ B) σ.toIntAlgHom fun _ _ ↦ Commute.all _ _
  have hτinr : (τ : R₀ ⊗[ℤ] A →+* B).comp inr.toRingHom = σ := by
    ext a
    simp [τ, inr]
  have hsp : spMap σ = spMap (τ : R₀ ⊗[ℤ] A →+* B) ≫ spMap inr.toRingHom := by
    rw [← hτinr]
    simp [spMap, Spec.map_comp]
  have h6C : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] A) := by
    have := h6.map inr
    rwa [map_natCast] at this
  obtain ⟨YC, ψ, hYC⟩ := Obj.exists_isPullBy Y (spMap inr.toRingHom)
  obtain ⟨ψ', hψ', -⟩ := Obj.IsPullBy.cancel (hsp ▸ hY') hYC
  obtain ⟨δC, hδC, -⟩ := hYC.existsUnique_detGen inr.toRingHom δ₀
  obtain ⟨δB, hδB, -⟩ := hψ'.existsUnique_detGen (τ : R₀ ⊗[ℤ] A →+* B) δC
  have e1 := s.baseChange _ B τ YC h6C Y' h ψ' δC δB hψ' hδB
  have e2 := t.baseChange _ B τ YC h6C Y' h ψ' δC δB hψ' hδB
  have e3 := hst YC ψ hYC h6C δC
  have hB : s.val B Y' h δB = t.val B Y' h δB := by rw [e1, e2, e3]
  obtain ⟨c, hc⟩ : ∃ c : B, δB.1 = c • δ.1 := by
    have : δB.1 ∈ Submodule.span B {δ.1} := by rw [δ.2]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
    exact ⟨c, hc.symm⟩
  rw [← s.homog B Y' h δ δB c hc, ← t.homog B Y' h δ δB c hc, hB]

end GlobalTheory.RealMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableProdPt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.LineForm
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.FibTriv

def prodPt {d : ℕ} (z : V d) (x : ℂ) : V (d + 1) := WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) z.ofLp x)

def basePt {d : ℕ} (v : V (d + 1)) : V d := WithLp.toLp 2 fun a => v a.castSucc

@[simp] theorem prodPt_castSucc {d : ℕ} (z : V d) (x : ℂ) (a : Fin d) : prodPt z x a.castSucc = z a := by
  simp [prodPt]

@[simp] theorem prodPt_last {d : ℕ} (z : V d) (x : ℂ) : prodPt z x (Fin.last d) = x := by simp [prodPt]

@[simp] theorem basePt_apply {d : ℕ} (v : V (d + 1)) (a : Fin d) : basePt v a = v a.castSucc := rfl

@[simp] theorem basePt_prodPt {d : ℕ} (z : V d) (x : ℂ) : basePt (prodPt z x) = z := by
  ext a; simp

@[simp] theorem prodPt_basePt {d : ℕ} (v : V (d + 1)) : prodPt (basePt v) (v (Fin.last d)) = v := by
  ext a
  induction a using Fin.lastCases <;> simp

theorem differentiable_basePt {d : ℕ} : Differentiable ℂ (basePt (d := d)) :=
  differentiable_euclidean.2 fun a => by simp only [basePt_apply]; fun_prop

theorem differentiable_prodPt {d : ℕ} : Differentiable ℂ fun z : V d × ℂ => prodPt z.1 z.2 :=
  differentiable_euclidean.2 fun a => by
    induction a using Fin.lastCases
    · simp only [prodPt_last]; fun_prop
    · simp only [prodPt_castSucc]; fun_prop

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {σ : k →+* ℂ}
  (π : Y ⟶ B) (w : π ≫ q = p) {E : B.Modules} (hE : IsVB E 2) (cE : Chart E 2)
  (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)

def lineVec (y : CxPts p σ) : Fin 2 → ℂ := (cE.pull hE π).crd p σ ((frameAt fl y).frame (.inl 0)) y

def slope (y : CxPts p σ) : ℂ := lineVec π hE cE fl y 1 / lineVec π hE cE fl y 0

def finPart (σ : k →+* ℂ) : Set (CxPts p σ) :=
  {y | PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U ∧ lineVec π hE cE fl y 0 ≠ 0}

def infPart (σ : k →+* ℂ) : Set (CxPts p σ) :=
  {y | PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U ∧ lineVec π hE cE fl y 0 = 0}

include w in

theorem lineVec_ne_zero {y : CxPts p σ} (hy : PtsOver.map π w (spMap σ) y ∈ ptsIn q σ cE.U) :
    lineVec π hE cE fl y ≠ 0 := fun h => by
  have hu := (cE.pull hE π).isUnit_tr ((frameAt fl y).mid (lineSC_shortExact fl)) (y := y) hy (mem_frameAt fl y)
  refine ((Matrix.isUnit_iff_isUnit_det _).1 hu).ne_zero (Matrix.det_eq_zero_of_column_eq_zero 0 fun i => ?_)
  exact congrFun h i

theorem infPart_eq : infPart π w hE cE fl σ =
    PtsOver.map π w (spMap σ) ⁻¹' ptsIn q σ cE.U \ finPart π w hE cE fl σ := by
  ext y
  simp only [infPart, finPart, Set.mem_diff, Set.mem_preimage, Set.mem_setOf_eq]
  tauto

end GlobalTheory.FibTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialZeroOfNotTangent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.UnifOffOrigin

theorem exists_totPos {F : Type} [Field F] [NumberField F] (𝔠 : FracId F) : ∃ c : 𝔠.elt, IsTotPos (c : F) := by
  have hne : (𝔠.elt : Submodule (𝓞 F) F) ≠ ⊥ := by
    intro h
    apply 𝔠.ne_zero
    exact (FractionalIdeal.coeToSubmodule_eq_bot).mp h
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hne
  obtain ⟨a, ha, hint⟩ := (𝔠 : FractionalIdeal (𝓞 F)⁰ F).isFractional
  obtain ⟨y, hy⟩ := hint x hx
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  have hy0 : (algebraMap (𝓞 F) F y) ≠ 0 := by
    rw [hy, Algebra.smul_def]
    exact mul_ne_zero ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)).mpr ha0) hx0
  refine ⟨⟨(a * y) • x, Submodule.smul_mem _ _ hx⟩, ?_⟩
  intro τ
  have hval : ((a * y) • x : F) = algebraMap (𝓞 F) F y * algebraMap (𝓞 F) F y := by
    rw [mul_comm a y, mul_smul, ← hy, Algebra.smul_def]
  show 0 < τ ((a * y) • x)
  rw [hval, map_mul]
  have : τ (algebraMap (𝓞 F) F y) ≠ 0 := (map_ne_zero τ).mpr hy0
  exact mul_self_pos.mpr this

theorem exists_affine_mem_mem {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ))
    (p q : X.A.left) : ∃ W : X.A.left.Opens, IsAffineOpen W ∧ p ∈ W ∧ q ∈ W := by
  obtain ⟨c, hc⟩ := exists_totPos 𝔠
  have hL : ((X.P c).pull (lift (𝟙 X.A) (𝟙 X.A)).left).IsLB := LB.isLB_pull (X.isLB c) _
  have hA := isAmpleLB_of_relAmple_of_isAffine X.A hL (X.pos c hc)
  obtain ⟨_, -, s, hS, -, ha⟩ := hA.exists_affine_finite_subset (S := {p, q}) (Set.toFinite _) (U := ⊤)
    (fun _ _ => trivial)
  exact ⟨_, ha, hS (by simp), hS (by simp)⟩

theorem eq_zero_of_isDiff_of_not_isTangent : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left) (n : ℕ)
    (u : HolUnif X.A L n) (w : Fin n → ℂ) (v : epsR ℂ ⟶ X.A), u.IsDiff w v → ¬ IsTangent v → w = 0 := by
  intro F _ _ 𝔠 X L n u w v hd hv
  let pt : PrimeSpectrum ℂ := default
  obtain ⟨W, hW, hx, h0⟩ := exists_affine_mem_mem X ((spMap TangentOrigin.fstC ≫ v.left) pt) ((u.ex 0).left pt)
  have hx' : ⊤ ≤ (spMap TangentOrigin.fstC ≫ v.left) ⁻¹ᵁ W := (top_le_preimage_iff_mem _ _).2 hx
  have h0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W := (top_le_preimage_iff_mem _ _).2 h0
  have hv' : ⊤ ≤ v.left ⁻¹ᵁ W := (TangentOrigin.top_le_preimage_iff v.left W).2 hx'
  have hsnd : ∀ f, (TangentOrigin.evalPt (R := DualNumber ℂ) v.left W hv' f).snd =
      (TangentOrigin.jet u w W h0' f).snd := fun f => hd W hv' f
  have hfst : ∀ f, (TangentOrigin.evalPt (R := DualNumber ℂ) v.left W hv' f).fst =
      TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f := fun f =>
    (TangentOrigin.evalPt_spMap_comp _ v.left W hv' hx' f).symm
  have key : ∀ f, (TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f -
      TangentOrigin.evalPt (u.ex 0).left W h0' f) * (TangentOrigin.jet u w W h0' f).snd = 0 := by
    intro f
    have e := hsnd (f * f)
    rw [map_mul, map_mul, DualNumber.snd_mul, DualNumber.snd_mul, hsnd f, hfst f,
      TangentOrigin.jet_fst] at e
    linear_combination e / 2
  obtain ⟨h, hh⟩ : ∃ h, TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' h ≠
      TangentOrigin.evalPt (u.ex 0).left W h0' h := by
    by_contra hc
    push_neg at hc
    exact hv ((TangentOrigin.ext_evalPt hW hx' h0' (RingHom.ext hc)).trans (TangentOrigin.ex_zero_left u))
  have hdh : (TangentOrigin.jet u w W h0' h).snd = 0 := (mul_eq_zero.1 (key h)).resolve_left (sub_ne_zero.2 hh)
  have hδ : ∀ f, (TangentOrigin.jet u w W h0' f).snd = 0 := by
    intro f
    by_cases hf : TangentOrigin.evalPt (spMap TangentOrigin.fstC ≫ v.left) W hx' f =
        TangentOrigin.evalPt (u.ex 0).left W h0' f
    · have k2 := key (f + h)
      rw [map_add, map_add, hf, add_sub_add_left_eq_sub] at k2
      have e := (mul_eq_zero.1 k2).resolve_left (sub_ne_zero.2 hh)
      rwa [map_add, TrivSqZeroExt.snd_add, hdh, add_zero] at e
    · exact (mul_eq_zero.1 (key f)).resolve_left (sub_ne_zero.2 hf)
  have ht := ArchMetricCompare.isTangent_zero X.A
  have h₁ := (TangentOrigin.tangent_mem_iff (u := u) ht W).2 h0'
  refine ArchMetricCompare.eq_zero_of_isDiff u ((TangentOrigin.isDiff_iff ht hW h₁ h0' w).2
    (RingHom.ext fun f => TrivSqZeroExt.ext (TangentOrigin.tangent_fst ht h₁ h0' f) ?_))
  have e := ArchMetricCompare.isDiff_zero u W h₁ f
  rw [map_zero] at e
  exact e.trans (hδ f).symm

end GlobalTheory.UnifOffOrigin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberMorphismEqOfLocal
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

namespace GlobalTheory.ArLieBase

set_option backward.isDefEq.respectTransparency false in

theorem hom_ext_dualNumber_away : ∀ {L : Type} [CommRing L] {s : Set L}, Ideal.span s = ⊤ → ∀ {Y : Scheme.{0}} {w w' : Sp (DualNumber L) ⟶ Y}, (∀ a : s, spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w = spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w') → w = w' := by
  intro L _ s hs Y w w' h
  have hs' : Ideal.span (Set.range (fun k : s => (TrivSqZeroExt.inl (k : L) : DualNumber L))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom L L)) hs
    rw [Ideal.map_span, Ideal.map_top, Set.image_eq_range] at this
    exact this
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber L)) _ hs').openCover
  refine Scheme.Cover.hom_ext 𝒰 _ _ fun (k : s) => ?_
  have hd : Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (k : L))) =
      ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L) := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  have e : 𝒰.f k = Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.toL (k : L))) ≫
      Spec.map (CommRingCat.ofHom (ReciprocityTheory.ChartRestriction.G.Chart.dAway (k : L))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ReciprocityTheory.ChartRestriction.G.Chart.toL_comp]
    rfl
  have hk := h k
  rw [hd] at hk
  rw [e, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) hk

end GlobalTheory.ArLieBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInAllCompleteDVRNormalNoetherianStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_dvd_in_all_completeDVR_normal_noetherian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (a b : R), b ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ φ : R →+* V, Function.Injective φ → φ b ∣ φ a) → b ∣ a := by
  first | exact @GlobalTheory.DvrDiv.dvd_of_forall_cDvr | exact GlobalTheory.DvrDiv.dvd_of_forall_cDvr | (intros; apply GlobalTheory.DvrDiv.dvd_of_forall_cDvr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfDvdInCompleteDVRsFiniteResidue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven

theorem dvd_of_forall_fintrait : ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [Algebra.FiniteType ℤ A] (a f : A), f ≠ 0 → (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∀ t : A →+* V, t f ≠ 0 → t f ∣ t a) → f ∣ a := by
  intro A _ _ _ _ _ a f hf H
  rcases eq_or_ne a 0 with rfl | ha
  · exact dvd_zero f
  let K := FractionRing A
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have haK : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ hinj).2 ha
  have hfK : algebraMap A K f ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
  let y : K := algebraMap A K f / algebraMap A K a
  have hy : y ≠ 0 := div_ne_zero hfK haK
  let S := Algebra.adjoin A {y}
  let z : S := ⟨y, Algebra.self_mem_adjoin_singleton A y⟩
  by_cases hz : IsUnit z
  · obtain ⟨w, hw⟩ := hz.exists_right_inv
    have hw' : (w : K) = y⁻¹ := eq_inv_of_mul_eq_one_right (congrArg Subtype.val hw)
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
      (GlobalTheory.ValCrit.isIntegral_of_mem_adjoin_inv y hy (hw' ▸ w.2))
    refine ⟨r, hinj ?_⟩
    rw [map_mul, hr, inv_div, mul_div_cancel₀ _ hfK]
  · exfalso
    have hft : Algebra.FiniteType A S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton y)
    haveI hftZ : @Algebra.FiniteType ℤ S _ _ (Ring.toIntAlgebra S) := by
      have h2 := Algebra.FiniteType.trans (R := ℤ) (S := A) (A := S) inferInstance hft
      convert h2 using 1 <;> first | rfl | exact Subsingleton.elim _ _
    have hinjS : Function.Injective (algebraMap A S) := fun b c h => hinj (congrArg Subtype.val h)
    have : CharZero S := charZero_of_injective_algebraMap hinjS
    obtain ⟨n, hn, hzn⟩ := exists_max_ideal_of_mem_nonunits hz
    have hfS : algebraMap A S f ≠ 0 := (map_ne_zero_iff _ hinjS).2 hf
    obtain ⟨V, _, _, _, _, t, hc, hfin, htf, hcomap⟩ := GlobalTheory.T.exists_trait_finiteResidue_charZero_avoiding S n (algebraMap A S f) hn hfS
    have hdiv := H V hc hfin (t.comp (algebraMap A S)) htf
    simp only [RingHom.comp_apply] at hdiv
    have hfa : algebraMap A S f = z * algebraMap A S a := by
      apply Subtype.ext
      show algebraMap A K f = (algebraMap A K f / algebraMap A K a) * algebraMap A K a
      rw [div_mul_cancel₀ _ haK]
    have htz : t z ∈ IsLocalRing.maximalIdeal V := by
      rw [← Ideal.mem_comap, hcomap]; exact hzn
    rw [hfa, map_mul] at hdiv htf
    obtain ⟨c, hc'⟩ := hdiv
    have hta : t (algebraMap A S a) ≠ 0 := right_ne_zero_of_mul htf
    have h1 : t z * c = 1 := by
      apply mul_left_cancel₀ hta
      calc t (algebraMap A S a) * (t z * c) = t z * t (algebraMap A S a) * c := by ring
        _ = t (algebraMap A S a) := hc'.symm
        _ = t (algebraMap A S a) * 1 := (_root_.mul_one _).symm
    exact (IsLocalRing.mem_maximalIdeal _).1 htz ⟨⟨t z, c, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

end GlobalTheory.KeyEven
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionLiftPadicAlgClosureNormLeOneIffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_fractionLift_padicAlgClosure_norm_le_one_iff : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (i : V →+* OO p), IsLocalHom i → ∀ (hi : Function.Injective ((OO p).subtype.comp i)) (x : FractionRing V), ‖IsFractionRing.lift (K := FractionRing V) hi x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  first | exact @GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range | exact GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range | (intros; apply GlobalTheory.Poinc.norm_lift_le_one_iff_mem_range <;> assumption)
end

