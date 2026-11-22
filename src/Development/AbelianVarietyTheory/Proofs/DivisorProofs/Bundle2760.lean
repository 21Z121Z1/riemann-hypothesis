import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyRestrictBasisExtendedBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2568
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0078
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2506
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0781
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeEqEulerCharacteristic
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericFibreDegree

theorem chi_eq_residueDegree : ∀ (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (f : Y ⟶ B)
    (G : Scheme.{0}) (j : G ⟶ Y) (s : G ⟶ Sp B.functionField),
    IsPullback j s f (B.fromSpecStalk (genericPoint B)) → IsProjOver s →
    topologicalKrullDim G ≤ (0 : ℕ) → Nonempty G → f.residueDegree (genericPoint Y) ≠ 0 ∧
      (letI := algebraΓOfHom s; chi B.functionField (structureModule G)) =
        f.residueDegree (genericPoint Y) := by
  intro B Y _ _ f G j s hpb hP hd hne
  obtain ⟨hpre, -, -, hint⟩ := GlobalTheory.T.generic_fibre_preimmersion_integral B Y f G j s hpb
  obtain ⟨hGint, hjη⟩ := hint hne

  have hu (w : G) : w = genericPoint G := by
    have h0 : Order.krullDim (IrreducibleCloseds G) ≤ 0 := (by simpa using hd : topologicalKrullDim G ≤ 0)
    have := Order.krullDim_nonpos_iff_forall_isMax.1 h0
      ⟨closure {w}, isIrreducible_singleton.closure, isClosed_closure⟩
    exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@this
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ G, isClosed_univ⟩ (Set.subset_univ _)))
      (genericPoint_spec G)

  haveI : IsAffine G := by
    obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := G) (x := genericPoint G)
      (U := ⊤) trivial
    have hUt : U = ⊤ := by
      ext w
      exact ⟨fun _ => trivial, fun _ => by rw [hu w]; exact hxU⟩
    subst hUt
    haveI : IsAffine (⊤ : G.Opens).toScheme := hU
    exact IsAffine.of_isIso G.topIso.inv
  haveI : IsProper s := CommonModel.isProper_of_isProjOver hP
  haveI : IsFinite s := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hsη : s (genericPoint G) = genericPoint (Sp B.functionField) := Subsingleton.elim _ _
  have h1 := GlobalTheory.ProjFin.finrank_app_eq_residueDegree s hsη (U := ⊤) (isAffineOpen_top _) trivial

  have h2 : f.residueDegree (genericPoint Y) = s.residueDegree (genericPoint G) := by
    have e := congrArg (fun h => Scheme.Hom.residueDegree h (genericPoint G)) hpb.w
    simp only [CurveDegreesCompare.residueDegree_comp] at e
    rw [CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks j,
      CoverDeg.residueDegree_eq_one_of_surjectiveOnStalks (B.fromSpecStalk (genericPoint B)),
      mul_one, one_mul, hjη] at e
    exact e
  letI := algebraΓOfHom s

  have h3 : Module.finrank B.functionField Γ(G, ⊤) = s.residueDegree (genericPoint G) := by
    refine Eq.trans ?_ h1
    letI := (s.app ⊤).hom.toAlgebra
    exact Algebra.finrank_eq_of_equiv_equiv
      (Scheme.ΓSpecIso (CommRingCat.of B.functionField)).symm.commRingCatIsoToRingEquiv
      (RingEquiv.refl _) rfl
  haveI hfin : Module.Finite B.functionField Γ(G, ⊤) := by
    have hf : (s.app ⊤).hom.Finite := IsFinite.finite_app s ⊤ (isAffineOpen_top _)
    have hi : ((Scheme.ΓSpecIso (CommRingCat.of B.functionField)).inv).hom.Finite :=
      RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B.functionField)).inv).2
    exact hf.comp hi
  haveI : Nontrivial Γ(G, ⊤) := inferInstance
  refine ⟨?_, ?_⟩
  · rw [h2, ← h3]
    exact Module.finrank_pos.ne'
  · rw [chi_structureModule_of_isAffine, h3, h2]

end GlobalTheory.GenericFibreDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictPairInjective
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LBObs.PairInj

theorem pull2_pairRes_restrict (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] {X₀ Z₀ : Scheme.{0}}
    (t₀ : Z₀ ⟶ Sp R₀) (f₀ : Z₀ ⟶ X₀) {D : Type} [Category.{0} D] (K : D ⥤ (Pair f₀)ᵒᵖ)
    (c : CatCoh.H2 (ext R₁ (OAff t₀))) :
    (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 ((extMap R₁ (pairRes f₀ t₀)).pull2 c) =
      (extMap R₁ (CoefMap.restrict (OAff t₀) (K ⋙ pairFst f₀))).pull2 c := by
  obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
  rw [CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class, CoefMap.pullCohomologyTwo_class]
  refine congrArg _ (Subtype.ext ?_)
  funext T T' T'' a b
  show extHom R₁ (coefHom (CoefMap.restrict (OPair f₀ t₀) K) T'')
      (extHom R₁ (coefHom (pairRes f₀ t₀) (K.obj T'')) _) =
    extHom R₁ (coefHom (CoefMap.restrict (OAff t₀) (K ⋙ pairFst f₀)) T'') _
  exact (PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).trans ((PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).trans
    (PairExt.extHom_of_id R₁ _ (fun _ ↦ rfl) _).symm)

theorem restrict_pair_injective : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (X₀ Z₀ : Scheme.{0}) (t₀ : Z₀ ⟶ Sp R₀) (f₀ : Z₀ ⟶ X₀) (D : Type) [Category.{0} D] [Quiver.IsThin D] (K : D ⥤ (Pair f₀)ᵒᵖ), IsBas (opOf (K ⋙ pairFst f₀)) → Function.Injective (extMap R₁ (CoefMap.restrict (OPair f₀ t₀) K)).pull2 := by
  intro R₀ R₁ _ _ _ X₀ Z₀ t₀ f₀ D _ _ K hB x y e
  have hG := (BasisExt.restrict_ext_bijective R₀ R₁ Z₀ t₀ D (K ⋙ pairFst f₀) hB.1 hB.2).2.1
  have hP := ((PairExt.pairRes_ext_bijective R₀ R₁ X₀ Z₀ t₀ f₀).1.2).2
  obtain ⟨x0, rfl⟩ := hP x
  obtain ⟨y0, rfl⟩ := hP y
  rw [pull2_pairRes_restrict, pull2_pairRes_restrict] at e
  rw [hG e]

end GlobalTheory.LBObs.PairInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen GlobalTheory.CurveRootGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoSeq

section General

variable {O : Type} [CommRing O] {X T T' S : Scheme.{0}} {A B A' B' : X.Modules}

def sqIso {b : S ⟶ T} {a : T ⟶ X} {c : S ⟶ T'} {a' : T' ⟶ X} (w : b ≫ a = c ≫ a') :
    Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback b ≅ Scheme.Modules.pullback a' ⋙ Scheme.Modules.pullback c :=
  Scheme.Modules.pullbackComp b a ≪≫ Scheme.Modules.pullbackCongr w ≪≫ (Scheme.Modules.pullbackComp c a').symm

structure Datum (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ) where

  D : X.Modules

  ρ : O →+* End D

  a : A ⟶ D

  b : D ⟶ B

  u : A' ⟶ D

  v : D ⟶ B'
  w₁ : a ≫ b = 0
  w₂ : u ≫ v = 0
  isVB : IsVB D r
  exact₁ : (ShortComplex.mk a b w₁).ShortExact
  exact₂ : (ShortComplex.mk u v w₂).ShortExact
  equiv_a : IsEquivariant α ρ a
  equiv_b : IsEquivariant ρ β b
  equiv_u : IsEquivariant α' ρ u
  equiv_v : IsEquivariant ρ β' v

variable (α : O →+* End A) (β : O →+* End B) (α' : O →+* End A') (β' : O →+* End B') (r : ℕ)

abbrev DatumOn (f : T ⟶ X) : Type 1 := Datum (pullAct α f) (pullAct β f) (pullAct α' f) (pullAct β' f) r

variable {α β α' β' r}

def Agree {a : T ⟶ X} {a' : T' ⟶ X} (d : DatumOn α β α' β' r a) (d' : DatumOn α β α' β' r a') {b : S ⟶ T} {c : S ⟶ T'}
    (w : b ≫ a = c ≫ a') (φ : (Scheme.Modules.pullback b).obj d.D ≅ (Scheme.Modules.pullback c).obj d'.D) : Prop :=
  IsEquivariant (pullAct d.ρ b) (pullAct d'.ρ c) φ.hom ∧
    (Scheme.Modules.pullback b).map d.a ≫ φ.hom = (sqIso w).hom.app A ≫ (Scheme.Modules.pullback c).map d'.a ∧
    φ.hom ≫ (Scheme.Modules.pullback c).map d'.b = (Scheme.Modules.pullback b).map d.b ≫ (sqIso w).hom.app B ∧
    (Scheme.Modules.pullback b).map d.u ≫ φ.hom = (sqIso w).hom.app A' ≫ (Scheme.Modules.pullback c).map d'.u ∧
    φ.hom ≫ (Scheme.Modules.pullback c).map d'.v = (Scheme.Modules.pullback b).map d.v ≫ (sqIso w).hom.app B'

def RestrictsTo (d : Datum α β α' β' r) {a : T ⟶ X} (d' : DatumOn α β α' β' r a)
    (e : (Scheme.Modules.pullback a).obj d.D ≅ d'.D) : Prop :=
  IsEquivariant (pullAct d.ρ a) d'.ρ e.hom ∧
    (Scheme.Modules.pullback a).map d.a ≫ e.hom = d'.a ∧ e.hom ≫ d'.b = (Scheme.Modules.pullback a).map d.b ∧
    (Scheme.Modules.pullback a).map d.u ≫ e.hom = d'.u ∧ e.hom ≫ d'.v = (Scheme.Modules.pullback a).map d.v

def biprodAct (α : O →+* End A) (β : O →+* End B) : O →+* End (A ⊞ B) where
  toFun x := biprod.map (act α x) (act β x)
  map_one' := by
    rw [act, act, map_one, map_one]
    exact biprod.hom_ext _ _ (by simp [End.one_def]) (by simp [End.one_def])
  map_mul' x y := by
    rw [act, act, map_mul, map_mul]
    exact biprod.hom_ext _ _ (by simp [End.mul_def]) (by simp [End.mul_def])
  map_zero' := by
    rw [act, act, map_zero, map_zero]
    change (biprod.map (0 : A ⟶ A) (0 : B ⟶ B) : A ⊞ B ⟶ A ⊞ B) = (0 : A ⊞ B ⟶ A ⊞ B)
    exact biprod.hom_ext _ _ (by simp) (by simp)
  map_add' x y := by
    rw [act, act, map_add, map_add]
    change (biprod.map (act α x + act α y) (act β x + act β y) : A ⊞ B ⟶ A ⊞ B) =
      (biprod.map (act α x) (act β x) + biprod.map (act α y) (act β y) : A ⊞ B ⟶ A ⊞ B)
    exact biprod.hom_ext _ _ (by simp) (by simp)

def Datum.split (α : O →+* End A) (β : O →+* End B) {m n : ℕ} (hA : IsVB A m) (hB : IsVB B n) :
    Datum α β β α (m + n) where
  D := A ⊞ B
  ρ := biprodAct α β
  a := biprod.inl
  b := biprod.snd
  u := biprod.inr
  v := biprod.fst
  w₁ := by simp
  w₂ := by simp
  isVB := hA.biprod hB
  exact₁ := (ShortComplex.Splitting.ofHasBinaryBiproduct A B).shortExact
  exact₂ := (ShortComplex.Splitting.mk (S := ShortComplex.mk (biprod.inr : B ⟶ A ⊞ B) biprod.fst (by simp))
    biprod.snd biprod.inl (by simp) (by simp) (by rw [add_comm]; exact biprod.total)).shortExact
  equiv_a x := by simp [act, biprodAct]
  equiv_b x := by simp [act, biprodAct]
  equiv_u x := by simp [act, biprodAct]
  equiv_v x := by simp [act, biprodAct]

example (X : Scheme.{0}) :
    let σ := scalarAct (GlobalTheory.QCoh.freeModule X (Fin 1)) (RingHom.id Γ(X, ⊤))
    Nonempty (Datum σ σ σ σ 2) :=
  ⟨Datum.split _ _ (isVB_freeModule_fin X 1) (isVB_freeModule_fin X 1)⟩

end General

section Dieu

variable {O : Type} [CommRing O] (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O) {C : Scheme.{0}}
  [Algebra k Γ(C, ⊤)] {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G)

abbrev DieuDatum (g : ℕ) : Type 1 :=
  Datum (omegaAct i) ((lieAct i).comp c) (pullAct ((lieAct i).comp c) (frob C q (natCast_eq_zero C q k)))
    (pullAct (omegaAct i) (frob C q (natCast_eq_zero C q k))) (2 * g)

abbrev DieuDatumOn (g : ℕ) {T : Scheme.{0}} (f : T ⟶ C) : Type 1 :=
  DatumOn (omegaAct i) ((lieAct i).comp c) (pullAct ((lieAct i).comp c) (frob C q (natCast_eq_zero C q k)))
    (pullAct (omegaAct i) (frob C q (natCast_eq_zero C q k))) (2 * g) f

theorem hasDieu_iff : HasDieu q k c i ↔ ∃ g, IsVB (omega G) g ∧ Nonempty (DieuDatum q k c i g) :=
  ⟨fun ⟨D, g, ρ, a, b, u, v, w₁, w₂, h, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ =>
      ⟨g, h, ⟨⟨D, ρ, a, b, u, v, w₁, w₂, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩⟩⟩,
    fun ⟨g, h, ⟨d⟩⟩ => ⟨d.D, g, d.ρ, d.a, d.b, d.u, d.v, d.w₁, d.w₂, h, d.isVB, d.exact₁, d.exact₂, d.equiv_a,
      d.equiv_b, d.equiv_u, d.equiv_v⟩⟩

end Dieu

end GlobalTheory.TwoSeq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieMeasureFrameBoxLeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.riemannianLieMeasure_frameBox_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type) (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ) (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r), 1 ≤ r → IsIdent p q Ψ G x σ A e → ∀ t : ℝ, 0 < t → riemLie Ψ G x {X | ∀ τ a b, ‖((mat x τ)⁻¹ * Matrix.of (X τ) * mat x τ) a b‖ < t} ≤ ENNReal.ofReal ((3 * t) ^ (Ψ.card * (r ^ 2 - 1))) := by
  first | exact @GlobalTheory.CovTop.VolUp.FrameBox.riemLie_frameBox_le | exact GlobalTheory.CovTop.VolUp.FrameBox.riemLie_frameBox_le | (intros; apply GlobalTheory.CovTop.VolUp.FrameBox.riemLie_frameBox_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfPow
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PDivGroup

theorem rigOfOmega_injective_of_pow (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ)
    (hN : (p : R) ^ N = 0) (G : PDivGroup p R) : Function.Injective G.rigOfOmega := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).1 hw
  rw [G.eq_zero_of_cob_eq_zero_of_pow p R N hN b (congrArg Prod.fst hb), map_zero] at hb
  exact (congrArg Prod.snd hb).symm

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedIdentificationsGenericFibreAgreeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_identifications_generic_fibre_agree : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R') (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∀ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w → PMaps w (K := PUnit) (fun _ => eSec D₃.P.A) (fun _ => eSec D₂.P.A) (fun _ => 1) D₃.rig D₂.rig (spMap ρ) → ∀ (Z : Scheme.{0}) (f : Z ⟶ E.P.A.left) (z : Z) (j : D₂.P.L.ι) (i : D₃.P.L.ι) (k : E.P.L.ι) (l : D₁.P.L.ι), GlobalTheory.PsiEvenPull.proj q₂ (f z) ∈ D₂.P.L.U j → κ (f z) ∈ D₃.P.L.U i → f z ∈ E.P.L.U k → GlobalTheory.PsiEvenPull.proj q₁ (f z) ∈ D₁.P.L.U l → gw w (f ≫ κ) z j i * (gw p.w (f ≫ κ) z l i)⁻¹ = gw q₂.w f z j k * (gw q₁.w f z l k)⁻¹ := by
  first | exact @GlobalTheory.GenEqual.genequal | exact GlobalTheory.GenEqual.genequal | (intros; apply GlobalTheory.GenEqual.genequal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedSymmetricOfSymmetricFieldExtensionPull
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem rigidified_and_sym_of_field_extension : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → Sym A' L' → Rigidified A L ∧ Sym A L := by
  intro K K' _ _ i A _ A' _ φ hA h L L' hL hL' hw hS
  refine ⟨?_, (GlobalTheory.PolDescent.rigidified_sym_kTriv_descend K K' i A A' φ L L' hA h hL hL' hw).2.1 hS⟩
  have : Subsingleton (𝟙_ (Over (Sp K))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact GlobalTheory.PolDescent.exists_gen_of_unique (default : PrimeSpectrum K) (pull_isLB hL _)

end GlobalTheory.Mum.GenDesc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivSubMemMaximalIdealOfPurelyInsepResidue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ResFix

theorem sigma_fix_mod_max : ∀ (A R R' : Type) [CommRing A] [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (b : A →+* R) (θ : R →+* R') [IsLocalHom θ] (q : ℕ) [ExpChar (ResidueField R) q] (σ : R' ≃+* R'), (∀ x : ResidueField R, ∃ n : ℕ, ∃ a : A, x ^ q ^ n = residue R (b a)) → (∀ a, σ (θ (b a)) = θ (b a)) → ∀ r, σ (θ r) - θ r ∈ maximalIdeal R' := by
  intro A R R' _ _ _ _ _ b θ _ q _ σ hins hfix r
  obtain ⟨n, a, ha⟩ := hins (residue R r)
  have h1 : r ^ q ^ n - b a ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff, map_sub, map_pow, ha, sub_self]
  have h2 : θ r ^ q ^ n - θ (b a) ∈ maximalIdeal R' := by
    have := map_nonunit θ _ h1
    simpa [map_sub, map_pow] using this
  have h3 : σ (θ r) ^ q ^ n - θ (b a) ∈ maximalIdeal R' := by
    have := map_nonunit (σ : R' →+* R') _ h2
    simpa [map_sub, map_pow, hfix a] using this
  haveI : ExpChar (ResidueField R') q :=
    expChar_of_injective_ringHom (ResidueField.map θ).injective q
  have e2 : residue R' (θ r) ^ q ^ n = residue R' (θ (b a)) := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h2
  have e3 : residue R' (σ (θ r)) ^ q ^ n = residue R' (θ (b a)) := by
    rw [← map_pow, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact h3
  have e4 : (residue R' (σ (θ r)) - residue R' (θ r)) ^ q ^ n = 0 := by
    rw [sub_pow_expChar_pow, e2, e3, sub_self]
  rw [← residue_eq_zero_iff, map_sub]
  exact pow_eq_zero_iff (pow_ne_zero _ (expChar_pos (ResidueField R') q).ne') |>.mp e4

end GlobalTheory.ResFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomCoeffSpanSetSectionsFlatBaseChangeNormalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHomCoeffSpanSet_sections_flat_baseChange_normal : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R₁] [IsDomain R₁] [IsNoetherianRing R₁] [IsIntegrallyClosed R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁) (f : R), f ≠ 0 → ρ.Flat → Function.Injective ρ → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (V₀ : Set F), (0 : F) ∈ V₀ → (∀ a ∈ V₀, ∀ b ∈ V₀, a + b ∈ V₀) → (∀ r, ∀ a ∈ V₀, c₀ r * a ∈ V₀) → (∀ a ∈ V₀, (c₀ f)⁻¹ * a ∈ V₀) → ∀ (W : Ideal R → Set F) (W₁ : Ideal R₁ → Set F₁), (∀ p : Ideal R, p.IsPrime → f ∈ p → ∀ u, ∃ m : ℕ, c₀ f ^ m * u ∈ W p) → (∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → (∀ a ∈ W p, ∀ b ∈ W p, a + b ∈ W p) ∧ (∀ r, ∀ a ∈ W p, c₀ r * a ∈ W p) ∧ (∀ s, s ∉ p → ∀ a ∈ W p, (c₀ s)⁻¹ * a ∈ W p)) → (∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → GaussAt c₁ q θ (W (q.comap ρ)) (W₁ q)) → spanBy c₁ (θ '' {u | u ∈ V₀ ∧ ∀ p : Ideal R, p.IsPrime → p.height = 1 → f ∈ p → u ∈ W p}) = spanBy c₁ (θ '' V₀) ∩ {v | ∀ q : Ideal R₁, q.IsPrime → q.height = 1 → ρ f ∈ q → v ∈ W₁ q} := by
  first | exact @GlobalTheory.Desc.spanBy_sections_eq_of_flat | exact GlobalTheory.Desc.spanBy_sections_eq_of_flat | (intros; apply GlobalTheory.Desc.spanBy_sections_eq_of_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFiniteOfQuasiFiniteCompleteLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.QuasiFiniteLocal

theorem finite_quotient_of_pow_le_of_span {A S : Type} [CommRing A] [CommRing S] [Algebra A S]
    [IsNoetherianRing S] {I J : Ideal S} (T : Set S) (hT : T.Finite)
    (h : ∀ s : S, ∃ t ∈ Submodule.span A T, s - t ∈ I) {N : ℕ}
    (hN : I ^ N ≤ J) : Module.Finite A (S ⧸ J) := by
  have key : ∀ N : ℕ, ∃ F : Submodule A S, F.FG ∧ F ⊔ (I ^ N).restrictScalars A = ⊤ := by
    intro N
    induction N with
    | zero => exact ⟨⊥, Submodule.fg_bot, by simp⟩
    | succ N ih =>
      obtain ⟨F, hF, hF'⟩ := ih
      obtain ⟨G, hG⟩ : (I ^ N).FG := IsNoetherian.noetherian _
      refine ⟨F ⊔ Submodule.span A (Set.image2 (· * ·) T (G : Set S)),
        hF.sup (Submodule.fg_span (hT.image2 _ G.finite_toSet)), ?_⟩
      rw [eq_top_iff, ← hF', sup_assoc]
      refine sup_le_sup_left (fun x hx => ?_) _
      have hx' : x ∈ Submodule.span S (G : Set S) := hG.ge hx
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hx'
      refine sum_mem fun y hy => ?_
      obtain ⟨t, ht, ha⟩ := h (c y)
      have e : c y • y = t * y + y * (c y - t) := by rw [smul_eq_mul]; ring
      rw [e]
      refine Submodule.add_mem_sup ?_ ?_
      · have hmul : ∀ u ∈ Submodule.span A T,
            u * y ∈ Submodule.span A (Set.image2 (· * ·) T (G : Set S)) := by
          intro u hu
          induction hu using Submodule.span_induction with
          | mem u hu => exact Submodule.subset_span (Set.mem_image2_of_mem hu hy)
          | zero => simp
          | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
          | smul a u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hu
        exact hmul t ht
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (hG.le (Ideal.subset_span hy)) ha
  obtain ⟨F, hF, hF'⟩ := key N
  have : Module.Finite A F := Module.Finite.iff_fg.2 hF
  refine Module.Finite.of_surjective ((Ideal.Quotient.mkₐ A J).toLinearMap ∘ₗ F.subtype) fun s => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hF'.ge (Submodule.mem_top (x := s)))
  exact ⟨⟨y, hy⟩, Ideal.Quotient.eq.2 (by simpa using hN hz)⟩

theorem finite_of_quasiFinite : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (b : A →+* R) [IsLocalHom b], IsAdicComplete (maximalIdeal A) A → (∀ p : Ideal R, p.IsPrime → (maximalIdeal A).map b ≤ p → p = maximalIdeal R) → ((residue R).comp b).Finite → b.Finite := by
  intro A R _ _ _ _ _ _ b _ hc hq hres
  letI : Algebra A R := b.toAlgebra
  have hb : algebraMap A R = b := rfl
  have hle : (maximalIdeal A).map (algebraMap A R) ≤ maximalIdeal R := by
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    rw [Ideal.mem_comap, hb, mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit b a h)
  have hrad : maximalIdeal R ≤ ((maximalIdeal A).map (algebraMap A R)).radical := by
    rw [Ideal.radical_eq_sInf]
    exact le_sInf fun p ⟨hJp, hp⟩ => (hq p hp hJp).ge
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)

  obtain ⟨T0, hT0⟩ : (⊤ : Submodule A (ResidueField R)).FG := by
    letI : Algebra A (ResidueField R) := ((residue R).comp b).toAlgebra
    exact hres.fg_top
  classical
  let lift : ResidueField R → R := Function.surjInv (residue_surjective (R := R))
  have hlift : ∀ t, residue R (lift t) = t := Function.surjInv_eq _
  let L : R →ₗ[A] ResidueField R :=
    { toFun := residue R
      map_add' := map_add _
      map_smul' := fun a x => by
        show residue R (b a * x) = residue R (b a) * residue R x
        exact map_mul _ _ _ }
  have hfin : Module.Finite A (R ⧸ (maximalIdeal A).map (algebraMap A R)) := by
    refine finite_quotient_of_pow_le_of_span (I := maximalIdeal R) (lift '' (T0 : Set _))
      ((T0.finite_toSet).image _) (fun s => ?_) hN
    have hs : residue R s ∈ Submodule.map L (Submodule.span A (lift '' (T0 : Set _))) := by
      rw [Submodule.map_span, ← Set.image_comp]
      have e : (⇑L ∘ lift) = id := funext fun t => hlift t
      rw [e, Set.image_id, hT0]
      trivial
    obtain ⟨t, ht, hts⟩ := hs
    refine ⟨t, ht, ?_⟩
    rw [← residue_eq_zero_iff, map_sub]
    exact sub_eq_zero.2 hts.symm
  have : IsHausdorff ((maximalIdeal A).map (algebraMap A R)) R :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hle)
  haveI := hc
  exact GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal A)

end GlobalTheory.QuasiFiniteLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleSectionNowhereVanishingRealStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.BdryUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rule_section_nowhere_vanishing_real : GlobalTheory.CovTop.Hypotheses2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (Z : Comp Xo c) (V : (Xo.XF c).Opens) (τ : Psi H) (sig : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.Rule Y V τ.1) (f : Rul Xo c), (V : Set (Xo.XF c)) = Z → sig ∈ GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.sections Y V τ.1 → GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.VanishesNowhere sig → Reads Y V τ sig f → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), (∀ a, a ≠ 0 → vV T.V (io a) = 0) → (letI := io.toAlgebra; LiesOn Z y₀.1) → nval T.V 1 (evI y₀ f) = 0 := by
  first | exact @GlobalTheory.BdryUnitVal.unit_at_integral | exact GlobalTheory.BdryUnitVal.unit_at_integral | (intros; apply GlobalTheory.BdryUnitVal.unit_at_integral <;> assumption)
end

