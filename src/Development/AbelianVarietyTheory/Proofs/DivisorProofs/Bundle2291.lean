import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverTargetOfIsGaloisCover
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSectionAndDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeterminantSectionRule
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0068
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0003
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0610
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0607
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0862
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimmersionFlatValuationSubringBaseRingStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreimmersion_flat_valuationSubring_baseRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), IsBaseRing β → ∀ (W : ValuationSubring c.F) (b : O →+* W), W.subtype.comp b = β → IsPreimmersion (spMap b) ∧ Flat (spMap b) := by
  first | exact @GlobalTheory.ValLocal.preimmersion_flat | exact GlobalTheory.ValLocal.preimmersion_flat | (intros; apply GlobalTheory.ValLocal.preimmersion_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory

theorem isProjOver_locallyOfFiniteType : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R),
    IsProjOver s → LocallyOfFiniteType s := by
  rintro R _ X s ⟨N, i, hi, rfl⟩
  haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.RelAmpleQProjNoeth

open GlobalTheory.RelAmpleQProj

theorem isQProjOver_of_relAmple_noeth : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X : Scheme.{0})
    (s : X ⟶ Sp K) (A : Over X) (L : LB A.left), IsQProjOver s → L.IsLB → Out.RelAmple A L →
    IsQProjOver (A.hom ≫ s) := by
  rintro K _ _ X s A L ⟨N, i, _, _, rfl⟩ hL hA
  obtain ⟨_, B, hB⟩ := isProper_and_exists_isAmpleLB A hL hA ((isAmple_projective_O_one K N).pull_of_isImmersion i)
  have := isProper_str K N
  exact hB.isQProjOver _

end GlobalTheory.RelAmpleQProjNoeth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.GaloisQuotientRing
open GlobalTheory.GaloisQuotient

theorem isQProjOver_of_isGaloisCover : ∀ (K : Type) [CommRing K] [IsNoetherianRing K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)), IsGaloisCover Ga ρ π → IsSeparated sY → LocallyOfFiniteType sY → IsQProjOver (π ≫ sY) → IsQProjOver sY := by
  intro K _ _ X Y π sY Ga _ ρ hG _ _ hX
  have := hG.finite
  let τ : Ga →* Aut X := MonoidHom.mk'
    (fun a => (⟨ρ a⁻¹, ρ a, by rw [← hG.mul, inv_mul_cancel, hG.one], by rw [← hG.mul, mul_inv_cancel, hG.one]⟩ :
      X ≅ X))
    fun a c => Iso.ext (by
      change ρ (a * c)⁻¹ = ρ c⁻¹ ≫ ρ a⁻¹
      rw [mul_inv_rev, hG.mul])
  have := OrbitsInAffineOpens.of_isQProjOver hX τ
  have hq := finiteQuotient.isAffineQuotient τ
  have hD := (GlobalTheory.ZM.galoisCover_descent X Y π Ga ρ hG).1
  obtain ⟨u, hu, -⟩ := hD _ (finiteQuotient.π τ) fun a => by
    simpa only [inv_inv] using (show ρ a⁻¹⁻¹ ≫ _ = _ from hq.comp_eq a⁻¹)
  let v := hq.desc π fun a => hG.inv a⁻¹
  have hv : finiteQuotient.π τ ≫ v = π := hq.comp_desc _ _
  have : IsIso u := ⟨v, (hD Y π hG.inv).unique (by rw [reassoc_of% hu, hv]) (Category.comp_id _),
    hq.hom_ext (by rw [reassoc_of% hv, hu, Category.comp_id])⟩
  obtain ⟨L, hL⟩ := exists_isAmpleLB_of_isAffineQuotient hq hX
  exact (hL.pull_of_isAffineHom u).isQProjOver sY

end GlobalTheory.GaloisQuotientRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor

namespace GlobalTheory.DetLine

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E}

section Generic

variable {S X : Scheme.{0}} {F : Type} [Field F]

def FrameCover (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) (p q : ℕ) : Prop :=
  ∀ z ∈ V, ∃ (W : X.Opens) (hW : IsAffineOpen W) (j : F →+* Γ(X, W))
    (v : Fin p → (epsAt ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) ⟶ t.G))
    (w : Fin q → (epsAt ((show Sp Γ(X, W) ⟶ X from hW.fromSpec) ≫ π) ⟶ t.G)),
    z ∈ W ∧ IsFrame t π s V χ j (show Sp Γ(X, W) ⟶ X from hW.fromSpec) v w

def IsChg (t : SAB H S) (π : X ⟶ S) {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R')
    (x : Sp R ⟶ X) (v : Fin p → (epsAt (x ≫ π) ⟶ t.G)) (w : Fin q → (epsAt (x ≫ π) ⟶ t.G))
    (x' : Sp R' ⟶ X) (v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)) (w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G))
    (M : Matrix (Fin p) (Fin p) R') (N : Matrix (Fin q) (Fin q) R') : Prop :=
  x' = spMap g ≫ x ∧
    (∀ i, FramedFlatCoordinates.IsCombination (x' ≫ π) (M i) (fun k => spMap (Chart.dualMapR g) ≫ (v k).left) (v' i)) ∧
    ∀ i, FramedFlatCoordinates.IsCombination (x' ≫ π) (N i) (fun k => spMap (Chart.dualMapR g) ≫ (w k).left) (w' i)

def locPt (Y : Scheme.{0}) (y : Y) : Sp (Y.presheaf.stalk y) ⟶ Y := Y.fromSpecStalk y

def genPt (Y : Scheme.{0}) [IsIntegral Y] : Sp Y.functionField ⟶ Y := Y.fromSpecStalk (genericPoint Y)

def UnitAtPt (t : SAB H S) (π : X ⟶ S) (s : X ⟶ Sp F) (V : Set X) (χ : 𝓞 E →+* F) {p q : ℕ}
    {Y : Scheme.{0}} [IsIntegral Y] (io : Y ⟶ X) (v₀ : Fin p → (epsAt ((genPt Y ≫ io) ≫ π) ⟶ t.G))
    (w₀ : Fin q → (epsAt ((genPt Y ≫ io) ≫ π) ⟶ t.G)) (δ : Y.functionField) (y : Y) : Prop :=
  ∃ (j : F →+* Y.presheaf.stalk y) (v : Fin p → (epsAt ((locPt Y y ≫ io) ≫ π) ⟶ t.G))
    (w : Fin q → (epsAt ((locPt Y y ≫ io) ≫ π) ⟶ t.G)) (M : Matrix (Fin p) (Fin p) Y.functionField)
    (N : Matrix (Fin q) (Fin q) Y.functionField) (u : (Y.presheaf.stalk y)ˣ),
    IsFrame t π s V χ j (locPt Y y ≫ io) v w ∧
    IsChg t π (algebraMap (Y.presheaf.stalk y) Y.functionField) (locPt Y y ≫ io) v w (genPt Y ≫ io) v₀ w₀ M N ∧
    N.det * algebraMap (Y.presheaf.stalk y) Y.functionField u = M.det * δ

end Generic

variable {D : Datum H} {l : Level H}

theorem comp_chi (c : Coeff l) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) :
    j.comp (HermitianCompactForm.chi c τ) = FramedFlatCoordinates.chr c τ j := rfl

theorem comp_chi_bar (c : Coeff l) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) :
    j.comp ((HermitianCompactForm.chi c τ).comp (H.bar : 𝓞 E →+* 𝓞 E)) = FramedFlatCoordinates.chr c (conjEmb τ) j := by
  refine RingHom.ext fun a => congrArg j (Subtype.ext ?_)
  change τ ((H.bar a : 𝓞 E) : E) = starRingEnd ℂ (τ (a : E))
  rw [H.bar_eq]
  exact IsCMField.complexEmbedding_complexConj E τ _

section Laws

variable {S X : Scheme.{0}} {c : Coeff l} {t : SAB H S} {π : X ⟶ S} {s : X ⟶ Sp c.F} {V : Set X} {τ : E →+* ℂ}
  {p q : ℕ} {R R' : Type} [CommRing R] [CommRing R']

theorem exists_pull (g : R →+* R') {j : c.F →+* R} {x : Sp R ⟶ X} {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)}
    {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)} (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) {x' : Sp R' ⟶ X}
    (hx : x' = spMap g ≫ x) :
    ∃ (v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)) (w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)),
      IsFrame t π s V (HermitianCompactForm.chi c τ) (g.comp j) x' v' w' ∧
      (∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left) ∧
      ∀ i, (w' i).left = spMap (Chart.dualMapR g) ≫ (w i).left := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e : x' ≫ π = spMap g ≫ x ≫ π := by rw [hx, Category.assoc]
  rw [comp_chi_bar] at h4
  obtain ⟨v', a, a'⟩ := DetExtendZero.exists_basis (FlatRow.eigStable t c) g e (τ := τ) h3
  obtain ⟨w', b, b'⟩ := DetExtendZero.exists_basis (FlatRow.eigStable t c) g e (τ := conjEmb τ) h4
  refine ⟨v', w', ⟨?_, ?_, a, by rw [comp_chi_bar]; exact b⟩, a', b'⟩
  · rw [hx, Category.assoc, h1, DetExtendZero.spMap_comp]
  · rintro _ ⟨z, rfl⟩
    rw [hx, Scheme.Hom.comp_apply]
    exact h2 ⟨_, rfl⟩

theorem exists_chg (g : R →+* R') {j : c.F →+* R} {j' : c.F →+* R'} {x : Sp R ⟶ X}
    {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)} {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)} {x' : Sp R' ⟶ X}
    {v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)} {w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w') (hx : x' = spMap g ≫ x) :
    j' = g.comp j ∧ ∃ M N, IsChg t π g x v w x' v' w' M N := by
  obtain ⟨v₁, w₁, h₁, a, b⟩ := exists_pull g h hx
  have hj : j' = g.comp j := by
    have := h'.1.symm.trans h₁.1
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
  subst hj
  choose M hM using fun i => (h₁.2.2.1.2 _ (h'.2.2.1.1 i)).exists
  choose N hN using fun i => (h₁.2.2.2.2 _ (h'.2.2.2.1 i)).exists
  refine ⟨rfl, Matrix.of M, Matrix.of N, hx, fun i => ?_, fun i => ?_⟩
  · simp only [← a]; exact hM i
  · simp only [← b]; exact hN i

theorem sec_chg {σ : Rule t π p q} (hσ : IsSection t π s V (HermitianCompactForm.chi c τ) σ) {g : R →+* R'} {j : c.F →+* R}
    {j' : c.F →+* R'} {x : Sp R ⟶ X} {v : Fin p → (epsAt (x ≫ π) ⟶ t.G)} {w : Fin q → (epsAt (x ≫ π) ⟶ t.G)}
    {x' : Sp R' ⟶ X} {v' : Fin p → (epsAt (x' ≫ π) ⟶ t.G)} {w' : Fin q → (epsAt (x' ≫ π) ⟶ t.G)}
    (h : IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w) (h' : IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w') {M N}
    (hc : IsChg t π g x v w x' v' w' M N) : N.det * g (σ R x v w) = M.det * σ R' x' v' w' := by
  obtain ⟨v₁, w₁, h₁, a, b⟩ := exists_pull g h hc.1
  obtain rfl := (exists_chg g h h' hc.1).1
  rw [← hσ.1 R R' g (Chart.dualMapR g) j _ x x' v w v₁ w₁ (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by ext <;> simp [Chart.dualMapR]) h h₁ hc.1 a b]
  refine hσ.2 R' _ x' v₁ w₁ v' w' M N h₁ h' (fun i => ?_) fun i => ?_
  · have := hc.2.1 i
    simp only [← a] at this
    exact this
  · have := hc.2.2 i
    simp only [← b] at this
    exact this

theorem isSection_of_chg {σ : Rule t π p q}
    (hσ : ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (j : c.F →+* R) (j' : c.F →+* R') x v w x' v' w' M N,
      IsFrame t π s V (HermitianCompactForm.chi c τ) j x v w → IsFrame t π s V (HermitianCompactForm.chi c τ) j' x' v' w' → IsChg t π g x v w x' v' w' M N →
      N.det * g (σ R x v w) = M.det * σ R' x' v' w') : IsSection t π s V (HermitianCompactForm.chi c τ) σ := by
  refine ⟨fun R R' _ _ g gε j j' x x' v w v' w' h1 h2 h h' hx a b => ?_, fun R _ j x v w v' w' M N h h' a b => ?_⟩
  · obtain rfl : gε = Chart.dualMapR g := by
      refine RingHom.ext fun z => ?_
      have e : z = algebraMap R _ z.fst + algebraMap R _ z.snd * DualNumber.eps := by
        ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
      rw [e, map_add, map_mul, h1, h1, h2]
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    have := hσ R R' g j j' x v w x' v' w' 1 1 h h' ⟨hx, fun i => ?_, fun i => ?_⟩
    · simpa using this.symm
    · simp only [← a]; exact DetExtendZero.comb_one (fun k => (h'.2.2.1.1 k).1) i
    · simp only [← b]; exact DetExtendZero.comb_one (fun k => (h'.2.2.2.1 k).1) i
  · refine hσ R R (RingHom.id R) j j x v w x v' w' M N h h'
      ⟨by rw [DetExtendZero.spMap_id, Category.id_comp], fun i => ?_, fun i => ?_⟩
    · simp only [DetExtendZero.dual_id, Category.id_comp]; exact a i
    · simp only [DetExtendZero.dual_id, Category.id_comp]; exact b i

end Laws

section Concrete

variable (Xo : Moduli D l) (c : Coeff l)

abbrev FrU (U : Set (Xo.XF c)) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Xo.XF c)
    (v : Fin D.p → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) (w : Fin D.q → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)) : Prop :=
  IsFrame Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) j x v w

abbrev RuleU : Type 1 := Rule Xo.univ.t (toX Xo c) D.p D.q

abbrev SecU (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) : Prop :=
  IsSection Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ

abbrev NzU (U : Set (Xo.XF c)) (τ : E →+* ℂ) (σ : RuleU Xo c) : Prop :=
  NowhereZero Xo.univ.t (toX Xo c) (toF Xo c) U (HermitianCompactForm.chi c τ) σ

variable {Xo c} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

abbrev FrY (V : Set (gen Y)) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ gen Y)
    (v : Fin D.p → (epsAt (x ≫ genι Y) ⟶ Y.t.G)) (w : Fin D.q → (epsAt (x ≫ genι Y) ⟶ Y.t.G)) : Prop :=
  IsFrame Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) j x v w

abbrev RuleY : Type 1 := Rule Y.t (genι Y) D.p D.q

abbrev SecY (V : Set (gen Y)) (τ : E →+* ℂ) (σ : RuleY Y) : Prop :=
  IsSection Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) σ

abbrev NzY (V : Set (gen Y)) (τ : E →+* ℂ) (σ : RuleY Y) : Prop :=
  NowhereZero Y.t (genι Y) (genStr Y) V (HermitianCompactForm.chi c τ) σ

variable {Y}

def Match (τ : E →+* ℂ) {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Y.X} (f : EigFrame Y φ x)
    (v : Fin D.p → (epsAt x ⟶ Y.t.G)) (w : Fin D.q → (epsAt x ⟶ Y.t.G)) : Prop :=
  (∀ (i : Fin D.p) (k : Fin (D.mult τ)), (i : ℕ) = k → (v i).left = f.v τ k) ∧
    ∀ (i : Fin D.q) (k : Fin (D.mult (conjEmb τ))), (i : ℕ) = k → (w i).left = f.v (conjEmb τ) k

def PerData (c : Coeff l) (e : c.F →+* ℂ) (Di : Datum H) {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
    (P : Di.La →+ (Fin g → ℂ)) (W : Pad.Letter D → Fin g → ℂ) (Q : Di.La →+ (Pad.Letter D → ℂ)) : Prop :=
  Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (herm Hm z z).re) ∧ Submodule.span ℝ (Set.range P) = ⊤ ∧
    (∀ a b, (herm Hm (P a) (P b)).im = Di.EF a b) ∧ LinearIndependent ℂ W ∧ (∀ v, P v = ∑ z, Q v z • W z) ∧
    ∀ (a : 𝓞 E) v (z : Pad.Letter D), Q (a • v) z = Formalism.L2.PjFree.relab c e z.1 (a : E) * Q v z

def MatchVec (τ : E →+* ℂ) {g : ℕ} (W : Pad.Letter D → Fin g → ℂ) (V : Fin D.p → Fin g → ℂ)
    (W₀ : Fin D.q → Fin g → ℂ) : Prop :=
  (∀ (i : Fin D.p) (k : Fin (D.mult τ)), (i : ℕ) = k → V i = W ⟨τ, k⟩) ∧
    ∀ (i : Fin D.q) (k : Fin (D.mult (conjEmb τ))), (i : ℕ) = k → W₀ i = W ⟨conjEmb τ, k⟩

end Concrete

end GlobalTheory.DetLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShortRuleOfRaw
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain

set_option autoImplicit false

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

namespace GlobalTheory.RawSpan

theorem isShortRule_of_raw : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ {n : ℕ} {Λ : GenLat E n} {N : ℕ},
    Λ.Unimod → Λ.TrivAt l.M → Λ.LevOK N l.M → ∀ {a : (E →+* ℂ) × ℕ → ℕ} {P : MvPolynomial (LtN Dw n) c.F},
    P ∈ harmL c Λ a → ∀ (x0 : Fin n → Dw.La) (f : Rul Xo c), f ∈ sec Xo c a n →
    (∀ (p : TRing c.F) (y : FrPt Xo c p.R), thLaValAt Xo c nab (x0Dat c x0) Λ N P y (f p y)) →
    IsShortRule Xo c (GlobalTheory.RawSpan.idCover nab n) Λ N x0 P ((betaH (Dw := Dw) c Λ)⁻¹ • f) := by
  intro E _ _ _ H Dw l Xo c _ nab hnab n Λ N hU hT hO a P hP x0 f hf h
  intro k _ _ i1 i2 hk y y₂ hov
  have e : i1 = i2 := (Algebra.algebra_ext _ _ fun a => hk a).symm
  subst e
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  letI : Algebra (idCover nab n).c₂.F k := i1
  have hyy : (y₂ : FrPt Xo c k) = y :=
    GlobalTheory.CoverSec.frOver_unique (idCover nab n) hL.globalFns (frOver_self nab n y₂) hov
  subst hyy
  have hβ := betaH_ne_zero (Dw := Dw) (c := c) Λ
  have hAT := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l Xo c
  have hW := (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw l Xo c).2.2.1
  obtain ⟨p, φ, y0, h0⟩ := hAT k y₂
  obtain ⟨hval, hnat⟩ := GlobalTheory.shortThetaValue_existsUnique_natural hL GlobalTheory.chartIndependence_unconditional E H Dw l Xo c
    nab hnab n Λ N hU hT hO a P hP.1 (x0Dat c x0) 1
  obtain ⟨v1, hv1, -⟩ := hval k y₂
  have e1 : φ (f p y0) = v1 := hnat p.R k φ y0 y₂ h0 _ _ (h p y0) hv1
  have hsm : (betaH (Dw := Dw) c Λ)⁻¹ • f ∈ sec Xo c a n := Submodule.smul_mem _ _ hf
  have e2 : evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂ = φ (((betaH (Dw := Dw) c Λ)⁻¹ • f) p y0) :=
    GlobalTheory.CoverDescent.evR_of_test hW _ hsm.1 p φ y0 y₂ h0
  have e3 : ((betaH (Dw := Dw) c Λ)⁻¹ • f) p y0 = algebraMap c.F p.R (betaH (Dw := Dw) c Λ)⁻¹ * f p y0 :=
    Algebra.smul_def (betaH (Dw := Dw) c Λ)⁻¹ (f p y0)
  refine ⟨evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂, ?_, ?_⟩
  · have e4 : MvPolynomial.map ((idCover nab n).eF : c.F →+* (idCover nab n).c₂.F) P = P := MvPolynomial.map_id P
    rw [e4, GlobalTheory.LevelCoverDatum.noDelta_w]
    refine (GlobalTheory.Survey.BaseClassMove.shortValAt_beta Xo c nab _ Λ (betaH (Dw := Dw) c Λ) hβ N P y₂ _).2 ?_
    rw [e2, e3, map_mul, AlgHom.commutes, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hβ, map_one, one_mul, e1]
    exact hv1
  · exact ((congrArg (· * evR Xo c ((betaH (Dw := Dw) c Λ)⁻¹ • f) y₂) (evR_one_field k y₂)).trans (one_mul _)).symm
end GlobalTheory.RawSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitThetaKeyScalarGoodReductionChart
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.KeyUnitGood

theorem exists_unit_of_map {R K A B : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] [Field B] [Algebra A B] [IsFractionRing A B] (e : R →+* A)
    [IsLocalHom e] (la : K →+* B) (hla : ∀ r, la (algebraMap R K r) = algebraMap A B (e r)) (x : K) (u : Aˣ)
    (hx : la x = algebraMap A B u) : ∃ v : Rˣ, x = algebraMap R K v := by
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · have h : e r = u := IsFractionRing.injective A B (by rw [← hla, hr, hx])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ u.isUnit)
    exact ⟨v, hr.symm⟩
  · have h : e r = (u⁻¹ : Aˣ) := IsFractionRing.injective A B (by rw [← hla, hr, map_inv₀, hx, map_units_inv])
    obtain ⟨v, rfl⟩ : IsUnit r := isUnit_of_map_unit e r (h ▸ (u⁻¹).isUnit)
    exact ⟨v⁻¹, by rw [map_units_inv, hr, inv_inv]⟩

theorem isUnit_key_of_good : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), ∀ κ : KeyRule, IsKeyRule κ → ∀ (M : GChart Y) (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (y : Sp K ⟶ Xo.XF c), y ≫ Y.j = spMap (algebraMap R K) ≫ z → Set.range z ⊆ abLocus Y.t.G → ∀ x : KeyIn K, KeyAt M (spMap (algebraMap R K) ≫ z) (le_preimage_comp _ hz) x → ∃ u : Rˣ, (κ K x : K) = algebraMap R K u := by
  intro E _ _ _ H D l Xo c O _ β Y κ hκ M R K _ _ _ _ _ _ _ z hz y hy hab x hx
  have : CharZero R := (algebraMap R K).charZero
  obtain ⟨T, i, hi, hil⟩ : ∃ (T : Formalism.L2.Pj.CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i :=
    ⟨GlobalTheory.CountableCompletion.completionCDVR R, algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R),
      GlobalTheory.algebraMap_adicCompletion_injective_of_dvr R, inferInstance⟩
  have hiF : Function.Injective ((algebraMap T.V T.Fr).comp i) := (IsFractionRing.injective T.V T.Fr).comp hi
  let iK : K →+* T.Fr := IsFractionRing.lift hiF
  have hiK : ∀ r, iK (algebraMap R K r) = algebraMap T.V T.Fr (i r) := fun r => IsFractionRing.lift_algebraMap hiF r
  have hsq : spMap iK ≫ spMap (algebraMap R K) = spMap (algebraMap T.V T.Fr) ≫ spMap i := by
    rw [← GlobalTheory.KeyAtBC.spMap_comp₀, ← GlobalTheory.KeyAtBC.spMap_comp₀]
    exact congrArg spMap (RingHom.ext hiK)
  have hpt : spMap iK ≫ spMap (algebraMap R K) ≫ z = spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z := by
    rw [← Category.assoc, hsq, Category.assoc]
  obtain ⟨t, ⟨m⟩⟩ := exists_sab (spMap i ≫ z) Y.t
  obtain ⟨tK, ⟨mK⟩⟩ := exists_sab (spMap (algebraMap T.V T.Fr)) t
  obtain ⟨n, -⟩ := ObjMaps.exists_sab_comp m mK
  have hj : spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z = (spMap iK ≫ y) ≫ Y.j := by
    rw [← hpt, Category.assoc, hy]
  obtain ⟨n₁, -⟩ := ObjMaps.exists_sab_cancel (show SABMap Y.oF.t Y.t Y.j from Y.m) (hj ▸ n)
  obtain ⟨n₂, -⟩ := ObjMaps.exists_sab_comp Y.m0.toSABMap n₁
  have hp : IsProper t.G.hom := GlobalTheory.GoodProper.isProper_of_abLocus_eq_univ E H D l Xo T _ t tK n₂ mK
    (Set.eq_univ_of_forall fun q => (abLocus_pullback abLocusOne Y.t.semi m.cart.1 q).1
      (hab ⟨spMap i q, (Scheme.Hom.comp_apply _ _ _).symm⟩))
  obtain ⟨-, hA, hK⟩ := GlobalTheory.GenericPol.proper_ample_kTriv (show SABMap Y.oF.t Y.t Y.j from Y.m)
    Y.oF.proper Y.oF.ample Y.oF.ktriv n (by
      rw [hj]
      rintro _ ⟨q, rfl⟩
      exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩)
  have hA' : Out.RelAmple t.G t.PP.L := GlobalTheory.GoodPol.relAmple_of_generic GlobalTheory.firstFiveLaws.1
    ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩ t.cub mK.cart tK.PP.isLB
    (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mK) hA hK
  obtain ⟨x', hx'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x iK
  have hzT : ⊤ ≤ (spMap i ≫ z) ⁻¹ᵁ M.U := le_preimage_comp _ hz
  have h₁ : KeyAt M (spMap (algebraMap T.V T.Fr) ≫ spMap i ≫ z) (le_preimage_comp _ hzT) x' := by
    have cast : ∀ (p q : Sp T.Fr ⟶ Y.X) (_ : p = q) hp hq, KeyAt M p hp x' → KeyAt M q hq x' := by
      rintro p q rfl _ _ h
      exact h
    exact cast _ _ hpt _ _ (GlobalTheory.KeyAtBC.keyAt_of_keyPB hx hx')
  obtain ⟨xT, -, hT⟩ := GlobalTheory.KeyAtFam.exists_keyAt_of_point M hzT m hp hA' _ h₁
  obtain ⟨u, hu, -⟩ := hκ.2.2.1 T.V T.Fr xT x' (GlobalTheory.KeyAtBC.keyPB_of_keyAt hT h₁)
  exact exists_unit_of_map i iK hiK _ u ((hκ.2.1 K T.Fr iK x x' hx').symm.trans hu)

end GlobalTheory.KeyUnitGood
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsolatedInFibreOfEtaleRestrictionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isolated_in_fibre_of_etale_restriction : ∀ (M W : Scheme.{0}) (f : M ⟶ W) (U : W.Opens), Etale (f ∣_ U) → ∀ z : M, f z ∈ U → ∃ V : M.Opens, z ∈ V ∧ ∀ y ∈ V, f y = f z → y = z := by
  first | exact @GlobalTheory.isolated_in_fibre_of_etale_restrict | exact GlobalTheory.isolated_in_fibre_of_etale_restrict | (intros; apply GlobalTheory.isolated_in_fibre_of_etale_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelChangeLocallyFiniteTypeStatement
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_change_locally_finite_type : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} (r : Xo'.XF c' ⟶ Xo.XF c) (hle : c.F ≤ c'.F), GlobalTheory.FlatModel.OverIncl r hle → LocallyOfFiniteType r := by
  first | exact @GlobalTheory.FlatModel.locallyOfFiniteType_of_overIncl | exact GlobalTheory.FlatModel.locallyOfFiniteType_of_overIncl | (intros; apply GlobalTheory.FlatModel.locallyOfFiniteType_of_overIncl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPrintsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_index_bound_of_classicalTheorems : ∀ (hP : Hypotheses2) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.IndexBound C i P := by
  first | exact @GlobalTheory.CovTop.LevelIndex.indexBound | exact GlobalTheory.CovTop.LevelIndex.indexBound | (intros; apply GlobalTheory.CovTop.LevelIndex.indexBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleSymmetryHypothesis_baseChange : ∀ (K K' : Type) [Field K] [Field K'] (f : K →+* K') (P : PolAV (Sp K)) (P' : PolAV (Sp K')) (ψ : P'.A.left ⟶ P.A.left), IsPolFibre f P P' ψ → (letI := P.isAb.comm; GlobalTheory.ZH.HypS P.A P.L) → (letI := P'.isAb.comm; GlobalTheory.ZH.HypS P'.A P'.L) := by
  first | exact @GlobalTheory.MBLow.hypS_of_isPolFibre | exact GlobalTheory.MBLow.hypS_of_isPolFibre | (intros; apply GlobalTheory.MBLow.hypS_of_isPolFibre <;> assumption)
end

