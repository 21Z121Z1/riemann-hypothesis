import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0737
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0738
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0742
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0424
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralRationalAtMember
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenRatAt

theorem transfer {K G Pl0 V : Type} [Field K] [NumberField K] [StarRing K] [Group G] [Fintype G]
    (B B' : Formalism.L2.DIV.BlockDat K G Pl0) (hB : B = B') (ℓ : Formalism.L2.DIV.Lvl K G) (Q : V → V → Prop)
    (e : (Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K) → V) (e' : (Fin (B'.S.lvlDim B'.r ℓ.P ℓ.ψ) → K) → V)
    (h : GlobalTheory.Mem.Top.Bl.SameOn e e') (a : MonoidAlgebra K G)
    (H : ∀ x, Q (e x) (e ((B.S.lvlOp B.r ℓ.P ℓ.ψ a).mulVec x))) (x' : Fin (B'.S.lvlDim B'.r ℓ.P ℓ.ψ) → K) :
    Q (e' x') (e' ((B'.S.lvlOp B'.r ℓ.P ℓ.ψ a).mulVec x')) := by
  subst hB
  have he : e = e' := funext fun x => h.2 x x fun i i' hi => congrArg x (Fin.ext hi)
  subst he
  exact H x'

theorem famR_L_eq (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U U' : Set I.ι)
    (Xg : Finset (R3.Gc X.B px → X.B.LL)) (tr tr' : R3.TrI X.B px) (k : Fin X.toD7.R.m) (s : R3.TupU I U) (s' : R3.TupU I U')
    (h : s.1 = s'.1) : (R3.famR X I hX U Xg tr).A.fam.L k s = (R3.famR X I hX U' Xg tr').A.fam.L k s' := by
  obtain ⟨τ, hτ⟩ := s
  obtain ⟨τ', hτ'⟩ := s'
  cases h
  rfl

section Main

variable {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {p0 : BaseLevelRowSide (w.D Z)}

set_option maxHeartbeats 1000000 in

theorem cenRat_of (t : RowsT K w Z Wt p0) (r : RXs t) : GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG := by
  intro s k z a ha x
  have h5 : (tAll w.I (t.r.Y.tup s)).1 = s.1 := (congrArg w.I.tup (t.r.tup_ix s)).trans (R3.tup_ixOf w.I s)
  have h3 := (r.all.cen (t.r.Y.tup s) z a ha).2.2 k
  exact transfer _ _ (famR_L_eq (w.st Z) w.I t.hX _ _ _ _ _ k _ _ h5) _
    (fun u v => (w.st Z).toD7.ntypes.cenMt (t.r.Y.tup s) ((k : ℕ) + 1) z ((w.st Z).toD7.what₂.jMt (t.r.Y.tup s) ((k : ℕ) + 1) u) =
      (w.st Z).toD7.what₂.jMt (t.r.Y.tup s) ((k : ℕ) + 1) v)
    (r.all.eMt k (t.r.Y.tup s)) (t.r.Y.eMt k s) (r.eMt_use k s) a h3 x

end Main

theorem cenRat_at : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ _ _ _ _ t _ _ _ => GlobalTheory.CenLocAt.CenRat t.r.Y t.r.z.cG :=
  fun _ => GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ t _ _ _ _ _ hR _ => hR.elim fun r => cenRat_of t r

end GlobalTheory.CenRatAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentreDepthLeStarDepthOfCellStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centreDepth_le_starDepth_of_cell : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X) (t : ℝ), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X → (∀ y, 0 ≤ v y y) → w.evalZ v = 1 → InRCone γ v → v ≠ 0 → (∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v) → 0 ≤ t → B - t • toReal v ∈ rcone γ → t ≤ evalR (starDepth bar ψ w) B := by
  first | exact @GlobalTheory.PolFan.depth_le_starDepth | exact GlobalTheory.PolFan.depth_le_starDepth | (intros; apply GlobalTheory.PolFan.depth_le_starDepth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTrivialOnUnipotentStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_trivial_on_unipotent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N), 1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (γ : X.Γ), (((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → φ γ = 1 := by
  first | exact @GlobalTheory.UnipKill.char_eq_one_of_sq_eq_zero | exact GlobalTheory.UnipKill.char_eq_one_of_sq_eq_zero | (intros; apply GlobalTheory.UnipKill.char_eq_one_of_sq_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharactersRestrictLinearToTraitUniformisationStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characters_restrict_linear_to_trait_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), IsCN R → P.TorsionIso →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (g : R →+* W) (hg : Function.Injective g), ¬ IsLocalHom g →
    ∀ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap g)) (P' : PELUnif (maximalIdeal W) t'),
      ∃ ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X, Function.Surjective ρ ∧
        ∀ (a b : P.D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing W)ˣ),
          GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P.D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ a) (ρ b) x' →
          ∃ u : Wˣ, IsFractionRing.lift (A := R) (K := FractionRing R)
              (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) (x : FractionRing R) =
            algebraMap W (FractionRing W) (u : W) * (x' : FractionRing W) := by
  first | exact @GlobalTheory.TauForm.main | exact GlobalTheory.TauForm.main | (intros; apply GlobalTheory.TauForm.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjMulTransposeInvStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_modelGram_conjMulTranspose_inv : ∀ {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n), (1 - (Z w)ᴴ * Z w).PosDef → curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η = -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := by
  first | exact @GlobalTheory.PointChern.curv_modelGram_lie | exact GlobalTheory.PointChern.curv_modelGram_lie | (intros; apply GlobalTheory.PointChern.curv_modelGram_lie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjugateEmbeddingStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernCurvature_modelGram_conjugateEmbedding : ∀ {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n), (1 - (Z w)ᴴ * Z w).PosDef → curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η = -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := by
  first | exact @GlobalTheory.PointChern.curv_modelGram_tauBar | exact GlobalTheory.PointChern.curv_modelGram_tauBar | (intros; apply GlobalTheory.PointChern.curv_modelGram_tauBar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffReindexFrameStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernFormPolyCoeff_reindex_frame : ∀ {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ), chernPoly (fun u => Matrix.reindex e e (F u)) v k = chernPoly F v k := by
  first | exact @GlobalTheory.ChernReindex.chernPoly_reindex | exact GlobalTheory.ChernReindex.chernPoly_reindex | (intros; apply GlobalTheory.ChernReindex.chernPoly_reindex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyConjLinearSubstCurvatureStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPoly_conj_linearSubst_curvature : ∀ {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n) (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ), IsUnit S.det → (∀ a b, curv F v (coordVec a) (coordVec b) = S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) → ∀ k, chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) (chernPoly F v' k) := by
  first | exact @GlobalTheory.ChernConj.chernPoly_conj_subst | exact GlobalTheory.ChernConj.chernPoly_conj_subst | (intros; apply GlobalTheory.ChernConj.chernPoly_conj_subst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityGrassmannRelationOriginZeroStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernPolyTopDensity_grassmannRelation_origin_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (τ : GlobalTheory.AllWt.Psi H) (k : ℕ), 1 ≤ k → ∀ P : MvPolynomial ((E →+* ℂ) × ℕ) ℝ, chernTop (relPoly τ k * P) (fun u => modelGram H Dw (coordOf ix u)) 0 = 0 := by
  first | exact @GlobalTheory.PointChernRel.relation_top_zero | exact GlobalTheory.PointChernRel.relation_top_zero | (intros; apply GlobalTheory.PointChernRel.relation_top_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernRootSubstitutionWeightLineBundleEqLinRoot
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.Schubert

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem flagRoot_term_big {H : Host E} (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin Dw.p) :
    C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩) : ℝ)) *
        flagRoot Dw ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩ =
      -(C ((la τ (Fin.castAdd Dw.q i) : ℤ) : ℝ) * X (τ, Fin.castAdd Dw.q i)) := by
  have he : GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm i⟩) =
      (GlobalTheory.AllWt.wtOf Dw la 0).1 (τ.1, (i : ℕ)) := rfl
  rw [he, GlobalTheory.AllWt.wtOf_big la 0 τ i i.2]
  unfold flagRoot
  rw [dif_pos τ.2]
  simp only [sub_zero, map_neg, neg_mul, neg_neg]
  rfl

theorem flagRoot_term_small {H : Host E} (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (τ : GlobalTheory.AllWt.Psi H)
    (i : Fin Dw.q) :
    C (-(GlobalTheory.AllWt.exOf Dw la 0
          (some ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩ =
      -(C ((la τ (Fin.natAdd Dw.p (Fin.rev i)) : ℤ) : ℝ) * X (τ, Fin.natAdd Dw.p (Fin.rev i))) := by
  have he : GlobalTheory.AllWt.exOf Dw la 0
      (some ⟨conjEmb τ.1, Fin.cast (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm i⟩) =
      (GlobalTheory.AllWt.wtOf Dw la 0).1 (conjEmb τ.1, (i : ℕ)) := rfl
  have hj : (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), by omega⟩ : Fin (Dw.p + Dw.q)) = Fin.natAdd Dw.p (Fin.rev i) := by
    ext; simp [Fin.val_rev]; omega
  rw [he, GlobalTheory.AllWt.wtOf_small la 0 τ i i.2, hj]
  unfold flagRoot
  rw [dif_neg (GlobalTheory.AllWt.conj_not_mem τ)]
  have hτ : (⟨conjEmb (conjEmb τ.1), GlobalTheory.AllWt.conj_mem (GlobalTheory.AllWt.conj_not_mem τ)⟩ : GlobalTheory.AllWt.Psi H) = τ :=
    Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
  have hx : ((⟨conjEmb (conjEmb τ.1), GlobalTheory.AllWt.conj_mem (GlobalTheory.AllWt.conj_not_mem τ)⟩ : GlobalTheory.AllWt.Psi H),
      (⟨Dw.p + (Dw.q - 1 - (i : ℕ)), by omega⟩ : Fin (Dw.p + Dw.q))) = (τ, Fin.natAdd Dw.p (Fin.rev i)) := by
    rw [hτ, hj]
  simp only [Fin.val_cast] at *
  rw [hx]
  simp only [sub_zero, Int.cast_neg, neg_neg, mul_neg]

theorem chernRootSubstitution_weightLineBundle_eq_linRoot (H : Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) :
    flagMap Dw (∑ x : GlobalTheory.GoodMetric.Root Dw.mult,
        MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) =
      Formalism.DegreeFormula.linRoot (fun τ i => (la τ i : ℝ)) := by
  simp only [flagMap, map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]
  rw [Fintype.sum_sigma, ← Fintype.sum_subtype_add_sum_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  let e : GlobalTheory.AllWt.Psi H ≃ {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} :=
    { toFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
      invFun := fun τ => ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
      left_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
      right_inv := fun τ => Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _) }
  rw [← e.sum_comp]
  unfold Formalism.DegreeFormula.linRoot
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_add, Finset.sum_add_distrib, neg_add]
  congr 1
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Fin.sum_congr' (fun i => C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨τ.1, i⟩) : ℝ)) * flagRoot Dw ⟨τ.1, i⟩)
      (GlobalTheory.PointChern.mult_of_mem Dw τ.2).symm, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => flagRoot_term_big Dw la τ i
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    change ∑ i : Fin (Dw.mult (conjEmb τ.1)), C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, i⟩ = _
    rw [← Fin.sum_congr' (fun i => C (-(GlobalTheory.AllWt.exOf Dw la 0 (some ⟨conjEmb τ.1, i⟩) : ℝ)) *
        flagRoot Dw ⟨conjEmb τ.1, i⟩) (GlobalTheory.PointChern.mult_of_not_mem Dw (GlobalTheory.AllWt.conj_not_mem τ)).symm,
      ← Equiv.sum_comp (Fin.revPerm (n := Dw.q)) (fun i => C ((la τ (Fin.natAdd Dw.p i) : ℤ) : ℝ) *
        X (τ, Fin.natAdd Dw.p i)), ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => flagRoot_term_small Dw la τ i

end GlobalTheory.Schubert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientFieldEqLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

namespace GlobalTheory.HeightCounting.Up.CoefficientAgreement

theorem atMem_of_forall {hL : GlobalTheory.Published.LocalLanglandsGL} {p : LayP hL}
    (h : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c) : AtMem hL p := by
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => ?_⟩
  intro _ w Z Wt p0 t nch n xd c _ _ _
  exact h K B f T w Z Wt p0 t nch n c

theorem tied_cf : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ _ => t.r.z.R.C = TC.cf w.I w.l Z := by
  intro _ hL
  exact atMem_of_forall fun K B f T w Z Wt p0 t nch n c => t.r.z.lev.C

end GlobalTheory.HeightCounting.Up.CoefficientAgreement
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompAtBaseCharacterMulUnramifiedEqTypeCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TypeCharRead

variable {K : Type} [Field K] [NumberField K]

theorem isUnit_of_val_eq_one (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletionIntegers K)
    (h : Valued.v (x : v.adicCompletion K) = 1) : IsUnit x :=
  (Valuation.integer.integers (Valued.v (R := v.adicCompletion K))).isUnit_iff_valuation_eq_one.2 h

theorem red_eq_zero_of_val_lt_one (v : HeightOneSpectrum (𝓞 K)) {p : ℕ} [Fact p.Prime]
    (red : v.adicCompletionIntegers K →+* ZMod p) (x : v.adicCompletionIntegers K)
    (hx : Valued.v (x : v.adicCompletion K) < 1) : red x = 0 := by
  by_contra h
  have ht : (red x)⁻¹ * red x = 1 := inv_mul_cancel₀ h
  set n : ℕ := ((red x)⁻¹ : ZMod p).val with hn
  set z : v.adicCompletionIntegers K := 1 - (n : v.adicCompletionIntegers K) * x with hz
  have hrz : red z = 0 := by
    rw [hz, map_sub, map_mul, map_one, map_natCast, hn, ZMod.natCast_zmod_val, ht, sub_self]
  have hnv : Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (n : v.adicCompletionIntegers K).2
  have hlt : Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K) * (x : v.adicCompletion K)) < 1 := by
    rw [map_mul]
    calc Valued.v (((n : v.adicCompletionIntegers K) : v.adicCompletion K)) * Valued.v (x : v.adicCompletion K)
        ≤ 1 * Valued.v (x : v.adicCompletion K) := by gcongr
      _ < 1 := by rw [one_mul]; exact hx
  have hvz : Valued.v (z : v.adicCompletion K) = 1 := by
    have e : (z : v.adicCompletion K) = 1 - ((n : v.adicCompletionIntegers K) : v.adicCompletion K) * (x : v.adicCompletion K) := by
      rw [hz]; push_cast; rfl
    rw [e]
    exact Valuation.map_one_sub_of_lt _ hlt
  have hu := (isUnit_of_val_eq_one v z hvz).map red
  rw [hrz] at hu
  exact not_isUnit_zero hu

end GlobalTheory.TypeCharRead

open Formalism.L2.DIV (kP)
open Formalism.IndefR.Links (IsRes)

namespace GlobalTheory.TypeCharRead

theorem compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf →
    ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ,
    (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    ∀ χ : HChar D.host.E, χ.UnrAt s.w →
    ∀ red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1),
    ∃ ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ, NG.IsCompAt (cf.mu0 j * χ) s ξ ∧
      ∀ (y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (hy : IsUnit (red y))
        (uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ), (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = y →
          ((ξ uu : ℂˣ) : ℂ) = embLL0 D ((τ (j.1 + 1) kv hy.unit : (↥D.LL0)ˣ) : ↥D.LL0) := by
  intro hGAR D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv s hsw χ hχ red
  haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime kv.1⟩
  obtain ⟨-, -, -, h4⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D 0
  obtain ⟨φ, hφs, hφ0, hφa, -⟩ := h4 s
  have hker : RingHom.ker φ ≤ RingHom.ker red := fun x hx =>
    (RingHom.mem_ker).2 (red_eq_zero_of_val_lt_one s.v red x ((hφ0 x).1 ((RingHom.mem_ker).1 hx)))
  set ι := φ.liftOfSurjective hφs ⟨red, hker⟩ with hι
  have hιφ : ∀ x, ι (φ x) = red x := fun x => RingHom.liftOfSurjective_comp_apply φ hφs ⟨red, hker⟩ x
  have hred0 : ∀ x, red x = 0 → Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1 := by
    intro x hx
    refine lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2) (fun h1 => ?_)
    have hu := (isUnit_of_val_eq_one s.v x h1).map red
    rw [hx] at hu
    exact not_isUnit_zero hu
  let c : (kP s.w)ˣ →* ℂˣ :=
    (Units.map (embLL0 D).toMonoidHom).comp ((τ (j.1 + 1) kv).comp (Units.map ι.toMonoidHom))
  have hres : IsRes (cf.mu0 j * χ) s.w c := by
    intro a k u hk hu
    have ha : a ∉ s.w.asIdeal := by
      intro hm
      have : (u : kP s.w) = 0 := by rw [hu]; exact Ideal.Quotient.eq_zero_iff_mem.2 hm
      exact u.ne_zero this
    have ha0 : ((a : 𝓞 D.host.E) : D.host.E) ≠ 0 := hk ▸ k.ne_zero
    obtain ⟨hia, hφia⟩ := hφa a
    set x : (ZMod (D.host.g kv.1))ˣ := Units.map ι.toMonoidHom u with hx
    have hxv : (x : ZMod (D.host.g kv.1)) = red ⟨_, hia⟩ := by
      show ι (u : kP s.w) = _
      rw [hu, ← hφia, hιφ]
    have hmem : (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a) ∈ (NX.pG D kv).asIdeal := by
      rw [← hsw]
      obtain ⟨hib, hφib⟩ := hφa (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a)
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hφib]
      apply (hφ0 _).2
      apply hred0
      have e : (⟨_, hib⟩ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) =
          (((x : ZMod (D.host.g kv.1)).val : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E))) - ⟨_, hia⟩ := by
        apply Subtype.ext
        show s.i (((((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - a : 𝓞 D.host.E)) : D.host.E) = _
        push_cast
        rw [map_sub, map_natCast]
      rw [e, map_sub, map_natCast, ZMod.natCast_zmod_val, hxv, sub_self]
    have h61 := GlobalTheory.T.levelCharacters_typePlaces_eq_local_components hGAR D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv x a ha0 hmem
    have hunit : IsUnitAt s.w (atFin s.w k) := by
      have e := GlobalTheory.ChainOnto.TameRes.val_alg s.w (k : D.host.E)
      show Valued.v (algebraMap D.host.E (s.w.adicCompletion D.host.E) (k : D.host.E)) = 1
      rw [e, hk]
      exact GlobalTheory.ChainOnto.TameRes.valuation_eq_one_of_not_mem s.w a ha
    have h2 : χ.locK s.w k = 1 := hχ _ hunit
    have hk' : Units.mk0 ((a : 𝓞 D.host.E) : D.host.E) ha0 = k := Units.ext hk.symm
    rw [hk', ← hsw] at h61
    apply Units.ext
    have e : (cf.mu0 j * χ).locK s.w k = (cf.mu0 j).locK s.w k * χ.locK s.w k := rfl
    rw [e, h2, mul_one, ← h61]
    rfl
  obtain ⟨ξ, hξc, hξr⟩ := GlobalTheory.T.exists_splitPlaceComponent_heckeChar_residue D s φ hφs hφ0 hφa _ c hres
  refine ⟨ξ, hξc, fun y hy uu huu => ?_⟩
  have hyv : Valued.v (y : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 := by
    refine le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2) (not_lt.1 fun hlt => ?_)
    have h0 := red_eq_zero_of_val_lt_one s.v red y hlt
    rw [h0] at hy
    exact not_isUnit_zero hy
  have hyu : IsUnit (φ y) := (isUnit_of_val_eq_one s.v y hyv).map φ
  rw [hξr uu y hyu.unit huu.symm hyu.unit_spec.symm]
  have hw : Units.map ι.toMonoidHom hyu.unit = hy.unit := by
    apply Units.ext
    show ι ((hyu.unit : kP s.w)) = red y
    rw [hyu.unit_spec, hιφ]
  show (embLL0 D) ((τ (j.1 + 1) kv (Units.map ι.toMonoidHom hyu.unit) : (↥D.LL0)ˣ) : ↥D.LL0) = _
  rw [hw]

end GlobalTheory.TypeCharRead

end
end

