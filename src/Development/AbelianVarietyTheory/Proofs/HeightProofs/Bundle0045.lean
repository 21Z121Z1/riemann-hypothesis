import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0041
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SpanResCharNeBot

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms Matrix NumberField
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothForms.RealPts

theorem infEmb_unique {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (τ : E →+* ℂ) (θ θ' : Ainf F ⊗[F] E →+* ℂ) (h : IsInfEmb τ θ) (h' : IsInfEmb τ θ') :
    θ = θ' :=
  by apply _root_.UpperTheory.Reformulated.B.Qh26.isInfEmb_unique <;> assumption

theorem tauE_injective (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem tauE_cm (D : D7) (σ : D.host.E →+* ℂ) :
    (∃ τ, tauE D τ = σ) ↔ ¬ ∃ τ, tauE D τ = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 σ
  have hc : ComplexEmbedding.conjugate (D.host.emb g) = D.host.emb (g * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    have hcm := D.host.isCMField_hostE
    have h : IsCMField.complexConj D.host.E x = D.host.conj x := by
      apply D.host.φ₀.injective
      rw [IsCMField.complexEmbedding_complexConj]
      exact (D.host.toHostAx.conjE_apply _ x).symm
    show starRingEnd ℂ (D.host.emb g x) = D.host.emb g (D.host.conj x)
    rw [← h, IsCMField.complexEmbedding_complexConj]
  have h : ∀ g, (∃ τ, tauE D τ = D.host.emb g) ↔ g ∈ D.R.Psi := fun g => by
    rw [← Formalism.L2.Geo.exists_tauEmb_iff D g]
    exact exists_congr fun τ => eq_comm
  rw [hc, h, h]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem gramAt_herm {D : D7} (V : HSp D) (τ : D.what₂.Tau) : (gramAt D V τ)ᴴ = gramAt D V τ := by
  ext i j
  have hcm := D.host.isCMField_hostE
  have h1 : star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j) := V.herm.eq _ _
  simp only [conjTranspose_apply, gramAt, map_apply, HSpace.gram]
  rw [← h1]
  exact (IsCMField.complexEmbedding_complexConj _ (tauE D τ) _).symm

theorem gramAt_unit {D : D7} (V : HSp D) (τ : D.what₂.Tau) : IsUnit (gramAt D V τ).det := by
  have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det _ _).symm
  rw [this, isUnit_iff_ne_zero]
  exact (map_ne_zero _).2 (GlobalTheory.UnitaryGlue.gram_det_ne_zero V)

theorem infMat_eq {D : D7} (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    infMat D.sp.cm.sig V.gram θ g = (infHom V g).1.map θ := rfl

theorem finMat_eq {D : D7} (V : HSp D) (g : GA D V) :
    finMat D.sp.cm.sig V.gram g = (finHom V g).1 := rfl

theorem glue {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) :
    (∀ g : GA D V, (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = 1) → g ∈ GfC V) ∧
    ∀ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
      ∃ g ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = u τ := by
  classical
  let Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.image (tauE D)
  have hm : ∀ σ, σ ∈ Ψ ↔ ∃ τ, tauE D τ = σ := fun σ => by simp [Ψ]
  choose s hs using fun σ : Ψ => (hm σ.1).1 σ.2
  have hst : ∀ τ, s ⟨tauE D τ, (hm _).2 ⟨τ, rfl⟩⟩ = τ := fun τ => tauE_injective D (hs _)
  obtain ⟨h1, -, -, h4⟩ := (GlobalTheory.UnitaryGlue.adelic_glue D V).2 Ψ (fun σ => θ (s σ))
    (fun σ => by rw [hm, hm]; exact tauE_cm D σ) (fun σ => by rw [← hs σ]; exact hθ (s σ))
  refine ⟨fun g hg => h1 g fun σ => hg (s σ), fun u hu => ?_⟩
  obtain ⟨h, hh, hhu⟩ := h4 (fun σ => u (s σ)) (fun σ => by rw [← hs σ]; exact hu (s σ))
  refine ⟨h, hh, fun τ => ?_⟩
  have := hhu ⟨tauE D τ, (hm _).2 ⟨τ, rfl⟩⟩
  simp only [hst] at this
  exact this

theorem realPoints : ∀ D : D7, (∀ θ θ' : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → IsInfFam θ' → θ = θ') ∧ ∀ θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfFam θ → ∀ V : HSp D, RealPoints θ V := by
  intro D
  refine ⟨fun θ θ' h h' => funext fun ρ => infEmb_unique _ _ _ (h ρ) (h' ρ), fun θ hθ V => ?_⟩
  obtain ⟨g1, g2⟩ := glue θ hθ V
  obtain ⟨s1, s2, s3, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  have hmul : ∀ g g' τ, infMat D.sp.cm.sig V.gram (θ τ) (g * g') =
      infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g' := fun g g' τ => by
    rw [infMat_eq V, infMat_eq V, infMat_eq V, map_mul, Units.val_mul, Matrix.map_mul]
  have hfin : ∀ k ∈ GfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = 1 := fun k hk τ => by
    have hk' : infHom V k = 1 := hk
    rw [infMat_eq V, hk', Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨fun τ => ⟨gramAt_herm V τ, gramAt_unit V τ⟩, g2, fun g hg g' hg' h => ?_, hmul, hfin, s2,
    fun g => ?_, fun g a ha => ?_⟩
  · refine mul_inv_eq_one.1 (s3 _ (mul_mem hg (inv_mem hg')) (g1 _ fun τ => ?_))
    rw [hmul, h, ← hmul, mul_inv_cancel, hfin 1 (one_mem _)]
  · obtain ⟨a, ha, k, hk, e⟩ := s1 g
    exact ⟨k, hk, a, ha, e.trans (s2 a ha k hk)⟩
  · have ha' : finHom V a = 1 := ha
    rw [finMat_eq V, finMat_eq V, map_mul, ha', mul_one]

end GlobalTheory.SmoothForms.RealPts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ArcWitnessTangentPoint
section
noncomputable section

namespace GlobalTheory.ConstEig

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ

section Transport

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLie

variable {R R₀ : Type} [CommRing R] [IsDomain R] [CommRing R₀] [IsDomain R₀] {D : DegPre R} {D₀ : DegPre R₀}
  {φ : D.P.A.left ⟶ D₀.P.A.left} {w : LB.Iso D.P.L (D₀.P.L.pull φ)} {e : D₀.X → D.X}

theorem tr_comp {T : Over (Sp R)} {T₀ T₁ : Over (Sp R₀)} {h : T.left ⟶ T₁.left} {g : GtPt D T} {g₀ : GtPt D₀ T₀}
    {g₁ : GtPt D₀ T₁} (H : Tr w e h g g₁) (ρ : T₁ ⟶ T₀) (P : GtPt.IsPull ρ.left g₀ g₁) :
    Tr w e (h ≫ ρ.left) g g₀ := fun x => by
  have hb : ρ ≫ g₀.b = g₁.b := (Over.OverMorphism.ext P.1).symm
  refine ⟨fun k => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [(H x).1, Category.assoc, ConstTanRed.comp_gtφT D₀ ρ g₀.b g₁.b hb]
  · refine Eq.trans ?_ ((H x).2 Z r z J J' hJ hJ')
    rw [← Category.assoc]
    exact (val_pull hJ _ _ _).symm.trans (val_corr hJ (P.2 x) (r ≫ h)).symm

end Transport

section ThetaShiftProofs

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ConstLie GlobalTheory.FormalPoint
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {A : Type} [CommRing A]
  [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] {b : O →+* A} {a : ArcIn Dw l β A b}
  {χ : Sp (PowerSeries A) ⟶ Y.X} (W : Wit Y a χ)

abbrev scaleE {R : Type} [CommRing R] (r : R) : epsR R ⟶ epsR R :=
  Over.homMk (spMap (epsScaleR r)) (LieCombBaseChange.epsScale_over _)

theorem scaleE_cstE {A : Type} [CommRing A] (r : A) :
    (scaleE (PowerSeries.C (R := A) r)).left ≫ cstE A = cstE A ≫ (scaleE r).left := by
  refine (spMap_comp' _ _).trans (Eq.trans (congrArg spMap ?_) (spMap_comp' _ _).symm)
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR]

variable (hG : GlobalFnsSt)
include hG

theorem lieImg_scale {ν ν' : GtPt a.D₀ (epsR A)} {v : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v) (r : A)
    (P : GtPt.IsPull (scaleE r).left ν ν') : LieImg W ν' (scaleE (PowerSeries.C (R := A) r) ≫ v) := by
  obtain ⟨g, hg, hp⟩ := exists_tr W hG hv
  obtain ⟨g', hg'⟩ := exists_tr_down hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (cstE A)
    (LieCombBaseChange.dualMap_over _) ν'
  have Q := Tr.cancel W.spec.1 W.e.surjective hg (tr_comp hg' (scaleE r) P) (scaleE (PowerSeries.C (R := A) r))
    (scaleE_cstE r)
  exact lieImg_of_tr W hg' (hp.pull _ Q)

theorem lieImg_act {ν ν' : GtPt a.D₀ (epsR A)} {v : epsR (PowerSeries A) ⟶ W.t.G} (hv : LieImg W ν v) (x : 𝓞 E)
    (hν' : letI := H.starRing; IsSmulPt a.oa x ν ν') : LieImg W ν' (v ≫ W.t.act.act x) := by
  letI := H.starRing
  obtain ⟨g, hg, hp⟩ := exists_tr W hG hv
  obtain ⟨g', hg'⟩ := exists_tr_down hG W.spec.1 W.spec.2.1 W.e.toAddEquiv W.spec.2.2.2.2.1 (cstE A)
    (LieCombBaseChange.dualMap_over _) ν'
  have s := Tr.smul hG W.spec.1 W.spec.2.1 W.e.surjective W.P.oD a.oa (fun x y => W.e.map_smul x y)
    W.spec.2.2.2.1 x (LieCombBaseChange.dualMap_over _) hg hg' hν'
  exact lieImg_of_tr W hg' (hp.smul hG W.P.lin x s)

end ThetaShiftProofs

theorem isEigGt_iff : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (t : 𝓞 E →+* A) (ν : Out.GtPt a.D₀ (epsR A)) (v : epsR (PowerSeries A) ⟶ W.t.G), LieImg W ν v → ((letI := H.starRing; GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.IsEigGt a.oa t ν) ↔ ∀ x : 𝓞 E, (v ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (t x))) ≫ v.left) := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W t ν v hv
  letI := H.starRing
  refine forall_congr' fun x => ⟨fun ⟨ν', h₁, h₂⟩ => ?_, fun h => ?_⟩
  · have e := (ConstLie.main hG E H Dw l Xo c O β Y A b a χ W ν').1.unique (lieImg_act W hG hv x h₂)
      (lieImg_scale W hG hv (t x) h₁)
    exact congrArg (fun q => q.left) e
  · obtain ⟨ν', h₂⟩ := TorusModel.exists_isSmulPt hG a.oa x ν
    obtain ⟨ν'', h₁⟩ := ConstLie.exists_isPull (scaleE (t x)) ν
    obtain rfl : ν' = ν'' := ConstLie.eq_of_red W hG (lieImg_act W hG hv x h₂) (lieImg_scale W hG hv (t x) h₁)
      (congrArg (ConstLie.redE A ≫ ·) h)
    exact ⟨ν', h₁, h₂⟩

end GlobalTheory.ConstEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.RamOverZRealPos
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory

theorem ramOverZ_real_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    (0 : ℝ) < (ramOverZ la : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Formalism.MainNotions.ModuliIntegralCharts.H1.H1algLink.ramOverZ_ne_zero la)

theorem numerical_h_one_of_weighted_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), ∀ (large₂ : SizeData₂ D) (wL : WeightFamilies.Wt D j) (nus : HeightOneSpectrum (𝓞 T.Q.c.F) → ℝ), Formalism.MainNotions.Gaps.EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ (recPJ h j hj) wL nus → NumericalH1Condition T.Q.c (fun la => nus la / (ramOverZ la : ℝ)) (WeightAlgebra.PN D large₂) wL.size ∧ nuOf T.Q.c (fun la => nus la / (ramOverZ la : ℝ)) = nus := by
  intro D T h j hj large₂ wL nus hH
  obtain ⟨h0, h1, h2⟩ := hH
  have he : ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F),
      (ramOverZ la : ℝ) * (nus la / (ramOverZ la : ℝ)) = nus la := fun la =>
    mul_div_cancel₀ _ (ramOverZ_real_pos la).ne'
  refine ⟨⟨fun la => div_nonneg (h0 la) (Nat.cast_nonneg _), h1.subset ?_, ?_⟩, funext he⟩
  · intro la hla h'
    exact hla (by simp only [show nus la = 0 from h', zero_div])
  · refine le_of_eq_of_le ?_ h2
    have hs : (Function.support fun la : HeightOneSpectrum (𝓞 T.Q.c.F) =>
        nus la * ReciprocityTheory.ChartRestriction.G.T0.logNorm la).Finite :=
      h1.subset fun la hla h' => hla (by simp only [show nus la = 0 from h', zero_mul])
    simp only [he]
    rw [div_eq_mul_inv, finsum_mul' _ _ hs]
    refine finsum_congr fun la => ?_
    rw [abs_of_nonneg (h0 la), mul_assoc, ← div_eq_mul_inv]
    rfl

end GlobalTheory
end

