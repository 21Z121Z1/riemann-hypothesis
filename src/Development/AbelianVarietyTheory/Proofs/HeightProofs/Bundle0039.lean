import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ArcWitnessThetaPullback
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0006
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0004
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0003
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PmapsOfGenRelR
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0006
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0031

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ArcWitnessThetaPullbackStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ArcQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_witness_theta_pullback : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (th : a.D₀.P.L.Sec) (S : Type) [CommRing S] (ι : PowerSeries A →+* S) (x : Sp S ⟶ Xo.X) (z : Sp S ⟶ Xo.XF c) (t' : SAB H (Sp S)) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' W.t (spMap ι)) (φ : t'.G.left ⟶ Y.oF.t.G.left) (s : LB.Sec (PPx x)), z ≫ Y.j = spMap ι ≫ χ → z ≫ pullback.fst _ _ = x → φ ≫ Y.oF.t.G.hom = t'.G.hom ≫ z → φ ≫ Y.m0.toSABMap.φ = m1.φ → φ ≫ Y.m.φ = m2.φ ≫ W.m.φ → ((∃ (θ : LB.Sec W.t.PP.L) (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (W.t.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (W.t.PP.L.pull m2.φ)), ThetaOf W th θ ∧ RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ' s1 ∧ IsoMaps w2 σ' θ2 ∧ PullSec m2.φ θ θ2 ∧ ∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ → g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom → ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)), s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ↔ GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints.ThetaAlong W ι z th s) := by
  first | exact @GlobalTheory.ArcQ.thetaClause_iff_thetaAlong | exact GlobalTheory.ArcQ.thetaClause_iff_thetaAlong | (intros; apply GlobalTheory.ArcQ.thetaClause_iff_thetaAlong <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.DenomBound
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct

namespace GlobalTheory.SmoothForms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def BddDen (V : HSp D) (d : ℕ) (g : GA D V) : Prop :=
  ∀ i j, d • finMat D.sp.cm.sig V.gram g i j ∈ intAE D ∧ d • finMat D.sp.cm.sig V.gram g⁻¹ i j ∈ intAE D

def DenomBound (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  ∃ (C : ℝ) (M : ℕ), ∀ g : GA D V, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ V g : ℝ) ^ M ∧
    ∀ i : Fin V.rank, (Pi.single i (d : D.host.E) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.latG V g

def RealPoints (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) : Prop :=
  (∀ τ, (gramAt D V τ)ᴴ = gramAt D V τ ∧ IsUnit (gramAt D V τ).det) ∧
  (∀ u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, u τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
    ∃ g ∈ GinfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = u τ) ∧
  (∀ g ∈ GinfC V, ∀ g' ∈ GinfC V,
    (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = infMat D.sp.cm.sig V.gram (θ τ) g') → g = g') ∧
  (∀ g g' τ, infMat D.sp.cm.sig V.gram (θ τ) (g * g') =
    infMat D.sp.cm.sig V.gram (θ τ) g * infMat D.sp.cm.sig V.gram (θ τ) g') ∧
  (∀ k ∈ GfC V, ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) k = 1) ∧
  (∀ a ∈ GinfC V, ∀ k ∈ GfC V, a * k = k * a) ∧
  (∀ g : GA D V, ∃ k ∈ GfC V, ∃ a ∈ GinfC V, g = k * a) ∧
  ∀ (g : GA D V), ∀ a ∈ GinfC V, finMat D.sp.cm.sig V.gram (g * a) = finMat D.sp.cm.sig V.gram g

end GlobalTheory.SmoothForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTanAtOfGenericFibre
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IntFramesCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.EigenLatticeFrames GlobalTheory.Reg

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Linear

variable {S : Type} [Field S] {x : Sp S ⟶ Xo.X} {m : ℕ} {u v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}

theorem comb_inv (hu : ∀ i, IsTanAt x (u i)) (hv : ∀ i, IsTanAt x (v i)) (M N : Matrix (Fin m) (Fin m) S)
    (hNM : N * M = 1) (h : ∀ i, IsCombAt x v (M i) (u i)) (i : Fin m) : IsCombAt x u (N i) (v i) := by
  have h1 := (ReframeEx.comb_iff hu (N i) _).2 rfl
  have h2 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv u M.transpose (N i) _ h h1
  have e : M.transpose.mulVec (N i) = Pi.single i 1 := by
    funext j
    have := congrFun (congrFun hNM i) j
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]
    rw [Finset.sum_congr rfl fun k _ => _root_.mul_comm (M k j) (N i k), this]
    simp only [eq_comm]
  rw [e] at h2
  rw [← ReframeEx.comb_unique hv h2 (ReframeEx.comb_single hv i)]
  exact h1

theorem tri_inv (hu : ∀ i, IsTanAt x (u i)) (hv : ∀ i, IsTanAt x (v i))
    (h : ∀ i, ∃ cf : Fin m → S, cf i ≠ 0 ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x v cf (u i)) :
    ∃ N : Matrix (Fin m) (Fin m) S, IsUnit N.det ∧
      ∀ i, N i i ≠ 0 ∧ (∀ j, i < j → N i j = 0) ∧ IsCombAt x u (N i) (v i) := by
  choose M hd hz hc using h
  let M' : Matrix (Fin m) (Fin m) S := Matrix.of M
  have hdet : IsUnit M'.det := by
    rw [Matrix.det_of_lowerTriangular M' (fun i j hij => hz i j hij), isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hd i
  have hNM : M'⁻¹ * M' = 1 := Matrix.nonsing_inv_mul _ hdet
  have hz' := BorelGroupoid.lower_of_mul_eq_one M' M'⁻¹ hz hNM
  refine ⟨M'⁻¹, Matrix.isUnit_det_of_right_inverse hNM, fun i => ⟨fun h0 => ?_, hz' i, comb_inv hu hv M' _ hNM hc i⟩⟩
  have h2 := BorelGroupoid.lower_mul_diag M'⁻¹ M' hz' hz i
  rw [hNM, Matrix.one_apply_eq, h0, zero_mul] at h2
  exact one_ne_zero h2

end Linear

section Basis

variable {S : Type} [Field S] [Algebra c.F S] {x : Sp S ⟶ Xo.X} {τ : E →+* ℂ}
  {u v : Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}

theorem exists_eigenBasisAt (hx0 : x ≫ Xo.s = sOf c S) (τ : E →+* ℂ) : ∃ u, IsEigenBasisAt Xo c x τ u := by
  obtain ⟨n, xc, hx⟩ := ReciprocityTheory.ChartRestriction.G.Chart.univChartLoc ((Over.pullback x).obj Xo.univ.t.G)
  let B : Module.Basis (Fin (Dw.mult τ)) S (gfpEig (c := c) hx τ) :=
    Module.finBasisOfFinrankEq S _ (gfp_finrank hx0 hx τ)
  have hd : LinearIndependent S ((gfpEig (c := c) hx τ).subtype ∘ B) :=
    B.linearIndependent.map' (gfpEig (c := c) hx τ).subtype (Submodule.ker_subtype _)
  have hW : ∀ i, ((gfpEig (c := c) hx τ).subtype ∘ B) i ∈ gfpEig (c := c) hx τ := fun i => (B i).2
  exact ⟨fun i => gfpVec x xc (((gfpEig (c := c) hx τ).subtype ∘ B) i), fun i => gfp_tan hx _,
    fun i => (gfp_eig_iff hx τ _).2 (hW i), fun w hw he => gfp_basis hx0 hx τ _ hd hW w hw he⟩

end Basis

section Generic

end Generic

variable (Xo c)

end GlobalTheory.IntFramesCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTangentOfIsLieImage
section
noncomputable section

namespace GlobalTheory.ArcLieCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LieLiftsTangentReduction
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

section General

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem prod_Oφ_zero {T : Over (Sp R)} (b : T ⟶ D.P.A) {Z : Scheme.{0}} (π : Z ⟶ T.left) (σ : Z ⟶ Sp R)
    (hb : π ≫ b.left = σ ≫ eSec D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (Z ⟶ D.P.A.left) → U) :
    ∏ k, h (π ≫ D.Oφ b χ k) ^ Oinvε k = 1 := by
  have hσ : σ = π ≫ T.hom := by
    have e : eSec D.P.A ≫ D.P.A.hom = 𝟙 (Sp R) := Over.w η[D.P.A]
    rw [← Over.w b, ← Category.assoc, hb, Category.assoc]
    exact ((congrArg (σ ≫ ·) e).trans (Category.comp_id _)).symm
  let FinalForm : Over (Sp R) := Over.mk (π ≫ T.hom)
  let π' : FinalForm ⟶ T := Over.homMk π rfl
  have h1 : π' ≫ b = 1 := Over.OverMorphism.ext (hb.trans (by
    rw [hσ]
    show _ = (toUnit FinalForm ≫ η[D.P.A]).left
    simp [eSec, FinalForm]))
  have e : ∀ k, π ≫ D.Oφ b χ k = D.Oφ (1 : FinalForm ⟶ D.P.A) χ k := fun k =>
    (WeightPf.Oφ_comp π' b χ k).trans (by rw [h1])
  simp only [e]
  rw [Fin.prod_univ_four]
  show h ((1 : FinalForm ⟶ D.P.A) * (toUnit FinalForm ≫ D.c χ)).left ^ (-1 : ℤ) * h (toUnit FinalForm ≫ D.c χ).left ^ (1 : ℤ) *
    h (1 : FinalForm ⟶ D.P.A).left ^ (1 : ℤ) * h (1 : FinalForm ⟶ D.P.A).left ^ (-1 : ℤ) = 1
  simp

theorem exists_isZero (T : Over (Sp R)) : ∃ g : GtPt D T, g.IsZero := by
  have hF : ∀ χ, FormEq (PEmpty.elim : PEmpty → (T.left ⟶ D.P.A.left)) PEmpty.elim
      (DegPre.gtφT D T 1 χ) DegPre.gtε := fun χ U _ h => by
    have := prod_Oφ_zero (D := D) (1 : T ⟶ D.P.A) (𝟙 _) T.hom (by
      show 𝟙 _ ≫ (toUnit T ≫ η[D.P.A]).left = _
      simp [eSec]) χ h
    simp only [Category.id_comp] at this
    rw [TorusCoord.gtφT_eq]
    exact (Fintype.prod_empty _).trans this.symm
  choose s hs vs using fun χ => exists_gen D.P.isLB (hF χ) (LB.oneGen D.P.L)
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)).symm)
  have v1 : ∀ χ y J, Good D.P.L y J → val (s χ) (𝟙 _) y J = 1 := fun χ y J hJ =>
    (vs χ _ _ y J hJ).trans (val_one _)
  refine ⟨⟨1, s, hs, corr_of_val D.P.isLB fun y J hJ => vs 0 _ _ y J hJ,
    fun χ χ' => corr_of_val D.P.isLB fun y J hJ => ?_⟩, rfl,
    fun χ => corr_of_val D.P.isLB fun y J hJ => vs χ _ _ y J hJ⟩
  have c := val_cub D.cub (𝟙 T) hJ (DegPre.cT D T χ) (DegPre.cT D T χ') 1
  rw [MonObj.comp_one, (isCub_cubV D.cub hJ).face₃] at c
  exact ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v1 _ y J hJ) c)).trans
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (v1 _ y J hJ) (v1 _ y J hJ))).symm

theorem exists_zero_pull_iff (ν : GtPt D (epsR R)) :
    (∃ g₀ : GtPt D (Over.mk (𝟙 (Sp R))), g₀.IsZero ∧ GtPt.IsPull (epsRed R) ν g₀) ↔ IsGtTangent ν := by
  have hz : (DegPre.zeroT D (Over.mk (𝟙 (Sp R)))).left = eSec D.P.A := by
    simp [eSec]
  constructor
  · rintro ⟨g₀, h₀, hp⟩
    refine ⟨hp.1.symm.trans (by rw [h₀.1]; exact hz), fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    exact (val_corr hJ (hp.2 χ) _).symm.trans (val_corr hJ (h₀.2 χ) _)
  · intro h
    obtain ⟨g₀, h₀⟩ := exists_isZero (D := D) (Over.mk (𝟙 (Sp R)))
    refine ⟨g₀, h₀, Eq.trans (by rw [h₀.1]; exact hz) h.1.symm, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
    exact (val_corr hJ (h₀.2 χ) _).trans (val_corr hJ (h.2 χ) _).symm

omit [IsDomain R] in

theorem eSec_fstG (I : Ideal R) (e : ℕ) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] :
    eSec (thickObj R I e G) ≫ (fstG I e G).left = thick R I e ≫ eSec G :=
  (cubeMapOf (isGrpPullback_pullback G (thick R I e))).e_comm

variable {I : Ideal R} {e : ℕ} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem eSec_pG : eSec (thickObj R I e G) ≫ g.pG.left = thick R I e ≫ eSec D.P.A := by
  have := g.q_hom
  have h : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (·.left) (IsMonHom.one_hom g.q)
  rw [← eSec_fstG I e D.P.A, ← h, Category.assoc]
  rfl

theorem eq_eSec (x : Sp (R ⧸ I ^ (e + 1)) ⟶ (thickObj R I e G).left)
    (hx : x ≫ g.pG.left = thick R I e ≫ eSec D.P.A)
    (ht : ∀ χ z J, Good D.P.L z J → val (g.t χ) x z J = 1) : x = eSec (thickObj R I e G) :=
  TorusCoord.ext_of_val g x _ (hx.trans (eSec_pG g).symm) fun χ z J hJ => by
    have h := (val_corr hJ (g.t_unit χ) (𝟙 _)).trans (val_one _)
    rw [val_pull hJ, Category.id_comp] at h
    exact (ht χ z J hJ).trans h.symm

theorem val_eq_one_of_genRelR {A : Type} [CommRing A] [IsLocalRing A] {B B₀ Z : Scheme.{0}} {M : LB B} {M₀ : LB B₀}
    {φ : B ⟶ B₀} {w : LB.Iso M (M₀.pull φ)} (hw : w.IsGen) (hM : M.IsLB) (hM₀ : M₀.IsLB) {K : Type} [Fintype K]
    {ε : K → ℤ} {pt : K → (Sp A ⟶ B)} {pt₀ : K → (Sp A ⟶ B₀)} {t : LB.Gen (LB.LinComb M pt ε)}
    {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} (ht : t.IsGen) (ht₀ : t₀.IsGen) (h : GenRelR w t t₀) (r : Z ⟶ Sp A) (z : Z)
    (hz : ∀ f : (Z ⟶ B) → (Z.presheaf.stalk z)ˣ, ∏ k, f (r ≫ pt k) ^ ε k = 1)
    (h₀ : ∀ J, Good M₀ z J → val t₀ r z J = 1) {J'} (hJ' : Good M z J') : val t r z J' = 1 := by
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' hM₀ z
  have v₁ := CubTransport.val_pmaps (fun k => (h.1 k).trans (Category.id_comp _).symm)
    (ConstGrp.pmaps_of_genRelR ((isGen_iff w).1 hw) hM hM₀ ht ht₀ h) r hJ hJ'
  rw [Category.comp_id, h₀ J hJ, hz (fun q => gw w q z (J (q ≫ φ)) (J' q)), _root_.one_mul] at v₁
  exact v₁.symm

omit [IsDomain R] in

theorem epsRed_dualMapR {R' : Type} [CommRing R'] (f : R →+* R') :
    epsRed R' ≫ spMap (dualMapR f) = spMap f ≫ epsRed R := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun x => ConstTan.fst_dualMapR _ x)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C) :
    spMap (f'.comp f) = spMap f' ≫ spMap f := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

omit [IsDomain R] in
theorem epsRed_hom : epsRed R ≫ (epsR R).hom = 𝟙 _ := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h3 : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R :=
    RingHom.ext fun r => (TrivSqZeroExt.fstHom R R R).commutes r
  rw [h3]
  exact Spec.map_id _

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section ThetaShiftProofs

variable {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {K₁ : Type} [Field K₁] {b : O →+* K₁}
  {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}

theorem gtTan_iff (ν : GtPt a.D₀ (epsR K₁)) : GtTan (a := a) ν ↔ IsGtTangent ν :=
  exists_zero_pull_iff ν

theorem isTangent_of_isLieImage
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    {ν : GtPt a.D₀ (epsR K₁)} (hν : IsGtTangent ν) {v : epsR (PowerSeries K₁) ⟶ W.t.G} (hv : IsLieImage W ν v) :
    IsTangent v := by
  let I : Ideal (PowerSeries K₁) := Ideal.span {PowerSeries.X}
  have hI : I ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact PowerSeries.X_prime.not_isUnit
  have : IsAdicComplete I (PowerSeries K₁) := inferInstance
  refine hom_ext_of_isHausdorff I fun e => ?_
  have : IsLocalRing (PowerSeries K₁ ⧸ I ^ (e + 1)) := isLocalRing_quotient_pow hI e
  have := ConstTan.isLocalRing_dual (PowerSeries K₁ ⧸ I ^ (e + 1))
  let m : PowerSeries K₁ →+* PowerSeries K₁ ⧸ I ^ (e + 1) := Ideal.Quotient.mk _
  let κ := dualMapR (m.comp (PowerSeries.C (R := K₁)))
  let s := (epsR (PowerSeries K₁ ⧸ I ^ (e + 1))).hom
  let r := epsRed (PowerSeries K₁ ⧸ I ^ (e + 1))
  have hs : s ≫ thick (PowerSeries K₁) I e = spMap (dualMapR m) ≫ (epsR (PowerSeries K₁)).hom := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun q => Spec.map (CommRingCat.ofHom q)) (RingHom.ext fun r => (ConstTan.dualMapR_inl m r).symm)
  let xe : Sp (DualNumber (PowerSeries K₁ ⧸ I ^ (e + 1))) ⟶ (thickObj (PowerSeries K₁) I e W.t.G).left :=
    pullback.lift (spMap (dualMapR m) ≫ v.left) s (by rw [Category.assoc, Over.w v, hs])
  have hx : xe ≫ (fstG I e W.t.G).left = spMap (dualMapR m) ≫ v.left := pullback.lift_fst _ _ _
  have hx' : xe ≫ (thickObj (PowerSeries K₁) I e W.t.G).hom = s := pullback.lift_snd _ _ _
  have h' := hv e (dualMapR m) κ xe (ConstTan.dualMapR_inl _) (ConstTan.dualMapR_eps _)
    (ConstTan.dualMapR_inl _) (ConstTan.dualMapR_eps _) hx' hx
  have hκ : r ≫ spMap κ = (thick (PowerSeries K₁) I e ≫ spMap (PowerSeries.C (R := K₁))) ≫ epsRed K₁ :=
    (epsRed_dualMapR (m.comp (PowerSeries.C (R := K₁)))).trans (congrArg (· ≫ epsRed K₁) (spMap_comp (PowerSeries.C (R := K₁)) m))
  have hp : (r ≫ xe) ≫ (W.P.U.gt e).pG.left = thick (PowerSeries K₁) I e ≫ eSec W.P.D.toPre.P.A := by
    refine W.spec.1.1.hom_ext ?_ ?_
    · have h2 : (xe ≫ (W.P.U.gt e).pG.left) ≫ W.φ = spMap κ ≫ ν.b.left := (h' 0).1 2
      have h3 := congrArg (r ≫ ·) h2
      simp only [← Category.assoc] at h3
      refine h3.trans ((congrArg (· ≫ ν.b.left) hκ).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) hν.1).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) W.he.symm).trans (Category.assoc _ _ _).symm)))))
    · have e₁ : eSec W.P.D.toPre.P.A ≫ W.P.D.toPre.P.A.hom = 𝟙 _ := Over.w η[W.P.D.toPre.P.A]
      have e₂ : (W.P.U.gt e).pG.left ≫ W.P.D.toPre.P.A.hom =
          (thickObj (PowerSeries K₁) I e W.t.G).hom ≫ thick (PowerSeries K₁) I e := Over.w _
      have e₃ : r ≫ s = 𝟙 _ := epsRed_hom
      refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans ?_)).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₁).trans (Category.comp_id _))).symm
      rw [← Category.assoc, Category.assoc r, hx', e₃, Category.id_comp]
  have key : r ≫ xe = eSec (thickObj (PowerSeries K₁) I e W.t.G) := by
    refine eq_eSec (W.P.U.gt e) _ hp fun y z J' hJ' => ?_
    obtain ⟨x, rfl⟩ := W.e.surjective y
    refine (val_pull hJ' _ _ _).symm.trans (val_eq_one_of_genRelR W.spec.2.1 W.P.D.toPre.P.isLB a.D₀.P.isLB
      (DVR.pullGen_isGen _ _ _ _ ((W.P.U.gt e).t_gen _) xe) (DVR.pullGen_isGen _ _ _ _ (ν.isGen x) _) (h' x) r z
      (fun f => ?_) (fun J hJ => ?_) hJ')
    · refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (prod_Oφ_zero (W.P.U.gt e).pG (r ≫ xe) _ hp (W.e x) f)
      exact congrArg (fun q => f q ^ Oinvε k) (Category.assoc _ _ _).symm
    · exact (val_pull hJ _ _ _).trans ((congrArg (fun q => val (ν.s x) q z J) hκ).trans
        ((val_pull hJ _ _ _).symm.trans ((val_corr hJ (hν.2 x) _).trans (val_one _))))
  have h₁ : r ≫ spMap (dualMapR m) = thick (PowerSeries K₁) I e ≫ epsRed (PowerSeries K₁) := epsRed_dualMapR m
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ v.left) h₁.symm).trans ((Category.assoc _ _ _).trans
    ((congrArg (r ≫ ·) hx.symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) key).trans (eSec_fstG I e W.t.G))))))

theorem isLieImage_iff
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ)
    {ν : GtPt a.D₀ (epsR K₁)} (hν : IsGtTangent ν) (v : epsR (PowerSeries K₁) ⟶ W.t.G) :
    IsLieImage W ν v ↔ IsTangent v ∧ IsLieImage W ν v :=
  ⟨fun h => ⟨isTangent_of_isLieImage W hν h, h⟩, fun h => h.2⟩

theorem lieLifts_iff
    (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ) :
    (∀ ν : GtPt a.D₀ (epsR K₁), GtTan (a := a) ν → ∃ v : epsR (PowerSeries K₁) ⟶ W.t.G, IsLieImage W ν v) ↔
      LieLifts W :=
  forall_congr' fun ν => ⟨fun h hν => (h ((gtTan_iff ν).2 hν)).imp fun v => (isLieImage_iff W hν v).1,
    fun h hν => (h ((gtTan_iff ν).1 hν)).imp fun _ => And.right⟩

end ThetaShiftProofs

theorem lieArcSt_iff {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    LieArcSt Y ↔ ∀ (K₁ : Type) [Field K₁] (b : O →+* K₁) (a : ArcIn Dw l β K₁ b) (χ : Sp (PowerSeries K₁) ⟶ Y.X)
      (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁)) PowerSeries.X χ), LieLifts W :=
  ⟨fun h _ _ _ a χ W => (lieLifts_iff W).1 (h a χ W), fun h _ _ _ a χ W => (lieLifts_iff W).2 (h _ _ a χ W)⟩

variable (Xo c) in

theorem main : (∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), LieArcSt Y) ↔ ArcLieLift Xo c :=
  ⟨fun h O _ β Y => (lieArcSt_iff Y).1 (h O β Y), fun h O _ β Y => (lieArcSt_iff Y).2 (h O β Y)⟩

end GlobalTheory.ArcLieCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesCongruencesModDegreeOnePrime
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize GlobalTheory.WeberCongruence
open scoped IntermediateField

namespace GlobalTheory.WeberCongruenceAnyOrder

theorem weber_congruences : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ (W : ValuationSubring ℂ) (π : 𝓞 K) (p : ℕ), p.Prime → 5 ≤ p → Ideal.absNorm (Ideal.span {π}) = p → ((π : K) : ℂ) ∈ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∈ W ∧ (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ^ p ∈ W.nonunits ∧ ∀ (m : ℕ), ¬ p ∣ m → (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ∈ W ∧ (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP (((π : K) : ℂ) * t)) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) ^ p ∈ W.nonunits) ∧ ((L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) ∉ W.nonunits → (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) - 1 ∉ W.nonunits → ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice → t' ∉ L.lattice → (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t) - (L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t') ∈ W.nonunits → t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice) := by
  intro K _ _ hK L hL W π p hp h5 hN hπ
  have hcm : ∀ a : 𝓞 K, ∀ z ∈ L.lattice, ((a : K) : ℂ) * z ∈ L.lattice := fun a z hz ↦ by
    obtain ⟨b, rfl⟩ := (hL z).mp hz
    exact (hL _).mpr ⟨a * b, by simp⟩
  have hj := mem_of_isIntegral W
    (CMCurves.isIntegral_latticeJ hK (K.val : K →+* ℂ) L hcm)
  have hn : ‖((π : K) : ℂ)‖ ^ 2 = p := by
    rw [← hN]; exact norm_sq_eq_absNorm hK (K.val : K →+* ℂ) π
  have hπi : IsIntegral ℤ ((π : K) : ℂ) :=
    (RingOfIntegers.isIntegral_coe π).map (K.val : K →+* ℂ).toIntAlgHom
  have hpW : (p : ℂ) ∈ W.nonunits := by
    have := mul_mem_nonunits W hπ
      (mem_of_isIntegral W (hπi.map (starRingEnd ℂ).toIntAlgHom))
    convert this using 1
    change _ = _ * (starRingEnd ℂ) _
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    simp
  have i2 : (2 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 2) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have i3 : (3 : ℂ)⁻¹ ∈ W := by
    simpa using inv_natCast_mem W (m := 3) hp hpW fun h ↦ by
      have := Nat.le_of_dvd (by norm_num) h; omega
  have hΔ := g₂_cube_sub_g₃_sq_ne_zero L
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) (n := 12) (by norm_num)
  have hc0 : c ≠ 0 := by rintro rfl; exact hΔ (by simpa using hc.symm)
  have H := isHomothetic_scalePeriods L c hc0
  generalize scalePeriods L c hc0 = L' at H
  have hΔ' : L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2 = 1 := by
    rw [H.g₂_eq, H.g₃_eq]; field_simp; linear_combination -hc
  have eJ : L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = L'.g₂ ^ 3 := by
    rw [H.g₂_eq, ← hc]; field_simp
  have eW : ∀ t, L.g₂ * L.g₃ / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) * L.weierstrassP t =
      L'.g₂ * L'.g₃ * L'.weierstrassP (c * t) := fun t ↦ by
    rw [H.g₂_eq, H.g₃_eq, H.weierstrassP_mul, ← hc]; field_simp
  have hJ : L'.g₂ ^ 3 ∈ W := by
    have := mul_mem (mul_mem (pow_mem i2 6) (pow_mem i3 3)) hj
    convert this using 1
    rw [← eJ, CMCurves.latticeJ]; ring
  have hg := mem_of_pow_mem W three_ne_zero hJ
  have hh : L'.g₃ ∈ W := by
    refine mem_of_pow_mem W two_ne_zero ?_
    have := mul_mem (pow_mem i3 3) (sub_mem hJ (one_mem W))
    convert this using 1
    linear_combination (-1 / 27 : ℂ) * hΔ'
  have hD : (L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2)⁻¹ ∈ W := by rw [hΔ', inv_one]; exact one_mem W
  obtain ⟨a, ha, -, -, a2, a3, a4⟩ := GlobalTheory.T.weierstrassP_mul_congr_frobenius_of_primeNorm L' W ((π : K) : ℂ) p i2 i3 hg hh hD hp hpW hπ
    (fun l hl ↦ by
      obtain ⟨z, rfl⟩ : ∃ z, l = c * z := ⟨c⁻¹ * l, by field_simp⟩
      rw [mul_left_comm]
      exact (H _).mpr (hcm π z ((H z).mp hl))) hn
  obtain ⟨c1, c2⟩ := congruences W hp hpW hg hh ha hΔ' a2 a3
  simp only [eW]
  rw [eJ]
  refine ⟨hJ, c1, fun m hpm ↦ ?_⟩
  have hm : 0 < m := Nat.pos_of_ne_zero fun h ↦ hpm (h ▸ dvd_zero p)
  have im := inv_natCast_mem W hp hpW hpm
  obtain ⟨t1, t2⟩ := GlobalTheory.T.weierstrassP_torsion_mem_and_distinct_mod_nonunits L' W m i2 i3 hg hh hD hm im
  have s1 : ∀ t, (m : ℂ) * t ∈ L.lattice → (m : ℂ) * (c * t) ∈ L'.lattice := fun t ht ↦ by
    rw [mul_left_comm]; exact (H _).mpr ht
  refine ⟨fun t ht ht' ↦ ?_, fun n1 n2 t t' ht ht0 ht' ht0' h ↦ ?_⟩
  · have hx := t1 (c * t) (s1 t ht) ((H t).not.mpr ht')
    refine ⟨mul_mem (mul_mem hg hh) hx, c2 _ _ hx ?_⟩
    rw [mul_left_comm]
    exact a4 m (c * t) hm im (s1 t ht) ((H t).not.mpr ht')
  · have n3 : L'.g₂ ∉ W.nonunits := fun h ↦ n1 (by
      simpa [pow_succ'] using mul_mem_nonunits W h (pow_mem hg 2))
    have n4 : L'.g₃ ∉ W.nonunits := fun h ↦ n2 (by
      have := mul_mem_nonunits W h (mul_mem (ofNat_mem W 27) hh)
      convert this using 1
      linear_combination hΔ')
    rw [← mul_sub, mul_assoc] at h
    have := t2 (c * t) (c * t') (s1 t ht) ((H t).not.mpr ht0) (s1 t' ht') ((H t').not.mpr ht0')
      (mem_nonunits_of_mul W n4 (mem_nonunits_of_mul W n3 h))
    rwa [← mul_sub, ← mul_add, H, H] at this

end GlobalTheory.WeberCongruenceAnyOrder
end

