import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantEigenbasisIndependentOfWitness
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExponentialFamilyDerivSumsAtPeriod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecThroughUp
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFactorOfIsAlgClosed

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantArcEigenbasisFlatBaseChange
section
noncomputable section

namespace GlobalTheory.BasisUniv

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp JetR IsTan
open scoped CategoryTheory.Obj

section Coord

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

theorem isUnivChart_iso {G' : Over (Spec (CommRingCat.of S))} [GrpObj G'] (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    IsUnivChart G' n (fun m => x m ≫ e.inv) := by
  have one : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G') ≫ e.hom = 1 := fun T =>
    map_one (IsMonHom.monoidHom e.hom T)
  have one' : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G) ≫ e.inv = 1 := fun T => by
    rw [← one, Category.assoc, e.hom_inv_id, Category.comp_id]
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hm y hy => ?_⟩
  · rw [← Category.assoc, hx.1]
  · rw [← Category.assoc, hx.2.1, one']
  · have := hx.2.2 A aug m hm (y ≫ e.hom) (by rw [← Category.assoc, hy, one])
    simpa only [← Category.assoc, Iso.eq_comp_inv] using this

theorem exists_chart_of_pullback {R : Type} [CommRing R] [IsLocalRing R] {G₀ : Over (Spec (CommRingCat.of R))} [GrpObj G₀]
    [Smooth G₀.hom] (f : R →+* S) {φ : G.left ⟶ G₀.left} (h : IsGrpPullback G G₀ (Geo.Tor.spMap f) φ) :
    ∃ (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G), IsUnivChart G n x := by
  let _ := f.toAlgebra
  obtain ⟨n, x, hx⟩ := univChartLoc G₀
  obtain ⟨x', hx', -⟩ := tanBC_alg (R' := S) G₀ n x hx
  obtain ⟨e, he, -⟩ := grpPullback_iso h (isGrpPullback_pullback G₀ (fB R S))
  exact ⟨n, _, isUnivChart_iso e hx'⟩

variable {n : ℕ} {y : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G} (hy : IsUnivChart G n y)
  {g : ℕ} {v : Fin g → (epsR S ⟶ G)}
include hy

theorem isTangent_of_comb (hv : ∀ i, IsTangent (v i)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) :
    IsTangent w := by
  obtain ⟨k, -⟩ := prodPts_tan hy z v fun i => (isTan_iff _).2 (hv i)
  rw [(isLieComb_iff _ _ _).1 hw]
  exact (isTan_iff _).1 k

theorem coord_inj (hv : IsLieBasis v) (tv : ∀ i, IsTan (v i)) {c c' : Fin g → S}
    (h : ∑ i, c i • tcoord hy (v i) (tv i) = ∑ i, c' i • tcoord hy (v i) (tv i)) : c = c' := by
  obtain ⟨k, e⟩ := prodPts_tan hy c v tv
  exact (hv.2 _ ((isTan_iff _).1 k)).unique ((comb_iff_coord hy c tv k).2 e)
    ((comb_iff_coord hy c' tv k).2 (e.trans h))

theorem comb_iff (hv : IsLieBasis v) {m : ℕ} {u : Fin m → (epsR S ⟶ G)} {U : Fin m → Fin g → S}
    (hU : ∀ k, IsLieComb (U k) v (u k)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) (cf : Fin m → S) :
    IsLieComb cf u w ↔ z = ∑ k, cf k • U k := by
  have tv := fun i => (isTan_iff _).2 (hv.1 i)
  have tu := fun k => (isTan_iff _).2 (isTangent_of_comb hy hv.1 (hU k))
  have tw := (isTan_iff _).2 (isTangent_of_comb hy hv.1 hw)
  have e : ∑ i, cf i • tcoord hy (u i) (tu i) = ∑ j, (∑ k, cf k • U k) j • tcoord hy (v j) (tv j) := by
    simp only [(comb_iff_coord hy _ tv (tu _)).1 (hU _), Finset.smul_sum, Finset.sum_smul, smul_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_comm
  rw [comb_iff_coord hy cf tu tw, e, (comb_iff_coord hy z tv tw).1 hw]
  exact ⟨fun q => coord_inj hy hv tv q, fun q => by rw [q]⟩

theorem tcoord_comp (f : G ⟶ G) [IsMonHom f] {w : epsR S ⟶ G} (tw : IsTan w) :
    tcoord hy (w ≫ f) (isTan_comp tw f) = tmap hy f (tcoord hy w tw) :=
  tcoord_congr hy (congrArg (· ≫ f) (tcoord_spec hy w tw)) _ (isTan_comp (isTan_tvec hy _) f)

theorem eig_iff (hv : IsLieBasis v) (f : G ⟶ G) [IsMonHom f] {M : Matrix (Fin g) (Fin g) S}
    (hM : ∀ i, IsLieComb (M i) v (v i ≫ f)) {z : Fin g → S} {w : epsR S ⟶ G} (hw : IsLieComb z v w) (r : S) :
    (w ≫ f).left = Geo.Tor.spMap (epsScaleR r) ≫ w.left ↔ z ᵥ* M = r • z := by
  have tv := fun i => (isTan_iff _).2 (hv.1 i)
  have tw := (isTan_iff _).2 (isTangent_of_comb hy hv.1 hw)
  have ew := (comb_iff_coord hy z tv tw).1 hw
  have e1 : tcoord hy (w ≫ f) (isTan_comp tw f) = ∑ j, (z ᵥ* M) j • tcoord hy (v j) (tv j) := by
    rw [tcoord_comp hy f tw, ew, map_sum]
    simp only [map_smul, ← tcoord_comp hy f, (comb_iff_coord hy _ tv (isTan_comp (tv _) f)).1 (hM _),
      Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    exact Finset.sum_comm
  have e2 : tcoord hy (spMap (scaleD r) ≫ w) (isTan_scale r tw) = ∑ j, (r • z) j • tcoord hy (v j) (tv j) := by
    rw [tcoord_scale hy r tw, ew, Finset.smul_sum]
    simp only [smul_smul, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro q
    have q' : w ≫ f = spMap (scaleD r) ≫ w := Over.OverMorphism.ext q
    exact coord_inj hy hv tv (e1.symm.trans ((tcoord_congr hy q' _ _).trans e2))
  · intro q
    have q' : w ≫ f = spMap (scaleD r) ≫ w :=
      tan_ext hy (isTan_comp tw f) (isTan_scale r tw) (by rw [e1, e2, q])
    exact congrArg (fun t => t.left) q'

omit hy in

theorem exists_lift {R : Type} [CommRing R] {G₀ : Over (Spec (CommRingCat.of R))} [GrpObj G₀]
    (f : R →+* S) {φ : G.left ⟶ G₀.left} (h : IsGrpPullback G G₀ (Geo.Tor.spMap f) φ) (w : epsR R ⟶ G₀) :
    ∃ w' : epsR S ⟶ G, w'.left ≫ φ = Geo.Tor.spMap (dualMapR f) ≫ w.left := by
  have c : (Geo.Tor.spMap (dualMapR f) ≫ w.left) ≫ G₀.hom = (epsR S).hom ≫ Geo.Tor.spMap f := by
    rw [Category.assoc, Over.w w]
    exact (Geo.Tor.spMap_comp _ _).symm.trans ((congrArg Geo.Tor.spMap (RingHom.ext fun r => by
      ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl])).trans (Geo.Tor.spMap_comp _ _))
  exact ⟨Over.homMk (h.1.lift _ _ c) (h.1.lift_snd _ _ c), h.1.lift_fst _ _ c⟩

end Coord

theorem eig_powerSeries {A : Type} [CommRing A] [IsNoetherianRing A] {I : Type} {g m : ℕ}
    (M : I → Matrix (Fin g) (Fin g) A) (ρ : I → A) (U : Fin m → Fin g → A)
    (hU : ∀ k i, U k ᵥ* M i = ρ i • U k)
    (h : ∀ w : Fin g → PowerSeries A, (∀ i, w ᵥ* (M i).map (PowerSeries.C (R := A)) = PowerSeries.C (R := A) (ρ i) • w) →
      ∃! cf : Fin m → PowerSeries A, w = ∑ k, cf k • fun j => PowerSeries.C (R := A) (U k j))
    {S : Type} [CommRing S] (f : A →+* S) (hf : f.Flat) (w : Fin g → S)
    (hw : ∀ i, w ᵥ* (M i).map f = f (ρ i) • w) : ∃! cf : Fin m → S, w = ∑ k, cf k • fun j => f (U k j) := by
  let _ := f.toAlgebra
  have : Module.Flat A S := hf
  refine (GlobalTheory.commonEigenvectors_flat_baseChange A I g m M ρ).1 A U hU (fun z hz => ?_) S w hw
  simp only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_id, Matrix.map_id] at hz ⊢
  obtain ⟨cf, hcf, huniq⟩ := h (fun j => PowerSeries.C (R := A) (z j)) (fun i => by
    funext j
    have := congrArg (PowerSeries.C (R := A)) (congrFun (hz i) j)
    simpa [Matrix.vecMul, dotProduct] using this)
  have key : ∀ c : Fin m → A, (z = ∑ k, c k • fun j => U k j) →
      (fun k => PowerSeries.C (R := A) (c k)) = cf := fun c hc => huniq _ (by
    funext j
    have := congrArg (PowerSeries.C (R := A)) (congrFun hc j)
    simpa [Finset.sum_apply] using this)
  refine ⟨fun k => PowerSeries.constantCoeff (R := A) (cf k), ?_, fun c hc => ?_⟩
  · funext j
    have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun hcf j)
    simpa [Finset.sum_apply] using this
  · rw [← key c hc]
    funext k
    simp

end GlobalTheory.BasisUniv

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

open Matrix GlobalTheory.BasisUniv in

theorem GlobalTheory.ArcQ.arcBasis_baseChange : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → ∀ (S : Type) [CommRing S] (ι : PowerSeries A →+* S), (ι.comp (PowerSeries.C (R := A))).Flat → ∀ (t' : SAB H (Sp S)) (m2 : SABMap t' W.t (spMap ι)), ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsR S ⟶ t'.G), (∀ τ k, ∃ v, LieImg W (e τ k) v ∧ (u τ k).left ≫ m2.φ = spMap (dualMap ι) ≫ v.left) ∧ ∀ τ, (∀ k, IsTangent (u τ k) ∧ ∀ x : 𝓞 E, (u τ k ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ (u τ k).left) ∧ ∀ w : epsR S ⟶ t'.G, IsTangent w → (∀ x : 𝓞 E, (w ≫ t'.act.act x).left = spMap (epsScaleR (ι (PowerSeries.C (R := A) (ρ τ x)))) ≫ w.left) → ∃! cf : Fin (Dw.mult τ) → S, IsLieComb cf (u τ) w := by
  intro hG E _ _ _ H Dw l Xo c O _ β Y A _ _ _ _ b a χ W ρ e hB S _ ι hflat t' m2
  obtain ⟨v₀, hv₀, hB⟩ := hB
  obtain ⟨g, e₁, v, M, hev, hv, hcomb, hM⟩ := GlobalTheory.T.exists_constantLieBasis_arcGroup hG E H Dw l Xo c O β Y A b a χ W
  have hsm : Smooth W.t.G.hom := W.t.semi.smooth
  have hmon : ∀ x, IsMonHom (W.t.act.act x) := W.t.act.hom
  have hmon' : ∀ x, IsMonHom (t'.act.act x) := t'.act.hom
  obtain ⟨n, y, hy⟩ := Chart.univChartLoc W.t.G
  obtain ⟨n', y', hy'⟩ := exists_chart_of_pullback ι m2.cart

  have hU : ∀ τ k, ∃ U : Fin g → A, IsLieComb (fun j => PowerSeries.C (R := A) (U j)) v (v₀ τ k) := fun τ k => by
    have ht : GtTanR (e τ k) :=
      ((GlobalTheory.T.exists_unique_constant_tangent_vectors_along_arc hG E H Dw l Xo c O β Y A b a χ W (e τ k)).2 _ (hv₀ τ k)).2 ((hB τ).1 k).1
    obtain ⟨U, hU, -⟩ := hcomb _ ht
    exact ⟨U, (GlobalTheory.T.lieImg_iff_isLieComb_of_gtComb hG E H Dw l Xo c O β Y A b a χ W g U e₁ (e τ k) v _ (fun i => (hev i).2) hU).1 (hv₀ τ k)⟩
  choose U hU using hU
  choose u hu using fun τ k => exists_lift ι m2.cart (v₀ τ k)
  choose v' hv' using fun j => exists_lift ι m2.cart (v j)
  have hb' : IsLieBasis v' := Chart.isLieBasis_baseChange ι m2.cart hv hv'
  have hU' : ∀ τ k, IsLieComb (fun j => (ι.comp (PowerSeries.C (R := A))) (U τ k j)) v' (u τ k) := fun τ k =>
    Chart.comb_baseChange ι m2.cart (hU τ k) hv' (hu τ k)
  have hM' : ∀ x i, IsLieComb ((M x).map (ι.comp (PowerSeries.C (R := A))) i) v' (v' i ≫ t'.act.act x) := fun x i =>
    Chart.comb_baseChange ι m2.cart (hM x i) hv' (by
      rw [Over.comp_left, Category.assoc, m2.act, ← Category.assoc, hv', Category.assoc, Over.comp_left])
  have hMR : ∀ x i, IsLieComb ((M x).map (PowerSeries.C (R := A)) i) v (v i ≫ W.t.act.act x) := hM
  have hUe : ∀ τ k x, U τ k ᵥ* M x = ρ τ x • U τ k := fun τ k x => by
    have := (eig_iff hy hv _ (hMR x) (hU τ k) _).1 (((hB τ).1 k).2 x)
    funext j
    have := congrArg (PowerSeries.constantCoeff (R := A)) (congrFun this j)
    simpa [Matrix.vecMul, dotProduct] using this
  refine ⟨u, fun τ k => ⟨v₀ τ k, hv₀ τ k, hu τ k⟩, fun τ => ⟨fun k => ⟨isTangent_of_comb hy' hb'.1 (hU' τ k), fun x => ?_⟩,
    fun w hw hwe => ?_⟩⟩
  · refine (eig_iff hy' hb' _ (hM' x) (hU' τ k) _).2 ?_
    funext j
    have := congrArg (ι.comp (PowerSeries.C (R := A))) (congrFun (hUe τ k x) j)
    simpa [Matrix.vecMul, dotProduct] using this
  · obtain ⟨z, hz, -⟩ := hb'.2 w hw
    simp only [comb_iff hy' hb' (hU' τ) hz]
    refine eig_powerSeries M (fun x => ρ τ x) (U τ) (hUe τ) (fun s hs => ?_) _ hflat z
      (fun x => (eig_iff hy' hb' _ (hM' x) hz _).1 (hwe x))
    have hc : IsLieComb s v (Chart.prodPts s v) := (Chart.isLieComb_iff _ _ _).2 rfl
    have := (hB τ).2 _ (isTangent_of_comb hy hv.1 hc) (fun x => (eig_iff hy hv _ (hMR x) hc _).2 (hs x))
    simpa only [comb_iff hy hv (hU τ) hc] using this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ConstantEigenbasisIndependentOfWitnessStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantEigenbasis_independent_of_witness : Out.GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] (b : O →+* A) (a : ArcIn Dw l β A b) (χ : Sp (PowerSeries A) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* A)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR A)), ArcBasis W ρ e → (∀ (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (b' : O' →+* A) (a' : ArcIn Dw l β' A b') (χ' : Sp (PowerSeries A) ⟶ Y'.X) (W' : Wit Y' a' χ') (p : Out.IsPullDeg (RingHom.id A) a.D₀ a'.D₀) (e' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a'.D₀ (epsR A)), (∀ (x : 𝓞 E) y, p.xe (x • y) = x • p.xe y) → (letI := H.starRing; ∀ x : 𝓞 E, (a'.oa.onB.act x).left ≫ prj p = prj p ≫ (a.oa.onB.act x).left) → (∀ τ k, LetBC p (e τ k) (e' τ k)) → ArcBasis W' ρ e') ∧ (∀ (χ' : Sp (PowerSeries A) ⟶ Y.X) (W' : Wit Y a χ'), ArcBasis W' ρ e) ∧ ∀ τ ν (v : epsR (PowerSeries A) ⟶ W.t.G), GtTanR ν → LieImg W ν v → (∀ x : 𝓞 E, (v ≫ W.t.act.act x).left = spMap (epsScaleR (PowerSeries.C (R := A) (ρ τ x))) ≫ v.left) → ∃! cf : Fin (Dw.mult τ) → A, GtComb cf (e τ) ν := by
  first | exact @GlobalTheory.ArcBasisIndep.arcBasis_indep | exact GlobalTheory.ArcBasisIndep.arcBasis_indep | (intros; apply GlobalTheory.ArcBasisIndep.arcBasis_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExponentialFamilyDerivSumsAtPeriodStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialFamily_deriv_sumsAt_period : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), AnFin Λ.A → C.Φ.Rational → ∀ (z₀ : Fin g → ℂ) (ν : Out.GtPt a.D₀ (epsR ℂ)) (v : epsR (PowerSeries ℂ) ⟶ W.t.G) (V : Y.t.G.left.Opens) (f : Γ(Y.t.G.left, V)), DiffHyp W (fun z => Λ.ex0 (K.h.symm z)) z₀ ν v → ⊤ ≤ (v.left ≫ W.m.φ) ⁻¹ᵁ V → ∃ T' : ℝ, ∀ w : ℂ, T' < w.im → ∀ xF : (Fin g → ℂ) → (Sp ℂ ⟶ Y.oF.t.G.left), (∀ z, xF z ≫ Y.m0.toSABMap.φ = (Fu.ex K.i (K.Pw w) z).left ∧ xF z ≫ Y.oF.t.G.hom ≫ pullback.snd _ _ = spMap bF) → SumsAt (TrivSqZeroExt.snd (valR (A := DualNumber (PowerSeries ℂ)) (v.left ≫ W.m.φ) V f)) w (fderiv ℂ (fun z => valAt' (xF z ≫ Y.m.φ) V f) 0 z₀) := by
  first | exact @GlobalTheory.ArcDeriv.deriv_sumsAt | exact GlobalTheory.ArcDeriv.deriv_sumsAt | (intros; apply GlobalTheory.ArcDeriv.deriv_sumsAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyChainArcWitnessUniversalFamily
section
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem algebraMap_laurent_comp_C :
    (algebraMap ℂ⟦X⟧ ℂ⸨X⸩).comp (PowerSeries.C (R := ℂ)) = algebraMap ℂ ℂ⸨X⸩ :=
  RingHom.ext fun _ => rfl

theorem X_not_mem_gen (p : Sp ℂ⸨X⸩) : PowerSeries.X ∉ (gen p).asIdeal := by
  intro h
  have h' : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ∈ p.asIdeal := h
  have hne : algebraMap ℂ⟦X⟧ ℂ⸨X⸩ PowerSeries.X ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℂ⟦X⟧ ℂ⸨X⸩)).2 PowerSeries.X_ne_zero
  exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (IsUnit.mk0 _ hne))

theorem exists_generic_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) (bF : c.F →+* ℂ) (χ : Sp ℂ⟦X⟧ ⟶ Y.X)
    (hχ : χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β))
    (hab : ∀ x : Sp ℂ⟦X⟧, PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) :
    ∃ yF : Sp ℂ⸨X⸩ ⟶ Xo.XF c, yF ≫ Y.j = gen ≫ χ ∧
      yF ≫ pullback.snd _ _ = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF) := by
  have h : (gen ≫ χ) ≫ Y.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp bF) ≫ spMap β := by
    rw [Category.assoc, hχ, ← algebraMap_laurent_comp_C, spMap_comp, spMap_comp, spMap_comp]
    simp only [Category.assoc]
  have := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ h) ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, hq⟩ := hab _ (X_not_mem_gen p)
    have hz : Y.jQ q ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    have hz' : Y.j q ∈ abLocus Y.t.G := by
      simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using hz
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, ← hq]
    exact hz'
  have hτ := IsOpenImmersion.lift_fac Y.jQ _ hr
  refine ⟨IsOpenImmersion.lift Y.jQ _ hr, ?_, ?_⟩
  · rw [Model.j, ← Category.assoc, hτ, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, hτ, pullback.lift_snd]

theorem nonempty_chain : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) , χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp β) → (∀ x : Sp ℂ⟦X⟧, PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Nonempty (Chain W Λ) := by
  intro L₁ L₂ E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ hχ hab
  obtain ⟨Ξ⟩ := GlobalTheory.ConstPoint.nonempty_constPts L₁ L₂ E H D l Xo c O β Y _ a χ W Λ
  obtain ⟨ΦW, hW⟩ := GlobalTheory.T.genericPoints_constantPoints_formalSum_values L₁ L₂ E H D l Xo c O β Y _ a χ W Λ Ξ
  obtain ⟨yF, hj, ho⟩ := exists_generic_point Y bF χ hχ hab
  obtain ⟨w₂, r₂⟩ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Y.t W.t χ W.m).1
  obtain ⟨w₁, r₁⟩ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Y.t Y.oF.t _ Y.m).1
  obtain ⟨w₀, r₀⟩ := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres L₁ L₂ E H _ _ Xo.univ.t Y.oF.t _ Y.m0.toSABMap).1
  obtain ⟨ΦY, e₂⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Y.t W.t χ W.m w₂ gen (gen ≫ χ) r₂ rfl).1 ΦW
  obtain ⟨ΦF, e₁⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Y.t Y.oF.t _ Y.m w₁ yF (gen ≫ χ) r₁ hj).2 ΦY
  obtain ⟨Φ, e₀⟩ := (GlobalTheory.ArcPts.genPts_transfer E H _ _ Λ.A Xo.univ.t Y.oF.t _ Y.m0.toSABMap w₀ yF
    (yF ≫ pullback.fst _ _) r₀ rfl).1 ΦF
  exact ⟨⟨Ξ, ΦW, hW, yF, hj, ho, ΦY, ΦF, Φ, w₂, w₁, w₀, r₂, r₁, r₀, e₂, e₁, e₀⟩⟩

end GlobalTheory.ArcPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointsFramesEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ConstRational

section Sums
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem fsum_mem (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (hth : th ∈ A.Theta j α) (v : A.V) :
    A.FSum j α th v ∈ Conv.convLaurent := by
  obtain ⟨T, hT⟩ := exists_formal_convergence O A
  obtain ⟨h, -⟩ := ((hT T le_rfl j).1 α th hth).1 v
  exact Conv.halfRing_le_convLaurent T h

theorem exists_shift_mem (k : ℕ) [NeZero k] (la : A.La) (hla : ∀ α, (k : ℤ) ∣ A.be la.y α) :
    ∃ ψ : (Σ α : A.X, A.Theta k α) → A.V → ℂ⸨X⸩,
      ∀ i z, IsFShift A k i.1 i.2 la z (ψ i z) ∧ ψ i z ∈ Conv.convLaurent := by
  obtain ⟨cz, -, h⟩ := GlobalTheory.T.theta_sum_shift_eq_single_mul_fSum O A k la hla
  choose th' hth' _ h' using h
  refine ⟨fun i z => HahnSeries.single (A.be la.y i.1 / k) (cz z) *
    A.FSum k (i.1 + la.y) (th' i.1 i.2 i.2.2) z, fun i z => ⟨((h' i.1 i.2 i.2.2 z).1 _).2 rfl, ?_⟩⟩
  exact mul_mem (Conv.halfRing_le_convLaurent 0 (Conv.single_mem_halfRing 0 _ _))
    (fsum_mem A k _ _ (hth' _ _ _) z)

end Sums

theorem points_frames_eq (L₁ : Out.Laws) (L₂ : Out.Laws2) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} [StarRing (𝓞 E)] {D : Datum H} {l : Level H} {Xo : Moduli D l} {A : AnArc (𝓞 E)}
    (σ : KA l →+* ℂ) {y : Sp ℂ⸨X⸩ ⟶ Xo.X} (Φ : GenPts A Xo.univ.t y) (laA laM : D.La → A.La) (hA : AnFin A)
    (hy : y ≫ Xo.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ))
    (levA : ∀ v, Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v))
    (levM : ∀ v ∈ idealPart D l, Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v))
    {F : Type} [Field F] [IsAlgClosed F] [CharZero F] (f g : ℂ⸨X⸩ →+* F)
    (hfg : ∀ a ∈ Conv.convLaurent, f a = g a) (v : A.V) :
    spMap f ≫ (Φ.x v).left = spMap g ≫ (Φ.x v).left ∧
      ∀ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → f (Φ.τ v j) = g (Φ.τ v j) := by
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  let φ : ∀ j, (Σ α : A.X, A.Theta j α) → A.V → F := fun j i v =>
    if h : j = 0 then 0 else haveI : NeZero j := ⟨h⟩; f (A.FSum j i.1 i.2 v)
  have hf : ∀ (j : ℕ) [NeZero j] i v, φ j i v = f (A.FSum j i.1 i.2 v) := fun j _ i v =>
    dif_neg (NeZero.ne j)
  have hg : ∀ (j : ℕ) [NeZero j] i v, φ j i v = g (A.FSum j i.1 i.2 v) := fun j _ i v =>
    (hf j i v).trans (hfg _ (fsum_mem A j _ _ i.2.2 v))
  obtain ⟨Θ₁, x₁, l₁⟩ := GlobalTheory.T.exists_arcGenericFibrePoints_baseChange E H Xo.X A Xo.univ.t y Φ F f φ hA hf
  obtain ⟨Θ₂, x₂, l₂⟩ := GlobalTheory.T.exists_arcGenericFibrePoints_baseChange E H Xo.X A Xo.univ.t y Φ F g φ hA hg
  have lev : ∀ (k : ℕ) [NeZero k] (ξ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (la : A.La),
      Φ.LevelPt k (toUnit _ ≫ ξ) la → ∃ ψ, Θ₁.Lev k (toUnit _ ≫ ξ) ψ ∧ Θ₂.Lev k (toUnit _ ≫ ξ) ψ := by
    intro k _ ξ la h
    obtain ⟨ψ, hψ⟩ := exists_shift_mem A k la h.2.1.2
    refine ⟨fun i z => f (ψ i z), l₁ k ξ la ψ h fun i z => (hψ i z).1, ?_⟩
    have e : (fun i z => f (ψ i z)) = fun i z => g (ψ i z) :=
      funext fun i => funext fun z => hfg _ (hψ i z).2
    rw [e]
    exact l₂ k ξ la ψ h fun i z => (hψ i z).1
  have hs : (spMap f ≫ y) ≫ Xo.s = (spMap g ≫ y) ≫ Xo.s := by
    have e : f.comp ((algebraMap ℂ ℂ⸨X⸩).comp σ) = g.comp ((algebraMap ℂ ℂ⸨X⸩).comp σ) :=
      RingHom.ext fun a => hfg _ (Conv.convLaurent.algebraMap_mem (σ a))
    rw [Category.assoc, Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.pointFamilies_eq_of_values_levels_universalFamily L₁ L₂ E H D l Xo F A.V _ _ φ _ _ Θ₁ Θ₂ hs
    (fun v => lev _ _ _ (levA v)) (fun v hv => lev _ _ _ (levM v hv)) v
  refine ⟨(x₁ v).1.symm.trans (e₁.trans (x₂ v).1), fun j hj => ?_⟩
  rw [← (x₁ v).2 j hj, ← (x₂ v).2 j hj]
  refine e₂ j ?_
  rw [(x₁ v).1]
  exact fun p _ => hj (Set.mem_univ (spMap f p))

theorem rational : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (A : AnArc (𝓞 E)) (σ : KA l →+* ℂ) (y : Sp ℂ⸨X⸩ ⟶ Xo.X) (Φ : GenPts A Xo.univ.t y) (laA laM : D.La → A.La), AnFin A → y ≫ Xo.s = spMap ((algebraMap ℂ ℂ⸨X⸩).comp σ) → (∀ v, Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v)) → (∀ v ∈ idealPart D l, Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v)) → Φ.Rational := by
  intro L₁ L₂ E _ _ _ H _ D l Xo A σ y Φ laA laM hA hy levA levM
  haveI : CharZero ℂ⸨X⸩ := algebraRat.charZero _
  haveI : CharZero Conv.convLaurent := algebraRat.charZero _
  have key := fun s : AlgebraicClosure ℂ⸨X⸩ ≃ₐ[Conv.convLaurent] AlgebraicClosure ℂ⸨X⸩ =>
    points_frames_eq L₁ L₂ σ Φ laA laM hA hy levA levM
      ((s : AlgebraicClosure ℂ⸨X⸩ →+* AlgebraicClosure ℂ⸨X⸩).comp (algebraMap ℂ⸨X⸩ _))
      (algebraMap ℂ⸨X⸩ (AlgebraicClosure ℂ⸨X⸩)) (fun a ha => s.commutes (⟨a, ha⟩ : Conv.convLaurent))
  refine ⟨fun v => ?_, fun v j hj => ?_⟩
  · refine (FixedPoint.existsUnique_factor (K₀ := Conv.convLaurent) (L := AlgebraicClosure ℂ⸨X⸩)
      (Φ.x v).left fun s => ?_).exists
    have h := (key s v).1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact h
  · obtain ⟨a, ha⟩ := FixedPoint.mem_range_of_algebraMap_fixed (K₀ := Conv.convLaurent)
      (L := AlgebraicClosure ℂ⸨X⸩) (Φ.τ v j) fun s => (key s v).2 j hj
    exact ha ▸ a.2

end GlobalTheory.ConstRational
end

