import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsLocalRingDual
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantLieBasisArcGroup
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0072
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DiscrMulXiIntegral
section
noncomputable section

namespace GlobalTheory.XiIntegral

section Tangent

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.L2.Pj.QAt GlobalTheory.ArcQ
open scoped CategoryTheory.Obj

def origin (R : Type) [CommRing R] : Over.mk (𝟙 (Sp R)) ⟶ epsR R :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom)
    ((spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun _ => rfl)).trans (Spec.map_id (CommRingCat.of R))))

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

theorem gtTanR_iff (ν : GtPt D (epsR R)) : GtTanR ν ↔ origin R ≫ ν.b = 1 ∧
    ∀ χ y J, Good D.P.L y J → val (ν.s χ) (origin R).left y J = 1 := by
  constructor
  · rintro ⟨g₀, h₀, h⟩
    obtain ⟨h₁, h₂⟩ := (ConstLie.isZero_iff_zeroAlong (ρ := origin R) h).1 h₀
    refine ⟨h₁, fun χ y J hJ => ?_⟩
    have := h₂ χ _ (𝟙 _) y J hJ
    rwa [Category.id_comp] at this
  · rintro ⟨h₁, h₂⟩
    obtain ⟨g₀, h⟩ := ConstLie.exists_isPullGt (origin R) ν
    obtain ⟨b, v⟩ := (TorusModel.isPull_iff _ _ _).1 h
    exact ⟨g₀, ⟨b.trans h₁, fun χ => corr_of_val D.P.isLB fun y J hJ =>
      (v χ y J hJ).trans ((h₂ χ y J hJ).trans (val_one _).symm)⟩, h⟩

theorem gtTanR_of_isZero {ν : GtPt D (epsR R)} (h : ν.IsZero) : GtTanR ν := by
  have hb : ν.b = 1 := h.1
  exact (gtTanR_iff ν).2 ⟨by rw [hb, MonObj.comp_one], fun χ y J hJ => (val_corr hJ (h.2 χ) _).trans (val_one _)⟩

theorem gtTanR_of_scale {a : R} {ν ν' : GtPt D (epsR R)} (h : GtPt.IsPull (spMap (epsScaleR a)) ν ν')
    (ht : GtTanR ν) : GtTanR ν' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  have s : (origin R).left ≫ spMap (epsScaleR a) = (origin R).left :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext fun x => by simp [epsScaleR]))
  refine (gtTanR_iff ν').2 ⟨Over.OverMorphism.ext ?_, fun χ y J hJ => ?_⟩
  · rw [← h₁, Over.comp_left, Over.comp_left, h.1, ← Category.assoc, s]
  · refine (val_corr hJ (h.2 χ) _).trans ((val_pull hJ _ _ _).trans ?_)
    rw [s]
    exact h₂ χ y J hJ

theorem gtTanR_of_isAdd {ν ν' ν'' : GtPt D (epsR R)} (h : ν.IsAdd ν' ν'') (ht : GtTanR ν) (ht' : GtTanR ν') :
    GtTanR ν'' := by
  obtain ⟨h₁, h₂⟩ := (gtTanR_iff ν).1 ht
  obtain ⟨h₁', h₂'⟩ := (gtTanR_iff ν').1 ht'
  have hb : ν''.b = ν.b * ν'.b := h.1
  refine (gtTanR_iff ν'').2 ⟨by rw [hb, MonObj.comp_mul, h₁, h₁', _root_.mul_one], fun χ y J hJ => ?_⟩
  have e := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (h.2 χ) (origin R).left).trans (val_mul hJ _ _ _))
  have c := val_cub D.cub (origin R) hJ (DegPre.cT D (epsR R) χ) ν.b ν'.b
  rw [h₁', (isCub_cubV D.cub hJ).face₃] at c
  have e' := (congrArg₂ (· * ·) rfl c).symm.trans (e.trans (congrArg₂ (· * ·) (h₂ χ y J hJ) (h₂' χ y J hJ)))
  simpa using e'

theorem gtTanR_of_gtComb {m : ℕ} {cf : Fin m → R} {e : Fin m → GtPt D (epsR R)} {ν : GtPt D (epsR R)}
    (h : GtComb cf e ν) (he : ∀ i, GtTanR (e i)) : GtTanR ν := by
  obtain ⟨u, p, hu, h₀, ha, rfl⟩ := h
  have : ∀ i, GtTanR (p i) := fun i => Fin.induction (gtTanR_of_isZero h₀)
    (fun j ih => gtTanR_of_isAdd (ha j) ih (gtTanR_of_scale (hu j) (he j))) i
  exact this _

end

end Tangent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem exists_intHom {E : Type} [Field E] [NumberField E] [IsCMField E] {K₁ : Type} [Field K₁] [NumberField K₁]
    (τK : E →+* K₁) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X) :
    ∃ φ : X →+ 𝓞 K₁, ∀ x, (φ x : K₁) = ((NumberField.discr E : ℤ) : K₁) * τK (cc (pairE ξ x)) := by
  obtain ⟨-, hadd, -, hint, -⟩ := GlobalTheory.ArcQ.pairE_properties E X ξ
  have hi : ∀ x, IsIntegral ℤ (((NumberField.discr E : ℤ) : K₁) * τK (cc (pairE ξ x))) := fun x => by
    have h := (hint x).map (τK.comp (IsCMField.complexConj E).toRingEquiv.toRingHom).toIntAlgHom
    simpa [cc] using h
  refine ⟨AddMonoidHom.mk' (fun x => ⟨_, hi x⟩) fun x y => ?_, fun x => rfl⟩
  apply RingOfIntegers.ext
  show _ * τK (cc (pairE ξ (x + y))) = _ * τK (cc (pairE ξ x)) + _ * τK (cc (pairE ξ y))
  rw [hadd]
  simp [cc, mul_add]

theorem discr_mul_xi_integral : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (ρ : 𝓞 K₁ →+* Tv.V) (ψ : M.aw.D₀.P.A.left ⟶ s.B.A.left), OverLa w Tv.V io 1 → (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → IsPolFibre ρ s.B M.aw.D₀.P ψ → prj M.pw ≫ ψ = prj M.pK ≫ s.φB → TauCan M.aw.D₀ n' → ∀ (τ : E →+* ℂ) (k : Fin (Dw.mult τ)), s.kind τ k = none → ∃ (ν : Out.GtPt M.aw.D₀ (epsR Tv.V)) (ν₁ e₂ : Out.GtPt M.aK.D₀ (epsR Tv.Fr)), GtTanR ν ∧ LetBC M.pw ν ν₁ ∧ LetBC M.pK (d.e τ k) e₂ ∧ GtComb ![((NumberField.discr E : ℤ) : Tv.Fr)] ![e₂] ν₁ := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s w Tv io Wl M ρ ψ _ hρ _ _ _ τ k hk
  have hG : Out.GlobalFnsSt := hK.laws.globalFns
  obtain ⟨φ, hφ⟩ := exists_intHom (labK c K₁ τ) s.ξ
  obtain ⟨hb, hd⟩ := s.xi τ k hk
  obtain ⟨hw1, -, hw3⟩ := GlobalTheory.TorusTangent.main hG Tv.V M.aw.D₀
  obtain ⟨-, -, hK3⟩ := GlobalTheory.TorusTangent.main hG K₁ d.a.D₀
  obtain ⟨hF1, hF2, -⟩ := GlobalTheory.TorusTangent.main hG Tv.Fr M.aK.D₀
  obtain ⟨-, hadd, -⟩ := GlobalTheory.ArcQ.pairE_properties E d.a.D₀.X s.ξ
  let φw : M.aw.D₀.X →+ Tv.V :=
    ρ.toAddMonoidHom.comp (φ.comp (M.pK.xe.toAddMonoidHom.comp M.pw.xe.symm.toAddMonoidHom))
  let φ₀ : d.a.D₀.X →+ K₁ := AddMonoidHom.mk' (fun x => labK c K₁ τ (cc (pairE s.ξ x))) fun x y => by
    rw [hadd]; simp [cc]
  let φ₂ : M.aK.D₀.X →+ Tv.Fr := io.toAddMonoidHom.comp (φ₀.comp M.pK.xe.toAddMonoidHom)
  obtain ⟨ν, ⟨hν, hνb, hνd⟩, -⟩ := hw1 φw
  obtain ⟨ν₁, h₁, -⟩ := GlobalTheory.ArcQBC.existsUnique_letBC M.pw hG ν
  obtain ⟨e₂, h₂, -⟩ := GlobalTheory.ArcQBC.existsUnique_letBC M.pK hG (d.e τ k)
  have t₁ := GlobalTheory.ArcQBC.gtTanR_of_letBC M.pw hG h₁ hν
  have t₂ := GlobalTheory.ArcQBC.gtTanR_of_letBC M.pK hG h₂ (s.tan τ k)
  obtain ⟨b₁, d₁⟩ := hw3 Tv.Fr M.aK.D₀ _ M.pw φw ν ν₁ hνb hνd h₁
  obtain ⟨b₂, d₂⟩ := hK3 Tv.Fr M.aK.D₀ _ M.pK φ₀ (d.e τ k) e₂ hb hd h₂
  obtain ⟨ν', hν'⟩ := GlobalTheory.ConstLie.exists_gtComb ![((NumberField.discr E : ℤ) : Tv.Fr)] ![e₂]
  have t₃ : GtTanR ν' := gtTanR_of_gtComb hν' fun i => by fin_cases i; exact t₂
  obtain ⟨b₃, d₃⟩ := hF2 φ₂ _ e₂ ν' t₂ b₂ d₂ hν'
  have key : ∀ x, algebraMap Tv.V Tv.Fr (φw (M.pw.xe x)) = (((NumberField.discr E : ℤ) : Tv.Fr) • φ₂) x := fun x => by
    show algebraMap Tv.V Tv.Fr (ρ (φ (M.pK.xe (M.pw.xe.symm (M.pw.xe x))))) =
      ((NumberField.discr E : ℤ) : Tv.Fr) * io (labK c K₁ τ (cc (pairE s.ξ (M.pK.xe x))))
    rw [AddEquiv.symm_apply_apply, hρ, hφ, map_mul, map_intCast]
  have e : ν₁ = ν' := (hF1 (((NumberField.discr E : ℤ) : Tv.Fr) • φ₂)).unique
    ⟨t₁, b₁, fun x j hj => (d₁ x j hj).trans (congrArg _ (key x))⟩ ⟨t₃, b₃, d₃⟩
  exact ⟨ν, ν₁, e₂, hν, h₁, h₂, e ▸ hν'⟩

end GlobalTheory.XiIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
section
noncomputable section

namespace GlobalTheory.DvrDeg

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull
attribute [local instance] Over.cartesianMonoidalCategory

section General

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem nonempty_psiOn_generic (D : DegPre R) [IsOpenImmersion (jK R)] : Nonempty (PsiOn D (jK R).opensRange) := by
  let W := (jK R).opensRange
  let s : W.toScheme ⟶ (TK R).left := (jK R).isoOpensRange.inv
  have hs : s ≫ jK R = W.ι := (jK R).isoOpensRange_inv_comp
  have hr : (jK R ∣_ W) ≫ s = (jK R ⁻¹ᵁ W).ι := by
    rw [← cancel_mono (jK R), Category.assoc, hs, morphismRestrict_ι]
  have hx : ∀ χ, s ≫ D.xK χ = (toUnit (TW W) ≫ D.c χ).left := fun χ => by
    show s ≫ jK R ≫ (D.c χ).left = W.ι ≫ (D.c χ).left
    rw [← Category.assoc, hs]
  choose t ht vt using fun χ => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W) ≫ D.c χ).left) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx χ))
    (LB.pullGen D.P.L _ _ (D.psi χ) s) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) s)
  refine ⟨⟨t, ht, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩⟩
  refine (val_pull hJ _ _ _).trans ((vt χ _ _ y J hJ).trans ((val_pull hJ _ _ _).trans
    (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
  exact congrArg (fun q => val (D.psi χ) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·) hr))

theorem exists_isPullDeg_of_val {i : R →+* R'} (hi : Function.Injective i) (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (s : (TK R).left ⟶ W.toScheme) (hs : s ≫ W.ι = jK R)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (genMap hi) z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨g, sq⟩ : ∃ g : (TK R').left ⟶ (TW W).left, g ≫ W.ι = genMap hi ≫ jK R :=
    ⟨genMap hi ≫ s, (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hs)⟩
  have hg : g ≫ W.ι = jK R' ≫ specOf i := sq.trans ((fracMap_sq hi).symm.trans (Category.id_comp _))
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R').left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = genMap hi ∧
      lam ≫ (jK R ∣_ W) = g :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ sq,
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂, hψ x y J J' hJ hJ'] at u
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

attribute [local instance] TorusExt.gtGroup in

theorem exists_qkExt_of_inverse {D : DegPre R} {F F' : Type} [Field F] [Field F'] [Algebra (FractionRing R) F]
    [Algebra (FractionRing R) F'] (f : F →+* F') (σ : F' →+* F) (h : f.comp σ = RingHom.id F')
    (hσ : σ.comp (algebraMap (FractionRing R) F') = algebraMap (FractionRing R) F) {k : ℕ} (q : QkPt D F' k) :
    ∃ p : QkPt D F k, QkExt f p q := by
  obtain ⟨g, h₁, h₂⟩ := q.eq
  obtain ⟨hb, hv⟩ := (isIota_iff _ _).1 h₂
  have e₁ : GtPtF.IsNsmul k (TorusExt.gtExt D σ hσ q.g) (TorusExt.gtExt D σ hσ g) := by
    rw [TorusExt.isNsmul_iff_eq] at h₁ ⊢
    rw [h₁, map_nsmul]
  have e₂ : GtPtF.IsIota q.y (TorusExt.gtExt D σ hσ g) :=
    (isIota_iff _ _).2 ⟨by rw [TorusExt.gtExt_b, hb, DVR.comp_cP], fun χ y J hJ =>
      (TorusExt.gtExt_val σ hσ _ χ hJ).trans ((val_corr hJ (h₂.2 χ) _).trans ((val_pull hJ _ _ _).trans
        (congrArg (fun r => val (D.tau q.y χ) r y J) (TorusExt.extMap_jFK σ hσ))))⟩
  have hs : spMap f ≫ spMap σ = 𝟙 _ := by
    rw [← spMap_comp, h]; exact Spec.map_id (CommRingCat.of F')
  obtain ⟨b, v⟩ := (TorusExt.eq_gtExt_iff σ hσ q.g _).1 rfl
  refine ⟨⟨q.y, TorusExt.gtExt D σ hσ q.g, _, e₁, e₂⟩, rfl, ?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · show q.g.b.left = spMap f ≫ (TorusExt.gtExt D σ hσ q.g).b.left
    rw [b, ← Category.assoc, hs]
    exact (Category.id_comp _).symm
  · refine Eq.symm ((val_pull hJ _ _ _).trans ((val_corr hJ (v χ) _).trans ((val_pull hJ _ _ _).trans ?_)))
    exact congrArg (fun r => val (q.g.s χ) r y J) ((Category.assoc _ _ _).trans
      ((congrArg (𝟙 _ ≫ ·) hs).trans (Category.id_comp _)))

end General

section Dvr

variable (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]

theorem isOpenImmersion_generic : IsOpenImmersion (jK V) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have : IsLocalization.Away ϖ (FractionRing V) := by
    refine (IsLocalization.iff_of_le_of_exists_dvd (Submonoid.powers ϖ)
      (nonZeroDivisors V) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ.ne_zero)
      fun a ha => ?_).2 inferInstance
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero ha) hϖ
    exact ⟨ϖ ^ n, ⟨n, rfl⟩, hn.dvd⟩
  exact IsOpenImmersion.of_isLocalization ϖ

omit [IsDiscreteValuationRing V] in

theorem exists_fracInv : ∃ σ : FractionRing K →+* FractionRing V,
    (fracMap (IsFractionRing.injective V K)).comp σ = RingHom.id _ ∧
    σ.comp (fracMap (IsFractionRing.injective V K)) = RingHom.id _ := by
  let σ : FractionRing K ≃+* FractionRing V :=
    (FractionRing.algEquiv K K).toRingEquiv.trans (FractionRing.algEquiv V K).symm.toRingEquiv
  have h : σ.toRingHom.comp (fracMap (IsFractionRing.injective V K)) = RingHom.id _ :=
    IsLocalization.ringHom_ext (nonZeroDivisors V) (RingHom.ext fun r => by
      show (FractionRing.algEquiv V K).symm (FractionRing.algEquiv K K (fracMap _ (algebraMap V _ r))) = algebraMap V _ r
      rw [fracMap_algebraMap, AlgEquiv.commutes]
      exact (FractionRing.algEquiv V K).symm.commutes r)
  exact ⟨σ.toRingHom, RingHom.ext fun x => σ.injective (RingHom.congr_fun h (σ x)), h⟩

variable {V K}

theorem exists_points {A : Over (Sp V)} {A' : Over (Sp K)} [GrpObj A] [GrpObj A'] [IsProper A.hom]
    {Φ : A'.left ⟶ A.left} (gp : IsGrpPullback A' A (spMap (algebraMap V K)) Φ) {X : Type} [Add X]
    (c : X → (𝟙_ (Over (Sp K)) ⟶ A')) (hc : ∀ a b, c (a + b) = c a * c b) :
    ∃ c₀ : X → (𝟙_ (Over (Sp V)) ⟶ A), (∀ a b, c₀ (a + b) = c₀ a * c₀ b) ∧
      ∀ x, (c x).left ≫ Φ = spMap (algebraMap V K) ≫ (c₀ x).left := by
  have hE : ValuativeCriterion.Existence A.hom := by
    have h : UniversallyClosed A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have ex : ∀ x, ∃ c₀ : 𝟙_ (Over (Sp V)) ⟶ A, (c x).left ≫ Φ = spMap (algebraMap V K) ≫ c₀.left := fun x => by
    let Q : ValuativeCommSq A.hom :=
      { R := V, K := K, i₁ := (c x).left ≫ Φ, i₂ := 𝟙 _, commSq := ⟨by
          rw [Category.assoc, gp.1.w, ← Category.assoc, Over.w]
          exact (Category.id_comp _).trans (Category.comp_id _).symm⟩ }
    obtain ⟨⟨l, h1, h2⟩⟩ := hE Q
    exact ⟨Over.homMk l h2, h1.symm⟩
  choose c₀ h₀ using ex
  refine ⟨c₀, fun a b => ?_, h₀⟩
  have e : spMap (algebraMap V K) ≫ (c₀ (a + b)).left = spMap (algebraMap V K) ≫ (c₀ a * c₀ b).left := by
    rw [← h₀, hc]
    exact mul_push gp (T' := 𝟙_ _) (T := 𝟙_ _) _ (h₀ a) (h₀ b)
  let Q : ValuativeCommSq A.hom :=
    { R := V, K := K, i₁ := spMap (algebraMap V K) ≫ (c₀ (a + b)).left, i₂ := 𝟙 _,
      commSq := ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (c₀ (a + b))))⟩ }
  have := (IsSeparated.valuativeCriterion A.hom Q).elim ⟨(c₀ (a + b)).left, rfl, Over.w _⟩
    ⟨(c₀ a * c₀ b).left, e.symm, Over.w _⟩
  exact Over.OverMorphism.ext (congrArg CommSq.LiftStruct.l this)

theorem exists_isPullDeg (hC : CubeSt) (P : PolAV (Sp V)) (D : DegPre K) (Φ : D.P.A.left ⟶ P.A.left)
    (gp : IsGrpPullback D.P.A P.A (spMap (algebraMap V K)) Φ) (hw₀ : LBIso D.P.L (P.L.pull Φ)) :
    ∃ (D₀ : DegPre V) (hD : IsPullDeg (algebraMap V K) D₀ D), D₀.P = P ∧ HEq (proj hD) Φ := by
  obtain ⟨w₀, hw₀⟩ := hw₀
  have hi := IsFractionRing.injective V K
  have := P.isAb.proper
  have := isOpenImmersion_generic V
  obtain ⟨c₀, cadd, hc⟩ := exists_points gp D.c D.c_add
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cub⟩ := (hC _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := SelfUnif.exists_sym P
  obtain ⟨w, hw, hr⟩ := TripleMap.exists_rigidified P.isLB D.P.isLB w₀ ((isGen_iff w₀).1 hw₀) (eSec P.A)
    (eSec D.P.A) D.P.A.hom (Over.w η[D.P.A]) (spMap (algebraMap V K)) (cubeMapOf gp).e_comm rig hrig D.rig D.rig_gen
  obtain ⟨σ, h₁, h₂⟩ := exists_fracInv V K
  let s : (TK V).left ⟶ (TK K).left := spMap σ
  have s₁ : genMap hi ≫ s = 𝟙 _ :=
    (spMap_comp _ _).symm.trans ((congrArg spMap h₁).trans (Spec.map_id (CommRingCat.of (FractionRing K))))
  have s₂ : s ≫ genMap hi = 𝟙 _ :=
    (spMap_comp _ _).symm.trans ((congrArg spMap h₂).trans (Spec.map_id (CommRingCat.of (FractionRing V))))
  have hx : ∀ χ, D.xK χ ≫ Φ = genMap hi ≫ ptK (c₀ χ) := fun χ => by
    show (jK K ≫ (D.c χ).left) ≫ Φ = genMap hi ≫ jK V ≫ (c₀ χ).left
    rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) ((Category.id_comp _).symm.trans (fracMap_sq hi))
  choose t ht vt using fun χ : D.X => exists_up hw P.isLB D.P.isLB (D.psi χ) (D.psi_gen χ)
  choose psi hpsi vpsi using fun χ : D.X => exists_gen P.isLB (K' := PUnit)
    (φ' := fun _ => ptK (c₀ χ)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (by
      show s ≫ D.xK χ ≫ Φ = _
      rw [hx, ← Category.assoc, s₂, Category.id_comp]))
    (LB.pullGen P.L _ _ (t χ) s) (DVR.pullGen_isGen _ _ _ _ (ht χ) s)
  let D₀ : DegPre V :=
    { P := P, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c₀, c_add := cadd, psi := psi, psi_gen := hpsi }
  obtain ⟨ψW⟩ := nonempty_psiOn_generic D₀
  obtain ⟨hD, e⟩ := exists_isPullDeg_of_val hi D₀ D ψW (jK V).isoOpensRange.hom (jK V).isoOpensRange_hom_ι gp w hw hr
    (AddEquiv.refl _) hc (fun x z J J' hJ hJ' => by
      have v := vt x _ (𝟙 _) z _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
      refine (vpsi x _ _ z J hJ).trans ((val_pull hJ _ _ _).trans
        ((congrArg (fun r => val (t x) r z J) s₁).trans (v.trans (congrArg₂ (· * ·) ?_ rfl))))
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp])
  exact ⟨D₀, hD, rfl, heq_of_eq e⟩

theorem exists_isPullQk_surj (hG : GlobalFnsSt) {D₀ : DegPre V} {D : DegPre K} (hD : IsPullDeg (algebraMap V K) D₀ D)
    {k : ℕ} (q' : QkPt D (FractionRing K) k) : ∃ q, IsPullQk hD q q' := by
  have hi := IsFractionRing.injective V K
  letI : Algebra (FractionRing V) (FractionRing K) := (fracMap hi).toAlgebra
  have hK : Compat (algebraMap V K) (FractionRing K) := fracMap_algebraMap hi
  obtain ⟨σ, h₁, h₂⟩ := exists_fracInv V K
  obtain ⟨q, hy, hg⟩ := qkPullExists hG V K _ D₀ D hD (FractionRing K) hK k q'
  obtain ⟨p, hp⟩ := exists_qkExt_of_inverse (F := FractionRing V) (fracMap hi) σ h₁ h₂ q
  exact ⟨p, _, hK, q, hp, hy, hg⟩

end Dvr

end GlobalTheory.DvrDeg

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem GlobalTheory.DvrDeg.exists_extension : Known → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (Pv : Out.PolAV (Sp V)) (DK : Out.DegPre K) (φ : DK.P.A.left ⟶ Pv.A.left), IsPolFibre (algebraMap V K) Pv DK.P φ → ∃ (DV : Out.DegPre V) (p : Out.IsPullDeg (algebraMap V K) DV DK), DV.P = Pv ∧ HEq (prj p) φ ∧ ∀ (k : ℕ) (q' : Out.QkPt DK (FractionRing K) k), DK.TauBimult → ∃ q, GlobalTheory.ArcPull.IsPullQk p q q' := by
  intro hK V K _ _ _ _ _ _ Pv DK φ h
  obtain ⟨DV, p, h₁, h₂⟩ := GlobalTheory.DvrDeg.exists_isPullDeg hK.laws.cube Pv DK φ h.2.1 h.2.2.symm
  exact ⟨DV, p, h₁, h₂, fun k q' _ => GlobalTheory.DvrDeg.exists_isPullQk_surj hK.laws.globalFns p q'⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLiftOpen
section
noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Units

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem arcιR_isUnit_mul (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) :
    IsUnit (arcιR Dw V ϖ (PowerSeries.C ϖ * PowerSeries.X)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  exact isUnit_of_mul_isUnit_left h

theorem letMR_det_isUnit (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) (τ : E →+* ℂ) :
    IsUnit (letMR Dw V ϖ τ).det := by
  classical
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  have h2 := isUnit_of_mul_isUnit_right h
  have h3 := isUnit_of_dvd_unit (map_dvd (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))
    (Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (PowerSeries V)))) (Finset.mem_univ τ))) h2
  rw [RingHom.map_det] at h3
  exact h3

theorem arcιR_C_isUnit (Dw : Datum H) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {v : V} (hv : v ≠ 0) : IsUnit (arcιR Dw V ϖ (PowerSeries.C v)) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hϖ
  have h := arcιR_isUnit_mul Dw V ϖ
  rw [map_mul (arcιR Dw V ϖ)] at h
  rw [map_mul (PowerSeries.C (R := V)), map_pow (PowerSeries.C (R := V)), map_mul (arcιR Dw V ϖ),
    map_pow (arcιR Dw V ϖ)]
  exact ((u.isUnit.map _).map _).mul ((isUnit_of_mul_isUnit_left h).pow n)

end Units

theorem exists_lift_open {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {S : Type} [CommRing S] (g : c.F →+* S) (χ : Sp S ⟶ Y.X) (hcond : χ ≫ Y.s = spMap g ≫ spMap β)
    (hj : ∀ q : Sp S, χ q ∈ Set.range Y.j) :
    ∃ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = χ ∧ z ≫ pullback.snd _ _ = spMap g := by
  let p : Sp S ⟶ pullback Y.s (spMap β) := pullback.lift χ (spMap g) hcond
  have hr : Set.range p ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    obtain ⟨w, hw⟩ := hj q
    rw [← hw]
    have h2 : Y.jQ w ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨w, rfl⟩
    simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using h2
  have := Y.jQ_open
  refine ⟨IsOpenImmersion.lift Y.jQ p hr, ?_, ?_⟩
  · show IsOpenImmersion.lift Y.jQ p hr ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

theorem exists_dvr_frPt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Tv : CDVR) (ϖ : Tv.V) (f : c.F →+* Tv.Fr) (b : O →+* Tv.V) (a : ArcIn Dw l β Tv.V b) (χ : Sp (PowerSeries Tv.V) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR Tv.V)) (th : a.D₀.P.L.Sec), Irreducible ϖ → f.comp β = (algebraMap Tv.V Tv.Fr).comp b → (∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = f (embK c τ x)) → χ ≫ Y.s = spMap (PowerSeries.C (R := Tv.V)) ≫ spMap b → (∀ x : Sp (PowerSeries Tv.V), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ArcBasis W ρ e → ThNZ th → ∃ (_ : Algebra c.F (ArcSR Dw Tv.V ϖ)), (∀ (x : c.F) (v : Tv.V) (n : ℕ), f x * algebraMap Tv.V Tv.Fr ϖ ^ n = algebraMap Tv.V Tv.Fr v → algebraMap c.F (ArcSR Dw Tv.V ϖ) x * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ) ^ n = arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) v)) ∧ ∃ y₀ yR : FrPt Xo c (ArcSR Dw Tv.V ϖ), IsArcFr W e th (arcιR Dw Tv.V ϖ) y₀ ∧ FrChg (letMR Dw Tv.V ϖ) 1 y₀ yR := by
  intro L1 L2 E _ _ _ H Dw l Xo c O _ β Y Tv ϖ f b a χ W ρ e th hϖ hfb hρ hχ hj _ hpush hbasis hth
  let ι := arcιR Dw Tv.V ϖ
  let κ : Tv.V →+* ArcSR Dw Tv.V ϖ := ι.comp (PowerSeries.C (R := Tv.V))
  have hκ : ∀ y : nonZeroDivisors Tv.V, IsUnit (κ y) := fun y =>
    arcιR_C_isUnit Dw Tv.V hϖ (nonZeroDivisors.ne_zero y.2)
  let g : Tv.Fr →+* ArcSR Dw Tv.V ϖ := IsLocalization.lift hκ
  have hg : ∀ v, g (algebraMap Tv.V Tv.Fr v) = κ v := fun v => IsLocalization.lift_eq hκ v
  letI alg : Algebra c.F (ArcSR Dw Tv.V ϖ) := (g.comp f).toAlgebra
  have halg : ∀ x, algebraMap c.F (ArcSR Dw Tv.V ϖ) x = g (f x) := fun _ => rfl
  refine ⟨alg, ?_, ?_⟩
  · intro x v n h
    have h2 := congrArg g h
    rw [map_mul, map_pow, hg, hg] at h2
    exact h2
  · have hcomp : (algebraMap c.F (ArcSR Dw Tv.V ϖ)).comp β = ι.comp ((PowerSeries.C (R := Tv.V)).comp b) := by
      ext1 x
      have h1 : f (β x) = algebraMap Tv.V Tv.Fr (b x) := RingHom.congr_fun hfb x
      show g (f (β x)) = κ (b x)
      rw [h1, hg]
    have hcond : (spMap ι ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcSR Dw Tv.V ϖ)) ≫ spMap β := by
      rw [Category.assoc, hχ, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]
    obtain ⟨z, hz1, hz2⟩ := exists_lift_open Y (algebraMap c.F (ArcSR Dw Tv.V ϖ)) (spMap ι ≫ χ) hcond (by
      intro q
      rw [Scheme.Hom.comp_apply]
      refine hj _ fun h => ?_
      have h' : ι (PowerSeries.C ϖ * PowerSeries.X) ∈ q.asIdeal := h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (arcιR_isUnit_mul Dw Tv.V ϖ)))
    have hflat := (GlobalTheory.LetterDenom.main E H Dw Tv ϖ hϖ.ne_zero).2.2.1
    obtain ⟨y₀, -, hy₀⟩ := exists_isArcFr L1 L2 E H Dw l Xo c O β Y Tv.V b a χ W ρ e th hbasis hth (Or.inr hpush)
      (ArcSR Dw Tv.V ϖ) ι z hflat hz1
      (by rw [pullback.condition, ← Category.assoc, hz2, ← spMap_comp]; rfl)
      (fun τ x => by rw [halg, ← hρ, hg]; rfl)
    obtain ⟨yR, hyR⟩ := (frChg_exists_unique_units E H Dw l Xo c (ArcSR Dw Tv.V ϖ) (letMR Dw Tv.V ϖ) 1 y₀).1
      (letMR_det_isUnit Dw Tv.V ϖ) isUnit_one
    exact ⟨y₀, yR, hy₀, hyR⟩

end GlobalTheory.ArcQ
end
end

