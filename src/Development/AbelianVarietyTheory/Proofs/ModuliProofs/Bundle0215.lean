import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.OLinBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ImportsTer
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnifMove

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT GlobalTheory.ArcPull GlobalTheory.PullLinear in

theorem exists_pull {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R}
    {I' : Ideal R'} (hR : AdmBase R I) (hR' : AdmBase R' I') (g : R →+* R') (hg : Function.Injective g)
    (hI : I.map g ≤ I') (gK : FractionRing R →+* FractionRing R') (sq : spMap gK ≫ jK R = jK R' ≫ spMap g)
    {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ (D' : DegData R' I') (hD : IsPullDeg g D.toPre D'.toPre) (A' : PolAV (Spec (CommRingCat.of (FractionRing R'))))
      (gA : A'.A.left ⟶ A.A.left) (U' : Unif I' D' A' ((Over.pullback (specOf g)).obj G)),
      IsPullUnif g hD (Iso.refl _) U U' ∧ IsGrpPullback A'.A A.A (spMap gK) gA ∧ LBIso A'.L (A.L.pull gA) ∧
      U'.gen.hom.left ≫ gA ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
        pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g) := by
  have hP : PolBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.polBaseChange
  have hU : UnifBaseChangeSt := GlobalTheory.UnifPullGuards.unifBaseChange_holds
  have hψ : PsiOnExistsSt := psiOnExists
  obtain ⟨A', gA, pA, dA, mA, tA⟩ := hP _ _ (spMap gK) A
  have gpA : IsGrpPullback A'.A A.A (spMap gK) gA := ⟨pA, fun T x y x₀ y₀ hx hy => by
    have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
    have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
    rw [e₁, e₂, ← mA]; rfl⟩
  have gpG := ThetaBaseChange.grp_generic U.toUnifPre
  have gp' : IsGrpPullback ((Over.pullback (jK R')).obj ((Over.pullback (specOf g)).obj G)) G (spMap gK ≫ jK R)
      (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap g)) :=
    ((isGrpPullback_pullback ((Over.pullback (specOf g)).obj G) (jK R')).comp (isGrpPullback_pullback G (spMap g))).congr sq.symm rfl
  obtain ⟨eA, mE, heA⟩ := grpPullback_iso gp' (gpA.comp gpG)
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hbc : (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = pullback.fst G.hom (spMap g) :=
    Category.id_comp _
  have wA : LBIso (A'.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst ((Over.pullback (specOf g)).obj G).hom (jK R') ≫
      (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g))) := by
    refine LBIso.trans (pull_isLB A'.isLB _) (pull_isLB (pull_isLB A.isLB gA) eA.hom.left)
      (pull_isLB U.LG.isLB _)
      ((LBIso.symm tA).chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull A'.L _ _ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (A.L.pull gA) _ _ rfl)) ?_
    refine LBIso.chartPull (h := eA.hom.left ≫ gA ≫ U.gen.inv.left)
      (chartPullLinComb A.L gA (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => ?_)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => ?_) U.ext
    · rw [Category.assoc, Category.assoc, hgi, Category.comp_id]
    · rw [hbc, ← heA]; simp only [Category.assoc]
  have he : eSec ((Over.pullback (specOf g)).obj G) ≫ (Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g) = specOf g ≫ eSec G := by
    rw [hbc]; exact (cubeMapOf (isGrpPullback_pullback G (spMap g))).e_comm
  have hr : (rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig).IsGen :=
    LBxP.isGen_pullAlong U.LG.L _ (specOf g) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec ((Over.pullback (specOf g)).obj G))
      (fun _ => he) U.LG.rig U.LG.rigGen
  let L' : RigLB ((Over.pullback (specOf g)).obj G) := ⟨U.LG.L.pull ((Iso.refl ((Over.pullback (specOf g)).obj G)).hom.left ≫ pullback.fst G.hom (specOf g)),
    rigPullOf (G := G) (G' := (Over.pullback (specOf g)).obj G) _ (specOf g) he U.LG.L U.LG.rig, pull_isLB U.LG.isLB _, hr⟩
  obtain ⟨Wo, hWo, hψ⟩ := hψ R I hR D
  have hgen : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) ∈ Wo := by
    have : (specOf g).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)
    rw [this]; exact hWo
  have mR : IsMonHom (Iso.refl ((Over.pullback (specOf g)).obj G)).hom := by show IsMonHom (𝟙 _); infer_instance
  obtain ⟨D', hD, U', -, hgenU, hPU⟩ := hU R R' I I' hR hR' g hI D A G hG U Wo hψ hgen ((Over.pullback (specOf g)).obj G)
    (Iso.refl _) mR A' dA eA mE wA L' (idIso _) he (idIso_isGen L'.isLB) (fun p => hr p.1 p.2)
  exact ⟨D', hD, A', gA, U', hPU, gpA, LBIso.symm tA, by rw [hgenU]; exact heA⟩

end GlobalTheory.UnifMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiUnitOnOfNeUniv
section
noncomputable section

namespace GlobalTheory.DvrDataCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke

section Ext

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem isFinUnram_of (W : UnramExt V) : DVRSplitting.IsFinUnram V W.W := ⟨W.inj, W.fin, W.unram⟩

theorem complete_of (hV : IsAdicComplete (maximalIdeal V) V) {W : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Algebra V W] (h : DVRSplitting.IsFinUnram V W) : IsAdicComplete (maximalIdeal W) W := by
  have := h.2.1
  rw [← h.map_maximalIdeal.2]
  exact isAdicComplete_map_of_finite (maximalIdeal V) W

def bundle (hV : IsAdicComplete (maximalIdeal V) V) (W : Type) [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Algebra V W] (h : DVRSplitting.IsFinUnram V W) : UnramExt V :=
  { W := W, fin := h.2.1, inj := h.1, unram := h.2.2, complete := complete_of hV h }

def extEquiv (hV : IsAdicComplete (maximalIdeal V) V) : UnramExt V ≃
    Σ' (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra V W),
      DVRSplitting.IsFinUnram V W where
  toFun W := ⟨W.W, W.ring, W.dom, W.dvr, W.alg, isFinUnram_of W⟩
  invFun x := @bundle V _ _ _ hV x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2
  left_inv _ := rfl
  right_inv _ := rfl

end Ext

section Move

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem psiUnitOn_of_ne_univ (D : DegPre R) (χ : D.X) {U : Set (Sp R)} (hU : U ≠ Set.univ) : PsiUnitOn D χ U := by
  intro j V _ hVU _ h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) := by
    refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} e => ⟨1, by rw [IsFractionRing.injective R _ e]⟩⟩
    · rintro ⟨_, n, rfl⟩
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (pow_ne_zero n hϖ.ne_zero))
    · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj (nonZeroDivisors R) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hϖ
      refine ⟨⟨a * (u⁻¹ : Rˣ), ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
      have e₁ : ϖ ^ n = (b : R) * (u⁻¹ : Rˣ) := by rw [hu, _root_.mul_right_comm, Units.mul_inv, _root_.one_mul]
      show z * algebraMap R _ (ϖ ^ n) = algebraMap R _ (a * (u⁻¹ : Rˣ))
      rw [e₁, map_mul, map_mul, ← _root_.mul_assoc]
      exact congrArg (· * _) e
  have : IsOpenImmersion (jK R) := IsOpenImmersion.of_isLocalization ϖ
  have hV : V ≤ (jK R).opensRange := by
    intro x hx
    have hx' : x ≠ closedPoint R := fun e => hU (Set.eq_univ_of_univ_subset (by
      have : V = ⊤ := (closedPoint_mem_iff V).1 (e ▸ hx)
      rw [this] at hVU
      exact hVU))
    have hb : x.asIdeal = ⊥ := by
      by_contra hb
      have := x.isPrime
      exact hx' (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal hb)))
    refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
    rw [hb]
    exact Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  have := (jK R).isIso_app V hV
  have hb := ConcreteCategory.bijective_of_isIso ((jK R).app V)
  obtain ⟨r, hr⟩ := hb.2 (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val)
  refine ⟨r, ?_, hr⟩
  have hu : IsUnit (((jK R).app V).hom r) := by
    have : ((jK R).app V).hom r = _ := hr
    rw [this]
    exact (Units.isUnit _).map _
  exact (MulEquiv.isUnit_map (RingEquiv.ofBijective ((jK R).app V).hom hb)).1 hu

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem exists_pull (P : ValPt Y) (W : UnramExt P.V) : ∃ t : SAB H (Sp W.W), Nonempty (SABMap t Y.t (P.ξ W)) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull allSixLaws.2.2.1.cubePull (P.ξ W) Y.t
  exact ⟨_, ⟨m⟩⟩

def DataWhereSplit (Y : Model Xo c β) : Prop :=
  ∀ (P : ValPt Y) (W : UnramExt P.V) (t : SAB H (Sp W.W)) (_ : SABMap t Y.t (P.ξ W)), SplitOver W t → DvrDataOver P W t

end GlobalTheory.DvrDataCompare
end
end

