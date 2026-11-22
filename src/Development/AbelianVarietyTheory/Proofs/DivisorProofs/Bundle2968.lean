import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2830
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2864
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2867
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedEighthPowerBundleClassEqSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.SharpBundle

open GlobalTheory.ZH.EndoExtend GlobalTheory.SquareOfGeneric

theorem prod_left_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} (f g : Z ⟶ (X ⊗ Y).left)
    (h₁ : f ≫ (fst X Y).left = g ≫ (fst X Y).left) (h₂ : f ≫ (snd X Y).left = g ≫ (snd X Y).left) : f = g := by
  apply pullback.hom_ext
  · simpa using h₁
  · simpa using h₂

theorem cls_eq_sum_lam : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : GlobalTheory.ZM.SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀) (y : Sp (FractionRing R) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → ∀ pr : Fin 8 → (A.A ⟶ c.A), LBIso A.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ q : Fin 8 → (G ⟶ G₀), (∀ u, IsMonHom (q u)) → (∀ u, ((Over.pullback (jK R)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → cls U.LG.L U.LG.isLB = ∑ a, ∑ b, W a b • lam (cls U₀.LG.L U₀.LG.isLB) (q a) (q b) := by
  intro g n o _ ζ F W R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG U U₀ y α α₂ hα hαs hαL c φc φ₂ hφ hφs hφL pr hP q hq hqg
  obtain ⟨hno, -, hic, -⟩ := hR.1
  have hS : IsSemiAbelian G := hG
  have := hS.smooth
  have := hS.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  have := U₀.gen_hom
  have hL := U.LG.isLB
  have hL₀ := U₀.LG.isLB
  have hA := A.isLB
  have hA₀ := A₀.isLB
  have hcP := c.isLB
  have hUP := F.univ.isLB
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have hn : Geo.Tor.IsNormalScheme (Sp R) := (GlobalTheory.isNormalScheme_iff_pred _).1 inferInstance

  have key : ∀ a b, CechPic.pull U.gen.hom.left (CechPic.pull (lift (pr a) (pr b)).left (cls c.P hcP)) =
      CechPic.pull (pullback.fst G.hom (jK R)) (lam (cls U₀.LG.L hL₀) (q a) (q b)) := by
    intro a b
    have eP : cls c.P hcP = CechPic.pull φ₂ (cls F.univ.P hUP) := (cls_eq_iff hcP (pull_isLB hUP _)).2 hφL
    have eΛ : CechPic.pull α₂ (cls F.univ.P hUP) = lam (cls A₀.L hA₀) (fst A₀.A A₀.A) (snd A₀.A A₀.A) :=
      ((cls_eq_iff (LB.isLB_linComb hA₀ _ _) (pull_isLB hUP _)).2 hαL).symm.trans (cls_cube_two hA₀ _ _ _)
    have eK : (U.gen.hom ≫ lift (pr a) (pr b)).left ≫ φ₂ =
        (lift ((Over.pullback (jK R)).map (q a) ≫ U₀.gen.hom) ((Over.pullback (jK R)).map (q b) ≫ U₀.gen.hom)).left ≫ α₂ := by
      apply GlobalTheory.SharpBundle.prod_left_ext
      · rw [Category.assoc, hφs.1, Category.assoc, hαs.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, Category.assoc, lift_fst, lift_fst]
        exact (hqg a).symm
      · rw [Category.assoc, hφs.2, Category.assoc, hαs.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
          ← Over.comp_left, Category.assoc, lift_snd, lift_snd]
        exact (hqg b).symm
    have hext₀ : CechPic.pull U₀.gen.hom.left (cls A₀.L hA₀) =
        CechPic.pull (pullback.fst G₀.hom (jK R)) (cls U₀.LG.L hL₀) := by
      obtain ⟨w, hw⟩ := U₀.ext
      rw [← cls_pull hL₀ _ (pull_isLB hL₀ _), ← cls_pull hA₀ _ (pull_isLB hA₀ _)]
      exact (cls_eq_iff _ _).2 ⟨w, hw⟩
    rw [← pull_comp, ← Over.comp_left, eP, ← pull_comp, eK, pull_comp, eΛ, pull_lam, lift_fst, lift_snd, ← lam_pull,
      hext₀, lam_pull_fst]
    let hh : Over.mk (((Over.pullback (jK R)).obj G).hom ≫ jK R) ⟶ G :=
      Over.homMk (pullback.fst G.hom (jK R)) pullback.condition
    show _ = CechPic.pull hh.left _
    rw [pull_lam]
    congr 1 <;> ext1 <;> exact pullback.lift_fst _ _ _
  refine pic_ext (jK R) hn G (eSec G) (Over.w η[G]) ?_ ?_
  · have h0 : CechPic.pull (eSec G) (cls U.LG.L hL) = 0 :=
      (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨U.LG.rig, U.LG.rigGen⟩
    rw [h0, map_sum]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    have := hq a
    have := hq b
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ G₀) = η[G₀] := by rw [Hom.one_def]; simp
    rw [map_zsmul]
    show _ • CechPic.pull η[G].left _ = 0
    rw [pull_lam, IsMonHom.one_hom, IsMonHom.one_hom, ← e₁, lam_one_left, smul_zero]
  · have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
        CechPic.pull U.gen.hom.left (cls A.L hA) := by
      obtain ⟨w, hw⟩ := U.ext
      rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
      exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
    rw [hc', (cls_eq_iff hA (LB.isLB_linComb hcP _ _)).2 hP, cls_linComb hcP, map_sum, map_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_zsmul, map_zsmul, key]

end GlobalTheory.SharpBundle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalUniq

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem abPart_eq {ρ : R →+* R'} {s : R' →+* R'} {D : DegPre R} {D' : DegPre R'}
    (hD : IsPullDeg ρ D D') (h h' : IsPullDeg s D' D') (H : PullOver hD h) (H' : PullOver hD h') :
    h.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) =
      h'.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s) := by
  have hcb := H.2 _ _ rfl rfl
  have hcb' := H'.2 _ _ rfl rfl
  have hov : ∀ k : IsPullDeg s D' D', (k.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf s)) ≫ D'.P.A.hom =
      D'.P.A.hom ≫ specOf s := by
    intro k
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w k.e.hom
  have : IsIso hD.e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map hD.e.hom))
  rw [← cancel_mono hD.e.hom.left]
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc]
    simp only [Category.assoc] at hcb hcb'
    rw [hcb, hcb']
  · simp only [Category.assoc]
    have w0 : hD.e.hom.left ≫ pullback.snd D.P.A.hom (specOf ρ) = D'.P.A.hom := Over.w hD.e.hom
    rw [w0, ← Category.assoc, hov h, ← Category.assoc, hov h']

theorem iso_eq_of_rig {s : R' →+* R'} {D' : DegPre R'} (F : D'.P.A.left ⟶ D'.P.A.left)
    (he : eSec D'.P.A ≫ F = specOf s ≫ eSec D'.P.A)
    (w w' : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen) (hw' : w'.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig))
    (hr' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig)) : w = w' :=
  iso_unique_of_rig GlobalTheory.globalFns_holds D'.P.A D'.P.isAb D'.P.isLB D'.P.isLB hw hw' hr hr'

theorem level_eq {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (g : GtCoord I' D' e G') (F : D'.P.A.left ⟶ D'.P.A.left)
    (w : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen)
    (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left)
    (hb : f ≫ pullback.snd G'.hom (thick R' I' e) = f' ≫ pullback.snd G'.hom (thick R' I' e))
    (hp : g.pG.left ≫ F = f ≫ g.pG.left) (hp' : g.pG.left ≫ F = f' ≫ g.pG.left)
    (ht : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG x k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t x)))
    (ht' : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f' ≫ D'.Oφ g.pG x k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f' _ Oinvε _ hψ (g.t x))) : f = f' := by
  refine GlobalTheory.T.thickenedUniformisedGroup_point_ext g f f' hb (hp.symm.trans hp') fun z J hJ χ => ?_
  obtain ⟨hψ, hm⟩ := ht χ
  obtain ⟨hψ', hm'⟩ := ht' χ
  exact GlobalTheory.T.torusCoordinate_value_eq_of_maps g F w f f' χ hψ hψ' hm hm' z J hJ

end GlobalTheory.Mum.GalUniq

namespace GlobalTheory.Mum.GalUniq

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem level_eq_two {s : R' →+* R'} {I' : Ideal R'} {D' : DegPre R'} {e : ℕ} {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (g : GtCoord I' D' e G') (F F' : D'.P.A.left ⟶ D'.P.A.left) (hF : F = F')
    (he : eSec D'.P.A ≫ F = specOf s ≫ eSec D'.P.A) (he' : eSec D'.P.A ≫ F' = specOf s ≫ eSec D'.P.A)
    (w : LB.Iso D'.P.L (D'.P.L.pull F)) (hw : w.IsGen)
    (w' : LB.Iso D'.P.L (D'.P.L.pull F')) (hw' : w'.IsGen)
    (hr : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F (specOf s) he D'.P.L D'.rig))
    (hr' : LB.Gen.Maps (LB.linCombIso w' (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => 1)) D'.rig
      (rigPullOf F' (specOf s) he' D'.P.L D'.rig))
    (xe xe' : D'.X → D'.X) (hxe : xe = id) (hxe' : xe' = id)
    (f f' : (thickObj R' I' e G').left ⟶ (thickObj R' I' e G').left)
    (hb : f ≫ pullback.snd G'.hom (thick R' I' e) = f' ≫ pullback.snd G'.hom (thick R' I' e))
    (hp : g.pG.left ≫ F = f ≫ g.pG.left) (hp' : g.pG.left ≫ F' = f' ≫ g.pG.left)
    (ht : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F = f ≫ D'.Oφ g.pG (xe x) k,
      LB.Gen.Maps (LB.linCombIso w _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F f _ Oinvε _ hψ (g.t (xe x))))
    (ht' : ∀ x : D'.X, ∃ hψ : ∀ k : Fin 4, D'.Oφ g.pG x k ≫ F' = f' ≫ D'.Oφ g.pG (xe' x) k,
      LB.Gen.Maps (LB.linCombIso w' _ Oinvε) (g.t x)
        (GeneratorPullback.pullAlong D'.P.L F' f' _ Oinvε _ hψ (g.t (xe' x)))) : f = f' := by
  subst hF hxe hxe'
  obtain rfl := iso_eq_of_rig F he w w' hw hw' hr hr'
  exact level_eq g F w hw f f' hb hp hp' ht ht'

end GlobalTheory.Mum.GalUniq

open GlobalTheory.Mum.GalUniq in

theorem GlobalTheory.Mum.galMap_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (σ : Gal ρ) (a a' : G'.left ⟶ G'.left), GalMap hD U' σ a → GalMap hD U' σ a' → a = a' := by
  intro R _ _ _ _ R' _ _ _ ρ hρ D D' hD A' G' _ _ hG U' σ a a' ha ha'
  obtain ⟨-, h, bc, rfl, P, PO⟩ := ha
  obtain ⟨-, h', bc', rfl, P', PO'⟩ := ha'
  have hc := abPart_eq hD h h' PO PO'
  have hxe : (⇑h.xe : D'.toPre.X → D'.toPre.X) = id := funext PO.1
  have hxe' : (⇑h'.xe : D'.toPre.X → D'.toPre.X) = id := funext PO'.1
  have hov : ∀ (b : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      b.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) ≫ G'.hom = G'.hom ≫ specOf (Gal.hom σ) := by
    intro b
    rw [pullback.condition, ← Category.assoc]
    congr 1
    exact Over.w b.hom
  have lev : ∀ n : ℕ, (fstG (maximalIdeal R') n G').left ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) =
      (fstG (maximalIdeal R') n G').left ≫ bc'.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) := by
    intro n
    obtain ⟨wL, -, he1, -, hl⟩ := P.lg
    obtain ⟨wL', -, he1', -, hl'⟩ := P'.lg
    obtain ⟨f, hf, hpG, hT, -⟩ := hl n
    obtain ⟨f', hf', hpG', hT', -⟩ := hl' n
    have hb : f ≫ pullback.snd G'.hom (thick R' (maximalIdeal R') n) =
        f' ≫ pullback.snd G'.hom (thick R' (maximalIdeal R') n) := by
      have : IsClosedImmersion (thick R' (maximalIdeal R') n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      rw [← cancel_mono (thick R' (maximalIdeal R') n), Category.assoc, Category.assoc,
        ← pullback.condition]
      have e1 : f ≫ (fstG (maximalIdeal R') n G').left ≫ G'.hom =
          (fstG (maximalIdeal R') n G').left ≫ G'.hom ≫ specOf (Gal.hom σ) := by
        rw [← Category.assoc, hf]; simp only [Category.assoc]; rw [hov bc]
      have e2 : f' ≫ (fstG (maximalIdeal R') n G').left ≫ G'.hom =
          (fstG (maximalIdeal R') n G').left ≫ G'.hom ≫ specOf (Gal.hom σ) := by
        rw [← Category.assoc, hf']; simp only [Category.assoc]; rw [hov bc']
      exact e1.trans e2.symm
    have := level_eq_two (U'.gt n) _ _ hc h.he h'.he h.w h.w_gen h'.w h'.w_gen h.w_rig h'.w_rig _ _ hxe hxe' f f' hb hpG hpG' hT hT'
    rw [← hf, ← hf', this]
  have hI : maximalIdeal R' ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have : IsNoetherianRing R' := hρ.1.1
  have : Smooth G'.hom := hG.smooth
  have : GeometricallyConnected G'.hom := hG.geomConnected
  have : IsSeparated G'.hom := hG.separated
  have : IsIso (CommRingCat.ofHom (Gal.hom σ)) := σ.1.toCommRingCatIso.isIso_hom
  have : IsIso (specOf (Gal.hom σ)) := inferInstanceAs (IsIso (Spec.map _))
  let Y : Over (Sp R') := Over.mk (G'.hom ≫ inv (specOf (Gal.hom σ)))
  have : IsSeparated Y.hom := inferInstanceAs (IsSeparated (G'.hom ≫ inv (specOf (Gal.hom σ))))
  have hov2 : ∀ (b : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'),
      (b.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) ≫ Y.hom = G'.hom := by
    intro b
    change _ ≫ G'.hom ≫ inv (specOf (Gal.hom σ)) = _
    simp only [Category.assoc]
    rw [reassoc_of% (hov b), IsIso.hom_inv_id, Category.comp_id]
  have key := (sec_eq_zero_and_hom_eq_of_thickenings R' (maximalIdeal R') hI G').2 Y
    (Over.homMk (bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (hov2 bc))
    (Over.homMk (bc'.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ))) (hov2 bc')) lev
  exact congrArg CommaMorphism.left key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomExtOfInducedMapsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroupHom_ext_of_induced_maps : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (g g' : G ⟶ G) (b : D'.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D'.toPre.X), IsMonHom g → IsMonHom g' → Over₀ U'.toUnifPre U.toUnifPre g b → Over₀ U'.toUnifPre U.toUnifPre g' b → OnTorus U'.toUnifPre U.toUnifPre g h → OnTorus U'.toUnifPre U.toUnifPre g' h → g = g' := by
  first | exact @GlobalTheory.Mum.Two.hom_eq_of_over₀_onTorus | exact GlobalTheory.Mum.Two.hom_eq_of_over₀_onTorus | (intros; apply GlobalTheory.Mum.Two.hom_eq_of_over₀_onTorus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomInducedMapsUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroupHom_induced_maps_unique : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂), (∀ b b' : D₁.toPre.P.A ⟶ D₂.toPre.P.A, Over₀ U₁ U₂ a b → Over₀ U₁ U₂ a b' → b = b') ∧ ∀ h h' : D₂.toPre.X → D₁.toPre.X, OnTorus U₁ U₂ a h → OnTorus U₁ U₂ a h' → h = h' := by
  first | exact @GlobalTheory.Mum.Two.over₀_onTorus_unique | exact GlobalTheory.Mum.Two.over₀_onTorus_unique | (intros; apply GlobalTheory.Mum.Two.over₀_onTorus_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupHomPullbackMapsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroupHom_pullback_maps : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (D₁' D₂' : DegData R' I') (A₁' A₂' : PolAV (Sp (FractionRing R'))) (hD₁ : IsPullDeg φ D₁.toPre D₁'.toPre) (hD₂ : IsPullDeg φ D₂.toPre D₂'.toPre) (U₁' : Unif I' D₁' A₁' ((Over.pullback (specOf φ)).obj G₁)) (U₂' : Unif I' D₂' A₂' ((Over.pullback (specOf φ)).obj G₂)), IsPullUnif φ hD₁ (Iso.refl _) U₁ U₁' → IsPullUnif φ hD₂ (Iso.refl _) U₂ U₂' → ∀ (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁.toUnifPre U₂.toUnifPre a b h → ∃ (b' : D₁'.toPre.P.A ⟶ D₂'.toPre.P.A) (h' : D₂'.toPre.X →+ D₁'.toPre.X), Lin U₁'.toUnifPre U₂'.toUnifPre ((Over.pullback (specOf φ)).map a) b' h' ∧ b' ≫ hD₂.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf φ)).map b ∧ ∀ χ, hD₁.xe (h' χ) = h (hD₂.xe χ) := by
  first | exact @GlobalTheory.Mum.Two.PullLin.linPull | exact GlobalTheory.Mum.Two.PullLin.linPull | (intros; apply GlobalTheory.Mum.Two.PullLin.linPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupIsoAbelianPartCharacterIsos
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
open GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.TInj

theorem torusHomOf_comp' {S : Scheme.{0}} {X₁ X₂ X₃ : Type} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    {h : X₂ → X₁} {k : X₃ → X₂} {t : splitTorus S X₁ ⟶ splitTorus S X₂} {s : splitTorus S X₂ ⟶ splitTorus S X₃}
    (ht : TorusHomOf h t) (hs : TorusHomOf k s) : TorusHomOf (fun χ => h (k χ)) (t ≫ s) := fun χ => by
  rw [← ht (k χ), ← hs χ]
  refine unit_ext fun z _ => ?_
  refine ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_
  refine Eq.symm (((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans ?_)
  refine ((gm_res _ z (V := ⊤) _ trivial _).trans (gm_pull _ _ z ⊤ trivial _)).trans ?_
  rfl

theorem torusHomOf_id' {S : Scheme.{0}} (X : Type) [AddCommGroup X] : TorusHomOf (fun χ : X => χ) (𝟙 (splitTorus S X)) :=
  fun χ => unit_ext fun z _ =>
    ((gm_res (𝟙 _) z (V := ⊤) _ trivial _).trans (gm_pull (𝟙 _) _ z ⊤ trivial _)).trans rfl

theorem iso_lin_coord : ∀ (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂) (a : G₁ ≅ G₂), IsMonHom a.hom → ∃ (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X ≃+ D₁.toPre.X), IsIso b ∧ Lin U₁ U₂ a.hom b h.toAddMonoidHom ∧ Coord U₁ U₂ a.hom b h.toAddMonoidHom := by
  intro R _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ a ha
  have ha' : IsMonHom a.inv := inferInstance
  obtain ⟨b, hb, hbO⟩ := exists_abelian_hom R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom ha
  obtain ⟨b', hb', hb'O⟩ := exists_abelian_hom R J hR D₂ D₁ A₂ A₁ G₂ G₁ U₂ U₁ a.inv ha'
  obtain ⟨h, hh⟩ := unifPre_hom_character_const R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom ha
  obtain ⟨h', hh'⟩ := unifPre_hom_character_const R J hR D₂ D₁ A₂ A₁ G₂ G₁ U₂ U₁ a.inv ha'
  have oComp : ∀ {Da Db : DegData R J} {Aa Ab : PolAV (Sp (FractionRing R))} {Ga Gb : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb]
      (Ua : UnifPre J Da Aa Ga) (Ub : UnifPre J Db Ab Gb) (f : Ga ⟶ Gb) (g : Gb ⟶ Ga) c c',
      Over₀ Ua Ub f c → Over₀ Ub Ua g c' → Over₀ Ua Ua (f ≫ g) (c ≫ c') := by
    intro Da Db Aa Ab Ga Gb _ _ _ _ Ua Ub f g c c' hf hg e
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hg e, ← Category.assoc, hf e, Category.assoc]
  have tComp : ∀ {Da Db : DegData R J} {Aa Ab : PolAV (Sp (FractionRing R))} {Ga Gb : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] [GrpObj Gb] [IsCommMonObj Gb]
      (Ua : UnifPre J Da Aa Ga) (Ub : UnifPre J Db Ab Gb) (f : Ga ⟶ Gb) (g : Gb ⟶ Ga) k k',
      OnTorus Ua Ub f k → OnTorus Ub Ua g k' → OnTorus Ua Ua (f ≫ g) (fun χ => k (k' χ)) := by
    intro Da Db Aa Ab Ga Gb _ _ _ _ Ua Ub f g k k' hf hg e
    obtain ⟨t, ht, hi⟩ := hf e
    obtain ⟨s, hs, hj⟩ := hg e
    refine ⟨t ≫ s, torusHomOf_comp' ht hs, ?_⟩
    rw [Functor.map_comp, ← Category.assoc, hi, Category.assoc, hj, Category.assoc]
  have oId : ∀ {Da : DegData R J} {Aa : PolAV (Sp (FractionRing R))} {Ga : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] (Ua : UnifPre J Da Aa Ga), Over₀ Ua Ua (𝟙 Ga) (𝟙 _) := by
    intro Da Aa Ga _ _ Ua e
    simp
  have tId : ∀ {Da : DegData R J} {Aa : PolAV (Sp (FractionRing R))} {Ga : Over (Sp R)}
      [GrpObj Ga] [IsCommMonObj Ga] (Ua : UnifPre J Da Aa Ga), OnTorus Ua Ua (𝟙 Ga) (fun χ => χ) := by
    intro Da Aa Ga _ _ Ua e
    exact ⟨𝟙 _, torusHomOf_id' _, by simp⟩
  have u₁ := over₀_onTorus_unique R J hR D₁ D₁ A₁ A₁ G₁ G₁ U₁ U₁ (𝟙 G₁)
  have u₂ := over₀_onTorus_unique R J hR D₂ D₂ A₂ A₂ G₂ G₂ U₂ U₂ (𝟙 G₂)
  have bb : b ≫ b' = 𝟙 _ := u₁.1 _ _ (a.hom_inv_id ▸ oComp U₁ U₂ a.hom a.inv b b' hbO hb'O) (oId U₁)
  have bb' : b' ≫ b = 𝟙 _ := u₂.1 _ _ (a.inv_hom_id ▸ oComp U₂ U₁ a.inv a.hom b' b hb'O hbO) (oId U₂)
  have hh₁ : (fun χ => h (h' χ)) = fun χ => χ :=
    u₁.2 _ _ (a.hom_inv_id ▸ tComp U₁ U₂ a.hom a.inv h h' hh hh') (tId U₁)
  have hh₂ : (fun χ => h' (h χ)) = fun χ => χ :=
    u₂.2 _ _ (a.inv_hom_id ▸ tComp U₂ U₁ a.inv a.hom h' h hh' hh) (tId U₂)
  let hE : D₂.toPre.X ≃+ D₁.toPre.X :=
    { toFun := h, invFun := h', left_inv := fun χ => congrFun hh₂ χ, right_inv := fun χ => congrFun hh₁ χ,
      map_add' := h.map_add }
  have hL : Lin U₁ U₂ a.hom b hE.toAddMonoidHom := ⟨ha, hb, hbO, hh⟩
  exact ⟨b, hE, ⟨b', bb, bb'⟩, hL, coord_of_lin R J hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a.hom b _ hL⟩

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupProdZpowCharacterMap
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

theorem torusHomOf_iff_charUnit {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

theorem charUnit_eq_pointsEquiv {S : Scheme.{0}} {X : Type} [AddCommGroup X] (χ : X) :
    charUnit S X χ = GlobalTheory.splitTorusPointsEquiv S X _ (𝟙 _) (Multiplicative.ofAdd χ) :=
  Units.ext ((GlobalTheory.splitTorusPointsEquiv_val S X _ (𝟙 _) χ).trans (GlobalTheory.SplitTorusHom.appTop_id _)).symm

theorem torusHomOf_prod_zpow {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {K : Type}
    [Fintype K] (n : K → ℤ) (h : K → X' → X) (t : K → (splitTorus S X ⟶ splitTorus S X'))
    (ht : ∀ i, TorusHomOf (h i) (t i)) : TorusHomOf (fun χ => ∑ i, n i • h i χ) (∏ i, t i ^ n i) := by
  simp only [torusHomOf_iff_charUnit] at ht
  rw [torusHomOf_iff_charUnit]
  intro χ
  have e₁ : ∀ i, GlobalTheory.splitTorusPointsEquiv S X' _ (t i) (Multiplicative.ofAdd χ) = charUnit S X (h i χ) := fun i =>
    Units.ext ((GlobalTheory.splitTorusPointsEquiv_val S X' _ (t i) χ).trans (ht i χ))
  rw [← GlobalTheory.splitTorusPointsEquiv_val, map_prod]
  simp only [map_zpow, MonoidHom.finset_prod_apply, MonoidHom.zpow_apply, e₁]
  rw [charUnit_eq_pointsEquiv, ofAdd_sum, map_prod]
  simp only [ofAdd_zsmul, map_zpow, ← charUnit_eq_pointsEquiv]

end GlobalTheory.Mum.PowData

theorem GlobalTheory.Mum.PowData.onTorus_prod_zpow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (h : K → D₀.toPre.X → D.toPre.X), (∀ i, OnTorus U U₀ (a i) (h i)) → OnTorus U U₀ (∏ i, a i ^ n i) (fun χ => ∑ i, n i • h i χ) := by
  intro R _ _ I D D₀ A A₀ G G₀ _ _ _ _ U U₀ K _ n a h H e
  choose t ht et using fun i => H i e
  refine ⟨∏ i, t i ^ n i, torusHomOf_prod_zpow n h t ht, ?_⟩
  have := (U₀.gt e).i_hom
  have hm : (Over.pullback (thick R I e)).map (∏ i, a i ^ n i) = ∏ i, (Over.pullback (thick R I e)).map (a i) ^ n i :=
    (map_prod ((Over.pullback (thick R I e)).homMonoidHom (X := G) (M := G₀)) _ _).trans
      (Finset.prod_congr rfl fun i _ => map_zpow ((Over.pullback (thick R I e)).homMonoidHom (X := G) (M := G₀)) _ _)
  rw [hm, comp_prod_zpow, prod_zpow_comp]
  exact Finset.prod_congr rfl fun i _ => by rw [et i]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupProdZpowOverAbelianParts
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData

theorem over₀_prod_zpow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), ∀ (D D₀ : DegData R I) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], ∀ (U : UnifPre I D A G) (U₀ : UnifPre I D₀ A₀ G₀) (K : Type) [Fintype K] (n : K → ℤ) (a : K → (G ⟶ G₀)) (b : K → (D.toPre.P.A ⟶ D₀.toPre.P.A)), (∀ i, Over₀ U U₀ (a i) (b i)) → Over₀ U U₀ (∏ i, a i ^ n i) (∏ i, b i ^ n i) := by
  intro R _ _ I D D₀ A A₀ G G₀ _ _ _ _ U U₀ K _ n a b h e
  let P := Over.pullback (thick R I e)
  have := (U₀.gt e).q_hom
  let fG : (G ⟶ G₀) →* (P.obj G ⟶ P.obj G₀) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  let fB : (D.toPre.P.A ⟶ D₀.toPre.P.A) →* (P.obj D.toPre.P.A ⟶ P.obj D₀.toPre.P.A) :=
    MonoidHom.mk' (fun x => P.map x) fun x y => Functor.map_mul P x y
  have hG : P.map (∏ i, a i ^ n i) = ∏ i, P.map (a i) ^ n i :=
    (map_prod fG _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fG _ _)
  have hB : P.map (∏ i, b i ^ n i) = ∏ i, P.map (b i) ^ n i :=
    (map_prod fB _ _).trans (Finset.prod_congr rfl fun i _ => map_zpow fB _ _)
  show P.map (∏ i, a i ^ n i) ≫ (U₀.gt e).q = (U.gt e).q ≫ P.map (∏ i, b i ^ n i)
  rw [hG, hB, prod_zpow_comp, comp_prod_zpow]
  exact Finset.prod_congr rfl fun i _ => by rw [h i e]

end GlobalTheory.Mum.PowData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedTraitMovesToFiniteExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedTrait_moves_to_finite_extension : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁], Base R₁ → ∀ (D₁ : DegData R₁ (maximalIdeal R₁)) (A : PolAV (Sp (FractionRing R₁))), UniTrait D₁.toPre A → ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (i₁₂ : R₁ →+* R₂), FinExt i₁₂ → IsLocalHom i₁₂ → ∀ (D₂ : DegData R₂ (maximalIdeal R₂)), Nonempty (IsPullDeg i₁₂ D₁.toPre D₂.toPre) → ∀ (A₂ : PolAV (Sp (FractionRing R₂))) (a : A₂.A.left ⟶ A.A.left), IsFib i₁₂ A A₂ a → UniTrait D₂.toPre A₂ := by
  first | exact @GlobalTheory.Mum.UniEnlarge.uniTrait_of_finExt | exact GlobalTheory.Mum.UniEnlarge.uniTrait_of_finExt | (intros; apply GlobalTheory.Mum.UniEnlarge.uniTrait_of_finExt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTripleFibrePrincipallyPolarisedDimensioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalTriple_fibre_principallyPolarised_dimension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] (x : Sp R ⟶ Xo.X), PolFib Xo.univ.t.G Xo.univ.t.PP.L (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) x := by
  first | exact @GlobalTheory.UMin.polFib_univ | exact GlobalTheory.UMin.polFib_univ | (intros; apply GlobalTheory.UMin.polFib_univ <;> assumption)
end

