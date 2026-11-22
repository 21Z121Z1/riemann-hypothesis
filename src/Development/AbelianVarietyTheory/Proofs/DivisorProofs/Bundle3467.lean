import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2616
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelFamilyProperExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3341
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3400
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3407
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3431
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOfBijectiveLiftSemi
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianUniformizationLinearActionDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.TraitTwist

theorem exists_bundle_data_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₉ : Type) [CommRing R₉] [IsDomain R₉] [IsLocalRing R₉] (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) [GrpObj G₉] [IsCommMonObj G₉] (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ → IsGrpPullback G₉ G (spMap ρ₉) β₉ → Geo.Tor.IsSquare β₉ β₉₂ → IsSemiAbelian G₉ → LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) → EvenOn P₉ → IsMonHom gen₉.hom → LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) → ∃ (R₀ : Type) (_ : CommRing R₀) (_ : IsDomain R₀) (_ : IsLocalRing R₀) (ρ₀ : R →+* R₀) (D₀ : DegData R₀ (maximalIdeal R₀)) (G₀ : Over (Sp R₀)) (_ : GrpObj G₀) (_ : IsCommMonObj G₀) (β₀ : G₀.left ⟶ G.left) (β₀₂ : (G2 G₀).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₀) (A₀ : PolAV (Sp (FractionRing R₀))) (gen₀ : (Over.pullback (jK R₀)).obj G₀ ≅ A₀.A), FinExt ρ₀ ∧ Nonempty (IsPullDeg ρ₀ D.toPre D₀.toPre) ∧ IsGrpPullback G₀ G (spMap ρ₀) β₀ ∧ Geo.Tor.IsSquare β₀ β₀₂ ∧ IsSemiAbelian G₀ ∧ LBIso (abelian₂ G₀ P.L.L) ((abelian₂ G' U'.LG.L).pull (β₀₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P ∧ IsMonHom gen₀.hom ∧ LBIso (A₀.L.pull gen₀.hom.left) (P.L.L.pull (pullback.fst G₀.hom (jK R₀))) ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₀ →+* W), Function.Injective φ → IsLocalHom φ → ∀ (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (β : GW.left ⟶ G₀.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW), IsGrpPullback GW G₀ (spMap φ) β → LBIso UW.LG.L (P.L.L.pull β) → Nonempty (IsPullDeg φ D₀.toPre DW.toPre) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi R₉ _ _ _ ρ₉ G₉ _ _ β₉ β₉₂ P₉ A₉ gen₉ hfin₉ hpb₉ hsq₉ hG₉ hlam₉ hev₉ hgen₉ hgl₉
  have hR₉ : Base R₉ := ⟨hfin₉.1, by
    haveI := hR.2
    exact charZero_of_injective_ringHom hfin₉.2.1⟩
  obtain ⟨D₉', U₉, hL₉, -⟩ := GlobalTheory.T.exists_uniformisation_completeLocal_evenOnTorus R₉ hR₉ G₉ P₉ hG₉ hev₉ A₉ gen₉ hgen₉ hgl₉
  obtain ⟨D₉, hD₉, hsame⟩ := GlobalTheory.T.uniformisation_pulledBackFactor_samePolarisation R hR D D' F A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi R₉ ρ₉ G₉ β₉ β₉₂ P₉ hfin₉ hpb₉ hsq₉ hG₉ hlam₉ A₉ D₉' U₉ hL₉
  obtain ⟨R₀, _, _, _, ρ, D₀, G₀, _, _, β, β₂, A₀, U₀, hfin, hD₀, hpb, hsq, hlam⟩ :=
    GlobalTheory.T.samePolarisedData_uniformise_finite_extension R₉ hR₉ D₉ D₉' A₉ G₉ hG₉ U₉ hsame
  have hG₀ : IsSemiAbelian G₀ := GlobalTheory.SiegLoc.TraitOrd.isSemiAbelian_of_isGrpPullback hpb hG₉
  obtain ⟨P, hPL, hPE⟩ := GlobalTheory.Mum.unif_evenOn R₀ hfin.1 D₀ A₀ G₀ hG₀ U₀
  obtain ⟨hfin', hD'⟩ := GlobalTheory.Mum.FinExtComp.finExt_comp_isPullDeg R R₉ R₀ ρ₉ ρ D.toPre D₉.toPre D₀.toPre hfin₉ hfin hD₉ hD₀
  have hsp : spMap (ρ.comp ρ₉) = spMap ρ ≫ spMap ρ₉ := by
    simp only [spMap]
    rw [← Spec.map_comp]
    rfl
  refine ⟨R₀, inferInstance, inferInstance, inferInstance, ρ.comp ρ₉, D₀, G₀, inferInstance, inferInstance, β ≫ β₉, β₂ ≫ β₉₂, P, A₀, U₀.gen,
    hfin', hD', ?_, GlobalTheory.ZM.SiegPull.isSquare_comp hsq hsq₉, hG₀, ?_, hPE, U₀.gen_hom, ?_, ?_⟩
  · rw [hsp]; exact IsGrpPullback.comp hpb hpb₉
  · rw [hPL]
    rw [← hL₉] at hlam₉
    have i₁ : (abelian₂ G₀ U₀.LG.L).IsLB := LB.isLB_linComb U₀.LG.isLB _ _
    have i₂ : ((abelian₂ G₉ U₉.LG.L).pull β₂).IsLB := pull_isLB (LB.isLB_linComb U₉.LG.isLB _ _) _
    have i₃ : ((abelian₂ G' U'.LG.L).pull ((β₂ ≫ β₉₂) ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)).IsLB :=
      pull_isLB (LB.isLB_linComb U'.LG.isLB _ _) _
    exact LBIso.trans i₁ i₂ i₃ hlam (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hlam₉ β₂ (Category.assoc _ _ _))
  · rw [hPL]; exact U₀.ext
  · intro W _ _ _ hW φ hφ hloc GW _ _ βW DW AW UW hpbW hLW
    rw [hPL] at hLW
    exact GlobalTheory.T.uniformization_base_change_complete_dvr R₀ hfin.1 D₀ A₀ G₀ hG₀ U₀ W hW φ hφ hloc GW βW DW AW UW hpbW hLW

end GlobalTheory.Mum.TraitTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackOfIdempotentImagesAndActionPullbac
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.UPel.HT

theorem siegPB_of_zRel_actPB : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O)
    (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O)
    (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B)
    (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A))
    (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)),
    ActPB w₂ act₂ w₁ act₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ → SiegPB c₂ c₁ y := by
  intro h h' M B _ ζ O _ e jl n o κ S₁ S₂ s₁ s₂ y c₁ w₁ act₁ c₂ w₂ act₂ hA hZ₁ hZ₂
  obtain ⟨ψ, ψ₂, hψ, sψ, lψ, vψ, aψ⟩ := hA
  obtain ⟨inc₁, pr₁, mi₁, mp₁, ip₁, pi₁, L₁, V₁, -⟩ := hZ₁
  obtain ⟨inc₂, pr₂, mi₂, mp₂, ip₂, pi₂, L₂, V₂, -⟩ := hZ₂
  have ip₁' : inc₁.left ≫ pr₁.left = 𝟙 _ := by rw [← Over.comp_left, ip₁]; rfl
  have ip₂' : inc₂.left ≫ pr₂.left = 𝟙 _ := by rw [← Over.comp_left, ip₂]; rfl
  have pi₁' : pr₁.left ≫ inc₁.left = (act₁ e).left := by rw [← Over.comp_left, pi₁]
  have pi₂' : pr₂.left ≫ inc₂.left = (act₂ e).left := by rw [← Over.comp_left, pi₂]
  have K0 : inc₂.left ≫ (act₂ e).left = inc₂.left := by
    rw [← pi₂', ← Category.assoc, ip₂', Category.id_comp]
  obtain ⟨φ, hφ⟩ : ∃ φ : c₂.A.left ⟶ c₁.A.left, φ = inc₂.left ≫ ψ ≫ pr₁.left := ⟨_, rfl⟩
  have K1 : φ ≫ inc₁.left = inc₂.left ≫ ψ := by
    rw [hφ, Category.assoc, Category.assoc, pi₁', ← aψ e, ← Category.assoc, K0]
  have K2 : pr₂.left ≫ φ = ψ ≫ pr₁.left := by
    have : (act₁ e).left ≫ pr₁.left = pr₁.left := by
      rw [← pi₁', Category.assoc, ip₁', Category.comp_id]
    rw [hφ, ← Category.assoc, ← Category.assoc, pi₂', aψ e, Category.assoc, this]
  have hw : φ ≫ c₁.A.hom = c₂.A.hom ≫ y := by
    rw [hφ, Category.assoc, Category.assoc, Over.w pr₁, hψ.1.w, ← Category.assoc, Over.w inc₂]
  have hpb : IsPullback φ c₂.A.hom c₁.A.hom y := by
    let lft : ∀ s : PullbackCone c₁.A.hom y, s.pt ⟶ c₂.A.left := fun s =>
      hψ.1.lift (s.fst ≫ inc₁.left) s.snd (by rw [Category.assoc, Over.w inc₁]; exact s.condition) ≫ pr₂.left
    refine IsPullback.of_isLimit (c := PullbackCone.mk φ c₂.A.hom hw)
      (PullbackCone.IsLimit.mk hw lft (fun s => ?_) (fun s => ?_) (fun s m hm1 hm2 => ?_))
    · simp only [lft]
      rw [Category.assoc, K2, ← Category.assoc, hψ.1.lift_fst, Category.assoc, ip₁', Category.comp_id]
    · simp only [lft]
      rw [Category.assoc, Over.w pr₂, hψ.1.lift_snd]
    · have e₁ : m ≫ inc₂.left = hψ.1.lift (s.fst ≫ inc₁.left) s.snd
          (by rw [Category.assoc, Over.w inc₁]; exact s.condition) := by
        apply hψ.1.hom_ext
        · rw [hψ.1.lift_fst, Category.assoc, ← K1, ← Category.assoc, hm1]
        · rw [hψ.1.lift_snd, Category.assoc, Over.w inc₂, hm2]
      calc m = m ≫ inc₂.left ≫ pr₂.left := by rw [ip₂', Category.comp_id]
        _ = lft s := by rw [← Category.assoc, e₁]
  have hmul : ∀ (T : Over S₂) (x x' : T ⟶ c₂.A) (x₀ x₀' : Over.mk (T.hom ≫ y) ⟶ c₁.A),
      x₀.left = x.left ≫ φ → x₀'.left = x'.left ≫ φ → (x₀ * x₀').left = (x * x').left ≫ φ := by
    intro T x x' x₀ x₀' hx hx'
    haveI := mi₂
    haveI := mp₁
    have wx : ∀ z : T ⟶ c₂.A, ((z ≫ inc₂).left ≫ ψ) ≫ w₁.A.hom = (Over.mk (T.hom ≫ y)).hom := fun z => by
      rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w (z ≫ inc₂)]; rfl
    let X₀ : Over.mk (T.hom ≫ y) ⟶ w₁.A := Over.homMk ((x ≫ inc₂).left ≫ ψ) (wx x)
    let X₀' : Over.mk (T.hom ≫ y) ⟶ w₁.A := Over.homMk ((x' ≫ inc₂).left ≫ ψ) (wx x')
    have m := hψ.2 T (x ≫ inc₂) (x' ≫ inc₂) X₀ X₀' rfl rfl
    rw [← mul_comp] at m
    have e₀ : X₀ ≫ pr₁ = x₀ := by
      ext1
      rw [Over.comp_left, hx, hφ]
      show ((x ≫ inc₂).left ≫ ψ) ≫ pr₁.left = _
      rw [Over.comp_left]; simp only [Category.assoc]
    have e₀' : X₀' ≫ pr₁ = x₀' := by
      ext1
      rw [Over.comp_left, hx', hφ]
      show ((x' ≫ inc₂).left ≫ ψ) ≫ pr₁.left = _
      rw [Over.comp_left]; simp only [Category.assoc]
    rw [← e₀, ← e₀', ← mul_comp, Over.comp_left, m, hφ, Over.comp_left, Category.assoc, Category.assoc]
  have sq := ActUnr.sqMap_fst hw
  have sq' := ActUnr.sqMap_snd hw
  refine ⟨φ, ActUnr.sqMap hw, ⟨hpb, hmul⟩, ⟨sq, sq'⟩, ?_, fun a => ?_⟩
  · have f₁ : (inc₁ ⊗ₘ inc₁).left ≫ (fst w₁.A w₁.A).left = (fst c₁.A c₁.A).left ≫ inc₁.left := by
      rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
    have g₁ : (inc₁ ⊗ₘ inc₁).left ≫ (snd w₁.A w₁.A).left = (snd c₁.A c₁.A).left ≫ inc₁.left := by
      rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
    have f₂ : (inc₂ ⊗ₘ inc₂).left ≫ (fst w₂.A w₂.A).left = (fst c₂.A c₂.A).left ≫ inc₂.left := by
      rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
    have g₂ : (inc₂ ⊗ₘ inc₂).left ≫ (snd w₂.A w₂.A).left = (snd c₂.A c₂.A).left ≫ inc₂.left := by
      rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
    have E : (inc₂ ⊗ₘ inc₂).left ≫ ψ₂ = ActUnr.sqMap hw ≫ (inc₁ ⊗ₘ inc₁).left := by
      apply ActUnr.left_hom_ext
      · rw [Category.assoc, sψ.1, ← Category.assoc, f₂]
        simp only [Category.assoc]
        rw [f₁]
        rw [← Category.assoc (ActUnr.sqMap hw), sq, Category.assoc, K1]
      · rw [Category.assoc, sψ.2, ← Category.assoc, g₂]
        simp only [Category.assoc]
        rw [g₁]
        rw [← Category.assoc (ActUnr.sqMap hw), sq', Category.assoc, K1]
    have l₂ := GlobalTheory.TChart.AbLevel.lbIso_comp w₁.isLB w₂.isLB c₂.isLB lψ L₂
    have hN := pull_isLB c₁.isLB (ActUnr.sqMap hw)
    have l₁ := GlobalTheory.TChart.AbLevel.lbIso_comp w₁.isLB c₁.isLB hN L₁ ((GlobalTheory.CechPic.cls_eq_iff hN hN).1 rfl)
    rw [E] at l₂
    exact LBIso.trans c₂.isLB (pull_isLB w₁.isLB _) hN l₂ (LBIso.symm l₁)
  · calc (c₂.lev a).left ≫ φ = (c₂.lev a ≫ inc₂).left ≫ ψ ≫ pr₁.left := by
          rw [hφ, Over.comp_left, Category.assoc]
      _ = (w₂.lev (jl a)).left ≫ ψ ≫ pr₁.left := by rw [V₂ a]
      _ = y ≫ (w₁.lev (jl a)).left ≫ pr₁.left := by rw [← Category.assoc, vψ, Category.assoc]
      _ = y ≫ (c₁.lev a).left := by rw [← V₁ a, Over.comp_left, Category.assoc, ip₁', Category.comp_id]

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackWithActionCancellation
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem actPB_cancel : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (S S₁ S₂ : Scheme.{0})
    (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)) (g₁ : S₁ ⟶ S)
    (y : S₂ ⟶ S₁) (w₁ : SiegPre h M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (w₂ : SiegPre h M ζ s₂)
    (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₁ act₁ z act g₁ → ActPB w₂ act₂ z act (y ≫ g₁) → ActPB w₂ act₂ w₁ act₁ y := by
  intro h M B _ ζ O _ S S₁ S₂ s s₁ s₂ z act g₁ y w₁ act₁ w₂ act₂ m₁ m₂
  obtain ⟨φ₁, φ₁₂, h1, s1, p1, l1, a1⟩ := m₁
  obtain ⟨φ₂, φ₂₂, h2, s2, p2, l2, a2⟩ := m₂
  have hw : φ₂ ≫ z.A.hom = (w₂.A.hom ≫ y) ≫ g₁ := by rw [h2.1.w, Category.assoc]
  let ψ : w₂.A.left ⟶ w₁.A.left := h1.1.lift φ₂ (w₂.A.hom ≫ y) hw
  have hψ₁ : ψ ≫ φ₁ = φ₂ := h1.1.lift_fst _ _ _
  have hψ : ψ ≫ w₁.A.hom = w₂.A.hom ≫ y := h1.1.lift_snd _ _ _
  let ψ₂ : (G2 w₂.A).left ⟶ (G2 w₁.A).left := ActUnr.sqMap hψ
  have sψ : IsSquare ψ ψ₂ := ⟨ActUnr.sqMap_fst hψ, ActUnr.sqMap_snd hψ⟩
  have e₂ : φ₂₂ = ψ₂ ≫ φ₁₂ := by
    apply ActUnr.left_hom_ext
    · rw [s2.1, Category.assoc, s1.1, ← Category.assoc, sψ.1, Category.assoc, hψ₁]
    · rw [s2.2, Category.assoc, s1.2, ← Category.assoc, sψ.2, Category.assoc, hψ₁]
  have n : IsGrpPullback w₂.A z.A (y ≫ g₁) (ψ ≫ φ₁) := by rw [hψ₁]; exact h2
  refine ⟨ψ, ψ₂, IsGrpPullback.cancel h1 n hψ, sψ, ?_, fun a => ?_, fun o => ?_⟩
  · refine LBIso.trans w₂.isLB (pull_isLB z.isLB _) (pull_isLB w₁.isLB _) p2 ?_
    refine LBIso.trans (pull_isLB z.isLB _) (pull_isLB (pull_isLB z.isLB _) _) (pull_isLB w₁.isLB _)
      (GlobalTheory.GenSpread.lbIso_pull_pull z.isLB ψ₂ e₂) ?_
    exact GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm p1) ψ₂
  · apply h1.1.hom_ext
    · rw [Category.assoc, hψ₁, l2 a, Category.assoc, Category.assoc, l1 a]
    · rw [Category.assoc, hψ, ← Category.assoc, Over.w (w₂.lev a), Category.assoc, Over.w (w₁.lev a)]
      simp
  · apply h1.1.hom_ext
    · rw [Category.assoc, hψ₁, a2 o, Category.assoc, a1 o, ← Category.assoc, hψ₁]
    · rw [Category.assoc, hψ, ← Category.assoc, Over.w (act₂ o), Category.assoc, Over.w (act₁ o), hψ]

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkDerivationMemSpanInvariantSemiAbelian
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDerSpan

open GlobalTheory.TangentOrigin

theorem stalk_derivation_span : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Algebra ℚ R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (p : G.left), G.hom.base p = genericPoint (Sp R) → ∀ (D : Fin n → G.left.presheaf.stalk p → G.left.presheaf.stalk p), (∀ a (W : G.left.Opens) (h : p ∈ W) (g : Γ(G.left, W)), D a (G.left.presheaf.germ W p h g) = G.left.presheaf.germ W p h (dd a W g)) → ∀ (δ : G.left.presheaf.stalk p → ResidueField (G.left.presheaf.stalk p)), (∀ u w, δ (u + w) = δ u + δ w) → (∀ u w, δ (u * w) = residue _ u * δ w + residue _ w * δ u) → (∀ r : R, δ ((G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = 0) → ∃ c : Fin n → G.left.presheaf.stalk p, ∀ y, δ y = residue _ (∑ a, c a * D a y) := by
  intro R _ _ _ _ G _ _ hsa n v dd hinv p _ D hD δ hadd hmul hbase
  haveI : Smooth G.hom := hsa.smooth
  have hv := GlobalTheory.VertCoeffRing.isLieBasis_tvE v
  have hdd := fun (B : Type) [CommRing B] [Algebra R B] e he z O h =>
    GlobalTheory.VertCoeffRing.evalPt_lieExp (fun a => v a) dd hinv B e he z O h

  let ψ : ∀ (V : G.left.Opens), p ∈ V → Γ(G.left, V) →+* ResidueField (G.left.presheaf.stalk p) :=
    fun V hpV => (residue _).comp (G.left.presheaf.germ V p hpV).hom
  have germ_res : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V') (f : Γ(G.left, V)),
      G.left.presheaf.germ V' p hpV' (resG G.left e f) = G.left.presheaf.germ V p hpV f := by
    intro V V' e hpV hpV' f
    exact TopCat.Presheaf.germ_res_apply _ (homOfLE e) p hpV' f

  have loc : ∀ (V : G.left.Opens) (hpV : p ∈ V), IsAffineOpen V →
      ∃! c : Fin n → ResidueField (G.left.presheaf.stalk p),
        ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f) := by
    intro V hpV hV
    obtain ⟨t, ht, et⟩ := exists_evalPt_eq hV (ψ V hpV)
    letI : Algebra R (ResidueField (G.left.presheaf.stalk p)) := (Spec.preimage (t ≫ G.hom)).hom.toAlgebra
    let y : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) (ResidueField (G.left.presheaf.stalk p)) ⟶ G :=
      Over.homMk t (Spec.map_preimage (t ≫ G.hom)).symm
    have h : ⊤ ≤ y.left ⁻¹ᵁ V := ht
    have ev : ∀ s, evalPt y.left V h s = ψ V hpV s := fun s => by
      change evalPt t V ht s = _
      rw [et]
    have hconst : ∀ r, G.left.presheaf.germ V p hpV (constFn G.hom V r) =
        (G.left.presheaf.germ ⊤ p trivial).hom ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
      intro r
      have e1 : constFn G.hom V r = resG G.left (le_top : V ≤ ⊤)
          ((G.hom.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) := by
        unfold constFn
        first
          | rfl
          | (rw [Scheme.Hom.appLE_eq_app_comp_map] ; rfl)
          | (simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]; rfl)
      rw [e1]
      exact germ_res ⊤ V le_top trivial hpV _
    have := GlobalTheory.VertCoeffRing.existsUnique_coeff_alg hv hdd y hV h
      (fun f => δ (G.left.presheaf.germ V p hpV f))
      (fun f f' => by simp only [map_add, hadd])
      (fun f f' => by simp only [map_mul, hmul, ev]; rfl)
      (fun r => by rw [hconst]; exact hbase r)
    simpa only [ev] using this

  have down : ∀ (V V' : G.left.Opens) (e : V' ≤ V) (hpV : p ∈ V) (hpV' : p ∈ V')
      (c : Fin n → ResidueField (G.left.presheaf.stalk p)),
      (∀ f, δ (G.left.presheaf.germ V' p hpV' f) = ∑ a, c a * ψ V' hpV' (dd a V' f)) →
      ∀ f, δ (G.left.presheaf.germ V p hpV f) = ∑ a, c a * ψ V hpV (dd a V f) := by
    intro V V' e hpV hpV' c hc f
    rw [← germ_res V V' e hpV hpV' f, hc]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    change residue _ (G.left.presheaf.germ V' p hpV' (dd a V' (resG G.left e f))) =
      residue _ (G.left.presheaf.germ V p hpV (dd a V f))
    rw [(hinv a).1.2.2 V V' e le_top f, germ_res]
  obtain ⟨V₀, hV₀, hpV₀, -⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ (⊤ : G.left.Opens) from trivial)
  obtain ⟨c₀, hc₀, hu₀⟩ := loc V₀ hpV₀ hV₀
  choose c hc using fun a => residue_surjective (R := G.left.presheaf.stalk p) (c₀ a)
  refine ⟨c, fun y => ?_⟩
  obtain ⟨W, hpW, g, rfl⟩ := TopCat.Presheaf.germ_exist _ y
  obtain ⟨V', hV', hpV', hle⟩ := exists_isAffineOpen_mem_and_subset (show p ∈ V₀ ⊓ W from ⟨hpV₀, hpW⟩)
  obtain ⟨c', hc', -⟩ := loc V' hpV' hV'
  have hcc : c' = c₀ := hu₀ c' (down V₀ V' (hle.trans inf_le_left) hpV₀ hpV' c' hc')
  subst hcc
  have eW : V' ≤ W := hle.trans inf_le_right
  rw [← germ_res W V' eW hpW hpV' g, hc', map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, hc, hD]
  rfl

end GlobalTheory.StalkDerSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1FiniteAffineOpen
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechFinGen

theorem finite_piece (hO : GlobalTheory.AbCoh.OStr) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (f : R) (hf : IsIdempotentElem f) (g : ℕ)
    (hg : SmoothOfRelativeDimension g (pullback.snd A.hom (spMap (Ideal.Quotient.mk (Ideal.span {1 - f}))))) :
    Module.Finite (R ⧸ Ideal.span {1 - f}) ((R ⧸ Ideal.span {1 - f}) ⊗[R] HO1 A.hom) := by
  haveI : IsLocalization.Away f (R ⧸ Ideal.span {1 - f}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem hf
  haveI : Module.Flat R (R ⧸ Ideal.span {1 - f}) :=
    IsLocalization.flat (R ⧸ Ideal.span {1 - f}) (Submonoid.powers f)
  let B : Over (Sp (R ⧸ Ideal.span {1 - f})) :=
    (Over.pullback (spMap (algebraMap R (R ⧸ Ideal.span {1 - f})))).obj A
  letI : GrpObj B := Functor.grpObjObj
  have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj _ A hA
  have hBg : SmoothOfRelativeDimension g B.hom := hg
  obtain ⟨hfp, -, -, -⟩ := hO _ B g hB hBg
  haveI := hA.proper
  obtain ⟨⟨e, -⟩, -⟩ := GlobalTheory.AbCoh.flat_baseChange_HO R (R ⧸ Ideal.span {1 - f}) A.left B.left A.hom B.hom
    (pullback.fst _ _) (IsPullback.of_hasPullback _ _) inferInstance inferInstance
  haveI := hfp.1
  exact Module.Finite.equiv e.symm

theorem finite_HO1 (hO : GlobalTheory.AbCoh.OStr) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) : Module.Finite R (HO1 A.hom) := by
  obtain ⟨n, e, he, hsm⟩ := GlobalTheory.DimSplit.exists_idempotents_smoothOfRelativeDimension R A hA
  have hspan : Ideal.span (Set.range e) = ⊤ := by
    rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff, ← he.complete]
    exact Ideal.sum_mem _ (fun k _ ↦ Ideal.subset_span ⟨k, rfl⟩)
  have hidem : ∀ g : Set.range e, IsIdempotentElem g.val := by
    rintro ⟨_, k, rfl⟩; exact he.idem k
  haveI : ∀ g : Set.range e, IsLocalization.Away g.val (R ⧸ Ideal.span {1 - g.val}) := fun g ↦
    IsLocalization.Away.quotient_of_isIdempotentElem (hidem g)
  haveI : ∀ g : Set.range e, IsLocalizedModule.Away g.val
      (TensorProduct.mk R (R ⧸ Ideal.span {1 - g.val}) (HO1 A.hom) 1) := fun g ↦
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.val) (R ⧸ Ideal.span {1 - g.val}) _).2
      (TensorProduct.isBaseChange R (HO1 A.hom) (R ⧸ Ideal.span {1 - g.val}))
  refine Module.Finite.of_localizationSpan' (Set.range e) hspan
    (Rₚ := fun g ↦ R ⧸ Ideal.span {1 - g.val})
    (Mₚ := fun g ↦ (R ⧸ Ideal.span {1 - g.val}) ⊗[R] HO1 A.hom)
    (fun g ↦ TensorProduct.mk R (R ⧸ Ideal.span {1 - g.val}) (HO1 A.hom) 1) (fun g ↦ ?_)
  obtain ⟨_, k, rfl⟩ := g
  obtain ⟨d, hd⟩ := hsm k
  exact finite_piece hO A hA (e k) (he.idem k) d hd

end GlobalTheory.CechFinGen

theorem GlobalTheory.CechFinGen.finite_HO1_onAff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ U : X.affineOpens,
    Module.Finite Γ(X, U.1) (HO1 (GlobalTheory.DeRhamSheaf.onAff t.G U.2).hom) := by
  intro E _ _ _ H X t hp U
  letI : GrpObj (GlobalTheory.DeRhamSheaf.onAff t.G U.2) := Functor.grpObjObj
  have hA : IsAbelianScheme t.G := GlobalTheory.AbelianLocusNormalisation.isAbelianScheme_of_isProper t hp
  exact GlobalTheory.CechFinGen.finite_HO1 GlobalTheory.AbCoh.oStr (GlobalTheory.DeRhamSheaf.onAff t.G U.2) (GlobalTheory.DeRhamSheaf.isAbelianScheme_onAff hA U.2)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1NakayamaClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

set_option autoImplicit false
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct

namespace GlobalTheory.AbCohFibre

theorem mem_smul_top_of_tmul_tmul_eq_zero {R S M : Type} [CommRing R] [CommRing S] [Algebra R S] (m : Ideal R)
    [Algebra S (R ⧸ m)] [IsScalarTower R S (R ⧸ m)] [AddCommGroup M] [Module R M] (x : M)
    (hx : ((1 : R ⧸ m) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] x) : (R ⧸ m) ⊗[S] (S ⊗[R] M)) = 0) :
    x ∈ m • (⊤ : Submodule R M) := by
  have h1 := congrArg (AlgebraTensorModule.cancelBaseChange R S (R ⧸ m) (R ⧸ m) M) hx
  rw [AlgebraTensorModule.cancelBaseChange_tmul, one_smul, map_zero] at h1
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul M m) h1
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

theorem mem_smul_top_of_pull_eq_zero : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (m : Ideal R), m.IsMaximal → ∀ (Y : Scheme.{0}) (s' : Y ⟶ Sp (R ⧸ m)) (φ : Y ⟶ A.left) (h : IsPullback φ s' A.hom (spMap (algebraMap R (R ⧸ m)))) (x : GlobalTheory.CechDR.HO1 A.hom), GlobalTheory.CechDR.pullHO1 h.w x = 0 → x ∈ m • (⊤ : Submodule R (GlobalTheory.CechDR.HO1 A.hom)) := by
  intro R _ A _ hA m hm Y s' φ h x hx
  haveI : m.IsMaximal := hm
  haveI : m.IsPrime := hm.isPrime
  let f := spMap (algebraMap R (Localization.AtPrime m))
  letI : GrpObj ((Over.pullback f).obj A) := Functor.grpObjObj
  have hAm : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.AbLaw.CubeGen.isAb_baseChange hA f
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim (Localization.AtPrime m) ((Over.pullback f).obj A) hAm
  have hsq0 : IsPullback (pullback.fst A.hom f) ((Over.pullback f).obj A).hom A.hom f :=
    IsPullback.of_hasPullback A.hom f
  have := hA.proper
  obtain ⟨⟨e₁, he₁⟩, -⟩ := GlobalTheory.AbCoh.flat_baseChange_HO R (Localization.AtPrime m) A.left _ A.hom _ _ hsq0
    inferInstance inferInstance
  obtain ⟨-, -, hbc, -⟩ := GlobalTheory.AbCoh.oStr (Localization.AtPrime m) ((Over.pullback f).obj A) g hAm hg
  let ψ : Localization.AtPrime m →+* R ⧸ m :=
    IsLocalization.lift (M := m.primeCompl) (g := Ideal.Quotient.mk m) (fun y : m.primeCompl => by
      show IsUnit (Ideal.Quotient.mk m (y : R))
      have hy : Ideal.Quotient.mk m (y : R) ≠ 0 := by rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact y.2
      letI := Ideal.Quotient.field m
      exact isUnit_iff_ne_zero.mpr hy)
  letI : Algebra (Localization.AtPrime m) (R ⧸ m) := ψ.toAlgebra
  have hcomp : (algebraMap (Localization.AtPrime m) (R ⧸ m)).comp (algebraMap R (Localization.AtPrime m)) =
      algebraMap R (R ⧸ m) := IsLocalization.lift_comp _
  haveI : IsScalarTower R (Localization.AtPrime m) (R ⧸ m) := IsScalarTower.of_algebraMap_eq'  hcomp.symm
  have hsp : spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) ≫ f = spMap (algebraMap R (R ⧸ m)) := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  let φ' : Y ⟶ ((Over.pullback f).obj A).left :=
    pullback.lift φ (s' ≫ spMap (algebraMap (Localization.AtPrime m) (R ⧸ m))) (by
      rw [h.w, Category.assoc, hsp])
  have hφ' : φ' ≫ pullback.fst A.hom f = φ := pullback.lift_fst _ _ _
  have hs' : φ' ≫ ((Over.pullback f).obj A).hom = s' ≫ spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) :=
    pullback.lift_snd _ _ _
  have hbig : IsPullback (φ' ≫ pullback.fst A.hom f) s' A.hom
      (spMap (algebraMap (Localization.AtPrime m) (R ⧸ m)) ≫ f) := by
    rw [hφ', hsp]; exact h
  have hsq : IsPullback φ' s' ((Over.pullback f).obj A).hom (spMap (algebraMap (Localization.AtPrime m) (R ⧸ m))) :=
    IsPullback.of_right hbig hs' hsq0
  obtain ⟨e₂, he₂⟩ := hbc (R ⧸ m) Y s' φ' hsq
  have cong : ∀ (φ₁ : Y ⟶ A.left) (σ₁ : R →+* R ⧸ m) (h₁ : φ₁ ≫ A.hom = s' ≫ spMap σ₁), φ₁ = φ →
      σ₁ = algebraMap R (R ⧸ m) → GlobalTheory.CechDR.pullHO1 h₁ x = GlobalTheory.CechDR.pullHO1 h.w x := by
    rintro _ _ _ rfl rfl; rfl
  have h'' : (φ' ≫ pullback.fst A.hom f) ≫ A.hom =
      s' ≫ spMap ((algebraMap (Localization.AtPrime m) (R ⧸ m)).comp (algebraMap R (Localization.AtPrime m))) := by
    rw [hφ', hcomp]; exact h.w
  have key : GlobalTheory.CechDR.pullHO1 hsq.w (GlobalTheory.CechDR.pullHO1 hsq0.w x) = 0 := by
    rw [GlobalTheory.CechDR.pullHO1_comp hsq0.w hsq.w h'', cong _ _ h'' hφ' hcomp]
    exact hx
  have k1 : ((1 : R ⧸ m) ⊗ₜ[Localization.AtPrime m] (GlobalTheory.CechDR.pullHO1 hsq0.w x)) = 0 := by
    apply e₂.injective
    rw [he₂, map_zero]; exact key
  have k2 := congrArg (LinearMap.lTensor (R ⧸ m) e₁.symm.toLinearMap) k1
  rw [LinearMap.lTensor_tmul, map_zero, ← he₁, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at k2
  exact mem_smul_top_of_tmul_tmul_eq_zero m x k2

end GlobalTheory.AbCohFibre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricBalancedTensorsFiniteProjectiveRankDimStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_balanced_tensors_finite_projective_rank_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → Module.Finite Γ(Y.X, U.1) (balanced H.bar A) ∧ Module.Projective Γ(Y.X, U.1) (balanced H.bar A) ∧ ∀ m : Ideal Γ(Y.X, U.1), m.IsMaximal → Module.finrank (Γ(Y.X, U.1) ⧸ m) ((Γ(Y.X, U.1) ⧸ m) ⊗[Γ(Y.X, U.1)] (balanced H.bar A)) = Dw.dim := by
  first | exact @GlobalTheory.BalProj.balanced_finite_projective_rank | exact GlobalTheory.BalProj.balanced_finite_projective_rank | (intros; apply GlobalTheory.BalProj.balanced_finite_projective_rank <;> assumption)
end

