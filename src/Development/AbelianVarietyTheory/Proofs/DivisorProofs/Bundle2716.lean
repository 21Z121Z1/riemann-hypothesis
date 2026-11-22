import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2609
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRunModel
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Build

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem exists_runModel (p : PtAt ex Csz) (hm : More p) (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r) (ho : OwnPin r)
    (i : Fin D.R.m) : ∃ (C : Type) (_ : Finite C) (_ : MulAction p.P.Gp C) (M : TwoLevels D.host.E D.R.r p.P.Gp C)
      (ka : Wt M.Ψ D.R.r), RunModel p r h i M ka := by
  classical
  obtain ⟨v⟩ := nonempty_place D
  have hne : Nonempty (uAt r v i).Comp := GlobalTheory.ModelLatticeCheck.comp_nonempty _ _ _
  have hcom := GlobalTheory.T.uniformisation_components_share_cmData p hm r h ho i v
  have hchi := GlobalTheory.T.uniformisation_character_trivial_arithmeticGroup p hm r h ho i v
  have hcong := GlobalTheory.T.lattice_preserved_by_component_stabilizer p hm r h ho i v
  obtain ⟨act, tr, h1, hmul, hmt, hconj, hcoc, hfaith, ⟨a, ha⟩, hd2⟩ := GlobalTheory.T.exists_levelGroup_transport_uniformisation_components p hm r h ho i v
  choose Xx hXd hXL using exists_dataX_latP p r h i v
  have hΓ : ∀ c, (Xx c).Γ = ((uAt r v i).X c).Γ := fun c => congrArg Data.Γ (hXd c)
  have hΛ : ∀ c, (Xx c).Λ = ((uAt r v i).X c).Λ := fun c => congrArg Data.Λ (hXd c)
  let k0 : (uAt r v i).Comp := hne.some
  letI inst : MulAction p.P.Gp (uAt r v i).Comp := { smul := act, one_smul := h1, mul_smul := hmul }
  let M : TwoLevels D.host.E D.R.r p.P.Gp (uAt r v i).Comp :=
    { Ψ := ((uAt r v i).X k0).Ψ
      Gm := ((uAt r v i).X k0).Gm
      p0 := ((uAt r v i).X k0).p0
      ξ0 := ((uAt r v i).X k0).ξ0
      comp := Xx
      comp_Ψ := fun c => (congrArg Data.Ψ (hXd c)).trans (hcom c k0).1
      comp_Gm := fun c => (congrArg Data.Gm (hXd c)).trans (hcom c k0).2.2.1
      comp_basePoint := fun c => (congrArg Data.p0 (hXd c)).trans (hcom c k0).2.1
      comp_ξ0 := fun c => (congrArg Data.ξ0 (hXd c)).trans (hcom c k0).2.2.2
      χ_one := fun c => chi_one_of_toData (Xx c) _ (hXd c) (hchi c)
      Γ_L' := fun c γ hγ w => by
        rw [hXL c]
        rw [hΓ c] at hγ
        exact mem_localLattice_iff_mulVec D _ (((uAt r v i).X c).Γ_stab γ hγ).2 w
      tr := tr
      tr_herm := fun u c w w' => by
        have e := (hmt u c).iso w w'
        rw [(hcom (act u c) k0).2.2.1, (hcom c k0).2.2.1] at e
        exact e
      tr_Λ := fun u c w => by
        rw [hΛ c, hΛ (u • c)]
        exact (hmt u c).lat w
      tr_L' := fun u c w => by
        rw [hXL c, hXL (u • c)]
        exact mem_localLattice_iff_mulVec D _ (hmt u c).lat w
      tr_conj := fun u c γ => by
        rw [hΓ c, hΓ (u • c)]
        exact hconj u c γ
      tr_mul := fun u u' c => by
        rw [hΓ]
        exact hcoc u u' c
      tr_faithful := fun u c hu ht => hfaith u c hu (by rw [hΓ c] at ht; exact ht) }
  let ka : Wt M.Ψ D.R.r := fun τ j => laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k0 τ j
  refine ⟨(uAt r v i).Comp, inferInstance, inst, M, ka, v, Equiv.refl _, fun c => hXd c, ?_, ⟨a, ?_⟩, ?_, ?_⟩
  · intro c τ h1 h2 j
    show laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) k0 ⟨τ, h1⟩ j = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) c ⟨τ, h2⟩ j
    unfold laR laU
    rw [(hcom c k0).2.1]
  · intro F g c x hx h1 h2
    have hx' : castFrame h1 x ∈ ((uAt r v i).X c).dom := by
      show castFrame h1 x ∈ GG ((uAt r v i).X c).Ψ ((uAt r v i).X c).Gm ((uAt r v i).X c).p0
      rw [(hcom c k0).2.2.1, (hcom c k0).2.1]
      exact fun τ => hx ⟨τ.1, by rw [h1]; exact τ.2⟩
    have e := ha F g c (castFrame h1 x) hx' (h1.symm.trans h2)
    exact e
  · intro c γ hγ w hw
    rw [hXL c] at hw ⊢
    rw [hΓ c] at hγ
    exact hcong c γ hγ w hw
  · exact hd2 (fun c => (Xx c).L') hXL

end Build

end GlobalTheory.ShareOn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfAppellHumbertThetaFunctionStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_of_appellHumbert_thetaFunction : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ := by
  first | exact @GlobalTheory.ThetaGAGA.exists_isFnPow | exact GlobalTheory.ThetaGAGA.exists_isFnPow | (intros; apply GlobalTheory.ThetaGAGA.exists_isFnPow <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistedLineBundleNonzeroClosedFibre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.TwistGen

theorem whisker_eq_twistLB {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (q : ℕ)
    {T T' : Over S} (ρ : T' ⟶ T) (c : T ⟶ A) :
    LB.LinComb L (K := Fin 2) (fun k => (ρ ▷ A).left ≫ ![(snd T A).left, (translPt A c).left] k)
      ![(q : ℤ) - 1, 1] = twistLB A L q (ρ ≫ c) := by
  unfold twistLB
  congr 1
  funext k
  fin_cases k
  · show (ρ ▷ A).left ≫ (snd T A).left = (snd T' A).left
    rw [← Over.comp_left, whiskerRight_snd]
  · show (ρ ▷ A).left ≫ (translPt A c).left = (translPt A (ρ ≫ c)).left
    rw [← Over.comp_left]
    congr 1
    simp [translPt, comp_lift_assoc]

theorem mem_of_isPullSecLC {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Y' ⟶ Y) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L (fun k => h ≫ φ k) ε))
    (hs : IsPullSecLC L φ ε h s s') (y : Y') (hy : y ∈ nonzeroLocus s') : h y ∈ nonzeroLocus s := by
  obtain ⟨(j : K → L.ι), hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  rw [hs j] at hj
  erw [Scheme.basicOpen_res] at hj
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, (Scheme.preimage_basicOpen h (s.f j)).ge hj.2⟩

theorem transfer {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (α : D.X)
    (s : LB.Sec (twistLB D.P.A D.P.L 2 (D.c α)))
    (z : (𝟙_ (Over (Spec (CommRingCat.of R))) ⊗ D.P.A).left) (hz : z ∈ nonzeroLocus s) :
    ∃ σ : D.SecB 2 α, (snd _ D.P.A).left z ∈ nonzeroLocus σ := by
  let T := 𝟙_ (Over (Spec (CommRingCat.of R)))
  let A := D.P.A
  let iota : A.left ⟶ (T ⊗ A).left := (lift (toUnit A) (𝟙 A)).left
  have hsec : snd T A ≫ lift (toUnit A) (𝟙 A) = 𝟙 (T ⊗ A) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact (toUnit_unique _ _)
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  have hiota : iota ((snd T A).left z) = z := by
    have e : (snd T A).left ≫ iota = 𝟙 _ := by rw [← Over.comp_left, hsec]; rfl
    have e' := congrArg (fun f => f.base z) e
    exact e'
  obtain ⟨u₀, hu₀⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2)
    (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) ![-1, 1]
  let u := LB.pullGen D.P.L _ _ u₀ (toUnit A).left
  have hu : u.IsGen := DVR.pullGen_isGen_of_isGen _ _ u₀ hu₀ _
  let s₁ := pullMulSec s iota u hu
  have hF : FormEq (Sum.elim (fun k => iota ≫ ![(snd T A).left, (translPt A (D.c α)).left] k)
      (fun k => (toUnit A).left ≫ (![(D.c α).left, η[A].left] : Fin 2 → (Spec (CommRingCat.of R) ⟶ A.left)) k))
      (Sum.elim ![((2 : ℕ) : ℤ) - 1, 1] ![-1, 1]) (D.famφB α) (DegPre.famε 2) := by
    have e₁ : iota ≫ (snd T A).left = 𝟙 _ := by
      rw [← Over.comp_left, lift_snd]; rfl
    have e₂ : iota ≫ (translPt A (D.c α)).left = (padd A (𝟙 A) (toUnit A ≫ D.c α)).left := by
      rw [← Over.comp_left]
      congr 1
      show lift (toUnit A) (𝟙 A) ≫ ((fst T A ≫ D.c α) * snd T A) = 𝟙 A * (toUnit A ≫ D.c α)
      rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift, lift_snd, ← Category.assoc, lift_fst]
      show (toUnit A ≫ D.c α) * 𝟙 A = 𝟙 A * (toUnit A ≫ D.c α)
      exact mul_comm _ _
    intro U _ hh
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_four, Sum.elim_inl, Sum.elim_inr,
      DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, e₁, e₂]
    simp only [_root_.mul_assoc]; rfl
  obtain ⟨σ, hσ⟩ := exists_sec D.P.isLB hF s₁
  refine ⟨σ, ?_⟩
  set xx := (snd T A).left z
  choose J hJ using fun χ : A.left ⟶ A.left => exists_chart D.P.isLB (χ xx)
  obtain ⟨(k : Fin 2 → D.P.L.ι), hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
  have hv : IsUnit (sval s (𝟙 A.left ≫ iota) xx J) := by
    refine H1.SectionArithmetic.isUnit_sval s (𝟙 A.left ≫ iota) xx hJ k ?_
    rw [Category.id_comp, hiota]; exact hk
  have hval : IsUnit (sval σ (𝟙 A.left) xx J) := by
    rw [hσ _ _ xx J hJ, sval_pullMulSec s iota u hu (𝟙 A.left) xx hJ]
    exact hv.mul (Units.isUnit _)
  have hm := (Good.mem hJ (D.famφB α) (𝟙 A.left))
  rw [sval] at hval
  erw [gs_eq (𝟙 A.left) xx _ hm] at hval
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun k => J (𝟙 A.left ≫ D.famφB α k), ?_⟩
  exact (A.left.mem_basicOpen _ xx hm).2 hval

theorem exists_sec_nonzeroLocus_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R],
    IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (D : DegPre R) (α : D.X) (x : D.P.A.left),
    D.P.A.hom x = IsLocalRing.closedPoint R → ∃ σ : D.SecB 2 α, x ∈ nonzeroLocus σ := by
  intro R _ _ _ _ _ D α x hx
  let S := Spec (CommRingCat.of R)
  let tk : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶ S :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let T : Over S := 𝟙_ (Over S)
  let ρ : Over.mk (tk ≫ T.hom) ⟶ Over.mk T.hom := Over.homMk tk rfl
  obtain ⟨y, hy⟩ : ∃ y : (Over.mk (tk ≫ T.hom) ⊗ D.P.A).left, (snd _ D.P.A).left y = x := by
    obtain ⟨p⟩ : Nonempty (Spec (CommRingCat.of (IsLocalRing.ResidueField R))) := inferInstance
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := tk ≫ T.hom) (g := D.P.A.hom) p x (by
      rw [hx]; exact IsLocalRing.PrimeSpectrum.comap_residue R p)
    exact ⟨z, hz⟩
  have hg := GlobalTheory.T.exists_section_translateTensor_fibre_nonvanishing S D.P _ (tk ≫ T.hom) (ρ ≫ D.c α) y
  rw [← whisker_eq_twistLB] at hg
  obtain ⟨sb, hsb⟩ := hg
  obtain ⟨s, hs⟩ := (GlobalTheory.abelianSchemeLaws_all.2.secTwist S D.P 2 (by norm_num) R T.hom (D.c α)).2 sb
  have hz := mem_of_isPullSecLC D.P.L _ _ _ s sb hs y hsb
  obtain ⟨σ, hσ⟩ := transfer D α s _ hz
  refine ⟨σ, ?_⟩
  have e : (snd T D.P.A).left ((ρ ▷ D.P.A).left y) = x := by
    rw [← hy]
    have e' := congrArg (fun f => f.left.base y) (whiskerRight_snd ρ D.P.A)
    exact e'
  rwa [e] at hσ

end GlobalTheory.TwistGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsRestrictBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem presents_lbPow_toLB {X : Scheme.{0}} [IsIntegral X] (A : CartierDiv X) (l : ℕ) :
    Presents (l • A) (lbPow (toLB A) l) fun j => (j PUnit.unit).1.2 ^ l := by
  refine ⟨isLB_lbPow (isLB_toLB A) l, fun i j h => ?_, fun i x hx => ?_⟩
  · simp only [show (lbPow (toLB A) l).g i j = _ from lbPow_g _ l i j, Units.val_pow_eq_pow_val,
      val_res, map_pow, fnOf_resG, fnOf_toLB_g]
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (Units.ne_zero _))]
  · exact ((i PUnit.unit).2.2 x ((lbPow_U _ l i).le hx)).nsmul l

theorem secPull_add' {X Y : Scheme.{0}} {L : LB X} (s t : L.Sec) (f : Y ⟶ X) :
    GlobalTheory.secPull (s + t) f = GlobalTheory.secPull s f + GlobalTheory.secPull t f :=
  LB.f_injective (funext fun i => by
    simp only [GlobalTheory.secPull, GlobalTheory.chartSec_f, LB.add_f, map_add])

theorem secPull_smul' {X Y : Scheme.{0}} {L : LB X} (c : Γ(X, ⊤)) (s : L.Sec) (f : Y ⟶ X) :
    GlobalTheory.secPull (c • s) f = f.appTop c • GlobalTheory.secPull s f :=
  LB.f_injective (funext fun i => by
    simp only [GlobalTheory.secPull, GlobalTheory.chartSec_f, LB.smul_f, map_mul]
    congr 1
    change ((X.presheaf.map _ ≫ f.appLE _ _ _).hom c) = ((f.appTop ≫ Y.presheaf.map _).hom c)
    rw [Scheme.Hom.map_appLE]
    rfl)

theorem algX_top_eq {X : Scheme.{0}} (p : X ⟶ Sp ℂ) (a : ℂ) :
    algX p ⊤ a = p.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv a) := by
  simp only [algX, RingHom.comp_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem redι_closure_genericPoint {X : Scheme.{0}} (z : X)
    [IrreducibleSpace (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme] :
    redι (Closeds.closure ({z} : Set X)) (genericPoint _) = z := by
  have hcl : closure ({redι (Closeds.closure ({z} : Set X)) (genericPoint _)} : Set X) = closure {z} := by
    rw [← Set.image_singleton, (redι _).isClosedEmbedding.closure_image_eq,
      (genericPoint_spec _).def, Set.image_univ, range_redι]
    rfl
  exact (inseparable_iff_closure_eq.2 hcl).eq

end GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_sections_restrict_basis :
    ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p →
      ∀ (A : CartierDiv X) (z : X), IsAmpleLB (toLB A) → ∃ l₁ : ℕ, ∀ l, l₁ ≤ l →
        ∃ (r : ℕ) (f : Fin r → X.functionField), (∀ i, f i ∈ (l • A).sections) ∧
          r = (letI := algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p);
            lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X))))) ∧
          ∀ a : Fin r → ℂ, a ≠ 0 → (l • A).GeneratesAt z (∑ i, Cartier.constFn p (a i) * f i) := by
  intro X _ _ p hp A z hA
  haveI hYi : IsIntegral (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme :=
    isIntegral_red isIrreducible_singleton.closure
  obtain ⟨l₁, hl₁⟩ := eventually_atTop.1 (GlobalTheory.T.eventually_exists_lift_section_of_ample_pow_from_closed X p hp (toLB A) (Closeds.closure ({z} : Set X)) hA)
  refine ⟨l₁, fun l hl => ?_⟩
  letI : Algebra ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) :=
    algebraΓOfHom (redι (Closeds.closure ({z} : Set X)) ≫ p)
  letI : Module ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
    Module.compHom _ (algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤))
  haveI : IsScalarTower ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤)
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
    ⟨fun a g s => by
      show (algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) a * g) • s =
        algebraMap ℂ Γ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))).subscheme, ⊤) a • (g • s)
      rw [mul_smul]⟩
  have hP := presents_lbPow_toLB A l
  have hr : Module.finrank ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec =
      lbH0 ℂ ((toLB (l • A)).pull (redι (Closeds.closure ({z} : Set X)))) := by
    rw [← lineBundleGlobalSectionsDim_eq_finrank]
    exact lineBundleGlobalSectionsDim_congr_picardClass (pull_isLB hP.isLB _) (pull_isLB (isLB_toLB _) _)
      (by rw [cls_pull hP.isLB, cls_pull (isLB_toLB _), ← hP.toPic_eq, toPic_apply])
  obtain ⟨v, hv⟩ : ∃ v : Fin (Module.finrank ℂ
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec) →
      ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec, LinearIndependent ℂ v := by
    by_cases hf : Module.Finite ℂ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec
    · exact ⟨_, (Module.finBasis ℂ _).linearIndependent⟩
    · rw [Module.finrank_of_not_finite hf]
      exact ⟨Fin.elim0, linearIndependent_empty_type⟩
  choose s hs using fun i => hl₁ l hl (v i)
  refine ⟨_, fun i => hP.rat (s i), fun i => hP.rat_mem _, hr, fun a ha => ?_⟩
  have e₁ : ∑ i, Cartier.constFn p (a i) * hP.rat (s i) = hP.rat (∑ i, algX p ⊤ (a i) • s i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, Algebra.smul_def, CartierDiv.algebraMap_top]
    rfl
  have e₂ : GlobalTheory.secPull (∑ i, algX p ⊤ (a i) • s i) (redι (Closeds.closure ({z} : Set X))) = ∑ i, a i • v i := by
    let F : (lbPow (toLB A) l).Sec →+ ((lbPow (toLB A) l).pull (redι (Closeds.closure ({z} : Set X)))).Sec :=
      { toFun := fun t => GlobalTheory.secPull t _
        map_zero' := by
          have := secPull_smul' (0 : Γ(X, ⊤)) (0 : (lbPow (toLB A) l).Sec) (redι (Closeds.closure ({z} : Set X)))
          rwa [zero_smul, map_zero, zero_smul] at this
        map_add' := fun t t' => secPull_add' t t' _ }
    change F _ = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change GlobalTheory.secPull _ _ = _
    rw [secPull_smul', hs i, algX_top_eq]
    rfl
  have hne : ∑ i, a i • v i ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    exact hi (Fintype.linearIndependent_iff.1 hv a h0 i)
  rw [← e₂] at hne
  have hgen := (sec_ne_zero_iff _).1 hne
  rw [GlobalTheory.nonzeroLocus_secPull] at hgen
  have hgen' : redι (Closeds.closure ({z} : Set X)) (genericPoint _) ∈
      nonzeroLocus (∑ i, algX p ⊤ (a i) • s i) := hgen
  have key : ∀ y : X, y = redι (Closeds.closure ({z} : Set X)) (genericPoint _) →
      y ∈ nonzeroLocus (∑ i, algX p ⊤ (a i) • s i) := fun y hy => hy ▸ hgen'
  have hz := key z (redι_closure_genericPoint z).symm
  rw [e₁]
  exact (hP.generatesAt_rat_iff _).2 hz

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearCochainOfDegreeOneObstructionZerStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semilinear_cochain_of_degreeOneObstruction_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), (∀ w, L.IsOb1 L' n l α w 0) → ∃ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) ∧ (∀ (r : R) w, u (π r • w) = r • u w) ∧ (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T) := by
  first | exact @GlobalTheory.Obs.exists_cochain_of_isOb1_zero | exact GlobalTheory.Obs.exists_cochain_of_isOb1_zero | (intros; apply GlobalTheory.Obs.exists_cochain_of_isOb1_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectOfSymplecticLevelPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegelLevelPull

theorem exists_siegPre_of_points : ∀ (n : ℕ) (hn : 3 ≤ n) (V V₁ : Type) [CommRing V] [CommRing V₁] [IsLocalRing V₁] [IsNoetherianRing V₁] (f₁ : V →+* V₁) (b : cycAway n →+* V) (PB : PolAV (Sp V)) (lev : (Fin PB.g ⊕ Fin PB.g → ℤ) → (Over.mk (spMap f₁) ⟶ PB.A)) (r : ℕ) (d₀ : Fin r → (Over.mk (spMap f₁) ⟶ PB.A)) (c : Fin r → (𝟙_ (Over (Sp V)) ⟶ PB.A)), (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ n = 1) → (∀ x y, Out.WeilIs PB.A PB.L n (lev x) (lev y) (unitOn (Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit ^ omegaStd x y))) → (∀ i, d₀ i ^ n = toUnit _ ≫ c i) → ∃ (s : SiegPre PB.g n (zetaAway n) (spMap (f₁.comp b))) (β₁ : s.A.left ⟶ PB.A.left) (β₁₂ : (G2 s.A).left ⟶ (G2 PB.A).left) (d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A)), s.Principal ∧ IsGrpPullback s.A PB.A (spMap f₁) β₁ ∧ IsSquare β₁ β₁₂ ∧ LBIso s.P ((abelian₂ PB.A PB.L).pull β₁₂) ∧ ∀ i, (d i ^ n).left ≫ β₁ = spMap f₁ ≫ (c i).left := by
  intro n hn V V₁ _ _ _ _ f₁ b PB lev r d₀ c hadd htors hweil hd
  have hn0 : n ≠ 0 := by omega
  haveI := PB.isAb.comm
  let P₁ : PolAV (Sp V₁) := GlobalTheory.StrictPull.polPull PB (spMap f₁)
  haveI : IsCommMonObj P₁.A := P₁.isAb.comm
  have hpb : IsGrpPullback P₁.A PB.A (spMap f₁) (pullback.fst PB.A.hom (spMap f₁)) :=
    isGrpPullback_pullback PB.A (spMap f₁)
  obtain ⟨κ, hκ⟩ := GlobalTheory.UnifPoint.exists_pointEquiv hpb
  have hk : ∀ x, (κ.symm x).left ≫ pullback.fst PB.A.hom (spMap f₁) = x.left := fun x => by
    rw [← hκ, κ.apply_symm_apply]
  let ze : V₁ˣ := Units.map (f₁.comp b).toMonoidHom (GlobalTheory.LowChart.isUnit_zetaAway n hn).unit
  let lev₁ : (Fin PB.g ⊕ Fin PB.g → ℤ) → (𝟙_ (Over (Sp V₁)) ⟶ P₁.A) := fun x => κ.symm (lev x)
  have hL₁ : LBIso P₁.L (PB.L.pull (pullback.fst PB.A.hom (spMap f₁))) :=
    GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB PB.isLB _)
  have hw : ∀ x y, WeilIs P₁.A P₁.L n (lev₁ x) (lev₁ y) (unitOn (ze ^ omegaStd x y)) := fun x y =>
    (GlobalTheory.weilIs_grpPullback_of_comm _ _ PB.A P₁.A (spMap f₁) _ PB.L P₁.L PB.isLB P₁.isLB hpb hL₁ _ n _ _
      (pushPt hpb.1.w (lev₁ x)) (pushPt hpb.1.w (lev₁ y)) _ rfl rfl).2
      (GlobalTheory.UnifPoint.weilIs_congr (Category.id_comp _).symm (hk _).symm (hk _).symm (hweil x y))
  have hadd₁ : ∀ x y, lev₁ (x + y) = lev₁ x * lev₁ y := fun x y => by
    simp only [lev₁, hadd, map_mul]
  have htors₁ : ∀ x, lev₁ x ^ n = 1 := fun x => by
    simp only [lev₁, ← map_pow, htors, map_one]
  have hu : IsUnit (n : V₁) := by simpa using (GlobalTheory.SiegelTor.isUnit_natCast hn0).map (f₁.comp b)
  have hze : (ze : V₁) = (f₁.comp b) (zetaAway n) := by simp [ze]
  have hprim : ∀ (k : Type) [Field k] (gk : V₁ →+* k), IsPrimitiveRoot (gk ze) n := fun k _ gk => by
    rw [hze]; exact GlobalTheory.SiegelTor.isPrimitiveRoot_map hn0 (gk.comp (f₁.comp b))
  haveI : IsMonHom (Iso.refl P₁.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  have hid : IsGrpPullback P₁.A P₁.A (spMap (RingHom.id V₁)) (𝟙 _) :=
    (isGrpPullback_of_iso (Iso.refl P₁.A)).congr (by simp [spMap]) rfl
  obtain ⟨s, ψ, hψ, hs, hsP⟩ := GlobalTheory.SiegelOverLocal.exists_siegPre V₁ V₁ P₁ (RingHom.id V₁) P₁ (𝟙 _) hid
    (GlobalTheory.lbIso_pull_id P₁.isLB).symm rfl (cycAway n) (f₁.comp b) PB.g n (zetaAway n) ze lev₁ rfl hu hze hprim
    hadd₁ htors₁ hw

  haveI := hψ
  have hLamB : (abelian₂ PB.A PB.L).IsLB := DVR.linComb_isLB _ PB.isLB _ _
  have hLam₁ : (abelian₂ P₁.A P₁.L).IsLB := DVR.linComb_isLB _ P₁.isLB _ _
  obtain ⟨β₂, hsq, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (spMap f₁) PB.A P₁.A _ hpb
  have e₁ : LBIso (abelian₂ P₁.A P₁.L) ((abelian₂ PB.A PB.L).pull (β₂ ≫ 𝟙 _)) :=
    hlam PB.L P₁.L _ (abelian₂ PB.A PB.L) (𝟙 _) PB.isLB P₁.isLB hLamB hL₁ (GlobalTheory.lbIso_pull_id hLamB).symm
  rw [Category.comp_id] at e₁
  let κ₂ := (lift (fst s.A s.A ≫ ψ.hom) (snd s.A s.A ≫ ψ.hom)).left
  have e₂ : LBIso ((abelian₂ P₁.A P₁.L).pull κ₂) ((abelian₂ PB.A PB.L).pull (κ₂ ≫ β₂)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl) (chartPullSame (abelian₂ PB.A PB.L) _ (fun _ => β₂) _ κ₂ fun _ => rfl) e₁
  let d : Fin r → (𝟙_ (Over (Sp V₁)) ⟶ s.A) := fun i => κ.symm (d₀ i) ≫ ψ.inv
  have hpow : ∀ (x : 𝟙_ (Over (Sp V₁)) ⟶ P₁.A) (m : ℕ), ((x ≫ ψ.inv) ^ m) ≫ ψ.hom = x ^ m := fun x m => by
    induction m with
    | zero => rw [pow_zero, pow_zero, MonObj.one_comp]
    | succ m ih => rw [pow_succ, MonObj.mul_comp, ih, Category.assoc, Iso.inv_hom_id, Category.comp_id, pow_succ]
  refine ⟨s, ψ.hom.left ≫ pullback.fst PB.A.hom (spMap f₁), κ₂ ≫ β₂, d, hs,
    ((isGrpPullback_of_iso ψ).comp hpb).congr (Category.id_comp _) rfl, ⟨?_, ?_⟩,
    LBIso.trans s.isLB (pull_isLB hLam₁ _) (pull_isLB hLamB _) hsP e₂, fun i => ?_⟩
  · rw [Category.assoc, hsq.1]
    have e : κ₂ ≫ (fst P₁.A P₁.A).left = (fst s.A s.A).left ≫ ψ.hom.left := by
      simp only [κ₂]; rw [← Over.comp_left, ← Over.comp_left, lift_fst]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst PB.A.hom (spMap f₁)) e).trans (Category.assoc _ _ _))
  · rw [Category.assoc, hsq.2]
    have e : κ₂ ≫ (snd P₁.A P₁.A).left = (snd s.A s.A).left ≫ ψ.hom.left := by
      simp only [κ₂]; rw [← Over.comp_left, ← Over.comp_left, lift_snd]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst PB.A.hom (spMap f₁)) e).trans (Category.assoc _ _ _))
  · have h1 : (d i ^ n).left ≫ ψ.hom.left = (κ.symm (d₀ i) ^ n).left := by
      rw [← Over.comp_left, hpow]
    have hT : (toUnit (Over.mk (spMap f₁))).left = spMap f₁ := by
      simpa using Over.w (toUnit (Over.mk (spMap f₁)))
    calc (d i ^ n).left ≫ ψ.hom.left ≫ pullback.fst PB.A.hom (spMap f₁)
        = ((d i ^ n).left ≫ ψ.hom.left) ≫ pullback.fst PB.A.hom (spMap f₁) := (Category.assoc _ _ _).symm
      _ = (κ.symm (d₀ i) ^ n).left ≫ pullback.fst PB.A.hom (spMap f₁) := by rw [h1]
      _ = (d₀ i ^ n).left := by rw [← map_pow, hk]
      _ = spMap f₁ ≫ (c i).left := by rw [hd, Over.comp_left, hT]

end GlobalTheory.SiegelLevelPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothAwayOfQuotientPowEquivStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_away_of_quotient_pow_equiv' : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (O C : Type) [CommRing O] [Algebra R O] [CommRing C] [Algebra R C], Algebra.Smooth R O → Algebra.FiniteType R C → (∀ e : ℕ, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)))) → ∀ q : Ideal C, q.IsPrime → q.comap (algebraMap R C) = maximalIdeal R → ∃ g : C, g ∉ q ∧ Algebra.Smooth R (Localization.Away g) := by
  first | exact @GlobalTheory.SmoothAdic.exists_smooth_away_of_quotient_pow_equiv | exact GlobalTheory.SmoothAdic.exists_smooth_away_of_quotient_pow_equiv | (intros; apply GlobalTheory.SmoothAdic.exists_smooth_away_of_quotient_pow_equiv <;> assumption)
end

