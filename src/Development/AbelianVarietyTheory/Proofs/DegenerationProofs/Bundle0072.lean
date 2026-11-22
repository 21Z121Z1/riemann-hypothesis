import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGrpPullbackThick
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0043
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalPointLiftingResiduePointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.exists_classical_point_lifting_residue_point : ∀ (X : Scheme.{0}) [IsIntegral X] (π : X ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] (U : X.Opens), (U : Set X).Nonempty → ∀ (p : ℕ) [Fact p.Prime], (∀ x : Sp (kb p) ⟶ X, ∃ b : Sp (OO p) ⟶ X, rPt p ≫ b = x ∧ Set.range (gPt p ≫ b) ⊆ U) ∧ (∀ (x : Sp (kb p) ⟶ X) (s : Sp (kb p)), IsClosed ({x s} : Set X)) := by
  first | exact @GlobalTheory.exists_integral_point_lifting_residue_point | exact GlobalTheory.exists_integral_point_lifting_residue_point | (intros; apply GlobalTheory.exists_integral_point_lifting_residue_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCmpOfIsPullDeg
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.PreBaseChange

theorem exists_cmp_of_isPullDeg (hG : GlobalFnsSt) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    {I : Ideal R} {I' : Ideal V} {φ : R →+* V} (hI : I.map φ ≤ I') {D : DegPre R} {D₁ D' : DegPre V}
    (hD : IsPullDeg φ D D₁) {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing V))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
    [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left)
    (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F))
    (hw : IsCPMap U'.P U.P (spMap φ) F pb.1.w wL) :
    ∃ (U₁ : PreU I' D₁ A' G') (C : Cmp φ U U₁ F), U₁.P = U'.P ∧ HEq C.wL wL := by
  obtain ⟨bc, hbc, rfl⟩ := grpPullback_iso pb (isGrpPullback_pullback G (specOf φ))
  choose h q' i' hh hq' using fun e => gtCoord_baseChange_maps R V φ D D₁ hD I I' hI G G' bc hbc e (U.gt e)
  choose g _ hg using fun e => exists_gtCoord_pull hG R V φ D D₁ hD I I' hI G G' bc hbc e (U.gt e) (h e) (q' e)
    (i' e) (hh e) (hq' e)
  have hc := fun e => gtCoord_compat_of_pull R V φ D D₁ hD I I' G G' _ e (U.gt e) (U.gt (e + 1)) (g e) (g (e + 1))
    (h e) (h (e + 1)) (hh e) (hh (e + 1)) (hg e) (hg (e + 1)) (U.gt_q e) (U.gt_t e)
  choose w w_gen sq using fun e => FourthSide.exists_fourth_side _ _ _ _ _ _ D.P.L D₁.P.L U.P.L.L U'.P.L.L D.P.isLB
    D₁.P.isLB U.P.L.isLB U'.P.L.isLB _ _ (U.gt e).pG.left (g e).pG.left (fstG I e G).left (fstG I' e G').left (h e)
    (hg e).1 (hh e) hD.w wL (U.w e) hD.w_gen hw.gen (U.w_gen e)
  have pt : ∀ {Z X Y : Scheme.{0}} {a b : X ⟶ Y} (_ : a = b) (x : Z ⟶ X) (z : Z) {W : Y.Opens},
      a (x z) ∈ W → b (x z) ∈ W := fun e _ _ _ k => e ▸ k
  have compat : ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj V I' e G').left) (z : Z) (j : D₁.P.L.ι)
      (k : U'.P.L.L.ι), (g e).pG.left (x z) ∈ D₁.P.L.U j → (fstG I' e G').left (x z) ∈ U'.P.L.L.U k →
      gw (w (e + 1)) (x ≫ thickMap V I' e G') z j (fun _ => k) = gw (w e) x z j (fun _ => k) := by
    intro e Z x z j k hj hk
    have := Cmp.mono_fstG I (e + 1) G
    have t := LevelCompat.thickMap_fstG I e G
    have t' := LevelCompat.thickMap_fstG I' e G'
    have hm : thickMap V I' e G' ≫ h (e + 1) = h e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, hh (e + 1), ← Category.assoc, t', Category.assoc, t,
        hh e]
    obtain ⟨jM, hM⟩ := exists_chart D.P.isLB
      ((hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ((g e).pG.left (x z)))
    obtain ⟨jL, hL⟩ := exists_chart U.P.L.isLB
      ((bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ((fstG I' e G').left (x z)))
    have a₀ := sq e Z x z jM j jL k hM hj hL hk
    have a₁ := sq (e + 1) Z (x ≫ thickMap V I' e G') z jM j jL k
      (pt (congrArg (· ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (hc e).1).symm x z hM)
      (pt (hc e).1.symm x z hj)
      (pt (congrArg (· ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ)) t').symm x z hL) (pt t'.symm x z hk)
    have b := U.w_compat e Z (x ≫ h e) z jM jL (pt (hg e).1 x z hM) (pt (hh e).symm x z hL)
    rw [Category.assoc x, Category.assoc x, Category.assoc x, (hc e).1, t', hm, ← Category.assoc x (h e), b] at a₁
    exact mul_left_cancel (a₁.trans a₀.symm)
  refine ⟨⟨U'.semi, U'.gen, U'.gen_hom, U'.P, U'.wA, U'.wA_gen, g, fun e => (hc e).1, fun e => (hc e).2, w, w_gen,
      fun e => GlobalTheory.T.fourthSide_respects_rig_symmetry_cube hG R V I I' φ hI D D₁ A G G' U U'.P _ _ wL hw _ _ hD.w (GlobalTheory.T.isCubicalBundleMap_of_pulled_back_degeneration hG R V φ D D₁ hD) e
        (g e) (h e) (hh e) (hg e).1 (w e) (sq e), compat⟩,
    ⟨pb, wL, hw, _, pull_grp hD, hD.w, hD.w_gen, hD.xe, hD.c_pr, fun e Z x' x hx => ?_, hI⟩, rfl, HEq.rfl⟩
  have := Cmp.mono_fstG I e G
  obtain rfl : x = x' ≫ h e := (cancel_mono (fstG I e G).left).1 (hx.trans (by rw [Category.assoc, hh e]))
  refine ⟨(congrArg (x' ≫ ·) (hg e).1).trans (Category.assoc _ _ _).symm,
    fun z J J' hJ hJ' => ⟨fun χ => ?_, fun k k' hk hk' => ?_⟩⟩
  · refine (CubTransport.val_pmaps ((hg e).2 χ).1 ((hg e).2 χ).2 x' hJ hJ').trans
      ((mul_comm _ _).trans (congrArg _ (Finset.prod_congr rfl fun k _ => ?_)))
    rw [Category.assoc]
  · exact sq e Z x' z _ _ k k' (pt (hg e).1.symm x' z (hJ ((x' ≫ h e) ≫ (U.gt e).pG.left)))
      (hJ' (x' ≫ (g e).pG.left)) (pt (hh e) x' z hk) hk'

theorem exists_cmp_pull : Laws → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (pb : IsGrpPullback G' G (spMap φ) F) (wL : LB.Iso U'.P.L.L (U.P.L.L.pull F)), IsCPMap U'.P U.P (spMap φ) F pb.1.w wL → ∃ (D₁ : DegPre V) (U₁ : PreU I' D₁ A' G') (C : Cmp φ U U₁ F), U₁.P = U'.P ∧ HEq C.wL wL := by
  intro hL R V _ _ _ _ _ I I' φ hI D D' A A' G _ _ G' _ _ U U' F pb wL hw
  obtain ⟨ψ, h, hW⟩ := GlobalTheory.T.exists_psi_generating_on_whole_spectrum R D
  obtain ⟨D₁, hD, -⟩ := DegPull.exists_isPullDeg hL.polBaseChange R V φ (setPsi D ψ h) ⊤ hW trivial
  obtain ⟨U₁, C, h₁, h₂⟩ := exists_cmp_of_isPullDeg hL.globalFns hI hD (U.setPsi ψ h) U' F pb wL hw
  exact ⟨D₁, U₁, ⟨C.pb, C.wL, C.wL_map, C.β, C.pbB, C.v, C.v_gen, C.xe, C.c_pr, C.lev, C.map_le⟩, h₁, h₂⟩

end GlobalTheory.LN.PreBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationPreDataOverSubfield
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull

theorem exists_pre_below : Laws → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K) (P₀ : PolAV (Sp K₀)) (Φ : D.P.A.left ⟶ P₀.A.left), IsGrpPullback D.P.A P₀.A (spMap i) Φ → LBIso D.P.L (P₀.L.pull Φ) → ∀ c₀ : D.X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) → (∀ y, (D.c y).left ≫ Φ = spMap i ≫ (c₀ y).left) → ∃ (D₀ : DegPre K₀) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (hD : IsPullDeg i D₀ (TauTwist.withPsi D ψ hψ)), D₀.P = P₀ ∧ HEq (PsiEvenPull.proj hD) Φ := by
  intro hL K₀ K _ _ i D P₀ Φ gp ⟨w₀, hw₀⟩ c₀ cadd hc
  obtain ⟨rig, hrig⟩ := P₀.rigid
  obtain ⟨cub⟩ := (hL.cube _ P₀ ⟨P₀.L, rig, P₀.isLB, hrig⟩ rfl).1
  obtain ⟨sym, hsym, hsr⟩ := SelfUnif.exists_sym P₀
  choose psi hpsi using fun χ : D.X => DVR.exists_gen_of_local (V := FractionRing K₀) P₀.L P₀.isLB (K := PUnit)
    (fun _ => ptK (c₀ χ)) (fun _ => -1)
  let D₀ : DegPre K₀ :=
    { P := P₀, rig := rig, rig_gen := hrig, cub := cub, sym := sym, sym_gen := hsym, sym_rig := hsr, X := D.X,
      c := c₀, c_add := cadd, psi := psi, psi_gen := hpsi }
  obtain ⟨w, hw, hr⟩ := TripleMap.exists_rigidified P₀.isLB D.P.isLB w₀ ((isGen_iff w₀).1 hw₀) (eSec P₀.A)
    (eSec D.P.A) D.P.A.hom (Over.w η[D.P.A]) (spMap i) (cubeMapOf gp).e_comm rig hrig D.rig D.rig_gen
  have hx : ∀ χ, D.xK χ ≫ Φ = genMap i.injective ≫ ptK (c₀ χ) := fun χ => by
    show (jK K ≫ (D.c χ).left) ≫ Φ = genMap i.injective ≫ jK K₀ ≫ (c₀ χ).left
    rw [Category.assoc, hc, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ _) ((Category.id_comp _).symm.trans (fracMap_sq i.injective))
  choose ψ hψ vψ using fun χ : D.X => exists_down_om ((isGen_iff w).2 hw) P₀.isLB D.P.isLB (K := PUnit)
    (φ' := fun _ => D.xK χ) (genMap i.injective) (fun _ => hx χ) (psi χ) (hpsi χ)
  obtain ⟨hD, e, -, -⟩ := exists_isPullDeg_of_val i D₀ (TauTwist.withPsi D ψ hψ) gp w hw hr (AddEquiv.refl _) hc
    (fun x z J J' hJ hJ' => by
      have v := vψ x _ (𝟙 _) z J J' hJ hJ'
      rw [Fintype.prod_unique, zpow_neg_one, Category.id_comp, Category.id_comp] at v
      exact v)
  exact ⟨D₀, ψ, hψ, hD, rfl, heq_of_eq e⟩

end GlobalTheory.FieldPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDenseClosedPointsChartSplitting
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.DenseSplit

theorem exists_ringHom_kb (F : Type) [Field F] [Finite F] :
    ∃ (p : ℕ) (_ : Fact p.Prime), Nonempty (F →+* kb p) := by
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have : CharP (kb p) p := (CharP.charP_iff_prime_eq_zero hpp.out).mpr
    (GlobalTheory.natCast_self_residueField_padicAlgCl_eq_zero p)
  have := (kb_isAlgClosed_and_conj p).1
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) (kb p) := ZMod.algebra _ p
  have : Module.Finite (ZMod p) F := Module.Finite.of_finite
  exact ⟨p, hpp, ⟨(IsAlgClosed.lift (R := ZMod p) (S := F) (M := kb p)).toRingHom⟩⟩

theorem isNoetherianRing_of_lft (R : Type) [CommRing R] (π : Sp R ⟶ Sp ℤ) [LocallyOfFiniteType π] :
    IsNoetherianRing R := by
  have : IsLocallyNoetherian (Sp R) := LocallyOfFiniteType.isLocallyNoetherian π
  exact isLocallyNoetherian_Spec.mp this

theorem exists_dense_splitOn : ∀ (C : Core) (L : C.Law), C.HasTests → C.HasCharts → letI := L.grp; letI := L.comm; ∀ z : C.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsNoetherianRing R) (t : Sp R ⟶ C.Z) (_ : IsImmersion t), t (⊥ : PrimeSpectrum R) = z ∧ ∃ (Ch : Charts ((Over.pullback t).obj C.GG).left) (d : ℕ) (c : Fin d → Ch.Cl) (Sg : Set (Sp R)), Dense Sg ∧ Ch.SplitOn c Sg ∧ ∀ x ∈ Sg, IsClosed ({t x} : Set C.Z) := by
  intro C L hT hC z
  letI := L.grp; letI := L.comm
  obtain ⟨R, _, _, t, _, htz, Ch, hCh⟩ := hC z
  have := C.lft
  have := C.flat
  obtain ⟨-, hfin, -, -, hdense⟩ := GlobalTheory.jacobson_closedPoints_tools_int (Sp R) (t ≫ C.π)
  refine ⟨R, inferInstance, inferInstance, isNoetherianRing_of_lft R (t ≫ C.π), t, inferInstance, htz, Ch, ?_⟩
  let κ := Σ d : Fin (C.g + 1), (Fin d → Ch.Cl)
  let Sg : κ → Set (Sp R) := fun k => {x | Charts.SplitOn (G := (Over.pullback t).obj C.GG) Ch k.2 {x} ∧
    IsClosed ({t x} : Set C.Z)}
  obtain ⟨k, hk⟩ := hdense κ Sg inferInstance (by
    intro x hx
    have := hfin x hx
    obtain ⟨p, hp, ⟨r⟩⟩ := exists_ringHom_kb ((Sp R).residueField x)
    let xb : Sp (kb p) ⟶ Sp R := Spec.map (CommRingCat.ofHom r) ≫ (Sp R).fromSpecResidueField x
    have hxb : ∀ s, xb s = x := fun s => by
      have : xb s ∈ Set.range ((Sp R).fromSpecResidueField x) := ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rwa [Scheme.range_fromSpecResidueField] at this
    have hrange : Set.range xb = {x} := by
      ext w
      exact ⟨fun ⟨s, hs⟩ => hs ▸ hxb s, fun hw => ⟨IsLocalRing.closedPoint (kb p), (hxb _).trans hw.symm⟩⟩
    obtain ⟨hlift, hcl⟩ := GlobalTheory.exists_integral_point_lifting_residue_point C.Z C.π C.U C.ne p
    obtain ⟨y, hy, hyU⟩ := hlift (xb ≫ t)
    obtain ⟨τ⟩ := hT p y hyU
    have e : (rPt p ≫ spMap τ.j) ≫ τ.y₀ = xb ≫ t := by rw [Category.assoc, τ.fac, hy]
    have g1 : IsGrpPullback ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) C.GG (xb ≫ t)
        (pullback.fst τ.H.hom (rPt p ≫ spMap τ.j) ≫ τ.f) :=
      ((isGrpPullback_pullback _ _).comp (L.test p y τ)).congr e rfl
    have g2 : IsGrpPullback ((Over.pullback t).obj C.GG) C.GG t (pullback.fst C.GG.hom t) :=
      isGrpPullback_pullback _ _
    have g3 : IsGrpPullback ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)) ((Over.pullback t).obj C.GG) xb
        (pullback.fst ((Over.pullback t).obj C.GG).hom xb) :=
      isGrpPullback_pullback _ _
    let h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom t :=
      pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _ ≫ xb) (g1.1.w.trans (Category.assoc _ _ _).symm)
    have h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
    have h2 : h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ xb := pullback.lift_snd _ _ _
    have g4 : IsGrpPullback ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) ((Over.pullback t).obj C.GG) xb h :=
      g2.cancel (g1.congr rfl h1.symm) h2
    have ha : IsAffineHom h := MorphismProperty.of_isPullback (P := @IsAffineHom) g4.1.flip inferInstance
    have ha' : IsAffineHom (pullback.fst ((Over.pullback t).obj C.GG).hom xb) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom) g3.1.flip inferInstance
    obtain ⟨d, hd, c, hs⟩ := hCh p y τ xb hy.symm h h1 h2
    have w : pullback.fst ((Over.pullback t).obj C.GG).hom xb ≫ ((Over.pullback t).obj C.GG).hom =
      ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)).hom ≫ xb := g3.1.w
    let φ := g4.1.lift _ _ w
    have f1 : φ ≫ h = _ := g4.1.lift_fst _ _ w
    have f2 : φ ≫ _ = _ := g4.1.lift_snd _ _ w
    have g5 : IsGrpPullback ((Over.pullback xb).obj ((Over.pullback t).obj C.GG))
        ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) (𝟙 _) φ :=
      g4.cancel (g3.congr (Category.id_comp _).symm f1.symm) (f2.trans (Category.comp_id _).symm)
    have hφ : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) g5.1.flip inferInstance
    have hs' := @SplitPull.pull_pull_and_split_pull.2 (kb p) (kb p) _ _
      ((Over.pullback (rPt p ≫ spMap τ.j)).obj τ.H) _ ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)) _
      (𝟙 _) φ hφ g5 (Ch.pull h) d c hs
    refine ⟨⟨⟨d, Nat.lt_succ_of_le hd⟩, c⟩, ?_, ?_⟩
    · rintro _ rfl
      refine ⟨kb p, inferInstance, xb, ha', hrange, ?_⟩
      have key : ∀ (ψ : ((Over.pullback xb).obj ((Over.pullback t).obj C.GG)).left ⟶ pullback C.GG.hom t)
          [IsAffineHom ψ], φ ≫ h = ψ →
          Charts.Split (H := (Over.pullback xb).obj ((Over.pullback t).obj C.GG)) (Ch.pull ψ) c := by
        intro ψ _ hψ
        subst hψ
        exact hs'
      exact @key _ ha' f1
    · have := hcl (xb ≫ t) (IsLocalRing.closedPoint (kb p))
      exact ((Scheme.Hom.comp_apply xb t _).trans (congrArg t (hxb _))) ▸ this)
  exact ⟨k.1, k.2, Sg k, hk, fun x hx => hx.1 x rfl, fun x hx => hx.2⟩

end GlobalTheory.ZJ.DenseSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsEquivYEqZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

namespace GlobalTheory.ZH

theorem exists_equiv_y_eq_zero : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ) (pk : QkPt D.toPre F k) (z : D.toPre.X), pk.y = k • z → ∃ p' : QkPt D.toPre F k, p'.y = 0 ∧ QkPt.Equiv D.toPre F pk p' := by
  intro _ R _ _ _ I _ D F _ _ _ k pk z hz
  refine ⟨GlobalTheory.TorusExt.qkShift D.tau_bimult pk (-z), ?_, GlobalTheory.TorusExt.equiv_qkShift D.tau_bimult pk (-z)⟩
  show pk.y + k • (-z) = 0
  rw [hz, smul_neg, add_neg_cancel]

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsExpansionTermUnitClosedFibreStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_expansionTerm_unit_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → FibNZ (𝟙_ _ ⊗ G).hom σ → ∃ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (α : D.X), Good D.P.L z J ∧ T.hom z = IsLocalRing.closedPoint R ∧ (∀ b ∈ I, Geo.Tor.cst T.hom z b = 0) ∧ IsUnit (sval (f α) (lift (toUnit T) y).left z J) := by
  first | exact @GlobalTheory.PsiRing.exists_unit_term | exact GlobalTheory.PsiRing.exists_unit_term | (intros; apply GlobalTheory.PsiRing.exists_unit_term <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClassicalPointOfLargeTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_finset_closure_eq_top {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {X : Scheme.{0}}
    (s : X ⟶ Sp o) [LocallyOfFiniteType s] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ t : Finset Γ(X, W), Subring.closure (t : Set Γ(X, W)) = ⊤ := by
  have h1 : (s.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  have h3 : (algebraMap ℤ o).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h4 := (h1.comp h2).comp h3
  have h5 : (algebraMap ℤ Γ(X, W)).FiniteType := by
    convert h4 using 1
    exact RingHom.ext_int _ _
  obtain ⟨t, ht⟩ := (RingHom.finiteType_algebraMap.1 h5).out
  refine ⟨t, ?_⟩
  rw [Algebra.adjoin_int] at ht
  exact top_unique fun x _ => (show x ∈ subalgebraOfSubring (Subring.closure (t : Set Γ(X, W))) from
    ht ▸ Algebra.mem_top)

theorem exists_factor_of_closure {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* C) (j : B →+* C)
    (hj : Function.Injective j) {t : Set A} (ht : Subring.closure t = ⊤) (h : ∀ a ∈ t, φ a ∈ j.range) :
    ∃ ψ : A →+* B, j.comp ψ = φ := by
  have h1 : ∀ a, φ a ∈ j.range := fun a =>
    (Subring.closure_le.2 (show t ⊆ (j.range.comap φ : Subring A) from h)) (ht ▸ Subring.mem_top a)
  let e : B ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun _ _ hx => hj (congrArg Subtype.val hx), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict j.range h1), RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ a, h1 a⟩)

theorem preimage_comp_eq_val {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens)
    (hne : (U₀ : Set M.Z).Nonempty) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R)
    (hu : ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom)
    {K : Type} [Field K] (t : Sp K ⟶ U₀.toScheme) (a : R) :
    (Spec.preimage (t ≫ u₀)).hom a = M.val (t ≫ U₀.ι) a := by
  have hle : (⊤ : U₀.toScheme.Opens) ≤ U₀.ι ⁻¹ᵁ U₀ := fun x _ => x.2
  have hs : Function.Surjective (U₀.ι.appLE U₀ ⊤ hle).hom := by
    have : IsIso (U₀.ι.appLE U₀ ⊤ hle) := inferInstance
    exact (asIso (U₀.ι.appLE U₀ ⊤ hle)).commRingCatIsoToRingEquiv.surjective
  obtain ⟨f, hf⟩ := hs ((u₀.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  have key : ∀ (L : Type) [Field L] (x : Sp L ⟶ U₀.toScheme),
      (Spec.preimage (x ≫ u₀)).hom a = valF (x ≫ U₀.ι) U₀ f := by
    intro L _ x
    rw [preimage_apply, ← valR_appLE x u₀ (U := ⊤) (V := ⊤) le_top (le_preimage_top _), ← hf,
      valR_appLE x U₀.ι hle (le_preimage_top _)]
    rfl
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hne)
  have h1 := key Ω (IsOpenImmersion.lift U₀.ι M.pt hr)
  rw [hu _ (IsOpenImmersion.lift_fac _ _ _), IsOpenImmersion.lift_fac, Spec.preimage_map] at h1
  rw [key K t]
  refine (RatModel.val_eq ?_ h1.symm).symm
  rintro _ ⟨w, rfl⟩
  exact (t w).2

theorem exists_fac_of_large_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), Set.range (gPt p ≫ y) ⊆ U₀ → ∃ (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ ∀ u : ρ.UTest p y₀, (∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))) → Nonempty (Q.Fac y u) := by
  intro o Ω _ _ _ hA S ρ M U₀ EE hB Q p _ y hy
  have hO := hB.ov
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hy ⟨w, rfl⟩
  have hle : S.R ≤ M.O ((gPt p ≫ y) w) := hO.le.trans (RatModel.ringOn_le_O hw)
  let y₀ : S.R →+* PadicAlgCl p :=
    (RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
  have hn : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a =>
    RatModel.norm_val_le_one (y := y) rfl (x := algebraMap o Ω a) ((M.O _).algebraMap_mem a)
  have hat : S.At M y y₀ := fun _ => rfl
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y (le_preimage_top y)
  haveI := hA.ft
  haveI := M.lft
  obtain ⟨t, ht⟩ := exists_finset_closure_eq_top M.s hW
  refine ⟨y₀, t.image (fun f => (((valMap y W hyW).hom f : OO p) : PadicAlgCl p)), hn, fun u hu => ?_⟩
  have hj : Function.Injective u.j := fun a b h =>
    IsFractionRing.injective u.V (FractionRing u.V)
      ((algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (congrArg Subtype.val h))
  obtain ⟨ψ, hψ⟩ := exists_factor_of_closure (valMap y W hyW).hom u.j hj ht (by
    intro a ha
    obtain ⟨x, hx⟩ := hu _ (Finset.mem_image_of_mem _ ha)
    obtain ⟨v, hv⟩ := (u.norm_le x).1 (by rw [hx]; exact (mem_OO_iff _).1 (Subtype.prop _))
    exact ⟨v, Subtype.ext (by rw [← hx, ← hv]; rfl)⟩)
  let yV : Sp u.V ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec
  have hfac : spMap u.j ≫ yV = y := by
    rw [← specMap_valMap_fromSpec hW y hyW, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    rfl
  have hg : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V ≫ yV = gPt p ≫ y := by
    have e : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V = gPt p ≫ spMap u.j := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    rw [← hfac, ← Category.assoc, e, Category.assoc]
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) w)]
    rw [← hg] at hw
    exact hw
  refine ⟨⟨hat, yV, hfac, IsOpenImmersion.lift U₀.ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩⟩
  rw [← Spec.map_preimage (IsOpenImmersion.lift U₀.ι _ hr ≫ Q.u₀)]
  congr 1
  ext a
  apply (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective
  have h1 := preimage_comp_eq_val M U₀ hO.ne S.R Q.u₀ Q.u₀_pt
    (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ IsOpenImmersion.lift U₀.ι _ hr) a
  rw [Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, hg, ← hat a, Spec.preimage_comp,
    Spec.preimage_map] at h1
  exact h1.trans (DFunLike.congr_fun u.fac a).symm

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateGeometricPointStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_good_torsion_translate_geometricPoint : Laws → ∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (n : ℕ), 2 ≤ n → (n : K) ≠ 0 → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver S))), UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) → ∀ a : Over.mk x ⟶ P.A, ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ ∀ (z : baseOver S ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver S).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (v : Γ((baseOver S).left, ⊤)), (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ z = a * y → τ.IsGen → IsValueAt P.A P.L 1 th z τ v → v ≠ 0 := by
  first | exact @GlobalTheory.ThetaReal.exists_good_translate | exact GlobalTheory.ThetaReal.exists_good_translate | (intros; apply GlobalTheory.ThetaReal.exists_good_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfComparisonStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPullDeg_of_comparison : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D.TauBimult → ∃ hD : IsPullDeg φ D D', hD.e.hom.left ≫ pullback.fst _ _ = β ∧ HEq hD.w v ∧ hD.xe = xe := by
  first | exact @GlobalTheory.PsiRing.exists_isPullDeg_of_cmp | exact GlobalTheory.PsiRing.exists_isPullDeg_of_cmp | (intros; apply GlobalTheory.PsiRing.exists_isPullDeg_of_cmp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLiftStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isTorsFrame_of_symLift' : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (n : ℕ), Odd n → ∀ (T : Over S) (y x : T ⟶ P.A), y ^ (n ^ 2) = 1 → y ^ n = x → ∀ θ : ThetaGrp P.A P.L (n ^ 2 : ℕ) T, SymLift P.A P.L (n ^ 2 : ℕ) (n ^ 2) y θ → ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)), IsTorsFrame P rig n x τ := by
  first | exact @GlobalTheory.exists_isTorsFrame_of_symLift | exact GlobalTheory.exists_isTorsFrame_of_symLift | (intros; apply GlobalTheory.exists_isTorsFrame_of_symLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharactersStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelMap_torsion_characters : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range, Function.Surjective yy ∧ (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) := by
  first | exact @GlobalTheory.ZH.LabelMap.exists_labelMap | exact GlobalTheory.ZH.LabelMap.exists_labelMap | (intros; apply GlobalTheory.ZH.LabelMap.exists_labelMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelOfPowEqOneStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_label_of_pow_eq_one' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (m : ℕ), m ∣ S.r * S.N → ∀ h : baseOver (Sp u.V) ⟶ u.G, h ^ m = 1 → ∃ b : S.Gam, m • b = 0 ∧ GlobalTheory.UnitTheta.Extends u b h := by
  first | exact @GlobalTheory.UnitTheta.exists_label_of_pow_eq_one | exact GlobalTheory.UnitTheta.exists_label_of_pow_eq_one | (intros; apply GlobalTheory.UnitTheta.exists_label_of_pow_eq_one <;> assumption)
end

