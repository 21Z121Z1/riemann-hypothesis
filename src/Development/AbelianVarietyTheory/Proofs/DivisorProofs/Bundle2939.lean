import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2829
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2820
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0144
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2242
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalThetaSectionsRatioCoordinatesOverlap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open GlobalTheory.ProjSpace GlobalTheory.UMin.ThBdl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.ThBdl

theorem cross_resG_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} {V W : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : W ≤ V) (s : Γ(Y, U)) :
    resG X h ((f.appLE U V e).hom s) = (f.appLE U W (h.trans e)).hom s := by
  rw [← Scheme.Hom.appLE_map f e (homOfLE h).op]
  rfl

theorem cross_resG_resG {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (s : Γ(X, U)) :
    resG X h2 (resG X h1 s) = resG X (h2.trans h1) s := by
  change (X.presheaf.map _ ≫ X.presheaf.map _).hom _ = _
  rw [← Functor.map_comp]
  rfl

theorem cross_resG_self {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (s : Γ(X, U)) : resG X h s = s := by
  change (X.presheaf.map (𝟙 _)).hom s = s
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem cross_appLE_resG {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (h : U ≤ U') (s : Γ(Y, U')) :
    (f.appLE U V e).hom (resG Y h s) = (f.appLE U' V (e.trans fun _ hx => h hx)).hom s := by
  rw [← Scheme.Hom.map_appLE f e (homOfLE h).op]
  rfl

theorem cross_ratio_val {k Ω : Type} [CommRing k] [Field Ω] {n : ℕ} {x : Sp Ω ⟶ PSpace k n}
    {c : Fin (n + 1) → Ω} (hc : PCrd x c) {U : (PSpace k n).Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) {a : Fin (n + 1)}
    (ha : U ≤ chart k n a) :
    c a ≠ 0 ∧ ∀ b, (x.appLE U ⊤ hU).hom (ratioOn U a ha b) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b * (c a)⁻¹) := by
  obtain ⟨τ, -, H⟩ := hc
  have h1 : ((O1 k n).pull x).U (fun _ => a) ≤ x ⁻¹ᵁ (O1 k n).U a :=
    LB.wchart_le (O1 k n) (fun _ => x) (fun _ => a) PUnit.unit
  have h2 : ⊤ ≤ ((O1 k n).pull x).U (fun _ => a) :=
    fun y hy => Set.mem_iInter.2 fun _ => ha (hU hy)
  set t : Γ(Sp Ω, ⊤) := resG _ h2 (τ.s (fun _ => a)).val with ht
  have key : ∀ b, (x.appLE U ⊤ hU).hom (ratioOn U a ha b) =
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b) * t := by
    intro b
    have e := congrArg (resG _ h2) (H b (fun _ => a) h1)
    rw [map_mul, cross_resG_appLE] at e
    have e2 : ratioOn U a ha b = resG _ ha (ratio k n a b) := rfl
    rw [e2, cross_appLE_resG]
    refine e.trans (congrArg (· * t) ?_)
    exact (cross_resG_resG _ _ _).trans (cross_resG_self _ _)
  have ka := key a
  rw [ratioOn_self, map_one] at ka
  have hne : c a ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at ka
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ka
    rw [map_one, map_zero] at this
    exact one_ne_zero (α := Ω) this
  refine ⟨hne, fun b => ?_⟩
  rw [key, map_mul]
  congr 1
  have : (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ *
      (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a) = 1 := by
    rw [← map_mul]
    exact (congrArg _ (inv_mul_cancel₀ hne)).trans (map_one _)
  calc t = (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ *
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a) * t) := by rw [← _root_.mul_assoc, this, _root_.one_mul]
    _ = _ := by rw [← ka, _root_.mul_one]

theorem cross_pull_base {S : Scheme.{0}} (G : Over S) [GrpObj G] {K : Type} [Field K] (ξ : Sp K ⟶ S)
    {N : S.Opens} (hN : ⊤ ≤ ξ ⁻¹ᵁ N) {V : G.left.Opens} (hV : V ≤ G.hom ⁻¹ᵁ N) {W : (Over.mk ξ ⊗ G).left.Opens}
    (hW : W ≤ (snd (Over.mk ξ) G).left ⁻¹ᵁ V) (r : Γ(S, N)) :
    ((snd (Over.mk ξ) G).left.appLE V W hW).hom (resG _ hV ((G.hom.app N).hom r)) =
      liftHom G (T := Over.mk ξ) W ((ξ.appLE N ⊤ hN).hom r) := by
  have e : (snd (Over.mk ξ) G).left ≫ G.hom = (fst (Over.mk ξ) G).left ≫ ξ :=
    (Over.w (snd (Over.mk ξ) G)).trans (Over.w (fst (Over.mk ξ) G)).symm
  have e1 : ((snd (Over.mk ξ) G).left.appLE V W hW).hom (resG _ hV ((G.hom.app N).hom r)) =
      (G.hom.appLE N V hV ≫ (snd (Over.mk ξ) G).left.appLE V W hW).hom r := rfl
  have e2 : liftHom G (T := Over.mk ξ) W ((ξ.appLE N ⊤ hN).hom r) =
      (ξ.appLE N ⊤ hN ≫ (fst (Over.mk ξ) G).left.appLE ⊤ W le_top).hom r := rfl
  rw [e1, e2, Scheme.Hom.appLE_comp_appLE]
  erw [Scheme.Hom.appLE_comp_appLE]
  simp only [e]

theorem cross_ratio_sections : ∀ (k Ω : Type) [CommRing k] [Field Ω] [Algebra k Ω] (M : RatModel k Ω) (G : Over M.Z) [GrpObj G]
    (L : LB G.left) (n : ℕ) (c : Fin (n + 1) → Ω) (h : M.Z ⟶ PSpace k n) (v : SecM G L 1 (Over.mk M.pt)),
    PCrd (M.pt ≫ h) c →
    (∀ (N N' : M.Z.Opens) (s : LocSec G L N) (s' : LocSec G L N') (w : SecM G L 1 (Over.mk M.pt)),
      GenIs M.pt s w → GenIs M.pt s' w → ∀ i,
        resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N) (s i) =
          resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ : L.U i ⊓ G.hom ⁻¹ᵁ (N ⊓ N') ≤ L.U i ⊓ G.hom ⁻¹ᵁ N') (s' i)) →
    ∀ (a b : Fin (n + 1)) (sa : LocSec G L (h ⁻¹ᵁ chart k n a)) (sb : LocSec G L (h ⁻¹ᵁ chart k n b)),
      (((h ⁻¹ᵁ chart k n a : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sa ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v)) →
      (((h ⁻¹ᵁ chart k n b : M.Z.Opens) : Set M.Z).Nonempty →
        GenIs M.pt sb ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c b)⁻¹ • v)) →
      ∀ i, resG _ (fun _ hx => ⟨hx.1, hx.2.1⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a)) (sa i) =
        resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i) := by
  intro k Ω _ _ _ M G _ L n c h v hc huniq a b sa sb ha hb i
  by_cases hne : ((h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) : Set M.Z).Nonempty
  swap
  · have hbot : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) = ⊥ :=
      eq_bot_iff.2 fun y hy => hne ⟨_, hy.2⟩
    have : Subsingleton Γ(G.left, L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b))) := by
      rw [hbot]; infer_instance
    exact Subsingleton.elim _ _
  obtain ⟨ha1, ha2⟩ := ha (hne.mono fun _ hx => hx.1)
  obtain ⟨hb1, hb2⟩ := hb (hne.mono fun _ hx => hx.2)
  have htop := M.top_le_preimage_pt hne
  have hr : Set.range M.pt ⊆ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b) : M.Z.Opens) :=
    (top_le_preimage_iff _ _).1 htop
  have htop' : ⊤ ≤ (M.pt ≫ h) ⁻¹ᵁ (chart k n a ⊓ chart k n b) := htop
  obtain ⟨hca, hra⟩ := cross_ratio_val hc htop' inf_le_left
  obtain ⟨hcb, -⟩ := cross_ratio_val hc htop' inf_le_right
  let s₂ : LocSec G L (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) := fun i =>
    resG _ (fun _ hx => hx.2 : L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
            G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)))
          ((G.hom.app _).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b))) *
        resG _ (fun _ hx => ⟨hx.1, hx.2.2⟩ :
          L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤ L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n b)) (sb i)
  have g₂ : GenIs M.pt s₂ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (c a)⁻¹ • v) := by
    refine ⟨hr, funext fun j => ?_⟩
    have e3 := congrFun hb2 j
    simp only [genPull, s₂] at e3 ⊢
    rw [map_mul, cross_pull_base G M.pt htop]
    refine (congrArg (_ * ·) ((cross_appLE_resG _ _ _ _).trans e3)).trans ?_
    have e4 : (M.pt.appLE _ ⊤ htop).hom ((h.app _).hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b)) =
        ((M.pt ≫ h).appLE _ ⊤ htop').hom (ratioOn (chart k n a ⊓ chart k n b) a inf_le_left b) := by
      rw [Scheme.Hom.comp_appLE]
      rfl
    rw [e4, hra]
    change liftHom G _ _ * (liftHom G _ _ * v.1 j) = liftHom G _ _ * v.1 j
    rw [← _root_.mul_assoc, ← map_mul]
    congr 2
    erw [← map_mul]
    congr 1
    change c b * (c a)⁻¹ * (c b)⁻¹ = (c a)⁻¹
    field_simp
  have e := congrArg (resG _ (fun _ hx => ⟨hx.1, hx.2.1, hx.2⟩ :
    L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ (chart k n a ⊓ chart k n b)) ≤
      L.U i ⊓ G.hom ⁻¹ᵁ (h ⁻¹ᵁ chart k n a ⊓ h ⁻¹ᵁ (chart k n a ⊓ chart k n b))))
    (huniq _ _ sa s₂ _ ⟨ha1, ha2⟩ g₂ i)
  exact (cross_resG_resG _ _ _).symm.trans (e.trans ((cross_resG_resG _ _ _).trans (cross_resG_self _ _)))

end GlobalTheory.UMin.ThBdl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogKodairaSpencerWedgeFrameChange
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.LogKSDiv.topPair_frameChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → FnAlgClosed Xo c → ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)], ∀ (w w' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (X₀ TF.Y Z).functionField) ⟶ TF.Y.t.G.left)) (D D' : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (X₀ TF.Y Z).functionField) (d : (E →+* ℂ) → (X₀ TF.Y Z).functionFieldˣ), GlobalTheory.LogKSDiv.GenKS TF Z w D → GlobalTheory.LogKSDiv.GenKS TF Z w' D' → (∀ τ i, IsCombAtG TF.Y.t ((show Sp (X₀ TF.Y Z).functionField ⟶ X₀ TF.Y Z from (X₀ TF.Y Z).fromSpecStalk (genericPoint (X₀ TF.Y Z))) ≫ (barComp TF.Y Z).ι) (w' τ) (A τ i) (w τ i)) → (∀ τ, (d τ : (X₀ TF.Y Z).functionField) = (A τ).det) → ∃ u : (X₀ TF.Y Z).functionField, (u = 1 ∨ u = -1) ∧ ∀ η : RatForms (s₀ TF.Y Z) Dw.dim, GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D η = u * ((∏ τ, d τ ^ (if τ (H.rt : E) = H.rt0 then (Dw.q : ℤ) else Dw.p) : (X₀ TF.Y Z).functionFieldˣ) : (X₀ TF.Y Z).functionField) * GlobalTheory.LogKSDiv.topPair (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)) D' η := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hF _ _ w w' D D' A d hw hw' hA hd
  obtain ⟨n, n', e, e', ε, ε', L, hM, hD⟩ := GlobalTheory.T.genericPoint_logKodairaSpencer_frame_change E H Dw l Xo c TF Z hpq hF w w' D D' A hw hw' hA
  obtain ⟨u, hu, hdet⟩ := GlobalTheory.T.det_frameChange_balancedTensors_cmType E H Dw _ A n n' e e' ε ε' L hM
  refine ⟨u, hu, fun η => ?_⟩
  rw [GlobalTheory.T.topFormDerivationDetPairing_change_matrix _ D D' L hD η, hdet]
  congr 2
  rw [Units.coe_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  split_ifs <;> simp [zpow_natCast, hd]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogSumBadPrimesLeSqStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logSum_badPrimes_le_mul_sq : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → GlobalTheory.FlatTw.logSum (GlobalTheory.FlatTw.badPrimes T.Q.H Y.d.l₂) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 := by
  first | exact @GlobalTheory.BadLogCov.logSum_badPrimes_le_sq | exact GlobalTheory.BadLogCov.logSum_badPrimes_le_sq | (intros; apply GlobalTheory.BadLogCov.logSum_badPrimes_le_sq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpOfVal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.Point

section Reg

variable {X X' Y W : Scheme.{0}} (L : LB X) (L' : LB X')

def tr {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (I : (Y ⟶ X) → L.ι) (ψ : Y ⟶ X) :
    (Z.presheaf.stalk z)ˣ :=
  gm (r ≫ ψ) z (L.U (J (r ≫ ψ)) ⊓ L.U (I ψ)) (L.g (J (r ≫ ψ)) (I ψ))

def Reg (F : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) → (Z.presheaf.stalk z)ˣ)
    (c : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → ((Y ⟶ X') → U) → U) : Prop :=
  ∀ (y : Y) I I', Good L y I → Good L' y I' → ∃ V : Y.Opens, y ∈ V ∧ ∃ u : Γ(Y, V)ˣ,
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', r z ∈ V → Good L z J → Good L' z J' →
      F Z r z J J' = c _ (tr L r z J I) (tr L' r z J' I') * gm r z V u

variable {L L'}
variable {F G : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Y) (z : Z), ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) → (Z.presheaf.stalk z)ˣ}
  {c d : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → ((Y ⟶ X') → U) → U}

theorem Reg.mul (hF : Reg L L' F c) (hG : Reg L L' G d) :
    Reg L L' (fun Z r z J J' => F Z r z J J' * G Z r z J J') (fun U _ h h' => c U h h' * d U h h') := by
  intro y I I' hI hI'
  obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
  obtain ⟨V', hV', u', hu'⟩ := hG y I I' hI hI'
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, res inf_le_left u * res inf_le_right u', fun Z r z J J' hz hJ hJ' => ?_⟩
  rw [map_mul, gm_res r z _ hz, gm_res r z _ hz]
  show F Z r z J J' * G Z r z J J' = _
  rw [hu Z r z J J' hz.1 hJ hJ', hu' Z r z J J' hz.2 hJ hJ', _root_.mul_mul_mul_comm]

theorem Reg.inv (hF : Reg L L' F c) :
    Reg L L' (fun Z r z J J' => (F Z r z J J')⁻¹) (fun U _ h h' => (c U h h')⁻¹) := by
  intro y I I' hI hI'
  obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
  refine ⟨V, hV, u⁻¹, fun Z r z J J' hz hJ hJ' => ?_⟩
  show (F Z r z J J')⁻¹ = _
  rw [map_inv, hu Z r z J J' hz hJ hJ', mul_inv]

theorem good_exists {M : LB X} (hM : M.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good M z J := by
  choose I hI using fun χ : Z ⟶ X => exists_chart hM (χ z)
  exact ⟨I, hI⟩

theorem Reg.glue (hL : L.IsLB) (hL' : L'.IsLB) (hF : Reg L L' F c)
    (hc : ∀ (U : Type) [CommGroup U] h h', c U h h' = 1) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', Good L z J → Good L' z J' →
      F Z r z J J' = gm r z ⊤ a := by
  have H : ∀ y : Y, ∃ V : Y.Opens, y ∈ V ∧ ∃ u : Γ(Y, V)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J', r z ∈ V → Good L z J → Good L' z J' → F Z r z J J' = gm r z V u := by
    intro y
    obtain ⟨I, hI⟩ := good_exists hL y
    obtain ⟨I', hI'⟩ := good_exists hL' y
    obtain ⟨V, hV, u, hu⟩ := hF y I I' hI hI'
    exact ⟨V, hV, u, fun Z r z J J' hz hJ hJ' => by rw [hu Z r z J J' hz hJ hJ', hc, _root_.one_mul]⟩
  choose V hV u hu using H
  obtain ⟨a, ha⟩ := glue_unit ⊤ V (fun _ => le_top) (fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hV y⟩) u
    (fun i j x hx => by
      obtain ⟨I, hI⟩ := good_exists hL x
      obtain ⟨I', hI'⟩ := good_exists hL' x
      exact (hu i _ (𝟙 Y) x I I' hx.1 hI hI').symm.trans (hu j _ (𝟙 Y) x I I' hx.2 hI hI'))
  refine ⟨a, fun Z r z J J' hJ hJ' => ?_⟩
  rw [hu (r z) Z r z J J' (hV _) hJ hJ', ← ha, gm_res r z _ (hV _)]

theorem Reg.rigid (hL : L.IsLB) (hL' : L'.IsLB) (hF : Reg L L' F c)
    (hc : ∀ (U : Type) [CommGroup U] h h', c U h h' = 1) {S : Scheme.{0}} (p : Y ⟶ S)
    (hp : Function.Surjective p.appTop.hom) {Z : Scheme.{0}} (r r' : Z ⟶ Y) (hr : r ≫ p = r' ≫ p) (z : Z) {J J'}
    (hJ : Good L z J) (hJ' : Good L' z J') : F Z r z J J' = F Z r' z J J' := by
  obtain ⟨a, ha⟩ := hF.glue hL hL' hc
  obtain ⟨a₀, e⟩ := hp a.val
  rw [ha Z r z J J' hJ hJ', ha Z r' z J J' hJ hJ']
  apply Units.ext
  have k : ∀ q : Z ⟶ Y, (gm q z ⊤ a).val = gs (q ≫ p) z ⊤ a₀ := fun q => by
    rw [← gs_unit q z ⊤ trivial, ← e]
    exact gs_pull q p z ⊤ trivial a₀
  rw [k, k, hr]

variable {K : Type} [Fintype K]

theorem reg_val {φ : K → (W ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (p : Y ⟶ W) :
    Reg L L' (fun _ r z J _ => val t (r ≫ p) z J) (fun _ _ h _ => ∏ k, h (p ≫ φ k) ^ ε k) := by
  intro y I I' hI _
  refine ⟨p ⁻¹ᵁ LB.wchart L φ (fun k => I (p ≫ φ k)), hI.mem φ p, pullU p _ (t.s _), fun Z r z J J' hz hJ _ => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gen_trans ht (r ≫ p) z (hJ.mem φ (r ≫ p)) hz).trans (congrArg (· * _) ?_)
  rfl

theorem reg_val' {φ : K → (W ⟶ X')} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L' φ ε)} (ht : t.IsGen) (p : Y ⟶ W) :
    Reg L L' (fun _ r z _ J' => val t (r ≫ p) z J') (fun _ _ _ h' => ∏ k, h' (p ≫ φ k) ^ ε k) := by
  intro y I I' _ hI
  refine ⟨p ⁻¹ᵁ LB.wchart L' φ (fun k => I' (p ≫ φ k)), hI.mem φ p, pullU p _ (t.s _), fun Z r z J J' hz _ hJ => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gen_trans ht (r ≫ p) z (hJ.mem φ (r ≫ p)) hz).trans (congrArg (· * _) ?_)
  rfl

def wv {pr : K → (X' ⟶ X)} {ε : K → ℤ} (w : LB.Iso L' (LB.LinComb L pr ε)) {Z : Scheme.{0}} (q : Z ⟶ X') (z : Z)
    (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) : (Z.presheaf.stalk z)ˣ :=
  gv w q z (fun k => J (q ≫ pr k)) (J' q)

theorem reg_wv {pr : K → (X' ⟶ X)} {ε : K → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} (hw : w.IsGen) (p : Y ⟶ X') :
    Reg L L' (fun _ r z J J' => wv w (r ≫ p) z J J') (fun _ _ h h' => (∏ k, h (p ≫ pr k) ^ ε k) * (h' p)⁻¹) := by
  intro y I I' hI hI'
  refine ⟨p ⁻¹ᵁ (LB.wchart L pr (fun k => I (p ≫ pr k)) ⊓ L'.U (I' p)), ⟨hI.mem pr p, hI' p⟩,
    pullU p _ (w.s (fun k => I (p ≫ pr k), I' p)), fun Z r z J J' hz hJ hJ' => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (gm_isGen hw (r ≫ p) z _ (fun k => I (p ≫ pr k)) _ (I' p) (hJ.mem pr (r ≫ p)) hz.1 (hJ' _) hz.2).trans
    (congrArg (· * _) (congrArg₂ (· * ·) ?_ rfl))
  refine (gm_linComb L pr ε (r ≫ p) z _ _ (hJ.mem pr (r ≫ p)) hz.1).trans ?_
  rfl

end Reg

open GlobalTheory.LamBiext GlobalTheory.LamRigid GlobalTheory.PolDeg in
theorem reg_lam {S S' Y : Scheme.{0}} {B : Over S} {B' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj B']
    [IsCommMonObj B'] {M : LB B.left} {M' : LB B'.left} {β₂ : (G2 B').left ⟶ (G2 B).left}
    {w : LB.Iso (abelian₂ B' M') ((abelian₂ B M).pull β₂)} (hw : w.IsGen) (p : Y ⟶ (G2 B').left) :
    Reg M M' (fun _ r z J J' => lamVal w (r ≫ p) z J J')
      (fun _ _ h h' => (∏ k, h ((p ≫ β₂) ≫ lamφ B k) ^ lamε k) * (∏ k, h' (p ≫ lamφ B' k) ^ lamε k)⁻¹) := by
  intro y I I' hI hI'
  refine ⟨p ⁻¹ᵁ (((abelian₂ B M).pull β₂).U (fun _ => ind B I (p ≫ β₂)) ⊓ (abelian₂ B' M').U (ind B' I' p)),
    ⟨mem_pull.2 (good_ind hI (p ≫ β₂)), good_ind hI' p⟩,
    pullU p _ (w.s (fun _ => ind B I (p ≫ β₂), ind B' I' p)), fun Z r z J J' hz hJ hJ' => ?_⟩
  refine Eq.trans ?_ (congrArg (_ * ·) (gm_pull r p z _ hz _).symm)
  refine (lamVal_eq w (r ≫ p) z J J').trans ?_
  refine ((isGen_iff w).1 hw Z (r ≫ p) z _ (ind B I (p ≫ β₂)) _ (ind B' I' p) (good_ind hJ ((r ≫ p) ≫ β₂))
    (mem_pull.1 hz.1) (good_ind hJ' _) hz.2).trans (congrArg (· * _) (congrArg₂ (· * ·) ?_ (congrArg (·⁻¹) ?_)))
  · refine (gm_linComb M (lamφ B) lamε ((r ≫ p) ≫ β₂) z _ _ (good_ind hJ ((r ≫ p) ≫ β₂)) (mem_pull.1 hz.1)).trans ?_
    rfl
  · refine (gm_linComb M' (lamφ B') lamε (r ≫ p) z _ _ (good_ind hJ' _) hz.2).trans ?_
    rfl

section Scale

variable {Y : Scheme.{0}} {M : LB Y}

def scale (a : Γ(Y, ⊤)ˣ) (t : LB.Gen M) : LB.Gen M := ⟨fun i => res le_top a * t.s i⟩

theorem gm_scale (a : Γ(Y, ⊤)ˣ) (t : LB.Gen M) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (i : M.ι) (h : r z ∈ M.U i) :
    gm r z (M.U i) ((scale a t).s i) = gm r z ⊤ a * gm r z (M.U i) (t.s i) :=
  (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z _ h a))

theorem scale_isGen (a : Γ(Y, ⊤)ˣ) {t : LB.Gen M} (ht : t.IsGen) : (scale a t).IsGen := fun i j =>
  unit_ext fun y hy => by
    have e := congrArg (gm (𝟙 Y) y _) (ht i j)
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_scale a t _ y i hy.1, gm_scale a t _ y j hy.2, e, mul_left_comm]

end Scale

theorem mapsAtExp_of_val {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB) {K : Type}
    [Fintype K] {pr : K → (X' ⟶ X)} {ε : K → ℤ} {w : LB.Iso L' (LB.LinComb L pr ε)} (hw : w.IsGen) {p : Y ⟶ X'} {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p) (fun _ => n))} (ha : a.IsGen)
    {b : LB.Gen (LB.LinComb L (K := K) (fun i => p ≫ pr i) (fun i => n * ε i))} (hb : b.IsGen)
    (H : ∀ (y : Y) J J', Good L y J → Good L' y J' → val b (𝟙 Y) y J = wv w p y J J' ^ n * val a (𝟙 Y) y J') :
    MapsAtExp L L' pr ε w p n a b := by
  intro jN jL
  refine unit_ext fun y hy => ?_
  obtain ⟨J, hJ⟩ := good_exists hL y
  obtain ⟨J', hJ'⟩ := good_exists hL' y
  have e := H y J J' hJ hJ'
  rw [val_of b _ y J (fun i => J (p ≫ pr i)) (fun i => by rw [Category.id_comp]),
    val_of a _ y J' (fun _ => J' p) (fun i => by rw [Category.id_comp])] at e
  have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun i => p ≫ pr i) (fun i => J (p ≫ pr i)) := Set.mem_iInter.2 fun i => hJ _
  have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' (fun _ : PUnit => p) (fun _ => J' p) := Set.mem_iInter.2 fun i => hJ' _
  have eb := gen_trans hb (𝟙 Y) y (mapsAtExp_le_b L L' pr ε p jN jL hy) m₁
  have ea := gen_trans ha (𝟙 Y) y (mapsAtExp_le_a L L' pr ε p jN jL hy) m₂
  have ew := gm_isGen hw p y jN (fun i => J (p ≫ pr i)) jL (J' p) hy.1 (hJ.mem pr p) hy.2 (hJ' p)
  have el := gm_linComb L pr ε p y jN (fun i => J (p ≫ pr i)) hy.1 (hJ.mem pr p)
  refine (gm_res _ y _ hy _).trans (eb.trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    ((map_zpow _ _ _).trans (congrArg (· ^ n) ((gm_pull (𝟙 Y) p y _ hy _).trans
      ((congrArg (fun q : Y ⟶ X' => gv w q y jN jL) (Category.id_comp p)).trans
        (ew.trans (congrArg (fun x => x * _ * _) el)))))) ((gm_res _ y _ hy _).trans ea))).symm))
  rw [e]
  simp only [trF, wv, Category.id_comp, Fintype.prod_unique, mul_zpow, ← Finset.prod_zpow, inv_zpow, ← zpow_mul,
    mul_comm n]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.MumCmp.Point
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSecOfMemCuspWWtZ
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefSum

theorem mem_sec_of_mem_cuspW_wtZ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ cuspW Xo c U (wtZ a n)) : f ∈ sec Xo c a n := by
  rw [cuspW_wtZ] at hf
  exact cusp_le_sec Xo c U a n hf

theorem refExp_vp_cover_le : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (cst : ℝ) (q : ℕ), q.Prime → refExp_vp Y.U cst (wtZ a n) q ≤ refExp_vp (T.U j) cst (wtZ a n) q := by
  intro D T j Y e o hJ hj hG a n hD cst q hq
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq', -⟩ := hJ.pins.2.2.2 j hj
    obtain ⟨h1, h2⟩ := hj
    have h3 := D.R.m_add_three_le_k
    rw [hp, hq']
    simp only [Ranks.sigW]
    omega
  have hL := GlobalTheory.LevGeo.laws_core D T j hJ hj
  have hne : (T.Q.Dw j).p ≠ (T.Q.Dw j).q := by
    obtain ⟨hp, hq', -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq']
    simp only [Ranks.sigW]
    omega
  rw [refExp_vp_le_iff]
  intro la₂ S io₂ e₂ ho₂ y₂ ha₂ φ hφ
  obtain ⟨y', ha', hφ', hv'⟩ := GlobalTheory.CoverDown.exists_intFr_below _ _ _ _ (T.Q.Xo j) Y.c' Y.d hpq hG.lev.1
    (Or.inl ⟨hne, hL.levA⟩) S io₂ y₂ ha₂
  obtain ⟨y, ha, hφy, hv⟩ := GlobalTheory.T.integralFramedPoint_restrict_coefficient_field _ _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle S _ y' ha'
  obtain ⟨la', e', hq', ho'⟩ := GlobalTheory.PlaceBelow.exists_overLa_under Y.c'.F Y.d.c₂.F (Y.d.eF : Y.c'.F →+* Y.d.c₂.F) q la₂.1 hq la₂.2 S io₂ e₂ ho₂
  obtain ⟨la, e₀, hq₀, ho⟩ := GlobalTheory.PlaceBelow.exists_overLa_under T.Q.c.F Y.c'.F (IntermediateField.inclusion Y.hle).toRingHom q la' hq hq' S _ e' ho'
  refine le_trans ?_ (refExp_vp_le_iff (T.U j) |>.1 le_rfl ⟨la, hq₀⟩ S _ e₀ ho y ha φ (hφy φ (hφ' φ hφ)))
  refine le_iInf₂ fun f hf => ?_
  obtain ⟨g, ⟨hg, hP⟩, -⟩ := GlobalTheory.T.existsUnique_cuspForm_pullback_goodCover D T j Y e o hJ hj hG hG.unit hG.modelW a n hD f.1 f.2
  have hgl := (GlobalTheory.T.pullback_mem_cuspFormSupLattice_iff D T j Y e o hJ hj hG a n f ⟨g, hg⟩ hP).2 hf
  have hfs : f.1 ∈ sec (T.Q.Xo j) T.Q.c a n := mem_sec_of_mem_cuspW_wtZ f.2
  have hP' := ((GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hJ hj hG hG.unit hG.modelW).2.2 a n f.1 hfs g).1 hP
  have hbc := ((GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (T.Q.Xo j) T.Q.c Y.c' Y.hle).1 a n f.1 hfs).1
  have hval : evI y₂ g = evI y f.1 :=
    (hv' a n _ hbc g (mem_sec_of_mem_cuspW_wtZ hg) hP').trans (hv a n f.1 hfs)
  refine (iInf₂_le (⟨g, hg⟩ : Y.V (wtZ a n)) hgl).trans (le_of_eq ?_)
  exact congrArg _ hval

end GlobalTheory.RefSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorOverRestrictEtaleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeDivisorOver_restrict_etale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E' : DivOver (f ≫ p), E'.Through y → ∃ E : DivOver p, E.Through (f y) ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  first | exact @GlobalTheory.EtaleKlt.divOver_restrict | exact GlobalTheory.EtaleKlt.divOver_restrict | (intros; apply GlobalTheory.EtaleKlt.divOver_restrict <;> assumption)
end

