import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2087
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.ReadsOnlyOmegaFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulEqOfHatCNeZeroOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfRhoEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelFamilyTangentDimensionBound
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1960

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowRepresentationPreservesLatticeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_representation_preserves_lattice : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows → GlobalTheory.CovTop.RecTied D L →
    ∀ (i : Fin D.R.m) (g : p.P.Gp) f, f ∈ (p.R.toRealDat.FW i).MK → (p.R.toRealDat.FW i).ρ g f ∈ (p.R.toRealDat.FW i).MK := by
  first | exact @GlobalTheory.TieMK.act_mem_MK | exact GlobalTheory.TieMK.act_mem_MK | (intros; apply GlobalTheory.TieMK.act_mem_MK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionOverFieldEqOfClosedPointImageEqStatement
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
open GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_over_field_eq_of_closedPoint_image_eq : ∀ (K : Type) [Field K] (X : Scheme.{0}) (q : X ⟶ Sp K) (z z' : Sp K ⟶ X), z ≫ q = 𝟙 _ → z' ≫ q = 𝟙 _ → z (IsLocalRing.closedPoint K) = z' (IsLocalRing.closedPoint K) → z = z' := by
  first | exact @GlobalTheory.section_eq_of_point_eq | exact GlobalTheory.section_eq_of_point_eq | (intros; apply GlobalTheory.section_eq_of_point_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueTangentLiftEqFirstJetStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionValue_tangentLift_eq_firstJet : ∀ (g : ℕ) (P : PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ)))) (f : (Fin g → ℂ) → ℂ) (v : epsR ℂ ⟶ P.A) (W : Fin g → ℂ) (i : P.L.ι), FnT u k t f → Differentiable ℂ f → IsTangent v → u.IsDiff W v → ⊤ ≤ (eSec P.A) ⁻¹ᵁ P.L.U i → valR (epsLift v) ((LPow P.A P.L (k : ℤ) (baseOver (Sp ℂ))).U fun _ => i) (t.f fun _ => i) = TrivSqZeroExt.inl (u.fr i 0 ^ k) * (TrivSqZeroExt.inl (f 0) + TrivSqZeroExt.inr (fderiv ℂ f 0 W + (k * fderiv ℂ (u.fr i) 0 W / u.fr i 0) * f 0)) := by
  first | exact @GlobalTheory.MBLow.EpsVal.valR_epsLift | exact GlobalTheory.MBLow.EpsVal.valR_epsLift | (intros; apply GlobalTheory.MBLow.EpsVal.valR_epsLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOfLevelClassStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_of_level_class : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m), letI : IsCMField D.host.E := D.host.isCMField_hostE; GlobalTheory.UCls.SelfDualLat (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i) := by
  first | exact @GlobalTheory.MassLinkSD.base_selfDualLat | exact GlobalTheory.MassLinkSD.base_selfDualLat | (intros; apply GlobalTheory.MassLinkSD.base_selfDualLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianTripleMapIsOpenImmersionOpensRangeStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelianTripleMap_isOpenImmersion_opensRange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (j : X' ⟶ X) [IsOpenImmersion j] (m : SABMap t' t j), ∃ _ : IsOpenImmersion m.φ, m.φ.opensRange = t.G.hom ⁻¹ᵁ j.opensRange := by
  first | exact @GlobalTheory.sabMap_isOpenImmersion_opensRange | exact GlobalTheory.sabMap_isOpenImmersion_opensRange | (intros; apply GlobalTheory.sabMap_isOpenImmersion_opensRange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortAtFrame
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section
namespace GlobalTheory.FrameShort

open GlobalTheory.PtId GlobalTheory.AdTh in
set_option maxHeartbeats 4000000 in

theorem short_at_frame : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (cc : (T.J.U ((i : ℕ) + 1) (O i).s0).Comp → ℂ) (ka : ℂ) (δ : ℤˣ) (c0 : ℂ), GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.J.U ((i : ℕ) + 1) (O i).s0) (O i).dict (O i).mu (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (R.ωP i A.μ0) (R.vacP i) cc → GlobalTheory.PtId.IoAt (O i) (v₀ i (sg0 D A)) ka → GlobalTheory.PtId.ClsAt R i (iotaW T.J i) δ → GlobalTheory.PtId.CovAt (O i) c0 → ‖ka‖ = 1 → ‖c0‖ = 1 → ∀ c0' : ℂ, c0' * c0⁻¹ ∈ D.what₂.embLL.range → (∃ m : ℕ, 0 < m ∧ (c0' * c0⁻¹) ^ m = 1) → (∀ (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin D.R.r) (e : Fin g ≃ Lt1 (T.Q.Dw ((i : ℕ) + 1))) (k : GA D (Wc D i)) (xk : (AE D)ˣ) (mk : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)), GlobalTheory.AdTh.IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → GlobalTheory.ThFr.IsSympl X bas → GlobalTheory.AdTh.IdxIs T.Q.c (O i).s0 X idx e → GlobalTheory.AdTh.latR (rank_Wc i) (latG (Wc D i) k) = X.Λ → IsDetRoot (Wc D i) k xk → GlobalTheory.Dict.IsMark (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ X.Λ mk → GlobalTheory.AdTh.MarkAd (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂ (Wc D i) (rank_Wc i) (iotaW T.J i) k mk → letI : Algebra (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F ℂ := ((O i).s0.comp ((T.dδ ((i : ℕ) + 1) (Vc D i).rank).eF.symm : (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂.F →+* T.Q.c.F)).toAlgebra; ∀ (y₂ : FrPt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ ℂ) (A₂ : GlobalTheory.Dict.AnFib X bas idx e (GlobalTheory.AdTh.frMove R.θ (Wc D i) (rank_Wc i) X k (fun τ => T.J.x₀ ((i : ℕ) + 1) (O i).s0 τ.1)) X.Λ y₂), A₂.Marked mk → evR (T.dδ ((i : ℕ) + 1) (Vc D i).rank).Xo₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).c₂ (T.dδ ((i : ℕ) + 1) (Vc D i).rank).cδ y₂ = c0' * ((χ xk : Circle) : ℂ)) → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ F₀ : (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i), IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x₀ P ((F₀).1 : T.R ((i : ℕ) + 1)) → ∀ g : GA D (Wc D i), (lieFac (T.J.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ GlobalTheory.PtId.degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) * c0⁻¹) • cc) ((F₀).1 : T.R ((i : ℕ) + 1)) g = D.what₂.embLL c * singleSeries R i ω φ' h ((O i).c0' y) w g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hOP hβ hU hIo hRow hPh hSp v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h hSB hLa N x₀ P y hUm hTb hTd hLev hAdm hPh' hio cc ka δ c0 hcc hka hδ hcov hka1 hc01 c0' hρ hρm hcT
  have hTi : TieIn T.J R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hP := hOP.2
  have hs : (O i).s0 = T.J.toCore.σ₀ := sOv_eq _ _ _
  have hσ : GoodEmb T.J.Q.c (O i).s0 := hs ▸ T.J.toCore.good_σ₀
  have hmod := models_at_record_core D G Pl0 T0 A T.J R F κ v₀ hC hTi i (O i).s0 hs
  obtain ⟨hemb, hisom, hroot, hmk⟩ := dict_cast T.J hTi.laws _ (inR i) (O i).s0 hσ (Wc D i) (O i).hV (rank_Wc i)
  obtain ⟨δ', hδ'⟩ := GlobalTheory.AdTh.ShortSeriesTw.thetaKO_eq_short_series_tw D G Pl0 T0 A _ R F hC i hP.lift.std _ _ (iotaW T.J i) hemb hisom
  obtain ⟨y₀, ζ, φc, hrk, hζL, hζm, hhat, hphi, hhalf, hbadP⟩ := GlobalTheory.CoverDatum.datum_eq_hat_free D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hβ v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK x₀ hAdm
  obtain ⟨hGf, e, Ps, he, hPs0, hsupp⟩ := hSB
  have hPs : ∀ PP ∈ Ps, ((badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP hm =>
    hPs0 PP hPP (by rw [Nat.cast_mul]; exact PP.asIdeal.mul_mem_right _ hm)
  have hPsO : ∀ PP ∈ Ps, (((O i).bad () : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hPP hm =>
    hPs0 PP hPP (by rw [Nat.cast_mul]; exact PP.asIdeal.mul_mem_left _ hm)
  obtain ⟨yd, hyd⟩ := exists_isDetAt he (Vc D i) h
  obtain ⟨c1, hc1, hint1⟩ := GlobalTheory.T.twisted_kernel_class_scalar_integral_standard D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP v hv hmu hQ hF0 hV hdel hMb hRun ℓ hLP hAP χ ξR ω φ hK Λ h N hUm hTb hTd hLev hLa e Ps yd hGf he hPs hPsO hsupp hyd
  obtain ⟨ρ, hρ'⟩ := hρ
  obtain ⟨ζL, hζL'⟩ := hζL
  have hρm' : ∃ m : ℕ, 0 < m ∧ ρ ^ m = 1 := by
    obtain ⟨m, hm, hm1⟩ := hρm
    refine ⟨m, hm, D.what₂.embLL.injective ?_⟩
    rw [map_pow, hρ', hm1, map_one]
  have hζm' : ∃ m : ℕ, 0 < m ∧ ζL ^ m = 1 := by
    obtain ⟨m, hm, hm1⟩ := hζm
    refine ⟨m, hm, D.what₂.embLL.injective ?_⟩
    rw [map_pow, hζL', hm1, map_one]
  have hroot_int : ∀ z : D.what₂.LL, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → IsIntegral ℤ z ∧ IsIntegral ℤ z⁻¹ := by
    rintro z ⟨m, hm, hz⟩
    have hzI : IsIntegral ℤ z := IsIntegral.of_pow hm (hz ▸ isIntegral_one)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hm.ne'] at hz
      exact zero_ne_one hz
    refine ⟨hzI, ?_⟩
    have e : z⁻¹ = z ^ (m - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hz0, ← pow_succ, Nat.sub_add_cancel hm]
      exact hz
    rw [e]
    exact hzI.pow _
  set d := degW (T.J.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) with hd
  refine ⟨y₀, ((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * c1, hrk, fun lam hlam => ?_, ?_⟩
  · obtain ⟨s, hs, hsi⟩ := hint1 lam hlam
    refine ⟨s, hs, ?_⟩
    have e : (s : D.what₂.LL) * (((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * c1) =
        ((((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ) : D.what₂.LL) * ρ * ζL⁻¹ * ((s : D.what₂.LL) * c1) := by ring
    rw [e]
    exact (((isIntegral_algebraMap (R := ℤ) (x := (((δ : ℤ) * (δ' : ℤ)) ^ d : ℤ))).mul (hroot_int ρ hρm').1).mul
      (hroot_int ζL hζm').2).mul hsi
  intro φ' hφ' w hw F₀ hF₀ g
  have hU' : IsUnf (T.J.U ((i : ℕ) + 1) (O i).s0) := hTi.laws.unf _ (inR i) (O i).s0 hσ
  obtain ⟨hX, hon, hinv, hp, hrk', hpq, h1, hrt, -, hbas, hD, -⟩ := hmod ((O i).dict g).1
  obtain ⟨hx, g', Dc, γ, mk, vv, ϑ, κ', B, hat, hsd, hm, hBm, hma, hϑ, hvv, hκ, hrd⟩ :=
    exists_point (T.J.U ((i : ℕ) + 1) (O i).s0) hσ hU' h1 hTi.laws.pins.2.1.2 R.θ (Vc D i) (Wc D i) (rank_Wc i) (O i).dict
      (iotaW T.J i) (T.J.x₀ ((i : ℕ) + 1) (O i).s0) (fun Wt k => hmk R.θ hC.models.inf (fun k => (hmod k).1) h1 Wt k)
      (wtA (κ i)) hD (O i).mu (R.ωP i A.μ0) (R.vacP i) cc hcc g
  obtain ⟨hγ, hΛ, hfr⟩ := hat
  obtain ⟨xk, hxk⟩ := hroot (γ * g)
  have hζ0 : ζ ≠ 0 := by
    obtain ⟨m, hm, hm1⟩ := hζm
    rintro rfl
    rw [zero_pow hm.ne'] at hm1
    exact zero_ne_one hm1
  letI : Algebra T.Q.c.F ℂ := (O i).s0.toAlgebra
  obtain ⟨mk₂, Y, hm₂, ha₂, hY, hgeo⟩ := GlobalTheory.ShortPtVal.short_value_at_point D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP χ c0' hcT Λ N x₀ P hUm hTb hTd hLev hAdm
    hPh' ζ φc hζ0 hhat F₀.1 hF₀ _ g' Dc (γ * g) xk hxk hX hp hΛ hsd _ hx hfr mk hm hma vv ϑ κ' hvv hκ _ B hBm hϑ
  obtain ⟨vr, hvr⟩ := exists_isVarOf (Vc D i) (Wc D i) (rank_Wc i) _ hX _ Dc.hr
  have hCs := GlobalTheory.AdTh.VecSeries.singleSeries_eq_phase_thetaKO D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOP hIo χ ω hK.weil _ _ φ' hφ' ka hka P y hio _ g' Dc vr hX hp hvr h w hw g γ hγ
  have htw := GlobalTheory.OnCmp.weil_twist_base_of D G Pl0 T0 A _ R F hC i χ ω hK.weil (γ * g) xk hxk (R.vacP i) (hC.thP.vP i A.μ0).1.2.theta
  have hrd' : Reads R.θ (Vc D i) (Wc D i) (rank_Wc i) ((T.J.U ((i : ℕ) + 1) (O i).s0).X ((O i).dict g).1) Dc.bas Dc.idx
      (ω (1, γ * g) (R.vacP i)) ((((χ xk : Circle) : ℂ) * (cc ((O i).dict g).1 * (O i).mu g * κ')) • vv) ((O i).dict g).2 := by
    obtain ⟨s1, s2⟩ := ((thA_heis_entire_linear_injective _ _ g' _ _ Dc.bas Dc.idx Dc.sympl hD.2 _ hx _ hrd.1).2.2 vv hvv.1).1
      ((χ xk : Circle) : ℂ) 0
    rw [zero_smul, add_zero, smul_smul] at s1 s2
    rw [zero_smul, add_zero] at s2
    refine ⟨s1, fun z hz => ?_⟩
    rw [htw, s2, Pi.smul_apply, Pi.smul_apply, hrd.2 z hz, smul_eq_mul, smul_eq_mul]
    ring
  have hH := hPh'.1
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map (O i).s0 P)).IsHomogeneous d :=
    ((isHomogeneous_of_rowDeg _ _ _ _ hH.2.2).map _).rename_isHomogeneous
  have hser := hδ' χ _ _ ω φ' hK.weil _ hK.chr hK.fin hK.ram hK.pl (GlobalTheory.OnCmp.readsOnly_omegaFree R i _ ξR y₀) hφ' _ φc hphi
    hhalf hrt g' _ _ Dc.hr Dc.bas Dc.idx _ vr hX Dc.sympl hon hinv (hbas _) hvr
    (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) N h (γ * g) Λ mk₂ e Ps yd hbadP he hPs hGf hsupp hyd hLa hTd hLev ha₂
    Y (hΛ ▸ hY) vv _ (hΛ ▸ hvv) (hfr ▸ hrd') _ d hhom
  rw [hΛ, ← hfr] at hser
  have hx0 : 0 < xiR D := norm_pos_iff.2 ((_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D))
  have hrdU : rdU (T.J.U ((i : ℕ) + 1) (O i).s0) (F₀.1 : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 = _ :=
    (dif_pos hx).trans hgeo
  have hphiE : (O i).phi ((ka * (-((δ : ℤ) : ℂ)) ^ d * c0⁻¹) • cc) (F₀.1 : T.R ((i : ℕ) + 1)) g =
      ((ka * (-((δ : ℤ) : ℂ)) ^ d * c0⁻¹) * cc ((O i).dict g).1) * (O i).mu g *
        rdU (T.J.U ((i : ℕ) + 1) (O i).s0) (F₀.1 : T.R ((i : ℕ) + 1)) ((O i).dict g).1 ((O i).dict g).2 := rfl
  have hSS := hCs.trans (congrArg (fun z => ka * z) hser)
  rw [hphiE, hrdU, hSS, GlobalTheory.AdTh.SerCore.lieFac_eq_sqrt_pow _ hx0, ← hc1]
  simp only [map_mul, map_inv₀, map_intCast, hρ', hζL']
  have hδ2 : ((δ' : ℤ) : ℂ) ^ d * ((δ' : ℤ) : ℂ) ^ d = 1 := by
    rw [← mul_pow]
    rcases Int.units_eq_one_or δ' with e | e <;> rw [e] <;> simp
  push_cast
  have alg : ∀ (s ka δc δc' c0 c0' k m x c1 a b q κ' ζ TH : ℂ) (n : ℕ), δc' ^ n * δc' ^ n = 1 →
      s ^ n * (ka * (-δc) ^ n * c0⁻¹ * k * m * (c0' * x * (c1 * (a * b * q) * κ' * ζ⁻¹ * TH))) =
        (δc * δc') ^ n * (c0' * c0⁻¹) * ζ⁻¹ * c1 * (ka * (δc' ^ n * (-1) ^ n * s ^ n * (x * (k * m * κ')) * (a * b) * q * TH)) := by
    intro s ka δc δc' c0 c0' k m x c1 a b q κ' ζ TH n hn
    rw [neg_pow, mul_pow]
    linear_combination (-(s ^ n * ka * (-1) ^ n * δc ^ n * c0⁻¹ * k * m * c0' * x * c1 * a * b * q * κ' * ζ⁻¹ * TH)) * hn
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hδ2

end GlobalTheory.FrameShort
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyClassifyingMapUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegUniq

theorem eq_of_siegPB : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (S : Scheme.{0})
    (s' : S ⟶ Sp (cycAway n)) (c : SiegPre g n (zetaAway n) s') (f f' : S ⟶ F.X), f ≫ F.s = s' → f' ≫ F.s = s' →
    SiegPB c F.univ f → SiegPB c F.univ f' → f = f' := by
  intro g n _ _ _ F S s' c f f' hf hf' h₁ h₂
  refine GlobalTheory.hom_ext_of_fromSpecStalk fun x => ?_
  haveI : IsLocalRing (S.presheaf.stalk x) := inferInstance
  obtain ⟨c', hc'⟩ := (GlobalTheory.siegPre_pullback g n (cycAway n) (zetaAway n) S (Sp (S.presheaf.stalk x)) s'
    (S.fromSpecStalk x ≫ s') (S.fromSpecStalk x) c rfl).1
  have e : (S.fromSpecStalk x ≫ f) ≫ F.s = (S.fromSpecStalk x ≫ f') ≫ F.s := by
    simp only [Category.assoc, hf, hf']
  exact @SFam.inj g n _ _ _ F (S.presheaf.stalk x) _ this (S.fromSpecStalk x ≫ f) (S.fromSpecStalk x ≫ f') (S.fromSpecStalk x ≫ s') c' e
    (GlobalTheory.SiegelPullComp.pb_comp h₁ hc') (GlobalTheory.SiegelPullComp.pb_comp h₂ hc')

end GlobalTheory.SiegUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyTangentBoundNonconstant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegelTangentBound

def acts (W : Matrix (Fin 8) (Fin 8) ℤ) : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ
  | .inl uv => Matrix.single uv.1 uv.2 1
  | .inr true => (W + W.transpose).adjugate * W
  | .inr false => (W + W.transpose).adjugate * W.transpose

theorem main : ∀ (h n : ℕ), 1 ≤ h → 3 ≤ n → Odd n → ∀ (K : Type) [Field K] [IsAlgClosed K] (r : ℕ) (β : cycAway n →+* K) (c : SiegPre h n (zetaAway n) (spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β))), c.Principal → (∀ (lam : (Fin r → K) →ₗ[K] K) (c' : SiegPre h n (zetaAway n) (spMap ((algebraMap K (DualNumber K)).comp β))), SiegPB c' c (spMap (dirMap lam)) → SiegPB c' c (constPt (spMap (dirMap lam))) → lam = 0) → r ≤ h * (h + 1) / 2 := by
  intro h n _ h3 hodd K _ _ r β c hc hun
  have hn : n ≠ 0 := by omega
  obtain ⟨L1, L2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨W, hW, hbasAll⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hbas⟩ := hbasAll h
  have hζ : (cycBase hn).ζ ^ n = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, cycBase_ζ]
    exact Subtype.ext (Complex.isPrimitiveRoot_exp n hn).pow_eq_one)
  have hdet : (W + W.transpose).det = 1 := hW.2
  have hw : (W + W.transpose) * acts W (.inr true) = W := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have hw' : (W + W.transpose) * acts W (.inr false) = W.transpose := by
    simp only [acts]; rw [← Matrix.mul_assoc, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mul]
  have he : ∀ u v : Fin 8, ∃ j, acts W j = Matrix.single u v 1 := fun u v => ⟨.inl (u, v), rfl⟩
  obtain ⟨t, ht⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c hodd h3 hζ hc
  refine GlobalTheory.PowerTangent.main L1 L2 GlobalTheory.Moduli.cube_of_isLB h (8 * h) W _ (acts W) bas hW hbas (.inr true) (.inr false)
    hw hw' n (cycAway n) (cycBase hn) K r β t c hc ht ?_
  intro lam t' m₁ m₂
  have hf : spMap (dirMap lam) ≫ spMap ((algebraMap K (TrivSqZeroExt K (Fin r → K))).comp β) =
      spMap ((algebraMap K (DualNumber K)).comp β) ≫ spMap (RingHom.id (cycAway n)) := by
    rw [← spMap_comp, ← spMap_comp]
    exact congrArg spMap (RingHom.ext fun z => by
      simp [dirMap, TrivSqZeroExt.algebraMap_eq_inl])
  obtain ⟨c', hc'⟩ := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).1 c
  have hc'P := (GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n _ _ (zetaAway n) (zetaAway n) (RingHom.id _) _ _ _ _
    (spMap (dirMap lam)) rfl hf).2.1 c c' hc' hc
  obtain ⟨t'', ht''⟩ := GlobalTheory.SiegelPower.exists_tObj_isSharp L1 L2 h (8 * h) W _ (acts W) bas hW hbas n (cycAway n)
    (cycBase hn) _ _ c' hodd h3 hζ hc'P
  have m₃ : TMap t'' t (spMap (dirMap lam)) :=
    (GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
      (spMap (dirMap lam)) hc hc'P ht ht'').1 hc'
  have m₄ : TMap t'' t' (𝟙 _) :=
    ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₁).2 (by rwa [Category.id_comp])
  have m₅ : TMap t'' t (constPt (spMap (dirMap lam))) := by
    have := ((GlobalTheory.ZM.tmap_id_comp_cancel _ _ _ _ _ _ _ _ _ _ _ t t' t'').2 _ (𝟙 _) m₂).1 m₄
    rwa [Category.id_comp] at this
  exact hun lam c' hc' ((GlobalTheory.PowerPullback.main L1 L2 h (8 * h) W _ (acts W) bas hW hbas n _ (cycBase hn) _ _ _ _ c c' t t''
    _ hc hc'P ht ht'').2 he m₅)

end GlobalTheory.SiegelTangentBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectPullbackLevelPowerCalculus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLevCalc

open GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''} {d d' d'' : ℕ}

theorem sRel_comp {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SRel c' c d' d f) (m' : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) := by
  obtain ⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨ψ, hψ, ⟨ψ₂, hs', hw'⟩, hl'⟩ := m'
  refine ⟨ψ ≫ φ, hψ.comp hφ, ⟨ψ₂ ≫ φ₂, ⟨?_, ?_⟩, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans c''.isLB (pull_isLB c'.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull ψ₂ hw)).trans
      c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB φ₂ ψ₂)
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) (hl' a)).trans ((Category.assoc _ _ _).trans
      ((congrArg (f' ≫ ·) (hl a)).trans (Category.assoc _ _ _).symm)))

theorem sRel_cancel {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S}
    {f' : S'' ⟶ S'} (m : SRel c' c d' d f) (m' : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' := by
  obtain ⟨φ, hφ, ⟨φ₂, hs, hw⟩, hl⟩ := m
  obtain ⟨χ, hχ, ⟨χ₂, hs', hw'⟩, hl'⟩ := m'
  have hp := hφ.1
  let F : c''.A.left ⟶ c'.A.left := hp.lift χ (c''.A.hom ≫ f') (by rw [hχ.1.w, Category.assoc])
  have hF : F ≫ φ = χ := hp.lift_fst _ _ _
  have hFw : F ≫ c'.A.hom = c''.A.hom ≫ f' := hp.lift_snd _ _ _
  let U : Over.mk ((c''.A ⊗ c''.A).hom ≫ f') ⟶ c'.A ⊗ c'.A :=
    lift (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A))
  let F₂ : (c''.A ⊗ c''.A).left ⟶ (c'.A ⊗ c'.A).left := U.left
  have h₁ : F₂ ≫ (fst c'.A c'.A).left = (fst c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_fst (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₂ : F₂ ≫ (snd c'.A c'.A).left = (snd c''.A c''.A).left ≫ F :=
    congrArg (fun q => q.left) (lift_snd (pushPt hFw (fst c''.A c''.A)) (pushPt hFw (snd c''.A c''.A)))
  have h₃ : F₂ ≫ φ₂ = χ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst c.A c.A).left = _ ≫ (fst c.A c.A).left
      rw [Category.assoc, hs.1, ← Category.assoc, h₁, Category.assoc, hF, hs'.1]
    · show (_ ≫ _) ≫ (snd c.A c.A).left = _ ≫ (snd c.A c.A).left
      rw [Category.assoc, hs.2, ← Category.assoc, h₂, Category.assoc, hF, hs'.2]
  refine ⟨F, hφ.cancel (by rw [hF]; exact hχ) hFw, ⟨F₂, ⟨h₁, h₂⟩, ?_⟩, fun a => ?_⟩
  · rw [← h₃] at hw'
    exact (hw'.trans c''.isLB (pull_isLB c.isLB _) (pull_isLB (pull_isLB c.isLB _) _)
      (iso_pull_pull c.isLB φ₂ F₂).symm).trans c''.isLB (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c'.isLB _)
      (iso_pull F₂ hw).symm
  · apply hp.hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hF).trans ((hl' a).trans ((Category.assoc _ _ _).trans
        ((congrArg (f' ≫ ·) (hl a).symm).trans (Category.assoc _ _ _).symm))))
    · have a₁ : (c''.lev a ^ d'').left ≫ c''.A.hom = 𝟙 S'' := Over.w (c''.lev a ^ d'')
      have a₂ : (c'.lev a ^ d').left ≫ c'.A.hom = 𝟙 S' := Over.w (c'.lev a ^ d')
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hFw).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ f') a₁).trans ((Category.id_comp _).trans ((Category.comp_id _).symm.trans
          ((congrArg (f' ≫ ·) a₂.symm).trans (Category.assoc _ _ _).symm))))))

theorem sRel_principal {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {f : S' ⟶ S} (m : SRel c' c d' d f)
    (hc : c.Principal) : c'.Principal := by
  obtain ⟨φ, pb, ⟨φ₂, sq, iso⟩, -⟩ := m
  obtain ⟨h₁, h₂⟩ := hc
  exact ⟨(pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
    (diag_iso sq iso)).2.1 h₁, nondeg_pull pb sq c.isLB c'.isLB iso h₂⟩

theorem pow_section {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (hφ : IsGrpPullback A' A f φ) (x' : 𝟙_ (Over S') ⟶ A') (x : 𝟙_ (Over S) ⟶ A)
    (e : x'.left ≫ φ = f ≫ x.left) (k : ℕ) : (x' ^ k).left ≫ φ = f ≫ (x ^ k).left := by
  have e₁ : x' = SiegelPull.secPull hφ x := by
    refine push_injective hφ _ (Over.OverMorphism.ext ?_)
    exact e.trans (SiegelPull.secPull_left hφ x).symm
  have e₂ : x' ^ k = SiegelPull.secPull hφ (x ^ k) := push_injective hφ _ (by
    rw [map_pow, e₁, push_secPull', push_secPull', MonObj.comp_pow])
  rw [e₂, SiegelPull.secPull_left]

theorem sRel_mul {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {f : S' ⟶ S} (m : SRel c' c d' d f) (e : ℕ) :
    SRel c' c (d' * e) (d * e) f := by
  obtain ⟨φ, pb, sq, hl⟩ := m
  refine ⟨φ, pb, sq, fun a => ?_⟩
  rw [pow_mul, pow_mul]
  exact pow_section pb _ _ (hl a) e

theorem sRel_calculus : ∀ (h n n' n'' : ℕ) (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B''] (ζ : B) (ζ' : B') (ζ'' : B'') (S S' S'' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (s'' : S'' ⟶ Sp B'') (c : SiegPre h n ζ s) (c' : SiegPre h n' ζ' s') (c'' : SiegPre h n'' ζ'' s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (d d' d'' : ℕ), SRel c' c d' d f → (SRel c'' c' d'' d' f' ↔ SRel c'' c d'' d (f' ≫ f)) ∧ (c.Principal → c'.Principal) ∧ ∀ e, SRel c' c (d' * e) (d * e) f :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m =>
    ⟨⟨sRel_comp m, sRel_cancel m⟩, sRel_principal m, sRel_mul m⟩

end GlobalTheory.SiegLevCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleSubquotientEmbedsDualWeylReductionMaxWeighStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_subquotient_embeds_dualWeyl_reduction_maxWeight : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (lam τ))) → GlobalTheory.HighWt.BaseChange → GlobalTheory.HighWt.CoefIn O N lam → ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], IsSimpleModule (alg O N lam) Gm → SubQ O N lam ϖ Gm → ∀ w : ι → Fin N → ℕ, (∀ τ, Antitone (w τ)) → GlobalTheory.HighWt.JointWt O N lam Gm w → (∀ w' : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w' → GlobalTheory.HighWt.pot N w' ≤ GlobalTheory.HighWt.pot N w) → Embeds O N lam (GlobalTheory.HighWt.extW N w) ϖ Gm := by
  first | exact @GlobalTheory.HighWtEmb.embeds_of_maxWeight | exact GlobalTheory.HighWtEmb.embeds_of_maxWeight | (intros; apply GlobalTheory.HighWtEmb.embeds_of_maxWeight <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianLatticeSelfDualSmulTransposeInert
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SkewScaleInert

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem latLoc_le_of_unit {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v) {n : ℕ}
    {L L' : Submodule (𝓞 E) (Fin n → E)} {s : E} (hs : w.valuation E s = 1) (hL : ∀ y ∈ L, s • y ∈ L') :
    latLoc F L v ≤ latLoc F L' v := by
  have hs0 : s ≠ 0 := fun h0 => by simp [h0] at hs
  have hu : (1 : Fv F v) ⊗ₜ[F] s⁻¹ ∈ intLoc F E v := by
    rw [InertChart.mem_intLoc_iff hw h, toCompl_tmul, map_one, one_mul]
    change Valued.v (algebraMap E (w.adicCompletion E) s⁻¹) ≤ 1
    rw [show Valued.v (algebraMap E (w.adicCompletion E) s⁻¹) = w.valuation E s⁻¹ from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _, map_inv₀, hs, inv_one]
  intro y hy
  refine latLoc_induction (p := fun y => y ∈ latLoc F L' v) (fun a ha x hx => ?_) (zero_mem _)
    (fun _ _ => add_mem) (fun _ => neg_mem) hy
  convert (latLoc F L' v).smul_mem ⟨_, hu⟩ (tmul_mem_latLoc ha (hL x hx)) using 1
  funext i
  change _ = ((1 : Fv F v) ⊗ₜ[F] s⁻¹) * (a ⊗ₜ[F] (s • x) i)
  rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel_left₀ hs0]

theorem isSelfDualAt_smul_transpose : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), W.IsSkew σ B r s →
    ∀ {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}, Formalism.UG.IsInertAt F E v w →
    ∀ (t : F), t ≠ 0 → ∀ (s₁ s₂ : E), w.valuation E s₁ = 1 → w.valuation E s₂ = 1 →
    (∀ e : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * e))) →
      s₁ * algebraMap F E t * e ∈ (algebraMap (𝓞 E) E).range) →
    (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * (s₂ * (algebraMap F E t)⁻¹)))) →
    GlobalTheory.AdelicU.IsSelfDualAt σ (algebraMap F E t • W.Jᵀ) W.L v := by
  intro F E _ _ _ _ _ σ B d W r s hX v w hw t ht s₁ s₂ hs₁ hs₂ h₁ h₂
  have h : w.under (𝓞 F) = v := GlobalTheory.LFun.under_eq_of_isInertAt hw
  have ht0 : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
  have hdet : (algebraMap F E t • W.Jᵀ).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ ht0) (GlobalTheory.SkewFrameInert.det_ne_zero hX)
  have hform : ∀ (c : E) (y x : Fin d → E), form σ W.J (c • y) x = c * form σ W.J y x := by
    intro c y x
    simp [form, smul_dotProduct]
  unfold IsSelfDualAt
  rw [← SelfDual.latLoc_dualGlob hdet hX.lat]
  refine le_antisymm (latLoc_le_of_unit hw h hs₁ fun y hy x hx => ?_) (latLoc_le_of_unit hw h hs₂ fun y hy => ?_)
  · rw [GlobalTheory.SkewFrameInert.hE_smul_transpose, hform,
      show algebraMap F E t * (s₁ * form σ W.J y x) = s₁ * algebraMap F E t * form σ W.J y x by ring]
    exact h₁ _ ((hX.dual y).1 hy x hx)
  · refine (hX.dual (s₂ • y)).2 fun x hx o => ?_
    obtain ⟨c, hc⟩ := hy x hx
    rw [GlobalTheory.SkewFrameInert.hE_smul_transpose] at hc
    have e : (o : E) * form σ W.J (s₂ • y) x = ((o * c : 𝓞 E) : E) * (s₂ * (algebraMap F E t)⁻¹) := by
      have hoc : ((o * c : 𝓞 E) : E) = (o : E) * (c : E) := map_mul (algebraMap (𝓞 E) E) o c
      have hc' : (c : E) = algebraMap F E t * form σ W.J y x := hc
      rw [hform, hoc, hc']
      field_simp
    rw [e]
    exact h₂ (o * c)

end GlobalTheory.SkewScaleInert
end
end

