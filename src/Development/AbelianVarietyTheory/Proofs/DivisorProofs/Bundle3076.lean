import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousLatticeVectorsAlongArc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0797
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0780
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0685
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0686
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0680
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralOfIntegralAtFibreGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.intAt_of_intAt_fibreGeneric : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k) (x ζ : G.left), G.hom ζ = G.hom x → (∀ z, G.hom z = G.hom x → ζ ⤳ z) → IntAt L α s ζ → IntAt L α s x := by
  intro R _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s x ζ hζ hgen hint
  have hx : x ∈ (⨆ i, L.U i) := by rw [hL.cover]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := G.hom x) (U := ⊤) trivial
  obtain ⟨W, hW, hxW, hWle⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := L.U j ⊓ G.hom ⁻¹ᵁ U) ⟨hj, hxU⟩
  have hζW : ζ ∈ W := (hgen x rfl).mem_open W.isOpen hxW
  have hWj : W ≤ L.U j := fun z hz => (hWle hz).1
  have hWU : W ≤ G.hom ⁻¹ᵁ U := fun z hz => (hWle hz).2
  obtain ⟨c', hxc', hc'⟩ := GlobalTheory.T.isIntegralElem_near_fibre_of_generic_point R M G hsm hqc hgi Y α t hpb W hW U hU hWU (chartVal L α s j W hWj) x ζ hxW hζ hgen
    (GlobalTheory.T.exists_basicOpen_integral_of_integral_at_point L α k s ζ hint j W hWj hW hζW)
  refine ⟨j, G.left.basicOpen c', (G.left.basicOpen_le c').trans hWj, hxc', hW.basicOpen c', ?_⟩
  convert hc' using 1
  simp only [chartVal]
  erw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationKillsMixedSectionSumsLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_relation_kills_mixed_section_sums_level : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Over₀ U₁ U₂ a b → ∀ (u : ∀ χ, LB.Gen (CmpLB D₁.toPre D₂.toPre b (h χ) χ)), (∀ χ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G₁).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → val ((U₂.gt e).t χ) (x ≫ ((Over.pullback (thick R I e)).map a).left) z (rr J) = val ((U₁.gt e).t (h χ)) x z (rl J) * val (u χ) (x ≫ (U₁.gt e).pG.left) z J) → ∀ (j j' e : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} → LB.Sec (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j'))), (∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) * (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) * (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val)) → ∀ (α : D₁.toPre.X), ∃ S : Finset {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}, ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D₁.toPre.P.A).left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J → (∀ i ∉ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0) ∧ ∑ i ∈ S, sval (m α i) (r ≫ (D₁.toPre.prBe I e).left) z J = 0 := by
  first | exact @GlobalTheory.Mum.Two.Mix.level | exact GlobalTheory.Mum.Two.Mix.level | (intros; apply GlobalTheory.Mum.Two.Mix.level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrallyClosedPointExtension
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem exists_weil_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l' : Level H)
    (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ)
    [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X)
      (y : Sp (FractionRing R) ⟶ Xo'.XF c'), spMap (algebraMap R (FractionRing R)) ≫ ξ = y ≫ Y.j → ∀ a : Dw.La,
    ∃ κ : (Sp (FractionRing R) ⟶ Y.t.G.left) → Rˣ, GlobalTheory.HTMap.Mult Y.t ξ (p ^ n) κ ∧
      ∀ (P' : GlobalTheory.HTMap.FP Y.t ξ (p ^ n)) (b : P'.Bˣ), P'.Gl κ b → ∀ (x0 : R →+* 𝓞_ℂ_[p])
        (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left),
        PtOn Y (spMap x0 ≫ ξ) yy P π ψ → ∀ tt : P.T, (tt.lev n).left ≫ ψ = yy ≫ (Y.oF.etaA a).left →
        ∀ (β : P'.B →+* 𝓞_ℂ_[p]) (w : Sp 𝓞_ℂ_[p] ⟶ Y.t.G.left), P'.At x0 w β →
        ∀ z : GlobalTheory.ChTor.Pts P.A.A, z.left ≫ P.gen ≫ π = spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ w →
          algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = (weil P.A (p ^ n) (tt.lev n) z : ℂ_[p]) := by
  intro E _ _ _ H Dw l' Xo' c' W Y p _ n _ hstar hpW hA R _ _ _ ξ y hy a
  obtain ⟨κ, hκM, hκW⟩ := GlobalTheory.T.integrally_closed_generic_extension E H Dw l' Xo' c' W Y p n hA R ξ y hy a
  refine ⟨κ, hκM, ?_⟩
  intro P' b hb x0 yy P π ψ hPt tt hlev β w hAt z hz
  have hAt' := hAt.map (algebraMap 𝓞_ℂ_[p] ℂ_[p])
  obtain ⟨φ, hφ⟩ := GlobalTheory.HTMap.FP.ex_lift (P := P') hAt'.unit
  rw [← hφ] at hAt'
  obtain ⟨σ, hσ⟩ := hAt'.sect
  let wf : Over.mk (spMap (algebraMap R (Localization.Away P'.f)) ≫ ξ) ⟶ Y.t.G :=
    GlobalTheory.HTMap.mkPt (spMap σ.toRingHom ≫ P'.u.left) (P'.at_sect σ).over
  have hwf : wf ^ (p ^ n) = 1 := (P'.at_sect σ).tors (w := wf)
  have hgl := hb.1 _ _ (P'.at_sectK σ)
  have hsb : σ b = algebraMap R (Localization.Away P'.f) (κ (spMap (P'.toK.comp σ.toRingHom) ≫ P'.u.left)) := by
    apply P'.toK_inj
    rw [← RingHom.comp_apply P'.toK (algebraMap R _), P'.toK_comp]
    exact hgl
  let eyy : Over.mk yy ⟶ Y.oF.t.G := Over.homMk (yy ≫ (Y.oF.etaA a).left) (by
    rw [Category.assoc, Over.w (Y.oF.etaA a)]; exact Category.comp_id _)
  let σyy : Over.mk yy ⟶ Y.oF.t.G := Over.homMk (z.left ≫ ψ) (by
    rw [Category.assoc, hPt.2.2.2.1.1.w, ← Category.assoc, Over.w z]; simp)
  have hσyy : σyy.left ≫ Y.m.φ = spMap φ ≫ wf.left := by
    show (z.left ≫ ψ) ≫ Y.m.φ = spMap φ ≫ spMap σ.toRingHom ≫ P'.u.left
    rw [Category.assoc, hPt.2.2.2.2.1, hz, ← hAt'.2, hσ]
    exact (GlobalTheory.HTMap.spc_assoc _ _ _).symm
  obtain ⟨hσt, hW⟩ := GlobalTheory.T.integrally_closed_point_level_extends E H Dw l' Xo' c' W Y p n hpW hA R ξ y hy a κ hκW P'.f wf hwf P'.toK P'.toK_comp x0 φ hφ
    yy hPt.1 eyy σyy rfl hσyy
  have hc := GlobalTheory.T.p_adic_point_lattice_evaluation E H Dw l' Xo' c' W Y p n _ yy P π ψ hPt a tt hlev z eyy σyy rfl rfl hσt _ hW
  rw [← hc]
  have e1 : spMap P'.toK ≫ wf.left = spMap (P'.toK.comp σ.toRingHom) ≫ P'.u.left := GlobalTheory.HTMap.spc_assoc _ _ _
  rw [e1]
  show algebraMap 𝓞_ℂ_[p] ℂ_[p] (β b) = ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp x0) _
  rw [← hφ, RingHom.comp_apply, ← hsb]
  exact RingHom.congr_fun hσ _

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

theorem diffVanish_chiPic_structureModule {K : Type} [Field K] (A : AbVar K) :
    letI := A.algΓ
    DiffVanish (A.dim + 1) (chiPic K (QCoh.structureModule A.X.left)) := by
  letI := A.algΓ
  refine diffVanish_chiPic_of_isProjOver (f := A.X.hom) (fun r => rfl) _
    (GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A).2 ?_
  refine (QCoh.suppDim_le _).trans ?_
  rw [GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A]

theorem inter_update_add {K : Type} [Field K] (A : AbVar K) {J : Type} [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = A.dim) (c : J → Pic A.X.left) (i : J) (a b : Pic A.X.left) :
    inter A (Function.update c i (a + b)) = inter A (Function.update c i a) + inter A (Function.update c i b) := by
  letI := A.algΓ
  exact congrFun ((diffVanish_chiPic_structureModule A).multiDiff_update_add_of_le_card hJ.ge c i a b) 0

def interAdd {K : Type} [Field K] (A : AbVar K) {J : Type} [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = A.dim) (c : J → Pic A.X.left) (i : J) : Pic A.X.left →+ ℤ :=
  AddMonoidHom.mk' (fun a => inter A (Function.update c i a)) (inter_update_add A hJ c i)

theorem inter_comp_equiv {K : Type} [Field K] (A : AbVar K) {J J' : Type} [Fintype J] [Fintype J']
    (e : J' ≃ J) (c : J → Pic A.X.left) : inter A (c ∘ e) = inter A c := by
  letI := A.algΓ
  exact congrFun (multiDiff_comp_equiv e c _) 0

theorem inter_multilinear_and_symm : ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J], Fintype.card J = A.dim → (∃ M : MultilinearMap ℤ (fun _ : J => Pic A.X.left) ℤ, ∀ c, M c = inter A c) ∧ ∀ (J' : Type) [Fintype J'] (e : J' ≃ J) (c : J → Pic A.X.left), inter A (c ∘ e) = inter A c := by
  intro K _ A J _ hJ
  classical
  refine ⟨⟨MultilinearMap.mk' (fun c => inter A c) (fun c i a b => inter_update_add A hJ c i a b)
    (fun c i n a => map_zsmul (interAdd A hJ c i) n a), fun c => rfl⟩, fun J' _ e c => inter_comp_equiv A e c⟩

end GlobalTheory.AV.AbVar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackNotSurjectiveEqZero
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar

theorem hom_genericPoint_ne {K : Type} [Field K] {A B : AbVar K} (f : A ⟶ B) [IsIntegral A.X.left]
    [IsIntegral B.X.left] (hns : ¬ Surjective f.hom.left) :
    f.hom.left (genericPoint A.X.left) ≠ genericPoint B.X.left := by
  intro h
  apply hns
  have : IsProper A.X.hom := A.ab.proper
  have : IsProper B.X.hom := B.ab.proper
  have hw : f.hom.left ≫ B.X.hom = A.X.hom := Over.w f.hom
  have : IsProper (f.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
  have : IsProper f.hom.left := IsProper.of_comp _ B.X.hom
  have hcl : IsClosed (Set.range f.hom.left) := by
    rw [← Set.image_univ]; exact f.hom.left.isClosedMap _ isClosed_univ
  have hsub : closure ({genericPoint B.X.left} : Set B.X.left) ⊆ Set.range f.hom.left :=
    hcl.closure_subset_iff.2 (Set.singleton_subset_iff.2 ⟨_, h⟩)
  rw [(genericPoint_spec B.X.left).def] at hsub
  exact ⟨fun y => hsub (Set.mem_univ y)⟩

theorem inter_pull_eq_zero_of_not_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → ¬ Surjective f.hom.left → ∀ (J : Type) [Fintype J], Fintype.card J = A.dim → ∀ c : J → Pic B.X.left, inter A (fun j => CechPic.pull f.hom.left (c j)) = 0 := by
  intro K _ A B f hdim hns J _ hJ c
  haveI := (GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K A).1
  haveI := (GlobalTheory.AV.AbVar.isIntegral_isLocallyNoetherian_compactSpace K B).1
  letI := A.algΓ
  obtain ⟨hs, hp⟩ := GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A
  choose L hL hc using fun j => cls_surj (c j)
  have hne := hom_genericPoint_ne f hns
  have hη : genericPoint B.X.left ∈ (closure ({f.hom.left (genericPoint A.X.left)} : Set B.X.left))ᶜ :=
    fun h => hne (((specializes_iff_mem_closure.2 h).antisymm (genericPoint_specializes _)).eq)
  have h1 := GlobalTheory.PullVanish.dim_closure_add_one_le (genericPoint_specializes (f.hom.left (genericPoint A.X.left)))
    isClosed_closure.isOpen_compl hη (fun h => h (subset_closure rfl))
  have h2 : topologicalKrullDim (closure ({genericPoint B.X.left} : Set B.X.left)) = topologicalKrullDim B.X.left := by
    rw [(genericPoint_spec B.X.left).def]
    exact (Homeomorph.Set.univ B.X.left).isHomeomorph.topologicalKrullDim_eq
  have hB : topologicalKrullDim B.X.left ≤ (A.dim : ℕ) := by
    rw [GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K B, hdim]
  have h3 := GlobalTheory.PullVanish.withBot_lt_of_add_one_le_nat (h1.trans (h2.trans_le hB))
  have hA : topologicalKrullDim A.X.left ≤ ((0 + A.dim : ℕ) : WithBot ℕ∞) := by
    rw [Nat.zero_add, GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A]
  let e : Fin 0 ⊕ Fin A.dim ≃ J := (Equiv.emptySum (Fin 0) (Fin A.dim)).trans (Fintype.equivFinOfCardEq hJ).symm
  have h := GlobalTheory.PullVanish.interNum_pull_eq_zero K 0 A.dim A.X.left B.X.left (hs ▸ hp) hA f.hom.left h3
    (fun i => i.elim0) (fun i => i.elim0) (fun a => L (e (.inr a))) (fun a => hL _)
  have hL' : ∀ j, ((L j).pull f.hom.left).IsLB := fun j => pull_isLB (hL j) _
  have hcl : (fun j => CechPic.pull f.hom.left (c j)) = fun j => cls ((L j).pull f.hom.left) (hL' j) := by
    funext j; rw [← hc j]; rfl
  rw [inter, hcl, ← interNum_eq_multiDiff K _ hL', ← interNum_comp_equiv K _ hL' e, ← h]
  congr 1
  funext x
  rcases x with i | a
  · exact i.elim0
  · rfl

end GlobalTheory.AV.AbVar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantsOfTrivialOnThickenings
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.InvAlg

theorem invariants_of_trivial_on_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C ∧ Module.Finite C C' ∧ ∃ f : C, f - 1 ∈ (maximalIdeal R).map (algebraMap R C) ∧ (∀ x : C', ∃ n : ℕ, (f : C') ^ n * x ∈ Set.range (Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') fun _ _ => Commute.all _ _)) ∧ (∀ t : TensorProduct R C R', Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = 0 → ∃ n : ℕ, ((f ^ n) ⊗ₜ[R] (1 : R')) * t = 0) ∧ ∀ e, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C))) := by
  intro R _ _ _ hR R' _ _ _ _ hinj hGal C' _ _ _ _ _ act hact O _ _ _ _ i hi1 hi2 hi3 C hC
  haveI : IsNoetherianRing R := hR.1
  haveI : Finite (Gal (algebraMap R R')) := hGal.1
  haveI : Algebra.FiniteType R C' := Algebra.FiniteType.trans (S := R') inferInstance inferInstance
  obtain ⟨hft, hfin⟩ := GlobalTheory.T.finiteType_invariants_finite_group_and_finite R C' (Gal (algebraMap R R')) act C hC
  have hg := GlobalTheory.T.completion_galoisInvariants_agree_mod_maxIdeal_pow R hR R' hinj hGal C' act hact O i hi1 hi2 hi3 C hC hft hfin
  choose gm hgc using hg
  obtain ⟨hs, hinj'⟩ := GlobalTheory.T.tensor_quotient_onto_and_injective_mod_ideal_pow R (maximalIdeal R) R' C' O i hi3 C gm hgc
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  obtain ⟨f, hf1, hf2, hf3⟩ := GlobalTheory.T.exists_unit_approximation_adic_completion C ((maximalIdeal R).map (algebraMap R C)) (TensorProduct R C R') C' _ hs hinj'
  have hL : ∀ t, Algebra.TensorProduct.lift (Algebra.ofId C C') (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t = Algebra.TensorProduct.lift C.val (IsScalarTower.toAlgHom R R' C') (fun _ _ => Commute.all _ _) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  refine ⟨hft, hfin, f, hf1, fun x => ⟨1, ?_⟩, fun t ht => ⟨1, ?_⟩, fun e => ⟨gm e⟩⟩
  · obtain ⟨t, ht⟩ := hf2 x
    exact ⟨t, by rw [← hL]; simpa using ht⟩
  · have := hf3 t (by rw [hL]; exact ht)
    rw [pow_one]
    rwa [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at this

end GlobalTheory.InvAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExponentialOfSemiAbelianFibreLinearChange
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj
open GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix

namespace GlobalTheory.ShFam.Hor.LogCh

theorem isExpAt_mulVec {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (X : Scheme.{0}) (t : SAB H X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G))
    (M : Matrix (Fin g) (Fin g) ℂ) (hM : IsUnit M.det) (hhol : IsHolTo Set.univ (fun z => (e z).left))
    (he : IsExpAt t y e) : IsExpAt t y (fun w => e (M *ᵥ w)) := by
  have hchain : ∀ w v, IsDerivAt0 (fun u => (e (M *ᵥ u)).left) w v ↔
      IsDerivAt0 (fun u => (e u).left) (M *ᵥ w) v := by
    intro w v
    rw [GlobalTheory.HolHom.isDerivAt0_iff, GlobalTheory.HolHom.isDerivAt0_iff]
    exact GlobalTheory.ShFam.BdArc.LatSec.isDerivAt_comp_iff (GlobalTheory.HolHom.holAt_of_isHolTo hhol (Set.mem_univ 0))
      (Matrix.mulVecLin M).toContinuousLinearMap w v
  have hMi : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have hiM : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  refine ⟨fun v w => ?_, fun w => ?_, fun v hv => ?_⟩
  · simp only [Matrix.mulVec_add]
    exact he.1 _ _
  · simp_rw [hchain]
    exact he.2.1 (M *ᵥ w)
  · obtain ⟨w', hw', huniq⟩ := he.2.2 v hv
    refine ⟨M⁻¹ *ᵥ w', ?_, fun w₂ hw₂ => ?_⟩
    · show IsDerivAt0 (fun u => (e (M *ᵥ u)).left) (M⁻¹ *ᵥ w') v
      rw [hchain, Matrix.mulVec_mulVec, hMi, Matrix.one_mulVec]
      exact hw'
    · have h2 : M *ᵥ w₂ = w' := huniq _ ((hchain w₂ v).1 hw₂)
      rw [← h2, Matrix.mulVec_mulVec, hiM, Matrix.one_mulVec]

end GlobalTheory.ShFam.Hor.LogCh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteOfSurjectiveOfDimEqStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_of_surjective_of_dim_eq' : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B), A.dim = B.dim → Surjective f.hom.left → IsFinite f.hom.left := by
  first | exact @GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq | exact GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq | (intros; apply GlobalTheory.AV.AbVar.isFinite_of_surjective_of_dim_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormOneAddMulSmul
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_one {i : A.ι} {v : V n} (hv : v ∈ (A.e i).target) : A.loc 1 i v = 1 := by
  rw [HolAtlas.loc, dif_pos hv]; rfl

theorem loc_add (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α + β) i v = A.loc α i v + A.loc β i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dif_pos hv, dif_pos hv, dif_pos hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dif_neg hv, dif_neg hv, dif_neg hv, add_zero]

theorem loc_mul (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α * β) i v = A.loc α i v * A.loc β i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dif_pos hv, dif_pos hv, dif_pos hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, HolAtlas.loc, dif_neg hv, dif_neg hv, dif_neg hv, mul_zero]

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) (v : V n) : A.loc (c • α) i v = c • A.loc α i v := by
  by_cases hv : v ∈ (A.e i).target
  · rw [HolAtlas.loc, HolAtlas.loc, dif_pos hv, dif_pos hv]; rfl
  · rw [HolAtlas.loc, HolAtlas.loc, dif_neg hv, dif_neg hv, smul_zero]

theorem isForm_algebra : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n), A.IsForm 1 ∧
    ∀ (c : ℂ) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α + β) ∧ A.IsForm (α * β) ∧ A.IsForm (c • α) := by
  intro M _ n A
  refine ⟨⟨fun i S => ?_, fun x x' _ => ?_⟩, fun c α β hα hβ => ⟨⟨fun i S => ?_, fun x x' h => ?_⟩,
    ⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩⟩
  · exact (contDiffOn_const (c := (bas n).repr (1 : Alt n) S)).congr fun v hv => by
      rw [loc_one A hv]
  · exact (map_one _).symm
  · exact ((hα.smooth i S).add (hβ.smooth i S)).congr fun v _ => by
      rw [loc_add, map_add, Finsupp.add_apply]
  · change α x + β x = pull _ (α x' + β x')
    rw [map_add, ← hα.compat x x' h, ← hβ.compat x x' h]
  · exact ((GlobalTheory.T.contDiffOn_coefficients_complexForm_mul n n (A.loc α i) (A.loc β i)).1 _ (hα.smooth i) (hβ.smooth i) S).congr fun v _ => by
      rw [loc_mul]
  · change α x * β x = pull _ (α x' * β x')
    rw [map_mul, ← hα.compat x x' h, ← hβ.compat x x' h]
  · exact ((hα.smooth i S).const_smul c).congr fun v _ => by
      rw [loc_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
  · change c • α x = pull _ (c • α x')
    rw [map_smul, ← hα.compat x x' h]

end GlobalTheory.CxForm.HolAtlas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicUnitMatrixAtRationalMatrixValuesStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (s : ℕ) (T : Matrix (Fin s) (Fin s) X.Fn) (y : CxPts X.str σ), (∀ i j, RegAt (under y) (T i j)) → T.det ≠ 0 → RegAt (under y) (T.det)⁻¹ → HolUnitAt (atlas X σ) (fun z => T.map (ratVal · z)) y := by
  first | exact @GlobalTheory.ChernCalc.holUnitAt_ratVal | exact GlobalTheory.ChernCalc.holUnitAt_ratVal | (intros; apply GlobalTheory.ChernCalc.holUnitAt_ratVal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfIsIsoOnGeometricFibresOfSmoothStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_of_isIso_on_geometric_fibres_of_smooth : ∀ (T X Z : Scheme.{0}) (p : X ⟶ T) (q : Z ⟶ T) (h : X ⟶ Z) (hh : h ≫ q = p), Smooth p → Smooth q → (∀ s : T, ∃ (Ω : Type) (_ : Field Ω) (x : Sp Ω ⟶ T), s ∈ Set.range x ∧ IsIso (pullback.map p x q x h (𝟙 _) (𝟙 _) (by simp [hh]) (by simp))) → IsIso h := by
  first | exact @GlobalTheory.Mum.isIso_of_isIso_fibres | exact GlobalTheory.Mum.isIso_of_isIso_fibres | (intros; apply GlobalTheory.Mum.isIso_of_isIso_fibres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenFlagBundleCellAndCoordsRegular
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem isOpen_setOf_mem_frames {F Ω ι : Type} [Field F] [Field Ω] [Algebra F Ω] [Finite ι] {m k : ι → ℕ}
    {M : GlobalTheory.ZH.RatModel F Ω} (S : Fr M m k) (B : Mat m Ω) : IsOpen {z : M.Z | B ∈ S.S z} := by
  have hP (g : Mat m Ω) : IsOpen {z : M.Z | Par k (M.O z).toSubring g} := by
    have : {z : M.Z | Par k (M.O z).toSubring g} = ⋂ τ, ((⋂ i, ⋂ j, {z : M.Z | g τ i j ∈ M.O z}) ∩
        ({_z : M.Z | (g τ).det ≠ 0} ∩ ({z : M.Z | (g τ).det⁻¹ ∈ M.O z} ∩
          {_z : M.Z | ∀ i j : Fin (m τ), (i : ℕ) < k τ → i < j → g τ i j = 0}))) := by
      ext z
      simp only [Par, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
      rfl
    rw [this]
    exact isOpen_iInter_of_finite fun τ => (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      M.isOpen_setOf_mem_O _).inter (isOpen_const.inter ((M.isOpen_setOf_mem_O _).inter isOpen_const))
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨U, A, hzU, -, hU⟩ := S.loc z
  exact ⟨(U : Set M.Z) ∩ {z' | Par k (M.O z').toSubring (B * A⁻¹)}, fun w hw => (hU w hw.1 B).2 hw.2,
    U.isOpen.inter (hP _), hzU, (hU z hzU B).1 hz⟩

theorem isOpen_inCell_and_regAt : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f →
    ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), IsOpen {y : Y.X | InCell E E' φ f A u y} ∧
      ∀ y, InCell E E' φ f A u y → ∀ j, RegAt y (u j) := by
  intro F _ X Y ι _ m E E' φ f hR A u
  refine ⟨((isOpen_setOf_mem_frames E A).preimage f.continuous).inter (isOpen_setOf_mem_frames E' _), ?_⟩
  rintro y ⟨hA, hu⟩ ⟨τ, ⟨b, a⟩, hab⟩
  have h := hR.sub y _ hu A hA
  have hd : ∀ τ, (A.map φ τ).det ≠ 0 := fun τ => by
    have := Mat.det_map A (φ : X.Fn →+* Y.Fn) τ
    exact this.trans_ne ((map_ne_zero _).2 (Fr.det_ne hA τ))
  rw [mul_assoc, Mat.mul_inv hd, mul_one] at h
  have h2 := (h τ).1 a b
  have hab' : a < b := hab
  have e : upM u τ a b = u ⟨τ, ⟨(b, a), hab⟩⟩ := by
    simp only [upM, upU, Matrix.of_apply, dif_pos hab']
  rw [e] at h2
  exact mem_O_ratOf.1 h2

end GlobalTheory.FlagCell2
end

