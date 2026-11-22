import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0082
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3157
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3060
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
import Development.AbelianVarietyTheory.Statements.HaarFundamentalDomain.ExistsHaarFundDom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0823
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0349
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0665
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0662
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3625
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartEqOfSameGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section
namespace GlobalTheory.TInj

theorem tautChart_eq_of_genPt : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (θ₁ θ₂ : C.R →+* R'), IsCN R' → Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ (κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing C.R)), κ₁ ≫ jK C.R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK C.R = jK R' ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → spMap (θ₁.comp C.iw) ≫ C.u = spMap (θ₂.comp C.iw) ≫ C.u ∧ (θ₁.comp C.iw = θ₂.comp C.iw → ∀ k, θ₁ (C.s k) = θ₂ (C.s k)) := by
  intro g n φ hn F C G₁ _ _ y α₁ hC R' _ _ _ θ₁ θ₂ hR' hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨hsa, -, -, hM, hys⟩ := hC
  have hn1 : 1 ≤ n := by omega
  have hCN : IsCN C.R := hM.isCN
  obtain ⟨R₁, _, _, _, ρ, D, e', hR₁, hρ, hρf, hρl, href⟩ := GlobalTheory.T.exists_refinement_tautologicalChart_finiteExtension hn1 C hCN
  obtain ⟨β, ββ, w, hFrom⟩ := GlobalTheory.T.comesFromBase_of_refines_polarisedData C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n C.R R₁ ρ C.iw C.s C.Q C.e D.toPre e' hρ C.data href
  obtain ⟨G₀, _, _, π, A₀, U₀, hU⟩ := hM.unif R₁ ρ hR₁ hρ hρf D e' href
  obtain ⟨hπ, κρ, πK, α₀, α₂, hκρ, -, hA, hsq, hL, -⟩ := hU
  have hsa₀ : IsSemiAbelian G₀ := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hπ hsa
  obtain ⟨V, _, _, _, _, η', f₁, f₂, hVc, hη', hf₁, hf₂, hlf₁, hlf₂, hc₁, hc₂⟩ :=
    exists_cDvr_two_embeddings C.R R₁ R' ρ hρ hρf hR' θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂
  obtain ⟨κf₁, hκf₁⟩ := exists_genericMap hf₁
  obtain ⟨κf₂, hκf₂⟩ := exists_genericMap hf₂
  obtain ⟨κη, hκη⟩ := exists_genericMap hη'
  have e₁ : κf₁ ≫ κρ = κη ≫ κ₁ := GlobalTheory.T.genericPointMap_over_ringHom_unique (f₁.comp ρ) _ _
    (by rw [Category.assoc, hκρ, ← Category.assoc, hκf₁, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₁, ← Category.assoc, hκη, Category.assoc, ← spMap_comp, hc₁])
  have e₂ : κf₂ ≫ κρ = κη ≫ κ₂ := GlobalTheory.T.genericPointMap_over_ringHom_unique (f₂.comp ρ) _ _
    (by rw [Category.assoc, hκρ, ← Category.assoc, hκf₂, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₂, ← Category.assoc, hκη, Category.assoc, ← spMap_comp, hc₂])
  have hy₀ : κf₁ ≫ (κρ ≫ y) = κf₂ ≫ (κρ ≫ y) := by
    rw [← Category.assoc, e₁, Category.assoc, hy, ← Category.assoc, ← e₂, Category.assoc]
  have hmap : ∀ f : R₁ →+* V, IsLocalHom f → (maximalIdeal R₁).map f ≤ maximalIdeal V := fun f hf =>
    Ideal.map_le_iff_le_comap.mpr fun x hx => (mem_maximalIdeal _).2 (map_nonunit f x ((mem_maximalIdeal _).1 hx))
  haveI : CharZero R₁ := hR₁.2.2.2
  obtain ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ', hE₁, hE₂, hMatch, hpairs⟩ :=
    GlobalTheory.T.uniformisation_pullbacks_match_torsionPairs F.univ (GlobalTheory.LowChart.isUnit_zetaAway n hn) hn1 R₁ (maximalIdeal R₁)
      ⟨hR₁.1, inferInstance, hR₁.2.1, hR₁.2.2.1⟩ D A₀ G₀ U₀ hsa₀ (κρ ≫ y) α₀ ⟨hA, α₂, hsq, hL⟩ V hVc f₁ f₂ hf₁ hf₂
      (hmap f₁ hlf₁) (hmap f₂ hlf₂) κf₁ κf₂ hκf₁ hκf₂ hy₀
  obtain ⟨ββ₁, w₁, hFrom₁⟩ := GlobalTheory.T.comesFromBase_of_pullback_injective_domains C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ V
    (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₁ D₁.toPre hD₁ hf₁ hFrom
  obtain ⟨ββ₂, w₂, hFrom₂⟩ := GlobalTheory.T.comesFromBase_of_pullback_injective_domains C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ V
    (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₂ D₂.toPre hD₂ hf₂ hFrom
  have hne₀ : ∀ k, ρ (C.s k) ≠ 0 := fun k => (map_ne_zero_iff ρ hρ).2 (C.s_ne_zero k)
  have htaut : ∀ a : Fin C.T.r → ℤ, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) n)
      (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) n),
      p₁.y = (hD₁.xe.trans (e'.trans C.e)).symm a ∧
      TautPt C.T (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n
        D₁.toPre (hD₁.xe.trans (e'.trans C.e)) ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
        (AlgebraicClosure (FractionRing V)) a p₁.g ∧
      p₂.y = (hD₂.xe.trans (e'.trans C.e)).symm a ∧
      TautPt C.T (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n
        D₂.toPre (hD₂.xe.trans (e'.trans C.e)) ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂
        (AlgebraicClosure (FractionRing V)) a p₂.g ∧ QImg b φ' p₁ p₂ := by
    intro a
    obtain ⟨p₀, hp₀y, hp₀⟩ := GlobalTheory.T.periodPart_mem_tautologicalPoint_torsion C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ D.toPre
      (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w D.tau_bimult hFrom hne₀
      (AlgebraicClosure (FractionRing R₁)) a
    obtain ⟨p₁, p₂, hp₁y, hTr₁, hp₂y, hTr₂, hQ⟩ := hpairs p₀
    refine ⟨p₁, p₂, ?_, ?_, ?_, ?_, hQ⟩
    · rw [hp₁y, hp₀y]; rfl
    · exact GlobalTheory.T.tautologicalPoint_transport_fieldMap C.T _ n R₁ V (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₁
        D₁.toPre hD₁ ββ₁ w₁ hf₁ D₁.tau_bimult hFrom hFrom₁ _ _ j₁ hE₁ a p₀.g p₁.g hp₀ hTr₁
    · rw [hp₂y, hp₀y]; rfl
    · exact GlobalTheory.T.tautologicalPoint_transport_fieldMap C.T _ n R₁ V (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₂
        D₂.toPre hD₂ ββ₂ w₂ hf₂ D₂.tau_bimult hFrom hFrom₂ _ _ j₂ hE₂ a p₀.g p₂.g hp₀ hTr₂
  have hlev := GlobalTheory.T.exists_level_point_pairs_lower_base C.toLowBase hn1 R₁ V (maximalIdeal R₁) (maximalIdeal V) D D₁ D₂ (ρ.comp C.iw) β hFrom.1
    f₁ f₂ hD₁ hD₂ (AlgebraicClosure (FractionRing R₁)) (AlgebraicClosure (FractionRing V)) j₁ j₂ b φ' hE₁ hE₂ hpairs
  have hloc : ∀ f : R₁ →+* V, IsLocalHom f → ∀ x, x ∈ maximalIdeal C.R → f (ρ x) ∈ maximalIdeal V := fun f hf x hx =>
    (mem_maximalIdeal _).2 (map_nonunit f _ (map_nonunit ρ x ((mem_maximalIdeal _).1 hx)))
  have hbd₁ : ∀ k, f₁ (ρ (C.s (.inl k))) ∈ maximalIdeal V ∧ f₁ (ρ (C.s (.inl k))) ≠ 0 := fun k =>
    ⟨hloc f₁ hlf₁ _ (C.bd k), (map_ne_zero_iff f₁ hf₁).2 (hne₀ _)⟩
  have hbd₂ : ∀ k, f₂ (ρ (C.s (.inl k))) ∈ maximalIdeal V ∧ f₂ (ρ (C.s (.inl k))) ≠ 0 := fun k =>
    ⟨hloc f₂ hlf₂ _ (C.bd k), (map_ne_zero_iff f₂ hf₂).2 (hne₀ _)⟩
  have hu₁ : ∀ k, IsUnit (f₁ (ρ (C.s (.inr k)))) := fun k => ((C.tor k).map ρ).map f₁
  have hu₂ : ∀ k, IsUnit (f₂ (ρ (C.s (.inr k)))) := fun k => ((C.tor k).map ρ).map f₂
  have hfin1 := GlobalTheory.T.tautological_lattice_identification_eq_id C.T φ C.m C.N n (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) hn C.cone C.defin V
    D₁.toPre D₂.toPre (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ hbd₁ hu₁ hbd₂ hu₂ hMatch htaut
  have hb := GlobalTheory.T.structureMap_eq_of_same_genericImage_moduli F.s y C.b hys θ₁ θ₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have k₁ : f₁.comp (ρ.comp C.iw) = η'.comp (θ₁.comp C.iw) := by
    rw [← RingHom.comp_assoc, hc₁, RingHom.comp_assoc]
  have k₂ : f₂.comp (ρ.comp C.iw) = η'.comp (θ₂.comp C.iw) := by
    rw [← RingHom.comp_assoc, hc₂, RingHom.comp_assoc]
  have hbase : (f₁.comp (ρ.comp C.iw)).comp C.toLowBase.T.b = (f₂.comp (ρ.comp C.iw)).comp C.toLowBase.T.b := by
    rw [k₁, k₂]
    change η'.comp (θ₁.comp C.b) = η'.comp (θ₂.comp C.b)
    rw [hb]
  obtain ⟨hU', hβeq⟩ := GlobalTheory.T.siegelFibrePower_point_eq_of_matching_lower_data C.toLowBase hn (GlobalTheory.LowChart.isUnit_zetaAway n hn) (isUnit_natCast (by omega))
    (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) V
    D₁.toPre D₂.toPre (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ hbase hMatch hfin1 htaut hlev
  refine ⟨GlobalTheory.T.specMap_comp_eq_of_comp_injective_localScheme C.u (θ₁.comp C.iw) (θ₂.comp C.iw) η' hη' (by rw [← k₁, ← k₂]; exact hU'), fun heq k => ?_⟩
  have hω : f₁.comp (ρ.comp C.iw) = f₂.comp (ρ.comp C.iw) := by rw [k₁, k₂, heq]
  have hβ₂ := hβeq hω
  rw [← hω] at hFrom₂ htaut
  have hs := GlobalTheory.T.tautological_coords_eq_of_matching_data C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n V (f₁.comp (ρ.comp C.iw))
    D₁.toPre D₂.toPre (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    hn1 ⟨C.ε, fun _ => rfl⟩ D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ (fun k => (map_ne_zero_iff f₁ hf₁).2 (hne₀ k))
    (fun k => (map_ne_zero_iff f₂ hf₂).2 (hne₀ k)) hMatch hfin1 hβ₂ htaut
  have h1 := congrFun hs k
  have h2 := DFunLike.congr_fun hc₁ (C.s k)
  have h3 := DFunLike.congr_fun hc₂ (C.s k)
  simp only [RingHom.comp_apply] at h1 h2 h3
  exact hη' (by rw [← h2, ← h3]; exact h1)

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntNeZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.ChainFr MeasureTheory

noncomputable section

namespace GlobalTheory.ConvThetaNe

open GlobalTheory.SquareAgree GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Over

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}

theorem int_eq (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) {ΦD : _} {Φ : WO W X → ℂ}
    (hD : IsDatum Γ.M ψ cA ΦD Φ) (h : GA D X) : thetaInt ωA ν 𝓕 Φ h = Γ.M.I om ΦD (kapX X e hO.JX h) :=
  thetaInt_eq_modelI D W X _ _ _ Γ.M 1 hO.JW ν 𝓕 ωA om (kapX X e hO.JX) ΦD Φ hO.measW hO.domW (hO.theta_eq_A hD) h

theorem integrable_big (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB)
    (hC : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, Γ.M.Conv om Φ) {Φ : WO W X → ℂ} (hΦ : Φ ∈ algF ψ θ true A B) (h : GA D X) :
    IntegrableOn (fun g => thetaKO ωA g h Φ) 𝓕 ν := by
  obtain ⟨ΦD, -, hD⟩ := hO.algA Φ hΦ
  have he := conjU_measurableEmbedding W 1 hO.JW
  have h1 := hC ΦD hD.1 (kapX X e hO.JX h)
  rw [hO.measW, hO.domW, he.integrableOn_map_iff, Set.preimage_image_eq _ he.injective] at h1
  have e1 : (fun g => thetaKO ωA g h Φ) = (fun g => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om ΦD g (kapX X e hO.JX h)) ∘
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW := funext fun g => (hO.theta_eq_A hD g h).symm
  rw [e1]
  exact h1

theorem hasDerivAt_big (hP : GlobalTheory.FunPr.Hypotheses₂) (hθ : IsInfFam θ)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om')
    (hC : ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F _, Γ.M.Conv om Φ) {τ : D.what₂.Tau} {Y : Matrix (Fin X.rank) (Fin X.rank) ℂ}
    (hY : Y ∈ lieAt X τ) {Φ Φ' : WO W X → ℂ} (hΦ : Φ ∈ algF ψ θ true A B) (hΦ' : Φ' ∈ algF ψ θ true A B)
    (hd : IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ') (h : GA D X) :
    HasDerivAt (fun t : ℝ => thetaInt ωA ν 𝓕 Φ (h * oneP θ X τ Y t)) (thetaInt ωA ν 𝓕 Φ' h) 0 := by
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := GlobalTheory.OscLie.exists_lie_deriv_pol Bs Γ Xc om om' hT γ hγ
  obtain ⟨ΦD, hΦD, hD⟩ := hO.algA Φ hΦ
  obtain ⟨Φ'D, -, hD'⟩ := hO.algA Φ' hΦ'
  have hPD : ΦD ∈ GlobalTheory.ThK.PolData Bs Γ.M := by
    refine Submodule.span_mono ?_ hΦD
    rintro _ ⟨f, φ, h1, h2, h3, rfl⟩
    exact ⟨f, h1, φ, h2, h3, rfl⟩
  obtain ⟨T, m, f, φ, hf, rfl⟩ := GlobalTheory.ThK.CycGen.exists_decOn_some Γ.M ΦD hPD
  have e1 := GlobalTheory.SquareAgree.DatA.datum_lieDer hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hO hT τ Y γ
    hγt hγ Φ Φ' hd T m f (fun i => δ (f i)) φ hf (fun i => (hδ _ (hf i).1).2) hD Φ'D hD'
  obtain ⟨l, hla, hl⟩ := GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil hC
  obtain ⟨Φ₁, -, hp, hI⟩ := GlobalTheory.ThetaIntegralLine.exists_deriv hP Γ.M Bs.ψ _ _ om hT.base.cm hT.base.std hT.weil hC
    (fun g hg x => by
      obtain ⟨L, hL⟩ := hT.weil.isUSplitting.adm (1, x) l hla g hg
      refine L.continuous.congr fun u => ?_
      rw [GlobalTheory.BigNZ.I_eq_l hT hl (Submodule.subset_span ⟨u, g, hg, rfl⟩), ← hL u]
      rfl) hγ hD.1
  have hM := hT.geo.hM
  have hrest : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑(f i)) (GlobalTheory.EvZeroInf.finPart (φ i)) := fun i =>
    ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, by
      rw [← GlobalTheory.EvZeroInf.pure_eq_tens]
      exact (GlobalTheory.BigNZ.IsFinPart.fam (M := Γ.M) (T := T) (hf i).2).mem hM _⟩
  have e2 : Φ₁ = Φ'D := by
    funext x
    refine (hp x).unique ?_
    rw [e1]
    simp only [map_sum, Finset.sum_apply, GlobalTheory.EvZeroInf.pure_eq_tens]
    exact HasDerivAt.fun_sum fun i _ => (hδ _ (hf i).1).2 _ (hrest i) x
  have := hI (kapX X e hO.JX h)
  rw [e2] at this
  simp only [int_eq hO hD, int_eq hO hD', GlobalTheory.KapXLine.kapX_mul, ← hγt]
  exact this

theorem exists_big_ne (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree) (hL : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching)
    (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB) (hT : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om') :
    ∃ Φ ∈ algF ψ θ true A B, thetaInt ωA ν 𝓕 Φ ≠ 0 := by
  obtain ⟨R, Rf, hm⟩ := hL _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨dec, hk⟩ := hK.1 _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨hc, hco⟩ := hk R Rf hm
  obtain ⟨l, hla, hl⟩ := GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil dec.1
  obtain ⟨f, hf, φ, hφ, hne⟩ := GlobalTheory.BigNZ.exists_I_ne_zero hm hc hco hla hl
  obtain ⟨Φ, hΦ, hD⟩ := hO.algA' _ (Submodule.subset_span ⟨f, φ, hf, hφ.fam.1, hφ.fam.2, rfl⟩)
  refine ⟨Φ, hΦ, fun h0 => hne (funext fun x => ?_)⟩
  obtain ⟨h, rfl⟩ := GlobalTheory.LineAtPlace.kapX_surj X e hO.JX x
  rw [← int_eq hO hD, h0]
  rfl

end Over

theorem thetaInt_ne_zero : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
  ∀ (ν₁ : Measure (GA D W₁)) (𝓕₁ : Set (GA D W₁)), IsHaarFD W₁ ν₁ 𝓕₁ →
  ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
  ∀ Φ' ∈ algF ψ θ false A₁ B, (∀ h, IntegrableOn (fun g => thetaKO ωB g h Φ') 𝓕₁ ν₁) → p' Φ' ≠ 0 → thetaInt ωB ν₁ 𝓕₁ Φ' ≠ 0 := by
  intro hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν₁ 𝓕₁ hν₁ ωA ωB Pm rf rl p p' hm Φ' hΦ' hint' hp' h0'
  obtain ⟨ν, 𝓕, hν⟩ := GlobalTheory.Ker.HypModel.exists_haar_fundDom D W
  obtain ⟨e, Bs, Γ, Xc, om, om', cA, cB, hO, hTD⟩ :=
    GlobalTheory.T.exists_placewise_seesaw_triple_over_hermitian D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB hm.weilA hm.weilB
  have hC := (hK.1 _ _ _ Bs _ _ Γ Xc om om' hTD).1.1
  obtain ⟨c, -, hc⟩ := GlobalTheory.T.square_commutation_integral_identity hP hK hL D ψ θ hψ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pm rf rl p p' hm
  set S := algF ψ θ true A B with hS
  have hint : ∀ Φ ∈ S, ∀ h, IntegrableOn (fun g => thetaKO ωA g h Φ) 𝓕 ν := fun Φ hΦ h => integrable_big hO hC hΦ h
  have tr : ∀ (Φ : WO W X → ℂ) (h k : GA D X), thetaInt ωA ν 𝓕 (ωA (1, k) Φ) h = thetaInt ωA ν 𝓕 Φ (h * k) := by
    intro Φ h k
    simp only [thetaInt, thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have tadd : ∀ Φ ∈ S, ∀ Ψ ∈ S, thetaInt ωA ν 𝓕 (Φ + Ψ) = thetaInt ωA ν 𝓕 Φ + thetaInt ωA ν 𝓕 Ψ := by
    intro Φ hΦ Ψ hΨ; funext h
    have e : (fun g => thetaKO ωA g h (Φ + Ψ)) = fun g => thetaKO ωA g h Φ + thetaKO ωA g h Ψ := by
      funext g; simp [thetaKO, map_add]
    simp only [thetaInt, Pi.add_apply]
    rw [e]
    exact integral_add (hint Φ hΦ h) (hint Ψ hΨ h)
  have tsmul : ∀ (s : ℂ) Φ, thetaInt ωA ν 𝓕 (s • Φ) = s • thetaInt ωA ν 𝓕 Φ := by
    intro s Φ; funext h
    have e : (fun g => thetaKO ωA g h (s • Φ)) = fun g => s * thetaKO ωA g h Φ := by
      funext g; simp [thetaKO, map_smul]
    simp only [thetaInt, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact integral_const_mul s _
  let K : Submodule ℂ (WO W X → ℂ) :=
    { carrier := {Φ | Φ ∈ S ∧ thetaInt ωA ν 𝓕 Φ = 0}
      add_mem' := fun {a b} ha hb => ⟨S.add_mem ha.1 hb.1, by rw [tadd a ha.1 b hb.1, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨S.zero_mem, by funext h; simp [thetaInt, thetaKO]⟩
      smul_mem' := fun s a ha => ⟨S.smul_mem s ha.1, by rw [tsmul, ha.2, smul_zero]⟩ }
  have kill : ∀ Ψ ∈ S, p Ψ = 0 → thetaInt ωA ν 𝓕 Ψ = 0 := fun Ψ hΨ h0 => by
    rw [hc Ψ hΨ 0 (zero_mem _) (fun h => by simp [thetaKO]) (by rw [h0, map_zero])]
    funext h; simp [thetaInt, thetaKO]
  have stf : ∀ g ∈ GfC X, ∀ x ∈ K.map p, rf g x ∈ K.map p := by
    rintro g hg _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩
    refine ⟨ωA (1, g) Ψ, ⟨hm.mapA.stabX.1 g hg Ψ hΨS, ?_⟩, hm.mapA.eqf g hg Ψ hΨS⟩
    funext h
    rw [tr, hΨ0]
    rfl
  have stl : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ K.map p, rl τ Y x ∈ K.map p := by
    rintro τ Y hY _ ⟨Ψ, ⟨hΨS, hΨ0⟩, rfl⟩
    obtain ⟨Ψ', hΨ'S, hder⟩ := hm.mapA.stabX.2 τ Y hY Ψ hΨS
    refine ⟨Ψ', ⟨hΨ'S, funext fun h => ?_⟩, hm.mapA.eql τ Y hY Ψ hΨS Ψ' hΨ'S hder⟩
    have h1 := hasDerivAt_big hP hθ hO hTD hC hY hΨS hΨ'S hder h
    rw [hΨ0] at h1
    exact h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℂ))
  rcases hm.irred.2 (K.map p) stf stl with hbot | htop
  · obtain ⟨Φ, hΦ, hpΦ⟩ : p' Φ' ∈ S.map p := hm.mapA.onto ▸ Submodule.mem_top
    have h1 : p Φ ∈ K.map p := ⟨Φ, ⟨hΦ, by rw [hc Φ hΦ Φ' hΦ' hint' hpΦ, h0', smul_zero]⟩, rfl⟩
    rw [hbot, Submodule.mem_bot, hpΦ] at h1
    exact hp' h1
  · obtain ⟨Φ, hΦ, hne⟩ := exists_big_ne hK hL hO hTD
    obtain ⟨Ψ, ⟨hΨS, hΨ0⟩, hΨp⟩ : p Φ ∈ K.map p := by rw [htop]; exact Submodule.mem_top
    have h1 := tadd _ (S.sub_mem hΦ hΨS) Ψ hΨS
    rw [sub_add_cancel, kill _ (S.sub_mem hΦ hΨS) (by rw [map_sub, hΨp, sub_self]), hΨ0, add_zero] at h1
    exact hne h1

end GlobalTheory.ConvThetaNe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleDescendsAlongGaloisExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisationBundle_descends_along_galoisExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ P : GlobalTheory.UU.CP G, LBIso U'.LG.L (P.L.L.pull β) := by
  first | exact @GlobalTheory.GaloisPackageDescent.exists_cp | exact GlobalTheory.GaloisPackageDescent.exists_cp | (intros; apply GlobalTheory.GaloisPackageDescent.exists_cp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelGeometricCoreStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_classSums_deeper_level_geometric_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ := by
  first | exact @GlobalTheory.UPoinc.UCore.classSums_core | exact GlobalTheory.UPoinc.UCore.classSums_core | (intros; apply GlobalTheory.UPoinc.UCore.classSums_core <;> assumption)
end

