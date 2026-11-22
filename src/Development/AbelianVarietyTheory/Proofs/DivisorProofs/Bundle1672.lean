import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0951
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0302
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRelationUniqueQuotient
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineQuot

open GlobalTheory.Twist (resM app_resM sec_ext_of_cover)

attribute [local instance] Abelian.hasFiniteBiproducts

section
variable {T : Scheme.{0}} {L Q : T.Modules} {N : ℕ}

theorem desc_app (s : Fin (N + 1) → (L ⟶ Q)) (V : T.Opens) (t : Γ(⨁ fun _ : Fin (N + 1) => L, V)) :
    (biproduct.desc s).app V t = ∑ m, (s m).app V ((biproduct.π (fun _ : Fin (N + 1) => L) m).app V t) := by
  have h : biproduct.desc s = ∑ m, biproduct.π (fun _ : Fin (N + 1) => L) m ≫ s m := by
    rw [← Category.id_comp (biproduct.desc s), ← biproduct.total, Preadditive.sum_comp]
    simp
  let ev : ((⨁ fun _ : Fin (N + 1) => L) ⟶ Q) →+ Γ(Q, V) :=
    { toFun := fun f => f.app V t
      map_zero' := by simp
      map_add' := fun f g => by simp }
  rw [h]
  exact (map_sum ev (fun m => biproduct.π (fun _ : Fin (N + 1) => L) m ≫ s m) Finset.univ).trans
    (Finset.sum_congr rfl fun m _ => rfl)

theorem desc_app_eq_zero {k : Type} [CommRing k] {Q' : T.Modules} {φ : T ⟶ PSpace k N}
    {s : Fin (N + 1) → (L ⟶ Q)} {s' : Fin (N + 1) → (L ⟶ Q')} (hs : Rel φ s) (hs' : Rel φ s')
    {W : T.Opens} (i j : Fin (N + 1)) (hi : W ≤ φ ⁻¹ᵁ ProjSpace.chart k N i)
    (hj : Function.Injective ((s j).app W)) (u : Γ(⨁ fun _ : Fin (N + 1) => L, W))
    (h0 : (biproduct.desc s).app W u = 0) : (biproduct.desc s').app W u = 0 := by
  set v : Γ(L, W) := ∑ m, ProjSpace.pullRatio φ W i hi m •
    (biproduct.π (fun _ : Fin (N + 1) => L) m).app W u with hv
  have key : ∀ {Q₁ : T.Modules} (s₁ : Fin (N + 1) → (L ⟶ Q₁)), Rel φ s₁ →
      (biproduct.desc s₁).app W u = (s₁ i).app W v := by
    intro Q₁ s₁ h₁
    rw [desc_app, hv, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [h₁ i m W hi, Scheme.Modules.Hom.app_smul]
  have hv0 : v = 0 := hj (by rw [hs i j W hi, ← key s hs, h0, smul_zero, map_zero])
  rw [key s' hs', hv0, map_zero]

end

theorem exists_factor_of_rel : ∀ (k : Type) [CommRing k] (N : ℕ) (T : Scheme.{0}) (L Q Q' : T.Modules)
    (s : Fin (N + 1) → (L ⟶ Q)) (s' : Fin (N + 1) → (L ⟶ Q')) (φ : T ⟶ PSpace k N),
    IsVB L 1 → IsVB Q 1 → JointEpi s → Gen s → Rel φ s → Rel φ s' →
      ∃ e : Q ⟶ Q', ∀ j, s j ≫ e = s' j := by
  intro k _ N T L Q Q' s s' φ _ _ hJ hG hs hs'
  have hepi : Epi (biproduct.desc s) := Preadditive.epi_of_cancel_zero _ fun {Z} a ha =>
    hJ Z a fun j => by simpa using congrArg (biproduct.ι (fun _ : Fin (N + 1) => L) j ≫ ·) ha
  choose j G hxG hGb using hG
  choose i hi using fun x : T => ProjSpace.exists_mem_chart k N (φ x)
  have loc : ∀ (V : T.Opens) (t : Γ(⨁ fun _ : Fin (N + 1) => L, V)),
      (biproduct.desc s).app V t = 0 → (biproduct.desc s').app V t = 0 := by
    intro V t h0
    refine sec_ext_of_cover (fun x => V ⊓ G x ⊓ φ ⁻¹ᵁ ProjSpace.chart k N (i x))
      (fun _ => inf_le_left.trans inf_le_left)
      (fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨y, ⟨⟨hy, hxG y⟩, hi y⟩⟩) fun x => ?_
    rw [← app_resM, map_zero]
    refine desc_app_eq_zero hs hs' (i x) (j x) inf_le_right
      (hGb x _ (inf_le_left.trans inf_le_right)).1 _ ?_
    rw [app_resM, h0, map_zero]
  have hk : kernel.ι (biproduct.desc s) ≫ biproduct.desc s' = 0 := by
    ext V x
    have h := congrArg (fun f => f.app V x) (kernel.condition (biproduct.desc s))
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.zero_app] at h ⊢
    exact loc V _ h
  refine ⟨Abelian.epiDesc _ _ hk, fun j => ?_⟩
  rw [← biproduct.ι_desc s j, Category.assoc, Abelian.comp_epiDesc, biproduct.ι_desc]

end GlobalTheory.LineQuot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatDarbouxCoordsRationalMatrixIffRatPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

noncomputable section

namespace GlobalTheory.RatDarbouxPointsD

set_option maxHeartbeats 1000000 in

theorem ratL_iff_ratPair : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE D.host.F D.host.E),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ := by
  intro D S T κ _ e hrat w
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  · intro hp

    let bA := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)
    haveI : Module.Free (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := Module.Finite.of_basis bA
    have hAE : Module.finrank (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) =
        Module.finrank D.host.F D.host.E := by
      rw [Module.finrank_eq_card_basis bA, Fintype.card_fin]
    have hκ : 2 * Fintype.card κ = T.rank * S.rank * Module.finrank D.host.F D.host.E := by
      have h := e.finrank_eq
      have ha : Module.finrank (AF D.host.F)
          (Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) =
          T.rank * S.rank * Module.finrank D.host.F D.host.E := by
        show Module.finrank (AF D.host.F) (Fin T.rank → Fin S.rank → AF D.host.F ⊗[D.host.F] D.host.E) = _
        simp [Module.finrank_pi_fintype, hAE, mul_assoc]
      have hb : Module.finrank (AF D.host.F) ((κ → AF D.host.F) × (κ → AF D.host.F)) = 2 * Fintype.card κ := by
        rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
        ring
      rw [← hb, ← h, ha]

    let J1 : (κ → D.host.F) →ₗ[D.host.F] (κ → AF D.host.F) :=
      LinearMap.compLeft (Algebra.linearMap D.host.F (AF D.host.F)) κ
    let J : ((κ → D.host.F) × (κ → D.host.F)) →ₗ[D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) :=
      J1.prodMap J1
    let I : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F]
        Matrix (Fin T.rank) (Fin S.rank) (AF D.host.F ⊗[D.host.F] D.host.E) :=
      (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
    let L := (e.toLinearMap.restrictScalars D.host.F).comp I
    have hJinj : Function.Injective J := by
      rintro ⟨y, z⟩ ⟨y', z'⟩ h
      have hi := AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F
      simp only [J, J1, LinearMap.prodMap_apply, Prod.mk.injEq] at h
      refine Prod.ext (funext fun i => hi ?_) (funext fun i => hi ?_)
      · exact congrFun h.1 i
      · exact congrFun h.2 i
    have hLinj : Function.Injective L := by
      have hr : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := RingHom.injective _
      intro x x' h
      have := e.injective h
      exact Matrix.ext fun i j => hr (congrFun (congrFun this i) j)
    have hle : LinearMap.range L ≤ LinearMap.range J := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, z, h⟩ := hrat x
      exact ⟨(y, z), by rw [show L x = e (incM D.host.F x) from rfl, h]; rfl⟩
    have heq : LinearMap.range L = LinearMap.range J := by
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hJinj]
      have hm : Module.finrank D.host.F (Matrix (Fin T.rank) (Fin S.rank) D.host.E) =
          T.rank * S.rank * Module.finrank D.host.F D.host.E := by
        show Module.finrank D.host.F (Fin T.rank → Fin S.rank → D.host.E) = _
        simp [Module.finrank_pi_fintype, mul_assoc]
      have hp2 : Module.finrank D.host.F ((κ → D.host.F) × (κ → D.host.F)) = 2 * Fintype.card κ := by
        rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
        ring
      rw [hm, hp2, hκ]
    obtain ⟨y, z, hw⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
    have hm : J (y, z) ∈ LinearMap.range L := heq ▸ LinearMap.mem_range_self J (y, z)
    obtain ⟨x, hx⟩ := hm
    refine ⟨x, ?_⟩
    have hx' : e (incM D.host.F x) = e w := by rw [hw]; exact hx
    exact e.injective hx'

end GlobalTheory.RatDarbouxPointsD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePosPowAffineBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowAmple

theorem pw_pw_mul {X : Scheme.{0}} (H : LB X) (a b : ℤ) :
    GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw H a) b = GlobalTheory.AbLaw.pw H (a * b) :=
  congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem relAmple_pw : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left),
    L.IsLB → RelAmple B L → ∀ a : ℕ, 1 ≤ a → RelAmple B (GlobalTheory.AbLaw.pw L (a : ℤ)) := by
  intro R _ B L hL hA a ha
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 hA
  obtain ⟨n', s', hs'⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw R B.left B.hom (GlobalTheory.AbLaw.pw L d) n s
    (GlobalTheory.AbLaw.isLB_pw hL d) hs a ha
  have e : GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (d : ℤ)) (a : ℤ) = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (a : ℤ)) (d : ℤ) := by
    rw [pw_pw_mul, pw_pw_mul, mul_comm]
  have h2 : ∃ t : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (a : ℤ)) (d : ℤ)),
      GlobalTheory.AbLaw.VeryAmpleBy B.hom _ t := by
    rw [← e]; exact ⟨s', hs'⟩
  obtain ⟨t, ht⟩ := h2
  exact GlobalTheory.Unif.relAmple_of_veryAmpleBy (GlobalTheory.AbLaw.isLB_pw hL a) hd t ht

end GlobalTheory.PowAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointNeZeroProjectiveSameDimStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueDegree_genericPoint_ne_zero_projective_same_dim : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D : ℕ), IsProjOver p → IsProjOver q → topologicalKrullDim X = D → topologicalKrullDim Y = D → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 := by
  first | exact @GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint | exact GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint | (intros; apply GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomEqOfCompEqId
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.TangentStalk

theorem ker_eq_maximalIdeal {k R : Type} [Field k] [CommRing R] [IsLocalRing R] (j : k →+* R)
    (g : R →+* k) (hg : g.comp j = RingHom.id k) : RingHom.ker g = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g
    (fun c => ⟨j c, RingHom.congr_fun hg c⟩))

theorem ringHom_eq_of_comp_eq_id {k R : Type} [Field k] [CommRing R] [IsLocalRing R] (j : k →+* R)
    (g₁ g₂ : R →+* k) (h₁ : g₁.comp j = RingHom.id k) (h₂ : g₂.comp j = RingHom.id k) : g₁ = g₂ := by
  ext a
  have hm : a - j (g₁ a) ∈ RingHom.ker g₂ := by
    rw [ker_eq_maximalIdeal j g₂ h₂, ← ker_eq_maximalIdeal j g₁ h₁, RingHom.mem_ker, map_sub,
      show g₁ (j (g₁ a)) = g₁ a from RingHom.congr_fun h₁ (g₁ a), sub_self]
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  rw [hm]
  exact (RingHom.congr_fun h₂ (g₁ a)).symm

theorem tangent_eq_stalk_dual : ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A] (x₀ : A.left), x₀ ∈ Set.range (η[A]).left.base →
    ∃ jk : k →+* A.left.presheaf.stalk x₀,
      (∀ a : A.left.presheaf.stalk x₀, ∃ c : k, a - jk c ∈ IsLocalRing.maximalIdeal (A.left.presheaf.stalk x₀)) ∧
      (∀ ψ : A.left.presheaf.stalk x₀ →+* DualNumber k, ψ.comp jk = algebraMap k (DualNumber k) →
        ∃ v : epsR k ⟶ A, IsTangent v ∧ v.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ∧
      (∀ ψ₁ ψ₂ : A.left.presheaf.stalk x₀ →+* DualNumber k, ψ₁.comp jk = algebraMap k (DualNumber k) →
        ψ₂.comp jk = algebraMap k (DualNumber k) →
        Spec.map (CommRingCat.ofHom ψ₁) ≫ A.left.fromSpecStalk x₀ = Spec.map (CommRingCat.ofHom ψ₂) ≫ A.left.fromSpecStalk x₀ →
        ψ₁ = ψ₂) := by
  intro k _ A _ x₀ hx
  obtain ⟨pt, rfl⟩ := hx
  have hpt : pt = IsLocalRing.closedPoint k := Subsingleton.elim (α := PrimeSpectrum k) _ _
  subst hpt
  let s : Sp k ⟶ A.left := (η[A]).left
  have hsA : s ≫ A.hom = 𝟙 _ := (η[A]).w.trans rfl
  have hr : Spec.map (Scheme.stalkClosedPointTo s) ≫ A.left.fromSpecStalk _ = s :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk s
  have hJ := Spec.map_preimage (A.left.fromSpecStalk (s.base (IsLocalRing.closedPoint k)) ≫ A.hom)

  set r := Scheme.stalkClosedPointTo s with hrdef
  set J := Spec.preimage (A.left.fromSpecStalk (s.base (IsLocalRing.closedPoint k)) ≫ A.hom) with hJdef
  have hrJ : J ≫ r = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, hJ, ← Category.assoc, hr, hsA, Spec.map_id]
  have hcomp : r.hom.comp J.hom = RingHom.id k := congrArg CommRingCat.Hom.hom hrJ
  have hfst : ∀ ψ : A.left.presheaf.stalk (s.base (IsLocalRing.closedPoint k)) →+* DualNumber k,
      ψ.comp J.hom = algebraMap k (DualNumber k) →
      ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ψ).comp J.hom = RingHom.id k := by
    intro ψ hψ
    rw [RingHom.comp_assoc, hψ]
    ext c
    simp
  refine ⟨J.hom, fun a => ⟨r.hom a, ?_⟩, fun ψ hψ => ?_, fun ψ₁ ψ₂ h₁ h₂ h => ?_⟩
  · rw [← ker_eq_maximalIdeal J.hom r.hom hcomp, RingHom.mem_ker, map_sub,
      show r.hom (J.hom (r.hom a)) = r.hom a from RingHom.congr_fun hcomp _, sub_self]
  · refine ⟨Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _) ?_, ?_, rfl⟩
    · show Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _ ≫ A.hom =
        Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k)))
      rw [← hJ, ← Spec.map_comp, ← hψ]
      rfl
    · show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
        Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk _ = s
      rw [← Category.assoc, ← Spec.map_comp, ← hr]
      congr 2
      ext1
      exact ringHom_eq_of_comp_eq_id J.hom _ _ (hfst ψ hψ) hcomp
  · have hloc : ∀ ψ : A.left.presheaf.stalk (s.base (IsLocalRing.closedPoint k)) →+* DualNumber k,
        ψ.comp J.hom = algebraMap k (DualNumber k) → IsLocalHom ψ := by
      intro ψ hψ
      refine ⟨fun a ha => ?_⟩
      by_contra hna
      have hm : a ∈ IsLocalRing.maximalIdeal _ := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hna)
      rw [← ker_eq_maximalIdeal J.hom _ (hfst ψ hψ), RingHom.mem_ker] at hm
      have hu := TrivSqZeroExt.isUnit_iff_isUnit_fst.1 ha
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        TrivSqZeroExt.fstHom_apply] at hm
      rw [hm] at hu
      exact not_isUnit_zero hu
    have e1 := hloc ψ₁ h₁
    have e2 := hloc ψ₂ h₂
    have hinj := (SpecToEquivOfLocalRing A.left (CommRingCat.of (DualNumber k))).symm.injective
      (a₁ := ⟨_, CommRingCat.ofHom ψ₁, e1⟩) (a₂ := ⟨_, CommRingCat.ofHom ψ₂, e2⟩) h
    have := eq_of_heq (Sigma.mk.inj_iff.mp hinj).2
    exact congrArg (fun f => f.1.hom) this
end GlobalTheory.TangentStalk
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionExtOfApplyEq
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.IwLevel

theorem section_ext_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}} (h : X ⟶ Sp k) {f g : Sp k ⟶ X}
    (hf : f ≫ h = 𝟙 _) (hg : g ≫ h = 𝟙 _)
    (pt : Sp k) (e : f pt = g pt) : f = g := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective f
  obtain ⟨⟨y, ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective g
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hf hg e ⊢
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply,
    Scheme.fromSpecResidueField_apply] at e
  subst e
  set ρ := Spec.preimage (X.fromSpecResidueField x ≫ h) with hρ
  have hr : X.fromSpecResidueField x ≫ h = Spec.map ρ := (Spec.map_preimage _).symm
  rw [Category.assoc, hr, ← Spec.map_comp, ← Spec.map_id] at hf hg
  have hφ := Spec.map_injective hf
  have hψ := Spec.map_injective hg
  suffices hfg : φ = ψ by rw [hfg]
  ext u
  have h1 : ∀ t : k, φ.hom (ρ.hom t) = t := fun t => by
    have := congrArg (fun m => m.hom t) hφ
    simpa using this
  have h2 : ∀ t : k, ψ.hom (ρ.hom t) = t := fun t => by
    have := congrArg (fun m => m.hom t) hψ
    simpa using this
  have hu : ρ.hom (φ.hom u) = u := φ.hom.injective (h1 _)
  rw [← hu, h2, h1]

theorem finite_points_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj B] (π : A ⟶ B) (d : ℕ),
    IsIsogDeg π d → Set.Finite {a : 𝟙_ (Over (Sp k)) ⟶ A | a ≫ π = 1} := by
  intro k _ A B _ π d hπ
  have := hπ.fin
  let pt : Sp k := IsLocalRing.closedPoint k
  have hF := π.left.finite_preimage_singleton ((1 : 𝟙_ (Over (Sp k)) ⟶ B).left pt)
  refine Set.Finite.of_finite_image (f := fun a => a.left pt) (hF.subset ?_) ?_
  · rintro _ ⟨a, ha, rfl⟩
    change π.left (a.left pt) = _
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, show a ≫ π = 1 from ha]
  · intro a _ b _ hab
    exact Over.OverMorphism.ext (section_ext_of_apply_eq A.hom (Over.w a) (Over.w b) pt hab)

end GlobalTheory.IwLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiNegativeDescendsFieldExtensionCurve
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Published
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiNegFieldChange

theorem semiNeg_descends_baseChange : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C →
    ∀ (k' : Type) [Field k'] [Algebra k k'], ∃ (C' : Scheme.{0}) (_ : Algebra k' Γ(C', ⊤)) (π : C' ⟶ C), IsCurve k' C' ∧
      ∀ F : C.Modules, SemiNeg k' ((Scheme.Modules.pullback π).obj F) → SemiNeg k F := by
  intro k _ C _ hC k' _ _
  obtain ⟨h1, h2, h3⟩ := hC
  let t : Sp k' ⟶ Sp k := spMap (algebraMap k k')
  let f := strHom k C
  letI A' : Algebra k' Γ(pullback f t, ⊤) := algebraΓOfHom (pullback.snd f t)
  have hs : strHom k' (pullback f t) = pullback.snd f t := strHom_eq fun _ => rfl
  refine ⟨pullback f t, A', pullback.fst f t, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hs]; exact (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback (IsPullback.of_hasPullback f t) h1
  · rw [hs]; exact GlobalTheory.ProjSpace.isProjOver_pullback_snd _ h2
  · rw [hs]; haveI := h3; infer_instance
  · intro F hF W r hW i hi
    have : IsProper f := by
      obtain ⟨N, j, hj, e⟩ := h2
      have := isProper_str k N
      change IsProper (strHom k C)
      rw [← e]
      infer_instance
    have hinst : (‹Algebra k Γ(C, ⊤)›) = algebraΓOfHom f :=
      Algebra.algebra_ext _ _ (algebraMap_eq_strHom k C)
    haveI : Flat (pullback.fst f t) := inferInstance
    have hm := GlobalTheory.T.mono_pullback_map_of_flat' _ _ (pullback.fst f t) W F i
    have h := hF _ r (hW.pullback _) _ hm
    rw [← interNum_congr_lbIso k' _ (isLB_vecOne (LB.isLB_pull hW.isLB_det _)) (isLB_vecOne (hW.pullback _).isLB_det)
      (fun j => by fin_cases j; exact hW.lbIso_det_pullback _)] at h
    have P := FieldChangeInter.interNum_pull (f := f) (f' := pullback.snd f t) (π := pullback.fst f t)
      (IsPullback.of_hasPullback f t) (L := ![det W r]) (isLB_vecOne hW.isLB_det)
    have e₃ : (fun j => ((![det W r] : Fin 1 → LB C) j).pull (pullback.fst f t)) = ![(det W r).pull (pullback.fst f t)] :=
      funext fun j => by fin_cases j; rfl
    rw [e₃] at P
    rw [hinst]
    exact P ▸ h

end GlobalTheory.SemiNegFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearModelFixesUnitSectionAbelianStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinearModel_fixes_unit_section_abelian : ∀ (W K' : Type) [CommRing W] [IsDomain W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ (σ : K' →+* K') (τ : W →+* W) (φ : G.left ⟶ G.left) (ρ : pullback G.hom (spMap (algebraMap W K')) ⟶ pullback G.hom (spMap (algebraMap W K'))), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) → φ ≫ G.hom = G.hom ≫ spMap τ → pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = ρ ≫ pullback.fst G.hom (spMap (algebraMap W K')) → ∀ (e₀ : Sp W ⟶ G.left), e₀ ≫ G.hom = 𝟙 _ → ∀ x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K')), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀ → x ≫ ρ = spMap σ ≫ x → e₀ ≫ φ = spMap τ ≫ e₀ := by
  first | exact @GlobalTheory.SemilinearModel.unit_section_semilinear | exact GlobalTheory.SemilinearModel.unit_section_semilinear | (intros; apply GlobalTheory.SemilinearModel.unit_section_semilinear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearSymmFixesUnitSectionGenericFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_symm_fixes_unit_section_genericFibre : ∀ (K W K' : Type) [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K'] (A : Over (Sp K)) [GrpObj A] (G : Over (Sp W)) [GrpObj G] (e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A), IsMonHom e.hom → ∀ (σ : K' ≃ₐ[K] K') (x : Sp K' ⟶ pullback G.hom (spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ η[G].left → x ≫ pullback.snd G.hom (spMap (algebraMap W K')) = 𝟙 _ → x ≫ (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫ e.inv.left) = spMap (σ : K' →+* K') ≫ x := by
  first | exact @GlobalTheory.semilinear_symm_fixes_unit | exact GlobalTheory.semilinear_symm_fixes_unit | (intros; apply GlobalTheory.semilinear_symm_fixes_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCompositionCompatibilityStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_composition_compatibility : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (A M B L Q V : X.Modules) (f : A ⟶ M) (g : M ⟶ B) (u : A ⟶ B) (q₀ : M ⟶ L) (q₁ : B ⟶ Q) (q₂ : B ⟶ V) (w₀ : f ≫ q₀ = 0) (w₁ : g ≫ q₁ = 0) (w₂ : u ≫ q₂ = 0) (hS₀ : (ShortComplex.mk f q₀ w₀).ShortExact) (hS₁ : (ShortComplex.mk g q₁ w₁).ShortExact) (hS₂ : (ShortComplex.mk u q₂ w₂).ShortExact) (l : L ⟶ V) (m : V ⟶ Q) (w₃ : l ≫ m = 0) (hS₃ : (ShortComplex.mk l m w₃).ShortExact) (n : ℕ) (hA : IsVB A n) (hM : IsVB M (n + 1)) (hL : IsVB L 1) (hQ : IsVB Q 1) (hV : IsVB V (1 + 1)) (hg : IsSubbundle g) (h : Met p σ B (n + 1 + 1)), f ≫ g = u → q₀ ≫ l = g ≫ q₂ → q₂ ≫ m = q₁ → ∀ hl : IsSubbundle l, (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV).restrict hl hL = Met.quot (S := ShortComplex.mk f q₀ w₀) (h.restrict hg hM) hS₀ hA hL ∧ Met.quot (S := ShortComplex.mk l m w₃) (Met.quot (S := ShortComplex.mk u q₂ w₂) (r := n) (s := 1 + 1) h hS₂ hA hV) hS₃ hL hQ = Met.quot (S := ShortComplex.mk g q₁ w₁) h hS₁ hM hQ := by
  first | exact @GlobalTheory.MetStage.metStages | exact GlobalTheory.MetStage.metStages | (intros; apply GlobalTheory.MetStage.metStages <;> assumption)
end

