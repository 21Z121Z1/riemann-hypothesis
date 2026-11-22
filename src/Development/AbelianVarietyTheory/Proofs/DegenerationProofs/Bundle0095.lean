import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0087
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOfValFGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0084
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0088
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSplitTorusKernelGenericFibre
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0079

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjBundleClosure
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'}

theorem exists_projBundle_closure : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (J : Type) [Fintype J] (EE : M.Lat J) (s : J → Ω'), IsProjOver M.s → (∃ j, s j ≠ 0) → Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤ → ∃ (M' : RatModel o Ω') (f : M'.Z ⟶ M.Z), M.IsHom M' φ f ∧ IsProjOver M'.s ∧ ∀ (W : M.Z.Opens) (B : Matrix J J Ω), IsAffineOpen W → (W : Set M.Z).Nonempty → (∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) → (∀ z', f z' ∈ W → ∃ i, M'.Div ((B.map φ).mulVec s) i z') ∧ ∀ i, (B.map φ).mulVec s i ≠ 0 → ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div ((B.map φ).mulVec s) i z'} ∧ M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => (B.map φ).mulVec s j / (B.map φ).mulVec s i) := by
  intro o Ω _ _ _ _ M Ω' _ _ φ J _ EE s hM ⟨j₀, hj₀⟩ hs
  obtain ⟨n, t, e, m, v, ht, hv⟩ := GlobalTheory.T.exists_projective_lattice_twist_generated o Ω M hM J EE
  obtain ⟨i₀, hi₀⟩ := ht.1 (genericPoint M.Z)
  obtain ⟨k₀, hk₀⟩ : ∃ k, pairing φ s (v k) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨c, hc⟩ := EE.exists_eq_sum_pairing (φ := φ) s (hv _ i₀ hi₀) j₀
    exact hj₀ (by simp [hc, pairing_div, h])
  let τ : Fin (n + 1) × Fin m → Ω' := fun q => φ (t q.1) * pairing φ s (v q.2)
  have hφ0 : φ (t i₀) ≠ 0 := (map_ne_zero φ).2 hi₀.1
  have hτ0 : τ (i₀, k₀) ≠ 0 := mul_ne_zero hφ0 hk₀
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (Fin (n + 1) × Fin m) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos_iff.2 ⟨(i₀, k₀)⟩).ne'
  let ε : Fin (N + 1) ≃ Fin (n + 1) × Fin m := (Fintype.equivFinOfCardEq hN).symm
  obtain ⟨M', hcl, hproj⟩ := exists_isCl_isProjOver o Ω' N (fun l => τ (ε l)) ⟨ε.symm (i₀, k₀), by simpa using hτ0⟩ (by
    set K := Subfield.closure (Set.range (algebraMap o Ω') ∪ {x | ∃ i j, x = τ (ε j) / τ (ε i)})
    have hK : ∀ q, τ q / τ (i₀, k₀) ∈ K := fun q =>
      Subfield.subset_closure (Or.inr ⟨ε.symm (i₀, k₀), ε.symm q, by simp⟩)
    obtain ⟨V, hV, hD, hR⟩ := ht.2 i₀ hi₀.1
    have h1 : ∀ x, φ x ∈ K := map_mem_of_ringOn hV ⟨genericPoint M.Z, hD ▸ hi₀⟩ fun x hx => by
      rw [hR] at hx
      induction hx using Algebra.adjoin_induction with
      | mem _ h =>
        obtain ⟨i, rfl⟩ := h
        simpa [τ, mul_div_mul_right _ _ hk₀] using hK (i, k₀)
      | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨r, (φ.commutes r).symm⟩)
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    refine EE.eq_top_of_pairing_mem hs (hv _ i₀ hi₀) hk₀ h1 fun k => ?_
    rw [pairing_div, mul_div_assoc]
    exact mul_mem (inv_mem (h1 _)) (by simpa [τ, mul_div_mul_left _ _ hφ0] using hK (i₀, k)))
  have hd : ∀ z, ∃ i k, M'.Div (fun i => φ (t i)) i z ∧ M'.Div (fun k => pairing φ s (v k)) k z := fun z => by
    obtain ⟨l, hl⟩ := hcl.1 z
    exact ⟨(ε l).1, (ε l).2, div_mul_prod_iff.1 ((div_comp_iff ε.surjective).1 hl)⟩
  obtain ⟨f, hf⟩ := ht.exists_isHom (M' := M') (φ := φ) fun z => (hd z).imp fun _ h => h.choose_spec.1
  refine ⟨M', f, hf, hproj, fun W B hW hne hB => ?_⟩
  exact charts_of_universal EE hs ht.1 hv hf (fun z => (hd z).choose_spec.imp fun _ h => h.2)
    (fun N' hN' => hcl.exists_isHom fun z => by
      obtain ⟨q, hq⟩ := hN' z
      obtain ⟨l, rfl⟩ := ε.surjective q
      exact ⟨l, (div_comp_iff (t := τ) ε.surjective).2 hq⟩) W B hW hne hB

end GlobalTheory.ZH.RatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjSpaceMapOfLocalSectionsNoCommonZero
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical

noncomputable section

namespace GlobalTheory.ZH.CoordMap

variable {X Y : Scheme.{0}}

def pullOn (B : LB X) (V : X.Opens) (g : Y ⟶ X) : LB Y where
  ι := B.ι
  U j := g ⁻¹ᵁ (V ⊓ B.U j)
  g j j' := Units.map (g.appLE (B.U j ⊓ B.U j') (g ⁻¹ᵁ (V ⊓ B.U j) ⊓ g ⁻¹ᵁ (V ⊓ B.U j'))
    (inf_le_inf (g.preimage_mono inf_le_right) (g.preimage_mono inf_le_right))).hom.toMonoidHom (B.g j j')

def pullSecOn {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j)) (h : σ ∈ secOn B V) :
    (pullOn B V g).Sec where
  f j := (g.appLE (V ⊓ B.U j) (g ⁻¹ᵁ (V ⊓ B.U j)) le_rfl).hom (σ j)
  compat j j' := by
    have hW : g ⁻¹ᵁ (V ⊓ B.U j) ⊓ g ⁻¹ᵁ (V ⊓ B.U j') ≤ g ⁻¹ᵁ (V ⊓ B.U j ⊓ B.U j') :=
      le_inf inf_le_left (inf_le_right.trans (g.preimage_mono inf_le_right))
    have e := congrArg (g.appLE _ _ hW).hom (h j j')
    rw [map_mul, ProjSpace.appLE_resG, ProjSpace.appLE_resG, ProjSpace.appLE_resG] at e
    exact (ProjSpace.resG_appLE g le_rfl inf_le_left _).trans (e.trans
      (congrArg (_ * ·) (ProjSpace.resG_appLE g le_rfl inf_le_right _).symm))

theorem resG_pullSecOn {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j)) (h : σ ∈ secOn B V)
    (j : B.ι) {T : Y.Opens} (hj : T ≤ g ⁻¹ᵁ (V ⊓ B.U j)) :
    resG Y (U := (pullOn B V g).U j) hj ((pullSecOn g σ h).f j) = (g.appLE _ T hj).hom (σ j) :=
  ProjSpace.resG_appLE g le_rfl hj _

theorem preimage_basicOpen_le {B : LB X} {V : X.Opens} (g : Y ⟶ X) (σ : ∀ j, Γ(X, V ⊓ B.U j))
    (h : σ ∈ secOn B V) (j : B.ι) : g ⁻¹ᵁ X.basicOpen (σ j) ≤ nonzeroLocus (pullSecOn g σ h) := by
  refine le_trans ?_ (le_iSup (fun k => Y.basicOpen ((pullSecOn g σ h).f k)) j)
  refine le_trans ?_ (Scheme.basicOpen_appLE g (g ⁻¹ᵁ (V ⊓ B.U j)) _ le_rfl (σ j)).ge
  exact le_inf (g.preimage_mono (X.basicOpen_le _)) le_rfl

theorem exists_coordMap : ∀ (o : Type) [CommRing o] (X Z : Scheme.{0}) (f : X ⟶ Z) (s : Z ⟶ Sp o) (B : LB X) (V : X.Opens) (J : Type) (σ : J → ∀ j, Γ(X, V ⊓ B.U j)) (m : ℕ) (e : Fin (m + 1) ≃ J), (∀ i, σ i ∈ secOn B V) → (∀ x ∈ V, ∃ i j, x ∈ X.basicOpen (σ i j)) → ∃ π : V.toScheme ⟶ PSpace o m, π ≫ PSpace.str o m = (V.ι ≫ f) ≫ s ∧ (∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens) (hi : T ≤ π ⁻¹ᵁ ProjSpace.chart o m i) (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) = ProjSpace.pullRatio π T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ V.toScheme) (j : B.ι), ⊤ ≤ (x ≫ V.ι) ⁻¹ᵁ B.U j → Crd (ProjSpace.O1 o m) (ProjSpace.coord o m) (x ≫ π) (fun k => valF (x ≫ V.ι) (V ⊓ B.U j) (σ (e k) j)) := by
  intro o _ X Z f s B V J σ m e hσ hne
  let t : Fin (m + 1) → (pullOn B V V.ι).Sec := fun k => pullSecOn V.ι (σ (e k)) (hσ _)
  have ht : ⨆ i, nonzeroLocus (t i) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, j, hij⟩ := hne (V.ι y) y.2
    obtain ⟨k, rfl⟩ := e.surjective i
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, preimage_basicOpen_le V.ι _ (hσ _) j hij⟩
  have key : ∀ (i : Fin (m + 1)) (j : B.ι) (T : V.toScheme.Opens)
      (hi : T ≤ ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht ⁻¹ᵁ ProjSpace.chart o m i)
      (hj : T ≤ V.ι ⁻¹ᵁ (V ⊓ B.U j)), IsUnit ((V.ι.appLE _ T hj).hom (σ (e i) j)) ∧
        ∀ k, (V.ι.appLE _ T hj).hom (σ (e k) j) =
          ProjSpace.pullRatio _ T i hi k * (V.ι.appLE _ T hj).hom (σ (e i) j) := by
    intro i j T hi hj
    refine ⟨?_, fun k => ?_⟩
    · rw [← resG_pullSecOn V.ι _ (hσ _) j hj]
      exact ProjSpace.isUnit_resG_sec (t i) j (hi.trans (ProjSpace.toProj_preimage_chart _ t ht i).le) hj
    · rw [← resG_pullSecOn V.ι _ (hσ _) j hj, ← resG_pullSecOn V.ι _ (hσ _) j hj]
      exact ProjSpace.sec_eq_pullRatio_toProj_mul _ t ht i k j hi hj
  refine ⟨ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht, ProjSpace.toProj_str _ t ht, key, ?_⟩
  generalize ProjSpace.toProj ((V.ι ≫ f) ≫ s) t ht = π at key
  intro K _ x j hx
  obtain ⟨i, hi⟩ := Points.exists_le_preimage_of_iSup_eq_top (x ≫ π) (ProjSpace.iSup_chart o m)
  have hT : ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ ProjSpace.chart o m i ⊓ V.ι ⁻¹ᵁ (V ⊓ B.U j)) :=
    fun z hz => ⟨hi hz, (x z).2, hx hz⟩
  obtain ⟨hu, hk⟩ := key i j _ inf_le_left inf_le_right
  have hu' := hu.map (Points.valMap x _ hT).hom
  rw [← Points.valR_eq] at hu'
  refine ⟨i, hu'.unit, hi, fun k => ?_⟩
  have := congrArg (valR x _) (hk k)
  rw [Points.valR_mul x _ hT, Points.valR_appLE x _ _ hT, ProjSpace.pullRatio, Points.valR_appLE x _ _ hT] at this
  exact this.trans (mul_comm _ _)

end GlobalTheory.ZH.CoordMap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPureWeightSectionNeZeroAt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem FibPre.exists_pure_ne_zero_at :
    Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∀ (α : Φ.E.X) (x : Φ.Pt), ∃ φ : (Φ.H 1).Sec, Φ.Pure α φ ∧ ⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ) := by
  intro hL hL2 k _ _ Φ N hN π α x
  obtain ⟨s, hs⟩ := GlobalTheory.TwistNoBasePoint.exists_sec_twist hL hL2 k π.PB (N * 1) (by omega) _
    (x ≫ Φ.D.q ≫ π.β.hom)
  obtain ⟨φ, hφ, h⟩ := (GlobalTheory.T.pureWeightSection_to_twistedPolarisationPower k Φ N 1 π α (by omega) le_rfl).2 s
  exact ⟨φ, hφ, (h x).2 hs⟩

end GlobalTheory.ZH
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnPowerOfLocalBasesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secOn_power_of_local_bases : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Q : ZHPre ρ M U₀), (U₀ : Set M.Z).Nonempty → (∀ (W : M.Z.Opens) (x₀ : S.Gam) (b : Matrix S.J S.J Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range b)) → ∃ σ : S.J → ∀ j, Γ(Q.G.left, Q.G.hom ⁻¹ᵁ W ⊓ (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))).U j), ∀ i, σ i ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W) ∧ GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => b i l / S.th x₀) _ (σ i)) → ∀ (W : M.Z.Opens) (x₀ : S.Gam) (v : S.J → Ω), (∀ z ∈ W, x₀ ∈ S.supI M z ∧ v ∈ EE.E z) → ∃ σ ∈ secOn (LB.LinComb Q.L.L (K := Fin 1) (fun _ => 𝟙 Q.G.left) (fun _ => (S.N : ℤ))) (Q.G.hom ⁻¹ᵁ W), GenVal ρ M U₀ Q.u₀ Q.G Q.φ Q.L.L Q.w S.N ρ.s (fun l => v l / S.th x₀) _ σ := by
  first | exact @GlobalTheory.ZH.exists_secOn_genVal_of_bases | exact GlobalTheory.ZH.exists_secOn_genVal_of_bases | (intros; apply GlobalTheory.ZH.exists_secOn_genVal_of_bases <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionExtendingTorsionPointsSupport
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorsionSection

theorem exists_field_point {X : Scheme.{0}} (w : X) :
    ∃ (K : Type) (_ : Field K) (y : Sp K ⟶ X), y (IsLocalRing.closedPoint K) = w :=
  ⟨X.residueField w, inferInstance, X.fromSpecResidueField w, Scheme.fromSpecResidueField_apply w _⟩

def trivSec {X : Scheme.{0}} {W : X.Opens} (f : Γ(X, W)) : LB.Sec (Inh.trivLB W.toScheme) where
  f := fun _ => (W.ι.appLE W ⊤ W.ι_preimage_self.ge).hom f
  compat := fun _ _ => (_root_.one_mul _).symm

theorem crd_trivSec {X : Scheme.{0}} {W : X.Opens} {J : Type} (f : J → Γ(X, W)) {R : Type} [CommRing R]
    (y : Sp R ⟶ W.toScheme) :
    Crd (Inh.trivLB W.toScheme) (fun j => trivSec (f j)) y (fun j => valR (y ≫ W.ι) W (f j)) :=
  ⟨PUnit.unit, 1, GlobalTheory.Points.le_preimage_top y, fun j =>
    (GlobalTheory.Points.valR_appLE y W.ι _ (GlobalTheory.Points.le_preimage_top y) (f j)).symm.trans (_root_.one_mul _).symm⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem exists_closed (hj : JacobsonSpace M.Z) (z : M.Z) :
    ∃ z' : M.Z, IsClosed ({z'} : Set M.Z) ∧ z ⤳ z' ∧ S.HH M z' = S.HH M z := by
  obtain ⟨z', ⟨h1, h2⟩, h3⟩ := nonempty_inter_closedPoints
    (Z := {z' | S.supI M z ⊆ S.supI M z'} ∩ closure {z}) ⟨z, fun _ h => h, subset_closure rfl⟩
    ((OpenPart.isOpen_supI_subset z).isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  have hs : z ⤳ z' := specializes_iff_mem_closure.2 h2
  refine ⟨z', h3, hs, congrArg AddSubgroup.closure (Set.Subset.antisymm (fun _ h => ?_) h1)⟩
  exact RatModel.Div.of_specializes h hs

theorem exists_functions (hB : BaseFacts S M U₀ EE) (Q : Clos ρ M U₀ EE) (z' : M.Z) {a : S.Gam}
    (ha : a ∈ S.HH M z') :
    ∃ (W : M.Z.Opens) (l : Q.Λ) (_ : W ≤ Q.W l) (t : Ω) (i : S.J) (f : S.J → Γ(M.Z, W)), z' ∈ W ∧ t ≠ 0 ∧
      (∀ w ∈ W, S.supI M z' ⊆ S.supI M w) ∧ (∀ k, valF M.pt W (f k) = (Q.B l k ⬝ᵥ S.ev a) / t) ∧
      ∀ (K : Type) [Field K] (y : Sp K ⟶ M.Z) (ψ : o →+* K), ⊤ ≤ y ⁻¹ᵁ W → y ≫ M.s = spMap ψ →
        ∑ j, ψ (S.proj (S.TT M z') 0 j i) *
          ((Q.c l).map (valR y (Q.W l))).mulVec (fun k => valR y W (f k)) j ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := hB.ov.div z'
  obtain ⟨h1, i, h2, h3⟩ := hB.sec z' x₀ hx₀ a ha
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (Q.cover.ge (Set.mem_univ z'))
  set d := (fun j => algebraMap o Ω (S.proj (S.TT M z') 0 j i)) ⬝ᵥ S.ev a with hd
  let V : M.Z.Opens := ⟨(⋂ k, {w | (Q.B l k ⬝ᵥ S.ev a) / S.th x₀ ∈ M.O w}) ∩ {w | S.th x₀ / d ∈ M.O w} ∩
      {w | S.supI M z' ⊆ S.supI M w},
    ((isOpen_iInter_of_finite fun _ => M.isOpen_setOf_mem_O _).inter (M.isOpen_setOf_mem_O _)).inter
      (OpenPart.isOpen_supI_subset z')⟩
  have hz : z' ∈ V ⊓ Q.W l := ⟨⟨⟨Set.mem_iInter.2 fun k => h1 _ (by
    rw [Q.basis l z' hl]; exact Submodule.subset_span ⟨k, rfl⟩), h3⟩, fun _ h => h⟩, hl⟩
  have hne : ((V ⊓ Q.W l : M.Z.Opens) : Set M.Z).Nonempty := ⟨z', hz⟩
  choose f hf using fun k => (RatModel.mem_ringOn_iff_exists hne (x := (Q.B l k ⬝ᵥ S.ev a) / S.th x₀)).1
    (RatModel.mem_ringOn.2 fun w hw => Set.mem_iInter.1 hw.1.1.1 k)
  obtain ⟨u, hu⟩ := (RatModel.mem_ringOn_iff_exists hne (x := S.th x₀ / d)).1
    (RatModel.mem_ringOn.2 fun w hw => hw.1.1.2)
  refine ⟨V ⊓ Q.W l, l, inf_le_right, S.th x₀, i, f, hz, hx₀.1, fun w hw => hw.1.2, hf, ?_⟩
  have key : ∀ (K : Type) [Field K] (y : Sp K ⟶ M.Z) (ψ : o →+* K) (hy : ⊤ ≤ y ⁻¹ᵁ (V ⊓ Q.W l)),
      y ≫ M.s = spMap ψ → CrdCalc.valHom y _ hy (∑ j, constFn M.s _ (S.proj (S.TT M z') 0 j i) *
        ∑ k, resG M.Z inf_le_right (Q.c l j k) * f k) = ∑ j, ψ (S.proj (S.TT M z') 0 j i) *
          ((Q.c l).map (valR y (Q.W l))).mulVec (fun k => valR y _ (f k)) j := by
    intro K _ y ψ hy hψ
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_sum, ← CrdCalc.valR_eq, GlobalTheory.Points.valR_constFn_of_over M.s ψ y hψ _ hy]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, CrdCalc.valR_res y _ hy]
    rfl
  have hone : u * (∑ j, constFn M.s _ (S.proj (S.TT M z') 0 j i) *
      ∑ k, resG M.Z inf_le_right (Q.c l j k) * f k) = 1 := by
    have hp := M.top_le_preimage_pt hne
    refine M.res_injective _ hne ?_
    rw [map_one, map_mul, M.res_apply, hu]
    have e := key Ω M.pt _ hp M.pt_s
    have e2 : (fun k => valR M.pt _ (f k)) = (S.th x₀)⁻¹ • (Q.B l).mulVec (S.ev a) := by
      funext k
      exact (hf k).trans (by rw [div_eq_inv_mul]; rfl)
    have e3 : (Q.c l).map (valR M.pt (Q.W l)) * Q.B l = 1 := Q.c_inv l
    rw [e2, Matrix.mulVec_smul, Matrix.mulVec_mulVec, e3, Matrix.one_mulVec] at e
    have e4 : ∑ j, algebraMap o Ω (S.proj (S.TT M z') 0 j i) * ((S.th x₀)⁻¹ • S.ev a) j = (S.th x₀)⁻¹ * d := by
      rw [hd, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply, smul_eq_mul, mul_left_comm]
    rw [M.res_apply, ← valR_of_field, CrdCalc.valR_eq _ _ hp, e, e4]
    have := hx₀.1
    field_simp
  intro K _ y ψ hy hψ
  rw [← key K y ψ hy hψ]
  have := congrArg (CrdCalc.valHom y _ hy) hone
  rw [map_mul, map_one] at this
  exact right_ne_zero_of_mul_eq_one this

def torsSec (Q : Clos ρ M U₀ EE) (a : S.Gam) : U₀.toScheme ⟶ pullback ρ.P.A.hom Q.u₀ :=
  pullback.lift (Q.u₀ ≫ (ρ.pt a).left) (𝟙 _) (by
    have h : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := Over.w (ρ.pt a)
    rw [Category.assoc, Category.id_comp]
    exact (congrArg (Q.u₀ ≫ ·) h).trans (Category.comp_id _))

theorem torsSec_over (Q : Clos ρ M U₀ EE) (a : S.Gam) : torsSec Q a ≫ Q.a₀ ≫ Q.P.hom = U₀.ι := by
  rw [Q.cart.w, torsSec, pullback.lift_snd_assoc, Category.id_comp]

theorem agree (Q : Clos ρ M U₀ EE) (a : S.Gam) {W : M.Z.Opens} (h : W.toScheme ⟶ Q.P.left)
    (hh : h ≫ Q.P.hom = W.ι) (e : Sp Ω ⟶ W.toScheme) (he : e ≫ W.ι = M.pt) (e₀ : Sp Ω ⟶ U₀.toScheme)
    (he₀ : e₀ ≫ U₀.ι = M.pt) (hg : e ≫ h = e₀ ≫ torsSec Q a ≫ Q.a₀) {K : Type} [Field K]
    (x : Sp K ⟶ W.toScheme) (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀)
    (h1 : x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι)
    (h2 : x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left) : x ≫ h = x' ≫ Q.a₀ := by
  have lift : ∀ {F : Type} [Field F] (y : Sp F ⟶ W.toScheme) (y₀ : Sp F ⟶ U₀.toScheme), y ≫ W.ι = y₀ ≫ U₀.ι →
      ∃ v : Sp F ⟶ (W ⊓ U₀).toScheme, v ≫ M.Z.homOfLE inf_le_left = y ∧ v ≫ M.Z.homOfLE inf_le_right = y₀ := by
    intro F _ y y₀ hy
    have hr : Set.range (y ≫ W.ι) ⊆ Set.range (W ⊓ U₀).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      exact ⟨(y w).2, hy ▸ (y₀ w).2⟩
    refine ⟨IsOpenImmersion.lift (W ⊓ U₀).ι _ hr, ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac]
    · rw [← cancel_mono U₀.ι, Category.assoc, Scheme.homOfLE_ι, IsOpenImmersion.lift_fac, hy]
  obtain ⟨v, hv, hv₀⟩ := lift e e₀ (he.trans he₀.symm)
  have hvι : v ≫ (W ⊓ U₀).ι = M.pt := by
    rw [← Scheme.homOfLE_ι M.Z (inf_le_left : W ⊓ U₀ ≤ W), ← Category.assoc, hv, he]
  have : IsDominant (v ≫ (W ⊓ U₀).ι) := hvι ▸ M.isDominant_pt
  have : IsDominant v := IsDominant.of_comp_of_isOpenImmersion v (W ⊓ U₀).ι
  have := Q.proper
  have E : M.Z.homOfLE (inf_le_left : W ⊓ U₀ ≤ W) ≫ h =
      M.Z.homOfLE (inf_le_right : W ⊓ U₀ ≤ U₀) ≫ torsSec Q a ≫ Q.a₀ := by
    refine ext_of_isDominant_of_isSeparated Q.P.hom ?_ v ?_
    · simp only [Category.assoc, hh, torsSec_over, Scheme.homOfLE_ι]
    · rw [← Category.assoc, hv, ← Category.assoc, hv₀, hg]
  obtain ⟨y, hy, hy₀⟩ := lift x (x' ≫ pullback.snd _ _) (by rw [h1, Category.assoc])
  have hx' : (x' ≫ pullback.snd _ _) ≫ torsSec Q a = x' := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, torsSec, pullback.lift_fst, h2, Category.assoc]
    · rw [Category.assoc, torsSec, pullback.lift_snd, Category.comp_id]
  rw [← hy, Category.assoc, E, ← Category.assoc, hy₀, ← Category.assoc, hx']

theorem crd_generic (Q : Clos ρ M U₀ EE) (a : S.Gam) (l : Q.Λ) {t : Ω} (ht : t ≠ 0)
    (x : Sp Ω ⟶ (Q.P.hom ⁻¹ᵁ Q.W l).toScheme) (hx : x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = M.pt)
    (hc : Crd Q.O1 Q.st (x ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (S.ev a)) :
    Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x (fun k => (Q.B l k ⬝ᵥ S.ev a) / t) := by
  obtain ⟨w, hw⟩ := CrdCalc.crd_exists (LB.isLB_pull Q.isLB (Q.P.hom ⁻¹ᵁ Q.W l).ι) (Q.σ l) x
  have h1 := Q.rel l Ω x w hw
  rw [hx] at h1
  obtain ⟨c, hc⟩ := CrdCalc.crd_unique h1 hc
  have e3 : (Q.c l).map (valR M.pt (Q.W l)) * Q.B l = 1 := Q.c_inv l
  have e4 := mul_eq_one_comm.1 e3
  have e5 : S.ev a = (c : Ω) • ((Q.c l).map (valR M.pt (Q.W l))).mulVec w := funext hc
  have e6 : (Q.B l).mulVec (S.ev a) = (c : Ω) • w := by
    rw [e5, Matrix.mulVec_smul, Matrix.mulVec_mulVec, e4, Matrix.one_mulVec]
  have := CrdCalc.crd_smul ((Units.mk0 t ht)⁻¹ * c) hw
  convert this using 2 with k
  have e7 : Q.B l k ⬝ᵥ S.ev a = c * w k := congrFun e6 k
  rw [e7, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, div_eq_inv_mul, _root_.mul_assoc]

theorem exists_section : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE), ∀ z, ∀ a ∈ S.HH M z, ∃ (W : M.Z.Opens) (h : W.toScheme ⟶ Q.G.toScheme), z ∈ W ∧ h ≫ Q.G.ι ≫ Q.P.hom = W.ι ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ W.toScheme) (x' : Sp K ⟶ pullback ρ.P.A.hom Q.u₀), x ≫ W.ι = x' ≫ pullback.snd _ _ ≫ U₀.ι → x' ≫ pullback.fst _ _ = x' ≫ pullback.snd _ _ ≫ Q.u₀ ≫ (ρ.pt a).left → x ≫ h ≫ Q.G.ι = x' ≫ Q.a₀ := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q z a ha
  obtain ⟨z', hcl, hs, hH⟩ := exists_closed (S := S) hB.jac z
  obtain ⟨W, l, hle, t, i, f, hz', ht, hsup, hf, hkey⟩ := exists_functions hB Q z' (hH ▸ ha)
  have liftPt : ∀ {X : Scheme.{0}} (y : Sp Ω ⟶ X) (V : X.Opens), ⊤ ≤ y ⁻¹ᵁ V →
      ∃ e : Sp Ω ⟶ V.toScheme, e ≫ V.ι = y := fun y V hV =>
    ⟨IsOpenImmersion.lift V.ι y (by rw [Scheme.Opens.range_ι]; exact (top_le_preimage_iff _ _).1 hV),
      IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨e, he⟩ := liftPt M.pt W (M.top_le_preimage_pt ⟨z', hz'⟩)
  obtain ⟨e₀, he₀⟩ := liftPt M.pt U₀ (M.top_le_preimage_pt hB.ov.ne)
  have hp : (e₀ ≫ torsSec Q a ≫ Q.a₀) ≫ Q.P.hom = M.pt := by
    simp only [Category.assoc, torsSec_over, he₀]
  obtain ⟨e', he'⟩ := liftPt (e₀ ≫ torsSec Q a ≫ Q.a₀) (Q.P.hom ⁻¹ᵁ Q.W l) (by
    change ⊤ ≤ ((e₀ ≫ torsSec Q a ≫ Q.a₀) ≫ Q.P.hom) ⁻¹ᵁ Q.W l
    rw [hp]
    exact M.top_le_preimage_pt (Q.ne l))
  have hp' : e' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = M.pt := by rw [← Category.assoc, he', hp]
  have hc : Crd Q.O1 Q.st (e' ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (S.ev a) := by
    rw [he', ← Category.assoc]
    refine Q.crd Ω _ _ ?_
    rw [Category.assoc, torsSec, pullback.lift_fst, ← Category.assoc, Q.u₀_pt e₀ he₀]
    exact (GlobalTheory.T.torsionValues_coords_operator_permute hL o Ω S ρ).1 Ω S.R.val.toRingHom a
  have hval : ∀ {K : Type} [Field K] (y : Sp K ⟶ W.toScheme), ∃ ψ : o →+* K, (y ≫ W.ι) ≫ M.s = spMap ψ ∧
      ∑ j, ψ (S.proj (S.TT M z') 0 j i) *
        ((Q.c l).map (valR (y ≫ W.ι) (Q.W l))).mulVec (fun k => valR (y ≫ W.ι) W (f k)) j ≠ 0 := fun y =>
    ⟨(Spec.preimage ((y ≫ W.ι) ≫ M.s)).hom, (Spec.map_preimage _).symm,
      hkey _ _ _ (fun w _ => (y w).2) (Spec.map_preimage _).symm⟩
  have hcov : ⨆ j, nonzeroLocus (trivSec (f j)) = ⊤ := by
    refine top_unique fun w _ => ?_
    obtain ⟨K, _, y, rfl⟩ := exists_field_point w
    obtain ⟨ψ, -, hψ⟩ := hval y
    have : ∃ k, valR (y ≫ W.ι) W (f k) ≠ 0 := by
      by_contra hn
      push_neg at hn
      simp [hn, Matrix.mulVec, dotProduct] at hψ
    obtain ⟨k, hk⟩ := this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, (CrdCalc.top_le_iff y _).1
      ((CrdCalc.crd_isUnit_iff k (crd_trivSec f y)).1 (isUnit_iff_ne_zero.2 hk))⟩
  have : IsDominant (e ≫ W.ι) := he ▸ M.isDominant_pt
  have hdom : IsDominant e := IsDominant.of_comp_of_isOpenImmersion e W.ι
  obtain ⟨g, hg, hge, hgc⟩ := GlobalTheory.T.exists_factor_closedImmersion_dense_points Γ(M.Z, Q.W l) _ W.toScheme
    ((Q.P.hom ∣_ Q.W l) ≫ (Q.aff l).isoSpec.hom) (M.Z.homOfLE hle ≫ (Q.aff l).isoSpec.hom) _ _ S.J (Q.σ l)
    (fun j => trivSec (f j)) (LB.isLB_pull Q.isLB _) (Inh.trivLB_isLB _) (Q.imm l) hcov Ω Unit (fun _ => e)
    (fun _ => e') (by rw [Set.iUnion_const]; exact hdom.denseRange) (fun _ => ⟨by
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      rw [← cancel_mono (Q.W l).ι, Category.assoc, morphismRestrict_ι, hp', Category.assoc, Scheme.homOfLE_ι, he],
      _, crd_trivSec f e, by
      have := crd_generic Q a l ht e' hp' hc
      convert this using 2 with k
      rw [he]
      exact hf k⟩)
  have hg' : g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom = W.ι := by
    rw [← Category.assoc, cancel_mono] at hg
    rw [← morphismRestrict_ι, ← Category.assoc, hg, Scheme.homOfLE_ι]
  have hG : Set.range (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) ⊆ Set.range Q.G.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    obtain ⟨K, _, y, rfl⟩ := exists_field_point w
    obtain ⟨ψ, hψ, hne⟩ := hval y
    have h1 := Q.rel l K _ _ (hgc K y _ (crd_trivSec f y))
    rw [Category.assoc y g (_ ≫ _), hg'] at h1
    obtain ⟨φ, hφ, -⟩ := GlobalTheory.SecRatio.existsUnique_isLin (Q.P.hom ≫ M.s) Q.st
      (fun j => S.proj (S.TT M z') 0 j i)
    have h2 := (OpenPart.le_nonzeroLocus_iff hφ (x := (y ≫ g) ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι) (ψ := ψ) (by
      rw [← hψ, ← hg']; simp only [Category.assoc]) h1).2 hne
    simp only [Clos.G, SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
    refine ⟨z', hcl, W, hsup, i, φ, hφ, ?_, (CrdCalc.top_le_iff _ _).1 h2⟩
    change (g ≫ (Q.P.hom ⁻¹ᵁ Q.W l).ι ≫ Q.P.hom) (y (IsLocalRing.closedPoint K)) ∈ W
    rw [hg']
    exact (y _).2
  have hfac := IsOpenImmersion.lift_fac Q.G.ι _ hG
  refine ⟨W, IsOpenImmersion.lift Q.G.ι _ hG, hs.mem_open W.isOpen hz', ?_, fun K _ x x' h1 h2 => ?_⟩
  · rw [← Category.assoc, hfac, Category.assoc, hg']
  · rw [hfac]
    refine agree Q a _ (by rw [Category.assoc, hg']) e he e₀ he₀ ?_ x x' h1 h2
    rw [← Category.assoc, hge (), he']

end GlobalTheory.ZH.TorsionSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionOfBaseProductSectionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_section_of_baseProduct_section : ∀ (R : Type) [CommRing R] (P : PolAV (Sp R)) (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), ∃ θ : LB.Sec P.L, (∀ y ∈ nonzeroLocus th, (snd (baseOver (Sp R)) P.A).left y ∈ nonzeroLocus θ) ∧ ∀ (z : baseOver (Sp R) ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Sp R)).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1))) (a : R), IsValueAt P.A P.L 1 th z τ (fn a) → ∀ (F : Type) [CommRing F] (f : R →+* F) (k : P.L.ι), ⊤ ≤ (spMap f ≫ z.left) ⁻¹ᵁ P.L.U k → valR (spMap f ≫ z.left) _ (θ.f k) = f a * valR (X := (baseOver (Sp R)).left) (spMap f) _ (τ.s (fun _ => k)).val := by
  first | exact @GlobalTheory.UnitTheta.exists_sec_of_baseOver | exact GlobalTheory.UnitTheta.exists_sec_of_baseOver | (intros; apply GlobalTheory.UnitTheta.exists_sec_of_baseOver <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSplitTorusKernelGenericFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitTorus_kernel_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∃ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i := by
  first | exact @GlobalTheory.ZJ.GenericTorus.exists_kerIs_generic | exact GlobalTheory.ZJ.GenericTorus.exists_kerIs_generic | (intros; apply GlobalTheory.ZJ.GenericTorus.exists_kerIs_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricLiftActionGeometricFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetricLift_action_geometricFibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)), w.IsGen → ∀ t : S.J → SecA u.A (PadicAlgCl p) S.N, (∀ i, Moved u w (t i) (ρ.s i)) → ∀ (a : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt (S.r • a)).left → x ^ S.N = 1 → ∃ θ : ThetaGrp u.A.A u.A.L (S.N : ℤ) (TFK (R := u.V) (PadicAlgCl p)), SymLift u.A.A u.A.L S.N S.N x θ ∧ ∀ i t', IsActOf u.A.A u.A.L S.N θ (t i) t' → SecM.ofSec u.A.A t' = ∑ l, kf u.V (PadicAlgCl p) (y₀ (algebraMap o S.R (S.ρ a l i))) • SecM.ofSec u.A.A (t l) := by
  first | exact @GlobalTheory.ZH.ClassWeight.exists_symLift_act | exact GlobalTheory.ZH.ClassWeight.exists_symLift_act | (intros; apply GlobalTheory.ZH.ClassWeight.exists_symLift_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusQuotientNoCocharacterStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusQuotient_no_cocharacter : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (B : Over (Sp k)) (_ : GrpObj B) (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q ∧ ∀ f : Gm (Sp k) ⟶ B, IsMonHom f → f = 1 := by
  first | exact @GlobalTheory.SS.MaxTorus.exists_quot_no_cocharacter | exact GlobalTheory.SS.MaxTorus.exists_quot_no_cocharacter | (intros; apply GlobalTheory.SS.MaxTorus.exists_quot_no_cocharacter <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericTrivialisationSectionAndPullbackStatement
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericTrivialisation_section_and_pullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω), M.GenTriv H d → (∀ x : Ω, (∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) → ∃ σ : H.Sec, M.HasVal d σ x) ∧ ∀ (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (a : N.Z ⟶ M.Z), M.IsHom N φ a → N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) := by
  first | exact @GlobalTheory.ZH.RatModel.genTriv_sec_and_pull | exact GlobalTheory.ZH.RatModel.genTriv_sec_and_pull | (intros; apply GlobalTheory.ZH.RatModel.genTriv_sec_and_pull <;> assumption)
end

