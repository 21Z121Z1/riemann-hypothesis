import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfAssociated
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueSpecializes
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0105
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0102
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ISupNonzeroLocusSecComb
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.PreSec
open GlobalTheory.Points GlobalTheory.ExpansionLinear

theorem eq_zero_of_valR {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}} (p : X ⟶ Sp K) [LocallyOfFiniteType p]
    [IsReduced X] (U : X.Opens) (f : Γ(X, U))
    (h : ∀ x : Sp K ⟶ X, x ≫ p = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → valR x U f = 0) : f = 0 := by
  refine eq_zero_of_basicOpen_eq_bot f (le_bot_iff.1 (ComplexPoints.opens_le_of_geomPoints p (𝟙 _) _ _ ?_))
  intro x hx hxf
  have hxU : ⊤ ≤ x ⁻¹ᵁ U := fun a ha => X.basicOpen_le f (hxf ha)
  exact absurd (h x hx hxU) ((le_preimage_basicOpen_iff x hxU f).1 hxf).ne_zero

theorem exists_matrix {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) {J : Type} [Fintype J]
    [DecidableEq J] (W : M.Z.Opens) (b : Matrix J J Ω)
    (hb : ∀ z ∈ W, (RatModel.Lat.const M J).E z = Submodule.span (M.O z) (Set.range b)) :
    ∃ B C : Matrix J J Γ(M.Z, W), C * B = 1 ∧ ((W : Set M.Z).Nonempty → ∀ i l, valF M.pt W (B i l) = b i l) := by
  by_cases hW : (W : Set M.Z).Nonempty
  swap
  · exact ⟨1, 1, _root_.mul_one _, fun h => absurd h hW⟩
  have h1 : ∀ z ∈ W, ∃ c : Matrix J J Ω, (∀ i l, c i l ∈ M.O z) ∧ c * b = 1 := fun z hz => by
    have : ∀ i, ∃ c : J → M.O z, ∑ l, c l • b l = Pi.single i 1 := fun i =>
      (Submodule.mem_span_range_iff_exists_fun _).1 (hb z hz ▸ Submodule.subset_span ⟨i, rfl⟩)
    choose c hc using this
    refine ⟨Matrix.of fun i l => (c i l : Ω), fun i l => (c i l).2, Matrix.ext fun i j => ?_⟩
    have := congrFun (hc i) j
    rw [Finset.sum_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact this.trans (by rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl)
  obtain ⟨c, -, hc⟩ := h1 _ hW.some_mem
  have h2 : ∀ i l, c i l ∈ M.ringOn W := fun i l => RatModel.mem_ringOn.2 fun z hz => by
    obtain ⟨c', h, h'⟩ := h1 z hz
    rw [Matrix.left_inv_eq_left_inv hc h']
    exact h i l
  have h3 : ∀ i l, b i l ∈ M.ringOn W := fun i l => RatModel.mem_ringOn.2 fun z hz =>
    (RatModel.Lat.mem_const_iff M).1 (hb z hz ▸ Submodule.subset_span ⟨i, rfl⟩) l
  choose B hB using fun i l => (RatModel.mem_ringOn_iff_exists hW).1 (h3 i l)
  choose C hC using fun i l => (RatModel.mem_ringOn_iff_exists hW).1 (h2 i l)
  refine ⟨Matrix.of B, Matrix.of C, Matrix.ext fun i j => M.res_injective W hW ?_, fun _ => hB⟩
  have := congrFun (congrFun hc i) j
  rw [Matrix.mul_apply] at this ⊢
  rw [map_sum, Matrix.one_apply, apply_ite (M.res W hW), map_one, map_zero, ← Matrix.one_apply, ← this]
  exact Finset.sum_congr rfl fun l _ => by
    rw [map_mul, M.res_apply, M.res_apply, Matrix.of_apply, Matrix.of_apply, hB, hC]

open GlobalTheory.SecAff in

theorem indep_fibre (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] [IsAffine S] (P : PolAV S) {n : ℕ}
    (hn : 1 ≤ n) {J : Type} [Fintype J] (hJ : Fintype.card J = n ^ P.g)
    (s : J → LB.Sec (LPow P.A P.L n (baseOver S)))
    (hs : ∀ σ : LB.Sec (LPow P.A P.L n (baseOver S)), ∃ c : J → Γ((baseOver S).left, ⊤),
      ∀ j, σ.f j = ∑ i, liftFun P.A _ (c i) * (s i).f j)
    {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (c : J → K)
    (hc : ∀ (r : Sp K ⟶ (baseOver S ⊗ P.A).left) (j), r ≫ (fst (baseOver S) P.A).left = x →
      ⊤ ≤ r ⁻¹ᵁ (LPow P.A P.L n (baseOver S)).U j → ∑ l, c l * valR r _ ((s l).f j) = 0) : c = 0 := by
  obtain ⟨V, hV, b, hb⟩ := hS S P n hn (x (IsLocalRing.closedPoint K))
  obtain ⟨t₀, ht₀⟩ := exists_lift (T := baseOver S) (T' := Over.mk x) (Over.homMk x (Category.comp_id _)) V
    (fun y => by rw [Subsingleton.elim (α := PrimeSpectrum K) y (IsLocalRing.closedPoint K)]; exact hV)
  let t : Spec (CommRingCat.of K) ⟶ (overRes (T := baseOver S) V).left := t₀.left
  have ht : (baseAt t).hom = x := Over.w t₀
  have hA : IsAffine (baseAt t).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))
  have : Nontrivial Γ((baseAt t).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨h₁, h₂⟩ := hb K t (fun i => SecM.toSec P.A (pull P.A P.L n (homAt t) (SecM.ofSec P.A (b i))))
    (fun i => (isPullSec_iff P.A P.L n _ _ _).2 rfl)
  have hrk := (Module.finrank_eq_card_basis (Module.Basis.mk h₁ h₂.ge)).trans (Fintype.card_fin _)
  let k : baseAt t ⟶ baseOver S := Over.homMk (baseAt t).hom (Category.comp_id _)
  obtain ⟨m, b₀, hb₀⟩ := GlobalTheory.exists_sections_span_affine hS S P n hn ⊤ (isAffineOpen_top S)
  obtain ⟨e, -⟩ := exists_lift (T := baseOver S) (𝟙 _) ⊤ (fun _ => trivial)
  have h₃ := hb₀ (baseAt t) (k ≫ e) (fun i => SecM.toSec P.A (pull P.A P.L n (k ≫ e) (SecM.ofSec P.A (b₀ i))))
    (fun i => (isPullSec_iff P.A P.L n _ _ _).2 rfl)
  have hcomb : ∀ (T : Over S) (d : J → Γ(T.left, ⊤)) (v : J → SecM P.A P.L n T) (j),
      (∑ l, d l • v l).1 j = ∑ l, liftFun P.A _ (d l) * (v l).1 j := fun T d v j => by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  have h₄ : ⊤ ≤ Submodule.span Γ((baseAt t).left, ⊤)
      (Set.range fun l => pull P.A P.L n k (SecM.ofSec P.A (s l))) := by
    refine h₃.ge.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    obtain ⟨d, hd⟩ := hs (SecM.toSec P.A (pull P.A P.L n e (SecM.ofSec P.A (b₀ i))))
    have := map_mem_span (pull P.A P.L n k) (fun l => SecM.ofSec P.A (s l)) (pull P.A P.L n e (SecM.ofSec P.A (b₀ i)))
      ((Submodule.mem_span_range_iff_exists_fun _).2
        ⟨d, Subtype.ext (funext fun j => (hcomb _ d _ j).trans (hd j).symm)⟩)
    rw [pull_pull] at this
    exact this
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank h₄ (hJ.trans hrk.symm)
  have := P.isAb.smooth
  have hsm : Smooth (fst (baseAt t) P.A).left := inferInstanceAs (Smooth (pullback.fst (baseAt t).hom P.A.hom))
  have : IsReduced (baseAt t ⊗ P.A).left := isReduced_scheme_of_smooth_of_isIntegrallyClosed K (fst (baseAt t) P.A).left
  have h0 := Fintype.linearIndependent_iff.1 hli (fun l => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (c l))
    (Subtype.ext (funext fun j => (hcomb _ _ _ j).trans (eq_zero_of_valR (K := K) (fst (baseAt t) P.A).left _ _
      fun p hp hU => ?_)))
  · funext l
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1
      ((h0 l).trans (map_zero _).symm)
  refine Eq.trans ?_ (hc (p ≫ (k ▷ P.A).left) j ?_ (le_preimage_comp p _ (chart_le P.A P.L n k j) hU))
  · refine (valR_eq p _ hU _).trans ((map_sum _ _ _).trans (Finset.sum_congr rfl fun l _ => (map_mul _ _ _).trans ?_))
    refine congrArg₂ (· * ·) ((valR_eq p _ hU _).symm.trans ?_) ((valR_eq p _ hU _).symm.trans
      (valR_appLE p _ (chart_le P.A P.L n k j) hU _))
    exact valR_constFn_of_section (fst (baseAt t) P.A).left p hp _ hU (c l)
  · rw [Category.assoc, whisker_fst_left, ← Category.assoc, hp, Category.id_comp]
    exact ht

def chartPullOne {X Y Y' : Scheme.{0}} (L : LB X) (a : Y ⟶ X) (k : Y' ⟶ Y) (a' : Y' ⟶ X) (e : a' = k ≫ a) :
    ChartPull (L.pull a') (LB.LinComb L (fun _ : Fin 1 => a) (fun _ => 1)) k :=
  have le : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => a') j ≤
      k ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => a) (fun _ => j PUnit.unit) := fun j y hy => Set.mem_iInter.2 fun _ => by
    have : a' y ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy PUnit.unit
    rw [e] at this; exact this
  { idx := fun j _ => j PUnit.unit
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L _ _ (𝟙 Y') y j j' hj hj').trans (Eq.trans ?_
        (gm_linComb L (fun _ : Fin 1 => a) (fun _ => 1) k y _ _ (le j hj) (le j' hj')).symm)
      rw [Fintype.prod_unique, Fintype.prod_unique, Category.id_comp, e] }

theorem exists_theta (hS : SecBaseChangeSt) {S X : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (p : X ⟶ S)
    (ψ : X ⟶ P.A.left) [IsIso ψ] (hψ : ψ ≫ P.A.hom = p) (L : LB X) (hL : L.IsLB) (H : LBIso L (P.L.pull ψ)) (z : S) :
    ∃ (N : S.Opens) (σ : LB.Sec (L.pull (p ⁻¹ᵁ N).ι)), z ∈ N ∧
      ∀ z' ∈ N, ∃ x ∈ nonzeroLocus σ, p ((p ⁻¹ᵁ N).ι x) = z' := by
  have := P.isAb.smooth
  have := P.isAb.geomConnected
  have : GeometricallyIntegral P.A.hom := geometricallyIntegral_of_smooth _
  obtain ⟨V, hV, θ, hθ⟩ := SepPoints.exists_sec_meetsFibres hS P z
  subst hψ
  let i := ((ψ ≫ P.A.hom) ⁻¹ᵁ V).ι
  have sq : IsPullback (i ≫ ψ) ((ψ ≫ P.A.hom) ∣_ V) P.A.hom (V.ι ≫ 𝟙 S) :=
    (isPullback_morphismRestrict (ψ ≫ P.A.hom) V).flip.paste_horiz (IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩ :
      IsPullback ψ (ψ ≫ P.A.hom) P.A.hom (𝟙 S))
  let k : _ ⟶ (overRes (T := baseOver S) V ⊗ P.A).left := sq.flip.isoPullback.hom
  have k₁ : k ≫ (fst (overRes (T := baseOver S) V) P.A).left = (ψ ≫ P.A.hom) ∣_ V := sq.flip.isoPullback_hom_fst
  have k₂ : k ≫ (snd (overRes (T := baseOver S) V) P.A).left = i ≫ ψ := sq.flip.isoPullback_hom_snd
  have hk : Function.Surjective k := sq.flip.isoPullback.hom.homeomorph.surjective
  obtain ⟨σ, hσ⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hL i) (LB.isLB_pull P.isLB (i ≫ ψ))
    (LBIso.chartPull (chartPullPull L i) (chartPullSame P.L _ _ _ i fun _ => rfl) H)
    (chartSec (chartPullOne P.L _ k _ k₂.symm) θ)
  rw [nonzeroLocus_chartSec _ _ fun y _ _ => exists_chart (LB.isLB_pull P.isLB (i ≫ ψ)) y] at hσ
  refine ⟨V, σ, hV, fun z' hz' => ?_⟩
  obtain ⟨x, hx, e⟩ := hθ ⟨z', hz'⟩
  obtain ⟨y, rfl⟩ := hk x
  refine ⟨y, hσ.ge hx, ?_⟩
  have e₁ : ((ψ ≫ P.A.hom) ∣_ V) y = ⟨z', hz'⟩ := (congrArg (fun q => q y) k₁).symm.trans e
  exact (congrArg (fun q => q y) (morphismRestrict_ι (ψ ≫ P.A.hom) V)).symm.trans (congrArg V.ι e₁)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real}
  [Algebra.FiniteType o S.R] [IsFractionRing S.R Ω]

theorem u₀_eq (Q : ZHPre ρ (RatModel.ofAffine o Ω S.R) ⊤) : Q.u₀ = (⊤ : (Sp S.R).Opens).ι := by
  let M := RatModel.ofAffine o Ω S.R
  have h : (M.pt ≫ M.Z.topIso.inv) ≫ (⊤ : M.Z.Opens).ι = M.pt :=
    (Category.assoc _ _ _).trans ((congrArg (M.pt ≫ ·) M.Z.topIso.inv_hom_id).trans (Category.comp_id _))
  have e : M.Z.topIso.inv ≫ Q.u₀ = 𝟙 M.Z :=
    ext_of_isDominant M.pt ((Category.assoc _ _ _).symm.trans ((Q.u₀_gen _ h).trans (Category.comp_id _).symm))
  exact (M.Z.topIso.hom_inv_id_assoc Q.u₀).symm.trans ((congrArg (M.Z.topIso.hom ≫ ·) e).trans (Category.comp_id _))

theorem exists_iso (Q : ZHPre ρ (RatModel.ofAffine o Ω S.R) ⊤) : ∃ ψ : Q.G.left ⟶ ρ.P.A.left, IsIso ψ ∧
    ψ ≫ ρ.P.A.hom = Q.G.hom ∧ Q.φ ≫ ψ = pullback.fst _ _ ∧ LBIso Q.L.L (ρ.P.L.pull ψ) := by
  have h₀ : IsIso (⊤ : (Sp S.R).Opens).ι := inferInstanceAs (IsIso (Sp S.R).topIso.hom)
  have h₁ : IsIso Q.φ := MorphismProperty.of_isPullback (P := .isomorphisms _) Q.cart.1.flip h₀
  have h₂ : IsIso Q.u₀ := by rw [u₀_eq]; exact h₀
  refine ⟨inv Q.φ ≫ pullback.fst _ _, inferInstance, ?_, IsIso.hom_inv_id_assoc _ _, ?_⟩
  · refine (Category.assoc _ _ _).trans ((IsIso.inv_comp_eq _).2 (pullback.condition.trans ?_))
    exact (congrArg (pullback.snd ρ.P.A.hom Q.u₀ ≫ ·) (u₀_eq Q)).trans Q.cart.1.w.symm
  · refine LBIso.trans Q.L.isLB (LB.isLB_pull Q.L.isLB (𝟙 _)) (LB.isLB_pull ρ.P.isLB _)
      (lbIso_of_chartPull (chartPullUnpull Q.L.L _ rfl) (LB.isLB_pull Q.L.isLB (𝟙 _))) ?_
    exact LBIso.chartPull (chartPullSame Q.L.L _ _ _ (inv Q.φ) fun _ => (IsIso.inv_hom_id _).symm)
      (chartPullSame ρ.P.L _ _ _ (inv Q.φ) fun _ => rfl) ⟨Q.w, Q.w_gen⟩

end GlobalTheory.ZH.PreSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionTestSpecialFibreOpenPart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FibreImm

theorem le_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] {U V : X.Opens}
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → ⊤ ≤ x ⁻¹ᵁ V) : U ≤ V := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace π
  intro z hz
  by_contra hV
  obtain ⟨y, ⟨hy, hy'⟩, hc⟩ := nonempty_inter_closedPoints (Z := (U : Set X) ∩ (V : Set X)ᶜ) ⟨z, hz, hV⟩
    (U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed)
  have e := pointOfClosedPoint_apply π y hc (IsLocalRing.closedPoint k)
  have h1 := (CrdCalc.top_le_iff _ _).1 (h _ (pointOfClosedPoint_comp π y hc)
    ((CrdCalc.top_le_iff _ _).2 (e.symm ▸ hy)))
  exact hy' (e ▸ h1)

theorem eq_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsReduced X] (π : X ⟶ Sp k)
    [LocallyOfFiniteType π] {U : X.Opens} {f g : Γ(X, U)}
    (h : ∀ x : Sp k ⟶ X, x ≫ π = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ U → GlobalTheory.ZH.valR x U f = GlobalTheory.ZH.valR x U g) : f = g := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
  refine le_of_points π fun x hx hb => ?_
  have hU : ⊤ ≤ x ⁻¹ᵁ U := hb.trans (Scheme.Hom.preimage_mono _ (X.basicOpen_le _))
  refine absurd ?_ ((CrdCalc.isUnit_valR_iff _ U hU _).2 hb).ne_zero
  rw [CrdCalc.valR_eq x U hU, map_sub, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, h x hx hU, sub_self]

theorem isClosedImmersion_of_surjective {V U : Scheme.{0}} [IsAffine V] [U.IsSeparated] (f : V ⟶ U)
    (hf : Function.Surjective f.appTop) : IsClosedImmersion f := by
  have : IsClosedImmersion (f ≫ U.toSpecΓ) := by
    refine IsClosedImmersion.of_surjective_of_isAffine _ ?_
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    exact hf.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2
  exact IsClosedImmersion.of_comp f U.toSpecΓ

theorem isClosedImmersion_of_crd {k : Type} [Field k] [IsAlgClosed k] {X T : Scheme.{0}} [IsReduced X]
    (pX : X ⟶ Sp k) (pT : T ⟶ Sp k) [LocallyOfFiniteType pX] [IsSeparated pT] (h : X ⟶ T) (hp : h ≫ pT = pX)
    {HX : LB X} {HT : LB T} (hX : HX.IsLB) (hT : HT.IsLB) {J : Type} (F : J → HX.Sec) (s : J → HT.Sec)
    (J₀ : Set J) (imm : ImmBy pX HX F J₀) (cov : ⨆ i : J₀, Out.nonzeroLocus (s i) = ⊤)
    (crd : ∀ (x : Sp k ⟶ X) (v : J → k), x ≫ pX = 𝟙 _ → Crd HX F x v → Crd HT s (x ≫ h) v) :
    IsClosedImmersion h := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion) _ cov fun i => ?_
  obtain ⟨haff, r, hr, hgen⟩ := imm.2 i i.2
  have hV : h ⁻¹ᵁ Out.nonzeroLocus (s i) = Out.nonzeroLocus (F i) := by
    refine le_antisymm (le_of_points pX fun x hx hU => ?_) (le_of_points pX fun x hx hU => ?_)
    · obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      exact (CrdCalc.crd_isUnit_iff _ hv).1 ((CrdCalc.crd_isUnit_iff _ (crd x v hx hv)).2 hU)
    · obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      exact (CrdCalc.crd_isUnit_iff _ (crd x v hx hv)).1 ((CrdCalc.crd_isUnit_iff _ hv).2 hU)
  have hsurj : Function.Surjective (h.appLE _ _ hV.ge).hom := by
    rw [← RingHom.range_eq_top, eq_top_iff, ← hgen, Subring.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨j, rfl⟩)
    · refine ⟨constFn pT _ a, eq_of_points pX fun x hx hU => ?_⟩
      rw [GlobalTheory.Points.valR_appLE x h hV.ge hU, GlobalTheory.Points.valR_constFn_of_section pX x hx _ hU,
        GlobalTheory.Points.valR_constFn_of_section pT (x ≫ h) (by rw [Category.assoc, hp, hx])
          (Out.nonzeroLocus (s i)) (hU.trans (x.preimage_mono hV.ge))]
    · obtain ⟨r', hr', -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hT (s j) (s i) _ le_rfl
      refine ⟨r', eq_of_points pX fun x hx hU => ?_⟩
      obtain ⟨v, hv⟩ := CrdCalc.crd_exists hX F x
      have h1 := CrdCalc.crd_ratio hv (hr j) hU
      have h2 := CrdCalc.crd_ratio (crd x v hx hv) hr' (hU.trans (x.preimage_mono hV.ge))
      rw [GlobalTheory.Points.valR_appLE x h hV.ge hU]
      exact ((CrdCalc.crd_isUnit_iff _ hv).2 hU).mul_right_cancel (h2.symm.trans h1)
  have hsurj' : Function.Surjective (h.app (Out.nonzeroLocus (s i))).hom := by
    revert hsurj
    generalize Out.nonzeroLocus (F i) = V at hV
    subst hV
    rw [Scheme.Hom.appLE_eq_app]
    exact id
  have : IsAffine (h ⁻¹ᵁ Out.nonzeroLocus (s i)).toScheme := by rw [hV]; exact haff
  have : T.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from pT]; infer_instance
  have : (Out.nonzeroLocus (s i)).toScheme.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from (Out.nonzeroLocus (s i)).ι]; infer_instance
  refine isClosedImmersion_of_surjective _ ?_
  rw [morphismRestrict_appTop]
  have h₁ : Function.Surjective (h.app ((Out.nonzeroLocus (s i)).ι ''ᵁ ⊤)).hom := by
    rw [Scheme.Opens.ι_image_top]
    exact hsurj'
  exact (ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom _).op)).2.comp h₁

abbrev pullLB {X Y : Scheme.{0}} (f : Y ⟶ X) (L : LB X) : LB Y :=
  ⟨L.ι, fun l => f ⁻¹ᵁ L.U l, fun l l' => pullU f (L.U l ⊓ L.U l') (L.g l l')⟩

def pullSection {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X} (s : L.Sec) : (pullLB f L).Sec where
  f l := (f.app (L.U l)).hom (s.f l)
  compat i j := by
    have e := congrArg (f.app (L.U i ⊓ L.U j)).hom (s.compat i j)
    rw [map_mul] at e
    have e₁ := congrArg (fun φ => φ.hom (s.f i)) (f.naturality (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op)
    have e₂ := congrArg (fun φ => φ.hom (s.f j)) (f.naturality (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op)
    exact e₁.symm.trans (e.trans (congrArg (_ * ·) e₂))

theorem crd_pull {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X} {J : Type} (s : J → L.Sec) {R : Type} [CommRing R]
    (x : Sp R ⟶ Y) (v : J → R) : Crd (pullLB f L) (fun j => pullSection f (s j)) x v ↔ Crd L s (x ≫ f) v := by
  refine exists_congr fun l => exists_congr fun c => and_congr Iff.rfl (forall_congr' fun j => ?_)
  rw [GlobalTheory.Points.valR_comp x f]
  rfl

theorem crd_lin {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X} {I J : Type} [Fintype J]
    {s : J → H.Sec} {s' : I → H.Sec} {n : Matrix I J k} (hn : ∀ i, IsLin p s (n i) (s' i)) {x : Sp k ⟶ X}
    (hx : x ≫ p = 𝟙 _) {v : J → k} (hv : Crd H s x v) : Crd H s' x (n.mulVec v) := by
  obtain ⟨l, c, hl, hv⟩ := hv
  refine ⟨l, c, hl, fun i => ?_⟩
  rw [hn i l, CrdCalc.valR_eq x _ hl, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq, GlobalTheory.Points.valR_constFn_of_section p x hx _ hl, hv,
    mul_left_comm]

theorem isClosedImmersion_special_fibre : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ (f' : t.u.G.left ⟶ Q.G.toScheme), f' ≫ Q.G.ι = tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι → ∀ h : pullback t.u.G.hom (rPt p ≫ spMap t.u.j) ⟶ pullback (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y), h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f' → h ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion h := by
  intro L o Ω _ _ _ _ S ρ M U₀ EE hbf Q p _ y y₀ t c tm hBig f' hf' h h1 h2
  have : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hB : Big S.g S.N (S.r * S.N) := ⟨(utest_dim_and_split L o Ω S ρ p y₀ t.u).2.2.2.1, hBig.1, hBig.2.1⟩
  have pb : IsPullback t.mod.r t.mod.Φ.G.hom t.u.G.hom (rPt p ≫ spMap t.u.j) := t.mod.cart.1
  have hs : Smooth t.u.G.hom := t.mod.smooth.smooth
  have : Smooth t.mod.Φ.G.hom := MorphismProperty.of_isPullback pb hs
  have : IsReduced t.mod.Φ.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced t.mod.Φ.G.hom
  have := Q.proper
  suffices IsClosedImmersion (pb.isoPullback.hom ≫ h) from
    (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion _ _).1 this
  have hrange : Set.range (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι) ⊆
      Set.range (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    have e : (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι ≫ Q.P.hom) z =
        (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ rPt p ≫ y) z := by rw [pullback.condition]
    have e₂ : rPt p (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) z) = cPt p := by
      rw [Subsingleton.elim (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) z) (IsLocalRing.closedPoint (kb p))]
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
    change (pullback.fst (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y) ≫ Q.G.ι ≫ Q.P.hom) z ∈ Q.W tm.l
    rw [e]
    exact (congrArg (fun w => y w ∈ Q.W tm.l) e₂).mpr tm.mem
  let e := IsOpenImmersion.lift (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι _ hrange
  have he : e ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = pullback.fst _ _ ≫ Q.G.ι := IsOpenImmersion.lift_fac _ _ _
  let ψ : t.u.V →+* kb p := (IsLocalRing.residue (OO p)).comp t.u.j
  have hψ : rPt p ≫ spMap t.u.j = spMap ψ := (Spec.map_comp _ _).symm
  have hm : IsUnit (tm.m.map ψ).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact tm.unit.map ψ
  have hH : (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι).IsLB := DVR.linComb_isLB _ Q.isLB _ _
  have hT := pullChart_isLB e hH
  choose s hs using fun i => (GlobalTheory.SecRatio.existsUnique_isLin (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y))
    (fun j => pullSection e (Q.σ tm.l j)) ((tm.m.map ψ)⁻¹ i)).exists
  have hsnd : (pb.isoPullback.hom ≫ h) ≫ pullback.snd _ _ = t.mod.Φ.G.hom := by
    rw [Category.assoc, h2, IsPullback.isoPullback_hom_snd]
  have hhe : (pb.isoPullback.hom ≫ h) ≫ e = t.mod.r ≫ tm.f := by
    rw [← cancel_mono (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι, Category.assoc, he, Category.assoc, Category.assoc,
      reassoc_of% h1, hf', IsPullback.isoPullback_hom_fst_assoc]
  refine isClosedImmersion_of_crd t.mod.Φ.G.hom (pullback.snd _ _) _ hsnd (t.mod.Φ.H_isLB 1) hT t.mod.F s _
    (GlobalTheory.T.immBy_weight_zero' L.1 L.2.1 (kb p) t.mod.Φ S.g S.N _ _ S.J _ t.mod.F t.mod.pol hB t.mod.good t.mod.dim) ?_ ?_
  · refine top_le_iff.1 (le_of_points (pullback.snd (Q.G.ι ≫ Q.P.hom) (rPt p ≫ y)) fun x hx _ => ?_)
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists hH (Q.σ tm.l) (x ≫ e)
    have hw := crd_lin hs hx ((crd_pull e _ x v).2 hv)
    have hv' : v = (tm.m.map ψ).mulVec ((tm.m.map ψ)⁻¹.mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm, Matrix.one_mulVec]
    rw [hv'] at hv
    obtain ⟨i, hi, hne⟩ := (GlobalTheory.T.le_preimage_openPart_iff_testCoordinates o Ω S ρ M U₀ EE hbf Q p y y₀ t c tm hBig (x ≫ e) _ (by
      rw [Category.assoc, reassoc_of% he, pullback.condition, reassoc_of% hx]) hv).1 (by
      rw [Category.assoc, he, ← Category.assoc, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]
      exact le_rfl)
    exact ((CrdCalc.crd_isUnit_iff i hw).1 hne.isUnit).trans (x.preimage_mono
      (le_iSup (fun i : {i | t.mod.xe.symm (t.cls i) = 0} => Out.nonzeroLocus (s i))
        ⟨i, t.mod.xe.symm.map_eq_zero_iff.2 hi⟩))
  · intro x v hx hv
    have h₁ := t.mod.red (Over.homMk x hx) v hv
    have h₂ := tm.crd (kb p) ψ (x ≫ t.mod.r) v (by rw [Category.assoc, pb.w, reassoc_of% hx, hψ]) h₁
    rw [Category.assoc, ← hhe, ← Category.assoc] at h₂
    have h₃ := crd_lin hs (by rw [Category.assoc, hsnd, hx]) ((crd_pull e _ _ _).2 h₂)
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hm, Matrix.one_mulVec] at h₃

end GlobalTheory.ZH.FibreImm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleLiftSquareZeroThickening
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleThickening

theorem surjective_spec_of_isNilpotent_ker {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g)) :
    Surjective (Spec.map (CommRingCat.ofHom g)) := by
  refine ⟨fun (x : PrimeSpectrum A) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap g) := by
    rw [range_comap_of_surjective _ _ hg]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker g ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

theorem exists_sec_lbPow_of_pw {X : Scheme.{0}} {H : LB X} {n : ℕ} (σ : LB.Sec (pw H n)) :
    ∃ s : (lbPow H n).Sec, nonzeroLocus s = nonzeroLocus σ :=
  ⟨powSecMk n σ.f fun i j => (σ.compat i j).trans (congrArg (· * _) (by
      change (H.g i j ^ (n : ℤ)).val = _
      rw [zpow_natCast, Units.val_pow_eq_pow_val])),
    nonzeroLocus_powSecMk n _ _⟩

theorem relAmple_of_sq_zero : ∀ (A A' : Type) [CommRing A] [CommRing A'] (g : A →+* A'), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ → ∀ (X : Over (Spec (CommRingCat.of A))) (X' : Over (Spec (CommRingCat.of A'))) (β : X'.left ⟶ X.left), IsPullback β X'.hom X.hom (Spec.map (CommRingCat.ofHom g)) → LocallyOfFiniteType X.hom → ∀ (L : LB X.left) (L' : LB X'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull β) → RelAmple X' L' → RelAmple X L := by
  intro A A' _ _ g hg h2 X X' β hβ _ L L' hL hL' hw hA
  have hn : IsNilpotent (RingHom.ker g) := ⟨2, h2⟩
  obtain ⟨d, -, m, s', hs'⟩ := (Unif.relAmple_iff_veryAmpleBy A' X' L' hL').1 hA
  have hP' : IsProper X'.hom := isProper_of_veryAmpleBy hs'
  have hs : Surjective (Spec.map (CommRingCat.ofHom g)) := surjective_spec_of_isNilpotent_ker g hg hn
  have hc : IsClosedImmersion (Spec.map (CommRingCat.ofHom g)) := .spec_of_surjective _ hg
  have : Surjective β := MorphismProperty.of_isPullback (P := @Surjective) hβ.flip hs
  have : IsClosedImmersion β := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hβ.flip hc
  have hp : IsProper (β ≫ X.hom) := by rw [hβ.w]; infer_instance
  have : UniversallyClosed X.hom := UniversallyClosed.of_comp_surjective β X.hom
  have : IsSeparated X.hom := NilProper.isSeparated_of_comp_surjective β X.hom
  have : IsProper X.hom := {}
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
  have h : IsAmpleLB (L.pull β) :=
    (isAmpleLB_of_relAmple_of_isAffine X' hL' hA).of_lbIso (LB.isLB_pull hL β) hw.symm
  refine (relAmple_iff_isAmpleLB_of_isAffine X hL).2 ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨z, rfl⟩ := β.surjective x
  obtain ⟨n, hn₁, s, hz, ha⟩ := h.exists_affine z
  have hH := isLB_lbPow hL n
  obtain ⟨s₀, hs₀⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hH β) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL β n).symm s
  obtain ⟨D, hD, e⟩ := AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent A A' g hg hn _ _ X.hom X'.hom
    β hβ _ ha
  obtain ⟨t, ht⟩ := secOn_pull_surjective_of_surjective A A' g hg _ _ X.hom X'.hom β hβ _ hH D hD
    (GlobalTheory.LB.ofSec s₀ (β ⁻¹ᵁ D))
  obtain ⟨k, hk, σ, hσ⟩ := GlobalTheory.T.exists_pow_section' _ _ β
    (SquareZero.mul_eq_zero_of_app_eq_zero A A' g hg h2 _ _ X.hom X'.hom β hβ) _ hH s₀ D (e.trans hs₀.symm) t ht
  obtain ⟨u, hu⟩ := exists_sec_lbPow_of_pw σ
  have e' : nonzeroLocus (secOfPowPow u) = D := (nonzeroLocus_secOfPowPow u).trans (hu.trans hσ)
  exact ⟨n * k, Nat.mul_pos hn₁ hk, secOfPowPow u, e'.ge (e.ge hz), e' ▸ hD⟩

end GlobalTheory.AmpleThickening
end

