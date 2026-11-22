import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0626
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalRingCardinality.Bundle0001
import Formalism.QuotientMetricDivisors.FinalW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0628

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionValuationBoundRingClosureStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionValuationBound_ring_closure : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (N : ℕ), 0 < N → (∀ (r : ℝ) (c : ℂ), Sz l lam r c → QAll (Sz l lam r) N fun _ => c) ∧ (∀ (r s : ℝ) f, r ≤ s → QAll (Sz l lam r) N f → QAll (Sz l lam s) N f) ∧ (∀ (r : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam r) N g → (QAll (Sz l lam r) N fun τ => f τ + g τ) ∧ QAll (Sz l lam r) N fun τ => f τ - g τ) ∧ (∀ (r s : ℝ) f g, QAll (Sz l lam r) N f → QAll (Sz l lam s) N g → QAll (Sz l lam (r + s)) N fun τ => f τ * g τ) ∧ (∀ (r : ℝ) f (k : ℕ), QAll (Sz l lam r) N f → QAll (Sz l lam (k * r)) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam r) N (f k)) → QAll (Sz l lam r) N fun τ => ∑ k ∈ t, f k τ) ∧ (∀ (κ : Type) (t : Finset κ) (r : κ → ℝ) (f : κ → ℍ → ℂ), (∀ k ∈ t, QAll (Sz l lam (r k)) N (f k)) → QAll (Sz l lam (∑ k ∈ t, r k)) N fun τ => ∏ k ∈ t, f k τ) := by
  first | exact @GlobalTheory.QFam.QSz.qAll_sz_ring | exact GlobalTheory.QFam.QSz.qAll_sz_ring | (intros; apply GlobalTheory.QFam.QSz.qAll_sz_ring <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorEqRangeGoodCoordinates
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K)
    {G : Type} [Group G] [Fintype G] (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G)
    (ψ : P →* Kˣ) :
    LinearMap.range (S.lvlOp r P ψ (idemOf X)).mulVecLin =
      LinearMap.range (S.lvlPr r P ψ * S.V0E r X P ψ).mulVecLin := by
  have hE : LinearMap.range (S.lvlE r P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (lvlIdem P ψ)).mulVecLin := (image_idempotent_spec K _ _).2
  have hV : LinearMap.range (S.V0E r X P ψ).mulVecLin =
      LinearMap.range (S.gaMat r (goodAt X P ψ)).mulVecLin := (image_idempotent_spec K _ _).2
  have hm : S.gaMat r (goodAt X P ψ) = S.gaMat r (idemOf X) * S.gaMat r (lvlIdem P ψ) :=
    (group_action_matrix_hom K S G r).2 _ _
  unfold CSD.lvlOp
  rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_comp,
    hE, hV, hm, Matrix.mulVecLin_mul, LinearMap.range_comp, Submodule.map_comp]

theorem range_goodProjector_eq_range_goodCoordinates : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
    (A : FamIn D.what₂.LL G Pl0 T m) (s : ℕ), A.fam.Ok s → ∀ (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T),
    LinearMap.range (rE D A P ψ t).mulVecLin = LinearMap.range (rV0 D A P ψ t).mulVecLin := by
  intro D G _ _ Pl0 T m A s _ P ψ t
  exact range_lvlOp_idemOf_eq_range_lvlPr_mul_V0E (A.fam.R t).S (A.fam.R t).r A.X P ψ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeOpEqSpanOfFormsTie
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem range_op_eq_span_of_formsTie :
    ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n k : ℕ} (σ : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W) (V : Matrix (Fin n) (Fin k) K), FormsTie σ j H E op → LinearMap.range E.mulVecLin = LinearMap.range V.mulVecLin → LinearMap.range op = Submodule.span ℂ (Set.range fun x => j (V.mulVec x)) := by
  intro K _ _ _ n k σ W _ _ j H E op V h hr
  apply le_antisymm
  · rw [← Submodule.map_top, ← h.span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hm : E.mulVec (Pi.single i 1) ∈ LinearMap.range V.mulVecLin := by
      rw [← hr]
      exact ⟨Pi.single i 1, rfl⟩
    obtain ⟨y, hy⟩ := hm
    refine Submodule.subset_span ⟨y, ?_⟩
    have hy' : V.mulVec y = E.mulVec (Pi.single i 1) := hy
    show j (V.mulVec y) = op (j (Pi.single i 1))
    rw [h.op_eq, hy']
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have hm : V.mulVec y ∈ LinearMap.range E.mulVecLin := by
      rw [hr]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hm
    have hx' : E.mulVec x = V.mulVec y := hx
    refine ⟨j x, ?_⟩
    show op (j x) = j (V.mulVec y)
    rw [h.op_eq, hx']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneProjectorWeightZeroInvarianceStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_one_projector_weight_zero_invariance : GlobalTheory.LeviCut.RankOne := by
  first | exact @GlobalTheory.LeviCut.rankOne | exact GlobalTheory.LeviCut.rankOne | (intros; apply GlobalTheory.LeviCut.rankOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankTwoConsecutiveProjectorInvarianceStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_two_consecutive_projector_invariance : GlobalTheory.LeviCut.RankTwo := by
  first | exact @GlobalTheory.LeviCut.RankTwoProof.rankTwo | exact GlobalTheory.LeviCut.RankTwoProof.rankTwo | (intros; apply GlobalTheory.LeviCut.RankTwoProof.rankTwo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegOneSubEqDifferentialStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_one_sub_eq_differential : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 1) U) (b : Sec ((res _ (tw q 1)).X 1) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = Sec.map ((res _ (tw Q 1)).d 0 1) (kumT Q V v)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (w : (Γ(V, ⊤))ˣ), w ^ q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g b = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q V w)) → (redMap Q q 1).app U 1 a - b = Sec.map ((res _ (tw q 1)).d 0 1) (GlobalTheory.EtC.RedChern.defectSec Q q U u) := by
  first
  | exact @GlobalTheory.EtC.RedChern.red_chern_deg_one
  | exact GlobalTheory.EtC.RedChern.red_chern_deg_one
  | (intros; apply GlobalTheory.EtC.RedChern.red_chern_deg_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedChernCocycleDegTwoSubEqDefectsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedChernCocycle_deg_two_sub_eq_defects : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u₁ u₂ : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → ∀ (a : Sec ((res _ (tw Q 1)).X 0) U) (b : Sec ((res _ (tw q 1)).X 0) U), (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ Q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g a = kumT Q V v + kumT Q V w - kumT Q V (v * w)) → (∀ (V : Scheme.{0}) (g : V ⟶ U) (v w : (Γ(V, ⊤))ˣ), v ^ q = Units.map g.appTop.hom.toMonoidHom u₁ → w ^ q = Units.map g.appTop.hom.toMonoidHom u₂ → Sec.res g b = kumT q V v + kumT q V w - kumT q V (v * w)) → (redMap Q q 1).app U 0 a - b = GlobalTheory.EtC.RedChern.defectSec Q q U u₂ - GlobalTheory.EtC.RedChern.defectSec Q q U (u₁ * u₂) + GlobalTheory.EtC.RedChern.defectSec Q q U u₁ := by
  first
  | exact @GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects
  | exact GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects
  | (intros; apply GlobalTheory.RedChern.redMap_cocycle_sub_eq_defects <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCompatibleFamilyToIntersectionsBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

noncomputable section

open Opposite

namespace GlobalTheory.CechPoset

section Bij

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem sec_res_self (s : X ⟶ Sp R) {U : X.Opens} (h : U ≤ U) (c : Sec s U) : Sec.res s h c = c :=
  congrArg (fun q ↦ q.hom c) (X.presheaf.map_id (op U))

theorem ker_res (s : X ⟶ Sp R) (g : LinearMap.ker (d0 (OAff s))) {U V : X.affineOpens}
    (h : V.1 ≤ U.1) : g.1 (op V) = Sec.res s h (g.1 (op U)) := by
  have := congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) (op U)) (op V))
    (homOfLE (show V ≤ U from h)).op
  rw [amitsur_d0_apply] at this
  exact sub_eq_zero.1 this

variable {κ : Type} [LinearOrder κ]

theorem kerF_res (s : X ⟶ Sp R) (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (g : LinearMap.ker (d0 (covF s D hD))) {I J : Finset κ} (hI : I.Nonempty) (hJ : J.Nonempty)
    (h : I ⊆ J) {U : X.Opens} (hU : U ≤ ⨅ k ∈ J, D k) (hU' : U ≤ ⨅ k ∈ I, D k) :
    Sec.res s hU' (g.1 (ne I hI)) = Sec.res s hU (g.1 (ne J hJ)) := by
  have e := congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) (ne I hI)) (ne J hJ))
    (homOf (a := ne I hI) (b := ne J hJ) h)
  rw [amitsur_d0_apply] at e
  have e' : g.1 (ne J hJ) = Sec.res s (show (⨅ k ∈ J, D k) ≤ ⨅ k ∈ I, D k from
      biInf_mono fun _ hk ↦ h hk) (g.1 (ne I hI)) := sub_eq_zero.1 e
  rw [e']
  exact Sec.res_res s _ hU _

end Bij

theorem restrictCompatibleFamilyToIntersections_bijective {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {κ : Type}
    [LinearOrder κ] [Fintype κ] (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    ⨆ i, D i = ⊤ → Function.Bijective (res0 s D hD) := by
  intro hcov
  have hle1 : ∀ i : κ, D i ≤ ⨅ k ∈ ({i} : Finset κ), D k := fun i ↦
    le_iInf₂ fun k hk ↦ by rw [Finset.mem_singleton.1 hk]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro g hg
    have h0 : ∀ i : κ, g.1 (op (cov D hD (OrderDual.toDual ⟨{i}, Finset.singleton_nonempty i⟩))) = 0 :=
      fun i ↦ congrFun (congrArg Subtype.val hg) (ne {i} (Finset.singleton_nonempty i))
    apply Subtype.ext
    funext V
    show g.1 V = 0
    let Idx := {p : X.affineOpens × κ // p.1.1 ≤ V.unop.1 ⊓ D p.2}
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun j : Idx ↦ j.1.1.1) V.unop.1
      (fun j ↦ homOfLE (j.2.trans inf_le_left)) ?_ _ _ ?_
    · intro x hx
      have hx' : x ∈ ⨆ i, D i := by rw [hcov]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
      obtain ⟨W, hWB, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ V.unop.1 ⊓ D i from ⟨hx, hi⟩)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨W, hWB⟩, i), hWle⟩, hxW⟩
    · intro j
      have hW : j.1.1.1 ≤ V.unop.1 := j.2.trans inf_le_left
      have hWi : j.1.1.1 ≤ (cov D hD (OrderDual.toDual ⟨{j.1.2}, Finset.singleton_nonempty _⟩)).1 :=
        (j.2.trans inf_le_right).trans (hle1 j.1.2)
      have e1 := ker_res s g (U := V.unop) (V := j.1.1) hW
      have e2 := ker_res s g (V := j.1.1) hWi
      rw [h0, map_zero] at e2
      show Sec.res s hW (g.1 V) = Sec.res s hW 0
      rw [map_zero, ← e1, e2]
  · intro g'
    let sf : ∀ i : κ, Sec s (D i) := fun i ↦ Sec.res s (hle1 i) (g'.1 (ne {i} (Finset.singleton_nonempty i)))
    have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 D sf := by
      intro i j
      show Sec.res s inf_le_left (sf i) = Sec.res s inf_le_right (sf j)
      have hij : D i ⊓ D j ≤ ⨅ k ∈ ({i, j} : Finset κ), D k := le_iInf₂ fun k hk ↦ by
        obtain hk | hk := Finset.mem_insert.1 hk
        · rw [hk]; exact inf_le_left
        · rw [Finset.mem_singleton.1 hk]; exact inf_le_right
      exact (Sec.res_res s (hle1 i) inf_le_left _).symm.trans
        ((kerF_res s D hD g' (Finset.singleton_nonempty i) (Finset.insert_nonempty _ _)
          (by simp) hij (inf_le_left.trans (hle1 i))).trans
        ((kerF_res s D hD g' (Finset.singleton_nonempty j) (Finset.insert_nonempty _ _)
          (by simp) hij (inf_le_right.trans (hle1 j))).symm.trans
        (Sec.res_res s (hle1 j) inf_le_right _)))
    obtain ⟨G, hG, -⟩ := X.sheaf.existsUnique_gluing' D ⊤ (fun i ↦ homOfLE le_top) hcov.symm.le sf hcomp
    let g : LinearMap.ker (d0 (OAff s)) := ⟨fun V ↦ Sec.res s le_top (G : Γ(X, ⊤)), by
      rw [LinearMap.mem_ker]
      funext U U' φ
      rw [amitsur_d0_apply]
      show Sec.res s le_top (G : Γ(X, ⊤)) - Sec.res s _ (Sec.res s le_top (G : Γ(X, ⊤))) = 0
      exact sub_eq_zero.2 (Sec.res_res s _ _ _)⟩
    refine ⟨g, Subtype.ext (funext fun I ↦ ?_)⟩
    show Sec.res s le_top (G : Γ(X, ⊤)) = g'.1 I
    have hm := mn_mem I
    have hi : (cov D hD I.unop).1 ≤ D (mn I) := iInf₂_le (mn I) hm
    have hGi : Sec.res s (le_top : D (mn I) ≤ ⊤) (G : Γ(X, ⊤)) = sf (mn I) := hG (mn I)
    refine (Sec.res_res s le_top hi _).trans ?_
    rw [hGi]
    exact (Sec.res_res s (hle1 (mn I)) hi _).symm.trans
      ((kerF_res s D hD g' (Finset.singleton_nonempty (mn I)) (sub_nonempty I)
        (Finset.singleton_subset_iff.2 hm) le_rfl _).trans (sec_res_self s _ _))

end GlobalTheory.CechPoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingActionOnGroupSchemeIntCombinationEqProdZpowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringActionOnGroupScheme_intCombination_eq_prod_zpow : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [Ring O] (act : O → (A ⟶ A)), IsRAct A act → ∀ (r : ℕ) (e : Fin r → O) (c : Fin r → ℤ), act (∑ k, c k • e k) = ∏ k, act (e k) ^ c k := by
  first | (exact @GlobalTheory.ActSum.act_sum_zsmul) | (exact GlobalTheory.ActSum.act_sum_zsmul) | (intros; apply GlobalTheory.ActSum.act_sum_zsmul  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeRootOfUnityEqOneOfGeometricPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scheme_rootOfUnity_eq_one_of_geometric_points : ∀ (R : Type) [CommRing R] (S : Scheme.{0}) (s : S ⟶ Sp R) (k : ℕ) (u : Γ(S, ⊤)ˣ), IsUnit (k : R) → u ^ k = 1 → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → Units.map x.appTop.hom.toMonoidHom u = 1) → u = 1 := by
  first | exact @GlobalTheory.rootOfUnity_eq_one_of_geom | exact GlobalTheory.rootOfUnity_eq_one_of_geom | (intros; apply GlobalTheory.rootOfUnity_eq_one_of_geom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearShortExactCompatibleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_short_exact_compatible : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (W' M' H' : Type) [AddCommGroup W'] [Module R' W'] [AddCommGroup M'] [Module R' M'] [AddCommGroup H'] [Module R' H'] (i : W →ₗ[R] M) (p : M →ₗ[R] H) (i' : W' →ₗ[R'] M') (p' : M' →ₗ[R'] H') (a : W →ₛₗ[algebraMap R R'] W') (b : M →ₛₗ[algebraMap R R'] M') (c : H →ₛₗ[algebraMap R R'] H'), Function.Surjective p → Function.Exact i p → Function.Injective i' → Function.Exact i' p' → (∀ x, b (i x) = i' (a x)) → (∀ x, p' (b x) = c (p x)) → (∃ e : R' ⊗[R] W ≃ₗ[R'] W', ∀ x, e (1 ⊗ₜ x) = a x) → (∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ x, e (1 ⊗ₜ x) = c x) → ∃ e : R' ⊗[R] M ≃ₗ[R'] M', ∀ x, e (1 ⊗ₜ x) = b x := by
  first | exact @GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact | exact GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact | (intros; apply GlobalTheory.AbCoh.baseChange_middle_equiv_of_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLocalizationEqZeroOfAvoidFibreMinimStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_algebra_localization_eq_zero_of_avoid_fibre_minimal : ∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  first | exact @GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero | exact GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero | (intros; apply GlobalTheory.FlatFibreRegular.localization_eq_zero_of_mul_eq_zero <;> assumption)
end

