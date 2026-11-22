import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0017
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0012
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0020
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0028
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0026
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFunctional
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnifPowAdm

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Comb

variable {K : Type} [CommRing K] {Y Y' : Scheme.{0}}

def cstHom (π : Y ⟶ Spec (CommRingCat.of K)) (W : Y.Opens) : K →+* Γ(Y, W) :=
  (Y.presheaf.map (homOfLE le_top).op).hom.comp
    (π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem res_cstHom (π : Y ⟶ Spec (CommRingCat.of K)) {W W' : Y.Opens} (h : W' ≤ W) (c : K) :
    (Y.presheaf.map (homOfLE h).op).hom (cstHom π W c) = cstHom π W' c :=
  SecOps.resTop_res h _

theorem app_cstHom (π : Y ⟶ Spec (CommRingCat.of K)) (q : Y' ⟶ Y) (W : Y.Opens) (c : K) :
    (q.app W).hom (cstHom π W c) = cstHom (q ≫ π) (q ⁻¹ᵁ W) c := by
  have e := congrArg (fun f => f.hom (scal π c)) (q.naturality (homOfLE (le_top : W ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e

def IsComb (π : Y ⟶ Spec (CommRingCat.of K)) {M : LB Y} {Λ : Type} [Fintype Λ] (s : LB.Sec M) (c : Λ → K)
    (t : Λ → LB.Sec M) : Prop :=
  ∀ jj, s.f jj = ∑ l, cstHom π (M.U jj) (c l) * (t l).f jj

variable (π : Y ⟶ Spec (CommRingCat.of K)) {M : LB Y} {Λ Λ' : Type} [Fintype Λ] [Fintype Λ']

theorem exists_isComb (c : Λ → K) (t : Λ → LB.Sec M) : ∃ s, IsComb π s c t :=
  ⟨⟨fun jj => ∑ l, cstHom π (M.U jj) (c l) * (t l).f jj, fun i j => by
    rw [map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, (t l).compat, res_cstHom, map_mul, res_cstHom, mul_left_comm]⟩, fun _ => rfl⟩

variable {π}

theorem IsComb.trans {s : LB.Sec M} {c : Λ → K} {t : Λ → LB.Sec M} {d : Λ → Λ' → K} {u : Λ' → LB.Sec M}
    (h : IsComb π s c t) (h' : ∀ l, IsComb π (t l) (d l) u) : IsComb π s (fun a => ∑ l, c l * d l a) u := by
  intro jj
  rw [h jj]
  simp only [h' _ jj, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul, _root_.mul_assoc]
  exact Finset.sum_comm

theorem IsComb.unique {s s' : LB.Sec M} {c : Λ → K} {t : Λ → LB.Sec M}
    (h : IsComb π s c t) (h' : IsComb π s' c t) : s = s' :=
  SecOps.sec_ext fun jj => (h jj).trans (h' jj).symm

end Comb

section Box

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  {LG : LB G.left} {LG' : LB G'.left}

theorem prK_snd (pG : IsPowGrp G' G j) (i : Fin j) :
    prK pG i ≫ pullback.snd G.hom (jK R) = pullback.snd G'.hom (jK R) :=
  Over.w ((Over.pullback (jK R)).map (pG.pr i))

theorem box_multilinear (hL : LG.IsLB) (pG : IsPowGrp G' G j) (w : LB.Iso LG' (boxLB LG pG.pr)) (k : ℕ)
    {Λ : Type} [Fintype Λ]
    (σ : Λ → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (σ' : (Fin j → Λ) →
      LB.Sec (LB.LinComb LG' (K := Fin 1) (fun _ => pullback.fst G'.hom (jK R)) (fun _ => (k : ℤ))))
    (hσ : ∀ a, IsBoxSecK pG w k (σ' a) (fun i => σ (a i)))
    (s : Fin j → LB.Sec (LB.LinComb LG (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))))
    (s' : LB.Sec (LB.LinComb LG' (K := Fin 1) (fun _ => pullback.fst G'.hom (jK R)) (fun _ => (k : ℤ))))
    (hs : IsBoxSecK pG w k s' s) (c : Fin j → Λ → FractionRing R)
    (hc : ∀ i, IsComb (pullback.snd G.hom (jK R)) (s i) (c i) σ) :
    IsComb (pullback.snd G'.hom (jK R)) s' (fun a => ∏ i, c i (a i)) σ' := by
  classical
  intro jj
  obtain ⟨jL, rfl⟩ : ∃ jL, jj = fun _ => jL := ⟨jj 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  refine fn_ext fun y hy => ?_
  choose jN hN using fun i => exists_chart hL ((pG.pr i).left (pullback.fst G'.hom (jK R) y))
  have hW : (𝟙 (pullback G'.hom (jK R)) : _ ⟶ _) y ∈
      pullback.fst G'.hom (jK R) ⁻¹ᵁ (LB.div (boxLB LG pG.pr) LG').U (jN, jL) :=
    ⟨Set.mem_iInter.2 hN, Set.mem_iInter.1 hy 0⟩
  refine (gs_res _ y (boxSec_le_a pG jN jL) hW _).symm.trans
    (Eq.trans (congrArg _ ?_) (gs_res _ y (boxSec_le_a pG jN jL) hW _))
  refine (Units.mul_right_inj
    ((pullU (Y := pullback G'.hom (jK R)) (pullback.fst G'.hom (jK R)) _ (w.s (jN, jL))) ^ k)).1 ?_
  refine (hs jN jL).trans ?_
  erw [map_sum, Finset.mul_sum]
  have e : ∀ i, ((pullback G'.hom (jK R)).presheaf.map (homOfLE (boxSec_le_b pG jN jL i)).op).hom
      (((prK pG i).app _).hom ((s i).f (fun _ => jN i))) =
      ∑ l, cstHom (pullback.snd G'.hom (jK R)) _ (c i l) *
        ((pullback G'.hom (jK R)).presheaf.map (homOfLE (boxSec_le_b pG jN jL i)).op).hom
          (((prK pG i).app _).hom ((σ l).f (fun _ => jN i))) := fun i => by
    erw [hc i (fun _ => jN i), map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    erw [map_mul, map_mul, app_cstHom, res_cstHom, prK_snd]
  rw [Finset.prod_congr rfl fun i _ => e i, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod]
  erw [map_mul, mul_left_comm]
  exact congrArg₂ (· * ·) (res_cstHom _ _ _).symm (hσ a jN jL).symm

end Box

section Exp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ)

theorem expands_comb {Λ : Type} [Fintype Λ] {c : Λ → FractionRing R} {s : Λ → U.SecK k}
    {E : Λ → Fam D.toPre (FractionRing R) k} {s₀ : U.SecK k} (h : ∀ l, U.Expands k (s l) (E l))
    (h₀ : IsComb (pullback.snd G.hom (jK R)) s₀ c s) : U.Expands k s₀ (∑ l, c l • E l) := by
  have e := (Fintype.equivFin Λ).symm
  rw [← e.sum_comp]
  exact ExpandsFracLinear.main R I D A G U k _ (fun l => c (e l)) (fun l => s (e l)) (fun l => E (e l)) s₀
    (fun l => h _) (fun jj => (h₀ jj).trans (e.sum_comp _).symm)

theorem expands_functional (hR : AdmBase R I) {s : U.SecK k} {E E' : Fam D.toPre (FractionRing R) k}
    (h : U.Expands k s E) (h' : U.Expands k s E') : E = E' := by
  have h₀ : U.Expands k SecOps.secZero (∑ l : Fin 2, (![1, -1] : Fin 2 → FractionRing R) l • ![E, E'] l) :=
    expands_comb U k (s := fun _ => s) (fun l => by fin_cases l; exacts [h, h']) (fun jj => by
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_neg, map_one, neg_mul, add_neg_cancel]
      rfl)
  have h₁ := GlobalTheory.ExpZero.main R I D A G U k hR _ _ (fun _ => rfl) h₀
  rw [Fin.sum_univ_two] at h₁
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul] at h₁
  exact add_neg_eq_zero.1 h₁

theorem expBij_of_basis (hR : AdmBase R I) {Λ : Type} [Fintype Λ]
    (b : Module.Basis Λ (FractionRing R) (Fam D.toPre (FractionRing R) k)) (σ : Λ → U.SecK k)
    (hσ : ∀ l, U.Expands k (σ l) (b l)) (hspan : ∀ s, ∃ c, IsComb (pullback.snd G.hom (jK R)) s c σ) :
    U.ExpBij k := by
  refine ⟨fun s => ?_, fun E => ?_⟩
  · obtain ⟨c, hc⟩ := hspan s
    exact ⟨_, expands_comb U k hσ hc, fun E hE => expands_functional U k hR hE (expands_comb U k hσ hc)⟩
  · obtain ⟨s, hs⟩ := exists_isComb (pullback.snd G.hom (jK R)) (b.equivFun E) σ
    refine ⟨s, ?_, fun t ht => ?_⟩
    · have := expands_comb U k hσ hs
      rwa [b.sum_equivFun] at this
    · obtain ⟨c, hc⟩ := hspan t
      have e := expands_functional U k hR ht (expands_comb U k hσ hc)
      have e' : b.equivFun E = c := by rw [e, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
      exact hc.unique (e' ▸ hs)

theorem span_of_expBij (h : U.ExpBij k) {Λ : Type} [Fintype Λ]
    (b : Module.Basis Λ (FractionRing R) (Fam D.toPre (FractionRing R) k)) (σ : Λ → U.SecK k)
    (hσ : ∀ l, U.Expands k (σ l) (b l)) (s : U.SecK k) : ∃ c, IsComb (pullback.snd G.hom (jK R)) s c σ := by
  obtain ⟨E, hE⟩ := (h.1 s).exists
  obtain ⟨t, ht⟩ := exists_isComb (pullback.snd G.hom (jK R)) (b.equivFun E) σ
  have := expands_comb U k hσ ht
  rw [b.sum_equivFun] at this
  exact ⟨_, (h.2 E).unique this hE ▸ ht⟩

end Exp

theorem unifPow_full (hL : Laws) (hL₂ : Laws2) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R)
    (hR : AdmBase R I) : UnifPowSt3 (R := R) (I := I) := by
  intro D A G _ _ U j D' A' G' _ _ pD pA pG
  obtain ⟨U', wL, H⟩ := GlobalTheory.T.uniformisation_power_without_expansion hL.globalFns R I j D D' A A' G G' pD pA pG U.toUnifPre
  have hexp : ∀ k : ℕ, 1 ≤ k → U'.ExpBij k := by
    intro k hk
    classical
    obtain ⟨hf, hd⟩ := GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) k hk
    obtain ⟨hf', hd'⟩ := GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D' (FractionRing R) k hk
    obtain ⟨hr, hg⟩ := rank_and_g_of_isPowDeg R j D.toPre D'.toPre pD
    obtain ⟨hex, hsp⟩ := GenericBoxSpan.main hL R I j D D' A A' G G' pD pA pG U' U.toUnifPre wL H k hk
    let b := Module.finBasisOfFinrankEq (FractionRing R) (Fam D.toPre (FractionRing R) k) hd
    choose σ hσ using fun l => ((U.expand k hk).2 (b l)).exists
    choose b' hb' using fun a : Fin j → Fin _ =>
      BoxFamily.exists_isBoxFam hL.globalFns R j D.toPre D'.toPre pD (FractionRing R) k (fun i => b (a i))
    choose σ' hσ' using fun a : Fin j → Fin _ => hex (fun i => σ (a i))
    have hli := boxFam_linearIndependent R j D.toPre D'.toPre pD (FractionRing R) k _ b b.linearIndependent b' hb'
    have hcard : Fintype.card (Fin j → Fin (k ^ (D.toPre.rank + D.toPre.P.g))) =
        Module.finrank (FractionRing R) (Fam D'.toPre (FractionRing R) k) := by
      rw [hd', hr, hg, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul, ← mul_add, mul_comm]
    haveI : Nonempty (Fin (k ^ (D.toPre.rank + D.toPre.P.g))) := ⟨⟨0, pow_pos hk _⟩⟩
    refine expBij_of_basis U' k hR (basisOfLinearIndependentOfCardEqFinrank hli hcard) σ' (fun a => ?_) (fun s₀ => ?_)
    · rw [coe_basisOfLinearIndependentOfCardEqFinrank]
      exact ExpandsBoxPre.main R I j D D' A A' G G' pD pA pG U' U.toUnifPre wL H k _ _ (fun i => hσ (a i)) _ _
        (hσ' a) (hb' a)
    · obtain ⟨n, c, s, s', hs, h₀⟩ := hsp s₀
      choose d hd using fun l i => span_of_expBij U.toUnifPre k (U.expand k hk) b σ hσ (s l i)
      exact ⟨_, IsComb.trans (c := c) (t := s') h₀ fun l =>
        box_multilinear U.LG.isLB pG wL k σ σ' hσ' (s l) (s' l) (hs l) (d l) (hd l)⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  exact ⟨⟨U', hexp⟩, ⟨⟨⟨⟨h₁, wL, h₂, h₃, h₄⟩, h₅⟩, h₆⟩⟩⟩

theorem main : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → UnifPowSt3 (R := R) (I := I) ∧ UnifPowSt2 (R := R) (I := I) ∧ UnifPowSt (R := R) (I := I) := by
  intro hL hL₂ R _ _ I hR
  have h := unifPow_full hL hL₂ R I hR
  refine ⟨h, ?_, ?_⟩
  · intro D A G _ _ U j D' A' G' _ _ pD pA pG
    obtain ⟨U', ⟨P⟩⟩ := h D A G U j D' A' G' pD pA pG
    exact ⟨U', ⟨P.toUnifPowOf2⟩⟩
  · intro D A G _ _ U j D' A' G' _ _ pD pA pG
    obtain ⟨U', ⟨P⟩⟩ := h D A G U j D' A' G' pD pA pG
    exact ⟨U', ⟨P.toUnifPowOf2.toUnifPowOf⟩⟩

end GlobalTheory.UnifPowAdm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsFiniteOfPullVeryAmpleIsoPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullAmpleFinite

open TopologicalSpace GlobalTheory.MulFinite

theorem sec_gs {Z Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) (r : Z ⟶ Y) (z : Z) {j j' : M.ι}
    (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') :
    gs r z (M.U j) (s.f j) = (gm r z (M.U j ⊓ M.U j') (M.g j j')).val * gs r z (M.U j') (s.f j') := by
  have hm : r z ∈ M.U j ⊓ M.U j' := ⟨hj, hj'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem pow_cancel {R : Type} [CommRing R] (g t : Rˣ) (x : R) (e : ℕ) :
    (g.val * x) ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t).val = x ^ e * t.val := by
  have h : (g ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t)) = t := by
    rw [zpow_natCast, _root_.one_mul, mul_inv_cancel_left]
  have h' : g.val ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t).val = t.val := congrArg Units.val h
  rw [mul_pow, ← h']; ring

theorem exists_fn {X W Z : Scheme.{0}} (H : LB X) (hH : H.IsLB) (L : LB W) (hL : L.IsLB)
    (s : LB.Sec L) (m : W ⟶ X) (e : ℕ) (he : e ≠ 0)
    (α : LB.Iso (pw L e) (H.pull m)) (hα : α.IsGen)
    (r : Z ⟶ W) (j₀ : H.ι) (h₀ : ∀ z, m (r z) ∈ H.U j₀) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => r ⁻¹ᵁ L.U j
  have l₂ : ∀ j, V j ≤ r ⁻¹ᵁ ((H.pull m).U (fun _ => j₀) ⊓ (pw L e).U j) :=
    fun j z hz => ⟨mem_pull.2 (h₀ z), hz⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (L.U j) (s.f j) ^ e * (gw α r z j₀ j).val := by
    refine ⟨fun j => (r.appLE _ _ le_rfl).hom (s.f j) ^ e *
      (r.appLE _ _ (l₂ j)).hom (α.s (fun _ => j₀, j)).val, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_) ?_)
    · exact congrArg (· ^ e) (gs_appLE r z _ _ _ hz _)
    · exact (gs_appLE r z _ _ _ hz _).trans (gs_unit r z _ (l₂ j hz) _)
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hL (r z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_gs s r z hz.1 hz.2,
        (isGen_iff α).1 hα Z r z j₀ j₀ j j' (h₀ z) (h₀ z) hz.1 hz.2]
      have h1 : gm (r ≫ m) z (H.U j₀ ⊓ H.U j₀) (H.g j₀ j₀) = 1 := gm_self hH _ z (h₀ z)
      have t₁ : gm r z ((pw L e).U j ⊓ (pw L e).U j') ((pw L e).g j j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') ^ (e : ℤ) := map_zpow _ _ _
      rw [h1, t₁]
      exact pow_cancel _ _ _ _)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hL (r z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔ IsUnit (gs r z (L.U j) (s.f j)) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, Units.isUnit_mul_units, isUnit_pow_iff he]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨j, (isUnit_gs r z _ hj _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ nonzeroLocus s from h)
    have hk' : r z ∈ L.U k := W.basicOpen_le _ hk
    rw [sec_gs s r z hj hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isFinite_of_pull_iso_pow :
    ∀ (K : Type) [Field K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (n : ℕ) (s : Fin (n + 1) → LB.Sec H') (d : ℕ), H.IsLB → H'.IsLB → IsSeparated f → VeryAmpleBy (φ ≫ f) H' s → 1 ≤ d → LBIso (pw H' d) (H.pull φ) → IsFinite φ := by
  intro K _ X X' f φ H H' n s d hH hH' hf hva hd ⟨α, hα⟩
  have : IsProper (φ ≫ f) := isProper_of_isProjBy K X' _ ⟨H', hH', n, s, hva⟩
  have : IsProper φ := .of_comp _ f
  suffices LocallyQuasiFinite φ from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  obtain ⟨hcov, hs⟩ := hva
  have hy : ∀ z, φ (φ.fiberι y z) = y := fun z => (φ.range_fiberι y).le ⟨z, rfl⟩
  have := isAffineHom_fromSpecResidueField X y
  have : IsAffineHom (φ.fiberι y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback φ (X.fromSpecResidueField y)).flip this
  obtain ⟨j₀, hj₀⟩ := Geo.Tor.exists_chart hH y
  have key := fun i => exists_fn H hH H' hH' (s i) φ d (by omega) α hα (φ.fiberι y) j₀ (fun z => by
    rw [hy]; exact hj₀)
  choose a ha using key
  have : IsProper (φ.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd φ (X.fromSpecResidueField y)))
  refine locallyQuasiFinite_of_cover (K := X.residueField y) (φ.fiberToSpecResidueField y) a ?_ fun i => ?_
  · simp only [ha]
    rw [← Scheme.Hom.preimage_iSup]
    exact (congrArg (fun V => φ.fiberι y ⁻¹ᵁ V) hcov).trans rfl
  · rw [ha]
    exact (hs i).1.preimage _

end GlobalTheory.PullAmpleFinite
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackOfEquationsLift
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjBaseChange

open MvPolynomial

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem appLE_cst (φ : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) :
    (φ.appLE U V h).hom.comp (cst f U) = cst (φ ≫ f) V := by
  have e : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ φ.appLE U V h =
      φ.appTop ≫ X'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE]
    rfl
  ext a
  exact congrArg (fun q => q.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))) e

theorem cst_comp (f' : X' ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (V : X'.Opens) :
    cst (f' ≫ Spec.map (CommRingCat.ofHom g)) V = (cst f' V).comp g := by
  ext a
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact congrArg (fun q => rs X' (le_top : V ≤ ⊤) (f'.appTop.hom q)) e.symm

theorem gs_appLE (φ : X' ⟶ X) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) (z : X') (hz : z ∈ V) (a : Γ(X, U)) :
    gs (𝟙 X') z V ((φ.appLE U V h).hom a) = gs φ z U a :=
  (gs_res (𝟙 X') z h hz ((φ.app U).hom a)).trans ((gs_pull (𝟙 X') φ z U (h hz) a).trans (by rw [Category.id_comp]))

theorem isClosedImmersion_of_charts (φ : X' ⟶ X) {J : Type} (U : J → X.Opens) (hc : ⨆ i, U i = ⊤)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (φ ⁻¹ᵁ U i))
    (hs : ∀ i, Function.Surjective (φ.app (U i)).hom) : IsClosedImmersion φ := by
  refine @HasAffineProperty.of_iSup_eq_top _ _ IsClosedImmersion.hasAffineProperty _ _ _ _
    (fun i => ⟨U i, hU i⟩) hc fun i => ⟨hV i, ?_⟩
  have key : ∀ (A : X.Opens) (B : X'.Opens) (h : B ≤ φ ⁻¹ᵁ A), A = U i → B = φ ⁻¹ᵁ U i →
      Function.Surjective (φ.appLE A B h).hom := by
    rintro _ _ h rfl rfl
    rw [Scheme.Hom.appLE_eq_app]
    exact hs i
  show Function.Surjective ((φ ∣_ U i).app ⊤).hom
  rw [morphismRestrict_app']
  exact key _ _ _ (by simp) (by simp)

theorem isPullback_of_charts (g : R →+* R') (hg : Function.Surjective g) (φ : X' ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R'))
    (hw : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) {J : Type} (U : J → X.Opens) (V : J → X'.Opens)
    (hUV : ∀ i, V i = φ ⁻¹ᵁ U i) (hc : ⨆ i, U i = ⊤) (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))
    (hs : ∀ i, Function.Surjective (φ.appLE (U i) (V i) (hUV i).le).hom)
    (hk : ∀ i a, (φ.appLE (U i) (V i) (hUV i).le).hom a = 0 → ∀ (B : Type) [CommRing B] (θ : Γ(X, U i) →+* B)
      (c : R' →+* B), θ.comp (cst f (U i)) = c.comp g → θ a = 0) :
    IsPullback φ f' f (Spec.map (CommRingCat.ofHom g)) := by
  obtain rfl : V = fun i => φ ⁻¹ᵁ U i := funext hUV
  simp only [Scheme.Hom.appLE_eq_app] at hs hk
  have := isClosedImmersion_of_charts φ U hc hU hV hs
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg
  have hle : φ.ker ≤ (pullback.fst f (Spec.map (CommRingCat.ofHom g))).ker := by
    refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun i => ⟨U i, hU i⟩) hc fun i a ha => ?_
    rw [Scheme.Hom.ker_apply] at ha ⊢
    refine hk i a ha _ _ (cst (pullback.snd f (Spec.map (CommRingCat.ofHom g))) _) ?_
    rw [← cst_comp, ← pullback.condition, ← appLE_cst _ f le_rfl, Scheme.Hom.appLE_eq_app]
  have hl := IsClosedImmersion.lift_fac φ _ hle
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _
    (fun t => pullback.lift t.fst t.snd t.condition ≫ IsClosedImmersion.lift φ _ hle) (fun t => ?_) (fun t => ?_)
    (fun t m h₁ _ => ?_)⟩⟩
  · rw [Category.assoc, hl, pullback.lift_fst]
  · rw [← cancel_mono (Spec.map (CommRingCat.ofHom g)), Category.assoc, ← hw, ← Category.assoc, Category.assoc _ _ φ,
      hl, pullback.lift_fst, t.condition]
  · rw [← cancel_mono φ, Category.assoc, hl, pullback.lift_fst, h₁]

theorem eventually_exists_form (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} {m : ℕ} {s : Fin (m + 1) → H.Sec}
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (m + 1) → Γ(X, nonzeroLocus (s i))) (hr' : ∀ i, IsRatioFamily s i (r i)) (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) R) (hp : eval₂Hom (cst f _) (r i) p = 0) :
    ∀ᶠ d in Filter.atTop, ∃ F ∈ vanishingForms f s d, MvPolynomial.X i - 1 ∣ F - p := by
  obtain ⟨e, F, hF, hFp⟩ := (ThetaDeform.exists_homogeneous i p).exists
  have hFi : eval₂Hom (cst f _) (r i) F = 0 := by
    obtain ⟨G, hG⟩ := hFp
    rw [eq_add_of_sub_eq hG, map_add, hp, map_mul, map_sub, map_one, eval₂Hom_X', (hr' i).self_eq_one]
    simp
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) F = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr' j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr' j).gs_form f hj hk hF).symm.trans ((hr' i).gs_form f hi hk hF)
    rw [hFi, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose n hn using hn
  filter_upwards [Filter.eventually_ge_atTop (Finset.univ.sup n + e)] with d hd
  obtain ⟨c, rfl⟩ : ∃ c, d = c + e := ⟨d - e, by omega⟩
  refine ⟨MvPolynomial.X i ^ c * F, ?_, ?_⟩
  · refine mem_vanishingForms_of_ratios f hc r hr' ((isHomogeneous_X_pow i c).mul hF) fun j => ?_
    have hle : n j ≤ c := (Finset.le_sup (Finset.mem_univ j)).trans (by omega)
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hle
    rw [map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hn j, mul_zero]
  · have : MvPolynomial.X i ^ c * F - p = (MvPolynomial.X i ^ c - 1) * F + (F - p) := by ring
    rw [this]
    exact ((sub_one_dvd_pow_sub_one _ c).mul_right _).add hFp

theorem isPullback_of_equations_lift : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Function.Surjective g → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R')) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' ≫ (Spec.map (CommRingCat.ofHom g)) → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → ∀ t₀ : ℕ, (∀ t, t₀ ≤ t → ∀ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous t → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (f' ≫ (Spec.map (CommRingCat.ofHom g))) ((H').U k)) (fun j => (s' j).f k) (F) = 0) → ∃ F₁ : MvPolynomial (Fin (n + 1)) R, F₁.IsHomogeneous t ∧ (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F₁) = 0) ∧ MvPolynomial.map g F₁ = MvPolynomial.map g F) → IsPullback φ f' f (Spec.map (CommRingCat.ofHom g)) := by
  intro R _ X f H n s hH ⟨hc, hs⟩ R' _ g hg X' f' H' s' φ w hH' ⟨hc', hs'⟩ hw _ hrel t₀ hlift
  choose ha r hr hsur using hs
  choose ha' r' hr' hsur' using hs'
  have hR : ∀ i, IsRatioFamily s i (r i) := hr
  have hR' : ∀ i, IsRatioFamily s' i (r' i) := hr'
  have unit : ∀ i z k, φ z ∈ H.U k → (φ z ∈ nonzeroLocus (s i) ↔ IsUnit (gs φ z _ ((s i).f k))) := fun i z k hk =>
    ((mem_nonzeroLocus_iff_isUnit _ hk).trans (LBGerm.isUnit_gs_iff (𝟙 X) _ _ hk _)).trans
      (LBGerm.isUnit_gs_iff φ z _ hk _).symm
  have hUV : ∀ i, nonzeroLocus (s' i) = φ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext z
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    refine (mem_nonzeroLocus_iff_isUnit _ hk').trans (Iff.trans ?_ (unit i z k hk).symm)
    rw [hrel i z k k' hk hk', Units.isUnit_units_mul]
  have hrr : ∀ i j, (φ.appLE _ _ (hUV i).le).hom (r i j) = r' i j := fun i j => fn_ext fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    have hz₁ : φ z ∈ nonzeroLocus (s i) := (hUV i).le hz
    have h : φ z ∈ nonzeroLocus (s i) ⊓ H.U k := ⟨hz₁, hk⟩
    have e := congrArg (gs φ z _) (hr i j k)
    rw [gs_res _ z _ h, gs_mul _ z _ h, gs_res _ z _ h, gs_res _ z _ h] at e
    rw [gs_appLE φ _ z hz]
    refine ((unit i z k hk).1 hz₁).mul_right_cancel (e.symm.trans ?_)
    rw [hrel j z k k' hk hk', hrel i z k k' hk hk', (hR' i).gs_eq hz hk' j]
    ring
  have hev : ∀ i p, (φ.appLE _ _ (hUV i).le).hom (eval₂Hom (cst f _) (r i) p) =
      eval₂Hom (cst (f' ≫ Spec.map (CommRingCat.ofHom g)) _) (r' i) p := fun i p => by
    rw [map_eval₂Hom, appLE_cst, hw]
    simp only [hrr]
  refine isPullback_of_charts g hg φ f f' hw _ _ hUV hc ha ha' (fun i b => ?_) fun i a h0 B _ θ c hθ => ?_
  · obtain ⟨q, rfl⟩ := hsur' i b
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective g hg q
    exact ⟨_, (hev i p).trans (by rw [cst_comp, eval₂Hom_map_hom])⟩
  · obtain ⟨p, rfl⟩ := hsur i a
    rw [hev] at h0
    obtain ⟨t, ht, F, hF, G, hG⟩ := ((Filter.eventually_ge_atTop t₀).and
      (eventually_exists_form _ hc' ha' r' hR' i p h0)).exists
    obtain ⟨F₁, h₁, h₂, h₃⟩ := hlift t ht F hF.1 hF.2
    have e₁ : eval₂Hom (cst f _) (r i) F₁ = 0 := (hR i).eval_eq_zero f ⟨h₁, h₂⟩
    have e₂ : eval₂Hom (cst f _) (r i) p = eval₂Hom (cst f _) (r i) F := by
      rw [eq_add_of_sub_eq hG, map_add, map_mul, map_sub, map_one, eval₂Hom_X', (hR i).self_eq_one]
      simp
    have e₃ : ∀ P, θ (eval₂Hom (cst f _) (r i) P) = eval₂Hom c (fun j => θ (r i j)) (MvPolynomial.map g P) :=
      fun P => by rw [map_eval₂Hom, hθ, eval₂Hom_map_hom]
    rw [e₂, e₃, ← h₃, ← e₃, e₁, map_zero]

end GlobalTheory.ProjBaseChange
end

