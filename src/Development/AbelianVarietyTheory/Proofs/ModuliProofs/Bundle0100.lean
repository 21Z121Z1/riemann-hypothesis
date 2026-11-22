import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0053
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0086
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfInvariant
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IsoDescent

variable {X X' Y Y' : Scheme.{0}}

theorem exists_gen_of_invariant (M : LB Y) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (a : ∀ j, Γ(Y', m ⁻¹ᵁ M.U j)ˣ)
    (hc : ∀ (y : Y') i j, m y ∈ M.U i → m y ∈ M.U j →
      gm (𝟙 Y') y _ (a i) = gm m y (M.U i ⊓ M.U j) (M.g i j) * gm (𝟙 Y') y _ (a j))
    (hinv : ∀ i (y : Y') j, m y ∈ M.U j → m (t i y) ∈ M.U j → gm (t i) y _ (a j) = gm (𝟙 Y') y _ (a j)) :
    ∃ v : LB.Gen M, v.IsGen := by
  have hinj : ∀ U : Y.Opens, Function.Injective (m.app U).hom := by
    intro U g g' h
    refine (hd U ((m.app U).hom g) fun i e => fn_ext fun y hy => ?_).unique rfl h.symm
    refine (gs_res (𝟙 Y') y e hy _).trans ((gs_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ U) (e hy) _).trans
      ((gs_pull (𝟙 Y' ≫ t i) m y U (e hy) _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') m y _ hy _).symm)))
    rw [Category.assoc, ht]
  have hunit : ∀ (U : Y.Opens) (a : Γ(Y', m ⁻¹ᵁ U)ˣ),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), res e (pullU (t i) _ a) = a) →
      ∃ b : Γ(Y, U)ˣ, pullU m U b = a := by
    intro U a ha
    obtain ⟨g, hg, -⟩ := hd U a.val fun i e => congrArg Units.val (ha i e)
    obtain ⟨g', hg', -⟩ := hd U (a⁻¹).val fun i e => congrArg Units.val
      (show res e (pullU (t i) _ a⁻¹) = a⁻¹ by rw [map_inv, map_inv, ha i e])
    have h1 : g * g' = 1 := hinj U (by rw [map_mul, map_one, hg, hg']; exact a.mul_inv)
    exact ⟨⟨g, g', h1, (mul_comm _ _).trans h1⟩, Units.ext hg⟩
  have hex : ∀ j, ∃ b : Γ(Y, M.U j)ˣ, pullU m _ b = a j := by
    intro j
    refine hunit _ _ fun i e => unit_ext fun y hy => ?_
    refine (gm_res (𝟙 Y') y e hy _).trans ((gm_pull (𝟙 Y') (t i) y (m ⁻¹ᵁ M.U j) (e hy) _).trans ?_)
    rw [Category.id_comp]
    exact hinv i y j hy (e hy)
  choose b hb using hex
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU m _ _ = pullU m _ _ from unit_ext fun y hy => ?_)))⟩
  have val : ∀ j, y ∈ m ⁻¹ᵁ M.U j → gm (𝟙 Y' ≫ m) y _ (b j) = gm (𝟙 Y') y _ (a j) := fun j hj =>
    (gm_pull (𝟙 Y') m y _ hj _).symm.trans (congrArg _ (hb j))
  refine (gm_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m y _ hy _).symm)
  refine ((gm_res _ y _ hy _).trans (val i hy.1)).trans ((hc y i j hy.1 hy.2).trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (by rw [Category.id_comp])
    ((gm_res _ y _ hy _).trans (val j hy.2)))

variable {L : LB X} {L' : LB X'} {K K' : Type} [Fintype K] [Fintype K']

theorem lbIso_of_invariant (hL : L.IsLB) (hL' : L'.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X'))
    (ε' : K' → ℤ) (m : Y' ⟶ Y) {I : Type} (t : I → (Y' ⟶ Y')) (ht : ∀ i, t i ≫ m = m)
    (hd : ∀ (U : Y.Opens) (f : Γ(Y', m ⁻¹ᵁ U)),
      (∀ i (e : m ⁻¹ᵁ U ≤ t i ⁻¹ᵁ (m ⁻¹ᵁ U)), ((t i).appLE _ _ e).hom f = f) →
      ∃! g : Γ(Y, U), (m.app U).hom g = f)
    (u : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε)) (hu : u.IsGen)
    (u' : LB.Gen (LB.LinComb L' (fun k => m ≫ φ' k) ε')) (hu' : u'.IsGen)
    (hinv : ∀ i y J J', Good L y J → Good L' y J' →
      val u' (t i) y J' * (val u (t i) y J)⁻¹ = val u' (𝟙 Y') y J' * (val u (𝟙 Y') y J)⁻¹) :
    LBIso (LB.LinComb L φ ε) (LB.LinComb L' φ' ε') := by
  have l₁ : ∀ p : (K' → L'.ι) × (K → L.ι), m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) ≤
      LB.wchart L' (fun k => m ≫ φ' k) p.1 := fun p y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 k
  have l₂ : ∀ p : (K' → L'.ι) × (K → L.ι), m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) ≤
      LB.wchart L (fun k => m ≫ φ k) p.2 := fun p y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 k
  have v : ∀ (r : Y' ⟶ Y') (y : Y') (p : (K' → L'.ι) × (K → L.ι)),
      r y ∈ m ⁻¹ᵁ (LB.wchart L' φ' p.1 ⊓ LB.wchart L φ p.2) →
      gm r y _ (res (l₁ p) (u'.s p.1) * (res (l₂ p) (u.s p.2))⁻¹) =
        gm r y (LB.wchart L' (fun k => m ≫ φ' k) p.1) (u'.s p.1) *
          (gm r y (LB.wchart L (fun k => m ≫ φ k) p.2) (u.s p.2))⁻¹ := fun r y p h =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r y _ h _)
      ((map_inv _ _).trans (congrArg (·⁻¹) (gm_res r y _ h _))))
  refine exists_gen_of_invariant (LB.div (LB.LinComb L' φ' ε') (LB.LinComb L φ ε)) m t ht hd
    (fun p => res (l₁ p) (u'.s p.1) * (res (l₂ p) (u.s p.2))⁻¹) (fun y p q hp hq => ?_) (fun i y p hp hp' => ?_)
  · refine (v (𝟙 Y') y p hp).trans (Eq.trans ?_ (congrArg₂ (· * ·) ((gm_div _ _ m y p q ⟨hp, hq⟩).trans
      (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L' φ' ε' m y p.1 q.1 hp.1 hq.1)
        (gm_linComb L φ ε m y p.2 q.2 hp.2 hq.2))) (v (𝟙 Y') y q hq)).symm)
    rw [gen_trans hu' (𝟙 Y') y (l₁ p hp) (l₁ q hq), gen_trans hu (𝟙 Y') y (l₂ p hp) (l₂ q hq), mul_inv,
      mul_mul_mul_comm]
    simp only [trF, Category.id_comp]
  · choose J hJ using fun χ : Y' ⟶ X => exists_chart hL (χ y)
    choose J' hJ' using fun χ : Y' ⟶ X' => exists_chart hL' (χ y)
    have gJ : Good L y J := hJ
    have gJ' : Good L' y J' := hJ'
    refine (v (t i) y p hp').trans (Eq.trans ?_ (v (𝟙 Y') y p hp).symm)
    rw [gen_trans hu' (t i) y (l₁ p hp') (gJ'.mem _ _), gen_trans hu (t i) y (l₂ p hp') (gJ.mem _ _),
      gen_trans hu' (𝟙 Y') y (l₁ p hp) (gJ'.mem _ _), gen_trans hu (𝟙 Y') y (l₂ p hp) (gJ.mem _ _),
      mul_inv, mul_inv, mul_mul_mul_comm, mul_mul_mul_comm (trF _ _ (𝟙 Y') _ _ _)]
    refine congrArg₂ (· * ·) ?_ (hinv i y J J' gJ gJ')
    have e : ∀ {W : Scheme.{0}} (χ : Y ⟶ W), t i ≫ m ≫ χ = 𝟙 Y' ≫ m ≫ χ := fun χ => by
      rw [reassoc_of% ht i, Category.id_comp]
    exact congrArg₂ (fun a b => a * b⁻¹) (Finset.prod_congr rfl fun k _ => congrArg
      (fun ψ : Y' ⟶ X' => gm ψ y (L'.U (p.1 k) ⊓ L'.U (J' ψ)) (L'.g (p.1 k) (J' ψ)) ^ ε' k) (e (φ' k)))
      (Finset.prod_congr rfl fun k _ => congrArg
        (fun ψ : Y' ⟶ X => gm ψ y (L.U (p.2 k) ⊓ L.U (J ψ)) (L.g (p.2 k) (J ψ)) ^ ε k) (e (φ k)))

theorem lbIso_of_gens (hL : L.IsLB) (hL' : L'.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X'))
    (ε' : K' → ℤ) (u : LB.Gen (LB.LinComb L φ ε)) (hu : u.IsGen) (u' : LB.Gen (LB.LinComb L' φ' ε'))
    (hu' : u'.IsGen) : LBIso (LB.LinComb L φ ε) (LB.LinComb L' φ' ε') :=
  lbIso_of_invariant hL hL' φ ε φ' ε' (𝟙 Y) (I := PEmpty) PEmpty.elim (fun i => i.elim)
    (fun _ f _ => ⟨f, rfl, fun _ h => h⟩) _ (DVR.pullGen_isGen _ _ _ u hu (𝟙 Y)) _
    (DVR.pullGen_isGen _ _ _ u' hu' (𝟙 Y)) (fun i => i.elim)

def chartPullDiv (M N : LB Y) (f : Y' ⟶ Y) :
    ChartPull ((LB.div M N).pull f) (LB.div (M.pull f) (N.pull f)) (𝟙 Y') :=
  have le : ∀ J : PUnit → M.ι × N.ι, ((LB.div M N).pull f).U J ≤
      (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (N.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    ⟨mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).1, mem_pull.2 ((mem_pull (L := LB.div M N)).1 hy).2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g (LB.div M N) f (𝟙 Y') y J J' hJ hJ').trans ((gm_div N M (𝟙 Y' ≫ f) y _ _
        ⟨(mem_pull (L := LB.div M N)).1 hJ, (mem_pull (L := LB.div M N)).1 hJ'⟩).trans (Eq.symm ((gm_div (N.pull f) (M.pull f) (𝟙 Y') y
          (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
          (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) ⟨le J hJ, le J' hJ'⟩).trans ?_)))
      exact congrArg₂ (fun a b => a * b⁻¹) (gm_pull_g M f (𝟙 Y') y _ _ (le J hJ).1 (le J' hJ').1)
        (gm_pull_g N f (𝟙 Y') y _ _ (le J hJ).2 (le J' hJ').2) }

def chartPullFlat (L : LB X) (F : X' ⟶ X) (e : ℤ) (ψ : K → (Y ⟶ X')) (ε : K → ℤ) (f : Y' ⟶ Y) :
    ChartPull ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f)
      (LB.LinComb L (fun k => f ≫ ψ k ≫ F) (fun k => ε k * e)) (𝟙 Y') :=
  have mem : ∀ (J : PUnit → K → PUnit → L.ι) (y : Y'),
      y ∈ ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f).U J →
      ∀ k, ψ k (f y) ∈ LB.wchart L (fun _ : PUnit => F) (J PUnit.unit k) := fun J y hy k =>
    Set.mem_iInter.1 ((mem_pull (L := LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε)).1 hy) k
  have le : ∀ J : PUnit → K → PUnit → L.ι,
      ((LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε).pull f).U J ≤
        LB.wchart L (fun k => f ≫ ψ k ≫ F) (fun k => J PUnit.unit k PUnit.unit) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem J y hy k) PUnit.unit
  { idx := fun J k => J PUnit.unit k PUnit.unit
    le := le
    g := fun y J J' hJ hJ' => by
      refine (gm_pull_g _ f (𝟙 Y') y J J' hJ hJ').trans ((gm_linComb
        (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε (𝟙 Y' ≫ f) y (J PUnit.unit) (J' PUnit.unit)
        (Set.mem_iInter.2 (mem J y hJ)) (Set.mem_iInter.2 (mem J' y hJ'))).trans (Eq.trans
          (Finset.prod_congr rfl fun k _ => ?_) (gm_linComb L _ _ (𝟙 Y') y _ _ (le J hJ) (le J' hJ')).symm))
      refine (congrArg (· ^ ε k) (gm_linComb L (fun _ : PUnit => F) (fun _ => e) ((𝟙 Y' ≫ f) ≫ ψ k) y _ _
        (mem J y hJ k) (mem J' y hJ' k))).trans ?_
      rw [Fintype.prod_unique, ← zpow_mul, mul_comm e]
      simp only [Category.assoc] }

theorem exists_gen_div_pull {W : Scheme.{0}} (L : LB X) (L' : LB X') (F : W ⟶ X) (F' : W ⟶ X') (e e' : ℤ)
    (ψ : K → (Y ⟶ W)) (ε : K → ℤ) (f : Y' ⟶ Y)
    (H : LBIso (LB.LinComb L (fun k => f ≫ ψ k ≫ F) (fun k => ε k * e))
      (LB.LinComb L' (fun k => f ≫ ψ k ≫ F') (fun k => ε k * e'))) :
    ∃ t : LB.Gen ((LB.div (LB.LinComb (LB.LinComb L' (K := PUnit) (fun _ => F') (fun _ => e')) ψ ε)
      (LB.LinComb (LB.LinComb L (K := PUnit) (fun _ => F) (fun _ => e)) ψ ε)).pull f), t.IsGen := by
  obtain ⟨w, hw⟩ := H.chartPull (chartPullFlat L F e ψ ε f) (chartPullFlat L' F' e' ψ ε f)
  exact gen_chartPull (chartPullDiv _ _ f) w hw

end GlobalTheory.IsoDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.RigidBundleGlue

variable {X Y Z : Scheme.{0}}

theorem exists_gen_of_lbIso {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId P) (chartPullPull Q (𝟙 X) (𝟙 X) rfl)
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull P (𝟙 X) (𝟙 X) rfl) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

theorem LBIso.pull {P Q : LB X} (h : LBIso P Q) (f : Y ⟶ X) : LBIso (P.pull f) (Q.pull f) :=
  h.chartPull (chartPullPull P f f rfl) (chartPullPull Q f f rfl)

def chartPullComp (L : LB X) (f : Y ⟶ X) (g : Z ⟶ Y) (c : Z ⟶ X) (e : c = g ≫ f) :
    ChartPull (L.pull c) ((L.pull f).pull g) (𝟙 Z) := by
  subst e
  exact chartPullIn L (fun _ : PUnit => f) (fun _ => 1) g

theorem eq_one_of_section {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {e : S ⟶ A.left}
    (he : e ≫ A.hom = 𝟙 S) (V : S.Opens) (u : Γ(A.left, A.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (A.hom ⁻¹ᵁ V))
    (hu : (e.appLE _ V h).hom u = 1) : u = 1 := by
  have := hA.smooth
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  have := GlobalFunctions.isIso_app FlatFibreInjective.injective_baseChange exists_noetherian_model_of_smooth A.hom V
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (A.hom.app V)).2 u
  have k : ∀ (q : S ⟶ S) (_ : q = 𝟙 S) (l : V ≤ q ⁻¹ᵁ V), (q.appLE V V l).hom a = a := by
    rintro _ rfl l
    have : (𝟙 S : S ⟶ S).appLE V V l = 𝟙 _ := by
      simp [Scheme.Hom.appLE]
      exact S.presheaf.map_id _
    rw [this]; rfl
  have h₁ : (e.appLE _ V h).hom ((A.hom.app V).hom a) = a :=
    (congrArg (fun q => q.hom a) (Scheme.Hom.comp_appLE e A.hom V V h)).symm.trans (k (e ≫ A.hom) he h)
  rw [h₁.symm.trans hu, map_one]

theorem eSec_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) : eSec G' ≫ φ = f ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem exists_glue : ∀ (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A] (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left), iSup U = ⊤ → (∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) → IsAbelianScheme A → (∀ i, IsAbelianScheme (G i)) → ∀ (M : ∀ i, LB (G i).left) (B : I → I → Scheme.{0}) (a : ∀ i j, B i j ⟶ (G i).left) (b : ∀ i j, B i j ⟶ (G j).left), (∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j)) → (∀ i, (M i).IsLB) → (∀ i, Out.Rigidified (G i) (M i)) → (∀ i j, LBIso ((M i).pull (a i j)) ((M j).pull (b i j))) → ∃ L : LB A.left, L.IsLB ∧ Out.Rigidified A L ∧ ∀ i, LBIso (M i) (L.pull (ψ i)) := by
  intro S I U A _ G _ ψ hU hψ hA _ M B a b hB hM hr hiso
  have oi : ∀ i, IsOpenImmersion (ψ i) := fun i => CoverGlue.isOpenImmersion (hψ i).1
  choose N hN₁ hN₂ hN₃ hN₄ using fun i => GlobalTheory.T.exists_cechData_pullback_of_lineBundle_on_open _ _ (ψ i) (M i) (hM i)
  have hR : ∀ i x, x ∈ (ψ i).opensRange ↔ A.hom x ∈ U i := fun i x => CoverGlue.mem_range (hψ i).1 x
  have hNU : ∀ i k, (N i).U k ≤ (ψ i).opensRange := fun i k => (le_iSup (N i).U k).trans (hN₁ i).le
  let e : S ⟶ A.left := eSec A
  have he : e ≫ A.hom = 𝟙 S := Over.w η[A]
  obtain ⟨L, hL, hLr, hLi⟩ := GlobalTheory.T.exists_glue_rigidified_partial_line_bundles A.left S A.hom e I U N he (eq_one_of_section A hA he) hU
    (fun i => (hN₁ i).trans (TopologicalSpace.Opens.ext (Set.ext (hR i)))) hN₂
    (fun i => by
      refine (GlobalTheory.T.generator_iso_extend_from_open_containing_charts S (U i).toScheme (U i).ι).1 _ (fun k s hs => ?_) ?_
      · have h₁ := (hR i _).1 (hNU i _ (mem_pull.1 hs))
        rw [← Scheme.Hom.comp_apply, he] at h₁
        exact ⟨⟨s, h₁⟩, rfl⟩
      · let e' : (U i).toScheme ⟶ (G i).left := eSec (G i)
        have hc : e' ≫ ψ i = (U i).ι ≫ e := eSec_comm (hψ i)
        obtain ⟨t, ht⟩ := exists_gen_of_lbIso (pull_isLB (hM i) e') (pull_isLB (hN₃ i) e')
          (LBIso.pull (hN₄ i) e') (hr i)
        obtain ⟨t', ht'⟩ := gen_chartPull (chartPullComp (N i) (ψ i) e' _ hc.symm) t ht
        exact gen_chartPull (chartPullOut (N i) (fun _ : PUnit => e) (fun _ => 1) (U i).ι _ fun _ => rfl) t' ht')
    (fun i j => by
      have : IsOpenImmersion (a i j) :=
        MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hB i j).flip (oi j)
      refine (GlobalTheory.T.generator_iso_extend_from_open_containing_charts A.left (B i j) (a i j ≫ ψ i)).2 _ _ (fun k l x hx => ?_) ?_
      · obtain ⟨y, hy⟩ := hNU i k hx.1
        obtain ⟨y', hy'⟩ := hNU j l hx.2
        obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (hB i j) y y' (hy.trans hy'.symm)
        exact ⟨z, by rw [Scheme.Hom.comp_apply, hz, hy]⟩
      · refine LBIso.chartPull (chartPullComp (N i) (ψ i) (a i j) _ rfl)
          (chartPullComp (N j) (ψ j) (b i j) _ (hB i j).w) ?_
        exact ((LBIso.pull (hN₄ i) (a i j)).symm.trans (pull_isLB (hN₃ i) _) (pull_isLB (hM i) _)
          (pull_isLB (hM j) _) (hiso i j)).trans (pull_isLB (hN₃ i) _) (pull_isLB (hM j) _) (pull_isLB (hN₃ j) _)
          (LBIso.pull (hN₄ j) (b i j)))
  exact ⟨L, hL, hLr, fun i => (hN₄ i).trans (hM i) (hN₃ i) (pull_isLB hL _) (LBIso.pull (hLi i) (ψ i))⟩

end GlobalTheory.RigidBundleGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'}
  {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left}

theorem isCommMonObj_of_isGrpPullback [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    (h : IsGrpPullback G' G f φ) : IsCommMonObj G' := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
  rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
    ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]

theorem isAbelianScheme_of_isGrpPullback [GrpObj G] [GrpObj G'] (hG : IsAbelianScheme G)
    (h : IsGrpPullback G' G f φ) : IsAbelianScheme G' where
  comm := have := hG.comm; isCommMonObj_of_isGrpPullback h
  smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth
  proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper
  geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected

theorem relAmple_restrict (h : IsPullback φ G'.hom G.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    (e : LBIso L' (L.pull φ)) (hA : Out.RelAmple G L) (V : S.Opens) (hV : IsAffineOpen V) :
    Out.RelAmple (Over.mk (G'.hom ∣_ (f ⁻¹ᵁ V))) (L'.pull (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) := by
  have H : IsPullback ((G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (G'.hom ∣_ (f ⁻¹ᵁ V)) G.hom ((f ⁻¹ᵁ V).ι ≫ f) :=
    (isPullback_morphismRestrict G'.hom (f ⁻¹ᵁ V)).flip.paste_horiz h
  obtain ⟨w, hw⟩ : LBIso (L'.pull (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) (L.pull ((G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ)) :=
    LBIso.chartPull (chartPullPull L' _ _ rfl)
      (chartPullSame L (fun _ : PUnit => (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (fun _ => φ) (fun _ => 1) _ fun _ => rfl) e
  exact relAmple_pull (A' := Over.mk (G'.hom ∣_ (f ⁻¹ᵁ V))) H hL (pull_isLB hL' _)
    ((isGen_iff w).1 hw) V hV (fun y => y.2) hA

theorem pol_pull_of_relAmple_local
    (hloc : ∀ (S : Scheme.{0}) (A : Over S) (L : LB A.left), L.IsLB → QuasiCompact A.hom → QuasiSeparated A.hom →
      (∀ s : S, ∃ (U : S.Opens) (_ : s ∈ U),
        Out.RelAmple (Over.mk (A.hom ∣_ U)) (L.pull (A.hom ⁻¹ᵁ U).ι)) → Out.RelAmple A L) :
    ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L') := by
  intro S S' G G' _ _ f φ L L' hL hL' hG h e
  have hG' := isAbelianScheme_of_isGrpPullback hG h
  have := hG'.proper
  refine ⟨hG', fun hA => hloc S' G' L' hL' inferInstance inferInstance fun s => ?_, fun hK => ?_⟩
  · obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f s) trivial
    exact ⟨f ⁻¹ᵁ V, hs, relAmple_restrict h.1 hL hL' e hA V hV⟩
  · obtain ⟨w, hw⟩ := e
    exact kTriv_pull h hL hL' ((isGen_iff w).1 hw) hK

end GlobalTheory.PolPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfProper
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

section Pts

variable {k : Type} [Field k] [IsAlgClosed k]

theorem hom_ext_pts {X Y : Over (Sp k)} (hX : Smooth X.hom) [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k _ X.hom hX).1
  exact Over.OverMorphism.ext (ComplexPoints.hom_ext_of_points X.hom Y.hom (by rw [Over.w, Over.w]) fun x hx =>
    congrArg (fun q => q.left) (h (Over.homMk x hx)))

theorem exists_lift_pt {S : Scheme.{0}} {A B : Over S} (ψ : A ⟶ B) [LocallyOfFiniteType ψ.left] [Surjective ψ.left]
    (t : Sp k ⟶ S) (y : Over.mk t ⟶ B) : ∃ x : Over.mk t ⟶ A, x ≫ ψ = y := by
  let y' : Sp k ⟶ B.left := y.left
  obtain ⟨z, -⟩ := (pullback.snd ψ.left y').surjective (default : PrimeSpectrum k)
  obtain ⟨x, hx, -⟩ := ComplexPoints.exists_point_mem (pullback.snd ψ.left y') (Z := Set.univ)
    isClosed_univ.isLocallyClosed ⟨z, trivial⟩
  have e : (x ≫ pullback.fst ψ.left y') ≫ ψ.left = y' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hx]
  exact ⟨Over.homMk (x ≫ pullback.fst ψ.left y') (by rw [← Over.w ψ, ← Category.assoc, e]; exact Over.w y),
    Over.OverMorphism.ext e⟩

theorem exists_fac {A B Y : Over (Sp k)} [GrpObj A] [GrpObj B] [GrpObj Y] (hA : Smooth A.hom) [IsSeparated Y.hom]
    (ψ₀ : A ⟶ B) [IsMonHom ψ₀] [Etale ψ₀.left] [Surjective ψ₀.left] [QuasiCompact ψ₀.left] (ψ : A ⟶ Y) [IsMonHom ψ]
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ ψ₀ = 1 → x ≫ ψ = 1) : ∃ α : B ⟶ Y, ψ₀ ≫ α = ψ := by
  let R : Over (Sp k) := Over.mk (pullback.fst ψ₀.left ψ₀.left ≫ A.hom)
  let p₁ : R ⟶ A := Over.homMk (pullback.fst _ _) rfl
  let p₂ : R ⟶ A := Over.homMk (pullback.snd _ _) (by
    show _ = pullback.fst ψ₀.left ψ₀.left ≫ A.hom
    rw [← Over.w ψ₀, ← pullback.condition_assoc])
  have e₀ : p₁ ≫ ψ₀ = p₂ ≫ ψ₀ := Over.OverMorphism.ext pullback.condition
  have e : p₁ ≫ ψ = p₂ ≫ ψ := hom_ext_pts (inferInstanceAs (Smooth (pullback.fst ψ₀.left ψ₀.left ≫ A.hom))) fun x => by
    have := h ((x ≫ p₁) * (x ≫ p₂)⁻¹) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, e₀, Category.assoc, mul_inv_cancel])
    rw [MonObj.mul_comp, GrpObj.inv_comp, mul_inv_eq_one, Category.assoc, Category.assoc] at this
    exact this
  have e' : pullback.fst ψ₀.left ψ₀.left ≫ ψ.left = pullback.snd ψ₀.left ψ₀.left ≫ ψ.left :=
    congrArg (fun q => q.left) e
  have hd : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.left), g₁ ≫ ψ₀.left = g₂ ≫ ψ₀.left → g₁ ≫ ψ.left = g₂ ≫ ψ.left :=
    fun g₁ g₂ hg => by
      rw [← pullback.lift_fst g₁ g₂ hg, Category.assoc, e', pullback.lift_snd_assoc]
  have f := EffectiveEpi.fac ψ₀.left ψ.left hd
  refine ⟨Over.homMk (EffectiveEpi.desc ψ₀.left ψ.left hd) ?_, Over.OverMorphism.ext f⟩
  rw [← cancel_epi ψ₀.left, reassoc_of% f, Over.w, Over.w]

theorem isIso_of_mono {A B : Over (Sp k)} (α : A ⟶ B) [IsProper A.hom] [IsSeparated B.hom] (hB : Smooth B.hom)
    [Mono α.left] (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ B, ∃ x, x ≫ α = y) : IsIso α := by
  have := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k _ B.hom hB).1
  have : IsProper (α.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper α.left := IsProper.of_comp α.left B.hom
  have : IsClosedImmersion α.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have : Surjective α.left := ComplexPoints.surjective_of_geomPoints_lift B.hom (𝟙 (Sp k)) α.left
    α.left.isClosedEmbedding.isClosed_range fun y hy => by
      obtain ⟨x, hx⟩ := h (Over.homMk y hy)
      exact ⟨x.left, congrArg (fun q => q.left) hx⟩
  have : IsIso α.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map α) := ‹_›
  exact isIso_of_reflects_iso α (Over.forget _)

omit [IsAlgClosed k] in

theorem toUnit_comp_injective {K : Type} [Field K] (x : Sp K ⟶ Sp k) (A : Over (Sp k)) :
    Function.Injective (fun z : 𝟙_ (Over (Sp k)) ⟶ A => toUnit (Over.mk x) ≫ z) := by
  have : Surjective x := ⟨fun z => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have : Epi x := Flat.epi_of_flat_of_surjective x
  intro a b h
  have e : (toUnit (Over.mk x)).left = x := by simp
  have h' : (toUnit (Over.mk x)).left ≫ a.left = (toUnit (Over.mk x)).left ≫ b.left := congrArg (fun q => q.left) h
  rw [e] at h'
  exact Over.OverMorphism.ext ((cancel_epi x).1 h')

theorem exists_of_torsion (hM : Out.MulNSt) (P : Out.PolAV (Sp k)) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ Sp k) {n : ℕ} (hk : (n : k) ≠ 0) (hK : (n : K) ≠ 0) (z : Over.mk x ⟶ P.A) (hz : z ^ n = 1) :
    ∃ z₀ : 𝟙_ (Over (Sp k)) ⟶ P.A, toUnit (Over.mk x) ≫ z₀ = z := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have c₁ : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} = n ^ (2 * P.g) := (hM _ P n hn).2.2.2.2 k (𝟙 _) hk
  have c₂ := (hM _ P n hn).2.2.2.2 K x hK
  have : Finite {y : Over.mk x ⟶ P.A // y ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  let F : {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} → {y : Over.mk x ⟶ P.A // y ^ n = 1} := fun a =>
    ⟨toUnit _ ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun a b h => Subtype.ext (toUnit_comp_injective x _ (congrArg Subtype.val h)), c₁.trans c₂.symm⟩
  obtain ⟨a, ha⟩ := hF.2 ⟨z, hz⟩
  exact ⟨a.1, congrArg Subtype.val ha⟩

end Pts

theorem exists_ptsEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (y : T.left ⟶ S) (e : T.hom ≫ f = y) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk y ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  subst e
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun z => ?_⟩, fun _ => rfl⟩
  exact ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem unitOn_bijective (R : Type) [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem unitOn_pow {R : Type} [CommRing R] (c : Rˣ) (n : ℕ) : unitOn (c ^ n) = unitOn c ^ n := map_pow _ _ _

theorem unitOn_one {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := map_one _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isAbelianScheme_of_proper {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom) : IsAbelianScheme t.G :=
  ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩

theorem exists_dim {k : Type} [Field k] (t : SAB H (Sp k)) : ∃ g, SmoothOfRelativeDimension g t.G.hom := by
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  exact exists_dim_of_preconnected t.G.hom (eSec t.G (default : PrimeSpectrum k))

abbrev polOf {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L)
    (hk : Out.KTriv t.G t.PP.L) {g : ℕ} (hg : SmoothOfRelativeDimension g t.G.hom) : Out.PolAV S where
  A := t.G
  isAb := isAbelianScheme_of_proper t hp
  g := g
  smoothDim := hg
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := fun _ => ⟨⊤, trivial, by
    obtain ⟨-, ws, gs', -⟩ := t.sym
    exact gen_of_iso ((isGen_iff ws).1 gs') _⟩
  ample := ha
  ktriv := hk

end GlobalTheory.HeckePoint
end
end

