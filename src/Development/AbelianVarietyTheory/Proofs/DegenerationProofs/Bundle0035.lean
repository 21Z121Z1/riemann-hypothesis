import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueRigidifiedGeneratorExtendNormal
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalHomAndIsAdicCompleteOfFiniteDvr
section
namespace GlobalTheory

open IsLocalRing in
private lemma exists_pow_maximalIdeal_eq_span {V V' : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V']
    [Algebra V V'] [IsLocalHom (algebraMap V V')] (hinj : Function.Injective (algebraMap V V'))
    {ϖ : V} (hϖ : Irreducible ϖ) :
    ∃ e : ℕ, 0 < e ∧ ∀ n, maximalIdeal V' ^ (e * n) = Ideal.span {algebraMap V V' ϖ ^ n} := by
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible V'
  have h0 : algebraMap V V' ϖ ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap V V')]
    exact fun h => hϖ.ne_zero (hinj h)
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 hϖ'
  have hnu : ¬ IsUnit (algebraMap V V' ϖ) := fun h => hϖ.not_isUnit (isUnit_of_map_unit _ _ h)
  refine ⟨e, Nat.pos_of_ne_zero fun he => hnu ?_, fun n => ?_⟩
  · rw [hu, he, pow_zero, mul_one]; exact u.isUnit
  · rw [hϖ'.maximalIdeal_eq, Ideal.span_singleton_pow, hu, mul_pow, ← pow_mul,
      ← Units.val_pow_eq_pow_val, Ideal.span_singleton_mul_left_unit (u ^ n).isUnit]

open IsLocalRing in
private lemma mem_span_pow_iff_repr {V V' : Type} [CommRing V] [CommRing V'] [Algebra V V']
    {ι : Type} [Fintype ι] (b : Module.Basis ι V V') (ϖ : V) (j : ℕ) (x : V') :
    x ∈ Ideal.span {algebraMap V V' ϖ ^ j} ↔ ∀ i, b.repr x i ∈ Ideal.span {ϖ ^ j} := by
  simp only [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, rfl⟩ i
    refine ⟨b.repr y i, ?_⟩
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
      smul_eq_mul, mul_comm]
  · intro h
    choose c hc using h
    refine ⟨∑ i, c i • b i, ?_⟩
    rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, Finset.smul_sum]
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc i, smul_smul, mul_comm (ϖ ^ j)]

open IsLocalRing in

theorem _root_.GlobalTheory.isLocalHom_and_isAdicComplete_of_finite_dvr :
    ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CommRing V'] [IsDomain V']
      [IsDiscreteValuationRing V'] [Algebra V V'], Module.Finite V V' →
      Function.Injective (algebraMap V V') →
      IsLocalHom (algebraMap V V') ∧ IsAdicComplete (IsLocalRing.maximalIdeal V') V' := by
  intro V V' _ _ _ _ _ _ _ _ hfin hinj
  have hloc : IsLocalHom (algebraMap V V') :=
    RingHom.IsIntegral.isLocalHom (fun x => Algebra.IsIntegral.isIntegral x) hinj
  refine ⟨hloc, ?_⟩
  haveI : FaithfulSMul V V' := (faithfulSMul_iff_algebraMap_injective V V').2 hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨e, he, hpow⟩ := exists_pow_maximalIdeal_eq_span hinj hϖ
  let b := Module.Free.chooseBasis V V'
  have hV : ∀ j, (maximalIdeal V ^ j • ⊤ : Submodule V V) = Ideal.span {ϖ ^ j} := by
    intro j
    rw [smul_eq_mul, Ideal.mul_top, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hV' : ∀ n, (maximalIdeal V' ^ n • ⊤ : Submodule V' V') = maximalIdeal V' ^ n := by
    intro n
    rw [smul_eq_mul, Ideal.mul_top]
  haveI hH : IsHausdorff (maximalIdeal V') V' :=
    IsHausdorff.of_isLocalRing (maximalIdeal V') V' (IsLocalRing.maximalIdeal.isMaximal V').ne_top
  have hP : IsPrecomplete (maximalIdeal V') V' := by
    rw [isPrecomplete_iff]
    intro f hf
    have hcoord : ∀ i : Module.Free.ChooseBasisIndex V V', ∀ {m n : ℕ}, m ≤ n →
        b.repr (f (e * m)) i ≡ b.repr (f (e * n)) i
          [SMOD maximalIdeal V ^ m • (⊤ : Submodule V V)] := by
      intro i m n hmn
      have h := hf (Nat.mul_le_mul_left e hmn)
      rw [hV', SModEq.sub_mem, hpow, mem_span_pow_iff_repr b] at h
      rw [hV, SModEq.sub_mem, ← Finsupp.sub_apply, ← map_sub]
      exact h i
    choose L hL using fun i =>
      (isPrecomplete_iff.1 (inferInstance : IsPrecomplete (maximalIdeal V) V)) _ (hcoord i)
    refine ⟨b.equivFun.symm L, fun n => ?_⟩
    have h1 : f n ≡ f (e * n) [SMOD maximalIdeal V' ^ n • (⊤ : Submodule V' V')] :=
      hf (Nat.le_mul_of_pos_left n he)
    have h2 : f (e * n) ≡ b.equivFun.symm L [SMOD maximalIdeal V' ^ n • (⊤ : Submodule V' V')] := by
      rw [hV', SModEq.sub_mem]
      refine Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left n he) ?_
      rw [hpow, mem_span_pow_iff_repr b]
      intro i
      have hi := hL i n
      rw [hV, SModEq.sub_mem] at hi
      rw [map_sub, Finsupp.sub_apply, ← b.equivFun_apply (b.equivFun.symm L),
        LinearEquiv.apply_symm_apply]
      exact hi
    exact h1.trans h2
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleIsoExtendOfNormalBase
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.IsoExtend

variable {X Y Y' : Scheme.{0}}

theorem exists_gen_chartPull {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (H : ∃ t : LB.Gen A, t.IsGen) : ∃ t : LB.Gen A', t.IsGen := by
  obtain ⟨w, hw⟩ := H
  refine ⟨⟨fun i => res (a.le i) (pullU h _ (w.s (a.idx i)))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have val : ∀ i, y ∈ A'.U i → gm (𝟙 Y') y _ (res (a.le i) (pullU h _ (w.s (a.idx i)))) =
      gm h y (A.U (a.idx i)) (w.s (a.idx i)) := fun i hi =>
    (gm_res (𝟙 Y') y (a.le i) hi _).trans ((gm_pull (𝟙 Y') h y _ (a.le i hi) _).trans (by rw [Category.id_comp]))
  have hm : h y ∈ A.U (a.idx i) ⊓ A.U (a.idx j) := ⟨a.le i hy.1, a.le j hy.2⟩
  have e := congrArg (gm h y (A.U (a.idx i) ⊓ A.U (a.idx j))) (hw (a.idx i) (a.idx j))
  have e' := (gm_res h y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    rfl (gm_res h y _ hm _))))
  refine ((gm_res (𝟙 Y') y _ hy _).trans (val i hy.1)).trans (e'.trans (Eq.symm ?_))
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (a.g y i j hy.1 hy.2)
    ((gm_res (𝟙 Y') y _ hy _).trans (val j hy.2)))

theorem gm_div_pull (L M : LB X) (f : Y ⟶ X) (y : Y) (J J' : PUnit → M.ι × L.ι) (p q : (PUnit → M.ι) × (PUnit → L.ι))
    (ep : J PUnit.unit = (p.1 PUnit.unit, p.2 PUnit.unit)) (eq : J' PUnit.unit = (q.1 PUnit.unit, q.2 PUnit.unit))
    (hJ : y ∈ ((LB.div M L).pull f).U J) (hJ' : y ∈ ((LB.div M L).pull f).U J')
    (hp : y ∈ (M.pull f).U p.1 ⊓ (L.pull f).U p.2) (hq : y ∈ (M.pull f).U q.1 ⊓ (L.pull f).U q.2) :
    gm (𝟙 Y) y (((LB.div M L).pull f).U J ⊓ ((LB.div M L).pull f).U J') (((LB.div M L).pull f).g J J') =
      gm (𝟙 Y) y ((LB.div (M.pull f) (L.pull f)).U p ⊓ (LB.div (M.pull f) (L.pull f)).U q)
        ((LB.div (M.pull f) (L.pull f)).g p q) := by
  refine (gm_pull_g (LB.div M L) f (𝟙 Y) y J J' hJ hJ').trans ?_
  rw [ep, eq]
  refine (gm_div L M (𝟙 Y ≫ f) y (p.1 PUnit.unit, p.2 PUnit.unit) (q.1 PUnit.unit, q.2 PUnit.unit)
    ⟨⟨mem_pull.1 hp.1, mem_pull.1 hp.2⟩, mem_pull.1 hq.1, mem_pull.1 hq.2⟩).trans (Eq.symm ?_)
  refine (gm_div (L.pull f) (M.pull f) (𝟙 Y) y p q ⟨hp, hq⟩).trans ?_
  exact congrArg₂ (· * ·) (gm_pull_g M f (𝟙 Y) y p.1 q.1 hp.1 hq.1)
    (congrArg (·⁻¹) (gm_pull_g L f (𝟙 Y) y p.2 q.2 hp.2 hq.2))

def chartPullDiv (L M : LB X) (f : Y ⟶ X) :
    ChartPull ((LB.div M L).pull f) (LB.div (M.pull f) (L.pull f)) (𝟙 Y) :=
  have le : ∀ (J : PUnit → M.ι × L.ι) (y : Y), y ∈ ((LB.div M L).pull f).U J →
      y ∈ (M.pull f).U (fun _ => (J PUnit.unit).1) ⊓ (L.pull f).U (fun _ => (J PUnit.unit).2) := fun J y hy =>
    have h : f y ∈ M.U (J PUnit.unit).1 ⊓ L.U (J PUnit.unit).2 := (mem_pull (L := LB.div M L) (J := J)).1 hy
    ⟨mem_pull.2 h.1, mem_pull.2 h.2⟩
  { idx := fun J => (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
    le := le
    g := fun y J J' hJ hJ' => gm_div_pull L M f y J J' (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2) rfl rfl hJ hJ' (le J y hJ) (le J' y hJ') }

def chartDivPull (L M : LB X) (f : Y ⟶ X) :
    ChartPull (LB.div (M.pull f) (L.pull f)) ((LB.div M L).pull f) (𝟙 Y) :=
  have le : ∀ (p : (PUnit → M.ι) × (PUnit → L.ι)) (y : Y), y ∈ (M.pull f).U p.1 ⊓ (L.pull f).U p.2 →
      y ∈ ((LB.div M L).pull f).U (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit)) := fun p y hy =>
    (mem_pull (L := LB.div M L) (J := fun _ => (p.1 PUnit.unit, p.2 PUnit.unit))).2
      ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
  { idx := fun p _ => (p.1 PUnit.unit, p.2 PUnit.unit)
    le := le
    g := fun y p q hp hq => (gm_div_pull L M f y (fun _ => (p.1 PUnit.unit, p.2 PUnit.unit))
      (fun _ => (q.1 PUnit.unit, q.2 PUnit.unit)) p q rfl rfl (le p y hp) (le q y hq) hp hq).symm }

theorem lbIso_pull_iff_gen (L M : LB X) (f : Y ⟶ X) :
    LBIso (L.pull f) (M.pull f) ↔ ∃ t : LB.Gen ((LB.div M L).pull f), t.IsGen :=
  ⟨exists_gen_chartPull (chartPullDiv L M f), exists_gen_chartPull (chartDivPull L M f)⟩

theorem exists_gen_of_chart {D : LB X} (hD : D.IsLB) (f : Y ⟶ X) (i : D.ι) (hf : ∀ y, f y ∈ D.U i) :
    ∃ t : LB.Gen (D.pull f), t.IsGen := by
  have le : ∀ J : PUnit → D.ι, (D.pull f).U J ≤ f ⁻¹ᵁ (D.U (J PUnit.unit) ⊓ D.U i) :=
    fun J y hy => ⟨mem_pull.1 hy, hf y⟩
  refine ⟨⟨fun J => res (le J) (pullU f _ (D.g (J PUnit.unit) i))⟩, fun J J' => unit_ext fun y hy => ?_⟩
  have val : ∀ J, y ∈ (D.pull f).U J → gm (𝟙 Y) y _ (res (le J) (pullU f _ (D.g (J PUnit.unit) i))) =
      gm (𝟙 Y ≫ f) y _ (D.g (J PUnit.unit) i) := fun J hJ =>
    (gm_res (𝟙 Y) y (le J) hJ _).trans (gm_pull (𝟙 Y) f y _ (le J hJ) _)
  refine ((gm_res (𝟙 Y) y _ hy _).trans (val J hy.1)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull_g D f (𝟙 Y) y J J' hy.1 hy.2)
    ((gm_res (𝟙 Y) y _ hy _).trans (val J' hy.2)))).trans ?_
  exact gm_cocycle hD (𝟙 Y ≫ f) y (mem_pull.1 hy.1) (mem_pull.1 hy.2) (hf y)

theorem exists_gen_of_diff {D : LB X} (hD : D.IsLB) (σ : X ⟶ X)
    (c : LB.Gen (LB.LinComb D ![𝟙 X, σ] ![1, -1])) (hc : c.IsGen) (r : Y ⟶ X) {B : Scheme.{0}} (q : Y ⟶ B)
    (τ : B ⟶ X) (hr : r ≫ σ = q ≫ τ) (H : ∃ t : LB.Gen (D.pull τ), t.IsGen) :
    ∃ t : LB.Gen (D.pull r), t.IsGen := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨u, hu, -⟩ := exists_gen hD (φ' := fun _ : PUnit => r) (ε' := fun _ => 1) (by
      intro U _ h
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, hr])
    (LB.mulGen D _ _ _ _ (LB.pullGen D _ _ c r) (LB.pullGen D _ _ t q))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ c hc r) (DVR.pullGen_isGen _ _ _ t ht q))
  exact ⟨u, hu⟩

theorem exists_gen_diff (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H)
    (pU : HU ⟶ U) (hp : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (sq : IsPullback jH pU p j)
    {D : LB H} (hD : D.IsLB) (H₀ : ∃ t : LB.Gen (D.pull jH), t.IsGen) :
    ∃ c : LB.Gen (LB.LinComb D ![𝟙 H, p ≫ e] ![1, -1]), c.IsGen := by
  obtain ⟨t, ht⟩ := H₀
  let eU : U ⟶ HU := sq.lift (j ≫ e) (𝟙 U) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : eU ≫ jH = j ≫ e := sq.lift_fst _ _ _
  have h₂ : eU ≫ pU = 𝟙 U := sq.lift_snd _ _ _
  have h₃ : jH ≫ p ≫ e = (pU ≫ eU) ≫ jH := by rw [Category.assoc, h₁, sq.w_assoc]
  obtain ⟨t', ht', vt⟩ := exists_gen hD (φ' := fun i => jH ≫ ![𝟙 H, p ≫ e] i) (ε' := ![1, -1]) (by
      intro U _ h
      simp [Fintype.prod_sum_type, Fin.prod_univ_two, h₃])
    (LB.mulGen D _ _ _ _ t (LB.invGen D _ _ (LB.pullGen D _ _ t (pU ≫ eU))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ t ht _)))
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen hD (φ' := fun i => e ≫ ![𝟙 H, p ≫ e] i) (ε' := ![1, -1]) (by
      intro U _ h
      simp [Fin.prod_univ_two, reassoc_of% he])
    (LB.oneGen D) (LB.isGen_oneGen D)
  obtain ⟨c, ⟨hc, -⟩, -⟩ := GlobalTheory.GenExtendNormal.existsUnique_gen_extend S hS U H HU H j p e jH pU eU hp hg he sq h₁ D hD (Fin 2) _ _ t' ρ ht' hρ
    (corr_of_val hD fun y J hJ => by
      rw [val_pull hJ, val_pull hJ, vt _ _ _ _ hJ, vρ _ _ _ _ hJ, val_mul hJ, val_inv, val_pull hJ, val_one,
        Category.id_comp, reassoc_of% h₂, mul_inv_cancel])
  exact ⟨c, hc⟩

end GlobalTheory.IsoExtend

open GlobalTheory.IsoExtend in

theorem GlobalTheory.lbIso_extend_of_normal : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → ∀ (L M : LB H), L.IsLB → M.IsLB → LBIso (L.pull jH) (M.pull jH) → (LBIso (L.pull e) (M.pull e) → LBIso L M) ∧ ∀ s : S, ∃ N : S.Opens, s ∈ N ∧ LBIso (L.pull (p ⁻¹ᵁ N).ι) (M.pull (p ⁻¹ᵁ N).ι) := by
  intro S _ _ hS U H HU _ j _ p e jH pU hp hg he sq L M hL hM h
  have hD : (LB.div M L).IsLB := LB.isLB_div hM hL
  obtain ⟨c, hc⟩ := exists_gen_diff S hS U H HU j p e jH pU hp hg he sq hD ((lbIso_pull_iff_gen L M jH).1 h)
  refine ⟨fun h' => ?_, fun s => ?_⟩
  · exact exists_gen_chartPull (chartPullUnpull (LB.div M L) (𝟙 H) rfl)
      (exists_gen_of_diff hD _ c hc (𝟙 H) p e (Category.id_comp _) ((lbIso_pull_iff_gen L M e).1 h'))
  · obtain ⟨i, hi⟩ := exists_chart hD (e s)
    refine ⟨e ⁻¹ᵁ (LB.div M L).U i, hi, (lbIso_pull_iff_gen L M _).2 ?_⟩
    exact exists_gen_of_diff hD _ c hc _ (𝟙 _) _ (Category.id_comp _).symm
      (exists_gen_of_chart hD _ i fun y => y.2)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormRepGeneratorsAndThetaSeriesTerm
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}

theorem norm_cubN (h : N.Int q) (k : ℕ) (a b x : N.A) : ‖((cubN N.θ k a b x : Cˣ) : C)‖ = 1 := by
  rw [cubN, Units.coe_prod, norm_prod]
  exact Finset.prod_eq_one fun i _ => h.θ _ _ _

theorem norm_dbl (h : N.Int q) (x : N.A) : ‖((dbl N.θ N.σ x : Cˣ) : C)‖ = 1 := by
  rw [dbl, Units.val_div_eq_div_val, norm_div, h.θ, h.σ, div_one]

theorem norm_mulq (h : N.Int q) (n : ℕ) (x : N.A) : ‖((mulq N.θ N.σ n x : Cˣ) : C)‖ = 1 := by
  rw [mulq, Units.coe_prod, norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [Units.val_div_eq_div_val, norm_div, h.norm_cubN, Units.val_pow_eq_pow_val, norm_pow, h.norm_dbl,
    one_pow, div_one]

theorem norm_τ (h : N.Int q) (a b : N.X) : ‖(N.τ a b : C)‖ = Real.exp (-QuadraticMap.polar q a b) := by
  rw [NumD.τ, Units.val_div_eq_div_val, Units.val_div_eq_div_val, norm_div, norm_div, h.ψ, h.ψ, h.ψ,
    ← Real.exp_sub, ← Real.exp_sub, QuadraticMap.polar]
  congr 1
  ring

theorem norm_pow_generators_eq_pow (h : N.Int q) (g : N.Gt) (k : ℕ) (χ : N.X) :
    ‖((g ^ k).s χ : C)‖ = ‖(g.s χ : C)‖ ^ k := by
  have := congrArg (fun u : Cˣ => ‖(u : C)‖) (g.pow_s k χ)
  simpa only [Units.val_mul, norm_mul, h.norm_cubN, mul_one, Units.val_pow_eq_pow_val, norm_pow] using this

theorem norm_rep_generators_eq_exp (h : N.Int q) {k : ℕ} (p : N.QT k) (hk : k ≠ 0) (χ : N.X) :
    ‖(p.1.2.s χ : C)‖ = Real.exp (-(QuadraticMap.polar q p.1.1.toAdd χ / k)) := by
  have e := h.norm_pow_generators_eq_pow p.1.2 k χ
  rw [N.mem_QT.1 p.2, NumD.io_s, h.norm_τ] at e
  refine (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le hk).1 ?_
  rw [← e, ← Real.exp_nat_mul]
  congr 1
  have : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk
  field_simp

theorem norm_wQ (h : N.Int q) {k : ℕ} (hk : Odd k) (p : N.QT k) :
    ‖(N.wQ p : C)‖ = Real.exp (-(q p.1.1.toAdd / k)) := by
  have hk0 : k ≠ 0 := hk.pos.ne'
  rw [NumD.wQ, NumB.wS]
  simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_pow_eq_pow_val, norm_div, norm_mul, norm_pow,
    h.norm_cubN, h.norm_dbl, h.norm_mulq, h.ψ, h.norm_rep_generators_eq_exp p hk0, mul_one, one_pow, div_one]
  rw [← Real.exp_nat_mul, ← Real.exp_sub, QuadraticMap.polar_self]
  congr 1
  obtain ⟨j, rfl⟩ := hk
  have e : (2 * j + 1 - 1) / 2 = j := by omega
  have : ((2 * j + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk0
  rw [e, two_smul]
  field_simp
  push_cast
  ring

theorem norm_txT (h : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    ‖N.txT m p χ‖ = Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) * ‖N.th (N.c χ * p.1.2.b ^ m)‖ := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  rw [NumD.txT, NumD.vt]
  simp only [Units.val_div_eq_div_val, Units.val_mul, norm_div, norm_mul, h.norm_mulq, h.ψ,
    h.norm_wQ hm.pow, h.norm_pow_generators_eq_pow, h.norm_rep_generators_eq_exp p (pow_ne_zero 2 hm0), div_one, NumD.Gt.pow_b]
  rw [← mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  congr 2
  have e : q (p.1.1.toAdd + m • χ) =
      q p.1.1.toAdd + (m : ℝ) ^ 2 * q χ + m * QuadraticMap.polar q p.1.1.toAdd χ := by
    have a : QuadraticMap.polar q p.1.1.toAdd (m • χ) = m * QuadraticMap.polar q p.1.1.toAdd χ := by
      rw [← natCast_zsmul, QuadraticMap.polar_smul_right, zsmul_eq_mul, Int.cast_natCast]
    have b : q (m • χ) = (m : ℝ) ^ 2 * q χ := by
      rw [← natCast_zsmul, QuadraticMap.map_smul, zsmul_eq_mul]
      push_cast
      ring
    rw [← a, ← b, QuadraticMap.polar]
    ring
  have : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm0
  rw [e]
  push_cast
  field_simp
  ring

end GlobalTheory.Ex.NumD.Int

namespace GlobalTheory.Ex

theorem norm_QT_s_and_norm_txT : ∀ (C : Type) [NormedField C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → (∀ (k : ℕ) (p : N.QT k), k ≠ 0 → ∀ χ, ‖(p.1.2.s χ : C)‖ = Real.exp (-(QuadraticMap.polar q p.1.1.toAdd χ / k))) ∧ ∀ (m : ℕ), Odd m → ∀ (p : N.QT (m ^ 2)) χ, ‖N.txT m p χ‖ = Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) * ‖N.th (N.c χ * p.1.2.b ^ m)‖ :=
  fun _ _ _ _ h => ⟨fun _ p hk χ => h.norm_rep_generators_eq_exp p hk χ, fun _ hm p χ => h.norm_txT hm p χ⟩
end GlobalTheory.Ex
end

