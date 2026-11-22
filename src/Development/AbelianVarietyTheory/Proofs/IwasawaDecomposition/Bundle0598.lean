import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Partition
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1319
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmoothHermitianMetricProjectiveVariety
section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false
noncomputable section
open Topology Filter
open scoped ContDiff Matrix ComplexOrder

namespace GlobalTheory.GoodMetric.SmoothMetric

theorem exists_partition {F : Type} [Field F] (σ : F →+* ℂ) (X : Var F)
    (W : CxPts X.str σ → Set (CxPts X.str σ)) (hWo : ∀ y, IsOpen (W y)) (hW : ∀ y, y ∈ W y) :
    ∃ (n : ℕ) (pt : Fin n → CxPts X.str σ) (χ : Fin n → CxPts X.str σ → ℝ),
      (∀ j y, 0 ≤ χ j y) ∧ (∀ y, ∑ j, χ j y = 1) ∧ (∀ j, tsupport (χ j) ⊆ W (pt j)) ∧
      ∀ j y, CInfAt (χ j) y := by
  classical
  haveI := CxPts.compactSpace σ X.isProjOver
  have hc : ∀ y, ∃ c : AlgChart X.str σ X.dim, y ∈ c.e.source ∧ c.e.source ⊆ W y := fun y => by
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
    exact ⟨c.restr (W y) (hWo y), ⟨hc, hW y⟩, Set.inter_subset_right⟩
  choose c hcy hcW using hc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (c y).e.source)
    (fun y => (c y).e.open_source) (fun y _ => Set.mem_iUnion.2 ⟨y, hcy y⟩)
  let pt : Fin t.card → CxPts X.str σ := fun j => (t.equivFin.symm j).1
  let Lc := EuclideanSpace.equiv (Fin X.dim) ℂ
  let L := Lc.toHomeomorph
  let e : Fin t.card → OpenPartialHomeomorph (CxPts X.str σ) (Fin X.dim → ℂ) :=
    fun j => (c (pt j)).e.transHomeomorph L
  have hcov : ∀ y, ∃ j, y ∈ (e j).source := by
    intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
    simpa [e, pt] using hy
  have htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source) := by
    intro i j
    have ho := isOpen_over (c (pt i)).e (c (pt j)).e.open_source
    have hg : ContDiffOn ℂ ∞ ((c (pt j)).e ∘ (c (pt i)).e.symm)
        ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source) :=
      contDiffOn_euclidean.2 fun a => ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ ho
        (differentiableOn_euclidean.1 ((c (pt i)).holo_trans (c (pt j))) a)
    have h2 := (Lc.contDiff.restrict_scalars ℝ).comp_contDiffOn
      ((hg.restrict_scalars ℝ).comp (Lc.symm.contDiff.restrict_scalars ℝ).contDiffOn
        (s := Lc.symm ⁻¹' ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source)) ?_)
    · refine h2.congr_mono ?_ ?_
      · intro v hv
        simp [e, L, Lc]
      · intro v hv
        simpa [e, L, Lc] using hv
    · intro v hv
      simpa using hv
  obtain ⟨χ, h0, h1, hs, hd⟩ := ReciprocityTheory.AnForm.exists_chart_partition e hcov htr
  refine ⟨t.card, pt, χ, h0, h1, fun j => (hs j).trans (hcW (pt j)), fun j y => ?_⟩
  obtain ⟨i, hi⟩ := hcov y
  have hi' : y ∈ (c (pt i)).e.source := hi
  refine cInfAt_of_chart (c (pt i)).e.open_source (c (pt i)) ?_ hi' hi'
  have h3 := (hd j i).comp (Lc.contDiff.restrict_scalars ℝ).contDiffOn
    (s := (c (pt i)).e.target) (fun v hv => by simpa [e, L, Lc] using hv)
  refine h3.congr_mono ?_ Set.inter_subset_left
  intro v hv
  simp [e, L, Lc]

end GlobalTheory.GoodMetric.SmoothMetric

namespace GlobalTheory.GoodMetric.SmoothMetric

theorem cInfAt_sum {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {κ : Type}
    (s : Finset κ) (f : κ → CxPts X.str σ → ℝ) {y : CxPts X.str σ} (h : ∀ j ∈ s, CInfAt (f j) y) :
    CInfAt (fun z => ∑ j ∈ s, f j z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := X.str) 0 y
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem exists_isMetricOn_top : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m 0), ∃ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H := by
  intro F _ σ X ι _ m E
  classical
  choose U A hz hA hU using fun y : CxPts X.str σ => E.loc (under y)
  obtain ⟨n, pt, χ, h0, h1, hs, hd⟩ := exists_partition σ X (fun y => ptsIn X.str σ (U y))
    (fun y => isOpen_ptsIn _) (fun y => mem_ptsIn.2 (hz y))
  let T : Fin n → Mat m X.Fn → CxPts X.str σ → Mat m ℂ := fun j B z => (B * (A (pt j))⁻¹).map (ratVal · z)

  have hpar : ∀ j y, y ∈ tsupport (χ j) → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy B hB =>
    (hU (pt j) (under y) (mem_ptsIn.1 (hs j hy)) B).1 hB
  have hpar' : ∀ j y, χ j y ≠ 0 → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy =>
    hpar j y (subset_tsupport _ hy)
  refine ⟨fun B z τ => ∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ), ⟨?_, ?_, ?_⟩⟩
  · intro y _ B hB τ
    obtain ⟨j, hj⟩ : ∃ j, χ j y ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      have := h1 y
      simp [hne] at this
    have hpos : 0 < χ j y := lt_of_le_of_ne (h0 j y) (Ne.symm hj)
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hdet := ((hpar' j y hj B hB).map_of (ratVal · y) ψ hψ).det_ne τ
    have hPD : (((χ j y : ℝ) : ℂ) • (T j B y τ * (T j B y τ)ᴴ)).PosDef :=
      Matrix.PosDef.smul (Matrix.PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit))) (by exact_mod_cast hpos)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    refine hPD.add_posSemidef (Matrix.posSemidef_sum _ fun i _ => ?_)
    exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (Complex.zero_le_real.2 (h0 i y))
  · intro y _ B hB τ i k
    have key : ∀ g : ℂ →L[ℝ] ℝ, CInfAt (fun z =>
        g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) y := by
      intro g
      have e : (fun z => g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) =
          fun z => ∑ j ∈ Finset.univ, χ j z * g ((T j B z τ * (T j B z τ)ᴴ) i k) := by
        funext z
        rw [Matrix.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul, ← Complex.real_smul, map_smul, smul_eq_mul]
      rw [e]
      refine cInfAt_sum _ _ fun j _ => ?_
      by_cases hy : y ∈ tsupport (χ j)
      · have hr (x : Fin (m τ) × Fin (m τ)) : RegAt (under y) ((B * (A (pt j))⁻¹) τ x.1 x.2) :=
          mem_O_ratOf.1 ((hpar j y hy B hB τ).1 _ _)
        have hG : ContDiff ℝ (⊤ : ℕ∞) fun w : Fin (m τ) × Fin (m τ) → ℂ => ∑ l, w (i, l) * star (w (k, l)) :=
          ContDiff.sum fun l _ => (contDiff_apply ℝ ℂ _).mul (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ _))
        refine ((hd j y).comp₂ (cInfAt_ratVal hr (g.contDiff.comp hG))
          (contDiff_fst.mul contDiff_snd)).congr (Eventually.of_forall fun z => ?_)
        simp [T, Matrix.mul_apply, Mat.map]
      · have hz : χ j =ᶠ[𝓝 y] fun _ => 0 := by
          rw [tsupport, ← Set.mem_compl_iff] at hy
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz'
          exact Function.notMem_support.1 fun h => hz' (subset_closure h)
        refine (cInfAt_const (p := X.str) 0 y).congr ?_
        filter_upwards [hz] with z hz'
        simp [hz']
    exact ⟨key Complex.reCLM, key Complex.imCLM⟩
  · intro y _ B hB B' hB' τ
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hBB : Par 0 ((ratOf X).O (under y)).toSubring (B' * B⁻¹) := (Fr.mem_iff hB).1 hB'
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : χ j y = 0
    · simp [hj]
    have e := Par.map_mul_of hBB (hpar' j y hj B hB) (ratVal · y) ψ hψ
    rw [mul_assoc, ← mul_assoc B⁻¹, Mat.inv_mul (Fr.det_ne hB), one_mul] at e
    simp only [T]
    rw [e, Pi.mul_apply, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end GlobalTheory.GoodMetric.SmoothMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)
open GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.VB GlobalTheory.LieVB.TangentSurj
open GlobalTheory.LB (resG_self)
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.TanFibre

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {π : Y ⟶ X} {e : X ⟶ Y} (he : e ≫ π = 𝟙 X)
  {x : Sp k ⟶ X} {v v' : (specO k (DualNumber k)).left ⟶ Y}

def form (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e) :
    (Scheme.Modules.pullback x).obj (conormal e) ⟶ structureModule (Sp k) :=
  baseMap (sec_hom (epsZero k)) w we ≫ (epsIso k).hom

theorem form_d (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    {V : X.Opens} {W : Y.Opens} (h : V ≤ e ⁻¹ᵁ W) (f : Γ(Y, W)) {U : (Sp k).Opens} (hU : U ≤ x ⁻¹ᵁ V)
    (q : (specO k (DualNumber k)).hom ⁻¹ᵁ U ≤ v ⁻¹ᵁ W) (a b : Γ(Sp k, U))
    (H : v.appLE W _ q f = (specO k (DualNumber k)).hom.appLE U _ le_rfl a +
      (specO k (DualNumber k)).hom.appLE U _ le_rfl b * resG _ le_top (epsFn k)) :
    (form w we).app U (pullbackSections x _ hU (d he h f)) = b := by
  have hV : U ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  refine (congrArg ((epsIso k).hom.app U) (baseMap_d he (sec_hom (epsZero k)) w we h hU hV q f)).trans ?_
  rw [H, map_add, d_base, zero_add, d_mul, d_base,
    smul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl, resG_self, d_resG,
    ← resM_d _ (le_preimage_top _ ⊤) le_top, Scheme.Modules.Hom.app_smul, app_resM, epsIso_d]
  exact (congrArg (b * ·) (map_one (resG (Sp k) (le_top : U ≤ ⊤)))).trans (_root_.mul_one b)

theorem preimage_le (we : sec (epsZero k) ≫ v = x ≫ e) {U : (Sp k).Opens} {W : Y.Opens}
    (h : U ≤ x ⁻¹ᵁ e ⁻¹ᵁ W) : (specO k (DualNumber k)).hom ⁻¹ᵁ U ≤ v ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero t
  have h₁ : s ∈ (sec (epsZero k) ≫ (specO k (DualNumber k)).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ : s ∈ (x ≫ e) ⁻¹ᵁ W := h h₁
  rw [← we] at h₂
  exact h₂

theorem appLE_eq (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    {U : (Sp k).Opens} (hU : IsAffineOpen U) {W : Y.Opens} (h : U ≤ x ⁻¹ᵁ e ⁻¹ᵁ W) (f : Γ(Y, W)) :
    v.appLE W _ (preimage_le we h) f =
      (specO k (DualNumber k)).hom.appLE U _ le_rfl ((x ≫ e).appLE W U h f) +
        (specO k (DualNumber k)).hom.appLE U _ le_rfl
          ((form w we).app U (pullbackSections x _ h (d he le_rfl f))) * resG _ le_top (epsFn k) := by
  obtain ⟨⟨a, b⟩, E⟩ := (bijective_add_mul_epsFn k U hU).2 (v.appLE W _ (preimage_le we h) f)
  have hV : U ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  have hb := form_d he w we le_rfl f h (preimage_le we h) a b E.symm
  have ha : (x ≫ e).appLE W U h f = a := by
    have e' := congrArg ((sec (epsZero k)).appLE _ U hV) E
    simp only [map_add, map_mul] at e'
    rw [appLE_sec_epsZero_epsFn, mul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl,
      resG_self, appLE_appLE we _ _ h] at e'
    exact e'.symm
  rw [ha, hb]
  exact E.symm

include he in

theorem eq_of_form_eq (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    (w' : v' ≫ π = (specO k (DualNumber k)).hom ≫ x) (we' : sec (epsZero k) ≫ v' = x ≫ e)
    (H : form w we = form w' we') : v = v' := by
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨W, hW, hW', -⟩ := QCoh.exists_affine_mem_le (U := ⊤)
    (e (x ((specO k (DualNumber k)).hom t))) trivial
  obtain ⟨U, hU, hU', h⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ e ⁻¹ᵁ W)
    ((specO k (DualNumber k)).hom t) hW'
  have hT : IsAffineOpen ((specO k (DualNumber k)).hom ⁻¹ᵁ U) := hU.preimage _
  have E : v.appLE W _ (preimage_le we h) = v'.appLE W _ (preimage_le we' h) := by
    ext f
    exact (appLE_eq he w we hU h f).trans (H ▸ (appLE_eq he w' we' hU h f).symm)
  refine ⟨(specO k (DualNumber k)).hom ⁻¹ᵁ U, hU', ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← hW.SpecMap_appLE_fromSpec _ hT (preimage_le we h),
    ← hW.SpecMap_appLE_fromSpec _ hT (preimage_le we' h), E]

include he in

theorem exists_form_eq [QuasiSeparated π]
    (L : (Scheme.Modules.pullback x).obj (conormal e) ⟶ structureModule (Sp k)) :
    ∃ (v : (specO k (DualNumber k)).left ⟶ Y) (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x)
      (we : sec (epsZero k) ≫ v = x ≫ e), form w we = L := by
  let e' : Sp k ⟶ pullback π x := pullback.lift (x ≫ e) (𝟙 _) (by simp [he])
  have he' : e' ≫ pullback.snd π x = 𝟙 _ := pullback.lift_snd _ _ _
  have we' : e' ≫ pullback.fst π x = x ≫ e := pullback.lift_fst _ _ _
  have : QuasiCompact e :=
    have : QuasiCompact (e ≫ π) := he ▸ inferInstance
    .of_comp _ π
  have : QuasiCompact e' :=
    have : QuasiCompact (e' ≫ pullback.snd π x) := he' ▸ inferInstance
    .of_comp _ (pullback.snd π x)
  have := isIso_baseMap he he' (IsPullback.of_hasPullback π x) we'
  let β := baseMap he' (IsPullback.of_hasPullback π x).w we'
  let D := homEquivDer _ he' (inv β ≫ L)
  let u := deform (specO k (DualNumber k)).hom (epsFn k) (epsFn_sq k) D
  have w : (u ≫ pullback.fst π x) ≫ π = (specO k (DualNumber k)).hom ≫ x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, deform_comp _ _ _ D he']
  have we : sec (epsZero k) ≫ u ≫ pullback.fst π x = x ≫ e := by
    rw [← Category.assoc, comp_deform _ _ (epsFn_sq k) D (sec_hom (epsZero k)) (epsZero_epsFn k), we']
  refine ⟨_, w, we, pullback_hom_ext he fun W f => ?_⟩
  have k₁ : x ⁻¹ᵁ e ⁻¹ᵁ W ≤ e' ⁻¹ᵁ pullback.fst π x ⁻¹ᵁ W := le_of_sq we' le_rfl le_rfl
  have k₂ := (specO k (DualNumber k)).hom.preimage_mono k₁
  let g := (pullback.fst π x).appLE W _ le_rfl f
  refine (form_d he w we le_rfl f le_rfl (preimage_le we le_rfl) (e'.appLE _ _ k₁ g) (val D k₁ g) ?_).trans ?_
  · have k₃ : (specO k (DualNumber k)).hom ⁻¹ᵁ x ⁻¹ᵁ e ⁻¹ᵁ W ≤ u ⁻¹ᵁ pullback.fst π x ⁻¹ᵁ W := k₂
    have e₁ : u.appLE _ _ k₃ g = resG _ k₂ (psi _ _ (epsFn_sq k) D _ g) :=
      deform_appLE _ _ (epsFn_sq k) D _ k₂ g
    rw [← appLE_appLE (f := u) (g := pullback.fst π x) rfl le_rfl k₃, e₁, psi_apply, map_add, map_mul, LB.resG_resG, DualPull.resG_appLE, DualPull.resG_appLE,
      ← DualPull.resG_appLE e' k₁ le_rfl, DualPull.appLE_resG,
      show val D k₁ g = resG _ k₁ (val D le_rfl g) from (D.res_app le_rfl k₁ g).symm, DualPull.appLE_resG]
  · have b := baseMap_d he he' (IsPullback.of_hasPullback π x).w we' le_rfl le_rfl k₁ le_rfl f
    have c : val D k₁ g = (inv β ≫ L).app _ (d he' k₁ g) := homEquivDer_app he' (inv β ≫ L) k₁ g
    rw [c, ← b]
    generalize pullbackSections x (conormal e) _ (d he _ f) = s
    have i : β ≫ inv β ≫ L = L := IsIso.hom_inv_id_assoc β L
    conv_rhs => rw [← i]
    rw [Scheme.Modules.Hom.comp_app β, AddCommGrpCat.comp_apply]

theorem exists_hom_of_isFrame {F : X.Modules} {n : ℕ} {s : Fin n → Γ(F, ⊤)} (hs : IsFrame s) (c : Fin n → Γ(X, ⊤)) :
    ∃ L : F ⟶ structureModule X, ∀ l, L.app ⊤ (s l) = c l := by
  refine ⟨homGlobalEquiv _ _ (∑ i, c i • hs.coord i), fun l => ?_⟩
  change dualApp (∑ i, c i • hs.coord i) le_rfl (s l) = c l
  have hsum (T : Finset (Fin n)) : dualApp (∑ i ∈ T, c i • hs.coord i) le_rfl (s l) = if l ∈ T then c l else 0 := by
    induction T using Finset.induction_on with
    | empty =>
      have := dualApp_smul (0 : Γ(X, ⊤)) (hs.coord l) le_rfl
      rw [zero_smul, map_zero, zero_smul] at this
      rw [Finset.sum_empty, this]
      simp
    | insert i T hi ih =>
      have := hs.dualApp_coord_frame i l le_rfl
      rw [Twist.resM_self] at this
      rw [Finset.sum_insert hi, dualApp_add, LinearMap.add_apply, ih, dualApp_smul, LinearMap.smul_apply, this,
        resG_self]
      by_cases hl : l = i
      · subst hl
        simp [hi]
      · simp [hl]
  simpa using hsum Finset.univ

theorem existsUnique_tanEv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (n : ℕ) (m : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)), GlobalTheory.VB.IsFrame m → ∀ c : Fin n → k, ∃! v : Sp (DualNumber k) ⟶ t.G.left, ∃ hv : IsTanAtG t x v, ∀ l, tanEv t hv h (m l) = c l := by
  intro E _ _ _ H X t k _ x V h n m hm c
  have := t.semi
  have hf : IsFrame fun l => pullbackSections x (omega t.G) h (m l) := by
    have := (hm.pullback x).res h
    exact (funext fun l => QCoh.res_pullbackSections x (omega t.G) le_rfl h (m l)) ▸ this
  obtain ⟨L, hL⟩ := exists_hom_of_isFrame hf fun l => cst k (c l)
  obtain ⟨v, w, we, hv⟩ := exists_form_eq (sec_hom η[t.G]) L
  have hv' : IsTanAtG t x v := ⟨w, we.trans (by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rfl)⟩
  have hval (l) : tanEv t hv' h (m l) = c l :=
    (congrArg (fun (a : Γ(Sp k, ⊤)) => (Scheme.ΓSpecIso (.of k)).hom a)
      ((congr(($hv).app ⊤ _)).trans (hL l))).trans (Iso.inv_hom_id_apply _ _)
  refine ⟨v, ⟨hv', hval⟩, ?_⟩
  rintro u ⟨hu, hu'⟩
  refine eq_of_form_eq (sec_hom η[t.G]) hu.1 (epsZero_comp_of_isTanAtG t hu) w we (hom_ext_of_isFrame hf fun l => ?_)
  exact (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective ((hu' l).trans (hval l).symm)

end GlobalTheory.TanFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitSectionOfLocalValues
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FieldPtGlue

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X}

theorem valF_ne_zero_iff {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF x U a ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dif_pos h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  rw [e3]
  constructor
  · intro hne
    exact (Scheme.basicOpen_of_isUnit _ ((Ne.isUnit hne).map _)).ge
  · intro hle h0
    rw [h0, map_zero, Scheme.basicOpen_zero] at hle
    exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

theorem valF_restrict {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem valF_sub {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valF x U (a - b) = valF x U a - valF x U b := by
  simp only [valF, dif_pos h, map_sub]

theorem le_preimage_iff (U : X.Opens) : ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint F) ∈ U := by
  constructor
  · intro h
    exact h (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)
  · intro h y _
    have : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
    subst this
    exact h

end Val

noncomputable def resPt (X : Scheme.{0}) (z : X) : Sp (X.residueField z : Type) ⟶ X := X.fromSpecResidueField z

theorem resPt_le_iff (X : Scheme.{0}) (z : X) (U : X.Opens) : ⊤ ≤ resPt X z ⁻¹ᵁ U ↔ z ∈ U := by
  rw [le_preimage_iff]
  have : resPt X z (IsLocalRing.closedPoint (X.residueField z : Type)) = z :=
    Scheme.fromSpecResidueField_apply z _
  rw [this]

theorem section_ext {X : Scheme.{0}} [IsReduced X] {U : X.Opens} (a b : Γ(X, U))
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → valF w U a = valF w U b) : a = b := by
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro z hz
  have hU : ⊤ ≤ resPt X z ⁻¹ᵁ U := (resPt_le_iff X z U).2 (X.basicOpen_le _ hz)
  have h1 := (valF_ne_zero_iff hU (a - b)).2 ((resPt_le_iff X z _).2 hz)
  rw [valF_sub hU, h _ _ hU, sub_self] at h1
  exact absurd rfl h1

theorem exists_unit_of_locally : ∀ (X : Scheme.{0}) [IsReduced X] (U : X.Opens) (P : ∀ (k : Type) [Field k], (Sp k ⟶ X) → k → Prop), (∀ (k : Type) [Field k] (w : Sp k ⟶ X) (a a' : k), ⊤ ≤ w ⁻¹ᵁ U → P k w a → P k w a' → a = a') → (∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → ¬ P k w 0) → (∀ z ∈ U, ∃ (V : X.Opens) (s : Γ(X, V)), z ∈ V ∧ V ≤ U ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ V → P k w (valF w V s)) → ∃ s : Γ(X, U)ˣ, ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → P k w (valF w U s.val) := by
  intro X _ U P huniq hne hloc
  choose V s hzV hVU hP using hloc
  let V' : U → X.Opens := fun z => V z.1 z.2
  let s' : ∀ z : U, Γ(X, V' z) := fun z => s z.1 z.2
  have hcov : U ≤ iSup V' := fun z hz =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzV z hz⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf V' s' := by
    intro i j
    refine section_ext (X := X) (U := V' i ⊓ V' j) _ _ fun k _ w hw => ?_
    have hi : ⊤ ≤ w ⁻¹ᵁ V' i := fun q hq => (hw hq).1
    have hj : ⊤ ≤ w ⁻¹ᵁ V' j := fun q hq => (hw hq).2
    refine (valF_restrict inf_le_left hw (s' i)).trans
      (Eq.trans ?_ (valF_restrict inf_le_right hw (s' j)).symm)
    exact huniq k w _ _ (fun q hq => hVU i.1 i.2 (hi hq)) (hP i.1 i.2 k w hi) (hP j.1 j.2 k w hj)
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' V' U (fun i => homOfLE (hVU i.1 i.2)) hcov s' hcomp
  have key : ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → P k w (valF w U t) := by
    intro k _ w hw
    have hz := (le_preimage_iff U).1 hw
    have hV : ⊤ ≤ w ⁻¹ᵁ V _ hz := (le_preimage_iff _).2 (hzV _ hz)
    have e : valF w U t = valF w (V _ hz) (s _ hz) :=
      (valF_restrict (hVU _ hz) hV t).symm.trans (congrArg (valF w (V _ hz)) (ht ⟨_, hz⟩))
    rw [e]
    exact hP _ hz k w hV
  have hu : IsUnit (M := Γ(X, U)) t := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    have hU : ⊤ ≤ resPt X z ⁻¹ᵁ U := (resPt_le_iff X z U).2 hz
    have h0 : valF (resPt X z) U t ≠ 0 := fun h0 => hne _ _ hU (h0 ▸ key _ _ hU)
    have h1 := (resPt_le_iff X z _).1 ((valF_ne_zero_iff hU t).1 h0)
    exact (X.mem_basicOpen t z hz).1 h1
  exact ⟨hu.unit, key⟩

end GlobalTheory.FieldPtGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDROfFullIntStep
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)

namespace GlobalTheory.DRFlag

theorem initSpan_self {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {m : ℕ} (v : Fin m → N) :
    initSpan R v m = Submodule.span R (Set.range v) := by
  rw [initSpan, ← Set.image_univ]
  congr 2
  exact Set.eq_univ_of_forall fun j => j.2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V : ValuationSubring c.F}
  {M : Model Xo c V.subtype} {X : Scheme.{0}} {π : X ⟶ M.X} {ty : (E →+* ℂ) → Finset ℕ}

theorem flagAt_of_intOn (A : Atlas M π ty) (hty : ∀ σ, ∀ j ∈ ty σ, j ≤ Dw.mult σ)
    {U : (E →+* ℂ) → X.Opens} {hU : ∀ σ, IsAffineOpen (U σ)} {m : (E →+* ℂ) → ℕ}
    (b : ∀ σ, Module.Basis (Fin (Dw.mult σ) ⊕ Fin (m σ)) Γ(X, U σ) (TanM (tau (hU σ) ≫ π) M.t.G))
    (hb : ∀ σ, IntOn A σ (Dw.mult σ) (hU σ) (b σ)) {K : Type} [Field K] (w : Sp K ⟶ X)
    (hw : ∀ σ, ⊤ ≤ w ⁻¹ᵁ U σ) (hc : Set.range w ⊆ A.ch.carrier) :
    A.FlagAt w (up (Dw := Dw) fun σ i => basAt (b σ) w (hw σ) (.inl i)) := by
  obtain ⟨a, φ, e⟩ := A.ch.exists_fac w (hc ⟨_, rfl⟩)
  obtain ⟨u₀, h₀⟩ := A.exists_up_fr e
  have f₀ := A.isFrame_bc e
  have g₀ := A.flagAt_fr e
  rw [← h₀] at f₀ g₀
  refine (A.flagAt_iff e h₀ _).2 ⟨(isFrame_up_iff _ _).2 fun σ => ⟨?_, ?_⟩,
    fun σ j hj => (hb σ K w (hw σ) u₀ g₀ j (hty σ j hj)).symm⟩
  · exact (basAt (b σ) w (hw σ)).linearIndependent.comp _ Sum.inl_injective
  · rw [← initSpan_self, ← hb σ K w (hw σ) u₀ g₀ _ le_rfl, initSpan_self]
    exact ((isFrame_up_iff _ _).1 f₀ σ).2

theorem hasDR_of_intStep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : Mdl Y i₀), (∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) → (∀ σ, IntStep (atlasOf Z) σ (Dw.mult σ)) → HasDR Z := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z hty hs
  refine ⟨hty, fun x => ?_⟩
  choose U hU m b hx hb using fun σ => hs σ x
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hx₀, hle⟩ := Z.X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ ⋂ σ, (U σ : Set Z.X) from Set.mem_iInter.2 hx) (isOpen_iInter_of_finite fun σ => (U σ).isOpen)
  have hle' : ∀ σ, U₀ ≤ U σ := fun σ q hq => Set.mem_iInter.1 (hle hq) σ
  let b' := fun σ => basAt (b σ) (tau hU₀) (tau_le hU₀ (hle' σ))
  refine ⟨U₀, hU₀, up (Dw := Dw) fun σ i => b' σ (.inl i), hx₀, fun σ => ?_, fun k _ φ hr => ?_⟩
  · let b'' := (b' σ).reindex finSumFinEquiv
    refine ⟨_, fun i => (tv (b'' i)).left, Fin.castAddEmb _, fun i => ?_, fun i => isTan_tv _, fun u hu => ?_⟩
    · simp only [b'', Module.Basis.reindex_apply, Fin.castAddEmb_apply, finSumFinEquiv_symm_apply_castAdd]
      rfl
    · exact (existsUnique_congr fun a => isComb_iff b'' a (tanOf hu)).2
        ⟨b''.repr (tanOf hu), (b''.sum_repr _).symm, fun a ha => by rw [ha]; exact (b''.repr_sum_self a).symm⟩
  · have hw : ∀ σ, ⊤ ≤ (spMap φ ≫ tau hU₀) ⁻¹ᵁ U σ := fun σ => le_preimage_comp _ (tau_le hU₀ (hle' σ))
    have key := flagAt_of_intOn (atlasOf Z) (fun σ j hj => by rw [hty, Finset.mem_range] at hj; omega)
      b hb (spMap φ ≫ tau hU₀) hw (by rw [(atlasOf Z).cover]; exact hr)
    rw [← up_tanPull φ (Category.assoc _ _ _).symm]
    simp only [b', tanPull_basAt _ φ _ _ rfl (hw _)]
    exact key

end GlobalTheory.DRFlag
end
end

