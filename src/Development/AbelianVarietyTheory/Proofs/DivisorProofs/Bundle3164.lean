import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3103
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSymplecticLevelFamilyUniversalProper
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2979
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramConnectionPairChernFieldsLocalFrame
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem loc_fields_near : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r] [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ (x : A.Pt) (k : ℕ), ∀ᶠ v in 𝓝 x.crd, A.loc (fld A (powFld A G k)) x.1.1 v = powAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (fld A (chernFld A G k)) x.1.1 v = chernAt (fun u => G x.pt (x.ch.symm u)) v k ∧ A.loc (transFld A G G' k) x.1.1 v = transAt (fun u => G x.pt (x.ch.symm u)) (fun u => G' x.pt (x.ch.symm u)) v k := by
  intro M _ n A r _ _ G G' hG x k
  obtain ⟨⟨i, y⟩, hy⟩ := x
  have hyt : A.e i y ∈ (A.e i).target := (A.e i).map_source hy
  have hsymm : (A.e i).symm (A.e i y) = y := (A.e i).left_inv hy
  have hcont : Tendsto (A.e i).symm (𝓝 (A.e i y)) (𝓝 y) := by
    have := (A.e i).continuousAt_symm hyt
    rwa [ContinuousAt, hsymm] at this
  obtain ⟨⟨hGu, hGs⟩, ⟨hG'u, hG's⟩⟩ := hG.smooth y
  have e1 := hGs i hy
  have e2 := hG's i hy
  have u1 := e1.self_of_nhds.eventually_isUnit (by simpa only [hsymm] using hGu)
  have u2 := e2.self_of_nhds.eventually_isUnit (by simpa only [hsymm] using hG'u)
  filter_upwards [(A.e i).open_target.mem_nhds hyt, hcont.eventually (hG.trans y), e1, e2, u1, u2]
    with v hv htr h1 h2 h3 h4
  obtain ⟨T, K, K', hT, hK, hK', hw⟩ := htr
  have hz : (A.e i).symm v ∈ (A.e i).source := (A.e i).map_target hv
  have hzv : A.e i ((A.e i).symm v) = v := (A.e i).right_inv hv
  have hct : Tendsto (A.e i).symm (𝓝 v) (𝓝 ((A.e i).symm v)) := (A.e i).continuousAt_symm hv
  have dT := hT.2 i hz
  have dK := hK.2 i hz
  have dK' := hK'.2 i hz
  rw [hzv] at dT dK dK'
  have key := GlobalTheory.T.chernTransgression_forms_frame_invariant n r (fun u => G y ((A.e i).symm u)) (fun u => G' y ((A.e i).symm u))
    (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (fun u => G' ((A.e i).symm v) ((A.e i).symm u))
    (fun u => T ((A.e i).symm u)) (fun u => K ((A.e i).symm u)) (fun u => K' ((A.e i).symm u)) v
    h1 h3 h2 h4 dT hT.1 dK hK.1 dK' hK'.1 (hct.eventually hw) k
  refine ⟨?_, ?_, ?_⟩
  · rw [HolAtlas.loc, dif_pos hv]
    show ((powAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (A.e i ((A.e i).symm v)) k : Ev n) : Alt n) = _
    rw [hzv, key.1]
  · rw [HolAtlas.loc, dif_pos hv]
    show ((chernAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (A.e i ((A.e i).symm v)) k : Ev n) : Alt n) = _
    rw [hzv, key.2.1]
  · rw [HolAtlas.loc, dif_pos hv]
    show transAt (fun u => G ((A.e i).symm v) ((A.e i).symm u)) (fun u => G' ((A.e i).symm v) ((A.e i).symm u))
      (A.e i ((A.e i).symm v)) k = _
    rw [hzv, key.2.2]

end GlobalTheory.ChernCalc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSum
section
set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

set_option autoImplicit false in
open Filter Topology MeasureTheory in
open scoped ComplexOrder Matrix in
private lemma ofReal_norm_sum_mul_sq_eq_double_sum_conj {ι : Type} [Fintype ι] (c w : ι → ℂ) :
    ((‖∑ i, c i * w i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * (w i * (starRingEnd ℂ) (w j)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

set_option autoImplicit false in
open Filter Topology MeasureTheory in
open scoped ComplexOrder Matrix in

theorem _root_.GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form (S : Type) (Y : S → Type)
    [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι]
    [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ)
    (h : _root_.GlobalTheory.HSAmp.IsFam μ v) :
    (_root_.GlobalTheory.HSAmp.gram μ v).IsHermitian ∧ ∀ c : ι → ℂ,
      (∀ σ, Integrable (_root_.GlobalTheory.HSAmp.cmb v c σ) (μ σ)) ∧
      0 ≤ _root_.GlobalTheory.HSAmp.l2 μ v c ∧
      (_root_.GlobalTheory.HSAmp.l2 μ v c : ℂ) =
        ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * _root_.GlobalTheory.HSAmp.gram μ v i j := by
  haveI : Fintype S := @Fintype.ofFinite S h.finite
  have hint := h.integrable
  have hterm : ∀ (c : ι → ℂ) (σ : S), Integrable (fun y => ∑ i, ∑ j,
      c i * (starRingEnd ℂ) (c j) * (v σ y i * (starRingEnd ℂ) (v σ y j))) (μ σ) :=
    fun c σ => integrable_finset_sum _ fun i _ =>
      integrable_finset_sum _ fun j _ => (hint σ i j).const_mul _
  refine ⟨?_, fun c => ⟨fun σ => ?_, ?_, ?_⟩⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, _root_.GlobalTheory.HSAmp.gram, Matrix.of_apply,
      finsum_eq_sum_of_fintype]
    rw [star_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Complex.star_def, ← integral_conj]
    congr 1 with y
    simp [mul_comm]
  · refine (hterm c σ).re.congr (ae_of_all _ fun y => ?_)
    simp only [_root_.GlobalTheory.HSAmp.cmb]
    rw [← ofReal_norm_sum_mul_sq_eq_double_sum_conj c (v σ y)]
    exact Complex.ofReal_re _
  · unfold _root_.GlobalTheory.HSAmp.l2
    exact finsum_nonneg fun σ => integral_nonneg fun y => by
      simp only [_root_.GlobalTheory.HSAmp.cmb]
      positivity
  · unfold _root_.GlobalTheory.HSAmp.l2 _root_.GlobalTheory.HSAmp.gram
    simp only [Matrix.of_apply, finsum_eq_sum_of_fintype]
    have key : ∀ σ, ((∫ y, _root_.GlobalTheory.HSAmp.cmb v c σ y ∂μ σ : ℝ) : ℂ) =
        ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ := by
      intro σ
      simp only [_root_.GlobalTheory.HSAmp.cmb]
      rw [← integral_complex_ofReal,
        integral_congr_ae (ae_of_all _ fun y => ofReal_norm_sum_mul_sq_eq_double_sum_conj c (v σ y)),
        integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
          (hint σ i j).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ fun j _ => (hint σ i j).const_mul _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    rw [Complex.ofReal_sum]
    simp only [key, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueOfBaseEqStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o : Obj b N s) (o' : Obj b N s') (f f' : S' ⟶ S) (m₁ : ObjMap o' o f) (m₂ : ObjMap o' o f'), f = f' → m₁.φ = m₂.φ := by
  first | exact @GlobalTheory.UPel.HT.Rigid.objMap_phi_unique | exact GlobalTheory.UPel.HT.Rigid.objMap_phi_unique | (intros; apply GlobalTheory.UPel.HT.Rigid.objMap_phi_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o' : Obj b N s') (o : Obj b N s) (f : S' ⟶ S) (m m' : ObjMap o' o f), m.φ = m'.φ := by
  first | exact @GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique | exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique | (intros; apply GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.HTQuotRigid

theorem objMap_comp_φ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁} {o₂ : Obj b N s₂}
    {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem eq_one_of_fixes_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N h M : ℕ), 3 ≤ N → N.Coprime p → 0 < M →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp R) (s₁ : X ⟶ Sp (cycAway M)) (u : Obj b N s)
      (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over X) ⟶ u.A)),
      IsSympLev u.P h M (zetaAway M) s₁ lev → ∀ ρ : sympSimGrp h M → (X ⟶ X), SympActs s s₁ u lev ρ →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ X) (a : sympSimGrp h M), y ≫ ρ a = y → a = 1 := by
  intro p _ D R _ b N h M hN hNp hM X s s₁ u lev hlev ρ hρ k _ _ y a hya
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨-, -, m, hm⟩ := hρ a
  obtain ⟨o, ⟨n⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N X (Sp k) s y u
  obtain ⟨c, hc⟩ := objMap_comp_φ n m
  have key : ∀ (f : Sp k ⟶ X), f = y → ∀ mm : ObjMap o u f, mm.φ = n.φ := by
    intro f hf mm
    subst hf
    exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique p D R b N hN hNp _ _ _ _ _ _ _ mm n
  have hφ : n.φ ≫ m.φ = n.φ := by rw [← hc]; exact key _ hya c

  have hx : ∀ x, y ≫ (sympTwist a lev x).left = y ≫ (lev x).left := by
    intro x
    have ht : (y ≫ (sympTwist a lev x).left) ≫ u.A.hom = 𝟙 (Sp k) ≫ y := by
      rw [Category.assoc, Over.w]
      rfl
    have hσ := n.cart.1.lift_fst (y ≫ (sympTwist a lev x).left) (𝟙 _) ht
    have e1 : (y ≫ (sympTwist a lev x).left) ≫ m.φ = y ≫ (lev x).left := by
      rw [Category.assoc, hm x, ← Category.assoc, hya]
    rw [← e1, ← hσ, Category.assoc, hφ]

  let β : cycAway M →+* k := (Spec.preimage (y ≫ s₁)).hom
  have hβ : y ≫ s₁ = spMap β := by
    change y ≫ s₁ = Spec.map (CommRingCat.ofHom (Spec.preimage (y ≫ s₁)).hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hpow : β (zetaAway M) ^ M = 1 := by rw [← map_pow, zetaAway_pow_self hM.ne', map_one]
  let z : kˣ := Units.ofPowEqOne _ M hpow hM.ne'
  have hcl := (hlev.2.2 k y β z hβ rfl).1
  have hunit : ∀ x, (toUnit (Over.mk y) ≫ lev x).left = y ≫ (lev x).left := by
    intro x
    rw [Over.comp_left]
    congr 1
  have hfix : ∀ x, (a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x) =
      reduceMod M x := by
    intro x
    set c := liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M x))
    have hsame : toUnit (Over.mk y) ≫ lev c = toUnit (Over.mk y) ≫ lev x := by
      ext1
      rw [hunit, hunit]
      exact hx x
    have hsplit : lev c = lev (c - x) * lev x := by rw [← hlev.1, sub_add_cancel]
    have h1 : toUnit (Over.mk y) ≫ lev (c - x) = 1 := by
      rw [hsplit, comp_mul] at hsame
      exact mul_eq_right.1 hsame
    obtain ⟨d, hd⟩ := (hcl (c - x)).1 h1
    have hr : reduceMod M c = reduceMod M x := by
      have : c = x + M • d := by rw [← hd]; abel
      rw [this]
      funext i
      simp [reduceMod]
    exact (reduceMod_liftMod _).symm.trans hr
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have := hfix (liftMod v)
  rw [reduceMod_liftMod] at this
  exact this

end GlobalTheory.HTQuotRigid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSiegelChartOfPolarisedMonomialPeriodChart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PolDeg

theorem hasChart_of_hasPolChart {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o)
    (j : F.X ⟶ S) [IsOpenImmersion j] {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ)
    (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S) (hn : n ≠ 0) (h : HasPolChart F s j e φ BD d x) :
    HasChart F s j e φ BD d x := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, ⟨hc, hz, hs, hx, he, hu⟩, ⟨ht, hI, hj⟩,
    ⟨hM, hX, hδ, hdef, hmon⟩, ha, hBD⟩ := h
  have hCN : IsCN R := ⟨inferInstance, (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2, hc, hz⟩
  have ht0 : ∀ i, t i ≠ 0 := by
    intro i h0
    have := ht.2 (Pi.single i 1) (by
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
      simp [h0]) i
    simp at this
  have hsym : ∀ i y z, ((n : ℤ) • δ i) y z = ((n : ℤ) • δ i) z y := fun i y z => by
    simp only [LinearMap.smul_apply, (mem_balForms_int.1 (hδ.mem i)) y z]
  have hnn : ∀ i y, 0 ≤ ((n : ℤ) • δ i) y y := fun i y => by
    simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_nonneg (by positivity) (hδ.nonneg i y)
  have hpos : ∀ y, y ≠ 0 → ∃ i, 0 < ((n : ℤ) • δ i) y y := fun y hy => by
    obtain ⟨i, hi⟩ := hdef y hy
    exact ⟨i, by simp only [LinearMap.smul_apply, smul_eq_mul]; exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) hi⟩
  obtain ⟨R', _, _, _, ρ, r, D, ε, hCN', hinj, hfin, hloc, hr, href, hmon'⟩ :=
    GlobalTheory.T.refine_polarised_monomial_periods_monomial_data R Q m t (fun i => (n : ℤ) • δ i) hCN hmon ht.1 ht0 hsym hnn hpos
  obtain ⟨G', _, _, π, A, U, hU⟩ := hM.unif R' ρ hCN' hinj hfin D ε href
  let ϑ : Fin m → LinearMap.BilinForm ℤ D.toPre.X := fun i => pull ε.toIntLinearEquiv.toLinearMap (δ i)
  have hϑ : ∀ (k : ℤ) i, pull ε.toIntLinearEquiv.toLinearMap (k • δ i) = k • ϑ i := fun k i =>
    LinearMap.ext₂ fun y z => by simp [ϑ]
  refine ⟨R, inferInstance, inferInstance, b, ξ, m, t, R', inferInstance, inferInstance, inferInstance, ρ, r, G', inferInstance,
    inferInstance, π, D, A, U, ϑ, a, ⟨hc, hs, hx, he, hu⟩, ⟨ht, hI, hj⟩,
    ⟨⟨hCN'.1, inferInstance, hCN'.2.1, hCN'.2.2.1⟩, hCN'.2.2.2, hinj, hfin, hloc, hr⟩,
    ⟨hU, ?_, hδ.pull_equiv ε.toIntLinearEquiv, ?_⟩, fun i => ?_, hBD⟩
  · rw [LinearEquiv.finrank_eq ε.toIntLinearEquiv]; exact hX
  · convert hmon' using 2 with i
    rw [hϑ, ← mul_smul]
  · rw [ha i, ← hϑ, evalZ_pull φ ε.toIntLinearEquiv.surjective]

end GlobalTheory.PolDeg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormDelDbarSmooth
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_eventuallyEq_pull {α : A.Fld} (hα : A.IsForm α) (x x' : A.Pt) (h : x.pt = x'.pt) :
    A.loc α x.1.1 =ᶠ[𝓝 x.crd] fun y => pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y)) := by
  have hU : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hxU : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩
  refine Filter.eventually_of_mem (hU.mem_nhds hxU) fun y hy => ?_
  show A.loc α x.1.1 y = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) y) (A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y))
  let p : A.Pt := ⟨(x.1.1, x.ch.symm y), x.ch.map_target hy.1⟩
  let p' : A.Pt := ⟨(x'.1.1, x.ch.symm y), hy.2⟩
  have e1 : A.loc α x.1.1 y = α p := by rw [HolAtlas.loc, dif_pos hy.1]
  have e2 : A.loc α x'.1.1 ((x'.ch ∘ x.ch.symm) y) = α p' := A.loc_crd α p'
  have e3 : p.crd = y := x.ch.right_inv hy.1
  rw [e1, e2, hα.compat p p' rfl]
  show pull (fderiv ℂ (x'.ch ∘ x.ch.symm) p.crd) (α p') = _
  rw [e3]

theorem chg_facts (x x' : A.Pt) (h : x.pt = x'.pt) :
    IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧ x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source ∧
    DifferentiableOn ℂ (x'.ch ∘ x.ch.symm) (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) ∧
    (x'.ch ∘ x.ch.symm) x.crd = x'.crd :=
  ⟨x.ch.isOpen_inter_preimage_symm x'.ch.open_source,
    ⟨x.ch.map_source x.2, by simp only [Set.mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩,
    A.holo x.1.1 x'.1.1, by simp only [Function.comp_apply, x.ch.left_inv x.2, h]⟩

theorem loc_diffAt {α : A.Fld} (hα : A.IsForm α) (x : A.Pt) (S : Finset (Fin (n + n))) :
    DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x.1.1 y) S) x.crd :=
  ((hα.smooth x.1.1 S).contDiffAt (x.ch.open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)

theorem isForm_del_dbar {α : A.Fld} (hα : A.IsForm α) : A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) := by
  have hloc : ∀ (T : (V n → Alt n) → V n → Alt n) (i : A.ι) (v : V n), v ∈ (A.e i).target →
      A.loc (fun x => T (A.loc α x.1.1) x.crd) i v = T (A.loc α i) v := by
    intro T i v hv
    rw [HolAtlas.loc, dif_pos hv]
    show T (A.loc α i) ((A.e i) ((A.e i).symm v)) = _
    rw [(A.e i).right_inv hv]
  refine ⟨⟨fun i S => ?_, fun x x' h => ?_⟩, ⟨fun i S => ?_, fun x x' h => ?_⟩⟩
  · exact ((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).1).congr fun v hv => by
      rw [show A.del α = fun x => delAt (A.loc α x.1.1) x.crd from rfl, hloc delAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show delAt (A.loc α x.1.1) x.crd = pull _ (delAt (A.loc α x'.1.1) x'.crd)
    rw [((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).1,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).1, hτx]
  · exact ((GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator n _ (A.loc α i) (A.e i).open_target (hα.smooth i) S).2).congr fun v hv => by
      rw [show A.dbar α = fun x => dbarAt (A.loc α x.1.1) x.crd from rfl, hloc dbarAt i v hv]
  · obtain ⟨hU, hxU, hτ, hτx⟩ := chg_facts A x x' h
    have hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (A.loc α x'.1.1 y) S) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hτx]; exact loc_diffAt A hα x'
    show dbarAt (A.loc α x.1.1) x.crd = pull _ (dbarAt (A.loc α x'.1.1) x'.crd)
    rw [((GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local n x.crd).2.2.2.1 _ _ (loc_eventuallyEq_pull A hα x x' h)).2,
      (GlobalTheory.T.del_dbar_chainRule_holomorphicPullback n n _ _ _ x.crd hU hxU hτ hβ).2, hτx]

end GlobalTheory.CxForm.HolAtlas

theorem GlobalTheory.CxForm.isForm_del_dbar : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α : A.Fld), A.IsForm α →
    A.IsForm (A.del α) ∧ A.IsForm (A.dbar α) :=
  fun _ _ _ A _ hα => A.isForm_del_dbar hα
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphic
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.PullbackForm

variable {M M' : Type} [TopologicalSpace M] [TopologicalSpace M'] {n n' : ℕ} {A : HolAtlas M n} {A' : HolAtlas M' n'}

theorem isOpen_dom {f : M' → M} (hf : Continuous f) (j : A'.ι) (i : A.ι) :
    IsOpen ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source)) :=
  (A'.e j).isOpen_inter_preimage_symm ((A.e i).open_source.preimage hf)

theorem smooth_pullback {f : M' → M} {α : A.Fld} (hf : A.IsHolo A' f) (hα : A.IsForm α) (j : A'.ι)
    (S : Finset (Fin (n' + n'))) :
    ContDiffOn ℝ ∞ (fun v => (bas n').repr (A'.loc (A.pullback A' f α) j v) S) (A'.e j).target := by
  refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
  obtain ⟨i, hi⟩ := A.cover (f ((A'.e j).symm v))
  have hU := isOpen_dom (A := A) (A' := A') hf.1 j i
  refine ⟨_, hU, ⟨hv, hi⟩, ?_⟩
  rw [Set.inter_eq_self_of_subset_right Set.inter_subset_left]
  have hτ := hf.2 j i
  have hτ' : ContDiffOn ℝ ∞ (A.e i ∘ f ∘ (A'.e j).symm)
      ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source)) :=
    (((GlobalTheory.SCV.analyticOnNhd_iff_differentiableOn hU).2 hτ).contDiffOn hU.uniqueDiffOn).restrict_scalars ℝ
  have key : ContDiffOn ℝ ∞ (fun w => ∑ T, (bas n).repr (A.loc α i ((A.e i ∘ f ∘ (A'.e j).symm) w)) T *
      (bas n').repr (pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) w) (bas n T)) S)
      ((A'.e j).target ∩ (A'.e j).symm ⁻¹' (f ⁻¹' (A.e i).source)) :=
    ContDiffOn.sum fun T _ => ((hα.smooth i T).comp hτ' fun w hw => (A.e i).map_source hw.2).mul
      (GlobalTheory.T.contDiffOn_repr_pullbackComplexForm_fderiv _ _ _ _ (bas n T) hU hτ S)
  refine key.congr fun w hw => ?_
  have h₁ : A'.loc (A.pullback A' f α) j w = pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) w)
      (A.loc α i ((A.e i ∘ f ∘ (A'.e j).symm) w)) := by
    rw [HolAtlas.loc, dif_pos hw.1]
    refine (GlobalTheory.T.holAtlas_pullback_eq_chart_expression M M' n n' A A' f α hf hα ⟨(j, (A'.e j).symm w), (A'.e j).map_target hw.1⟩ i hw.2).trans ?_
    refine (congrArg _ (A.loc_crd α ⟨(i, f ((A'.e j).symm w)), hw.2⟩).symm).trans ?_
    show pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) (A'.e j ((A'.e j).symm w))) _ = _
    rw [(A'.e j).right_inv hw.1]
    rfl
  rw [h₁]
  conv_lhs => rw [← (bas n).sum_repr (A.loc α i ((A.e i ∘ f ∘ (A'.e j).symm) w))]
  simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem compat_pullback {f : M' → M} {α : A.Fld} (hf : A.IsHolo A' f) (hα : A.IsForm α) (x x' : A'.Pt)
    (h : x.pt = x'.pt) :
    A.pullback A' f α x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (A.pullback A' f α x') := by
  obtain ⟨⟨j, y⟩, hy⟩ := x
  obtain ⟨⟨j', y'⟩, hy'⟩ := x'
  obtain rfl : y = y' := h
  obtain ⟨i, hi⟩ := A.cover (f y)
  refine (GlobalTheory.T.holAtlas_pullback_eq_chart_expression M M' n n' A A' f α hf hα ⟨(j, y), hy⟩ i hi).trans (Eq.trans ?_
    (congrArg _ (GlobalTheory.T.holAtlas_pullback_eq_chart_expression M M' n n' A A' f α hf hα ⟨(j', y), hy'⟩ i hi).symm))
  rw [← GlobalTheory.T.pullbackComplexFormsLinearMap_comp]
  show pull (fderiv ℂ (A.e i ∘ f ∘ (A'.e j).symm) (A'.e j y)) _ =
    pull ((fderiv ℂ (A.e i ∘ f ∘ (A'.e j').symm) (A'.e j' y)).comp
      (fderiv ℂ (A'.e j' ∘ (A'.e j).symm) (A'.e j y))) _
  have e : (A'.e j).symm (A'.e j y) = y := (A'.e j).left_inv hy
  have e' : (A'.e j').symm (A'.e j' y) = y := (A'.e j').left_inv hy'
  have hW : (A'.e j).target ∩ (A'.e j).symm ⁻¹' (A'.e j').source ∈ 𝓝 (A'.e j y) :=
    ((A'.e j).isOpen_inter_preimage_symm (A'.e j').open_source).mem_nhds
      ⟨(A'.e j).map_source hy, by simpa only [Set.mem_preimage, e] using hy'⟩
  have d₁ : DifferentiableAt ℂ (A'.e j' ∘ (A'.e j).symm) (A'.e j y) := (A'.holo j j').differentiableAt hW
  have e₂ : (A'.e j' ∘ (A'.e j).symm) (A'.e j y) = A'.e j' y := congrArg _ e
  have d₂ : DifferentiableAt ℂ (A.e i ∘ f ∘ (A'.e j').symm) ((A'.e j' ∘ (A'.e j).symm) (A'.e j y)) := by
    rw [e₂]
    exact (hf.2 j' i).differentiableAt ((isOpen_dom hf.1 j' i).mem_nhds
      ⟨(A'.e j').map_source hy', by simpa only [Set.mem_preimage, e'] using hi⟩)
  have hc := fderiv_comp _ d₂ d₁
  rw [e₂] at hc
  rw [← hc]
  congr 2
  refine Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem hW fun w hw => ?_)
  simp only [Function.comp_apply, (A'.e j').left_inv hw.2]

theorem isForm_pullback : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n)
    (A' : HolAtlas M' n') (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A'.IsForm (A.pullback A' f α) :=
  fun _ _ _ _ _ _ _ _ _ _ hf hα => ⟨smooth_pullback hf hα, compat_pullback hf hα⟩

end GlobalTheory.PullbackForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapLiftsLocallyToPeriodFamiliesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type) (F : Fam ℂ O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ F.X)) (b₀ : Fin m → ℂ) P₀ e₀, 0 < N → (∀ a, F.eta a ^ N = 1) → LocallyOfFiniteType F.s → IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ F.s = spMap (RingHom.id ℂ)) → IsHolTo B y → UnifAt F (RingHom.id ℂ) ρ N D' t P₀ (y b₀) e₀ → ∃ (B' : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))) (e : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ F.A)), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ P b₀ = P₀ ∧ IsHolPeriods D' ρ B' P ∧ IsHolTo (B' ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (e bz.1 bz.2).left) ∧ ∀ b ∈ B', UnifAt F (RingHom.id ℂ) ρ N D' t (P b) (y b) (e b) := by
  first | exact @GlobalTheory.PELU.holomorphic_map_lifts_to_periods | exact GlobalTheory.PELU.holomorphic_map_lifts_to_periods | (intros; apply GlobalTheory.PELU.holomorphic_map_lifts_to_periods <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtClosedFibreOfRegularAtAllTraitsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_at_closedFibre_of_regular_at_all_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ (k : ℕ) (s : SecK L α k), TraitReg M G L s → ∀ x : G.left, M.π (G.hom x) = closedPoint R → IntAt L α s x := by
  first | exact @GlobalTheory.Mum.intAt_closed_of_traitReg | exact GlobalTheory.Mum.intAt_closed_of_traitReg | (intros; apply GlobalTheory.Mum.intAt_closed_of_traitReg <;> assumption)
end

