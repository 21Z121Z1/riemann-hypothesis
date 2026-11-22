import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0987
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0003
import ReciprocityTheory.SemistableReduction.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstCoeffOperatorLinearSubstitutionProofStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constCoeffOperatorLinearSubstitution_proof : LinSt := by
  first | exact @GlobalTheory.IsoTriv.linSt_holds | exact GlobalTheory.IsoTriv.linSt_holds | (intros; apply GlobalTheory.IsoTriv.linSt_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermCenterActionSmoothFormStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_center_action_smooth_form : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → μ 𝓕 = 1 → ∀ φ : Sm E a, (∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g) → IsOpen {k | finRep E a k φ = φ} → ∀ z ∈ Zalg E a, ∀ c : Sm E a, c.1 = (fun g : GA E a => ∫ x in 𝓕, φ.1 (unip x * g) ∂μ) → (z c).1 = fun g : GA E a => ∫ x in 𝓕, (z φ).1 (unip x * g) ∂μ := by
  first | exact @GlobalTheory.ConstTermZalg.constTerm_zalg | exact GlobalTheory.ConstTermZalg.constTerm_zalg | (intros; apply GlobalTheory.ConstTermZalg.constTerm_zalg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtLevi
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open ReciprocityTheory.L2DbarEstimates (V leviV)
open GlobalTheory GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CxPts

namespace GlobalTheory.SemiPosBir

variable {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Z ⟶ Sp k} {σ : k →+* ℂ}
  {D : ℕ}

open ReciprocityTheory.L2DbarEstimates in

theorem continuousAt_levi {g : V D → ℂ} {x : V D} (hg : ContDiffAt ℝ 2 g x) (ξ : Fin D → ℂ) :
    ContinuousAt (fun v => leviV D g v ξ) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) x := hg.fderiv_right (by norm_num)
  have h2 : ∀ l, ContDiffAt ℝ 1 (wdb D l g) x := fun l =>
    ((h1.clm_apply contDiffAt_const).add
      (contDiffAt_const.mul (h1.clm_apply contDiffAt_const))).div_const 2
  have h3 : ∀ j l, ContinuousAt (wd D j (wdb D l g)) x := fun j l => by
    have h4 : ContinuousAt (fderiv ℝ (wdb D l g)) x :=
      ((h2 l).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((h4.clm_apply continuousAt_const).sub
      (continuousAt_const.mul (h4.clm_apply continuousAt_const))).div_const 2
  unfold leviV
  exact tendsto_finset_sum _ fun j _ => tendsto_finset_sum _ fun l _ =>
    ((h3 j l).mul continuousAt_const).mul continuousAt_const

theorem ae_mem [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ) (c : AlgChart p σ D)
    {U : X.Opens} (hU : (U : Set X).Nonempty) :
    ∀ᵐ v : V D, v ∈ c.e.target → c.e.symm v ∈ ptsIn p σ U := by
  rcases c.e.source.eq_empty_or_nonempty with h | ⟨y, hy⟩
  · exact .of_forall fun v hv => absurd (c.e.map_target hv) (h ▸ notMem_empty _)
  have hy' := mem_ptsIn.1 (c.source_subset hy)
  obtain ⟨x, hx, hx'⟩ := nonempty_preirreducible_inter U.isOpen c.U.isOpen hU ⟨_, hy'⟩
  obtain ⟨a, ha, ha'⟩ := c.affine.exists_basicOpen_le (V := U) ⟨x, hx⟩ hx'
  have h0 : a ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at ha'
    exact ha'
  have : Nonempty c.U := ⟨⟨_, hy'⟩⟩
  let φ := MvPolynomial.eval₂Hom (algX p c.U) c.x
  let : Algebra (MvPolynomial (Fin D) k) Γ(X, c.U) := φ.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin D) k) Γ(X, c.U) := c.etale
  have h₁ := isAlgebraic_of_flat_of_formallyUnramified (MvPolynomial (Fin D) k) Γ(X, c.U)
  obtain ⟨r, hr, b, hb⟩ := (h₁.isAlgebraic a).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero h0)
  have hr' : MvPolynomial.map σ r ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective σ hσ)).2 hr
  filter_upwards [ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear (volume : Measure (V D))
    (WithLp.linearEquiv 2 ℂ (Fin D → ℂ)) _ hr'] with v hv hvt
  have hs := c.e.map_target hvt
  have hz := c.source_subset hs
  refine ptsIn_mono ha ((mem_ptsIn_basicOpen hz a).2 fun e => hv ?_)
  have e₁ : (evHom hz).comp φ = (MvPolynomial.eval (WithLp.linearEquiv 2 ℂ (Fin D → ℂ) v)).comp
      (MvPolynomial.map σ) := by
    refine MvPolynomial.ringHom_ext (fun t => ?_) fun i => ?_
    · simp only [φ, RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C,
        MvPolynomial.eval_C, ← ev_eq, ev_algX hz]
    · simp only [φ, RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X,
        MvPolynomial.eval_X, ← ev_eq, ← c.apply_eq _ hs, c.e.right_inv hvt]
      rfl
  have e₂ : φ r = a * b := hb
  refine (RingHom.congr_fun e₁ r).symm.trans ?_
  rw [RingHom.comp_apply, e₂, ← ev_eq, ev_mul, e, zero_mul]

variable (D) in

def PosOn (f : CxPts p σ → ℝ) (S : Set (CxPts p σ)) : Prop :=
  ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source ∩ S, ∀ ξ : Fin D → ℂ,
    0 ≤ (leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e y) ξ).re

theorem PosOn.of_inter [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ)
    {f : CxPts p σ → ℝ} {S : Set (CxPts p σ)} (hS : IsOpen S) (hf : ∀ y ∈ S, CInfAt f y)
    {U : X.Opens} (hU : (U : Set X).Nonempty) (h : PosOn D f (S ∩ ptsIn p σ U)) :
    PosOn D f S := fun c y hy ξ => by
  have ho := (isOpen_over c.e hS).mem_nhds (mem_over c.e hy.1 hy.2)
  have hd : ContDiffAt ℝ 2 (fun v => f (c.e.symm v)) (c.e y) :=
    ((contDiffOn_chart hf c).contDiffAt ho).of_le (by norm_cast)
  have hc := Complex.continuous_re.continuousAt.comp
    (continuousAt_levi (Complex.ofRealCLM.contDiff.contDiffAt.comp _ hd) ξ)
  have hfr := (mem_closure_iff_frequently.1 ((Measure.dense_of_ae (ae_mem hσ c hU)) (c.e y)))
  refine isClosed_Ici.mem_of_frequently_of_tendsto ((hfr.and_eventually ho).mono ?_) hc
  rintro v ⟨h₁, h₂, h₃⟩
  have := h c _ ⟨c.e.map_target h₂, h₃, h₁ h₂⟩ ξ
  rwa [c.e.right_inv h₂] at this

theorem levi_pull {j : Z ⟶ X} (hj : j ≫ p = q) (f : CxPts p σ → ℝ) (c : AlgChart p σ D)
    (c' : AlgChart q σ D) (e : c'.U ≤ j ⁻¹ᵁ c.U) (hx : ∀ a, c'.x a = (j.appLE _ _ e).hom (c.x a))
    {z : CxPts q σ} (hz : z ∈ c'.e.source) (hz' : PtsOver.map j hj _ z ∈ c.e.source)
    (ξ : Fin D → ℂ) :
    leviV D (fun v => (f (PtsOver.map j hj _ (c'.e.symm v)) : ℂ)) (c'.e z) ξ =
      leviV D (fun v => (f (c.e.symm v) : ℂ)) (c.e (PtsOver.map j hj _ z)) ξ := by
  have he (w) (hw : w ∈ c'.e.source) (hw' : PtsOver.map j hj (spMap σ) w ∈ c.e.source) :
      c'.e w = c.e (PtsOver.map j hj (spMap σ) w) := by
    ext a
    rw [c'.apply_eq w hw, c.apply_eq _ hw', hx]
    exact valR_appLE w.1 j e (c'.source_subset hw) _
  have hS : IsOpen (c'.e.source ∩ PtsOver.map j hj (spMap σ) ⁻¹' c.e.source) :=
    c'.e.open_source.inter (c.e.open_source.preimage (PtsOver.continuous_map j hj _))
  rw [← he z hz hz']
  refine ReciprocityTheory.L2DbarEstimates.leviV_congr ?_ ξ
  filter_upwards [(isOpen_over c'.e hS).mem_nhds (mem_over c'.e hz (S := _) ⟨hz, hz'⟩)] with v hv
  have e₁ : c.e.symm v = PtsOver.map j hj _ (c'.e.symm v) := by
    have := he _ hv.2.1 hv.2.2
    rw [c'.e.right_inv hv.1] at this
    exact (congrArg c.e.symm this).trans (c.e.left_inv hv.2.2)
  rw [e₁]

theorem appLE_comp_eval {j : Z ⟶ X} (hj : j ≫ p = q) {U : X.Opens} {W : Z.Opens}
    (e : W ≤ j ⁻¹ᵁ U) (x : Fin D → Γ(X, U)) :
    (j.appLE U W e).hom.comp (MvPolynomial.eval₂Hom (algX p U) x) =
      MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE U W e).hom (x a) := by
  subst hj
  refine MvPolynomial.ringHom_ext (fun t => ?_) fun i => ?_
  · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
    exact congrArg (fun g : Γ(Sp k, ⊤) ⟶ Γ(Z, W) => g.hom ((Scheme.ΓSpecIso (.of k)).inv.hom t))
      (Scheme.Hom.appLE_comp_appLE j p ⊤ U W le_top e)
  · rw [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']

theorem exists_map_eq (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ j.opensRange) : ∃ z : CxPts q σ, PtsOver.map j hj _ z = y := by
  have H : Set.range y.1 ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    exact hy (x := x) trivial
  refine ⟨⟨IsOpenImmersion.lift j y.1 H, ?_⟩, Subtype.ext (IsOpenImmersion.lift_fac _ _ _)⟩
  rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac]
  exact y.2

theorem PosOn.pull (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)} (h : PosOn D f S) :
    PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S) :=
  fun c' z hz ξ => by
  have e : c'.U ≤ j ⁻¹ᵁ j ''ᵁ c'.U := (j.preimage_image_eq _).ge
  have hi : IsIso (j.appLE _ _ e) := by
    rw [← Scheme.Hom.appIso_hom']
    infer_instance
  have hb := ConcreteCategory.bijective_of_isIso (j.appLE _ _ e)
  choose x hx using fun a => hb.2 (c'.x a)
  have h₁ := appLE_comp_eval hj e x
  have h₂ : (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x).Etale := by
    refine (RingHom.Etale.respectsIso.cancel_right_isIso (CommRingCat.ofHom
      (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x)) (j.appLE _ _ e)).1 ?_
    change ((j.appLE _ _ e).hom.comp (MvPolynomial.eval₂Hom (algX p (j ''ᵁ c'.U)) x)).Etale
    rw [h₁, show (fun a => (j.appLE _ _ e).hom (x a)) = c'.x from funext hx]
    exact c'.etale
  obtain ⟨c, hc, hU, hcx⟩ := AlgChart.exists_of_etale (y := PtsOver.map j hj (spMap σ) z)
    (c'.affine.image_of_isOpenImmersion j) x h₂
    (mem_ptsIn.2 ⟨_, mem_ptsIn.1 (c'.source_subset hz.1), rfl⟩)
  have key : ∀ (U : X.Opens) (hU : c.U = U) (e : c'.U ≤ j ⁻¹ᵁ U) (x : Fin D → Γ(X, U)),
      c.x = hU ▸ x → (∀ a, (j.appLE _ _ e).hom (x a) = c'.x a) →
      ∃ e : c'.U ≤ j ⁻¹ᵁ c.U, ∀ a, c'.x a = (j.appLE _ _ e).hom (c.x a) := by
    rintro _ rfl e x h₁ h₂
    exact ⟨e, fun a => by rw [h₁]; exact (h₂ a).symm⟩
  obtain ⟨e', hx'⟩ := key _ hU e x hcx hx
  rw [levi_pull hj f c c' e' hx' hz.1 hc]
  exact h c _ ⟨hc, hz.2⟩ ξ

theorem PosOn.of_pull (j : Z ⟶ X) [IsOpenImmersion j] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)}
    (h : PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S)) :
    PosOn D f (S ∩ ptsIn p σ j.opensRange) := fun c y hy ξ => by
  obtain ⟨z, rfl⟩ := exists_map_eq j hj hy.2.2
  obtain ⟨W, hW, hzW, e⟩ := exists_isAffineOpen_le z.1 (V := j ⁻¹ᵁ c.U) (c.source_subset hy.1)
  have h₂ : (MvPolynomial.eval₂Hom (algX q W) fun a => (j.appLE _ W e).hom (c.x a)).Etale := by
    rw [← appLE_comp_eval hj e]
    exact RingHom.Etale.stableUnderComposition _ _ c.etale
      (HasRingHomProperty.appLE @Etale j inferInstance ⟨c.U, c.affine⟩ ⟨W, hW⟩ e)
  obtain ⟨c', hc, rfl, hcx⟩ := AlgChart.exists_of_etale (y := z) hW _ h₂ hzW
  rw [← levi_pull hj f c c' e (congrFun hcx) hc hy.1]
  exact h c' _ ⟨hc, hy.2.1⟩ ξ

theorem posOn_iff_pull [IsDomain k] [IsIntegral X] (hσ : Function.Injective σ) (j : Z ⟶ X)
    [IsOpenImmersion j] [Nonempty Z] (hj : j ≫ p = q) {f : CxPts p σ → ℝ}
    {S : Set (CxPts p σ)} (hS : IsOpen S) (hf : ∀ y ∈ S, CInfAt f y) : PosOn D f S ↔
    PosOn D (fun w => f (PtsOver.map j hj _ w)) (PtsOver.map j hj (spMap σ) ⁻¹' S) :=
  ⟨fun h => h.pull j hj, fun h => (h.of_pull j hj).of_inter hσ hS hf (range_nonempty _)⟩

theorem semiPos_iff_pull : ∀ (k : Type) [CommRing k] (X X' : Scheme.{0}) (p : X ⟶ Sp k) (q : X' ⟶ Sp k) (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : X' ⟶ X) (hπ : π ≫ p = q) (U : X.Opens), (U : Set X).Nonempty → IsIso (π ∣_ U) → ∀ L : HermLB p, (L.SemiPos D ↔ (L.pull π hπ).SemiPos D) := by
  intro k _ X X' p q D hp hq π hπ U hU hi L
  have := hp.isDomain
  have := hp.finite
  have := hp.isIntegral
  have := hq.isIntegral
  refine forall_congr' fun σ => ?_
  have hσ : Function.Injective σ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have : Nonempty U.toScheme := hU.to_subtype
  have : Nonempty (π ⁻¹ᵁ U).toScheme := (π ∣_ U).surjective.nonempty
  have : IsOpenImmersion ((π ⁻¹ᵁ U).ι ≫ π) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have key (i : L.B.ι) : PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i)) ↔
      PosOn D (fun w => (L.φ σ).φ i (PtsOver.map π hπ _ w))
        (PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U i)) := by
    rw [posOn_iff_pull hσ ((π ⁻¹ᵁ U).ι ≫ π) rfl (isOpen_ptsIn _) (L.cInf σ i),
      posOn_iff_pull hσ (π ⁻¹ᵁ U).ι (q := ((π ⁻¹ᵁ U).ι ≫ π) ≫ p) (by rw [Category.assoc, hπ])
        ((isOpen_ptsIn _).preimage (PtsOver.continuous_map π hπ _))
        fun y hy => CInfAt.pull π hπ (L.cInf σ i _ hy)]
    have e (w : CxPts (((π ⁻¹ᵁ U).ι ≫ π) ≫ p) σ) : PtsOver.map ((π ⁻¹ᵁ U).ι ≫ π) rfl _ w =
        PtsOver.map π hπ _ (PtsOver.map (π ⁻¹ᵁ U).ι (by rw [Category.assoc, hπ]) _ w) :=
      Subtype.ext (Category.assoc _ _ _).symm
    rw [funext e]
    simp only [e]
    rfl
  have e₁ (J : (L.B.pull π).ι) : ptsIn q σ ((L.B.pull π).U J) =
      PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ (L.B.U (J PUnit.unit)) := Set.ext fun z => by
    rw [mem_preimage, mem_ptsIn, mem_ptsIn]
    exact ⟨fun h => mem_iInter.1 h PUnit.unit, fun h => mem_iInter.2 fun _ => h⟩
  have e₂ (J : (L.B.pull π).ι) : ((L.φ σ).pull π hπ).φ J =
      fun w => (L.φ σ).φ (J PUnit.unit) (PtsOver.map π hπ _ w) :=
    funext ((L.φ σ).pull_φ π hπ J)
  change (∀ i, PosOn D ((L.φ σ).φ i) (ptsIn p σ (L.B.U i))) ↔
    ∀ J, PosOn D (((L.φ σ).pull π hπ).φ J) (ptsIn q σ ((L.B.pull π).U J))
  simp only [e₁, e₂, key]
  exact ⟨fun h J => h _, fun h i => h fun _ => i⟩

end GlobalTheory.SemiPosBir
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCharpolyCoeffMulLeftFiniteAdelesAwayP
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CharpolyCont

theorem continuous_eval₂_of {X R : Type*} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {σ : Type*} (f : ℤ →+* R) (P : MvPolynomial σ ℤ) (x : X → σ → R)
    (hx : ∀ i, Continuous fun t => x t i) : Continuous fun t => MvPolynomial.eval₂ f (x t) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval₂_C]; exact continuous_const
  | add P Q hP hQ => simp only [MvPolynomial.eval₂_add]; exact hP.add hQ
  | mul_X P i hP => simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]; exact hP.mul (hx i)

theorem continuous_charpoly_coeff_mulLeft {R A : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] [TopologicalSpace A] [IsModuleTopology R A]
    (k : ℕ) : Continuous fun a : A => (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k := by
  let b := Module.Free.chooseBasis R A
  have e : ∀ a : A, (LinearMap.charpoly (LinearMap.mulLeft R a)).coeff k =
      MvPolynomial.eval₂Hom (Int.castRingHom R)
        (fun ij : Module.Free.ChooseBasisIndex R A × Module.Free.ChooseBasisIndex R A =>
          LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2)
        ((Matrix.charpoly.univ ℤ (Module.Free.ChooseBasisIndex R A)).coeff k) := by
    intro a
    rw [Matrix.charpoly.univ_coeff_eval₂Hom, ← LinearMap.charpoly_toMatrix _ b]
    rfl
  simp_rw [e]
  refine continuous_eval₂_of _ _ _ fun ij => ?_
  have h : ∀ a : A, LinearMap.toMatrix b b (LinearMap.mulLeft R a) ij.1 ij.2 =
      (b.coord ij.1).comp (LinearMap.mulRight R (b ij.2)) a := by
    intro a
    simp [LinearMap.toMatrix_apply]
  simp_rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

end GlobalTheory.CharpolyCont

open GlobalTheory.CharpolyCont in
theorem GlobalTheory.charpoly_coeff_continuous_GAf : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (k : ℕ), Continuous fun g : G.GAf =>
    (LinearMap.charpoly (LinearMap.mulLeft (AfP p) (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : (AfP p ⊗[ℚ] G.C)ˣ) :
      AfP p ⊗[ℚ] G.C))).coeff k := by
  intro p _ G k
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  exact (continuous_charpoly_coeff_mulLeft (R := AfP p) (A := AfP p ⊗[ℚ] G.C) k).comp
    (Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousGlobalWhittakerCoefficientArchimedeanStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_globalWhittakerCoefficient_archimedean : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ g h : GA E a, Continuous (fun y : GL (Fin a) (Cinf E) => GlobalTheory.JSW.whit φ.1 (g * infGL E a y * h)) := by
  first | exact @GlobalTheory.JSW.continuous_whit_infGL | exact GlobalTheory.JSW.continuous_whit_infGL | (intros; apply GlobalTheory.JSW.continuous_whit_infGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicComponentAtPlaceExplicit
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem continuous_tensorMap {R R' : Type} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing R'] [Algebra ℚ R'] [TopologicalSpace R'] [IsTopologicalRing R']
    {C : Type} [Ring C] [Algebra ℚ C] [Module.Finite ℚ C] (f : R →ₐ[ℚ] R') (hf : Continuous f) :
    letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
    letI : TopologicalSpace (R' ⊗[ℚ] C) := moduleTopology R' (R' ⊗[ℚ] C)
    Continuous (Algebra.TensorProduct.map f (AlgHom.id ℚ C)) := by
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  letI : TopologicalSpace (R' ⊗[ℚ] C) := moduleTopology R' (R' ⊗[ℚ] C)
  haveI : IsModuleTopology R (R ⊗[ℚ] C) := ⟨rfl⟩
  haveI : IsModuleTopology R' (R' ⊗[ℚ] C) := ⟨rfl⟩
  haveI : ContinuousAdd (R' ⊗[ℚ] C) := IsModuleTopology.toContinuousAdd R' _
  haveI : ContinuousSMul R' (R' ⊗[ℚ] C) := IsModuleTopology.toContinuousSMul R' _
  let b := Module.finBasis ℚ C
  let bA := Algebra.TensorProduct.basis R b
  let bB := Algebra.TensorProduct.basis R' b
  have key : ∀ x, Algebra.TensorProduct.map f (AlgHom.id ℚ C) x = ∑ i, f (bA.repr x i) • bB i := by
    intro x
    conv_lhs => rw [← bA.sum_repr x]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bA, bB, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e : (⇑(Algebra.TensorProduct.map f (AlgHom.id ℚ C))) = fun x => ∑ i, f (bA.repr x i) • bB i := funext key
  rw [e]
  refine continuous_finset_sum _ fun i _ => ?_
  exact (hf.comp (IsModuleTopology.continuous_of_linearMap (bA.coord i))).smul continuous_const

theorem continuous_piV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Continuous (piV G v) := by
  intro p _ G v
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) _
  have hf : Continuous (AfP.eval v) := RestrictedProduct.continuous_eval v
  have hφ := continuous_tensorMap (C := G.C) (AfP.eval v) hf
  have h1 := Units.continuous_map (f := (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom.toMonoidHom) hφ
  have h2 := Units.continuous_map (f := (AfP.eval v).toRingHom.toMonoidHom) hf
  refine continuous_induced_rng.2 ?_
  exact (h1.comp (continuous_fst.comp continuous_subtype_val)).prodMk (h2.comp (continuous_snd.comp continuous_subtype_val))

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordEqOfPerConj
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

section Letters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_of_mem (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) :
    perFr X x v τ.1 i =
      if hi : X.p0 + i < r then ((mat x τ)⁻¹.mulVec (Data.emb τ.1 v)) ⟨X.p0 + i, hi⟩ else 0 := by
  unfold perFr
  rw [dif_pos τ.2]

theorem perFr_of_conj (X : Data E r) (x : Frame X.Ψ r) (v : Fin r → E) (τ : X.Ψ) (i : ℕ) (j : Fin r)
    (hj : (j : ℕ) = X.p0 - 1 - i) :
    perFr X x v (conjEmb τ.1) i = hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
  have hcc : conjEmb (conjEmb τ.1) = τ.1 := by
    ext a; simp [conjEmb]
  have h1 : conjEmb τ.1 ∉ X.Ψ := (X.cmType τ.1).1 τ.2
  have h2 : conjEmb (conjEmb τ.1) ∈ X.Ψ := by rw [hcc]; exact τ.2
  have h3 : X.p0 - 1 - i < r := hj ▸ j.2
  unfold perFr
  rw [dif_neg h1, dif_pos h2, dif_pos h3]
  have key : ∀ (σ : E →+* ℂ) (hσ : σ ∈ X.Ψ), σ = τ.1 →
      hermC σ X.Gm (FD.col (mat x ⟨σ, hσ⟩) ⟨X.p0 - 1 - i, h3⟩) (Data.emb σ v) =
        hermC τ.1 X.Gm (FD.col (mat x τ) j) (Data.emb τ.1 v) := by
    intro σ hσ h
    subst h
    have : (⟨X.p0 - 1 - i, h3⟩ : Fin r) = j := Fin.ext hj.symm
    rw [this]
  exact key _ h2 hcc

theorem coord_eq_of_per_mem (X : Data E r) (τ : X.Ψ) (a : Fin r) (ha : X.p0 ≤ (a : ℕ)) (i : ℕ)
    (h : ∀ x v, per X x v (τ, a) = perFr X x v τ.1 i) : (a : ℕ) = X.p0 + i := by
  obtain ⟨x, hm⟩ : ∃ x : Frame X.Ψ r, mat x τ = 1 := ⟨fun _ => (1 : Matrix (Fin r) (Fin r) ℂ), rfl⟩
  have h1 := h x (Pi.single a 1)
  rw [per_of_le X _ _ _ ha, perFr_of_mem, hm, inv_one, one_mulVec] at h1
  by_contra hne
  split_ifs at h1 with hi
  · have h2 : (⟨X.p0 + i, hi⟩ : Fin r) ≠ a := fun e => hne (by rw [← e])
    simp [Data.emb, Pi.single_eq_of_ne h2] at h1
  · simp [Data.emb] at h1

theorem coord_eq_of_per_conj (X : Data E r) (τ : X.Ψ) (a : Fin r) (ha : (a : ℕ) < X.p0) (i : ℕ)
    (h : ∀ x v, per X x v (τ, a) = perFr X x v (conjEmb τ.1) i) : (a : ℕ) = X.p0 - 1 - i := by
  have hle := X.p0_le
  obtain ⟨s, t, hst⟩ : ∃ s t, X.Gm s t ≠ 0 := by
    by_contra hc
    push Not at hc
    exact X.Gm_det (Matrix.det_eq_zero_of_row_eq_zero a (hc a))
  obtain ⟨x, hm⟩ : ∃ x : Frame X.Ψ r, mat x τ = Matrix.single s a 1 :=
    ⟨fun _ => (Matrix.single s a 1 : Matrix (Fin r) (Fin r) ℂ), rfl⟩
  have h1 := h x (Pi.single t 1)
  rw [per_of_lt X _ _ _ ha, perFr_of_conj X _ _ τ i ⟨X.p0 - 1 - i, by omega⟩ rfl, hm] at h1
  by_contra hne
  have h2 : a ≠ (⟨X.p0 - 1 - i, by omega⟩ : Fin r) := fun e => hne (by rw [e])
  simp [hermC, FD.col, Data.emb, Matrix.single_apply, Pi.single_apply, h2, apply_ite, hst] at h1

theorem Dic.letter {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} {σ : c.F →+* ℂ}
    {X : Data E r} {g q0 n : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} (Dc : Dic Dw c σ X g q0 n a)
    (hσ : ∀ τ, Formalism.L2.PjFree.relab c σ τ = τ) (hm : ∀ τ, τ ∉ X.Ψ → Dw.mult τ ≤ X.p0) (ℓ : LtN Dw n) :
    (Dc.eL ℓ).2.2 = ℓ.2.2 ∧
      ((∃ k, (Dc.eL ℓ).2.1 = Sum.inl k ∧ ℓ.1 = (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1) ∨
       (∃ k, (Dc.eL ℓ).2.1 = Sum.inr k ∧ ℓ.1 = conjEmb (Dc.eL ℓ).1.1 ∧ (k : ℕ) = ℓ.2.1)) := by
  have hd := Dc.dir_eq ℓ
  generalize Dc.eL ℓ = L at hd ⊢
  obtain ⟨t, ρ, b⟩ := L
  obtain ⟨τ, i, b'⟩ := ℓ
  simp only [letterDir] at hd ⊢
  have hb : b = b' := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    simp [Pi.single_eq_of_ne hne] at this
  subst hb
  have hj : Dc.idx.symm (rowOf X Dc.hr (t, ρ)) = Dc.e.symm ⟨τ, i⟩ := by
    by_contra hne
    have := congrFun (congrFun hd b) (Dc.idx.symm (rowOf X Dc.hr (t, ρ)))
    rw [Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_same, Pi.single_eq_of_ne hne] at this
    exact one_ne_zero this
  have hi : Dc.idx (Dc.e.symm ⟨τ, i⟩) = (t, rowIdx Dc.hr ρ) := by rw [← hj, Equiv.apply_symm_apply]; rfl
  have hty := Dc.ty_eq (Dc.e.symm ⟨τ, i⟩)
  have hper : ∀ x v, per X x v (t, rowIdx Dc.hr ρ) = perFr X x v τ i := fun x v => by
    have := Dc.per_eq x v (Dc.e.symm ⟨τ, i⟩)
    rwa [pv, Function.comp_apply, hi, hσ, Equiv.apply_symm_apply] at this
  rw [hi, hσ, Equiv.apply_symm_apply] at hty
  refine ⟨rfl, ?_⟩
  rcases ρ with k | k
  · have h1 : τ = t.1 := hty.symm.trans (rowType_rowOf_inl X Dc.hr t k)
    subst h1
    have h2 := coord_eq_of_per_mem X t _ (by simp) i hper
    rw [rowIdx_inl] at h2
    exact Or.inl ⟨k, rfl, rfl, by omega⟩
  · have h1 : τ = conjEmb t.1 := hty.symm.trans (rowType_rowOf_inr X Dc.hr t k)
    subst h1
    have hk := k.2
    have h2 := coord_eq_of_per_conj X t _ (by rw [rowIdx_inr]; omega) i hper
    rw [rowIdx_inr] at h2
    have h3 := hm _ ((X.cmType t.1).1 t.2)
    have h4 : (i : ℕ) < X.p0 := lt_of_lt_of_le i.2 h3
    exact Or.inr ⟨k, rfl, rfl, by omega⟩

end Letters

set_option maxHeartbeats 1000000 in

theorem letters_eq_fockVars : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (X : Data D.host.E D.R.r) (g : ℕ) (Dc : Dic (T.Q.Dw ((i : ℕ) + 1)) O.c' (inC O.c') X g (T.Q.Dw ((i : ℕ) + 1)).p (Vc D i).rank (wtA (κ i))) (vr : Harm.Var X.Ψ (T.Q.Dw ((i : ℕ) + 1)).p X.p0 (Fin (Vc D i).rank) ≃ FVar D (Wc D i).rank (Vc D i).rank), IsMod (Wc D i) (rank_Wc i) X → X.p0 = (T.Q.Dw ((i : ℕ) + 1)).q → IsVarOf (Vc D i) (Wc D i) X (T.Q.Dw ((i : ℕ) + 1)).p vr → (∀ ℓ : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank, (vr (Dc.eL ℓ)).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (vr (Dc.eL ℓ)).1 ∧ ((vr (Dc.eL ℓ)).2.1 : ℕ) = ℓ.2.1) ∨ (ℓ.1 = conjEmb (tauE D (vr (Dc.eL ℓ)).1) ∧ ((vr (Dc.eL ℓ)).2.1 : ℕ) = (T.Q.Dw ((i : ℕ) + 1)).p + ℓ.2.1))) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ _ hT i Tp tup O _ X g Dc vr hM hp hv ℓ
  have hP := hT.laws.pins
  have hm : ∀ τ, τ ∉ X.Ψ → (T.Q.Dw ((i : ℕ) + 1)).mult τ ≤ X.p0 := fun τ hτ => by
    unfold Datum.mult
    rw [if_neg fun h : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 => hτ ((hM.psi τ).2 (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ h)), hp]
  obtain ⟨h1, h2⟩ := Dic.letter Dc (fun τ => RingHom.ext fun _ => rfl) hm ℓ
  obtain ⟨g1, g2, g3⟩ := hv (Dc.eL ℓ)
  refine ⟨g2.trans h1, ?_⟩
  rcases h2 with ⟨k, e1, e2, e3⟩ | ⟨k, e1, e2, e3⟩
  · rw [e1, Sum.elim_inl] at g3
    exact Or.inl ⟨e2.trans g1, g3.trans e3⟩
  · rw [e1, Sum.elim_inr] at g3
    exact Or.inr ⟨by rw [← g1]; exact e2, by rw [g3, e3]⟩

end GlobalTheory.AdTh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormModerateGrowthCompactStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_moderate_growth_compact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (π : CuspSub E a) (φ : Sm E a), φ ∈ π.V → ∀ F ∈ GlobalTheory.JSW.MirSemi.locSpan S φ.1, Continuous F ∧ ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E), ‖F (g * infGL E a y)‖ ≤ C * height y ^ N := by
  first | exact @GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate | exact GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate | (intros; apply GlobalTheory.JSW.MirSemi.locSpan_continuous_moderate <;> assumption)
end

