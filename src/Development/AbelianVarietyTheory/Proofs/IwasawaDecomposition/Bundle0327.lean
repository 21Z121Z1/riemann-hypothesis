import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0310
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDivZpowOrd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLocalSubringGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.InducedPow

section Charts

variable {X Z : Scheme.{0}} (B : LB X) (j : Z ⟶ X) (m : ℕ)

theorem mem_chart {i : ((lbPow B m).pull j).ι} {x : Z} (hx : x ∈ ((lbPow B m).pull j).U i) :
    x ∈ (B.pull j).U fun _ => i PUnit.unit PUnit.unit :=
  Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (Set.mem_iInter.1 hx PUnit.unit) PUnit.unit

theorem pull_g (i i' : (B.pull j).ι)
    (l : (B.pull j).U i ⊓ (B.pull j).U i' ≤ j ⁻¹ᵁ (B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit))) :
    ((B.pull j).g i i').val = (j.appLE _ _ l).hom (B.g (i PUnit.unit) (i' PUnit.unit)).val := by
  have : (B.pull j).g i i' = res l (pullU j _ (B.g (i PUnit.unit) (i' PUnit.unit))) := by
    change ∏ _k : PUnit, _ = _
    exact (Fintype.prod_unique _).trans (zpow_one _)
  rw [this]
  rfl

theorem pow_g (i i' : (lbPow B m).ι)
    (l : (lbPow B m).U i ⊓ (lbPow B m).U i' ≤ B.U (i PUnit.unit) ⊓ B.U (i' PUnit.unit)) :
    ((lbPow B m).g i i').val =
      (X.presheaf.map (homOfLE l).op).hom (B.g (i PUnit.unit) (i' PUnit.unit)).val ^ m := by
  have : (lbPow B m).g i i' = res l (B.g (i PUnit.unit) (i' PUnit.unit)) ^ m := by
    change ∏ _k : PUnit, _ = _
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rfl
  rw [this, Units.val_pow_eq_pow_val]
  rfl

variable [IsIntegral Z]

theorem presents_pow (hB : B.IsLB) {Δ : CartierDiv Z} {r : (B.pull j).ι → Z.functionFieldˣ}
    (hr : Presents Δ (B.pull j) r) :
    Presents (m • Δ) ((lbPow B m).pull j) fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ m := by
  refine ⟨LB.isLB_pull (isLB_lbPow hB m) j, fun i i' h => ?_,
    fun i x hx => (hr.isEqn _ x (mem_chart B j m hx)).nsmul m⟩
  have l₀ : ((lbPow B m).pull j).U i ⊓ ((lbPow B m).pull j).U i' ≤
      (B.pull j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (B.pull j).U fun _ => i' PUnit.unit PUnit.unit :=
    fun _ hx => ⟨mem_chart B j m hx.1, mem_chart B j m hx.2⟩
  have l₁ : ((lbPow B m).pull j).U i ⊓ ((lbPow B m).pull j).U i' ≤
      j ⁻¹ᵁ ((lbPow B m).U (i PUnit.unit) ⊓ (lbPow B m).U (i' PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have l₂ : (lbPow B m).U (i PUnit.unit) ⊓ (lbPow B m).U (i' PUnit.unit) ≤
      B.U (i PUnit.unit PUnit.unit) ⊓ B.U (i' PUnit.unit PUnit.unit) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have l₃ : (B.pull j).U (fun _ => i PUnit.unit PUnit.unit) ⊓ (B.pull j).U (fun _ => i' PUnit.unit PUnit.unit) ≤
      j ⁻¹ᵁ (B.U (i PUnit.unit PUnit.unit) ⊓ B.U (i' PUnit.unit PUnit.unit)) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hr.isRatSec _ _ (l₀ h), mul_pow,
    pull_g _ j i i' l₁, pow_g B m _ _ l₂, map_pow, map_pow, pull_g B j _ _ l₃, ← fnOf_resG l₀ h]
  congr 3
  have e : j.appLE _ _ l₃ ≫ Z.presheaf.map (homOfLE l₀).op =
      X.presheaf.map (homOfLE l₂).op ≫ j.appLE _ _ l₁ := by
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  exact congrArg (fun ψ => ψ.hom (B.g (i PUnit.unit PUnit.unit) (i' PUnit.unit PUnit.unit)).val) e

end Charts

theorem unitAt_pow {Z : Scheme.{0}} [IsIntegral Z] {x : Z} {f : Z.functionField} (h : UnitAt x f) (n : ℕ) :
    UnitAt x (f ^ n) := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a ^ n, ha.pow n, map_pow _ _ _⟩

theorem valAt_pow {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {f : Z.functionField}
    (h : RegAt (below y) f) (n : ℕ) : valAt y (f ^ n) = valAt y f ^ n := by
  obtain ⟨a, rfl⟩ := h
  rw [← map_pow, OfModel.valAt_algebraMap, OfModel.valAt_algebraMap, map_pow]

theorem ratVal_pow {k : Type} [CommRing k] {σ : k →+* ℂ} {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (y : CxPts q σ) {f : Z.functionField} (h : UnitAt (under y) f) (n : ℕ) :
    ratVal (f ^ n) y = ratVal f y ^ n := by
  induction n with
  | zero =>
    have e := ratVal_fnOf (y := y) CxPts.mem_ptsIn_top trivial 1
    rwa [map_one, CxPts.ev_one CxPts.mem_ptsIn_top, ← pow_zero f, ← pow_zero (ratVal f y)] at e
  | succ n ih => rw [pow_succ, pow_succ, ratVal_mul (unitAt_pow h n).regAt h.regAt, ih]

theorem induced_pow : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (k m : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
    A.Induced M L k cf → A.Induced M (L.pow m) (k * m) cf := by
  rintro F _ _ C Y A M L k m cf ⟨hfin, r, hr, hinf, hv⟩
  have hD : ((k * m : ℕ+) : ℕ) • A.D = (m : ℕ) • (k : ℕ) • A.D := by rw [PNat.mul_coe, mul_nsmul]
  have hr' := presents_pow L.B M.j m L.isLB hr
  refine ⟨hfin, fun i => r (fun _ => i PUnit.unit PUnit.unit) ^ (m : ℕ), ?_, ?_, ?_⟩
  · rw [hD]; exact hr'
  · intro σ y y' i f hy hi hf
    have hi' := mem_chart L.B M.j m hi
    obtain ⟨g, hg⟩ := A.D.exists_isEqn (under y)
    have hgen := CartierDiv.isEqn_iff_generatesAt_inv.1 hg
    have hgenk (n : ℕ) : (n • A.D).GeneratesAt (under y) ((g : Y.Fn)⁻¹ ^ n) := by
      have := CartierDiv.isEqn_iff_generatesAt_inv.1 (hg.nsmul n)
      rwa [Units.val_pow_eq_pow_val, ← inv_pow] at this
    have h₁ := hinf σ y y' (fun _ => i PUnit.unit PUnit.unit) _ hy hi' (hgenk k).regularAt
    rw [C.pn_mPow Y σ A.D k (A.m σ) _ y hgen] at h₁
    have hu := (hr.isEqn _ _ hi').generatesAt_iff.1 (hgenk k)
    have ha : RegAt (under y) (f * (g : Y.Fn) ^ ((k * m : ℕ+) : ℕ)) := by
      have := (hg.nsmul _).regularAt_iff.1 hf
      rwa [Units.val_pow_eq_pow_val] at this
    have h₂ := C.pn_mul Y σ _ (C.mPow Y σ A.D ((k * m : ℕ+) : ℕ) (A.m σ)) _ _ y ha (hgenk _).regularAt
    rw [C.pn_mPow Y σ A.D _ (A.m σ) _ y hgen, mul_assoc, ← mul_pow, mul_inv_cancel₀ g.ne_zero, one_pow,
      mul_one] at h₂
    have h₃ : f * ((r (fun _ => i PUnit.unit PUnit.unit) ^ (m : ℕ) : Y.Fnˣ) : Y.Fn) =
        f * (g : Y.Fn) ^ ((k * m : ℕ+) : ℕ) *
          ((g : Y.Fn)⁻¹ ^ (k : ℕ) * (r (fun _ => i PUnit.unit PUnit.unit) : Y.Fn)) ^ (m : ℕ) := by
      rw [Units.val_pow_eq_pow_val, mul_pow, ← pow_mul, PNat.mul_coe, mul_assoc, ← mul_assoc (_ ^ (_ * _)),
        ← mul_pow, mul_inv_cancel₀ g.ne_zero, one_pow, one_mul]
    have h₄ : ((L.pow m).φ _).φ (i PUnit.unit) y' =
        ((m : ℕ) : ℝ) * (L.φ _).φ (i PUnit.unit PUnit.unit) y' :=
      ((L.φ _).zpow_φ _ _ y').trans (by simp)
    rw [h₂, h₃, ratVal_mul ha (unitAt_pow hu _).regAt, ratVal_pow y hu, h₄, norm_mul, norm_pow, mul_pow,
      ← pow_mul, mul_comm (m : ℕ) 2, pow_mul, ← mul_neg ((m : ℕ) : ℝ), Real.exp_nat_mul, mul_assoc (_ ^ 2), ← mul_pow, ← h₁,
      mul_pow, ← Real.exp_nat_mul, ← pow_mul, PNat.mul_coe, mul_left_comm]
    congr 3
    push_cast
    ring
  · intro v e y yt i h hi
    have hi' : ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit PUnit.unit) := fun x hx => Set.mem_iInter.1 (hi hx) PUnit.unit
    have h₁ := hv v e y yt (fun _ => i PUnit.unit PUnit.unit) h hi'
    have h₂ : below y.1 ∈ (L.B.pull M.j).U fun _ => i PUnit.unit PUnit.unit :=
      OfModel.le_chart M L.B e y yt h (i := fun _ => i PUnit.unit PUnit.unit) hi' trivial
    have hu : RegAt (below y.1) (((eqn A.D (below y.1))⁻¹ ^ (k : ℕ) *
        r (fun _ => i PUnit.unit PUnit.unit) : Y.Fnˣ) : Y.Fn) := by
      have := (((A.D.exists_isEqn (below y.1)).choose_spec.nsmul k).iff_unitAt.1 (hr.isEqn _ _ h₂)).regAt
      rwa [div_eq_inv_mul, ← Units.val_inv_eq_inv_val, ← Units.val_mul, ← inv_pow] at this
    rw [PNat.mul_coe, pow_mul, ← mul_pow, Units.val_pow_eq_pow_val, valAt_pow _ hu, map_pow, Real.log_pow]
    push_cast at h₁ ⊢
    linear_combination ((m : ℕ) : ℝ) * h₁

end GlobalTheory.TrueGeo.InducedPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegrationByPartsRightDerivativeAdelicQuotient
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.IntByParts

theorem setIntegral_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (a : G) :
    ∫ g in 𝓕, Φ (g * a) ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hm : MeasurePreserving (fun g : G => g * a) μ μ := measurePreserving_mul_right μ a
  have h' : IsFundamentalDomain Γ ((fun g : G => g * a) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv hm.quasiMeasurePreserving Function.bijective_id fun γ g => mul_assoc _ _ _
  rw [← hm.setIntegral_preimage_emb (measurableEmbedding_mulRight a) Φ 𝓕]
  exact h.setIntegral_eq h' (f := fun g => Φ (g * a)) fun γ g => by
    change Φ ((γ : G) * g * a) = _
    rw [mul_assoc, hΦ _ γ.2]

theorem setIntegral_deriv_eq_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) {Φ Φ' : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hc : Continuous Φ) (hc' : Continuous Φ')
    {B B' : ℝ} (hB : ∀ g, ‖Φ g‖ ≤ B) (hB' : ∀ g, ‖Φ' g‖ ≤ B') {a : ℝ → G} (h0 : a 0 = 1)
    (hd : ∀ g t, HasDerivAt (fun s : ℝ => Φ (g * a s)) (Φ' (g * a t)) t) : ∫ g in 𝓕, Φ' g ∂μ = 0 := by
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ) (x₀ := 0)
    (F := fun t g => Φ (g * a t)) (F' := fun t g => Φ' (g * a t)) (s := Set.univ) (bound := fun _ => B')
    Filter.univ_mem
    (.of_forall fun t => (hc.comp (continuous_mul_right _)).measurable.aestronglyMeasurable)
    (Integrable.of_bound (hc.comp (continuous_mul_right _)).measurable.aestronglyMeasurable B
      (.of_forall fun g => hB _))
    (hc'.comp (continuous_mul_right _)).measurable.aestronglyMeasurable
    (.of_forall fun g t _ => hB' _) (integrable_const _) (.of_forall fun g t _ => hd g t)
  have h2 := key.2
  simp only [setIntegral_mul_right Γ μ h hΦ, h0, mul_one] at h2
  exact h2.unique (hasDerivAt_const _ _)

variable {D : D7} {θ : InfF D} {V : HSp D}

theorem mul_cont_bounded {φ F : GA D V → ℂ} (hφ : IsMod θ V φ) (hF : F ∈ Decay θ V) :
    Continuous (fun g => φ g * F g) ∧ ∃ B : ℝ, ∀ g, ‖φ g * F g‖ ≤ B := by
  obtain ⟨c1, N, C, hC⟩ := hφ.2.2 [] (by simp)
  obtain ⟨c2, hr⟩ := hF.2.2 [] (by simp)
  obtain ⟨B, hB⟩ := IsRapidDecay.mul_bounded (φ := F) (ψ := φ) hr hφ.2.1 hC
  exact ⟨Continuous.mul c1 c2, B, fun g => by rw [norm_mul]; exact hB g⟩

theorem integral_Rder_mul : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ F, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ ∧ ∫ g in 𝓕, Rder θ V τ X φ g * F g ∂μ = -∫ g in 𝓕, φ g * Rder θ V τ X F g ∂μ := by
  intro D θ hθ V μ 𝓕 hq τ X hX φ F hφ hF
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hfin := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 hq).2
  haveI := hq.1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hq.1).1
  have int : ∀ {φ F : GA D V → ℂ}, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ := by
    intro φ F hφ hF
    obtain ⟨c, B, hB⟩ := mul_cont_bounded hφ hF
    exact Measure.integrableOn_of_bounded (M := B) hfin c.measurable.aestronglyMeasurable (.of_forall hB)
  refine ⟨int hφ hF, ?_⟩
  obtain ⟨c0, B0, hB0⟩ := mul_cont_bounded hφ hF
  obtain ⟨c1, B1, hB1⟩ := mul_cont_bounded (hφ.rder hX) hF
  obtain ⟨c2, B2, hB2⟩ := mul_cont_bounded hφ (Rder_mem_Decay hF hX)
  have key := setIntegral_deriv_eq_zero (GQ V) μ hq.2 hfin (Φ := fun g => φ g * F g)
    (Φ' := fun g => Rder θ V τ X φ g * F g + φ g * Rder θ V τ X F g)
    (fun γ hγ g => by simp only [hφ.2.1 γ hγ, hF.2.1 γ hγ]) c0 (c1.add c2) hB0
    (fun g => (norm_add_le _ _).trans (add_le_add (hB1 g) (hB2 g))) (oneP_zero (V := V) (τ := τ) (X := X) hθ)
    fun g t => (hasDerivAt_oneP hθ hX (hasDerivAt_Rder hφ.1 hX) g t).mul
      (hasDerivAt_oneP hθ hX (hasDerivAt_Rder hF.1 hX) g t)
  rw [integral_add (int (hφ.rder hX) hF) (int hφ (Rder_mem_Decay hF hX))] at key
  exact eq_neg_of_add_eq_zero_left key

end GlobalTheory.Mem.IntByParts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntersectionNumberFinitePushforwardStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intersection_number_finite_pushforward : ∀ (κ : Type) [Field κ] (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] [Algebra κ Γ(Z, ⊤)] (f : Z' ⟶ Z) [IsFinite f], IsProjOver (strHom κ Z) → topologicalKrullDim Z = 1 → f (genericPoint Z') = genericPoint Z → ∀ N : LB Z, N.IsLB → interNumOn κ f ![N] = (f.residueDegree (genericPoint Z') : ℤ) * interNum κ (structureModule Z) ![N] := by
  first | exact @GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul | exact GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul | (intros; apply GlobalTheory.ProjFin.interNumOn_eq_residueDegree_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompactBoundedTorusStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_boundedTorus' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m : ℕ) (R1 R2 : kˣ), IsCompact {t : Fin m → kˣ | ∀ i, valuation k (R2 : k) ≤ valuation k (t i : k) ∧ valuation k (t i : k) ≤ valuation k (R1 : k)} := by
  first | exact @GlobalTheory.isCompact_boundedTorus | exact GlobalTheory.isCompact_boundedTorus | (intros; apply GlobalTheory.isCompact_boundedTorus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalIsometryTransportHermitianStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspidal_isometryTransport_hermitian : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (φ : GA D V → ℂ), IsCuspFun V φ → IsCuspFun V' (I.tr φ) := by
  first | exact @GlobalTheory.Mem.Isom.isCuspFun_tr | exact GlobalTheory.Mem.Isom.isCuspFun_tr | (intros; apply GlobalTheory.Mem.Isom.isCuspFun_tr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureBoundedDomainHodgeGStatement
section
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_boundedDomainHodgeGram : ∀ (m r : ℕ) (x : Fin m → Fin r → ℂ), (1 - Matrix.of x * (Matrix.of x)ᴴ).PosDef →
    IsNegSq (curv (domGram m r) x) r := by
  first | exact @GlobalTheory.PointFormSign.curv_domGram_isNegSq | exact GlobalTheory.PointFormSign.curv_domGram_isNegSq | (intros; apply GlobalTheory.PointFormSign.curv_domGram_isNegSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureOfHolomorphicFrameCStatement
section
open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNegHermitianSquare_curvature_of_holomorphic_frameChange : ∀ {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (W : V n → Matrix (Fin m) (Fin m) ℂ)
    (Z : V n → (Fin m → Fin r → ℂ)) (κ : ℝ), 0 < κ →
    (∀ᶠ u in 𝓝 v, G u = (κ : ℂ) • ((W u)ᵀ * domGram m r (Z u) * (W u)ᴴᵀ)) →
    (∀ᶠ u in 𝓝 v, DifferentiableAt ℂ Z u) → (∀ i j, ∀ᶠ u in 𝓝 v, DifferentiableAt ℂ (fun u => W u i j) u) →
    IsUnit (W v).det → (1 - Matrix.of (Z v) * (Matrix.of (Z v))ᴴ).PosDef →
    IsNegSq (curv (domGram m r) (Z v)) r → IsNegSq (curv G v) r := by
  first | exact @GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp | exact GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp | (intros; apply GlobalTheory.PointFormSign.isNegSq_curv_of_changeFrame_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IwasawaCellDecomposition
section
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwaCell

theorem exists_mem_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ g : GL (Fin m) k, ∃ a : Fin m → ℤ, g ∈ GlobalTheory.IwaCell.cell ϖ a := by
  intro k _ _ _ _ m ϖ hϖ g
  obtain ⟨k₀, b, hb, hg⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k m g⁻¹
  have hg' : g = b⁻¹ * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹ := by
    rw [← _root_.mul_inv_rev, ← hg, inv_inv]
  set c := b⁻¹ with hc
  have hcT : c.val.BlockTriangular id := by
    have : c.val = b.val⁻¹ := by rw [hc, Matrix.coe_units_inv]
    rw [this]; exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hdet : c.val.det = ∏ i, c.val i i := Matrix.det_of_upperTriangular hcT
  have hd : ∀ i, c.val i i ≠ 0 := fun i h => by
    have := Matrix.GeneralLinearGroup.det_ne_zero c
    rw [hdet] at this
    exact this (Finset.prod_eq_zero (Finset.mem_univ i) h)
  let d : Fin m → kˣ := fun i => Units.mk0 _ (hd i)
  let a : Fin m → ℤ := fun i => ord k (d i)
  let e : Fin m → kˣ := fun i => d i / ϖ ^ a i
  have he : ∀ i, valuation k (e i : k) = 1 := fun i => by
    apply ord_eq_zero_iff.1
    simp only [e, div_eq_mul_inv, ← _root_.zpow_neg, ord_mul, ord_zpow, hϖ, a]
    ring
  have hde : d = (fun i => ϖ ^ a i) * e := by
    funext i; simp [e]
  let u := c * (diagT k (Fin m) d)⁻¹
  have hu : u ∈ unipB k (Fin m) := by
    rw [mem_unipB]
    have hval : u.val = c.val * diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) := by
      simp only [u, ← map_inv, Units.val_mul, val_diagT, Pi.inv_apply]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hval, mul_diagonal, hcT hij, zero_mul]
    · rw [hval, mul_diagonal]; simp [d, mul_inv_cancel₀ (hd i)]
  refine ⟨a, u, hu, diagT k (Fin m) e * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹,
    mul_mem (GlobalTheory.LocalCartan.diagT_mem_KO he) (inv_mem ⟨k₀, rfl⟩), ?_⟩
  rw [hg', tD, ← mul_assoc, mul_assoc u, ← map_mul, ← hde]
  simp [u]

end GlobalTheory.IwaCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ProperCover

theorem isFractionRing_evaluation (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

theorem evaluation_genericPoint_injective (X : Scheme.{0}) [IsIntegral X] (V : X.Opens)
    (hV : genericPoint X ∈ V) : Function.Injective (X.evaluation V (genericPoint X) hV) := by
  intro a b h
  apply germ_injective_of_isIntegral X _ hV
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  apply φ.injective
  exact h

theorem dim_le_of_residueDegree_pos {Z' Z : Scheme.{0}} [IsIntegral Z'] [IsIntegral Z]
    [IsLocallyNoetherian Z] (f : Z' ⟶ Z) [LocallyOfFiniteType f]
    (hg : f (genericPoint Z') = genericPoint Z) (hdeg : 0 < f.residueDegree (genericPoint Z')) :
    topologicalKrullDim Z' ≤ topologicalKrullDim Z := by
  have hd : ∀ {X : Scheme.{0}} (U : X.Opens), IsAffineOpen U →
      topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) := fun {X} U hU => by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U))
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens (Opens.mem_top (f x))
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 Z'.isBasis_affineOpens (show x ∈ f ⁻¹ᵁ U from hxU)
  refine ⟨V, V.isOpen, hxV, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le Z (U : Set Z))
  rw [hd U hU, hd V hV]
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Z, U) Γ(Z', V) := f.finiteType_appLE hU hV hVU
  have hηV : genericPoint Z' ∈ V :=
    ((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  have hyU : f (genericPoint Z') ∈ U := hVU hηV
  letI := (Z.evaluation U _ hyU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    (Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z')))
      (Z'.residueField (genericPoint Z')) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := isFractionRing_evaluation Z hU hg hyU
  have : Algebra.IsAlgebraic Γ(Z, U) (Z.residueField (f (genericPoint Z'))) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(Z, U))
  have : Module.Finite (Z.residueField (f (genericPoint Z'))) (Z'.residueField (genericPoint Z')) :=
    Module.finite_of_finrank_pos hdeg
  have : Algebra.IsAlgebraic Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    Algebra.IsAlgebraic.trans Γ(Z, U) (Z.residueField (f (genericPoint Z'))) _
  have hnat : f.appLE U V hVU ≫ Z'.evaluation V _ hηV =
      Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z') := by
    rw [Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp [Scheme.evaluation]
  let ψ : Γ(Z', V) →ₐ[Γ(Z, U)] Z'.residueField (genericPoint Z') :=
    { (Z'.evaluation V _ hηV).hom with
      commutes' := fun a => RingHom.congr_fun congr($(hnat).hom) a }
  have hψ : Function.Injective ψ := evaluation_genericPoint_injective Z' V hηV
  have hinj : Function.Injective (algebraMap Γ(Z, U) Γ(Z', V)) := by
    have h1 : Function.Injective (algebraMap Γ(Z, U) (Z'.residueField (genericPoint Z'))) := by
      rw [IsScalarTower.algebraMap_eq Γ(Z, U) (Z.residueField (f (genericPoint Z')))
        (Z'.residueField (genericPoint Z'))]
      exact (f.residueFieldMap (genericPoint Z')).hom.injective.comp (IsFractionRing.injective Γ(Z, U) _)
    intro a b h
    apply h1
    rw [← ψ.commutes, ← ψ.commutes, h]
  have : FaithfulSMul Γ(Z, U) Γ(Z', V) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Algebra.IsAlgebraic Γ(Z, U) Γ(Z', V) := Algebra.IsAlgebraic.of_injective ψ hψ
  exact GlobalTheory.ModelDom.ringKrullDim_le_of_isAlgebraic _ _

theorem dim_eq_one : ∀ (Z' Z : Scheme.{0}) [IsIntegral Z'] [IsIntegral Z] [IsNoetherian Z] (f : Z' ⟶ Z)
    [IsProper f], topologicalKrullDim Z = 1 → f (genericPoint Z') = genericPoint Z →
    0 < f.residueDegree (genericPoint Z') → topologicalKrullDim Z' = 1 := by
  intro Z' Z _ _ _ f _ hd hg hdeg
  have : IsDominant f := ⟨(dense_iff_closure_eq.2 (genericPoint_spec Z)).mono
    (Set.singleton_subset_iff.2 ⟨_, hg⟩)⟩
  have := surjective_of_isDominant_of_isClosed_range f f.isClosedMap.isClosed_range
  refine le_antisymm ((dim_le_of_residueDegree_pos f hg hdeg).trans hd.le) ?_
  rw [← hd]
  exact PosBaseChange.dim_le_of_isClosedMap f.isClosedMap f.surjective

end GlobalTheory.ProperCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastThetaChainStepExponentsAndNonzeroVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.Cx GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastThetaChainStep_exponents_and_nonzero_vacuum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → IsInfFam R.θ → R.chain_ωX → R.chain_vX → ∀ t (k : Fin D.R.m), (k : ℕ) = D.R.m - 1 → IsStepWeil k R.ψ (Yc D (D.R.m - 1)) D.sp.X' (R.ωX t) ∧ IsVacVec R.ψ R.θ (R.MY (D.R.m - 1)) R.MX (R.vX t) := by
  first | exact @GlobalTheory.LastStepVac.last_step | exact GlobalTheory.LastStepVac.last_step | (intros; apply GlobalTheory.LastStepVac.last_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterSpaceCoordsIffLevelActsByCharStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (S : CSD K) (G : Type) [Group G] [Fintype G] (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (f : S.Forms), (∃ x, S.basis.equivFun.symm ((S.lvlE r P ψ).mulVec x) = f) ↔ ∀ h : P, r h f = ((ψ h : Kˣ) : K) • f := by
  first | exact @GlobalTheory.TopSpan.lvlE_range_iff | exact GlobalTheory.TopSpan.lvlE_range_iff | (intros; apply GlobalTheory.TopSpan.lvlE_range_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalChartLastStepClassesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFunctional_chart_lastStep_classes : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (A : ∀ u, Formalism.L2.Herm.AtT (I.rec7 l Z) u (H.vT u) (H.Fv u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → CarT H F A → ∀ u (h1 : 1 ≤ (I.rec7 l Z).R.m) (v : ((I.rec7 l Z).mem u).A.vT) (β : H.Ch u (I.rec7 l Z).R.m), Nonempty (Formalism.L2.Herm.FvTie (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (I.rec7 l Z).R.m) (H.lev u (I.rec7 l Z).R.m h1 le_rfl β).Lb (H.cls u (I.rec7 l Z).R.m h1 le_rfl β).y (fun c => (I.rec7 l Z).clsLat u (I.rec7 l Z).R.m c.1) (H.vT u v).1 (((I.rec7 l Z).mem u).A.Fv v) (fun c z => ((I.rec7 l Z).fm u).fv (I.rec7 l Z).R.m v c.1 ((A u).pr (I.rec7 l Z).R.m v c.1 z))) := by
  first | exact @GlobalTheory.Mem.Col2.TC.fvTie_chart_top | exact GlobalTheory.Mem.Col2.TC.fvTie_chart_top | (intros; apply GlobalTheory.Mem.Col2.TC.fvTie_chart_top <;> assumption)
end

