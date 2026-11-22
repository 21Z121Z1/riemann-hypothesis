import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2993
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0020
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2653
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3034
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2815
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResolutionMultLtOfConnectedness
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.LogResConn

theorem mult_le_ord_of_regularAt {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {F : CartierDiv Y} {v : Y} {f : Y.functionField} (h : (-F).RegularAt v f) (hf : f ≠ 0)
    (hv : Order.coheight v = 1) : F.mult v ≤ Scheme.ord f v := by
  obtain ⟨g, hg⟩ := F.exists_isEqn v
  obtain ⟨a, ha⟩ := hg.neg.regularAt_iff.1 h
  have hg0 : ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) ≠ 0 := Units.ne_zero _
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact mul_ne_zero hf hg0 ha.symm
  have h2 := ord_algebraMap hv ha0
  rw [ha, Scheme.ord_mul hf hg0] at h2
  have h3 := Scheme.ord_mul (x := v) (Units.ne_zero g) hg0
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, (unitAt_one v).ord_eq_zero] at h3
  rw [hg.mult_eq]
  have : (0 : ℤ) ≤ ((Module.length (Y.presheaf.stalk v) (Y.presheaf.stalk v ⧸ Ideal.span {a})).toNat : ℤ) :=
    Int.natCast_nonneg _
  omega

theorem mem_ring_of_regularAt {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] {q : Y ⟶ Sp k} {E : DivOver q} {F : CartierDiv Y} {w : Y}
    {f : Y.functionField} (hE : E.IsAt w) (h : (-F).RegularAt w f) (hF : 0 ≤ F.mult w) :
    f ∈ E.ring := by
  by_cases hf : f = 0
  · rw [hf]; exact zero_mem _
  have h1 := mult_le_ord_of_regularAt h hf hE.coheight_eq_one
  have h2 := hE.ord_eq (Units.mk0 f hf)
  have h3 := (E.ord_nonneg_iff (Units.mk0 f hf)).1 (by rw [h2]; simpa using hF.trans h1)
  simpa using h3

variable {k : Type} [Field k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [IsLocallyNoetherian Y] [GlobalTheory.IsNormalScheme Y]

theorem regAt_pull {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] [LocallyOfFiniteType (s ≫ p)]
    (hbir : Function.Bijective (functionFieldMap s)) {v : Y} {y : X} (hv : Order.coheight v = 1)
    (hsv : s v ⤳ y) {f : X.functionField} (hf : RegAt y f) : RegAt v (functionFieldMap s f) := by
  obtain ⟨E', hE'⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) hv
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_primeDivisor_over_target_birational k X Y p s hbir E'
  have ht := GlobalTheory.T.primeDivisorCentre_through_image k X Y p s E' E hE v (hE'.through specializes_rfl)
  exact (hE' _).1 ((hE f).1 ((ht.of_specializes hsv) f hf))

theorem unitAt_pull {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] [LocallyOfFiniteType (s ≫ p)]
    (hbir : Function.Bijective (functionFieldMap s)) {v : Y} {y : X} (hv : Order.coheight v = 1)
    (hsv : s v ⤳ y) {f : X.functionField} (hf : UnitAt y f) : UnitAt v (functionFieldMap s f) := by
  have hf0 := hf.ne_zero
  obtain ⟨h1, h2⟩ := (unitAt_iff hf0).1 hf
  refine (unitAt_iff ((map_ne_zero _).2 hf0)).2 ⟨regAt_pull (p := p) s hbir hv hsv h1, ?_⟩
  rw [← map_inv₀]
  exact regAt_pull (p := p) s hbir hv hsv h2

end GlobalTheory.LogResConn

namespace GlobalTheory.LogResConn

theorem mult_lt_of_connected : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  intro X _ _ p n hp hn η m G N Y _ _ s _ K B F hη hm hres hF hcoh y σ hyint hdisc hσ hsσ hnear
    v hvσ hsv
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hFσ : F.mult σ = 1 := by rw [hF, hσ]; exact Int.ediv_self hm'.ne'
  have hFle : ∀ z, F.mult z ≤ 0 ↔ (pullCart s G - m • K).mult z < m := fun z => by
    rw [hF, ← Int.lt_add_one_iff, zero_add, Int.ediv_lt_iff_lt_mul hm', one_mul]
  have hFnn : ∀ z, 0 ≤ (pullCart s G - m • K).mult z → 0 ≤ F.mult z := fun z hz => by
    rw [hF]; exact Int.ediv_nonneg hz hm'.le
  by_cases hvc : Order.coheight v ≠ 1
  · have : (pullCart s G - m • K).mult v = 0 := by
      by_contra h0
      exact hvc (CartierDiv.coheight_eq_one_of_mult_ne_zero h0)
    rw [this]; exact hm'
  push_neg at hvc
  haveI := hres.smooth
  haveI : Smooth (s ≫ p) := SmoothOfRelativeDimension.smooth n _
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.ModifSections.isNormalScheme_of_smooth (s ≫ p)
  haveI : IsProper (s ≫ p) := ((isProjOver_iff_isProper_and_exists_isAmpleLB (s ≫ p)).1 hres.proj).1
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  haveI : IsProper s := IsProper.of_comp s p
  have hbir := hres.bir
  have hσc : Order.coheight σ = 1 :=
    CartierDiv.coheight_eq_one_of_mult_ne_zero (by rw [hσ]; exact_mod_cast hm.ne')
  obtain ⟨h, hσreg, hreg⟩ := GlobalTheory.T.exists_lifted_function_on_logResolution X p n hp hn η m G N Y s K B F hres hcoh y σ
    (fun v w h1 h2 h3 h4 => (hFle v).2 (hnear v w h1 h2 h3 h4)) hsσ hσc
  obtain ⟨h₀, rfl⟩ := hbir.2 h

  have hη' : EtaleKlt.ratPull p s n η ≠ 0 := fun h0 =>
    hη ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hbir n).1 (h0.trans (map_zero _).symm))

  have hDnn : ∀ (z : X), z ⤳ y → ∀ (E : DivOver p) (E' : DivOver (s ≫ p)), E.IsAt z →
      DivOver.Over s E' E → ∀ w, s w = z → E'.IsAt w → 0 ≤ F.mult w := by
    intro z hz E E' hE hE'E w hwz hw
    subst hwz
    obtain ⟨g, hg⟩ := G.exists_isEqn (s w)
    have hd := hdisc (s w) hz E hE g hg
    have h1 := GlobalTheory.T.discrepancy_formula_divisor ℂ Y (s ≫ p) n (EtaleKlt.ratPull p s n η) hη' K (pullCart s G) m hm
      hres.div E' w (fnPull s g) hw (isEqn_pullCart s hg)
    have h2 : discrep E' (EtaleKlt.ratPull p s n η) m (fnPull s g) = discrep E η m g := by
      unfold discrep
      rw [GlobalTheory.T.form_order_birational_pullback ℂ X Y p s hbir E' E hE'E n η hη, GlobalTheory.T.ord_functionField_pullback_primeDivisor_over ℂ X Y p s hbir E' E hE'E g]
    rw [h2] at h1
    rw [h1] at hd
    have hmq : (0 : ℚ) < m := by exact_mod_cast hm
    have : (0 : ℚ) ≤ ((pullCart s G - m • K).mult w : ℚ) := by
      rw [neg_div, neg_nonpos] at hd
      exact (div_nonneg_iff.1 hd).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hmq))
    exact hFnn w (by exact_mod_cast this)

  have hreg0 : RegAt y h₀ := by
    refine GlobalTheory.T.regular_at_normal_point_of_divisors X p hp y hyint h₀ fun z hz E hE => ?_
    obtain ⟨E', hE'E⟩ := GlobalTheory.T.exists_primeDivisor_over_source_birational ℂ X Y p s hbir E
    obtain ⟨w, hwz, hw⟩ := GlobalTheory.T.divisor_point_proper_lift ℂ X Y p s hbir inferInstance E' E hE'E z hE
    have hFw := hDnn z hz E E' hE hE'E w hwz hw
    have hsw : s w ⤳ y := hwz ▸ hz
    rw [hE'E h₀]
    by_cases hwσ : w = σ
    · subst hwσ
      have := mem_ring_of_regularAt hw hσreg hFw
      simpa using add_mem this (one_mem E'.ring)
    · exact mem_ring_of_regularAt hw (hreg w hwσ hw.coheight_eq_one hsw) hFw

  have hunit0 : UnitAt y h₀ := by
    by_cases hh1 : functionFieldMap s h₀ - 1 = 0
    · have : h₀ = 1 := hbir.1 (by rw [map_one]; exact sub_eq_zero.1 hh1)
      rw [this]; exact unitAt_one y
    have hnu : ¬ UnitAt y (h₀ - 1) := fun hu => by
      have hu' := unitAt_pull (p := p) s hbir hσc hsσ hu
      rw [map_sub, map_one] at hu'
      have := mult_le_ord_of_regularAt hσreg hh1 hσc
      rw [hu'.ord_eq_zero, hFσ] at this
      omega
    obtain ⟨a, ha, e⟩ := zeroAt_iff.2 ⟨hreg0.add ⟨-1, by rw [map_neg, map_one]⟩, by
      rwa [sub_eq_add_neg] at hnu⟩
    have h1a : (1 + a) ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := fun h' => by
      have h1 : (1 : X.presheaf.stalk y) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
        simpa using sub_mem h' ha
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    exact ⟨1 + a, IsLocalRing.notMem_maximalIdeal.1 h1a, by rw [map_add, map_one, e]; ring⟩
  have hu := unitAt_pull (p := p) s hbir hvc hsv hunit0
  have := mult_le_ord_of_regularAt (hreg v hvσ hvc hsv) hu.ne_zero hvc
  rw [hu.ord_eq_zero] at this
  exact (hFle v).1 this

end GlobalTheory.LogResConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleGlobalLiftIdentity
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaIntegralLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem I_om_one (M : Model σ Y W) (om : Rep σ Y W) (Φ : Fn F n d) (k h : UA σ W.J) :
    M.I om (om (1, k) Φ) h = M.I om Φ (h * k) := by
  unfold Model.I theta
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (om (1, k) Φ)) = thetaSum F (om (g, h * k) Φ)
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem I_smul (M : Model σ Y W) (om : Rep σ Y W) (c : ℂ) (Φ : Fn F n d) (h : UA σ W.J) :
    M.I om (c • Φ) h = c * M.I om Φ h := by
  unfold Model.I theta
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (c • Φ)) = c * thetaSum F (om (g, h) Φ)
  rw [map_smul, thetaSum_smul]

theorem I_add (M : Model σ Y W) (om : Rep σ Y W) (hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) (h : UA σ W.J) : M.I om (Φ + Ψ) h = M.I om Φ h + M.I om Ψ h := by
  unfold Model.I
  rw [← integral_add (hconv Φ hΦ h) (hconv Ψ hΨ h)]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (Φ + Ψ)) = thetaSum F (om (g, h) Φ) + thetaSum F (om (g, h) Ψ)
  rw [map_add, thetaSum_add F (hpres _ _ hΦ) (hpres _ _ hΨ)]

theorem snd_eq_zero_of_at {κ : Type} (z : κ → AF F) (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from (0, 1))
  have hu : evI F u = 0 := by
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun (hz u hu) i)
  rwa [one_mul] at h1

theorem exists_deriv (hP : GlobalTheory.FunPr.Hypotheses₂) (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (χY χW : Chr F E) (om : Rep σ Y W)
    (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (hw : M.IsWeil ψ χY χW om) (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ)
    (hcont : ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ h, Continuous fun f : SInf F (Fin n × Fin d) => M.I om (pureA F f φ) h)
    {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ Φ₁ ∈ schA F (Fin n × Fin d), (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) ∧
      ∀ h, HasDerivAt (fun t : ℝ => M.I om Φ (h * γ (Multiplicative.ofAdd t))) (M.I om Φ₁ h) 0 := by
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d) :=
    (GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw).pres
  induction hΦ using Submodule.span_induction with
  | zero =>
    refine ⟨0, Submodule.zero_mem _, fun x => ?_, fun h => ?_⟩
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
    · have e : ∀ h', M.I om 0 h' = 0 := fun h' => by simpa using I_smul M om 0 0 h'
      simpa [e] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add Φ Ψ hΦ hΨ ihΦ ihΨ =>
    obtain ⟨Φ₁, m₁, p₁, q₁⟩ := ihΦ
    obtain ⟨Ψ₁, m₂, p₂, q₂⟩ := ihΨ
    refine ⟨Φ₁ + Ψ₁, Submodule.add_mem _ m₁ m₂, fun x => ?_, fun h => ?_⟩
    · simpa only [map_add, Pi.add_apply] using (p₁ x).fun_add (p₂ x)
    · simpa only [I_add M om hpres hconv hΦ hΨ, I_add M om hpres hconv m₁ m₂] using (q₁ h).fun_add (q₂ h)
  | smul c Φ hΦ ih =>
    obtain ⟨Φ₁, m₁, p₁, q₁⟩ := ih
    refine ⟨c • Φ₁, Submodule.smul_mem _ c m₁, fun x => ?_, fun h => ?_⟩
    · simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using (p₁ x).const_mul c
    · simpa only [I_smul] using (q₁ h).const_mul c
  | mem Φ hΦ =>
    obtain ⟨f, φ, hφ, rfl⟩ := hΦ
    obtain ⟨c, c', h0, hlim, hacts⟩ := GlobalTheory.WeilArchSmooth.exists_orbit hP M ψ χY χW om hcm hψ hw γ hγ f
    have hmem : ∀ u : SInf F (Fin n × Fin d), pureA F u φ ∈ schA F (Fin n × Fin d) :=
      fun u => Submodule.subset_span ⟨u, φ, hφ, rfl⟩
    have hR : Rest (evI F) (⇑f) (fun x : Fin n × Fin d → AF F => φ fun i => (x i).2) := by
      refine ⟨fun x z hz => congrArg φ (funext fun i => ?_), hmem f⟩
      show (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at z hz i, add_zero]
    have hc : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (pureA F f φ) = pureA F (c t) φ := fun t => hacts t _ hR
    refine ⟨pureA F c' φ, hmem c', fun x => ?_, fun h => ?_⟩
    · have ev : Continuous fun s : SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) :=
        (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
          (fun j => evI F (x j))).comp
          (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
      have h2 : HasDerivAt (fun t : ℝ => c t (fun j => evI F (x j)) * φ fun i => (x i).2)
          (c' (fun j => evI F (x j)) * φ fun i => (x i).2) 0 := by
        rw [hasDerivAt_iff_tendsto_slope]
        refine (((ev.tendsto c').comp hlim).mul_const _).congr' (Filter.Eventually.of_forall fun t => ?_)
        rw [slope_def_module, h0]
        simp only [Function.comp_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
        ring
      simp only [hc]
      exact h2
    · let L : SInf F (Fin n × Fin d) →ₗ[ℝ] ℂ :=
        { toFun := fun u => M.I om (pureA F u φ) h
          map_add' := fun u u' => by
            have e : pureA F ⇑(u + u') φ = pureA F u φ + pureA F u' φ := by
              funext x; simp [pureA, add_mul]
            rw [e, I_add M om hpres hconv (hmem u) (hmem u')]
          map_smul' := fun s u => by
            have e : pureA F ⇑(s • u) φ = (s : ℂ) • pureA F u φ := by
              funext x; simp [pureA, mul_assoc, Complex.real_smul]
            rw [e, I_smul, RingHom.id_apply, Complex.real_smul] }
      have hL : Continuous L := hcont φ hφ h
      have hcurve : (fun t : ℝ => M.I om (pureA F f φ) (h * γ (Multiplicative.ofAdd t))) = fun t => L (c t) := by
        funext t
        rw [← I_om_one, hc]
        rfl
      rw [hcurve, hasDerivAt_iff_tendsto_slope]
      refine ((hL.tendsto c').comp hlim).congr' (Filter.Eventually.of_forall fun t => ?_)
      simp only [Function.comp_apply, slope_def_module, h0, sub_zero, map_smul, map_sub]

theorem polData_le_schA {B : Base F E} {M : Model σ Y W} (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ h1 ((h2.and hM.std).mono fun w hw => hw.1.trans hw.2)

end GlobalTheory.ThetaIntegralLine

theorem GlobalTheory.ThetaIntegralLine.hasDerivAt_I_line : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, ∀ Φ₁ ∈ GlobalTheory.ThK.PolData B G.M, (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → ∀ h, HasDerivAt (fun t : ℝ => G.M.I om Φ (h * γ (Multiplicative.ofAdd t))) (G.M.I om Φ₁ h) 0 := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ Φ hΦ Φ₁ _ hd h
  have hT := hM.triple
  have hineq : (a + a') + 2 * min (a - G.p) G.p < 2 * a ∨ min (a - G.p) G.p = 0 := by
    have h1 := hT.geo.eBig
    have h2 := hT.geo.lt
    left
    have := min_le_right (a - G.p) G.p
    omega
  obtain ⟨hc, hcont⟩ := GlobalTheory.T.weil_convergence_of_kernel hK F E σ B _ _ _ _ G.M _ _ om _ _ _ _ (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1 hineq
  obtain ⟨Ψ, -, hΨ, hI⟩ := GlobalTheory.ThetaIntegralLine.exists_deriv hK.base G.M B.ψ _ _ om hT.base.cm hT.base.std hT.weil
    (fun Φ hΦ => (hc Φ hΦ).1) hcont hγ (GlobalTheory.ThetaIntegralLine.polData_le_schA hT.geo.hM hΦ)
  have e : Φ₁ = Ψ := funext fun x => (hd x).unique (hΨ x)
  rw [e]
  exact hI h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurePreservingPtSplit
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

noncomputable def ptEquiv (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) : V d × (J → ℂ) ≃ᵐ V n :=
  ((MeasurableEquiv.prodCongr (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm (MeasurableEquiv.refl (J → ℂ))).trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin d ⊕ J => ℂ).symm).trans
    ((MeasurableEquiv.arrowCongr' ε.symm (MeasurableEquiv.refl ℂ)).trans (MeasurableEquiv.toLp 2 (Fin n → ℂ)))

theorem ptEquiv_apply (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J) (x : V d × (J → ℂ)) :
    ptEquiv n d J ε x = pt ε x.1 x.2 := by
  ext i
  change (Equiv.sumPiEquivProdPi fun _ : Fin d ⊕ J => ℂ).symm (x.1.ofLp, x.2) (ε i) = Sum.elim (fun a => x.1.ofLp a) x.2 (ε i)
  cases ε i <;> rfl

theorem measurePreserving_pt_split : ∀ (n d : ℕ) (J : Type) [Fintype J] (ε : Fin n ≃ Fin d ⊕ J),
    MeasurePreserving (fun x : V d × (J → ℂ) => pt ε x.1 x.2) volume volume ∧
      MeasurableEmbedding (fun x : V d × (J → ℂ) => pt ε x.1 x.2) := by
  intro n d J _ ε
  have e : (fun x : V d × (J → ℂ) => pt ε x.1 x.2) = ⇑(ptEquiv n d J ε) := by
    funext x; exact (ptEquiv_apply n d J ε x).symm
  rw [e]
  refine ⟨?_, (ptEquiv n d J ε).measurableEmbedding⟩
  have h1 : MeasurePreserving (fun z : V d => z.ofLp) volume volume := volume_preserving_ofLp_complex (Fin d)
  have h2 := h1.prod (MeasurePreserving.id (volume : Measure (J → ℂ)))
  have h3 := (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin d ⊕ J => ℂ)).comp h2
  have h4 := (volume_preserving_arrowCongr' ε.symm (MeasurableEquiv.refl ℂ) (MeasurePreserving.id volume)).comp h3
  have h5 : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℂ)) volume volume :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin n → ℂ)).symm (volume_preserving_ofLp_complex (Fin n))
  exact h5.comp h4

end GlobalTheory.FlagCell2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimiserCellFunctionMinFinitelyManyCombinations
section
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

theorem GlobalTheory.Poinc.finite_types : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (N : ℕ) [NeZero N], 3 ≤ N → (∃ ε : Fin 8 → ℤ, Nat.Coprime N (2 * (∑ u, ∑ v, W u v * ε u * ε v).natAbs)) → ∀ r : ℕ, r ≤ g → ∃ (ι : ℕ) (𝓛 : Finset (Finset ((Fin 8 → Fin r → ZMod N) → ℤ))), 1 ≤ ι ∧ ∀ (b : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) → ∀ μ : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ), (∀ c u i, ((μ c u i : ℤ) : ZMod N) = c u i) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b (μ c) ≤ qW W b α) → ∃ L ∈ 𝓛, ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)), (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) → (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ c) ≤ qW W b' α) → (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ c)) ∧ ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ c) := by
  intro g φ hφ W hW N _ hN hε r hr
  classical
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_minimiser_systems_definite_forms_upTo_aut g φ hφ W hW N hN r hr
  have hP : ∀ μ' : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ),
      ((∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) ∧ ∃ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ),
        (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
        (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b₀ (μ' c) ≤ qW W b₀ α)) →
      ∃ (ι : ℕ) (L : Finset ((Fin 8 → Fin r → ZMod N) → ℤ)), 1 ≤ ι ∧ ∀ (b' : LinearMap.BilinForm ℤ (Fin r → ℤ)),
        (∀ x y, b' x y = b' y x) → (∀ x, 0 ≤ b' x x) →
        (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) → qW W b' (μ' c) ≤ qW W b' α) →
        (∀ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' ≤ ∑ c, (ν c : ℝ) * qW W b' (μ' c)) ∧
          ∃ ν ∈ L, (ι * N : ℝ) * φ.evalZ b' = ∑ c, (ν c : ℝ) * qW W b' (μ' c) :=
    fun μ' ⟨h1, b₀, h2, h3, h4⟩ => GlobalTheory.T.polarisationFunction_cell_eq_min_integral_comb g φ hφ W hW N hN hε r hr μ' h1 b₀ h2 h3 h4
  choose! ιf Lf hιf hLf using hP
  set ι : ℕ := ∏ μ' ∈ S, max (ιf μ') 1 with hιdef
  refine ⟨ι, S.biUnion fun μ' => Finset.univ.image fun σ : Equiv.Perm (Fin 8 → Fin r → ZMod N) =>
    (Lf μ').image fun ν c => ((ι / ιf μ' : ℕ) : ℤ) * ν (σ c), ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => by omega)
  intro b hbs hbp μ hμ hmin
  obtain ⟨e, he⟩ := hS b hbs hbp
  obtain ⟨σ, hσ1, hσ2⟩ := GlobalTheory.T.exists_transport_minimisers_latticeAutomorphism W N r μ hμ e
  have hpd : ∀ x, x ≠ 0 → 0 < pull e.toLinearMap b x x := fun x hx => by
    simpa using hbp (e x) (by simpa using hx)
  have hPμ := And.intro hσ1 (⟨pull e.toLinearMap b, fun x y => hbs _ _, hpd, hσ2 b hmin⟩ :
    ∃ b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧
      (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) →
        qW W b₀ ((fun c u => e.symm (μ (σ c) u)) c) ≤ qW W b₀ α))
  have hmem := he _ hσ1 (hσ2 b hmin)
  have hι1 := hιf _ hPμ
  have hL := hLf _ hPμ
  set μ' : (Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ) := fun c u => e.symm (μ (σ c) u) with hμ'
  have hdvd : ιf μ' ∣ ι := by
    have := Finset.dvd_prod_of_mem (fun μ'' => max (ιf μ'') 1) hmem
    simpa [max_eq_left hι1] using this
  set k : ℕ := ι / ιf μ' with hk
  have hkι : (ι : ℝ) = k * ιf μ' := by exact_mod_cast (Nat.div_mul_cancel hdvd).symm
  refine ⟨(Lf μ').image fun ν c => ((k : ℕ) : ℤ) * ν (σ.symm c),
    Finset.mem_biUnion.2 ⟨μ', hmem, Finset.mem_image.2 ⟨σ.symm, Finset.mem_univ _, rfl⟩⟩, ?_⟩
  intro b' hb's hb'p hb'min
  have key := hL (pull e.toLinearMap b') (fun x y => hb's _ _) (fun x => hb'p _) (hσ2 b' hb'min)
  have hφ' : φ.evalZ (pull e.toLinearMap b') = φ.evalZ b' := evalZ_pull φ e.surjective b'
  have hq : ∀ c, qW W (pull e.toLinearMap b') (μ' c) = qW W b' (μ (σ c)) := fun c => by
    simp [qW, μ']
  have hsum : ∀ ν : (Fin 8 → Fin r → ZMod N) → ℤ,
      ∑ c, ((((k : ℕ) : ℤ) * ν (σ.symm c) : ℤ) : ℝ) * qW W b' (μ c) =
        k * ∑ c, (ν c : ℝ) * qW W (pull e.toLinearMap b') (μ' c) := fun ν => by
    rw [Finset.mul_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hq]; simp; ring
  have hlhs : (ι * N : ℝ) * φ.evalZ b' = k * ((ιf μ' * N : ℝ) * φ.evalZ (pull e.toLinearMap b')) := by
    rw [hφ', hkι]; ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨fun ν' hν' => ?_, ?_⟩
  · obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hν'
    rw [hsum, hlhs]
    exact mul_le_mul_of_nonneg_left (key.1 ν hν) hk0
  · obtain ⟨ν, hν, heq⟩ := key.2
    exact ⟨_, Finset.mem_image_of_mem _ hν, by rw [hsum, hlhs, heq]⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchLogNormIntegralIsometrySymmCongr
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem pol_comp_equiv {ι : Type} [Fintype ι] (τ : ι ≃ ι) (φ : (ι → ℤ) → ℝ) :
    FibreProj.pol (fun n => φ (n ∘ τ.symm)) = FibreProj.pol φ := by
  classical
  unfold FibreProj.pol
  refine Fintype.sum_equiv (Equiv.finsetCongr τ) _ _ fun S => ?_
  simp only [Equiv.finsetCongr_apply, Finset.card_map]
  congr 2
  funext j
  simp only [Function.comp_apply, Finset.mem_map_equiv]

theorem mixArch_iso_symm_congr : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → mixArch L M hr = mixArch L' M hr) ∧ (∀ τ : Equiv.Perm (Fin e), mixArch (fun a => L (τ a)) M hr = mixArch L M hr) ∧ ∀ (M' : HermLB q) (r' : M'.B.ι → Y.functionFieldˣ) (hr' : IsRatSec M'.B r'), M'.div hr' = M.div hr → (∀ σ, Set.EqOn (logNorm (M'.φ σ) r') (logNorm (M.φ σ) r) (offSupp q σ (M.div hr))) → mixArch L M' hr' = mixArch L M hr := by
  intro k _ Y _ q e L M r hr
  refine ⟨fun L' hL => ?_, fun τ => ?_, fun M' r' hr' hd hn => ?_⟩
  · have h : ∀ n, (comb L n).archInt M e hr = (comb L' n).archInt M e hr := fun n =>
      by simp only [HermLB.archInt, (isometric_comb_congr hL n).chernInt_eq]
    simp only [mixArch, h]
  · have h : ∀ n, (comb (fun a => L (τ a)) (n ∘ τ)).archInt M e hr = (comb L n).archInt M e hr := fun n => by
      have iso : (comb (fun a => L (τ a)) (n ∘ τ)).Isometric (comb L n) := by
        refine HermLB.icls_eq_iff.1 ?_
        rw [icls_comb, icls_comb]
        exact Fintype.sum_equiv τ _ _ fun a => by simp
      simp only [HermLB.archInt, iso.chernInt_eq]
    simp only [mixArch]
    rw [← pol_comp_equiv τ.symm (fun n => (comb (fun a => L (τ a)) n).archInt M e hr)]
    simp only [Equiv.symm_symm, h]
  · have h : ∀ n, (comb L n).archInt M' e hr' = (comb L n).archInt M e hr := fun n => by
      simp only [HermLB.archInt, hd]
      exact finsum_congr fun σ => Weight.chernInt_congr (isOpen_offSupp _).measurableSet (hn σ)
    simp only [mixArch, h]

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPoints
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem archInt_eq_zero_of_isEmpty {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) (L M : HermLB q) (e : ℕ)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : L.archInt M e hr = 0 := by
  unfold HermLB.archInt
  refine finsum_eq_zero_of_forall_eq_zero fun σ => ?_
  haveI := hq σ
  simp [Weight.chernInt, MeasureTheory.integral_of_isEmpty]

theorem mixArch_eq_zero_of_isEmpty {k : Type} [CommRing k] {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp k}
    (hq : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) {e : ℕ} (L : Fin e → HermLB q) (M : HermLB q)
    {r : M.B.ι → Z.functionFieldˣ} (hr : IsRatSec M.B r) : mixArch L M hr = 0 := by
  unfold mixArch
  simp [archInt_eq_zero_of_isEmpty hq, FibreProj.pol]

theorem mixArch_resArch_eq_zero_of_noCxPts : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), (∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)) → ∀ (e : ℕ) (L : Fin e → HermLB q) (M : HermLB q), (∀ (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), mixArch L M hr = 0) ∧ ∀ (t : M.B.Sec) (z : Y), resArch L M t z = 0 := by
  intro k _ Y _ q hq e L M
  refine ⟨fun r hr => mixArch_eq_zero_of_isEmpty hq L M hr, fun t z => ?_⟩
  unfold resArch
  split_ifs with h
  · refine mixArch_eq_zero_of_isEmpty (fun σ => ?_) _ _ _
    exact (Points.PtsOver.map (cloι z) rfl _ : CxPts (cloι z ≫ q) σ → CxPts q σ).isEmpty
  · rfl

end GlobalTheory.MixHt
end

