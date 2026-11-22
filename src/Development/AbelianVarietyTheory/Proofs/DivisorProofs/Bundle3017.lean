import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2912
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2537
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1169
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0189
import ReciprocityTheory.GaloisValuations.Global
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0255
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TxFrameTranslate
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResidueDominantCartier
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair.AdjUp

theorem regAt_map {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    (z : Y) {f : X.functionField} (h : RegAt (s z) f) : RegAt z (functionFieldMap s f) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨s.stalkMap z a, (functionFieldMap_algebraMap s z a).symm⟩

theorem scheme_ord_zero {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y] (z : Y) :
    Scheme.ord (0 : Y.functionField) z = 0 := by
  unfold Scheme.ord
  split_ifs <;> simp

theorem place_ord_eq {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]
    {q : Y ⟶ Sp k} {E : DivOver q} {z : Y} (h : E.IsAt z) (f : Y.functionField) :
    (placeEquiv q E).ord f = Scheme.ord f z := by
  by_cases hf : f = 0
  · subst hf
    rw [scheme_ord_zero]
    simp [Place.ord]
  · exact h.ord_eq (Units.mk0 f hf)

theorem ring_eq_of_isAt {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}
    {E F : DivOver q} {z : Y} (hE : E.IsAt z) (hF : F.IsAt z) :
    (placeEquiv q E).ring = (placeEquiv q F).ring :=
  SetLike.ext fun f => (hE f).trans (hF f).symm

def stalkEquiv {Y : Scheme.{0}} [IsIntegral Y] (w : Y) : Y.presheaf.stalk w ≃+* locRing w :=
  RingEquiv.ofBijective (algebraMap (Y.presheaf.stalk w) Y.functionField).rangeRestrict
    ⟨fun _ _ e => IsFractionRing.injective _ Y.functionField (congrArg Subtype.val e),
      RingHom.rangeRestrict_surjective _⟩

theorem stalkEquiv_apply {Y : Scheme.{0}} [IsIntegral Y] (w : Y) (a : Y.presheaf.stalk w) :
    ((stalkEquiv w a : locRing w) : Y.functionField) = algebraMap _ Y.functionField a := rfl

theorem map_maximalIdeal_equiv {R R' : Type*} [CommRing R] [CommRing R'] [IsLocalRing R]
    [IsLocalRing R'] (φ : R ≃+* R') :
    (IsLocalRing.maximalIdeal R).map φ = IsLocalRing.maximalIdeal R' := by
  ext a
  rw [Ideal.mem_map_of_equiv, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · rintro ⟨b, hb, rfl⟩ h
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb
    exact hb ((isUnit_map_iff φ b).1 h)
  · intro ha
    refine ⟨φ.symm a, ?_, by simp⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro h
    exact ha (by simpa using h.map φ)

end GlobalTheory.FieldPair.AdjUp

open GlobalTheory.FieldPair.AdjUp in

theorem GlobalTheory.FieldPair.mult_lt_of_adjKlt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (x : Fin n → X.functionField) (m : ℕ) (g : X.functionFieldˣ) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (y : X) (σ : Y) (S : DivOver p) (S' : DivOver (s ≫ p)), TrBasis (Cartier.constFn p) x → 0 < m → IsLogRes p n (dForm (Cartier.constFn p) x) m (CartierDiv.principal g) s K B → DivOver.Over s S' S → S'.IsAt σ → (pullCart s (CartierDiv.principal g) - m • K).mult σ = m → AdjKlt (Cartier.constFn p) n (locRing y) (placeEquiv p S) (dForm (Cartier.constFn p) x) (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) → ∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s (CartierDiv.principal g) - m • K).mult v < m := by
  intro X _ _ p n _ _ x m g Y _ _ s _ K B y σ S S' hx hm hres hover hσ hmσ hadj v w hvσ hvw hσw hwy
  by_cases hv0 : (pullCart s (CartierDiv.principal g) - m • K).mult v ≤ 0
  · exact lt_of_le_of_lt hv0 (by exact_mod_cast hm)
  have hv0' : (pullCart s (CartierDiv.principal g) - m • K).mult v ≠ 0 := by omega
  haveI := hres.smooth
  haveI := SmoothOfRelativeDimension.smooth n (s ≫ p)
  haveI : GlobalTheory.IsNormalScheme Y := Discrepancy.CanonIso.isNormalScheme_of_smooth' (s ≫ p)
  have hmσ0 : (pullCart s (CartierDiv.principal g) - m • K).mult σ ≠ 0 := by
    rw [hmσ]; exact_mod_cast hm.ne'
  have hvB : v ∈ B := hres.supp (CartierDiv.mem_supp_of_mult_ne_zero hv0')
  have hσB : σ ∈ B := hres.supp (CartierDiv.mem_supp_of_mult_ne_zero hmσ0)
  have hv1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hv0'
  have hσ1 := hσ.coheight_eq_one
  obtain ⟨w', t, u, hw'w, hvw', hσw', hdim, hspan, htσ, huv, hB⟩ :=
    GlobalTheory.SncMeet.exists_meet_point Y (s ≫ p) n B hres.snc v σ w hvB hσB hv1 hσ1 hvσ hvw hσw
  obtain ⟨Ev, hEv⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := s ≫ p) hv1
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap s) hres.bir
  have hc : ∀ a, e (Cartier.constFn p a) = Cartier.constFn (s ≫ p) a := fun a =>
    RingHom.congr_fun (EtaleKlt.functionFieldMap_comp_constFn p s) a
  have hadj' := GlobalTheory.FieldPair.adjKlt_ringEquiv (Cartier.constFn p) (Cartier.constFn (s ≫ p)) e hc n x (locRing y)
    (Finsupp.single (g : X.functionField) (1 / (m : ℚ))) (placeEquiv p S) (placeEquiv (s ≫ p) S') hx
    (fun a => (hover a).symm) hadj
  rw [Finsupp.mapDomain_single] at hadj'
  have hη : dForm (Cartier.constFn (s ≫ p)) (e ∘ x) =
      EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x) := by
    rw [EtaleKlt.ratPull, formMap_dForm]
    rfl
  have hη0 : EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x) ≠ 0 := fun h0 =>
    hadj.form_ne_zero ((EtaleKlt.ratPull_bijective_of_birational ℂ X Y p s hres.bir n).1
      (h0.trans (map_zero _).symm))
  rw [hη] at hadj'
  unfold AdjKlt at hadj'
  have hdisc : ∀ (P : DivOver (s ≫ p)) (z : Y), P.IsAt z →
      (placeEquiv (s ≫ p) P).disc (EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x))
        (Finsupp.single (e g) (1 / (m : ℚ))) =
        -((pullCart s (CartierDiv.principal g) - m • K).mult z : ℚ) / m := by
    intro P z hP
    have h1 := disc_placeEquiv P (EtaleKlt.ratPull p s n (dForm (Cartier.constFn p) x)) m (fnPull s g)
    exact h1.trans (discrep_isAt_eq_neg_mult ℂ Y (s ≫ p) n _ hη0 K _ m hm hres.div P z (fnPull s g) hP
      (isEqn_pullCart s (CartierDiv.isEqn_principal g (s z))))
  have hTQ : (locRing y).map e.toRingHom ≤ locRing w' := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : s w' ⤳ y := (hw'w.map s.continuous).trans hwy
    exact regAt_map s w' (regAt_of_specializes h1 ha)
  have hQ := isLocModel_locRing (p := s ≫ p) w'
  have key := hadj'.2.2 (locRing w') hQ (stalkEquiv w' t) (stalkEquiv w' u) (placeEquiv (s ≫ p) Ev) hTQ
    ?_ ?_ ((isPrimeOf_placeEquiv S' w').2 ⟨σ, hσw', hσ⟩) ((isPrimeOf_placeEquiv Ev w').2 ⟨v, hvw', hEv⟩)
    (by rw [stalkEquiv_apply, place_ord_eq hσ]; exact htσ)
    (by rw [stalkEquiv_apply, place_ord_eq hEv]; exact huv) ?_
  · rw [hdisc Ev v hEv] at key
    have hm' : (0 : ℚ) < m := by exact_mod_cast hm
    rw [lt_div_iff₀ hm'] at key
    have : ((pullCart s (CartierDiv.principal g) - m • K).mult v : ℚ) < m := by linarith
    exact_mod_cast this
  · have h1 : Ideal.span {stalkEquiv w' t, stalkEquiv w' u} = (Ideal.span {t, u}).map (stalkEquiv w') := by
      rw [Ideal.map_span]; simp [Set.image_insert_eq]
    rw [h1, hspan]
    haveI := hQ.isLocalRing
    exact map_maximalIdeal_equiv _
  · exact (ringKrullDim_eq_of_ringEquiv (stalkEquiv w')).symm.trans hdim
  · intro P hP h1 h2
    obtain ⟨P₀, rfl⟩ := (placeEquiv (s ≫ p)).surjective P
    obtain ⟨z, hzw', hz⟩ := (isPrimeOf_placeEquiv P₀ w').1 hP
    rw [hdisc P₀ z hz]
    have hz1 := hz.coheight_eq_one
    have hzσ : z ≠ σ := by rintro rfl; exact h1 (ring_eq_of_isAt hz hσ)
    have hzv : z ≠ v := by rintro rfl; exact h2 (ring_eq_of_isAt hz hEv)
    have hzB : z ∉ B := fun hzB => (hB z hzB hz1 hzw').elim hzv hzσ
    have h0 : (pullCart s (CartierDiv.principal g) - m • K).mult z = 0 := by
      by_contra h0
      exact hzB (hres.supp (CartierDiv.mem_supp_of_mult_ne_zero h0))
    rw [h0]
    simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MdbarZeroOfHolo
section
set_option autoImplicit false

noncomputable section

open Filter Topology Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.HermFrame
open scoped Matrix ContDiff

namespace GlobalTheory.ChernCalc.FrameChange

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
variable {r : Type*} [Fintype r] [DecidableEq r] {H A B : E → Matrix r r ℂ} {z : E}

theorem conn_mul_mul (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 1 A z) (hAu : IsUnit (A z).det) (hB : MContDiffAt 1 B z) (hBu : IsUnit (B z).det)
    (hB0 : ∀ η, mdbar B z η = 0) (ξ : E) :
    conn (fun x => A x * H x * (B x)ᴴ) z ξ = (A z)ᵀ⁻¹ * (conn H z ξ * (A z)ᵀ + (mdel A z ξ)ᵀ) := by
  refine (eq_conn_of_compatible ?_ ?_).symm
  · simp only [det_mul, det_conjTranspose]
    exact (hAu.mul hu).mul hBu.star
  · rw [mdel_mul (hA.mul h) hB.conjTranspose, mdel_mul hA h, mdel_conjTranspose, hB0, ← conn_transpose_mul hu,
      transpose_mul, transpose_nonsing_inv]
    simp only [Matrix.mul_assoc, nonsing_inv_mul_cancel_left _ _ hAu, transpose_add, transpose_mul, Matrix.add_mul,
      conjTranspose_zero, transpose_transpose, Matrix.mul_zero, zero_add]

theorem curv_mul_mul (h : MContDiffAt 2 H z) (hu : IsUnit (H z).det)
    (hA : MContDiffAt 2 A z) (hAu : IsUnit (A z).det) (hA0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar A x η = 0)
    (hB : MContDiffAt 2 B z) (hBu : IsUnit (B z).det) (hB0 : ∀ᶠ x in 𝓝 z, ∀ η, mdbar B x η = 0) (ξ η : E) :
    curv (fun x => A x * H x * (B x)ᴴ) z ξ η = (A z)ᵀ⁻¹ * curv H z ξ η * (A z)ᵀ := by
  have he : (fun x => conn (fun x => A x * H x * (B x)ᴴ) x ξ) =ᶠ[𝓝 z]
      fun x => (A x)ᵀ⁻¹ * (conn H x ξ * (A x)ᵀ + (mdel A x ξ)ᵀ) := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu, hA.eventually_two,
      hA.eventually_isUnit hAu, hB.eventually_two, hB.eventually_isUnit hBu, hB0] with x h1 h2 h3 h4 h5 h6 h7
    exact conn_mul_mul (h1.of_le one_le_two) h2 (h3.of_le one_le_two) h4 (h5.of_le one_le_two) h6 h7 ξ
  have hA1 : MContDiffAt 1 (fun x => (A x)ᵀ) z := (hA.of_le one_le_two).transpose
  have hAu' : IsUnit (A z)ᵀ.det := by rwa [det_transpose]
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have hd : MContDiffAt 1 (fun x => (mdel A x ξ)ᵀ) z := (hA.mdel (by norm_num) ξ).transpose
  have h0 : mddbar A z ξ η = 0 := by
    rw [← mdel_mdbar hA, mdel_congr (B := fun _ => 0) (hA0.mono fun x hx => hx η), mdel_const]
  rw [curv, mdbar_congr he, mdbar_mul (hA1.inv hAu') ((hc.mul hA1).add hd), mdbar_inv hA1 hAu',
    mdbar_add (hc.mul hA1) hd, mdbar_mul hc hA1, mdbar_transpose (fun x => mdel A x ξ), mdbar_mdel hA, h0,
    mdbar_transpose A, hA0.self_of_nhds, curv]
  simp [Matrix.mul_assoc]

end General

variable {n : ℕ} {r : Type} [Fintype r] {T : V n → Matrix r r ℂ} {v : V n}

omit [Fintype r] in

theorem two_of_holo (h : ∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) : MContDiffAt 2 T v :=
  fun a b => ((SCV.analyticAt_iff_eventually_differentiableAt.2 (h a b)).contDiffAt).restrict_scalars ℝ

theorem mdbar_zero_of_holo (h : ∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) :
    ∀ᶠ x in 𝓝 v, ∀ η, mdbar T x η = 0 :=
  (eventually_all.2 fun a => eventually_all.2 fun b => h a b).mono fun x hx η => by
    ext a b
    rw [mdbar_apply, dbar_eq_zero (hx a b)]
    rfl

theorem conn_curv_frame : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G₂ T K : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) → IsUnit (T v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K u a b) x) → IsUnit (K v).det → (∀ᶠ x in 𝓝 v, G₂ x = T x * G x * (K x)ᴴ) → (∀ ξ, conn G₂ v ξ = (T v)ᵀ⁻¹ * (conn G v ξ * (T v)ᵀ + (mdel T v ξ)ᵀ)) ∧ ∀ ξ η, curv G₂ v ξ η = (T v)ᵀ⁻¹ * curv G v ξ η * (T v)ᵀ := by
  intro n r _ _ G G₂ T K v hG hGu hT hTu hK hKu he
  have hG2 : MContDiffAt 2 G v := hG.of_le (by norm_cast)
  refine ⟨fun ξ => ?_, fun ξ η => ?_⟩
  · rw [conn_congr he]
    exact conn_mul_mul (hG2.of_le one_le_two) hGu ((two_of_holo hT).of_le one_le_two) hTu
      ((two_of_holo hK).of_le one_le_two) hKu (mdbar_zero_of_holo hK).self_of_nhds ξ
  · rw [curv_congr he]
    exact curv_mul_mul hG2 hGu (two_of_holo hT) hTu (mdbar_zero_of_holo hT) (two_of_holo hK) hKu
      (mdbar_zero_of_holo hK) ξ η

end GlobalTheory.ChernCalc.FrameChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDecompositionSubgroupIff
section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual
open scoped Pointwise

namespace GlobalTheory.QuadSplit

theorem mem_decompositionSubgroup_iff' {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : ValuationSubring Ω)
    (g : Ω ≃ₐ[K] Ω) : g ∈ A.decompositionSubgroup K ↔ ∀ x, g x ∈ A ↔ x ∈ A := by
  rw [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h x
    rw [← ValuationSubring.smul_mem_pointwise_smul_iff (g := g) (S := A) (x := x), h]
    rfl
  · intro h
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h]
    simp [AlgEquiv.smul_def]

end GlobalTheory.QuadSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMapFibreDivisibilityIdealCompletionLimitStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_map_fibreDivisibilityIdeal_completion_limit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z) (hπ : M₁.IsHom M (AlgHom.id o Ω) π), IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (D : EffCartierData M.Z) (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ (F : AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a : ℕ → M₁.O z), (∀ n, F - algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a n) ∈ (maximalIdeal (M₁.O z)).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) ^ n) → (∀ x' : M.Z, π x' = z → IsClosed ({x'} : Set M.Z) → ∀ f', EqAt M D x' f' → ∀ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∃ c d : M.O x', (a n : Ω) = c * f' + d ∧ d ∈ maximalIdeal (M.O x') ^ e) → F ∈ (GlobalTheory.FibreCorr.fibreIdeal hπ D z).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) := by
  first | exact @GlobalTheory.FormalCorr.mem_map_fibreIdeal | exact GlobalTheory.FormalCorr.mem_map_fibreIdeal | (intros; apply GlobalTheory.FormalCorr.mem_map_fibreIdeal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.GroupBplus

namespace GlobalTheory.BplusDescent

variable {X : Scheme.{0}} [IsIntegral X]

def ringOver (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) : Subring U.Bp :=
  K'.toSubalgebra.toSubring.comap (algebraMap U.Bp (Kbar X))

theorem mem_ringOver {K' : IntermediateField X.functionField (Kbar X)} {U : AffOp X} {x : U.Bp} :
    x ∈ ringOver K' U ↔ (x : Kbar X) ∈ K' := Iff.rfl

def descMod (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) {h : ℕ}
    (L : Submodule U.Bp (Fin h → U.Bp)) : Submodule (ringOver K' U) (Fin h → ringOver K' U) where
  carrier := {a | (fun i => (a i : U.Bp)) ∈ L}
  add_mem' {a b} ha hb := by
    have : (fun i => ((a + b) i : U.Bp)) = (fun i => (a i : U.Bp)) + fun i => (b i : U.Bp) := by
      funext i; simp
    change (fun i => ((a + b) i : U.Bp)) ∈ L
    rw [this]; exact L.add_mem ha hb
  zero_mem' := by
    have : (fun i => ((0 : Fin h → ringOver K' U) i : U.Bp)) = 0 := by funext i; simp
    change (fun i => ((0 : Fin h → ringOver K' U) i : U.Bp)) ∈ L
    rw [this]; exact L.zero_mem
  smul_mem' c a ha := by
    have : (fun i => ((c • a) i : U.Bp)) = (c : U.Bp) • fun i => (a i : U.Bp) := by
      funext i; simp
    change (fun i => ((c • a) i : U.Bp)) ∈ L
    rw [this]; exact L.smul_mem (c : U.Bp) ha

theorem mem_descMod {K' : IntermediateField X.functionField (Kbar X)} {U : AffOp X} {h : ℕ}
    {L : Submodule U.Bp (Fin h → U.Bp)} {a : Fin h → ringOver K' U} :
    a ∈ descMod K' U L ↔ (fun i => (a i : U.Bp)) ∈ L := Iff.rfl

def IsDescended (K' : IntermediateField X.functionField (Kbar X)) (U : AffOp X) {h : ℕ}
    (L : Submodule U.Bp (Fin h → U.Bp)) : Prop :=
  Module.Finite (ringOver K' U) (descMod K' U L) ∧ Module.Projective (ringOver K' U) (descMod K' U L) ∧
    L = Submodule.span U.Bp {x | ∃ a ∈ descMod K' U L, x = fun i => (a i : U.Bp)}

end GlobalTheory.BplusDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSectionBallOfMulSmallSectionPowTwistStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_sectionBall_of_mul_smallSection_pow_twist : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (c : ℕ), GenAt P c → ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N (-c) → f * s ^ m ∈ P.Bl N (m - c) 2 → f ∈ P.Bl N (-c) (Real.exp (δ * N + C * m + C)) := by
  first | exact @GlobalTheory.HSNef.MpDivTwist.mem_Bl_of_mul_pow_twist | exact GlobalTheory.HSNef.MpDivTwist.mem_Bl_of_mul_pow_twist | (intros; apply GlobalTheory.HSNef.MpDivTwist.mem_Bl_of_mul_pow_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberTorsionPointsAdditiveLabelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberTorsionPoints_additive_label : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → ∀ (a τ : X₁.S.Gam) (xτ : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), xτ.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left → x (a + τ) = x a * xτ := by
  first | exact @GlobalTheory.Poinc.PtAdd.x_add | exact GlobalTheory.Poinc.PtAdd.x_add | (intros; apply GlobalTheory.Poinc.PtAdd.x_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedModelVacuumEqSmulIntegralMatrixIndicatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModel_vacuum_eq_smul_integralMatrix_indicator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X → ∀ w ∈ locPl G t, ∀ ι : ToB G t i j w, IsMixModelB W B t e Γ w ι →
      ι (Γ.M'.vac _) = ι (Γ.M'.vac _) 0 • Set.indicator {Z | ∀ r s, Z r s ∈ (ValuativeRel.valuation (Kw w)).integer} 1 := by
  first | exact @GlobalTheory.TopFlip.MixVacSmall.mixVac_eq_indicator | exact GlobalTheory.TopFlip.MixVacSmall.mixVac_eq_indicator | (intros; apply GlobalTheory.TopFlip.MixVacSmall.mixVac_eq_indicator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSectionValueProductExpansionTerms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange GlobalTheory.Mum.Two.Mix
namespace GlobalTheory.Mum.Two.Mix
open GlobalTheory.UT.MixedConv

theorem val_mixed_eval : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (b : D₁.P.A ⟶ D₂.P.A) (h : D₂.X →+ D₁.X) (g : GtPtF D₁ F) (g' : GtPtF D₂ F), Act D₁ D₂ b h g g' → ∀ (j j' : ℕ) (w : Frm D₂ F j g'.b) (w' : Frm D₁ F j' g.b) (χ : D₂.X) (δ : D₁.X) (u : LB.Gen (CmpLB D₁ D₂ b (h χ) χ)), Nrm u → ∀ (f : D₂.SecB j χ) (f' : D₁.SecB j' δ) (y y' : F), MixedConv.IsCoefB j g' w χ f y → MixedConv.IsCoefB j' g w' δ f' y' → ∀ (z : (TF (R := R) F).left) (J), Good (JN D₁ D₂) z J → sval f (g.b.left ≫ b.left) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J * val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J)).val = cst F z (y * y') * (rigV D₂ (TF (R := R) F).hom z (rr J) ^ j * rigV D₁ (TF (R := R) F).hom z (rl J) ^ j' * (val (g.s (h χ + δ)) (𝟙 _) z (rl J) * (val w (𝟙 _) z (rr J) * val w' (𝟙 _) z (rl J)))⁻¹).val := by
  intro R _ _ D₁ D₂ F _ _ b h g g' hg j j' w w' χ δ u hu f f' y y' hy hy' z J hJ
  have h₁ : Good D₁.P.L z (rl J) := (isPart_inl D₁.P.L D₂.P.L).good hJ
  have h₂ : Good D₂.P.L z (rr J) := (isPart_inr D₁.P.L D₂.P.L).good hJ
  have c₂ : val (MixedConv.cubB D₁ (h χ) δ) g.b.left z (rl J) =
      th D₁ z (rl J) (cP D₁ _ (h χ)) (cP D₁ _ δ) g.b := by
    refine (val_cub D₁.cub g.b h₁ _ _ _).trans ?_
    rw [comp_cP, comp_cP, Category.comp_id]
  have c₃ := gt_mul (𝟙 (TF (R := R) F)) h₁ g (h χ) δ
  have c₄ := hy z (rr J) h₂
  have c₅ := hy' z (rl J) h₁
  have c₆ : g.b.left ≫ b.left = g'.b.left := (congrArg (fun q => q.left) hg.1).symm
  have c₉ := hg.2 χ u hu z J hJ
  rw [Category.id_comp, Over.id_left] at c₃
  rw [c₉, CoefBasic.cst_eq] at c₄
  rw [CoefBasic.cst_eq] at c₅
  rw [c₂, c₆, CoefBasic.cst_eq, map_mul, eq_comm, Units.val_mul, ← _root_.mul_assoc, Units.mul_inv_eq_iff_eq_mul]
  have c₇ := congrArg Units.val c₃
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c₄ c₅ c₇ ⊢
  have c₈ := congrArg₂ (· * ·) c₄ c₅
  linear_combination c₈ - sval f (Over.Hom.left g'.b) z (rr J) * sval f' g.b.left z (rl J) * (val u g.b.left z J).val *
    (val w (𝟙 _) z (rr J)).val * (val w' (𝟙 _) z (rl J)).val * c₇

end GlobalTheory.Mum.Two.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialsDifferByUnitsPositiveBoundaryCombinatioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (r m N n : ℕ), 1 ≤ n → ∀ (ε : (Fin m ⊕ Fin N) → LinearMap.BilinForm ℤ (Fin r → ℤ)) (s₁ s₂ : (Fin m ⊕ Fin N) → V) (ga : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ)), (∀ k, s₁ (.inl k) ∈ maximalIdeal V ∧ s₁ (.inl k) ≠ 0) → (∀ k, IsUnit (s₁ (.inr k))) → (∀ k, s₂ (.inl k) ∈ maximalIdeal V ∧ s₂ (.inl k) ≠ 0) → (∀ k, IsUnit (s₂ (.inr k))) → (∀ a b, ∃ u : Vˣ, ∏ i, algebraMap V (FractionRing V) (s₂ i) ^ ((n : ℤ) * ε i (ga a) (ga b)) = algebraMap V (FractionRing V) u * ∏ i, algebraMap V (FractionRing V) (s₁ i) ^ ((n : ℤ) * ε i (a) (b))) → ∃ c₁ c₂ : Fin m → ℕ, (∀ k, 0 < c₁ k) ∧ (∀ k, 0 < c₂ k) ∧ ∑ k, c₁ k • ε (.inl k) = ∑ k, c₂ k • pull ga.toLinearMap (ε (.inl k)) := by
  first | exact @GlobalTheory.TInj.coneval | exact GlobalTheory.TInj.coneval | (intros; apply GlobalTheory.TInj.coneval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPullOfRigOfSym
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymMulPull

open GlobalTheory.MulPull

section Base

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem hasGen_theta (hC : GlobalTheory.Published.CubeTheorem) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) :
    HasGen L (thφ A (x3 A)) thε := by
  have := hA.comm
  obtain ⟨t, ht⟩ := hC S A hA L hL _ (x3 A 0) (x3 A 1) (x3 A 2)
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := thφ A (x3 A)) (ε' := thε) (fun U _ h => by
    have e := prod_cub (x3 A 0) (x3 A 1) (x3 A 2) h
    have i : lift (x3 A 0) (lift (x3 A 1) (x3 A 2)) = 𝟙 _ := by ext <;> simp [x3]
    rw [i] at e
    simp only [Over.id_left, Category.id_comp] at e
    rw [e, Fin.prod_univ_eight]
    simp only [Matrix.cons_val, zpow_one, zpow_neg]) t ht
  exact ⟨t', ht'⟩

end Base

end GlobalTheory.SymMulPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultilinearQuadraticIsHomogeneous
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem multilinear_quadratic_isHomogeneous : ∀ (P : Type) [AddCommGroup P] (g n : ℕ) (M : MultilinearMap ℤ (fun _ : Fin g => P) ℤ) (a : Fin n → Fin n → P), ∃ F : MvPolynomial (Fin n) ℤ, F.IsHomogeneous (2 * g) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval m F = M (fun _ => ∑ i, ∑ j, (m i * m j) • a i j) := by
  intro P _ g n M a
  refine ⟨∑ r : Fin g → Fin n × Fin n, MvPolynomial.C (M (fun k => a (r k).1 (r k).2)) *
      ∏ k, (MvPolynomial.X (r k).1 * MvPolynomial.X (r k).2), ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro r _
    have hX : ∀ k, (MvPolynomial.X (R := ℤ) (r k).1 * MvPolynomial.X (r k).2).IsHomogeneous 2 :=
      fun k => (MvPolynomial.isHomogeneous_X ℤ _).mul (MvPolynomial.isHomogeneous_X ℤ _)
    have h := (MvPolynomial.isHomogeneous_C (Fin n) (M fun k => a (r k).1 (r k).2)).mul
      (MvPolynomial.IsHomogeneous.prod Finset.univ _ (fun _ => 2) (fun k _ => hX k))
    convert h using 1
    simp [mul_comm]
  · intro m
    have hx : (fun _ : Fin g => ∑ i, ∑ j, (m i * m j) • a i j) =
        fun _ => ∑ p : Fin n × Fin n, (m p.1 * m p.2) • a p.1 p.2 := by
      funext _; exact (Fintype.sum_prod_type' (fun i j => (m i * m j) • a i j)).symm
    rw [hx, MultilinearMap.map_sum]
    simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [MultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]

end GlobalTheory
end

