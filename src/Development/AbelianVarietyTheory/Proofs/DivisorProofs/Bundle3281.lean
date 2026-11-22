import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1353
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0081
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFunctionalChernIntegral
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm.GeoInt

open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.HermFrame (ddc kappa)
open GlobalTheory.GoodMetric (coordVec)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem c1F_comb (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) :
    c1F hX σ (comb L n) = ∑ i, n i • c1F hX σ (L i) := by
  have B := (GlobalTheory.T.firstChern_form_properties k X p D hX σ).1
  let f : HermLB.IsomClass p →+ ((hX.atlas σ).Pt → Ev D) :=
    AddMonoidHom.mk' (Quotient.lift (s := HermLB.isometrySetoid p) (fun L => c1F hX σ L)
      (fun L M h => (B L M).2.2.2.2.2 h)) (by
        intro a b
        induction a using Quotient.inductionOn with | h L => ?_
        induction b using Quotient.inductionOn with | h M => ?_
        exact (B L M).2.2.2.1)
  have hf : ∀ M : HermLB p, f M.icls = c1F hX σ M := fun _ => rfl
  rw [← hf, icls_comb, map_sum]
  simp only [map_zsmul, hf]

theorem dens_pow_sum (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ) :
    dens (((∑ a, ∑ b, H a b • sym (a, b) : Ev n) ^ n : Ev n) : Alt n) =
      (n.factorial : ℂ) * H.det / (Complex.I / 2) ^ n := GlobalTheory.T.top_power_hermitian_form_density n H

theorem ddc_coordVec (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) (a b : Fin n) :
    ddc u v (coordVec a) (coordVec b) = kappa * cHess n (fun w => (u w : ℂ)) v a b := by
  rw [GlobalTheory.HermFrame.ddc, GlobalTheory.leviForm, GlobalTheory.ddbar_eq_del_dbar (contDiffAt_ofReal_comp hu)]
  congr 1
  have hg : (fun x => GlobalTheory.dbar (fun w => (u w : ℂ)) x (coordVec b)) =
      ReciprocityTheory.L2DbarEstimates.wdb n b (fun w => (u w : ℂ)) := by
    funext x
    simp only [GlobalTheory.dbar, GlobalTheory.antilinPart, ReciprocityTheory.L2DbarEstimates.wdb, ReciprocityTheory.L2DbarEstimates.bas,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    ring
  rw [hg]
  simp only [GlobalTheory.del, GlobalTheory.linPart, cHess, Matrix.of_apply, ReciprocityTheory.L2DbarEstimates.wd, ReciprocityTheory.L2DbarEstimates.bas,
    ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
  ring

theorem dens_ofValues_ddc_pow (n : ℕ) (u : V n → ℝ) (v : V n) (hu : ContDiffAt ℝ 2 u v) :
    (dens ((ofValues (ddc u v) ^ n : Ev n) : Alt n)).re =
      n.factorial / Real.pi ^ n * (cHess n (fun w => (u w : ℂ)) v).det.re := by
  have e : ofValues (ddc u v) = ∑ a, ∑ b, (kappa • cHess n (fun w => (u w : ℂ)) v) a b • sym (a, b) := by
    simp only [ofValues, ddc_coordVec n u v hu, Matrix.smul_apply, smul_eq_mul]
  rw [e, dens_pow_sum, Matrix.det_smul, Fintype.card_fin]
  have hk : kappa = Complex.I / 2 * ((Real.pi : ℂ)⁻¹) := by
    rw [GlobalTheory.HermFrame.kappa]; field_simp
  have h2 : (Complex.I / 2) ^ n ≠ 0 := pow_ne_zero _ (by simp)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hk, show ∀ d : ℂ, (n.factorial : ℂ) * ((Complex.I / 2 * ((Real.pi : ℂ))⁻¹) ^ n * d) / (Complex.I / 2) ^ n =
      (((n.factorial / Real.pi ^ n : ℝ)) : ℂ) * d from fun d => by
    rw [mul_pow]; field_simp; push_cast; ring, Complex.re_ofReal_mul]

theorem evalF_lin_pow (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ)
    (x : (hX.atlas σ).Pt) :
    evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D) x =
      ((c1F hX σ (comb L n) x ^ D : Ev D) : Alt D) := by
  rw [c1F_comb]
  simp only [evalF, fld, lin, map_pow, map_sum, map_mul, MvPolynomial.map_C,
    MvPolynomial.map_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Finset.sum_apply, Pi.smul_apply]
  congr 2

theorem dens_loc_eq (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ)
    (c : AlgChart p σ D) (y : CxPts p σ) (hy : y ∈ c.e.source) :
    (dens ((hX.atlas σ).loc (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) c (c.e y))).re =
      c.chernDens ((comb L n).φ σ) y := by
  have e := (hX.atlas σ).loc_crd (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D))
    (⟨(c, y), hy⟩ : (hX.atlas σ).Pt)
  erw [e, evalF_lin_pow]
  have hs := ((comb L n).cInf σ).contDiffAt c hy (mem_pick ((comb L n).φ σ).isLB y)
  erw [c1F, dens_ofValues_ddc_pow D _ _ hs]
  rfl

theorem part_eq_chernPart (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ)
    (ε : ℤˣ) :
    (hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε =
      ((comb L n).φ σ).chernPart D ε := by
  unfold HolAtlas.part Weight.chernPart ChartGlue.glueMeas
  refine iSup_congr fun c => ?_
  unfold ChartGlue.chartMeas
  congr 1
  refine withDensity_congr_ae (ae_restrict_of_forall_mem c.e.open_target.measurableSet fun v hv => ?_)
  have hy := c.e.map_target hv
  simp only [Function.comp_apply]
  erw [dens_loc_eq hX σ L n c _ hy]

theorem integral_eq_chernInt (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) :
    (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) =
      ((comb L n).φ σ).chernInt D Set.univ (fun _ => 1) := by
  simp only [HolAtlas.integral, Weight.chernInt, part_eq_chernPart, Measure.restrict_univ, integral_const,
    smul_eq_mul, mul_one]

theorem mem_span_pow_lin {ι : Type} [Fintype ι] (d : ℕ) (F : MvPolynomial ι ℝ) (hF : F.IsHomogeneous d) :
    F ∈ Submodule.span ℝ (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d) := by
  by_contra hnot
  obtain ⟨φ, hφF, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hkill : ∀ n : ι → ℤ, φ (lin (fun i => (n i : ℝ)) ^ d) = 0 := by
    intro n
    have hm : lin (fun i => (n i : ℝ)) ^ d ∈ Submodule.span ℝ
        (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d) := Submodule.subset_span ⟨n, rfl⟩
    have h2 : φ (lin (fun i => (n i : ℝ)) ^ d) ∈ (Submodule.span ℝ
        (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d)).map φ := Submodule.mem_map_of_mem hm
    rw [hφ] at h2
    exact (Submodule.mem_bot ℝ).mp h2
  have hP : PowLinSpan.polOf φ d = 0 := by
    refine eq_zero_of_eval_zero_at_prod_finset (PowLinSpan.polOf φ d)
      (fun _ => (Finset.range (d + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
    · intro x
      rw [Finset.card_image_of_injective _ Nat.cast_injective]
      simpa using Nat.lt_succ_of_le (PowLinSpan.degreeOf_polOf_le φ d x)
    · intro v hv
      have hv' : ∀ i, ∃ k : ℕ, (k : ℝ) = v i := by
        intro i
        obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hv i)
        exact ⟨k, hk⟩
      choose k hk using hv'
      rw [PowLinSpan.eval_polOf]
      have h := hkill (fun i => (k i : ℤ))
      have he : (∑ x, C (v x) * X x : MvPolynomial ι ℝ) = lin (fun i => (((k i : ℤ)) : ℝ)) := by
        simp only [lin, Int.cast_natCast, hk]
      rw [he]
      exact h
  exact hφF (PowLinSpan.homog_kill φ d hP F hF)

section Linear

variable {M : Type} [TopologicalSpace M] {m : ℕ} (A : HolAtlas M m) {ι : Type} (w : ι → A.Pt → Ev m)

theorem evalF_add (G₁ G₂ : MvPolynomial ι ℝ) : evalF A w (G₁ + G₂) = evalF A w G₁ + evalF A w G₂ := by
  funext x
  simp [evalF, fld]

theorem evalF_smul (t : ℝ) (G : MvPolynomial ι ℝ) : evalF A w (t • G) = (t : ℂ) • evalF A w G := by
  funext x
  simp [evalF, fld, MvPolynomial.smul_eq_C_mul, Algebra.smul_def]

end Linear

theorem integral_lin (hX : IsRegVar p D) (σ : k →+* ℂ) {ι : Type} (L : ι → HermLB p) :
    (∀ G₁ G₂ : MvPolynomial ι ℝ,
      (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (G₁ + G₂)) =
        (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G₁) +
          (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G₂)) ∧
    ∀ (t : ℝ) (G : MvPolynomial ι ℝ),
      (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (t • G)) =
        t * (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) := by
  haveI := hX.toIsArithVar.compactSpace σ
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  have hform : ∀ G : MvPolynomial ι ℝ, (hX.atlas σ).IsForm (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) :=
    fun G => ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hX.atlas σ)).2.2.2.1 ι _ G
      (fun i => ((GlobalTheory.T.firstChern_form_properties k X p D hX σ).1 (L i) (L i)).1.1)).1
  have P := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous (CxPts p σ) D (hX.atlas σ)
  have hint : ∀ G : MvPolynomial ι ℝ, ∀ ε : ℤˣ,
      Integrable (fun _ => (1 : ℝ)) ((hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) ε) :=
    fun G ε => by
      haveI := P.1 _ (hform G) ε
      exact integrable_const _
  refine ⟨fun G₁ G₂ => ?_, fun t G => ?_⟩
  · rw [← wInt_one, ← wInt_one, ← wInt_one, evalF_add]
    exact (P.2.1 _ _ _ (hform G₁) (hform G₂) (hint G₁) (hint G₂)).2
  · rw [← wInt_one, ← wInt_one, evalF_smul]
    exact P.2.2.1 _ t _ (hform G)

theorem geoFun_eq_integral : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (ι : Type) [Fintype ι] (L : ι → HermLB p) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ),
    IsGeoFun L D Ψ → ∀ G : MvPolynomial ι ℝ, G.IsHomogeneous D →
      Ψ G = ∑ᶠ σ : k →+* ℂ, (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) := by
  intro k _ X _ p D hX ι _ L Ψ hΨ G hG
  haveI := hX.toIsArithVar.finite_emb
  have hspan := mem_span_pow_lin D G hG
  clear hG
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    rw [hΨ.1 n]
    unfold gdeg chInt
    exact finsum_congr fun σ => (integral_eq_chernInt hX σ L n).symm
  | zero =>
    rw [map_zero]
    refine (finsum_eq_zero_of_forall_eq_zero fun σ => ?_).symm
    have := (integral_lin hX σ L).2 0 0
    rw [zero_smul, zero_mul] at this
    exact this
  | add x y _ _ hx hy =>
    rw [map_add, hx, hy, ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
    exact finsum_congr fun σ => ((integral_lin hX σ L).1 x y).symm
  | smul t x _ hx =>
    rw [map_smul, hx, smul_eq_mul, mul_finsum _ _]
    exact finsum_congr fun σ => ((integral_lin hX σ L).2 t x).symm

end GlobalTheory.LineForm.GeoInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateLociClosedSiegelPullback
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem lieGeom_locus_closed : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), (∃ z : T ⟶ Z, z ≫ j = g) ↔ ((∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ g ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ g)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : R →+* k), x ≫ g ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ g)) := by
  intro p _ D R _ b N hN3 hNp h M B _ ζ S s₁ t c e he hK X _ πX AX _ _ φX φ₂X actX ηX hpb hsq hros heta
  have hab : IsAbelianScheme AX := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab hpb
  obtain ⟨Z₁, i₁, hi₁, hZ₁⟩ := lieHer_closed b (πX ≫ t) AX hab.smooth actX
  obtain ⟨o, ho⟩ := GlobalTheory.T.exists_harrisTaylorPreObject_of_siegelPullback p D R b N h M B ζ S s₁ t c e he hK X πX AX φX φ₂X actX ηX hpb hsq hros heta
  obtain ⟨U, hU, hUx⟩ := PreEta.exists_clopen_geomAt p D R b N hN3 hNp X (πX ≫ t) o
  obtain ⟨Z, j, hj, hZ⟩ := GlobalTheory.T.closedImmersion_restrict_clopen_factorization i₁ hi₁ U hU
  refine ⟨Z, j, hj, fun T g => ?_⟩
  rw [hZ T g]
  apply and_congr
  · constructor
    · rintro ⟨y, rfl⟩ R' _ β x hx
      exact (hZ₁ R' β (x ≫ y ≫ i₁) (by simpa only [Category.assoc] using hx)).1 ⟨x ≫ y, by simp⟩
    · intro H
      refine GlobalTheory.T.exists_factor_closedImmersion_of_affine_points i₁ hi₁ g fun R' _ x => ?_
      obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ g ≫ πX ≫ t)
      exact (hZ₁ R' β (x ≫ g) (by simpa only [Category.assoc] using hβ)).2 (H R' β x hβ)
  · constructor
    · intro hg k _ _ x β _
      refine (ho k (x ≫ g)).1 ((hUx k (x ≫ g)).1 ?_)
      rintro _ ⟨u, rfl⟩
      exact hg ⟨x.base u, by simp⟩
    · intro H
      rintro _ ⟨τ, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point T τ
      obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ g ≫ πX ≫ t)
      have hG := (hUx k (x ≫ g)).2 ((ho k (x ≫ g)).2 (H k x β hβ))
      obtain ⟨u, hu⟩ : τ ∈ Set.range x.base := by rw [hx]; rfl
      exact hG ⟨u, by simp [hu]⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceVectorValuedEqFiniteKernelSum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

section Assembly
variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem trOn_eqvM (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ)
    (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) (hsupp : {q : G ⧸ K' | F q.out ≠ 0}.Finite)
    (hdc : Finite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)))
    (hst : ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G)) :
    trOn (eqvM ι ρ K') (levOp (rightReg ℂ G V) K K' F LinearMap.id) =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G),
        ((stabCard ι K' (Quotient.out q) : ℂ))⁻¹ *
          ∑ᶠ h : H, F ((Quotient.out q)⁻¹ * ι h * Quotient.out q) * LinearMap.trace ℂ V (ρ h) := by
  classical
  have hR : ∀ k ∈ K', ∀ x, F (x * k) = F x := fun k hk x => (hF k hk x).2
  have hmaps := GlobalTheory.T.heckeOperator_preserves_equivariantRightInvariant G H V ι ρ K K' F hF
  unfold trOn
  rw [dif_pos hmaps]
  haveI : Fintype (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)) := Fintype.ofFinite _
  set T := levOp (rightReg ℂ G V) K K' F LinearMap.id with hT
  set M := eqvM ι ρ K' with hM
  let x : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → G := fun q => Quotient.out q
  let e : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → (M →ₗ[ℂ] V) :=
    fun q => (LinearMap.proj (R := ℂ) (φ := fun _ : G => V) (x q)).comp M.subtype
  let s : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → (V →ₗ[ℂ] M) :=
    fun q => (secM ι ρ K' (x q)).codRestrict M (fun v => GlobalTheory.T.equivariantDoubleCosetSection_mem_equivariant G H V ι ρ K' (x q) v)
  have hid : ∑ q, s q ∘ₗ e q = LinearMap.id := by
    ext φ : 1
    apply Subtype.ext
    have := GlobalTheory.T.equivariantFunction_eq_finsum_doubleCosetSections G H V ι hι ρ K' hdc hst φ.1 φ.2
    rw [finsum_eq_sum_of_fintype] at this
    simpa [s, e, x] using this
  have h1 : ∀ φ : M, φ = ∑ q, s q (e q φ) := fun φ => by
    conv_lhs => rw [← LinearMap.id_apply (R := ℂ) φ, ← hid]
    simp
  haveI : Module.Finite ℂ M := by
    refine Module.Finite.of_injective (LinearMap.pi e) fun a b hab => ?_
    rw [h1 a, h1 b]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show e q a = e q b from congrFun hab q]
  have htr : LinearMap.trace ℂ M (T.restrict hmaps) =
      ∑ q, LinearMap.trace ℂ V (e q ∘ₗ T.restrict hmaps ∘ₗ s q) := by
    have hsum : T.restrict hmaps ∘ₗ (∑ q, s q ∘ₗ e q) = ∑ q, (T.restrict hmaps ∘ₗ s q) ∘ₗ e q := by
      ext φ : 1
      simp [LinearMap.sum_apply, map_sum]
    conv_lhs => rw [← LinearMap.comp_id (T.restrict hmaps), ← hid, hsum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [LinearMap.trace_comp_comm']
  rw [htr, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hfin := GlobalTheory.T.finite_rationalPoints_conj_in_support G H ι hι K' F hR hsupp (x q) (hst _)
  have hsub : ∀ {β : Type} [AddCommMonoid β] (g : H → β), (∀ h, F ((x q)⁻¹ * ι h * x q) = 0 → g h = 0) →
      Function.support g ⊆ hfin.toFinset := fun g hg h hh => by
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    exact fun h0 => hh (hg h h0)
  have hA : e q ∘ₗ T.restrict hmaps ∘ₗ s q = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ((stabCard ι K' (x q) : ℂ))⁻¹ •
      ∑ h ∈ hfin.toFinset, F ((x q)⁻¹ * ι h * x q) • ρ h := by
    ext v
    have := GlobalTheory.T.heckeOperator_equivariantDoubleCosetSection_basePoint G H V ι hι ρ K K' F hR hsupp (x q) (hst _) hfin v
    rw [finsum_eq_sum_of_support_subset _ (hsub _ fun h h0 => by simp [h0])] at this
    simpa [e, s, LinearMap.restrict_apply, LinearMap.sum_apply] using this
  rw [hA, LinearMap.map_smul, LinearMap.map_smul, map_sum, smul_eq_mul, smul_eq_mul,
    finsum_eq_sum_of_support_subset _ (hsub (fun h => F ((x q)⁻¹ * ι h * x q) * LinearMap.trace ℂ V (ρ h))
      fun h h0 => by simp [h0])]
  simp only [map_smul, smul_eq_mul, x]

end Assembly

end GlobalTheory.BCT.TraceBlocks

namespace GlobalTheory.BCT.TraceBlocks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finPtHom_injective : Function.Injective (finPtHom (E := E) (n := n)) := by
  intro a b h
  have h1 : finGL E n (ratF E n a.1) = finGL E n (ratF E n b.1) := by
    have := congrArg (fun k : finU E n => (k : UA E n).1) h
    simpa only [finPtHom_apply, FinPtLoc.finPt_eq] using this
  have h2 : ratF E n a.1 = ratF E n b.1 := by
    have := congrArg (GeneralLinearGroup.map (pFin E)) h1
    simpa using this
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩⟩
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact (algebraMap E (Af E)).injective (congrArg (fun g : GL (Fin n) (Af E) => g.val i j) h2)

theorem finPtHom_range : (finPtHom (E := E) (n := n)).range = ratFinU E n := by
  ext k
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨γ.1, γ.2, ?_⟩
    have := FinPtLoc.finPt_eq γ
    exact (congrArg Subtype.val this).symm
  · rintro ⟨g, hg, he⟩
    refine ⟨⟨g, hg⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [finPtHom_apply, FinPtLoc.finPt_eq]
    exact he

end GlobalTheory.BCT.TraceBlocks

open GlobalTheory.BCT.TraceBlocks in

theorem GlobalTheory.BCT.TrKer.trOn_vecM_hopM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ * ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU E n)) (globLev S K' : Set (finU E n)), ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU E n)) : ℂ))⁻¹ * ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * LinearMap.trace ℂ _ (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹) := by
  intro E _ _ _ hU n _ S hS lam K' hK f hf
  have hV : GlobalTheory.BCT.TrKer.vecM S lam K' = eqvM finPtHom (wDual lam) (globLev S K') := rfl
  have hT : GlobalTheory.BCT.TrKer.hopM S lam K' f =
      levOp (rightReg ℂ (finU E n) (Module.Dual ℂ (GlobalTheory.BCT.TrKer.Wsp lam))) (globLev S (KL n)) (globLev S K')
        (globFn S f) LinearMap.id := rfl
  have hF := globFn_inv S K' f fun w => (hf.1 w).2
  have hdc : Finite (DoubleCoset.Quotient ((finPtHom (E := E) (n := n)).range : Set (finU E n))
      (globLev S K' : Set (finU E n))) := by
    rw [finPtHom_range]
    exact GlobalTheory.T.finite_doubleCoset_definiteUnitaryRational_of_isOpen E n _ (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK)
  have hst : ∀ x : finU E n, Finite ((finPtHom (E := E) (n := n)).range ⊓
      (globLev S K').map (MulAut.conj x).toMonoidHom : Subgroup (finU E n)) := fun x => by
    rw [finPtHom_range]
    exact GlobalTheory.T.finite_definiteUnitary_rational_inf_conj_level E hU n S hS K' hK x
  rw [hV, hT, trOn_eqvM finPtHom finPtHom_injective (wDual lam) _ _ _ hF (GlobalTheory.T.finite_productOfLocalFunctionsUnitary_ne_zero E hU n S K' hK f hf) hdc hst]
  have htr : ∀ γ : UE E n, LinearMap.trace ℂ _ (wDual lam γ) = LinearMap.trace ℂ _ (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹) :=
    fun γ => LinearMap.trace_transpose' _
  simp only [htr, finPtHom_apply, stabCard]
  rw [finPtHom_range]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightGenericPointNonnegAmpleSemiPositive
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem GlobalTheory.HSNef.height_generic_nonneg_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → 1 ≤ D → ∀ (C : HermLB p) (h : X → ℝ), IsAmpleLB C.B → C.SemiPos D → C.IsArithHeight h → (∀ z, z ≠ genericPoint X → 0 ≤ h z) → 0 ≤ h (genericPoint X) := by
  intro hAr hHS k _ X _ p D hX hD C h hA hS hH hnn
  by_contra hc
  push_neg at hc
  have hg : 0 < gdeg C D := GlobalTheory.T.geometricDegree_pos_of_ample_semiPositive hAr hHS k X p D hX C hA hS
  set c := h (genericPoint X) with hcdef
  set g := gdeg C D with hgdef
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  set x : ℝ := -c / g with hx
  have hx0 : 0 < x := div_pos (by linarith) hg
  have hxg : x * g = -c := by rw [hx]; field_simp
  set u : ℝ := x * (D + 2) / (2 * (D + 1)) with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  set α : ℝ := c + ((D : ℝ) + 1) * u * g with hα
  have hαv : α = -c * D / 2 := by
    rw [hα, hu]; field_simp; linear_combination ((D : ℝ) + 2) * hxg
  have hα0 : 0 < α := by rw [hαv]; have : 0 < -c := by linarith
                         positivity
  have hcu : c + u * g < 0 := by
    have e : c + u * g = c * D / (2 * (D + 1)) := by
      rw [hu]; field_simp; linear_combination ((D : ℝ) + 2) * hxg
    rw [e]; exact div_neg_of_neg_of_pos (by nlinarith) (by positivity)
  set C' := C.shift (fun _ => u) fun _ => rfl with hC'
  have hself : C.IsSelfInter c := ⟨h, hH, rfl⟩
  have hα' : C'.IsSelfInter α := hAr.arShift k X p D hX C c u hself
  have hA' : IsAmpleLB C'.B := hA
  have hS' : C'.SemiPos D := hS.shift _ _
  obtain ⟨P, hPL, -⟩ := exists_pair C' C'
  have hrep : P.Rep 1 0 C' := hPL ▸ (GlobalTheory.VolBr.Pair.rep_base k X p P).1
  have hfac : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have hε : 0 < α / (2 * ((D + 1).factorial : ℝ)) := by positivity
  obtain ⟨m, hm, hm0⟩ := ((GlobalTheory.T.log_count_radius_one_lower_bound_ample_semiPos hHS k X p D hX P 1 0 0 0 C' α hrep hA' hS' hα' _ hε).and
    (eventually_gt_atTop 0)).exists
  have hcoef : α / ((D + 1).factorial : ℝ) - α / (2 * ((D + 1).factorial : ℝ)) = α / (2 * ((D + 1).factorial : ℝ)) := by
    field_simp; ring
  rw [hcoef] at hm
  have hlc : 0 < P.lc ((m : ℤ) * 1) ((m : ℤ) * 0) 1 := by
    have : (0 : ℝ) < (m : ℝ) ^ (D + 1) := by positivity
    have := mul_pos hε this
    simpa using lt_of_lt_of_le this hm
  have hn : 1 < (P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).ncard := by
    by_contra hle
    push_neg at hle
    have : ((P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).ncard : ℝ) ≤ 1 := by exact_mod_cast hle
    exact absurd hlc (not_lt.2 (Real.log_nonpos (Nat.cast_nonneg _) this))
  have hfin : (P.Bl ((m : ℤ) * 1) ((m : ℤ) * 0) 1).Finite :=
    Set.finite_of_ncard_ne_zero (by omega)
  have henc : 1 < ((C'.pow m).smallSec).encard := by
    rw [(GlobalTheory.VolBr.SmallBall.main k X p P 1 0 C' hrep 0 m).2.1, ← hfin.cast_ncard_eq]
    exact_mod_cast hn
  obtain ⟨a, b, ha, hb, hab⟩ := Set.one_lt_encard_iff.1 henc
  have hex : ∃ s ∈ (C'.pow m).smallSec, s ≠ 0 := by
    by_cases ha0 : a = 0
    · exact ⟨b, hb, fun hb0 => hab (ha0.trans hb0.symm)⟩
    · exact ⟨a, ha, ha0⟩
  have := GlobalTheory.T.height_add_mul_geometricDegree_nonneg_of_smallSection hAr k X p D hX hD C h hS hH hnn m u hm0 hu0 hex
  linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFamilyExpansionEqConstMulAlgClosureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_family_expansion_eq_const_mul_algClosure : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ E₀ (Φ₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → H0 C.A.L (C.n ^ j)), Eqv D.toPre C.A (Kb R) (C.n ^ j) (C.lab j) E₀ → (∀ F₀ s, F₀.Over s → Agree C.A.L (E₀ s) (Φ₀ F₀)) → ∀ (Φ : IntFam (maximalIdeal R) D.toPre (C.n ^ j) → SecK C.P.L.L C.α (C.n ^ j)), (∀ F₀ (Z : Scheme.{0}) (p : Z ⟶ C.A.A.left) (z : Z) J J', Good C.P.L.L z J → Good C.A.L z J' → sval (Φ F₀) p z J = (gw wA p z (J (p ≫ C.α)) (J' p) ^ (C.n ^ j)).val * sval (Φ₀ F₀) p z J') → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∃ c : F, c ≠ 0 ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)) (σ : SecK C.P.L.L T.β (C.n ^ j)), T.ExpBy 1 σ F₀ → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left), p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = p' ≫ (fst (TFK (R := R) F) C.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs (p' ≫ (fst (TFK (R := R) F) C.A.A).left) z ⊤ (fnF F c) * sval (Φ F₀) (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z J := by
  first | exact @GlobalTheory.Mum.fvalue_const | exact GlobalTheory.Mum.fvalue_const | (intros; apply GlobalTheory.Mum.fvalue_const <;> assumption)
end

