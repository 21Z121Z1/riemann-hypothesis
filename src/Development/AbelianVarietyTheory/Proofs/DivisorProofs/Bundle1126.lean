import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0015
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1070
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasicoherentOfLocallyIso
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0903
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1087
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChartMetricBlockForm
section
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

open Filter Topology Set
open scoped ContDiff

namespace GlobalTheory.HessPull

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.AR.Up.RGF in

theorem cHess_comp_apply (n d : ℕ) (g : V d → ℂ) (F : V n → V d) (U : Set (V n)) (hU : IsOpen U)
    (v : V n) (hv : v ∈ U) (hF : ContDiffOn ℂ 2 F U) (hg : ContDiffAt ℝ 2 g (F v)) (j k : Fin n) :
    cHess n (g ∘ F) v j k = ∑ a, ∑ b,
      cHess d g (F v) b a * fderiv ℂ F v (bas n j) b *
        (starRingEnd ℂ) (fderiv ℂ F v (bas n k) a) := by
  have hFd : ∀ y ∈ U, HasFDerivAt F (fderiv ℂ F y) y := fun y hy =>
    (((hF.differentiableOn (by norm_num)) y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
  have hgev : ∀ᶠ y in 𝓝 v, ContDiffAt ℝ 2 g (F y) :=
    (hFd v hv).continuousAt.eventually (hg.eventually (by simp))
  have hwdb : ∀ k, wdb n k (g ∘ F) =ᶠ[𝓝 v]
      fun y => ∑ a, wdb d a g (F y) * (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a) := by
    intro k
    filter_upwards [hgev, hU.mem_nhds hv] with y hy hyU
    exact gc_wdb_comp n d g F _ y (hy.differentiableAt (by simp)) (hFd y hyU) k
  have hD : DifferentiableAt ℝ (fderiv ℝ g) (F v) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hWg : ∀ a, DifferentiableAt ℝ (wdb d a g) (F v) := by
    intro a
    show DifferentiableAt ℝ (fun y => (fderiv ℝ g y (bas d a) +
      Complex.I * fderiv ℝ g y (Complex.I • bas d a)) / 2) (F v)
    have h1 := hD.clm_apply (differentiableAt_const (bas d a))
    have h2 := hD.clm_apply (differentiableAt_const (Complex.I • bas d a))
    have h3 := (h1.add (h2.const_mul Complex.I)).mul_const ((2 : ℂ)⁻¹)
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [div_eq_mul_inv]
  have hWa : ∀ a, DifferentiableAt ℝ (fun y => wdb d a g (F y)) v := fun a =>
    (hWg a).comp v ((hFd v hv).restrictScalars ℝ).differentiableAt
  have hDF : DifferentiableAt ℂ (fun y => fderiv ℂ F y) v :=
    ((hF.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt (hU.mem_nhds hv)).differentiableAt
      (by norm_num)
  have hPa : ∀ k a, DifferentiableAt ℂ (fun y => fderiv ℂ F y (bas n k) a) v := fun k a =>
    (differentiableAt_piLp 2).1 (hDF.clm_apply (differentiableAt_const _)) a
  have hCa : ∀ k a, DifferentiableAt ℝ
      (fun y => (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v := by
    intro k a
    have := Complex.conjCLE.differentiableAt.comp v ((hPa k a).restrictScalars ℝ)
    simpa [Function.comp_def] using this
  show wd n j (wdb n k (g ∘ F)) v = _
  rw [wd_congr n j _ _ v (hwdb k),
    fc_wd_sum n j Finset.univ (fun a y => wdb d a g (F y) *
      (starRingEnd ℂ) (fderiv ℂ F y (bas n k) a)) v (fun a _ => (hWa a).mul (hCa k a))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [wd_mul' n j _ _ v (hWa a) (hCa k a), wd_conj', fc_wdb_holo n _ v (hPa k a) j, map_zero,
    mul_zero, add_zero]
  have := gc_wd_comp n d (wdb d a g) F (fderiv ℂ F v) v (hWg a) (hFd v hv) j
  rw [show (fun y => wdb d a g (F y)) = wdb d a g ∘ F from rfl, this, Finset.sum_mul]
  rfl

end GlobalTheory.HessPull

namespace GlobalTheory.HessPull

open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open GlobalTheory.ChartGlue

theorem hess_pull_factor : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k)
    (f : Y ⟶ B) (w : f ≫ q = p) (σ : k →+* ℂ) (D d : ℕ) (c : AlgChart p σ D) (c' : AlgChart q σ d)
    (y : CxPts p σ), y ∈ c.e.source → PtsOver.map f w (spMap σ) y ∈ c'.e.source →
    ∃ (P : Matrix (Fin D) (Fin d) ℂ) (Q : Matrix (Fin d) (Fin D) ℂ), ∀ (A : HermLB q)
      (i : (A.pull f w).B.ι), y ∈ ptsIn p σ ((A.pull f w).B.U i) →
        ∃ K : Matrix (Fin d) (Fin d) ℂ, c.hess ((A.pull f w).φ σ) i y = P * K * Q := by
  intro k _ B Y q p f w σ D d c c' y hy hy'
  set m := PtsOver.map f w (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ f := fun _ => rfl
  set F : V D → V d := c'.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c'.e.source)
  have hU : IsOpen U := isOpen_over c.e (c'.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := mem_over c.e hy hy'
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c'
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c'.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy]
  refine ⟨Matrix.of fun j b => fderiv ℂ F (c.e y) (bas D j) b,
    Matrix.of fun a k => (starRingEnd ℂ) (fderiv ℂ F (c.e y) (bas D k) a), ?_⟩
  intro A i hi
  have him : m y ∈ ptsIn q σ (A.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hi PUnit.unit
  set g : V d → ℂ := fun v => ((A.φ σ).φ (i PUnit.unit) (c'.e.symm v) : ℂ)
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((A.cInf σ).contDiffAt c' hy' him)
  have e : (fun v => (((A.pull f w).φ σ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ (A.φ σ) f w i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c'.e.left_inv hv.2]
    exact congrArg _ this
  refine ⟨cHess d g (F (c.e y)), ?_⟩
  show cHess D _ (c.e y) = _
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]
  ext j k
  rw [cHess_comp_apply D d g F U hU _ hyU hF hg j k, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end GlobalTheory.HessPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory

namespace GlobalTheory.FlagPull

theorem injective_of_isBaseChange_of_retraction {A B M M' N N' : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M] [AddCommGroup M'] [Module A M']
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] [AddCommGroup N']
    [Module A N'] [Module B N'] [IsScalarTower A B N'] {l : M →ₗ[A] N} {l' : M' →ₗ[A] N'}
    (hl : IsBaseChange B l) (hl' : IsBaseChange B l') (a : M →ₗ[A] M') (b : N →ₗ[B] N')
    (hab : ∀ m, b (l m) = l' (a m)) (r : M' →ₗ[A] M) (hr : r ∘ₗ a = LinearMap.id) :
    Function.Injective b := by
  have e : b ∘ₗ hl.equiv.toLinearMap = hl'.equiv.toLinearMap ∘ₗ a.baseChange B := by
    ext m
    simp [hab]
  have ha : Function.Injective (a.baseChange B) := by
    have h : (r.baseChange B) ∘ₗ (a.baseChange B) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, hr, LinearMap.baseChange_id]
    exact Function.LeftInverse.injective (g := r.baseChange B) fun x => by
      rw [← LinearMap.comp_apply, h, LinearMap.id_apply]
  have h : Function.Injective (b ∘ₗ hl.equiv.toLinearMap) := by
    rw [e]
    exact hl'.equiv.injective.comp ha
  exact Function.Injective.of_comp_right h hl.equiv.surjective

theorem isQuasicoherent_X₂ {X : Scheme.{0}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {s : ℕ} (h₃ : IsVB S.X₃ s) [S.X₁.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  have := hS.mono_f
  have := hS.epi_g
  have : S.X₃.IsQuasicoherent := h₃.isQuasicoherent
  have hex (W : X.Opens) (t : Γ(S.X₂, W)) (ht : S.g.app W t = 0) : ∃ u, S.f.app W u = t :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W t).1 ht
  refine QCoh.isQuasicoherent_of_forall_exists_affine _ fun x => ?_
  obtain ⟨U, -, hxU, σ, hσ, hg⟩ :=
    DualExact.exists_local_section S.g h₃ (V := ⊤) (x := x) trivial
  obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  have hle : U' ≤ U := hle
  refine ⟨U', hU', hxU', fun a => (QCoh.isLocalizedModule_resBasicOpen_iff _ a).2
    ⟨fun t => ?_, fun t ht => ?_⟩⟩
  · have hD : X.basicOpen a ≤ U' := X.basicOpen_le a
    obtain ⟨n, t₃, ht₃⟩ := QCoh.exists_pow_smul_eq_res S.X₃ hU' a hD rfl (S.g.app _ t)
    obtain ⟨u, hu⟩ := hex _ (t - σ _ (hD.trans hle) (S.g.app _ t)) (by rw [map_sub, hg, sub_self])
    obtain ⟨m, u', hu'⟩ := QCoh.exists_pow_smul_eq_res S.X₁ hU' a hD rfl u
    refine ⟨n + m, a ^ m • σ U' hle t₃ + a ^ n • S.f.app U' u', ?_⟩
    have e₁ : S.X₂.presheaf.map (homOfLE hD).op (σ U' hle t₃) =
        σ _ (hD.trans hle) (S.X₃.presheaf.map (homOfLE hD).op t₃) := (hσ _ _ hle hD t₃).symm
    have e₂ : S.X₂.presheaf.map (homOfLE hD).op (S.f.app U' u') =
        S.f.app _ (S.X₁.presheaf.map (homOfLE hD).op u') := (QCoh.app_res S.f hD u').symm
    have e₃ : t = σ _ (hD.trans hle) (S.g.app _ t) + S.f.app _ u := by rw [hu]; abel
    rw [map_add, S.X₂.map_smul, S.X₂.map_smul, e₁, e₂, ← ht₃, ← hu', map_smul,
      Scheme.Modules.Hom.app_smul, map_pow, map_pow, smul_smul, smul_smul]
    conv_lhs => rw [e₃]
    rw [smul_add, pow_add]
    congr 1
    · rw [mul_comm]
  · have hD : X.basicOpen a ≤ U' := X.basicOpen_le a
    obtain ⟨n, hn⟩ := QCoh.exists_pow_smul_eq_zero S.X₃ hU' a hD rfl (S.g.app U' t)
      (by rw [← QCoh.app_res, ht, map_zero])
    obtain ⟨u, hu⟩ := hex U' (a ^ n • t) (by rw [Scheme.Modules.Hom.app_smul, hn])
    obtain ⟨m, hm⟩ := QCoh.exists_pow_smul_eq_zero S.X₁ hU' a hD rfl u
      (QCoh.injective_app_of_mono S.f _ (by
        rw [QCoh.app_res, hu, S.X₂.map_smul, ht, smul_zero, map_zero]))
    exact ⟨m + n, by rw [pow_add, mul_smul, ← hu, ← Scheme.Modules.Hom.app_smul, hm, map_zero]⟩

theorem mono_pullback_map_f {X Y : Scheme.{0}} (f : Y ⟶ X) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) {s : ℕ} (h₃ : IsVB S.X₃ s) [S.X₁.IsQuasicoherent]
    [S.X₂.IsQuasicoherent] : Mono ((Scheme.Modules.pullback f).map S.f) := by
  have := hS.mono_f
  have := hS.epi_g
  have hex (W : X.Opens) (t : Γ(S.X₂, W)) (ht : S.g.app W t = 0) : ∃ u, S.f.app W u = t :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W t).1 ht
  have hz (W : X.Opens) (u : Γ(S.X₁, W)) : S.g.app W (S.f.app W u) = 0 :=
    (QCoh.exact_app_of_exact_of_mono hS.exact W _).2 ⟨u, rfl⟩
  refine QCoh.mono_of_locally_app_injective _ fun W y hy => ?_
  obtain ⟨U, -, hxU, σ, -, hg⟩ :=
    DualExact.exists_local_section S.g h₃ (V := ⊤) (x := f y) trivial
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxU U.2
  have hVU : V ≤ U := hVU
  obtain ⟨_, ⟨U', hU', rfl⟩, hyU', hle⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ W ⊓ f ⁻¹ᵁ V from ⟨hy, hyV⟩) (W ⊓ f ⁻¹ᵁ V).2
  have e : U' ≤ f ⁻¹ᵁ V := fun _ h => (hle h).2
  refine ⟨U', hyU', fun _ h => (hle h).1, ?_⟩
  let π : Γ(S.X₂, V) →ₗ[Γ(X, V)] Γ(S.X₂, V) := LinearMap.id - σ V hVU ∘ₗ QCoh.homAppLinear S.g V
  have hc (t : Γ(S.X₂, V)) : ∃ u, QCoh.homAppLinear S.f V u = π t := hex V _ (by
    change S.g.app V (t - σ V hVU (S.g.app V t)) = 0
    rw [map_sub, hg, sub_self])
  let ρ : Γ(S.X₂, V) →ₗ[Γ(X, V)] Γ(S.X₁, V) :=
    LinearMap.codRestrictOfInjective π (QCoh.homAppLinear S.f V) (QCoh.injective_app_of_mono S.f V) hc
  have hρ : ρ ∘ₗ QCoh.homAppLinear S.f V = LinearMap.id := by
    refine LinearMap.ext fun u => QCoh.injective_app_of_mono S.f V ?_
    have h := LinearMap.codRestrictOfInjective_comp_apply π (QCoh.homAppLinear S.f V)
      (QCoh.injective_app_of_mono S.f V) hc (S.f.app V u)
    change S.f.app V (ρ (S.f.app V u)) = S.f.app V u
    refine h.trans ?_
    change S.f.app V u - σ V hVU (S.g.app V (S.f.app V u)) = S.f.app V u
    rw [hz, map_zero, sub_zero]
  letI := QCoh.appLEAlgebra f e
  letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj S.X₁) e
  haveI := QCoh.appLE_isScalarTower f ((Scheme.Modules.pullback f).obj S.X₁) e
  letI := QCoh.appLEModule f ((Scheme.Modules.pullback f).obj S.X₂) e
  haveI := QCoh.appLE_isScalarTower f ((Scheme.Modules.pullback f).obj S.X₂) e
  exact injective_of_isBaseChange_of_retraction
    (QCoh.isBaseChange_pullbackSections f S.X₁ hU' hV e)
    (QCoh.isBaseChange_pullbackSections f S.X₂ hU' hV e) (QCoh.homAppLinear S.f V)
    (QCoh.homAppLinear ((Scheme.Modules.pullback f).map S.f) U')
    (QCoh.pullback_map_app_pullbackSections f S.f e) ρ hρ

theorem isQuasicoherent_and_hasFlag_pullback {X Y : Scheme.{0}} (f : Y ⟶ X) {E : X.Modules}
    {l : List (LB X)} (h : HasFlag E l) :
    E.IsQuasicoherent ∧ HasFlag ((Scheme.Modules.pullback f).obj E) (l.map fun L => L.pull f) := by
  induction h with
  | nil h => exact ⟨QCoh.isQuasicoherent_of_isZero h, .nil (Functor.map_isZero _ h)⟩
  | @cons L l S hS hL e h ih =>
    obtain ⟨h₁, ih⟩ := ih
    have h₃ : IsVB S.X₃ 1 := (isVB_toMod hL).of_iso e.symm
    haveI := h₁
    haveI h₂ : S.X₂.IsQuasicoherent := isQuasicoherent_X₂ S hS h₃
    refine ⟨h₂, ?_⟩
    have := hS.epi_g
    obtain ⟨φ⟩ := nonempty_pullback_toMod_iso hL f
    have hS' : (S.map (Scheme.Modules.pullback f)).ShortExact :=
      ShortComplex.ShortExact.mk' (QCoh.exact_map_pullback f hS.exact).1
        (mono_pullback_map_f f S hS h₃) (QCoh.exact_map_pullback f hS.exact).2
    exact .cons (S.map (Scheme.Modules.pullback f)) hS' (Semi.LB.isLB_pull hL f)
      ((Scheme.Modules.pullback f).mapIso e ≪≫ φ) ih

theorem hasFlag_pullback : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (E : X.Modules) (l : List (LB X)),
    HasFlag E l → HasFlag ((Scheme.Modules.pullback f).obj E) (l.map fun L => L.pull f) :=
  fun _ _ f _ _ h => (isQuasicoherent_and_hasFlag_pullback f h).2

end GlobalTheory.FlagPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticTwistCmCurveModelDiscriminantNegPrimeCu
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.LocAll

theorem modelAt_of_val {V : ValuationSubring ℂ} {F : IntermediateField ℚ ℂ} {W : WeierstrassCurve ℂ} {D D' : ℂ}
    (h : ModelAt V F W D) (hv : V.valuation D = V.valuation D') : ModelAt V F W D' := by
  obtain ⟨C, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨C, h1, h2, h3, h4, h5, h6.trans hv⟩

theorem mem_of_isIntegral (V : ValuationSubring ℂ) {y : ℂ} (hy : IsIntegral ℤ y) : y ∈ V := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := V) (K := ℂ) (hy.tower_top (A := V))
  exact hz ▸ z.2

theorem short_Δ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).Δ =
    d ^ 6 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem short_c₄ (d a b : ℂ) : (⟨0, 0, 0, d ^ 2 * a, d ^ 3 * b⟩ : WeierstrassCurve ℂ).c₄ =
    d ^ 2 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).c₄ := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

end GlobalTheory.CMModel.LocAll

open GlobalTheory.CMModel.LocAll in

theorem GlobalTheory.CMModel.twist_modelAt_all : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → sqProd p L t ∈ F → ∀ V : ValuationSubring ℂ, ModelAt V F (shortTwist (if p % 8 = 3 then 1 else -(p : ℂ)) (-L.g₂ / 4) (-L.g₃ / 4)) (-(p : ℂ) ^ 3) := by
  intro p F L t hp h4 h3 hD hsq V
  have h27 : (27 : ℂ) ∈ F := by simpa using F.algebraMap_mem (27 : ℚ)
  have h4F : (4 : ℂ) ∈ F := by simpa using F.algebraMap_mem (4 : ℚ)
  have hg2 : -L.g₂ / 4 ∈ F := div_mem (neg_mem hD.g₂_mem) h4F
  have hg3 : -L.g₃ / 4 ∈ F := div_mem (neg_mem hD.g₃_mem) h4F
  have hpF : (p : ℂ) ∈ F := by simpa using F.algebraMap_mem (p : ℚ)
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  by_cases hv : V.valuation (p : ℂ) = 1
  · have hgood : ModelAt V F ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ 1 := GlobalTheory.T.weierstrassModel_unit_discriminant_away_from_p p F L t hp h4 h3 hD hsq V hv
    split_ifs with h8
    · have hk := GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 0 hg2 hg3 hgood
      have e : (4 * ((0 : ℤ) : ℂ) + 1) = 1 := by simp
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, p + 1 = 4 * m := ⟨(p + 1) / 4, by omega⟩
      have hk := GlobalTheory.T.modelAt_shortTwist_four_mul_add_one' V F (-L.g₂ / 4) (-L.g₃ / 4) 1 (-(m : ℤ)) hg2 hg3 hgood
      have hmC : (p : ℂ) + 1 = 4 * m := by exact_mod_cast hm
      have e : (4 * ((-(m : ℤ) : ℤ) : ℂ) + 1) = -(p : ℂ) := by push_cast; linear_combination hmC
      rw [e] at hk
      exact modelAt_of_val hk (by simp [hv])
  · have h6 : V.valuation (6 : ℂ) = 1 := by
      have hc : Nat.Coprime p 6 := by
        have h2 : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
        have h3' : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
        simpa using Nat.Coprime.mul_right h2 h3'
      rcases GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime V p 6 hc with h | h
      · exact absurd h hv
      · exact_mod_cast h
    obtain ⟨A, hAF, hA0, hA⟩ := GlobalTheory.T.exists_cube_valuation_eq_discriminant p F L t hp h4 h3 hD V
    have hsq8 := GlobalTheory.T.prodDerivWeierstrassPOverSquares_pow_eight_mul p F L t hp h4 h3 hD
    have hΔF : (latticeCurve L).Δ ∈ F := by
      rw [latticeCurve_Δ]
      exact sub_mem (pow_mem hD.g₂_mem 3) (mul_mem h27 (pow_mem hD.g₃_mem 2))
    obtain ⟨u, huF, hu0, hu⟩ := GlobalTheory.T.exists_valuation_pow_twelve_mul_eq p V F (latticeCurve L).Δ A (sqProd p L t) h4 hΔF hAF hsq
      (latticeCurve_Δ_ne_zero L) hA0 hA hsq8
    have him : (sqrtNegNat p).im ≠ 0 := by
      simp [sqrtNegNat]
      exact hp.pos.ne'
    have hj : (latticeCurve L).j ∈ V := mem_of_isIntegral V (GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L (sqrtNegNat p) hD.mul him)
    have hjΔ := GlobalTheory.j_mul_Δ (latticeCurve L)
    have hDV : -(p : ℂ) ^ 3 ∈ V := neg_mem (pow_mem (natCast_mem V p) 3)
    have hvD : V.valuation (-(p : ℂ) ^ 3) = V.valuation (p : ℂ) ^ 3 := by simp
    set d : ℂ := if p % 8 = 3 then 1 else -(p : ℂ) with hd
    show ModelAt V F ⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ (-(p : ℂ) ^ 3)
    have hjt : (latticeCurve L).j * (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).Δ =
        (⟨0, 0, 0, d ^ 2 * (-L.g₂ / 4), d ^ 3 * (-L.g₃ / 4)⟩ : WeierstrassCurve ℂ).c₄ ^ 3 := by
      rw [short_Δ, short_c₄]
      rw [show (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L from rfl]
      linear_combination d ^ 6 * hjΔ
    by_cases h8 : p % 8 = 3
    · have hd1 : d = 1 := by rw [hd, if_pos h8]
      rw [if_pos h8] at hu
      refine GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ u _ hj hjt h6 huF hu0 hDV ?_
      rw [short_Δ, hvD, hd1, one_pow, one_mul]
      exact hu
    · have hdp : d = -(p : ℂ) := by rw [hd, if_neg h8]
      rw [if_neg h8] at hu
      refine GlobalTheory.T.modelAt_short_of_valuation_six_eq_one V F _ _ _ (u * p) _ hj hjt h6 (mul_mem huF hpF) (mul_ne_zero hu0 hp0) hDV ?_
      rw [short_Δ, hvD, hdp]
      change V.valuation (u * p) ^ 12 * V.valuation (p : ℂ) ^ 3 = V.valuation ((-(p : ℂ)) ^ 6 * (latticeCurve L).Δ)
      rw [map_mul, map_mul, map_pow, Valuation.map_neg, ← hu, mul_pow]
      rw [show V.valuation (p : ℂ) ^ 9 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 3 by rw [← pow_add],
        show V.valuation (p : ℂ) ^ 12 = V.valuation (p : ℂ) ^ 6 * V.valuation (p : ℂ) ^ 6 by rw [← pow_add]]
      ac_rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointLeSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.AdjSpanLift

open GlobalTheory.AdjBlock

section Linear

variable {K V H E : Type} [Field K] [AddCommGroup V] [Module K V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {σ : K →+* ℂ} {j : V →ₛₗ[σ] H} {ι : Type} [Fintype ι] {b : Module.Basis ι K V}

theorem range_adjoint_le_span [FiniteDimensional ℂ H] [FiniteDimensional ℂ E]
    (hli : LinearIndependent ℂ fun i => j (b i))
    (hsp : Submodule.span ℂ (Set.range j) = ⊤) {e : Module.End K V}
    (he : ∀ v w, inner ℂ (j (e v)) (j w) = inner ℂ (j v) (j (e w))) {Θ : H →ₗ[ℂ] E}
    (hΘ : ∀ v, Θ (j (e v)) = Θ (j v)) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := by
  obtain ⟨U, hU⟩ := exists_cx hli hsp e
  have h1 : Θ ∘ₗ U = Θ := ext_of_span hsp fun v => by simp only [LinearMap.comp_apply, hU, hΘ]
  have h2 : ∀ w y, inner ℂ (U y) (j w) = inner ℂ y (U (j w)) := fun w y => by
    have : innerₛₗ ℂ (j w) ∘ₗ U = innerₛₗ ℂ (U (j w)) := ext_of_span hsp fun v => by
      simp only [LinearMap.comp_apply, innerₛₗ_apply_apply, hU, he]
    have h := LinearMap.congr_fun this y
    simp only [LinearMap.comp_apply, innerₛₗ_apply_apply] at h
    rw [← inner_conj_symm, h, inner_conj_symm]
  have h3 : ∀ y, U y ∈ Submodule.span ℂ (j '' (LinearMap.range e : Set V)) := fun y => by
    have hy : y ∈ Submodule.span ℂ (Set.range j) := hsp ▸ Submodule.mem_top
    refine (Submodule.span_le (p := (Submodule.span ℂ (j '' (LinearMap.range e : Set V))).comap U)).2 ?_ hy
    rintro _ ⟨v, rfl⟩
    show U (j v) ∈ Submodule.span ℂ (j '' (LinearMap.range e : Set V))
    rw [hU]
    exact Submodule.subset_span ⟨e v, ⟨v, rfl⟩, rfl⟩
  rintro _ ⟨u, rfl⟩
  have h4 : innerₛₗ ℂ (U (LinearMap.adjoint Θ u)) = innerₛₗ ℂ (LinearMap.adjoint Θ u) := ext_of_span hsp fun w => by
    simp only [innerₛₗ_apply_apply]
    rw [h2, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hU, hΘ]
  rw [← (ext_inner_right ℂ fun w => LinearMap.congr_fun h4 w : U (LinearMap.adjoint Θ u) = LinearMap.adjoint Θ u)]
  exact h3 _

end Linear

section Pres

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [Field K] [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (G → W))
  (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y)) {j : S.Forms →ₛₗ[σ] M.H}
  (hj : ∀ x, M.e (j x) = P.extL x)

include hM hj

theorem model_good_span {G0 E : Type} [Group G0] [Fintype G0] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {r : Representation K G0 S.Forms} (hr : S.ActGood r) {X : Finset (G0 → K)}
    (hX : ∀ c ∈ X, IsAbsIrrChar c) {Θ : M.H →ₗ[ℂ] E} (gE : Representation ℂ G0 E)
    (hΘ : ∀ g v, Θ (j (r g v)) = gE g (Θ (j v)))
    (he : ∀ y, ∑ g, σ ((idemOf X).coeff g) • gE g (Θ y) = Θ y) :
    LinearMap.range (LinearMap.adjoint Θ) ≤ Submodule.span ℂ
      (j '' (LinearMap.range (S.gaOp r (goodAt X (⊥ : Subgroup G0) 1)) : Set S.Forms)) := by
  obtain ⟨h1, h2, h3⟩ := model_form P M hM hj
  rw [goodAt, level_idempotent_bot, mul_one]
  refine range_adjoint_le_span h1 h2 (sum_selfAdj r _ (fun g => ?_) fun g v w => ?_) fun v => ?_
  · simp only [coeff_idemOf, map_sum, map_mul, map_div₀, map_natCast, inv_inv]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← (hX c hc).map_inv σ, ← (hX c hc).map_inv σ, inv_one, inv_inv]
  · rw [h3, h3, hr.unitary]
  · rw [← he (j v)]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smulₛₗ, hΘ, RingHom.id_apply]

end Pres

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem proj_lifts_core {R : RealDat D A Ks} {F : Face D A} {s : ℕ} (hC : Core R F) (hOk : A.fam.Ok s) (i : Fin D.R.m) (t : T)
    (y : (R.HV i t).H) :
    ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g (R.thG i t y) = R.thG i t y := by
  have h1 : R.thF i t y ∈ LinearMap.range (R.HW i (sg0 D A)).e :=
    (hC.models.HW i (sg0 D A)).2.1.ge (hC.thP.thF_mem i t y)
  obtain ⟨z, hz⟩ := h1
  have hs : ∀ a, sg0 D A a = D.what₂.embLL a := fun a => by rw [sg0, sgAt_mk _ R.hv0]
  have h2 : R.thG i t y = ∑ g, D.what₂.embLL ((idemOf A.X).coeff g) • R.gW i (sg0 D A) g z := by
    refine (hC.models.HW i _).1 ?_
    rw [hC.thP.thG, ← hz, map_sum]
    refine (postOn_gaL (R.MW i (sg0 D A)) (R.βW i) (R.datWp i R.triv) R.eG _ _).trans ?_
    exact Finset.sum_congr rfl fun g _ => by rw [map_smul, hC.models.gW, RealDat.eC, hs]; rfl
  rw [h2]
  exact idem_idem _ hOk.irr _ z

theorem range_adjoint_lift_le (R : RealDat D A Ks) (F : Face D A) {s : ℕ} (hOk : A.fam.Ok s) (hC : Core R F)
    (hG : ∀ i t g (v : (A.MtCSD i t).Forms),
      R.thG i t (R.jV i t (A.leftGroupActionLift i t g v)) = R.gW i (sg0 D A) g (R.thG i t (R.jV i t v))) (i : Fin D.R.m) (t : T) :
    LinearMap.range (LinearMap.adjoint (R.thG i t)) ≤
      Submodule.span ℂ (R.jV i t '' ((A.fam.L i t).goodF A.X : Set (A.fam.L i t).S.Forms)) :=
  model_good_span (W := (R.cV i).W) (ι := Bridge.ratF (Vc D i)) (ρ := (R.cV i).coef.ρ)
    (J := (levEnv _ (R.βV i) (R.datVt i t)).J) (χ := (levEnv _ (R.βV i) (R.datVt i t)).χ) (R.B.L i t).pres (R.HV i t)
    (hC.models.HV i t) (hC.models.jV i t) (hOk.lifts i t).act hOk.irr
    (R.gW i (sg0 D A)) (hG i t) fun y => proj_lifts_core hC hOk i t y

end GlobalTheory.AdjSpanLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatMemSpanCoordinateBoxIndicatorsStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_mem_span_coordinateBox_indicators : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (φ : (κ → Fv F v) → ℂ), φ ∈ SB (κ → Fv F v) → ∃ N₀ : ℕ, ∀ N ≥ N₀, φ ∈ Submodule.span ℂ (Set.range fun c : κ → Fv F v => Set.indicator {x : κ → Fv F v | ∀ i, Valued.v (x i - c i) ≤ WithZero.exp (-(N : ℤ))} (1 : (κ → Fv F v) → ℂ)) := by
  first | exact @GlobalTheory.BoxDecomp.mem_span_boxes | exact GlobalTheory.BoxDecomp.mem_span_boxes | (intros; apply GlobalTheory.BoxDecomp.mem_span_boxes <;> assumption)
end

