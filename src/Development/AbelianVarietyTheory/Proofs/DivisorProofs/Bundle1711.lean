import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0064
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0052
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0053
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1688
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1671
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagThetaProductEqScalarSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUgReindex

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem covolume_ne_top_of_continuousMulEquiv : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H) (Γ : Subgroup G) (Λ : Subgroup H) [Countable Γ], (∀ g, g ∈ Γ ↔ e g ∈ Λ) → (∀ μ : Measure G, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤) → ∀ (π : Measure H) (𝓜 : Set H), π.IsHaarMeasure → IsFundamentalDomain Λ 𝓜 π → π 𝓜 ≠ ⊤ := by
  intro G _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ e Γ Λ _ hmem hfin π 𝓜 hπ h𝓜
  let E : G ≃ᵐ H := e.toHomeomorph.toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun _ => rfl
  set μ : Measure G := π.map E.symm with hμdef
  have hμ : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map π e.symm
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving E μ π := by
    refine ⟨E.measurable, ?_⟩
    rw [hμdef, Measure.map_map E.measurable E.symm.measurable]
    simp only [MeasurableEquiv.self_comp_symm, Measure.map_id]
    exact Measure.AbsolutelyContinuous.rfl
  let φ : Λ → Γ := fun l => ⟨e.symm l, (hmem _).2 (by simpa using l.2)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      apply Subtype.ext
      have := congrArg (fun x : Γ => e (x : G)) hab
      simpa [φ] using this
    · intro g
      refine ⟨⟨e g, (hmem g).1 g.2⟩, ?_⟩
      apply Subtype.ext; simp [φ]
  have hsemi : ∀ l : Λ, Function.Semiconj E (φ l • ·) (l • ·) := by
    intro l x
    show e ((e.symm l : G) * x) = (l : H) * e x
    simp [map_mul]
  have hF := h𝓜.preimage_of_equiv hqmp hφ hsemi
  have hlt := hfin μ hμ _ hF
  have : μ (E ⁻¹' 𝓜) = π 𝓜 := by
    rw [hμdef, MeasurableEquiv.map_apply]
    congr 1
    ext x; simp
  rw [this] at hlt
  exact hlt.ne

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImagesEigenLinesCmUnitaryShimuraObject
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section
namespace GlobalTheory.FlatCM.ImageDeg

open GlobalTheory.HermHom in

theorem form_diff_eq_pair : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P)
  (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (h : HermFam K (Fin F.P₀.g → K)) (h' : HermFam K (Fin F'.P₀.g → K))
  (f₁ f₂ : P.A ⟶ P'.A) (g : P.A ⟶ P.A) (M₁ M₂ : (Fin F.P₀.g → K) →ₗ[K] (Fin F'.P₀.g → K))
  (N : (Fin F.P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h → F'.IsHerm h' → IsMonHom f₁ → IsMonHom f₂ →
  IsMonHom g → LamEq P'.L f₁ f₂ P.L g (𝟙 P.A) → F.IsDiffOf F' f₁ M₁ → F.IsDiffOf F' f₂ M₂ → F.IsDiffOf F g N →
  ∀ s c c', h'.form s (M₂ c) (M₁ c') = h.form s c (N c') := by
  intro hU hL K _ _ P F P' F' h h' f₁ f₂ g M₁ M₂ N hh hh' hf₁ hf₂ hg hlam hM₁ hM₂ hN s c c'
  obtain ⟨Q, φ, t, u, Hm, χ, W, hφ, hA, hW, hform⟩ := hh s
  obtain ⟨Q', φ', t', u', Hm', χ', W', hφ', hA', hW', hform'⟩ := hh' s
  obtain ⟨-, a₀, ha₀, ea₀, da⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f₁ hf₁
  obtain ⟨-, b₀, hb₀, eb₀, db⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P' F' f₂ hf₂
  obtain ⟨-, g₀, hg₀, eg₀, dg⟩ := GlobalTheory.T.existsUnique_differential_monHom_lieBasis K P F P F g hg
  have hlam₀ : LamEq F'.P₀.L a₀ b₀ F.P₀.L g₀ (𝟙 F.P₀.A) :=
    lamEq_baseChange _ _ (spMap (algebraMap (𝓞 K) K)) P.A P.A P'.A P.A F.P₀.A F.P₀.A F'.P₀.A F.P₀.A
      F.φ F.φ F'.φ F.φ F.fib.2.1.1.w F.fib.2.1.1.w F'.fib.2.1 F.fib.2.1
      P'.L P.L F'.P₀.L F.P₀.L P'.isLB P.isLB F'.P₀.isLB F.P₀.isLB F'.fib.2.2 F.fib.2.2 f₁ f₂ g (𝟙 _) a₀ b₀ g₀ (𝟙 _)
      ea₀ eb₀ eg₀ (by simp) hlam
  obtain ⟨a₁, ha₁, ea⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ'.2.1 a₀
  obtain ⟨b₁, hb₁, eb⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ'.2.1 b₀
  obtain ⟨g₁, hg₁, eg⟩ := NormHom.exists_monHom_lift hφ.2.1 hφ.2.1 g₀
  obtain ⟨-, -, -, -, t₁, t₂, -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q Q.g u Hm χ hA
  obtain ⟨-, -, -, -, t₁', t₂', -⟩ := AHWeil.tangent_and_weil_of_isAH hU Q' Q'.g u' Hm' χ' hA'
  obtain ⟨Φ₁, hΦ₁, -, hΦd₁, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' a₁ ha₁
  obtain ⟨Φ₂, hΦ₂, -, hΦd₂, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L Q.g Q'.g u u' t₁' t₂' b₁ hb₁
  obtain ⟨G, hG, -, hGd, -⟩ :=
    HomLinear.exists_linear_of_isMonHom Q.A Q.A Q.isAb Q.isAb Q.L Q.L Q.g Q.g u u t₁ t₂ g₁ hg₁
  have hlam₁ : LamEq Q'.L a₁ b₁ Q.L g₁ (𝟙 Q.A) :=
    lamEq_baseChange _ _ (spMap s) F.P₀.A F.P₀.A F'.P₀.A F.P₀.A Q.A Q.A Q'.A Q.A φ φ φ' φ
      hφ.2.1.1.w hφ.2.1.1.w hφ'.2.1 hφ.2.1
      F'.P₀.L F.P₀.L Q'.L Q.L F'.P₀.isLB F.P₀.isLB Q'.isLB Q.isLB hφ'.2.2 hφ.2.2 a₀ b₀ g₀ (𝟙 _) a₁ b₁ g₁ (𝟙 _)
      ea eb eg (by simp) hlam₀
  have hweil := weilEq_of_lamEq hL ℂ Q Q Q' Q a₁ b₁ g₁ (𝟙 _) ha₁ hb₁ hg₁ inferInstance hlam₁
  have hherm := (weilEq_iff_hermForm_eq hU hL Q Q Q' Q u u u' u Hm' Hm χ' χ hA' hA a₁ b₁ g₁ (𝟙 _) Φ₁ Φ₂ G
    LinearMap.id hΦ₁ hΦ₂ hG (fun z => by simp)).1 hweil
  have e₁ := map_comb s hφ.2.1 hφ'.2.1 u u' F.basis.1 F'.basis.1 hW hW' t₁' ea hΦd₁ (da M₁ hM₁ c')
  have e₂ := map_comb s hφ.2.1 hφ'.2.1 u u' F.basis.1 F'.basis.1 hW hW' t₁' eb hΦd₂ (db M₂ hM₂ c)
  have e₃ := map_comb s hφ.2.1 hφ.2.1 u u F.basis.1 F.basis.1 hW hW t₁ eg hGd (dg N hN c')
  rw [form_eq h' s Hm' W' _ hform', form_eq h s Hm W _ hform, ← e₁, ← e₂, ← e₃, hherm, LinearMap.id_apply]

theorem gram_images : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
  [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (FA : GenFib A.pol) (FB : GenFib B.pol)
  (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K)) (f₁ f₂ : A.t.G ⟶ B.t.G)
  (M₁ M₂ : (Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) (g : 𝓞 E), FA.IsHerm hA → FB.IsHerm hB →
  IsMonHom f₁ → IsMonHom f₂ →
  WeilEq B.t.PP.L f₁ f₂ A.t.PP.L (A.t.act.act g) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
  FA.IsDiffOf FB f₁ M₁ → FA.IsDiffOf FB f₂ M₂ → ∀ (τ : 𝓞 E →+* 𝓞 K) (s : K →+* ℂ),
  ∀ c ∈ FA.eigLat A.t.act τ, hB.form s (M₂ c) (M₁ c) = s (τ g : K) * hA.form s c c := by
  intro hU hL E _ _ _ H K _ _ σ₁ A B FA FB hA hB f₁ f₂ M₁ M₂ g hhA hhB hf₁ hf₂ hw hM₁ hM₂ τ s c hc
  obtain ⟨r, hr, he⟩ := GlobalTheory.T.exists_lieRepresentation_eigenLattices K A.pol FA (𝓞 E) A.t.act
  have hg : IsMonHom (A.t.act.act g) := A.t.act.hom _
  have hinj : Function.Injective (σ₁.comp (algebraMap (𝓞 K) K)) :=
    σ₁.injective.comp (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  have hlam := (GlobalTheory.T.cubeLBPairingIso_iff_weilPairingCompatible_over_ring hL (𝓞 K) A.pol A.pol B.pol A.pol f₁ f₂ (A.t.act.act g) (𝟙 _) hf₁ hf₂ hg inferInstance ℂ
    (σ₁.comp (algebraMap (𝓞 K) K))).2 inferInstance hinj hw
  have hf := form_diff_eq_pair hU hL K A.pol FA B.pol FB hA hB f₁ f₂ (A.t.act.act g) M₁ M₂ (r g) hhA hhB hf₁ hf₂ hg
    hlam hM₁ hM₂ (hr _) s c c
  have hev : r g c = (τ g : K) • c := ((he τ c).1.1 hc).2 _
  rw [hf]
  erw [hev]
  rw [HermFam.smul_right]

theorem side (hU : ThetaUnifAV) (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {K : Type} [Field K] [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (FA : GenFib A.pol)
    (FB : GenFib B.pol) (hA : HermFam K (Fin FA.P₀.g → K)) (hB : HermFam K (Fin FB.P₀.g → K)) {n : ℕ}
    (f : Fin n → (A.t.G ⟶ B.t.G)) (M : Fin n → ((Fin FA.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))
    (g : Matrix (Fin n) (Fin n) (𝓞 E)) (τ : 𝓞 E →+* 𝓞 K) (Ω : ℝ) (hhA : FA.IsHerm hA) (hhB : FB.IsHerm hB)
    (hf : ∀ a, IsMonHom (f a))
    (hw : ∀ a b, WeilEq B.t.PP.L (f a) (f b) A.t.PP.L (A.t.act.act (g a b)) (𝟙 _)
      (spMap (σ₁.comp (algebraMap (𝓞 K) K))))
    (hM : ∀ a, FA.IsDiffOf FB (f a) (M a)) (hr : latRank K (FA.eigLat A.t.act τ) = 1)
    (hi : ∀ a, Function.Injective (M a))
    (hind : iSupIndep (fun a => Submodule.span K
      (((FA.eigLat A.t.act τ).map ((M a).restrictScalars (𝓞 K)) : Submodule (𝓞 K) _) : Set (Fin FB.P₀.g → K))))
    (hΩ : 2 * deg hA (FA.eigLat A.t.act τ) = Ω) :
    g.det ≠ 0 ∧ deg hB (⨆ a, (FA.eigLat A.t.act τ).map ((M a).restrictScalars (𝓞 K))) =
      n * (Ω / 2) - Real.log |((Algebra.norm ℚ ((g.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  set y : Matrix (Fin n) (Fin n) K := g.map fun x => (τ x : K) with hy
  have hgr : ∀ (s : K →+* ℂ) a b, ∀ c ∈ FA.eigLat A.t.act τ,
      hB.form s (M b c) (M a c) = s (y a b) * hA.form s c c := fun s a b c hc =>
    gram_images hU hL E H K σ₁ A B FA FB hA hB (f a) (f b) (M a) (M b) (g a b) hhA hhB (hf a) (hf b) (hw a b)
      (hM a) (hM b) τ s c hc
  obtain ⟨hne, hdeg⟩ := GlobalTheory.T.deg_iSup_map_rankOne_lattice_of_gram K _ _ hA hB n M _ y (GlobalTheory.CM.DegBound.eigLat_fg FA A.t.act τ) hr hi hind hgr
  have hdet : y.det = ((τ g.det : 𝓞 K) : K) := by
    rw [hy, show (fun x : 𝓞 E => (τ x : K)) = ⇑((algebraMap (𝓞 K) K).comp τ) from rfl, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
    rfl
  refine ⟨fun h0 => hne (by rw [hdet, h0, map_zero]; rfl), ?_⟩
  have hn := GlobalTheory.T.mean_log_norm_embeddings_ringHom_eq E K τ g.det
  rw [hdeg, ← hΩ, hdet]
  have e : (∑ s : K →+* ℂ, Real.log ‖s ((τ g.det : 𝓞 K) : K)‖) / (2 * (Module.finrank ℚ K : ℝ)) =
      Real.log |((Algebra.norm ℚ ((g.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * (Module.finrank ℚ E : ℝ)) := by
    rw [mul_comm (2 : ℝ), ← div_div, hn, div_div, mul_comm]
  rw [e]
  ring

theorem deg_images : CMCurve → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p q : ℕ) (X : CMObj H K ρ σ₁ p q), ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → ∀ gP gQ, IsGram X gP gQ → ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol) (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))) (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ → ∀ (h : HermFam K (Fin FB.P₀.g → K)), FB.IsHerm h → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → gP.det ≠ 0 ∧ gQ.det ≠ 0 ∧ deg h (subP FP FB MP τ) = p * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gP.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) ∧ deg h (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) = q * ((logOm E χ).re / 2) - Real.log |((Algebra.norm ℚ ((gQ.det : 𝓞 E) : E) : ℚ) : ℝ)| / (2 * Module.finrank ℚ E) := by
  intro hC hU hL hE E _ _ _ H K _ _ ρ σ₁ p q X _ χ hχ gP gQ hG FP FQ FB MP MQ hDf h hh τ hτ
  have hD : DegSt := PureDeg.degSt hC hU hL hE
  obtain ⟨hP, hhP⟩ := (LieMetric.exists_unique_isHerm hU hL K _ FP).1
  obtain ⟨hQ, hhQ⟩ := (LieMetric.exists_unique_isHerm hU hL K _ FQ).1
  have hρ : ρ ≠ 0 := fun h0 => by
    have := X.ρ_sq
    rw [h0] at this
    exact H.d_prime.ne_zero (by simpa using this)
  have hτ' : (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)) H.rt = -ρ := by
    have e : (H.bar : 𝓞 E →+* 𝓞 E) H.rt = -H.rt := by simp
    rw [RingHom.comp_apply, e, map_neg, hτ]
  have hne : -ρ ≠ ρ := fun e => hρ (by
    have : (2 : 𝓞 K) * ρ = 0 := by linear_combination -e
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero)
  let FA : ∀ b, GenFib (X.A b).pol := fun b => Bool.rec (motive := fun b => GenFib (X.A b).pol) FQ FP b
  let M : ∀ j : Fin p ⊕ Fin q, (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K) := fun j =>
    Sum.rec (motive := fun j => (Fin (FA j.isLeft).P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)) MP MQ j
  have hM : ∀ j, (FA j.isLeft).IsDiffOf FB (X.φ j) (M j) := by
    rintro (a | a)
    exacts [hDf.1 a, hDf.2 a]
  obtain ⟨-, -, hinj, hind, -⟩ := Indep.letters_independent hU hL E H K ρ σ₁ p q X FA FB M hM
  have hrP := (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A true) FP 1 0 X.split X.typeP X.ρ_sq).1 τ
  have hrQ := (GlobalTheory.T.lieAlgebra_eigenDecomposition_CM_signature E H K ρ (X.A false) FQ 0 1 X.split X.typeM X.ρ_sq).1 (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))
  rw [if_pos hτ] at hrP
  rw [if_neg (by rw [hτ']; exact hne)] at hrQ
  have hΩP : 2 * deg hP (FP.eigLat (X.A true).t.act τ) = (logOm E χ).re := by
    have := hD E H χ hχ K ρ (X.A true) X.split X.ρ_sq X.typeP FP hP hhP τ hτ
    rw [← this, Complex.ofReal_re]
  have hΩQ := NumInh.deg_conjugate_type hD hχ X FQ hhQ hτ'
  have hindP := iSupIndep.comp (f := fun a : Fin p => ((Sum.inl a : Fin p ⊕ Fin q), τ)) hind
    (fun a b e => Sum.inl_injective (congrArg Prod.fst e))
  have hindQ := iSupIndep.comp (f := fun a : Fin q => ((Sum.inr a : Fin p ⊕ Fin q), τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) hind
    (fun a b e => Sum.inr_injective (congrArg Prod.fst e))
  obtain ⟨h1, h2⟩ := side hU hL σ₁ (X.A true) X.B FP FB hP h (fun a => phiP X a) MP gP τ _ hhP hh
    (fun a => (X.lin (Sum.inl a)).1) hG.1 hDf.1 hrP (fun a => hinj (Sum.inl a)) hindP hΩP
  obtain ⟨h3, h4⟩ := side hU hL σ₁ (X.A false) X.B FQ FB hQ h (fun a => phiQ X a) MQ gQ
    (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)) _ hhQ hh (fun a => (X.lin (Sum.inr a)).1) hG.2 hDf.2 hrQ
    (fun a => hinj (Sum.inr a)) hindQ hΩQ
  exact ⟨h1, h3, h2, h4⟩

end GlobalTheory.FlatCM.ImageDeg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DensityInequalityLogOneSubCosSq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.CurveDens

section Abstract

variable {Y : Type} [MeasurableSpace Y] {ν : Measure Y}

theorem integrableOn_and_sub_withDensity {g F : Y → ℝ} {S : Set Y} (hg : Measurable g)
    (hS : MeasurableSet S)
    (h₁ : IntegrableOn F S (ν.withDensity fun y => ENNReal.ofReal (g y)))
    (h₂ : IntegrableOn F S (ν.withDensity fun y => ENNReal.ofReal (-g y))) :
    IntegrableOn (fun y => g y * F y) S ν ∧
      (∫ y in S, F y ∂(ν.withDensity fun y => ENNReal.ofReal (g y))) -
        (∫ y in S, F y ∂(ν.withDensity fun y => ENNReal.ofReal (-g y))) =
      ∫ y in S, g y * F y ∂ν := by
  have m₁ : Measurable fun y => ENNReal.ofReal (g y) := hg.ennreal_ofReal
  have m₂ : Measurable fun y => ENNReal.ofReal (-g y) := hg.neg.ennreal_ofReal
  have t₁ : ∀ᵐ y ∂(ν.restrict S), ENNReal.ofReal (g y) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have t₂ : ∀ᵐ y ∂(ν.restrict S), ENNReal.ofReal (-g y) < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold IntegrableOn at h₁ h₂ ⊢
  rw [restrict_withDensity hS] at h₁ h₂
  rw [restrict_withDensity hS, restrict_withDensity hS]
  have i₁ := (integrable_withDensity_iff_integrable_smul' m₁ t₁).1 h₁
  have i₂ := (integrable_withDensity_iff_integrable_smul' m₂ t₂).1 h₂
  have e : ∀ y, g y * F y =
      (ENNReal.ofReal (g y)).toReal • F y - (ENNReal.ofReal (-g y)).toReal • F y := fun y => by
    rw [ENNReal.toReal_ofReal', ENNReal.toReal_ofReal', smul_eq_mul, smul_eq_mul, ← sub_mul]
    congr 1
    rcases le_total 0 (g y) with h | h
    · simp [h]
    · simp [h]
  refine ⟨(i₁.sub i₂).congr (Eventually.of_forall fun y => (e y).symm), ?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul₀ m₁.aemeasurable t₁,
    integral_withDensity_eq_integral_toReal_smul₀ m₂.aemeasurable t₂, ← integral_sub i₁ i₂]
  exact integral_congr_ae (Eventually.of_forall fun y => (e y).symm)

theorem tendsto_partial_log {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, x ^ (n + 1) / ((n : ℝ) + 1)) atTop
      (𝓝 (-Real.log (1 - x))) := by
  have := (Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rwa [abs_of_nonneg h0])).tendsto_sum_nat
  exact this

theorem partial_log_bound {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (N : ℕ) :
    0 ≤ ∑ n ∈ Finset.range N, x ^ (n + 1) / ((n : ℝ) + 1) ∧
      ∑ n ∈ Finset.range N, x ^ (n + 1) / ((n : ℝ) + 1) ≤ -Real.log (1 - x) := by
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rwa [abs_of_nonneg h0])
  have hn : ∀ n : ℕ, 0 ≤ x ^ (n + 1) / ((n : ℝ) + 1) := fun n => by positivity
  refine ⟨Finset.sum_nonneg fun n _ => hn n, ?_⟩
  rw [← hs.tsum_eq]
  exact hs.summable.sum_le_tsum _ fun n _ => hn n

theorem integral_log_eq_of_forall_pow [IsFiniteMeasure ν] {v D d : Y → ℝ}
    (hv : Measurable v) (hD : Measurable D) (hd : Measurable d)
    (bD : ∃ C, ∀ y, |D y| ≤ C) (bd : ∃ C, ∀ y, |d y| ≤ C)
    (h0 : ∀ y, 0 ≤ v y) (h1 : ∀ᵐ y ∂ν, v y < 1)
    (hi : Integrable (fun y => D y * Real.log (1 - v y)) ν)
    (H : ∀ n : ℕ, ∫ y, (v y ^ (n + 1) * D y + (n + 1) * v y ^ n * (1 - v y) * d y) ∂ν = 0) :
    ∫ y, D y * Real.log (1 - v y) ∂ν = ∫ y, d y ∂ν := by
  obtain ⟨CD, hCD⟩ := bD
  obtain ⟨Cd, hCd⟩ := bd
  have hdi : Integrable d ν := Integrable.of_bound hd.aestronglyMeasurable Cd
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hCd y)
  have hhm : ∀ n : ℕ, Measurable fun y =>
      v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y := fun n =>
    ((hv.pow_const _).mul hD).add
      (((measurable_const.mul (hv.pow_const _)).mul (measurable_const.sub hv)).mul hd)
  have hhi : ∀ n : ℕ, Integrable (fun y =>
      v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y) ν := fun n => by
    refine Integrable.of_bound (hhm n).aestronglyMeasurable (CD + ((n : ℝ) + 1) * Cd) ?_
    filter_upwards [h1] with y hy
    have a0 : 0 ≤ v y ^ (n + 1) := pow_nonneg (h0 y) _
    have a1 : v y ^ (n + 1) ≤ 1 := pow_le_one₀ (h0 y) hy.le
    have b0 : 0 ≤ v y ^ n * (1 - v y) := mul_nonneg (pow_nonneg (h0 y) _) (by linarith)
    have b1 : v y ^ n * (1 - v y) ≤ 1 :=
      mul_le_one₀ (pow_le_one₀ (h0 y) hy.le) (by linarith) (by linarith [h0 y])
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [Real.norm_eq_abs]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg a0]
      calc v y ^ (n + 1) * |D y| ≤ 1 * |D y| := by gcongr
        _ ≤ CD := by simpa using hCD y
    · have e : ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y =
          ((n : ℝ) + 1) * ((v y ^ n * (1 - v y)) * d y) := by ring
      rw [e, abs_mul, abs_mul, abs_of_nonneg hn, abs_of_nonneg b0]
      gcongr
      calc v y ^ n * (1 - v y) * |d y| ≤ 1 * |d y| := by gcongr
        _ ≤ Cd := by simpa using hCd y

  have hQ : ∀ N : ℕ, ∫ y, (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ *
      (v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y))) ∂ν = 0 := fun N => by
    rw [integral_finset_sum _ fun n _ => (hhi n).const_mul _]
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [integral_const_mul]
    have := H n
    push_cast at this
    rw [this, mul_zero]
  have hform : ∀ (N : ℕ) (y : Y), (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ *
      (v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y))) =
      (∑ n ∈ Finset.range N, v y ^ (n + 1) / ((n : ℝ) + 1)) * D y + (1 - v y ^ N) * d y := by
    intro N y
    rw [← geom_sum_mul_neg, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have hlim : Tendsto (fun N : ℕ => ∫ y, (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ *
      (v y ^ (n + 1) * D y + ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y))) ∂ν) atTop
      (𝓝 (∫ y, (-(D y * Real.log (1 - v y)) + d y) ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => |D y * Real.log (1 - v y)| + |d y|)
      (fun N => (Finset.measurable_sum _ fun n _ =>
        measurable_const.mul (hhm n)).aestronglyMeasurable)
      (hi.abs.add hdi.abs) (fun N => ?_) ?_
    · filter_upwards [h1] with y hy
      rw [hform, Real.norm_eq_abs]
      obtain ⟨q0, q1⟩ := partial_log_bound (h0 y) hy N
      have l0 : 0 ≤ -Real.log (1 - v y) :=
        neg_nonneg.2 (Real.log_nonpos (by linarith) (by linarith [h0 y]))
      have p0 : 0 ≤ v y ^ N := pow_nonneg (h0 y) _
      have p1 : v y ^ N ≤ 1 := pow_le_one₀ (h0 y) hy.le
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, abs_mul, abs_of_nonneg q0, mul_comm, ← abs_neg (Real.log _),
          abs_of_nonneg l0]
        gcongr
      · rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - v y ^ N)]
        calc (1 - v y ^ N) * |d y| ≤ 1 * |d y| := by gcongr; linarith
          _ = |d y| := one_mul _
    · filter_upwards [h1] with y hy
      simp_rw [hform]
      have t1 := tendsto_partial_log (h0 y) hy
      have t2 : Tendsto (fun N : ℕ => v y ^ N) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (h0 y) hy
      have := (t1.mul_const (D y)).add ((tendsto_const_nhds (x := (1 : ℝ)).sub t2).mul_const (d y))
      convert this using 2
      ring
  have hz : ∫ y, (-(D y * Real.log (1 - v y)) + d y) ∂ν = 0 := by
    refine tendsto_nhds_unique hlim ?_
    simp_rw [hQ]
    exact tendsto_const_nhds
  rw [integral_add (show Integrable (fun y => -(D y * Real.log (1 - v y))) ν from hi.neg) hdi,
    integral_neg] at hz
  linarith

end Abstract

theorem green_sum : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [CompactSpace (CxPts p σ)] [T2Space (CxPts p σ)] [SecondCountableTopology (CxPts p σ)], Nonempty (AnRead p σ 1) → ∀ (κ κ' δ : AlgChart p σ 1 → CxPts p σ → ℝ), IsDens κ → IsDens κ' → IsDens δ → ∀ (v f : CxPts p σ → ℝ) (S : Set (CxPts p σ)), Continuous v → (∀ y, 0 ≤ v y ∧ v y ≤ 1) → IsOpen S → Sᶜ.Finite → (∀ y ∈ S, v y < 1 ∧ f y = Real.log (1 - v y) / 2) → IntegrableOn f S (part κ) → IntegrableOn f S (part fun c y => -κ c y) → IntegrableOn f S (part κ') → IntegrableOn f S (part fun c y => -κ' c y) → (∀ n : ℕ, total (fun c y => v y ^ (n + 1) * (κ c y - κ' c y) + (n + 1) * v y ^ n * (1 - v y) * δ c y) = 0) → 2 * ((∫ y in S, f y ∂(part κ) - ∫ y in S, f y ∂(part fun c y => -κ c y)) - (∫ y in S, f y ∂(part κ') - ∫ y in S, f y ∂(part fun c y => -κ' c y))) = total δ := by
  intro k _ X p σ _ _ _ hR κ κ' δ hκ hκ' hδ v f S hv hv01 hSo hSf hSv i1 i2 i3 i4 H
  obtain ⟨ν, w, hfin, hno, hdens, hmeas⟩ := GlobalTheory.T.finite_measure_density_exists k X p σ hR
  obtain ⟨g, hg, hgw⟩ := hdens κ hκ
  obtain ⟨g', hg', hgw'⟩ := hdens κ' hκ'
  obtain ⟨d, hd, hdw⟩ := hdens δ hδ
  have p1 := (hmeas κ g hg hgw).1
  have p2 := (hmeas (fun c y => -κ c y) (fun y => -g y) hg.neg
    fun c y hy => by rw [hgw c y hy, neg_mul]).1
  have p3 := (hmeas κ' g' hg' hgw').1
  have p4 := (hmeas (fun c y => -κ' c y) (fun y => -g' y) hg'.neg
    fun c y hy => by rw [hgw' c y hy, neg_mul]).1
  have hSm : MeasurableSet S := hSo.measurableSet
  haveI : NullSingletonClass ν := hno
  have hae : ∀ᵐ y ∂ν, y ∈ S := mem_ae_iff.2 (hSf.measure_zero ν)
  have hres : ν.restrict S = ν := Measure.restrict_eq_self_of_ae_mem hae
  have hF : Set.EqOn f (fun y => Real.log (1 - v y) / 2) S := fun y hy => (hSv y hy).2
  rw [p1] at i1
  rw [p2] at i2
  rw [p3] at i3
  rw [p4] at i4
  obtain ⟨a1, e1⟩ := integrableOn_and_sub_withDensity hg.measurable hSm
    (i1.congr_fun hF hSm) (i2.congr_fun hF hSm)
  obtain ⟨a2, e2⟩ := integrableOn_and_sub_withDensity hg'.measurable hSm
    (i3.congr_fun hF hSm) (i4.congr_fun hF hSm)
  unfold IntegrableOn at a1 a2
  rw [hres] at a1 a2 e1 e2
  have hi : Integrable (fun y => (g y - g' y) * Real.log (1 - v y)) ν :=
    ((a1.sub a2).const_mul 2).congr (Eventually.of_forall fun y => by simp only [Pi.sub_apply]; ring)
  have key := integral_log_eq_of_forall_pow (ν := ν) (v := v) (D := fun y => g y - g' y) (d := d)
    hv.measurable (hg.sub hg').measurable hd.measurable
    (by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hg.sub hg').continuousOn
      exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩)
    (by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hd.continuousOn
      exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩)
    (fun y => (hv01 y).1) (hae.mono fun y hy => (hSv y hy).1) hi
    (fun n => by
      have hc : Continuous fun y => v y ^ (n + 1) * (g y - g' y) +
          ((n : ℝ) + 1) * v y ^ n * (1 - v y) * d y := by fun_prop
      rw [← (hmeas _ _ hc fun c y hy => ?_).2]
      · exact H n
      · rw [hgw c y hy, hgw' c y hy, hdw c y hy]
        ring)
  rw [p1, p2, p3, p4, (hmeas δ d hd hdw).2, ← key,
    setIntegral_congr_fun hSm hF, setIntegral_congr_fun hSm hF,
    setIntegral_congr_fun hSm hF, setIntegral_congr_fun hSm hF, e1, e2, ← integral_sub a1 a2,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  ring

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDerivativesDivJacobianIndependentStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.TangentOrigin
open GlobalTheory.FlagMod GlobalTheory.TopForm
open GlobalTheory.FlagTan (dimFlag psiSet TIx HIx VIx IsTanFrame IsDef IsVert KSIso kap)
open GlobalTheory.AllWt (exOf)
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_derivatives_div_jacobian_independent : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c} (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw)) {K : Type} [Field K] (z : Sp K ⟶ M.X) (i : M.K.bundle.ι)
    (w : Fin (dimFlag Dw) → (Sp (DualNumber K) ⟶ M.X))
    (hw : ∀ b, spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ w b = z)
    (O O' : M.X.Opens) (hO : O ≤ M.K.bundle.U i) (hO' : O' ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (g' : Fin (dimFlag Dw) → Γ(M.X, O'))
    (hz : ⊤ ≤ z ⁻¹ᵁ O) (hz' : ⊤ ≤ z ⁻¹ᵁ O') (hwO : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O) (hwO' : ∀ b, ⊤ ≤ w b ⁻¹ᵁ O'), (Matrix.of fun a b => (evalPt (w b) O (hwO b) (g a)).snd).det * evalPt z O' hz' (M.K.jacobian i hO' g') =
      (Matrix.of fun a b => (evalPt (w b) O' (hwO' b) (g' a)).snd).det * evalPt z O hz (M.K.jacobian i hO g) := by
  first | exact @GlobalTheory.TanJac.det_mul_jacobian_comm | exact GlobalTheory.TanJac.det_mul_jacobian_comm | (intros; apply GlobalTheory.TanJac.det_mul_jacobian_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Dets
section
set_option autoImplicit false

noncomputable section

open NumberField

namespace GlobalTheory.IdxTensor

def dets (F : Type) [Field F] [NumberField F] (p : ℕ) (L : Submodule (𝓞 F) (Fin p → F)) : Submodule (𝓞 F) F :=
  Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ L) ∧ d = (Matrix.of y).det}

example (F : Type) [Field F] [NumberField F] (p : ℕ) :
    (1 : F) ∈ dets F p (Submodule.span (𝓞 F) (Set.range fun a => (Pi.single a (1 : F) : Fin p → F))) :=
  Submodule.subset_span ⟨fun a => Pi.single a 1, fun i => Submodule.subset_span ⟨i, rfl⟩, by
    rw [show (Matrix.of fun a : Fin p => (Pi.single a (1 : F) : Fin p → F)) = 1 from by
      ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]⟩

end GlobalTheory.IdxTensor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilDatumDiagThetaProductEqScalarSmulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledWeilDatum_diag_thetaProduct_eq_scalar_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
      (ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ)),
      Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
      ∀ ωd : GA D S × GA D (GlobalTheory.Doubling.dblSp T) →* Module.End ℂ (Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) → ℂ),
        Formalism.IndefR.Datum.IsWeilDatumO ψ S (GlobalTheory.Doubling.dblSp T) χS 1 ωd →
        ∀ (h : GA D T) (hd : GA D (GlobalTheory.Doubling.dblSp T)),
          Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp T) hd =
            Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.L2.Theta.mt T h) 0 0 1) →
          ∃ c : ℂ, ∀ f₁ f₂ : Formalism.IndefR.Datum.WO S T → ℂ,
            Formalism.IndefR.Datum.IsThetaFunO ψ S T f₁ → Formalism.IndefR.Datum.IsThetaFunO ψ S T f₂ →
              ωd (1, hd) (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) = c • (fun w : Formalism.IndefR.Datum.WO S (GlobalTheory.Doubling.dblSp T) => ω (1, h) f₁ (w.submatrix (finSumFinEquiv ∘ Sum.inl) id) * star (f₂ (w.submatrix (finSumFinEquiv ∘ Sum.inr) id))) := by
  first | exact @GlobalTheory.DblThetaRestrict.scalar | exact GlobalTheory.DblThetaRestrict.scalar | (intros; apply GlobalTheory.DblThetaRestrict.scalar <;> assumption)
end

