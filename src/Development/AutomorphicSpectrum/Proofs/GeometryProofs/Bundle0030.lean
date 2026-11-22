import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEval
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.ValEmb

theorem valAt_pull {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}}
    (j : X ⟶ Spec (CommRingCat.of A)) (x : Spec (CommRingCat.of B) ⟶ X) (ρ : A →+* B)
    (h : x ≫ j = Spec.map (CommRingCat.ofHom ρ)) (f : A) :
    valAt x ⊤ le_top (j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom f)) = ρ f := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop ≫ x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      = CommRingCat.ofHom ρ := by
    have : j.appTop ≫ x.appTop = (Spec.map (CommRingCat.ofHom ρ)).appTop := by
      rw [← h, Scheme.Hom.comp_appTop]
    rw [reassoc_of% this, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  have h2 := congrArg (fun φ => φ.hom f) h1
  have hle : x.appLE ⊤ ⊤ le_top = x.appTop := by
    simp only [Scheme.Hom.appLE]
    exact Category.comp_id _
  simp only [valAt]
  rw [hle]
  simpa using h2

theorem valAt_sub {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valAt x U h (a - b) = valAt x U h a - valAt x U h b := by
  simp [valAt]

theorem val_emb : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → ∀ (f : Γ.btOrder ⊤) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f : T → R) → ∀ (B : Type) [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (ρ : (Γ.btOrder ⊤) →+* B), y ≫ j = Spec.map (CommRingCat.ofHom ρ) → valAt y ⊤ le_top s = ρ f := by
  intro R _ _ T _ _ Γ j hj f s hs B _ y ρ hy
  have hz : s - j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f) = 0 := by
    refine GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤ _ fun t h => ?_
    rw [valAt_sub, hs t, valAt_pull j (Γ.pt t).left _ (hj.pt t) f]
    simp
  rw [sub_eq_zero.mp hz]
  exact valAt_pull j y ρ hy f

end GlobalTheory.CompanionTheory.Ar.BT.ValEmb
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLatticeGeneratorsStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_lattice_generators : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (L : ι → AddSubgroup (Fin r → Ω)),
    (∀ c, ∀ a ∈ chartRing O x c, ∀ e ∈ L c, a • e ∈ L c) →
    (∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ L i, ∃ m : ℕ, (x i / x j) ^ m • e ∈ L j) →
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ L c) ∧
      ∀ e ∈ L c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i j, x i ≠ 0 → x j ≠ 0 → ∀ e ∈ dotDual (chartRing O x i) (L i),
      ∃ m : ℕ, (x i / x j) ^ m • e ∈ dotDual (chartRing O x j) (L j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.dotDual_overlap | exact GlobalTheory.CompanionTheory.Ar.Num.dotDual_overlap | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.dotDual_overlap <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartBundleLocalGenerationStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GlobalTheory.CompanionTheory.Ar.Num (dotDual)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_local_generation : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (ι : Type) (x : ι → Ω) (r : ℕ)
    (B : ChartBundle O x r (Fin r → Ω)),
    (∀ c, x c ≠ 0 → ∃ (n : ℕ) (s : Fin n → Fin r → Ω), (∀ k, s k ∈ B.lat c) ∧
      ∀ e ∈ B.lat c, ∃ a : Fin n → Ω, (∀ k, a k ∈ chartRing O x c) ∧ e = ∑ k, a k • s k) →
    ∀ i, x i ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing O x i) ∧ (∀ l, c l ∈ chartRing O x i) ∧
      ∑ l, c l * f l = 1 ∧ ∀ l, ∃ b : Fin r → Fin r → Ω, LinearIndependent Ω b ∧
        Submodule.span Ω (Set.range b) = ⊤ ∧ ∀ e : Fin r → Ω,
          ((∃ n : ℕ, f l ^ n • e ∈ dotDual (chartRing O x i) (B.lat i)) ↔
            ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing O x i) ∧ e = ∑ q, a q • b q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.chartBundle_dotDual_localFrame | exact GlobalTheory.CompanionTheory.Ar.Num.chartBundle_dotDual_localFrame | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.chartBundle_dotDual_localFrame <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointConjugate
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem evC_conj {K : Type} {ι : K → Type} (z : (Σ k, ι k) → ℂ) (g : MRing ι) :
    evC (fun p => (starRingEnd ℂ) (z p)) g = (starRingEnd ℂ) (evC z g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [evC]
  | add p q hp hq =>
    simp only [evC, Polynomial.map_add, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul, map_X, eval_X] at hp ⊢
    rw [hp]

theorem ptOver_conj : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type)
    [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (σ : F →+* ℂ) (z : (Σ k, ι k) → ℂ),
    PtOver y φ σ z → PtOver y φ (ComplexEmbedding.conjugate σ) (fun p => (starRingEnd ℂ) (z p)) := by
  intro K _ ι _ Ω _ F _ _ y φ σ z h
  obtain ⟨⟨hne, hvan⟩, hrel⟩ := h
  refine ⟨⟨fun k => ?_, fun f hf => ?_⟩, fun a d g h' hg hh e => ?_⟩
  · obtain ⟨i, hi⟩ := hne k
    exact ⟨i, by simpa using hi⟩
  · have := evC_conj z f
    have h0 : evC z f = 0 := hvan f hf
    rw [h0, map_zero] at this
    exact this
  · rw [evC_conj, evC_conj, hrel a d g h' hg hh e, map_mul, ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointExistsUniqueEmbedding
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo

namespace OverUnique

open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {F : Type} [Field F] [NumberField F]

theorem evC_eq_aeval (z : (Σ k, ι k) → ℂ) (g : MRing ι) : evC z g = aeval z g := by
  have h : algebraMap ℤ ℂ = Int.castRingHom ℂ := RingHom.ext_int _ _
  simp only [evC, eval_map, aeval_def, h]

theorem homog_X [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  classical
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k0, i0⟩ := p
  by_cases h : k = k0
  · subst h
    simp [Finsupp.single_apply]
  · have h' : ∀ i : ι k, ¬ ((⟨k0, i0⟩ : Σ k, ι k) = ⟨k, i⟩) := fun i e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, h', h]

theorem homog_sub {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d) :
    IsMultiHomog (g - h) d := by
  rw [sub_eq_add_neg]
  refine isMultiHomog_add hg ?_
  intro m hm
  exact hh m (by simpa using hm)

theorem exists_form (c : ∀ k, ι k) (G : MRing ι) :
    ∃ (D : K → ℕ) (H M : MRing ι), IsMultiHomog H D ∧ IsMultiHomog M D ∧
      ∀ (L : Type) [Field L] (w : (Σ k, ι k) → L), (∀ k, w ⟨k, c k⟩ ≠ 0) →
        aeval w M ≠ 0 ∧ aeval w H = aeval w M * aeval (fun p => w p / w ⟨p.1, c p.1⟩) G := by
  classical
  induction G using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, C a, 1, ?_, isMultiHomog_one, fun L _ w hw => ?_⟩
    · intro m hm k
      have := support_monomial_subset hm
      simp at this
      simp [this]
    · simp
  | add p q hp hq =>
    obtain ⟨D₁, H₁, M₁, h₁, m₁, e₁⟩ := hp
    obtain ⟨D₂, H₂, M₂, h₂, m₂, e₂⟩ := hq
    refine ⟨D₁ + D₂, H₁ * M₂ + H₂ * M₁, M₁ * M₂,
      isMultiHomog_add (isMultiHomog_mul h₁ m₂) (by rw [add_comm D₁]; exact isMultiHomog_mul h₂ m₁),
      isMultiHomog_mul m₁ m₂, fun L _ w hw => ?_⟩
    obtain ⟨n₁, f₁⟩ := e₁ L w hw
    obtain ⟨n₂, f₂⟩ := e₂ L w hw
    refine ⟨by rw [map_mul]; exact mul_ne_zero n₁ n₂, ?_⟩
    simp only [map_add, map_mul, f₁, f₂]
    ring
  | mul_X p i hp =>
    obtain ⟨D, H, M, h, m, e⟩ := hp
    have hX₁ : IsMultiHomog (X i : MRing ι) (Pi.single i.1 1 : K → ℕ) := homog_X i
    have hX₂ : IsMultiHomog (X ⟨i.1, c i.1⟩ : MRing ι) (Pi.single i.1 1 : K → ℕ) :=
      homog_X (⟨i.1, c i.1⟩ : Σ k, ι k)
    have hH := isMultiHomog_mul h hX₁
    have hM := isMultiHomog_mul m hX₂
    refine ⟨_, _, _, hH, hM, fun L _ w hw => ?_⟩
    obtain ⟨n, f⟩ := e L w hw
    have hc := hw i.1
    refine ⟨by rw [map_mul, aeval_X]; exact mul_ne_zero n hc, ?_⟩
    simp only [map_mul, aeval_X, f]
    field_simp

variable {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem aeval_eq_zero {P : MRing ι} {d : K → ℕ} (hz : z ∈ mcPts (mCoordIdeal y)) (hP : IsMultiHomog P d)
    (h0 : aeval y P = 0) : aeval z P = 0 := by
  rw [← evC_eq_aeval]
  exact hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hP h0)

theorem chart_ne {k : K} {i : ι k} (hz : z ∈ mcPts (mCoordIdeal y)) (h : z ⟨k, i⟩ ≠ 0) : y ⟨k, i⟩ ≠ 0 := by
  classical
  intro h0
  apply h
  have := aeval_eq_zero hz (homog_X (⟨k, i⟩ : Σ k, ι k)) (by rw [aeval_X]; exact h0)
  simpa using this

theorem chart_ker (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k} (hc : ∀ k, z ⟨k, c k⟩ ≠ 0)
    (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) {G : MRing ι} (h0 : aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = 0) :
    aeval (fun p => z p / z ⟨p.1, c p.1⟩) G = 0 := by
  obtain ⟨D, H, M, h, m, e⟩ := exists_form c G
  obtain ⟨-, fy⟩ := e Ω y hy
  obtain ⟨nz, fz⟩ := e ℂ z hc
  rw [h0, mul_zero] at fy
  have := aeval_eq_zero hz h fy
  rw [fz] at this
  exact (mul_eq_zero.mp this).resolve_left nz

theorem exists_intHom (φ : F →+* Ω) (hz : z ∈ mcPts (mCoordIdeal y)) {c : ∀ k, ι k}
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (hy : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hG : ∀ a : 𝓞 F, ∃ G : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F)) :
    ∃ τ : 𝓞 F →+* ℂ, ∀ (a : 𝓞 F) (G : MRing ι), aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F) →
      τ a = aeval (fun p => z p / z ⟨p.1, c p.1⟩) G := by
  set v : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩ with hv
  set u : (Σ k, ι k) → ℂ := fun p => z p / z ⟨p.1, c p.1⟩ with hu
  let A : MRing ι →ₐ[ℤ] Ω := aeval v
  let ψ : MRing ι →+* A.range := (A.rangeRestrict : MRing ι →+* A.range)
  let ψ' : MRing ι →+* ℂ := ((aeval u : MRing ι →ₐ[ℤ] ℂ) : MRing ι →+* ℂ)
  have hs : Function.Surjective ψ := A.rangeRestrict_surjective
  have hker : RingHom.ker ψ ≤ RingHom.ker ψ' := by
    intro G hGk
    rw [RingHom.mem_ker] at hGk ⊢
    have h1 : aeval v G = 0 := congrArg Subtype.val hGk
    exact chart_ker hz hc hy h1
  let l : A.range →+* ℂ := RingHom.liftOfSurjective ψ hs ⟨ψ', hker⟩
  have hl : ∀ G, l (ψ G) = ψ' G := fun G =>
    RingHom.liftOfRightInverse_comp_apply ψ _ _ ⟨ψ', hker⟩ G
  let ρ : 𝓞 F →+* A.range := (φ.comp (algebraMap (𝓞 F) F)).codRestrict A.range (fun a => by
    obtain ⟨G, hG'⟩ := hG a
    exact ⟨G, hG'⟩)
  refine ⟨l.comp ρ, fun a G h => ?_⟩
  have : ρ a = ψ G := Subtype.ext h.symm
  rw [RingHom.comp_apply, this, hl]
  rfl

theorem intHom_injective (τ : 𝓞 F →+* ℂ) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  rw [eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, RingHom.mem_ker] at hn
  simpa using hn

end OverUnique

open OverUnique GroundTheory.Heights₂.Heights.LowerBoundFree in

theorem existsUnique_ptOver (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (hO : OverInt y φ) :
    ∀ z ∈ mcPts (mCoordIdeal y), ∃! σ : F →+* ℂ, PtOver y φ σ z := by
  classical
  intro z hz
  choose c hc using hz.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => chart_ne hz (hc k)
  have hG : ∀ a : 𝓞 F, ∃ G : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) G = φ (a : F) := by
    intro a
    have h := hO.2 c hy a
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval] at h
    exact h
  obtain ⟨τ, hτ⟩ := exists_intHom φ hz hc hy hG
  have hinj := intHom_injective τ
  let σ : F →+* ℂ := IsFractionRing.lift hinj
  have hσ : ∀ a : 𝓞 F, σ (a : F) = τ a := fun a => IsFractionRing.lift_algebraMap hinj a
  refine ⟨σ, ⟨hz, fun a d g h hg hh he => ?_⟩, fun σ' hσ' => ?_⟩
  · obtain ⟨a₁, a₂, ha₂, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    have ha₂' : algebraMap (𝓞 F) F a₂ ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha₂
    obtain ⟨G₁, e₁⟩ := hG a₁
    obtain ⟨G₂, e₂⟩ := hG a₂
    obtain ⟨D₁, H₁, M₁, h₁, m₁, f₁⟩ := exists_form c G₁
    obtain ⟨D₂, H₂, M₂, h₂, m₂, f₂⟩ := exists_form c G₂
    obtain ⟨ny₁, y₁⟩ := f₁ Ω y hy
    obtain ⟨ny₂, y₂⟩ := f₂ Ω y hy
    obtain ⟨nz₁, z₁⟩ := f₁ ℂ z hc
    obtain ⟨nz₂, z₂⟩ := f₂ ℂ z hc
    have hP : IsMultiHomog (H₂ * M₁ * g - H₁ * M₂ * h) (D₁ + D₂ + d) := by
      refine homog_sub ?_ (isMultiHomog_mul (isMultiHomog_mul h₁ m₂) hh)
      rw [add_comm D₁]
      exact isMultiHomog_mul (isMultiHomog_mul h₂ m₁) hg
    have h0 : aeval y (H₂ * M₁ * g - H₁ * M₂ * h) = 0 := by
      have hφ : φ (algebraMap (𝓞 F) F a₂) ≠ 0 := by simpa using ha₂'
      simp only [map_sub, map_mul, y₁, y₂, he, e₁, e₂]
      rw [map_div₀]
      field_simp
      ring
    have h1 := aeval_eq_zero hz hP h0
    simp only [map_sub, map_mul, z₁, z₂, ← hτ a₁ G₁ e₁, ← hτ a₂ G₂ e₂, ← evC_eq_aeval z g,
      ← evC_eq_aeval z h, ← hσ] at h1
    have hs₂ : σ (algebraMap (𝓞 F) F a₂) ≠ 0 := by simpa using ha₂'
    rw [map_div₀]
    have hM : aeval z M₁ * aeval z M₂ ≠ 0 := mul_ne_zero nz₁ nz₂
    have h2 : σ (algebraMap (𝓞 F) F a₂) * evC z g = σ (algebraMap (𝓞 F) F a₁) * evC z h := by
      apply mul_left_cancel₀ hM
      linear_combination h1
    field_simp
    linear_combination h2
  · refine RingHom.ext fun a => ?_
    have key : ∀ a : 𝓞 F, σ' (a : F) = σ (a : F) := by
      intro a
      obtain ⟨G, e⟩ := hG a
      obtain ⟨D, H, M, h, m, f⟩ := exists_form c G
      obtain ⟨-, fy⟩ := f Ω y hy
      obtain ⟨nz, fz⟩ := f ℂ z hc
      have hy' : aeval y H = φ (a : F) * aeval y M := by rw [fy, e, mul_comm]
      have h1 := hσ'.2 (a : F) D H M h m hy'
      rw [evC_eq_aeval, evC_eq_aeval, fz] at h1
      rw [hσ, hτ a G e]
      have := mul_left_cancel₀ nz (h1.trans (mul_comm _ _))
      exact this.symm
    obtain ⟨a₁, a₂, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    rw [map_div₀, map_div₀]
    exact congrArg₂ _ (key a₁) (key a₂)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegularStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominates_of_coords_regular : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (X' : Scheme.{0}) (Ω' : Type) [Field Ω'] (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (i : Ω →+* Ω'), CoordTie o ξ x → IsCptGen ξ' → (∀ q : X', genPt ξ' ⤳ q) → (∀ (r : o) (p' : Cpt ξ'), i (algebraMap o Ω r) ∈ regAt ξ' p') → (∀ p' : Cpt ξ', ∃ c, InChart ξ' (fun k => i (x k)) c p') → ∃ f : X' ⟶ X, Dominates ξ' ξ f i ∧ ∀ (p' : Cpt ξ') (c : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c p' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map | exact GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map | (intros; apply GlobalTheory.CompanionTheory.Ar.CoordMap.exists_dominating_map <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCechNerveDiagonalIsoZeroOverBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagDet

theorem alt_triangular {Ω E W : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup W] [Module Ω W] {s : ℕ}
    (f : E [⋀^Fin s]→ₗ[Ω] W) (v w : Fin s → E) (c : Fin s → Ω)
    (h : ∀ i, v i - c i • w i ∈ Submodule.span Ω (w '' {k | k < i})) :
    f v = (∏ i, c i) • f w := by
  classical
  have key : ∀ j : ℕ, f v = f (fun i => if (i : ℕ) < j then c i • w i else v i) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih]
      by_cases hj : j < s
      · obtain ⟨i, rfl⟩ : ∃ i : Fin s, (i : ℕ) = j := ⟨⟨j, hj⟩, rfl⟩
        have hnew : (fun k : Fin s => if (k : ℕ) < i + 1 then c k • w k else v k) =
            Function.update (fun k : Fin s => if (k : ℕ) < i then c k • w k else v k) i (c i • w i) := by
          funext k
          by_cases hk : k = i
          · rw [hk, Function.update_self, if_pos (Nat.lt_succ_self _)]
          · rw [Function.update_of_ne hk]
            have hk' : (k : ℕ) ≠ i := fun h => hk (Fin.ext h)
            by_cases hki : (k : ℕ) < i
            · rw [if_pos hki, if_pos (show (k : ℕ) < i + 1 by omega)]
            · rw [if_neg hki, if_neg (show ¬ ((k : ℕ) < i + 1) by omega)]
        rw [hnew]
        generalize hm : (fun k : Fin s => if (k : ℕ) < i then c k • w k else v k) = m
        have hmi : m i = v i := by
          rw [← hm]
          simp
        have hmk : ∀ k : Fin s, k < i → m k = c k • w k := by
          intro k hk
          rw [← hm]
          simp [Fin.lt_def.1 hk]
        have hzero : ∀ u ∈ Submodule.span Ω (w '' {k | k < i}), f (Function.update m i u) = 0 := by
          intro u hu
          induction hu using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨k, hk, rfl⟩ := hx
            have hki : k ≠ i := ne_of_lt hk
            have hmk' : Function.update m i (w k) k = c k • w k := by
              rw [Function.update_of_ne hki]
              exact hmk k hk
            rw [← Function.update_eq_self k (Function.update m i (w k)), hmk', f.map_update_smul]
            rw [f.map_eq_zero_of_eq _ (i := k) (j := i)
              (by rw [Function.update_self, Function.update_of_ne hki.symm, Function.update_self]) hki,
              smul_zero]
          | zero => exact f.map_coord_zero i (by simp)
          | add x y _ _ hx hy => rw [f.map_update_add, hx, hy, add_zero]
          | smul a x _ hx => rw [f.map_update_smul, hx, smul_zero]
        have hv : v i = c i • w i + (v i - c i • w i) := by abel
        conv_lhs => rw [← Function.update_eq_self i m, hmi, hv, f.map_update_add]
        rw [hzero _ (h i), add_zero]
      · congr 1
        funext k
        have := k.2
        simp [show (k : ℕ) < j by omega, show (k : ℕ) < j + 1 by omega]
  rw [key s]
  have hfun : (fun i : Fin s => if (i : ℕ) < s then c i • w i else v i) = fun i => c i • w i := by
    funext i
    rw [if_pos i.2]
  rw [hfun]
  exact f.toMultilinearMap.map_smul_univ c w

theorem exists_diag {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b b₀ : Fin r → E}
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) :
    ∃ c : Ω, b i - c • b₀ i ∈ flagStep Ω b₀ i := by
  have hb : b i ∈ flagStep Ω b₀ ((i : ℕ) + 1) := by
    rw [← hF]
    exact Submodule.subset_span ⟨i, show (i : ℕ) < (i : ℕ) + 1 by omega, rfl⟩
  have hset : b₀ '' {k : Fin r | (k : ℕ) < (i : ℕ) + 1} = b₀ '' {k | (k : ℕ) < i} ∪ {b₀ i} := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      by_cases h : (k : ℕ) < i
      · exact Or.inl ⟨k, h, rfl⟩
      · right
        have hk' : (k : ℕ) < (i : ℕ) + 1 := hk
        have : k = i := Fin.ext (by omega)
        rw [this, Set.mem_singleton_iff]
    · rintro (⟨k, hk, rfl⟩ | hx)
      · exact ⟨k, show (k : ℕ) < (i : ℕ) + 1 by have : (k : ℕ) < i := hk; omega, rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        exact ⟨i, show (i : ℕ) < (i : ℕ) + 1 by omega, hx.symm⟩
  unfold flagStep at hb ⊢
  rw [hset, Submodule.span_union, Submodule.mem_sup] at hb
  obtain ⟨y, hy, z, hz, hyz⟩ := hb
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
  exact ⟨c, by rw [← hyz, add_sub_cancel_right]; exact hy⟩

end GlobalTheory.CompanionTheory.Ar.FlagDet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorBtOrderStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_denominator_btOrder : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ Γ.btOrder ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank | exact GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.btOrder_full_rank <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagCoefficientRatioIntegralStatement
section
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_coefficient_ratio_integral : ∀ (Ω : Type) [Field Ω] (Li : Type) [AddCommGroup Li] [Module Ω Li] (W : Subring Ω) (r : ℕ) (b₀ b b' : Fin r → Li) (N : Ω) (k : Fin r) (t t' : Ω), LinearIndependent Ω b → (∀ j, flagStep Ω b j = flagStep Ω b₀ j) → (∀ j, flagStep Ω b' j = flagStep Ω b₀ j) → (∀ j, N • b' j ∈ Submodule.span W (Set.range b)) → b k - t • b₀ k ∈ flagStep Ω b₀ k → b' k - t' • b₀ k ∈ flagStep Ω b₀ k → N * (t' / t) ∈ W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem | exact GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem | (intros; apply GlobalTheory.CompanionTheory.Ar.leadCoef_ratio_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTrdegFormulaStatement
section
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_trdeg_formula : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω] (E : Type) [AddCommGroup E] [Module Ω₀ E] (E' : Type) [AddCommGroup E'] [Module Ω E'] (j : E →+ E') (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω₀ E) (b₀ : ∀ σ, Fin (r σ) → E') (d : ℕ), IsGenericFlag (Ω' := Ω) j V b₀ d → Algebra.trdeg Ω₀ Ω = ((∑ σ, r σ * (r σ - 1) / 2 : ℕ) : Cardinal) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagTrdeg.trdeg_of_isGenericFlag <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagTriangularChangeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_flag_triangular_change : ∀ (L Li : Type) [Field L] [AddCommGroup Li] [Module L Li] (r : ℕ) (f b g : Fin r → Li) (v w : Matrix (Fin r) (Fin r) L), LinearIndependent L f → LinearIndependent L b → (∀ k, v k k = 1) → (∀ l k, l < k → v l k = 0) → (∀ l k, k < l → w l k = 0) → (∀ k, w k k ≠ 0) → (∀ k, g k = ∑ j, (v * w) j k • f j) → (∀ i : ℕ, GlobalTheory.CompanionTheory.Ar.flagStep L b i = GlobalTheory.CompanionTheory.Ar.flagStep L g i) → ∃ Tm : Matrix (Fin r) (Fin r) L, (∀ i, b i = ∑ m, Tm i m • ∑ j, v j m • f j) ∧ (∀ i m, i < m → Tm i m = 0) ∧ ∀ i, Tm i i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular | exact GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagChange.adapted_triangular <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GluedLatticeFiniteIndexStatement
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glued_lattice_finite_index : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (T : FinitePlace L → Matrix (Fin n) (Fin n) L), (∀ v, (T v).det ≠ 0) → {v : FinitePlace L | ¬ UnitAt v (T v)}.Finite → (glued T).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧ (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (glued T).toAddSubgroup ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable | exact GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.Comm.glued_commensurable <;> assumption)
end

