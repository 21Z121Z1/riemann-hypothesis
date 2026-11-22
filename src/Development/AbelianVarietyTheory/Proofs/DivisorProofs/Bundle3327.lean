import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedConjClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3313
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3314
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3309
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCosetsAndFixedPoints
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinPtsSep
open scoped Pointwise in
open IsDedekindDomain GlobalTheory.OrbFinAf GlobalTheory.OrbFinAf.AwayIrr in

theorem fin_cosets_away_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y₀ : grp G β), (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → ∃ R : Finset G.GAf, ∀ h : G.GAf, f (h⁻¹ * toAfF G β x t hx y₀ * h) ≠ 0 → ∃ c : G.GAf, c * toAfF G β x t hx y₀ = toAfF G β x t hx y₀ * c ∧ ∃ r ∈ R, ∃ k ∈ L.K.toSubgroup, h = c * r * k := by
  intro p _ G L f hf β x t hx y₀ hsep0 hdeg
  set y : G.Cˣ := (y₀ : G.Cˣ × ℚˣ).1 with hy
  have hsep : (minpoly G.F (y : G.C)).Separable := hsep0
  set γ := toAfF G β x t hx y₀ with hγ
  have hg0 : ∀ v, ((piV G v γ : (Qv v ⊗[ℚ] G.C)ˣ × (Qv v)ˣ).1 : (Qv v ⊗[ℚ] G.C)ˣ) =
      xV G x v * yV G y v * (xV G x v)⁻¹ := fun v => piV_toAfF_fst G β x t hx y₀ v
  set T := GlobalTheory.BCT.twCent (MonoidHom.id G.GAf) γ with hT
  set K := L.K.toSubgroup with hK
  obtain ⟨S, hSf⟩ := hf.2.2.2
  let Ω : Set G.GAf := ⋃ s ∈ S, (fun k : G.GAf × G.GAf => k.1 * s * k.2) '' ((K : Set G.GAf) ×ˢ (K : Set G.GAf))
  have hΩ : IsCompact Ω := S.isCompact_biUnion fun s _ =>
    (L.compact.prod L.compact).image ((continuous_fst.mul continuous_const).mul continuous_snd)
  have hsupp : ∀ g : G.GAf, f g ≠ 0 → g ∈ Ω := by
    intro g hg
    obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, e⟩ := hSf g hg
    exact Set.mem_biUnion hs ⟨(k₁, k₂), ⟨hk₁, hk₂⟩, e.symm⟩
  let Good : Set (AwayP p) := {v | piV G v '' Ω ⊆ IntV G v ∧
    (∀ g : Gv G v, g⁻¹ * piV G v γ * g ∈ IntV G v → ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (piV G v γ),
      ∃ d ∈ IntV G v, g = c * d) ∧ ∀ a ∈ IntV G v, ∀ b ∈ IntV G v, a * b ∈ IntV G v}
  have hGood : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), v ∈ Good := by
    filter_upwards [GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral p G Ω hΩ, kottwitz_almost' G y hdeg hsep x (fun v => piV G v γ) hg0, GlobalTheory.T.eventually_integralUnitaryPointsAtPlace_mul_mem p G]
      with v h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hL1 := fun v : AwayP p => local_fin' G v y hdeg hsep (xV G x v) (piV G v γ) (hg0 v) (piV G v '' Ω)
    (hΩ.image (GlobalTheory.T.continuous_unitaryAdelicComponentAtPlace_explicit p G v))
  choose D₁ hD₁ hD₁g using hL1
  let D' : ∀ v : AwayP p, Set (Gv G v) := fun v => if v ∈ Good then IntV G v else D₁ v
  have hD'c : ∀ v, IsCompact (D' v) := by
    intro v; by_cases hv : v ∈ Good
    · simp only [D', if_pos hv]; exact GlobalTheory.T.isCompact_integralUnitaryPointsAtPlace p G v
    · simp only [D', if_neg hv]; exact hD₁ v
  have hD'i : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), D' v ⊆ IntV G v := by
    filter_upwards [hGood] with v hv
    simp only [D', if_pos hv]; exact le_rfl
  have key : ∀ g : G.GAf, g⁻¹ * γ * g ∈ Ω → ∃ c ∈ T, ∃ d ∈ {g : G.GAf | ∀ v, piV G v g ∈ D' v}, g = c * d := by
    intro g hg
    have hloc : ∀ v, ∃ c ∈ GlobalTheory.BCT.twCent (MonoidHom.id (Gv G v)) (piV G v γ), ∃ d ∈ D' v, piV G v g = c * d := by
      intro v
      have hgv : (piV G v g)⁻¹ * piV G v γ * piV G v g ∈ piV G v '' Ω :=
        ⟨_, hg, by simp only [map_mul, map_inv]⟩
      by_cases hv : v ∈ Good
      · obtain ⟨c, hc, d, hd, e⟩ := hv.2.1 _ (hv.1 hgv)
        exact ⟨c, hc, d, by simp only [D', if_pos hv]; exact hd, e⟩
      · obtain ⟨c, hc, d, hd, e⟩ := hD₁g v _ hgv
        exact ⟨c, hc, d, by simp only [D', if_neg hv]; exact hd, e⟩
    choose c hc d hd e using hloc
    have hcint : ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), c v ∈ IntV G v := by
      filter_upwards [GlobalTheory.T.eventually_compact_unitaryAdelic_image_integral p G {g} isCompact_singleton, hGood] with v h1 h2
      have hdv : d v ∈ IntV G v := by have := hd v; simp only [D', if_pos h2] at this; exact this
      have ec : c v = piV G v g * (d v)⁻¹ := by rw [e v]; group
      rw [ec]
      exact h2.2.2 _ (h1 ⟨g, rfl, rfl⟩) _ (inv_mem_IntV G v hdv)
    obtain ⟨tt, htt⟩ := GlobalTheory.T.exists_unitaryAdelicPoint_of_eventually_integral_local p G c hcint
    refine ⟨tt, ?_, tt⁻¹ * g, ?_, by group⟩
    · show tt * γ = γ * (MonoidHom.id _) tt
      apply GlobalTheory.T.unitaryAdelicPoint_ext_of_components p G
      intro v
      have h1 : c v * piV G v γ = piV G v γ * (MonoidHom.id _) (c v) := hc v
      simp only [map_mul, htt, MonoidHom.id_apply] at h1 ⊢
      exact h1
    · intro v
      have : piV G v (tt⁻¹ * g) = d v := by rw [map_mul, map_inv, htt, e v]; group
      rw [this]; exact hd v
  set D := {g : G.GAf | ∀ v, piV G v g ∈ D' v}
  have hD : IsCompact D := GlobalTheory.T.isCompact_unitaryAdelic_prod_local_compacts p G D' hD'c hD'i
  obtain ⟨I, hI⟩ := hD.elim_finite_subcover (fun d : G.GAf => d • (K : Set G.GAf))
    (fun d => L.K.isOpen.smul d) (fun d _ => Set.mem_iUnion.2 ⟨d, ⟨1, one_mem _, mul_one d⟩⟩)
  refine ⟨I, fun h hh => ?_⟩
  obtain ⟨c, hc, d, hd, e⟩ := key _ (hsupp _ hh)
  obtain ⟨i, hi, hdi⟩ := Set.mem_iUnion₂.1 (hI hd)
  obtain ⟨k, hk, rfl⟩ := hdi
  refine ⟨c, hc, i, hi, k, hk, ?_⟩
  rw [e]; simp only [smul_eq_mul]; group

end GlobalTheory.FinPtsSep

noncomputable section

namespace GlobalTheory.FinPtsSep

variable {p : ℕ} [Fact p.Prime]

theorem exists_finset_doubleCoset_cover_of_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (y₀ : grp G β),
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    ∃ R : Finset (Gr G 1), ∀ h : Gr G 1, f' (h⁻¹ * toP1 G β y₀ * h) ≠ 0 →
      ∃ c : Gr G 1, c * toP1 G β y₀ = toP1 G β y₀ * c ∧ ∃ r ∈ R, ∃ k ∈ K', h = c * r * k := by
  intro p _ G K' f' hT β y₀ hsep hdeg
  obtain ⟨hcomm, -, -, S₀, hS₀⟩ := hT
  obtain ⟨S, hS⟩ := GlobalTheory.FinAtP.prod_fin G (toP1 G β y₀)
    (fun w => by rw [GlobalTheory.FinAtP.charpoly_formGroupToPadicPoints_component]; exact (GlobalTheory.FinAtP.rho_charpoly_sep G w _ hdeg hsep).map) S₀
  obtain ⟨T, hT⟩ := GlobalTheory.FinAtP.exists_finset_cosets (KHT p G.m G.n 1 G.Fw) K' hcomm.1
  refine ⟨(S ×ˢ T).image fun x => x.1 * x.2, fun h hh => ?_⟩
  obtain ⟨a, ha, s, hs, k, hk, rfl⟩ := hS h (hS₀ _ hh)
  obtain ⟨t, ht, k', hk', rfl⟩ := hT k hk
  exact ⟨a, ha, s * t, Finset.mem_image.2 ⟨(s, t), Finset.mem_product.2 ⟨hs, ht⟩, rfl⟩, k', hk', by group⟩

theorem posV_toV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : PosV G v β) :
    0 < (star ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (herm G v β *ᵥ ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1))).re := by
  have hs := GlobalTheory.LKCx.grp_similitude_herm p G v β y
  have e : star ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (herm G v β *ᵥ ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1)) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) * (star z.1 ⬝ᵥ (herm G v β *ᵥ z.1)) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hs, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [e]
  have hpos : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
  rw [show (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) = ((((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ)) : ℂ) by push_cast; rfl,
    Complex.re_ofReal_mul]
  exact mul_pos (by exact_mod_cast hpos) z.2

def mapPosV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : PosV G v β) : PosV G v β :=
  ⟨(toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1, posV_toV G v β y z⟩

def conjC (G : HTGroup p) (y : G.Cˣ) : G.C ≃ₐ[G.F] G.C where
  toFun x := y * x * ((y⁻¹ : G.Cˣ) : G.C)
  invFun x := ((y⁻¹ : G.Cˣ) : G.C) * x * y
  left_inv x := by simp [_root_.mul_assoc]
  right_inv x := by simp [_root_.mul_assoc]
  map_mul' a b := by simp [_root_.mul_assoc]
  map_add' a b := by simp [mul_add, add_mul]
  commutes' a := by
    show (y : G.C) * algebraMap G.F G.C a * ((y⁻¹ : G.Cˣ) : G.C) = algebraMap G.F G.C a
    rw [← Algebra.commutes, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

theorem minpoly_conjC (G : HTGroup p) (y g : G.Cˣ) :
    minpoly G.F ((y * g * y⁻¹ : G.Cˣ) : G.C) = minpoly G.F (g : G.C) := by
  have := minpoly.algEquiv_eq (conjC G y) (g : G.C)
  rw [← this]
  rfl

theorem fixL_conj (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (g y : grp G β) (z : Fin G.n → ℂ)
    (h : FixL G v β (g * y * g⁻¹) z) : FixL G v β y ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  have e : y * g⁻¹ = g⁻¹ * (g * y * g⁻¹) := by group
  calc (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z)
      = (toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β (g * y * g⁻¹) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul, e]
    _ = c • ((toV G v β g⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z) := by rw [hc, Matrix.mulVec_smul]

theorem finite_pts_conj_fixL_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, Set.Finite {q : Pts G v β x t hx L.K.toSubgroup K' | ∃ γ : grp G β, FixL G v β (γ * y₀ * γ⁻¹) (Quot.out q).2.1 ∧ f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * (Quot.out q).1.1) * f' ((Quot.out q).1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * (Quot.out q).1.2) ≠ 0} := by
  intro p _ G ha v hv L f hf K' f' hf' β x t hx hsees hsym htr y₀
  classical
  by_cases hne : ∃ (b : Dat G v β) (γ : grp G β), FixL G v β (γ * y₀ * γ⁻¹) b.2.1 ∧
      f (b.1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * b.1.1) * f' (b.1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * b.1.2) ≠ 0
  swap
  · convert Set.finite_empty
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨γ, h1, h2⟩
    exact hne ⟨_, γ, h1, h2⟩
  obtain ⟨b₀, γ₀, hfix₀, hne₀⟩ := hne
  have hsd : (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧
      (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable := by
    have h := hsees (γ₀ * y₀ * γ₀⁻¹) b₀.1.1 (left_ne_zero_of_mul hne₀) ⟨b₀.2.1, b₀.2.2, hfix₀⟩
    have e : (((γ₀ * y₀ * γ₀⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) =
        ((γ₀ : G.Cˣ × ℚˣ).1) * ((y₀ : G.Cˣ × ℚˣ).1) * ((γ₀ : G.Cˣ × ℚˣ).1)⁻¹ := by simp
    rw [e, minpoly_conjC] at h
    exact h
  let z₀ : PosV G v β := mapPosV G v β γ₀⁻¹ b₀.2
  have hz₀ : FixL G v β y₀ z₀.1 := fixL_conj G v β γ₀ y₀ _ hfix₀
  obtain ⟨R1, hR1⟩ := fin_cosets_away_sep p G L f hf β x t hx y₀ hsd.2 hsd.1
  obtain ⟨R2, hR2⟩ := exists_finset_doubleCoset_cover_of_separable p G K' f' hf' β y₀ hsd.2 hsd.1
  have h3 := GlobalTheory.T.finite_classNumber_centraliserTorus_separable p G L K' hf'.1 β x t hx hsym y₀ hsd.2 hsd.1
  choose R3 hR3 using h3
  let Fs : Finset (G.GAf × Gr G 1) := (R1 ×ˢ R2).biUnion R3
  refine (Fs.finite_toSet.image (fun s => (Quot.mk _ (s, z₀) : Pts G v β x t hx L.K.toSubgroup K'))).subset ?_
  rintro q ⟨γ, hfix, hne⟩
  have hq : Quot.mk (Same G v β x t hx L.K.toSubgroup K') (Quot.out q) = q := Quot.out_eq q
  generalize Quot.out q = b at hfix hne hq
  have e1 : (toAfF G β x t hx γ⁻¹ * b.1.1)⁻¹ * toAfF G β x t hx y₀ * (toAfF G β x t hx γ⁻¹ * b.1.1) =
      b.1.1⁻¹ * toAfF G β x t hx (γ * y₀ * γ⁻¹) * b.1.1 := by
    simp only [map_mul, map_inv]; group
  have e2 : (toP1 G β γ⁻¹ * b.1.2)⁻¹ * toP1 G β y₀ * (toP1 G β γ⁻¹ * b.1.2) =
      b.1.2⁻¹ * toP1 G β (γ * y₀ * γ⁻¹) * b.1.2 := by
    simp only [map_mul, map_inv]; group
  obtain ⟨c1, hc1, r1, hr1, k1, hk1, hh1⟩ := hR1 _ (by rw [e1]; exact left_ne_zero_of_mul hne)
  obtain ⟨c2, hc2, r2, hr2, k2, hk2, hh2⟩ := hR2 _ (by rw [e2]; exact right_ne_zero_of_mul hne)
  obtain ⟨y, hy, s, hs, k3, hk31, hk32, hcr⟩ := hR3 (r1, r2) (c1, c2) (Prod.ext hc1 hc2)
  have hfix' : FixL G v β y₀ (mapPosV G v β γ⁻¹ b.2).1 := fixL_conj G v β γ y₀ _ hfix
  let w : PosV G v β := mapPosV G v β y⁻¹ (mapPosV G v β γ⁻¹ b.2)
  have hw : FixL G v β y₀ w.1 := by
    have e : y * y₀ * y⁻¹ = y₀ := by rw [hy]; group
    exact fixL_conj G v β y y₀ _ (by rw [e]; exact hfix')
  obtain ⟨c, hc⟩ := GlobalTheory.LKCx.fixL_pos_unique_of_sep p G v hv β hsym htr y₀ hsd.1 hsd.2 z₀.1 w.1 z₀.2 w.2 hz₀ hw
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h := w.2
    rw [hc, zero_smul] at h
    simp at h
  have hb2 : b.2.1 = c • ((toV G v β (γ * y) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z₀.1) := by
    rw [← Matrix.mulVec_smul, ← hc]
    show b.2.1 = (toV G v β (γ * y) : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ
      ((toV G v β y⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ ((toV G v β γ⁻¹ : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ b.2.1))
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    simp
  have hb1 : b.1 = ((toAfF G β x t hx (γ * y), toP1 G β (γ * y)) : G.GAf × Gr G 1) * s * (k3 * (k1, k2)) := by
    have hh : ((toAfF G β x t hx γ⁻¹ * b.1.1, toP1 G β γ⁻¹ * b.1.2) : G.GAf × Gr G 1) =
        (c1, c2) * (r1, r2) * (k1, k2) := Prod.ext hh1 hh2
    rw [hcr] at hh
    have hb : b.1 = ((toAfF G β x t hx γ, toP1 G β γ) : G.GAf × Gr G 1) *
        ((toAfF G β x t hx γ⁻¹ * b.1.1, toP1 G β γ⁻¹ * b.1.2) : G.GAf × Gr G 1) := by
      ext <;> simp [← mul_assoc]
    rw [hb, hh]
    ext <;> simp [mul_assoc]
  have hsF : s ∈ Fs := Finset.mem_biUnion.2 ⟨(r1, r2), Finset.mem_product.2 ⟨hr1, hr2⟩, hs⟩
  refine ⟨s, hsF, ?_⟩
  rw [← hq]
  exact Quot.sound ⟨γ * y, k3 * (k1, k2), c, mul_mem hk31 hk1, mul_mem hk32 hk2, hc0, hb1, hb2⟩

end GlobalTheory.FinPtsSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankHopfAlgebraEqRangeMulKernel
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_eq_range_mul_ker : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A]
    [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
    [Module.Finite k C] (f : C →ₐc[k] A),
    Module.finrank k A = Module.finrank k (LinearMap.range (f : C →ₐ[k] A).toLinearMap) *
      Module.finrank k (A ⧸ kerIdeal f) := by
  intro k _ A _ _ _ _ C _ _ _ _ f
  rw [GlobalTheory.PDiv.finrank_eq_ker_mul_range k A C f, mul_comm]

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotKernelIdealEqBeyondExponent
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem finrank_quot_kerIdeal_succ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G Q : PDivGroup p k)
    (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G) (h : q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G) (hmn : m ≤ n) :
    Module.finrank k (G.A (n + 1) ⧸ kerIdeal (q.app (n + 1))) =
      Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) := by
  have h1 : Hom.app (q ≫ q') (n + 1) = mulBy k (G.A (n + 1)) (p ^ m) := by
    rw [h, ← Nat.cast_pow, natCast_smul_id_app]
  have h2 : torsionIdeal k (G.A (n + 1)) (p ^ m) ≤ kerIdeal (q.app (n + 1)) := by
    rw [torsionIdeal, ← h1, comp_app, kerIdeal_comp]
    refine Ideal.map_mono ((kerIdeal_le_ker_iff _ (counitAlgHom k _)).2 fun c => ?_)
    simp
  have h3 : RingHom.ker (G.res n : G.A (n + 1) →ₐ[k] G.A n) ≤ kerIdeal (q.app (n + 1)) :=
    (G.ker_res n).le.trans ((torsionIdeal_le_of_dvd (pow_dvd_pow p hmn)).trans h2)
  have h4 : Ideal.map (G.res n : G.A (n + 1) →ₐ[k] G.A n) (kerIdeal (q.app (n + 1))) =
      kerIdeal (q.app n) := by
    rw [← kerIdeal_comp, q.comm n, kerIdeal_comp_of_surjective _ (Q.res_surjective n)]
  have hs : Function.Surjective (G.res n : G.A (n + 1) →ₐ[k] G.A n) := G.res_surjective n
  have hc : Ideal.comap (G.res n : G.A (n + 1) →ₐ[k] G.A n) (kerIdeal (q.app n)) =
      kerIdeal (q.app (n + 1)) := by
    rw [← h4, Ideal.comap_map_of_surjective _ hs, ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.2 h3
  let e := Ideal.quotientMapₐ (kerIdeal (q.app n)) (G.res n : G.A (n + 1) →ₐ[k] G.A n) hc.ge
  have he : Function.Bijective e :=
    ⟨Ideal.quotientMap_injective' (H := hc.ge) hc.le, Ideal.quotientMap_surjective (H := hc.ge) hs⟩
  exact (AlgEquiv.ofBijective e he).toLinearEquiv.finrank_eq

theorem finrank_quot_kerIdeal_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G Q : PDivGroup p k) (m n : ℕ) (q : G ⟶ Q) (q' : Q ⟶ G),
    q ≫ q' = (p : ℤ_[p]) ^ m • 𝟙 G → m ≤ n →
      Module.finrank k (G.A n ⧸ kerIdeal (q.app n)) = Module.finrank k (G.A m ⧸ kerIdeal (q.app m)) := by
  intro p _ k _ _ G Q m n q q' h hmn
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih => exact (finrank_quot_kerIdeal_succ p k G Q m n q q' h hmn).trans ih

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSuccessiveQuotientLine
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.OmitStep

theorem omitStep_bundle : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k)
    (d D : ℕ), IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι]
    (E : ι → B.Modules) (r : ι → ℕ), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) →
    ∀ (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl →
    ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 →
    ∃ (Y₁ : Scheme.{0}) (σ : Y₁ ⟶ B) (ρ : Y ⟶ Y₁) (wσ : ρ ≫ σ = π) (S P E₁ : Y₁.Modules) (s : S ⟶ P)
      (j : P ⟶ (Scheme.Modules.pullback σ).obj (E a)) (t : P ⟶ E₁) (wst : s ≫ t = 0)
      (fl₁ : Vert.Flag ((Scheme.Modules.pullback ρ).obj E₁) 2) (A₀ A₁ : (Σ b, Fin (r b)) → Y₁.Modules)
      (u : ∀ z, A₀ z ⟶ A₁ z) (v : ∀ z, A₁ z ⟶ (Scheme.Modules.pullback σ).obj (E z.1)),
      IsIntegral Y₁ ∧ IsProjOver (σ ≫ q) ∧ Surjective ρ ∧ topologicalKrullDim Y = topologicalKrullDim Y₁ + 1 ∧
      IsFlagBundle ρ (fun _ : Unit => E₁) (fun _ => 2) (fun _ => fl₁) ∧
      (ShortComplex.mk s t wst).ShortExact ∧ GlobalTheory.VB.IsSubbundle s ∧ GlobalTheory.VB.IsSubbundle j ∧ GlobalTheory.VB.IsVB S i ∧
      GlobalTheory.VB.IsVB P ((i : ℕ) + 2) ∧ GlobalTheory.VB.IsVB E₁ 2 ∧
      (∃ e : (Scheme.Modules.pullback ρ).obj P ≅ (fl a).F i'.succ, e.hom ≫ (fl a).ι i'.succ =
        (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a)) ∧
      (∃ e : (Scheme.Modules.pullback ρ).obj S ≅ (fl a).F i.castSucc, e.hom ≫ (fl a).ι i.castSucc =
        (Scheme.Modules.pullback ρ).map (s ≫ j) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a)) ∧
      (∃ (x : (fl a).F i.succ ⟶ (Scheme.Modules.pullback ρ).obj P) (g : (fl a).F i.succ ⟶ fl₁.F 1),
        x ≫ (Scheme.Modules.pullback ρ).map j ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E a) ≫
          (Scheme.Modules.pullbackCongr wσ).hom.app (E a) = (fl a).ι i.succ ∧
        g ≫ fl₁.ι 1 = x ≫ (Scheme.Modules.pullback ρ).map t ∧ Epi g) ∧
      ∀ z : Σ b, Fin (r b), z ≠ ⟨a, i⟩ → z ≠ ⟨a, i'⟩ →
        GlobalTheory.VB.IsSubbundle (u z) ∧ GlobalTheory.VB.IsSubbundle (v z) ∧ GlobalTheory.VB.IsVB (A₀ z) z.2 ∧
        GlobalTheory.VB.IsVB (A₁ z) ((z.2 : ℕ) + 1) ∧
        (∃ e : (Scheme.Modules.pullback ρ).obj (A₁ z) ≅ (fl z.1).F z.2.succ, e.hom ≫ (fl z.1).ι z.2.succ =
          (Scheme.Modules.pullback ρ).map (v z) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E z.1) ≫
            (Scheme.Modules.pullbackCongr wσ).hom.app (E z.1)) ∧
        (∃ e : (Scheme.Modules.pullback ρ).obj (A₀ z) ≅ (fl z.1).F z.2.castSucc, e.hom ≫ (fl z.1).ι z.2.castSucc =
          (Scheme.Modules.pullback ρ).map (u z ≫ v z) ≫ (Scheme.Modules.pullbackComp ρ σ).hom.app (E z.1) ≫
            (Scheme.Modules.pullbackCongr wσ).hom.app (E z.1)) := by
  intro k _ B Y _ _ q p d D hq hp π w ι _ E r hE fl hfl a i i' hi
  haveI : IsNoetherianRing k := by
    haveI := hq.finite
    exact isNoetherian_of_tower ℤ (inferInstance : IsNoetherian ℤ k)
  obtain ⟨Y₁, σ, ρ, wσ, S, P, E₁, s, j, t, wst, fl₁, A₀, A₁, u, v, hpr, hfb, hrest⟩ :=
    GlobalTheory.T.flag_bundle_successive_projection k B q hq.isProjOver Y π ι E r hE fl hfl a i i' hi
  have hE₁ : GlobalTheory.VB.IsVB E₁ 2 := hrest.2.2.2.2.2.1
  refine ⟨Y₁, σ, ρ, wσ, S, P, E₁, s, j, t, wst, fl₁, A₀, A₁, u, v,
    GlobalTheory.T.flag_bundle_integral_base Y Y₁ ρ E₁ fl₁ hp.isIntegral hE₁ hfb, hpr,
    ⟨GlobalTheory.FlagSurj.isFlagBundle_surjective Y₁ Y ρ Unit (fun _ => E₁) (fun _ => 2) (fun _ => fl₁) (fun _ => hE₁) hfb⟩,
    GlobalTheory.T.flag_bundle_dim_plus_one k Y Y₁ p ρ E₁ fl₁ hp.isProjOver hE₁ hfb, hfb, hrest⟩

end GlobalTheory.OmitStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatWeightPairProductUnitStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_weight_pair_product_unit : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (n : ℤ) (Z : Comp Y.d.Xo₂ Y.d.c₂) (τ : Psi T.Q.H) (s i : Rul Y.d.Xo₂ Y.d.c₂), (s ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ i ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ (-Formalism.L2.Pj.exZ (T.Q.Dw j) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * i = i ∧ s * i = GlobalTheory.FlatLine.idem Z ∧ (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0) s z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) (-(wtOf (T.Q.Dw j) (n • GlobalTheory.FlatLine.flatWt (T.Q.Dw j) τ) 0)) i z ≤ C)) → ∃ m : ℕ, 0 < m ∧ ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, 0 ≤ v ((m : Y.d.c₂.F) • s) ∧ 0 ≤ v ((m : Y.d.c₂.F) • i) := by
  first | exact @GlobalTheory.FlatUnitInt.integral_inverse | exact GlobalTheory.FlatUnitInt.integral_inverse | (intros; apply GlobalTheory.FlatUnitInt.integral_inverse <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFunctionsExistsGlobalFunctionOfThickeningsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalFunctions_exists_globalFunction_of_thickenings : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (I : Ideal A), IsAdicComplete I A → ∀ (X : Over (Sp A)), IsProper X.hom → ∀ f : ∀ e : ℕ, Γ((thickObj A I e X).left, ⊤), (∀ e, (thickMap A I e X).appTop.hom (f (e + 1)) = f e) → ∃ s : Γ(X.left, ⊤), ∀ e, (pullback.fst X.hom (thick A I e)).appTop.hom s = f e := by
  first | exact @GlobalTheory.FormalFunctions.exists_of_thick | exact GlobalTheory.FormalFunctions.exists_of_thick | (intros; apply GlobalTheory.FormalFunctions.exists_of_thick <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagGradedLineChernFormsSmoothDbarClosed
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernCalc.GradedForm

variable {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ}

def lineGram (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (x : Root m) (y z : CxPts X.str σ) :
    Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => ((grD (gramAt E H x.1 y z) x.2 : ℝ) : ℂ)

variable [Finite ι] {E : Fr (ratOf X) m m} {H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ}

theorem grD_pos (h : IsMetricFr E H) (x : Root m) (y : CxPts X.str σ) : 0 < grD (gramAt E H x.1 y y) x.2 :=
  ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ (h.posDef y _ (E.nonempty (under y)).choose_spec x.1)).2.1 x.2).1

theorem lineGram_smooth (h : IsMetricFr E H) (x : Root m) (y : CxPts X.str σ) :
    SmoothUnitAt (atlas X σ) (lineGram E H x y) y := by
  refine ⟨?_, fun c hc => ?_⟩
  · rw [Matrix.det_fin_one]
    exact isUnit_iff_ne_zero.2 (Complex.ofReal_ne_zero.2 (grD_pos h x y).ne')
  · filter_upwards [(GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m m E H h y _ (E.nonempty (under y)).choose_spec x.1).2 c hc] with v hv
    intro a b
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp v ((GlobalTheory.T.gramLowerTriangularFactor_gradedLength_smooth _ _ _ v hv.1 hv.2).2 x.2)

theorem isGramPair_lineGram (h : IsMetricFr E H) (x : Root m) :
    IsGramPair (atlas X σ) (lineGram E H x) (lineGram E H x) := by
  refine ⟨fun y => ⟨lineGram_smooth h x y, lineGram_smooth h x y⟩, fun y => ?_⟩
  have hy := (E.nonempty (under y)).choose_spec
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E y _ hy] with z hyz
  have hz := (E.nonempty (under z)).choose_spec
  set A := (E.nonempty (under y)).choose with hA
  set B := (E.nonempty (under z)).choose with hB
  have hP := (Fr.mem_iff hyz).1 hz
  have hhol := GlobalTheory.T.isHolomorphicUnitMatrixAt_rational_matrix_values F σ X _ ((B * A⁻¹) x.1) z (fun i j => mem_O_ratOf.1 ((hP x.1).1 i j)) (hP x.1).2.1
    (mem_O_ratOf.1 (hP x.1).2.2.1)
  have hval : ∀ w : CxPts X.str σ, A ∈ E.S (under w) → B ∈ E.S (under w) →
      Par m ⊤ ((B * A⁻¹).map (ratVal · w)) := fun w h1 h2 => by
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom w
    exact ((Fr.mem_iff h1).1 h2).map_of _ ψ hψ
  let T : CxPts X.str σ → Matrix (Fin 1) (Fin 1) ℂ := fun w _ _ => ratVal ((B * A⁻¹) x.1 x.2 x.2) w
  have hT : HolUnitAt (atlas X σ) T z := by
    refine ⟨?_, fun c hc _ _ => hhol.2 c hc x.2 x.2⟩
    rw [Matrix.det_fin_one]
    have hp := hval z hyz hz x.1
    have hd := hp.2.1
    rw [Matrix.det_of_lowerTriangular _ (fun i j hij => hp.2.2.2 i j i.2 hij)] at hd
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 hd x.2 (Finset.mem_univ _))
  refine ⟨T, T, T, hT, hT, hT, ?_⟩
  filter_upwards [GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ hyz, GlobalTheory.T.adaptedFrame_eventually_frame_near_complex_point F σ X ι m m E z _ hz] with w h1 h2
  rw [and_self]
  have hp := hval w h1 h2 x.1
  have e := (GlobalTheory.T.gramLowerTriangularFactor_lowerTriangular_conj _ _ _ (h.posDef w A h1 x.1) (fun i j hij => hp.2.2.2 i j i.2 hij)
    (isUnit_iff_ne_zero.2 hp.2.1)).2 x.2
  rw [← h.trans w A h1 B h2 x.1] at e
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.conjTranspose_apply]
  change ((grD (H B w x.1) x.2 : ℝ) : ℂ) = ((B * A⁻¹).map (ratVal · w) x.1 x.2 x.2) * ((grD (H A w x.1) x.2 : ℝ) : ℂ) *
    star ((B * A⁻¹).map (ratVal · w) x.1 x.2 x.2)
  rw [e, mul_right_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem chernFld_lineGram (h : IsMetricFr E H) (x : Root m) :
    chernFld (atlas X σ) (lineGram E H x) 1 = grF E H x := by
  funext p
  have hs := ((lineGram_smooth h x p.pt).2 p.1.1 p.2).self_of_nhds
  have e := GlobalTheory.T.chernForm_triangular_eq_esymm_firstChernForms _ 1 (fun v => lineGram E H x p.pt (p.ch.symm v))
    (fun _ v => grD (gramAt E H x.1 p.pt (p.ch.symm v)) x.2) p.crd hs
    (fun _ => by
      have : p.ch.symm p.crd = p.pt := p.ch.left_inv p.2
      rw [this]; exact grD_pos h x _)
    (Eventually.of_forall fun v => ⟨fun i j hij => absurd (Subsingleton.elim i j) hij.ne, fun _ => rfl⟩) 1
  refine e.trans ?_
  rw [esymm_one, Fin.sum_univ_one, aeval_X]
  rfl

theorem dbarCoh_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H →
    ∀ x : Root m, DbarCoh (atlas X σ) (grF E H x) (grF E H x) := by
  intro F _ σ X ι _ m E H h x
  rw [← chernFld_lineGram h x]
  exact GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ _ _ _ _ (isGramPair_lineGram h x) 1

end GlobalTheory.ChernCalc.GradedForm
end
end

