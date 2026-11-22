import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0114
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0107
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0120
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0057
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0122
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0108
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentSecond
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.GP

section Frames

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem exists_coeff {r : ℕ} (b b₀ : Fin r → E) (h : ∀ i, GlobalTheory.CompanionTheory.Ar.flagStep Ω b i = GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i)
    (hli : LinearIndependent Ω b) (i : Fin r) :
    ∃ t : Ω, t ≠ 0 ∧ b i - t • b₀ i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i := by
  have hni : b i ∉ GlobalTheory.CompanionTheory.Ar.flagStep Ω b i := hli.notMem_span_image (by simp)
  have h1 : b i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ (i+1) := by rw [← h]; exact Submodule.subset_span ⟨i, by simp, rfl⟩
  rw [GlobalTheory.CompanionTheory.Ar.Flag.step_succ] at h1
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz
  have ht : t ≠ 0 := by rintro rfl; apply hni; rw [h, ← hyz]; simpa using hy
  exact ⟨t, ht, by rw [← hyz]; simpa using hy⟩

theorem gr_isGen_of_frame (L : GlobalTheory.CompanionTheory.Ar.Lat ξ E) {r : ℕ} (b b₀ : Fin r → E) (p : Cpt ξ)
    (h : ∀ i, GlobalTheory.CompanionTheory.Ar.flagStep Ω b i = GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i) (hb : L.IsFrameAt b p) (i : Fin r) {t : Ω}
    (ht : t ≠ 0) (hy : b i - t • b₀ i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b₀ i) : (L.gr b₀ i).IsGenAt p t := by
  refine ⟨ht, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro s ⟨e, he, hs⟩
    rw [hb.2] at he
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
    have h2 : (∑ k, c k • b k) - (s / t) • b i ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω b i := by
      rw [h]
      have : (∑ k, c k • b k) - (s / t) • b i =
          ((∑ k, c k • b k) - s • b₀ i) - (s / t) • (b i - t • b₀ i) := by
        rw [smul_sub, smul_smul, div_mul_cancel₀ _ ht]; abel
      rw [this]; exact sub_mem hs (Submodule.smul_mem _ _ hy)
    obtain ⟨φ, hφ⟩ : ∃ φ : E →ₗ[Ω] Ω, ∀ k, φ (b k) = if k = i then 1 else 0 := by
      obtain ⟨g, hg⟩ := (Fintype.linearCombination Ω b).exists_leftInverse_of_injective
        (LinearMap.ker_eq_bot.2 (by rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; intro m hm; funext k; exact Fintype.linearIndependent_iff.1 hb.1 m (by simpa [Fintype.linearCombination_apply] using hm) k))
      refine ⟨(LinearMap.proj i).comp g, fun k => ?_⟩
      have := LinearMap.congr_fun hg (Pi.single k 1)
      simp [Fintype.linearCombination_apply_single] at this
      simp [this, Pi.single_apply, eq_comm]
    have h3 : GlobalTheory.CompanionTheory.Ar.flagStep Ω b i ≤ LinearMap.ker φ := Submodule.span_le.2 (by
      rintro _ ⟨k, hk, rfl⟩
      have : k ≠ i := by rintro rfl; simp at hk
      simp [hφ, this])
    have h4 := h3 h2
    have h5 : ∀ k, φ (c k • b k) = (c k : Ω) * φ (b k) := fun k => φ.map_smul (c k : Ω) (b k)
    simp only [LinearMap.mem_ker, map_sub, map_sum, h5, map_smul, hφ] at h4
    simp at h4
    refine Submodule.mem_span_singleton.2 ⟨c i, ?_⟩
    show (c i : Ω) * t = s
    rw [sub_eq_zero.1 h4, div_mul_cancel₀ _ ht]
  · rintro _ rfl
    exact ⟨b i, by rw [hb.2]; exact Submodule.subset_span ⟨i, rfl⟩, hy⟩

theorem gen_ratio {Λ : GlobalTheory.CompanionTheory.Ar.Lat ξ Ω} {p : Cpt ξ} {s t : Ω} (hs : Λ.IsGenAt p s) (ht : Λ.IsGenAt p t) :
    ∃ u : Ω, u ∈ regAt ξ p ∧ u⁻¹ ∈ regAt ξ p ∧ s = u * t := by
  have a1 : s ∈ Submodule.span (regAt ξ p) {t} := by
    rw [← ht.2, hs.2]; exact Submodule.mem_span_singleton_self _
  have a2 : t ∈ Submodule.span (regAt ξ p) {s} := by
    rw [← hs.2, ht.2]; exact Submodule.mem_span_singleton_self _
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 a1
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 a2
  have hu' : (u : Ω) * t = s := hu
  have hv' : (v : Ω) * s = t := hv
  have e : (v : Ω) * (u : Ω) = 1 := by
    refine mul_right_cancel₀ ht.1 ?_
    rw [_root_.mul_assoc, hu', hv', _root_.one_mul]
  refine ⟨u, u.2, ?_, hu'.symm⟩
  rw [← eq_inv_of_mul_eq_one_left e]
  exact v.2

theorem gen_mul {Λ : GlobalTheory.CompanionTheory.Ar.Lat ξ Ω} {p : Cpt ξ} {t u : Ω} (h : Λ.IsGenAt p t) (h0 : u ≠ 0)
    (hu : u ∈ regAt ξ p) (hu' : u⁻¹ ∈ regAt ξ p) : Λ.IsGenAt p (u * t) := by
  refine ⟨mul_ne_zero h0 h.1, ?_⟩
  rw [h.2]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ rfl
    exact Submodule.mem_span_singleton.2 ⟨⟨u⁻¹, hu'⟩, inv_mul_cancel_left₀ h0 _⟩
  · rintro _ rfl
    exact Submodule.mem_span_singleton.2 ⟨⟨u, hu⟩, rfl⟩

end Frames

section Pull

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {E E₀ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₀] [Module Ω₀ E₀]

theorem mem_flagStep_pull {i : Ω₀ →+* Ω} {j : E₀ →+ E} (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e) {r : ℕ}
    {y : Fin r → E₀} {n : ℕ} {x : E₀} (hx : x ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ y n) :
    j x ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (y k)) n := by
  unfold GlobalTheory.CompanionTheory.Ar.flagStep at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨k, hk, rfl⟩ := h
    exact Submodule.subset_span ⟨k, hk, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [hj]; exact Submodule.smul_mem _ _ hx

theorem flagStep_pull_le {i : Ω₀ →+* Ω} {j : E₀ →+ E} (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e) {r : ℕ}
    {x y : Fin r → E₀} {n : ℕ} (h : GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ x n ≤ GlobalTheory.CompanionTheory.Ar.flagStep Ω₀ y n) :
    GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (x k)) n ≤ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (y k)) n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨k, hk, rfl⟩
  exact mem_flagStep_pull hj (h (Submodule.subset_span ⟨k, hk, rfl⟩))

theorem isFrameAt_pull {i : Ω₀ →+* Ω} {j : E₀ →+ E} {L₀ : GlobalTheory.CompanionTheory.Ar.Lat ξ₀ E₀} {L : GlobalTheory.CompanionTheory.Ar.Lat ξ E}
    {p₀ : Cpt ξ₀} {p : Cpt ξ} (hreg : ∀ a, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p)
    (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → E₀), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k))
    (hL : L p = Submodule.span (regAt ξ p) (j '' (L₀ p₀ : Set E₀))) {r : ℕ} {b : Fin r → E₀}
    (hb : L₀.IsFrameAt b p₀) : L.IsFrameAt (fun k => j (b k)) p := by
  refine ⟨hli _ _ hb.1, ?_⟩
  rw [hL]
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨e, he, rfl⟩
    have he' : e ∈ L₀ p₀ := he
    rw [hb.2] at he'
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'
    rw [map_sum]
    refine sum_mem fun k _ => ?_
    have e1 : j (c k • b k) = (⟨i (c k), hreg _ (c k).2⟩ : regAt ξ p) • j (b k) := hj (c k : Ω₀) (b k)
    rw [e1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rintro _ ⟨k, rfl⟩
    refine ⟨b k, ?_, rfl⟩
    show b k ∈ L₀ p₀
    rw [hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩

theorem isGenAt_pull (i : Ω₀ →+* Ω) (j : E₀ →+ E) {L₀ : GlobalTheory.CompanionTheory.Ar.Lat ξ₀ E₀} {L : GlobalTheory.CompanionTheory.Ar.Lat ξ E}
    {p₀ : Cpt ξ₀} {p : Cpt ξ} (hreg : ∀ a, a ∈ regAt ξ₀ p₀ → i a ∈ regAt ξ p)
    (hj : ∀ (a : Ω₀) e, j (a • e) = i a • j e)
    (hli : ∀ (n : ℕ) (b : Fin n → E₀), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k))
    {r : ℕ} {c₀ : Fin r → E₀} {c : Fin r → E} (hc : ∀ a, j (c₀ a) = c a)
    (hL : L p = Submodule.span (regAt ξ p) (j '' (L₀ p₀ : Set E₀)))
    (hf : L₀.IsFlagVBOn Set.univ c₀) (a : Fin r) {t₀ : Ω₀} (h : (L₀.gr c₀ a).IsGenAt p₀ t₀) :
    (L.gr c a).IsGenAt p (i t₀) := by
  obtain ⟨U, hU, b₁, hb, hfr⟩ := hf p₀ trivial
  have hfr' := hfr p₀ trivial hU
  obtain ⟨t₁, ht₁, hy⟩ := exists_coeff b₁ c₀ hb hfr'.1 a
  have g₁ := gr_isGen_of_frame L₀ b₁ c₀ p₀ hb hfr' a ht₁ hy
  obtain ⟨u, hu, hu', rfl⟩ := gen_ratio h g₁
  have hc' : c = fun k => j (c₀ k) := funext fun a => (hc a).symm
  subst hc'
  have hframe : L.IsFrameAt (fun k => j (b₁ k)) p := isFrameAt_pull hreg hj hli hL hfr'
  have hadapt : ∀ n, GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (b₁ k)) n = GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (c₀ k)) n :=
    fun n => le_antisymm (flagStep_pull_le hj (hb n).le) (flagStep_pull_le hj (hb n).ge)
  have hy' : j (b₁ a) - i t₁ • j (c₀ a) ∈ GlobalTheory.CompanionTheory.Ar.flagStep Ω (fun k => j (c₀ k)) a := by
    have := mem_flagStep_pull hj hy
    rwa [map_sub, hj] at this
  have g := gr_isGen_of_frame L (fun k => j (b₁ k)) (fun k => j (c₀ k)) p hadapt hframe a
    ((map_ne_zero i).2 ht₁) hy'
  have hu0 : u ≠ 0 := left_ne_zero_of_mul h.1
  rw [map_mul]
  refine gen_mul g ((map_ne_zero i).2 hu0) (hreg _ hu) ?_
  rw [← map_inv₀]
  exact hreg _ hu'

end Pull

theorem genPull_of_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → GenPull Fl₀ Fl i hd := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl j hr hj hli hb hV
  intro q hq s a t₀ hg
  exact isGenAt_pull i j (hr q) hj hli (hb s) (hV q hq s) (Fl₀.sub s) a hg

end GlobalTheory.CompanionTheory.Ar.Chg.GP
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAtlasCoordCompat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ImmBlock

theorem aeval_mul_of_isHomogeneous {σ R : Type*} [Fintype σ] [CommRing R] {alg : Algebra ℤ R}
    {F : MvPolynomial σ ℤ} {n : ℕ}
    (hF : F.IsHomogeneous n) (a : σ → R) (t : R) :
    MvPolynomial.aeval (fun i => a i * t) F = MvPolynomial.aeval a F * t ^ n := by
  classical
  simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = n := by
    have h := hF (MvPolynomial.mem_support_iff.1 hd)
    have h2 : Finsupp.degree d = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact h
    rw [← h2, Finsupp.degree_apply]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)).symm
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, _root_.mul_assoc]

theorem aeval_ringHom {σ A B : Type*} [CommRing A] [CommRing B] {algA : Algebra ℤ A} {algB : Algebra ℤ B}
    (φ : A →+* B) (a : σ → A) (P : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (fun i => φ (a i)) P = φ (MvPolynomial.aeval a P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.aeval_C, eq_intCast, map_intCast]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X]

theorem differentiable_aeval {σ κ : Type*} [Fintype κ] (g : σ → κ) (P : MvPolynomial σ ℤ) :
    Differentiable ℂ (fun u : κ → ℂ => MvPolynomial.aeval (fun i => u (g i)) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using differentiable_const _
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (differentiable_apply _)

theorem form_mem {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (k₀ k : K) (n : ℕ) (F G : MvPolynomial (J k₀) ℤ) (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous n) (c d : J k)
    (h : MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) F * y ⟨k, c⟩ =
      MvPolynomial.aeval (fun i : J k₀ => y ⟨k₀, i⟩) G * y ⟨k, d⟩) :
    MvPolynomial.rename (Sigma.mk k₀) F * MvPolynomial.X ⟨k, c⟩ -
      MvPolynomial.rename (Sigma.mk k₀) G * MvPolynomial.X ⟨k, d⟩ ∈ mCoordIdeal y := by
  have hh := congrArg (MvPolynomial.C : Ω → MvPolynomial K Ω) h
  simp only [map_mul] at hh
  rw [mCoordIdeal, RingHom.mem_ker]
  simp only [mConeMap, map_sub, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X, Function.comp_def]
  rw [aeval_mul_of_isHomogeneous hF (fun i : J k₀ => (MvPolynomial.C (y ⟨k₀, i⟩) : MvPolynomial K Ω)) (MvPolynomial.X k₀),
    aeval_mul_of_isHomogeneous hG (fun i : J k₀ => (MvPolynomial.C (y ⟨k₀, i⟩) : MvPolynomial K Ω)) (MvPolynomial.X k₀),
    aeval_ringHom MvPolynomial.C (fun i : J k₀ => y ⟨k₀, i⟩) F,
    aeval_ringHom MvPolynomial.C (fun i : J k₀ => y ⟨k₀, i⟩) G]
  linear_combination (MvPolynomial.X k₀ ^ n * MvPolynomial.X k) * hh

theorem differentiableAt_quot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a b : E → ℂ} {v : E}
    (ha : DifferentiableAt ℂ a v) (hb : DifferentiableAt ℂ b v) (h : b v ≠ 0) :
    DifferentiableAt ℂ (fun w => a w / b w) v := by
  simp only [div_eq_mul_inv]
  exact ha.mul (hb.inv h)

theorem ker_bot_of_factor {E F₁ F₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F₁]
    [NormedSpace ℂ F₁] [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] {f : E → F₁} {a : E → F₂} {Ψ : F₁ → F₂} {v₀ : E}
    (hf : DifferentiableAt ℂ f v₀) (hΨ : DifferentiableAt ℂ Ψ (f v₀)) (h : a =ᶠ[nhds v₀] Ψ ∘ f)
    (hk : (fderiv ℂ a v₀).ker = ⊥) : (fderiv ℂ f v₀).ker = ⊥ := by
  rw [h.fderiv_eq, fderiv_comp v₀ hΨ hf] at hk
  rw [eq_bot_iff]
  intro u hu
  have hu' : fderiv ℂ f v₀ u = 0 := hu
  have : u ∈ ((fderiv ℂ Ψ (f v₀)).comp (fderiv ℂ f v₀)).ker := by
    change (fderiv ℂ Ψ (f v₀)) (fderiv ℂ f v₀ u) = 0
    rw [hu', map_zero]
  rwa [hk] at this

theorem immersion_block : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (k₀ : K), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → EmbedsGeneric ξ (fun i : J k₀ => y ⟨k₀, i⟩) → ∀ (e : ℕ) (M : Type) [TopologicalSpace M] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e M) (U : M → Set M) (lam : M → M → (Σ k, J k) → ℂ), Cmp.IsEmbedded A (mCoordIdeal y) U lam → ∀ (κ : Type) [Fintype κ] (ix : κ ≃ J k₀) (x : M) (p : κ), lam x x ⟨k₀, ix p⟩ ≠ 0 → ∀ j, x ∈ (A.chart j).source → DifferentiableAt ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x) ∧ (fderiv ℂ (fun (v : Fin e → ℂ) (i : κ) => lam x ((A.chart j).symm v) ⟨k₀, ix i⟩ / lam x ((A.chart j).symm v) ⟨k₀, ix p⟩) (A.chart j x)).ker = ⊥ := by
  intro X Ω _ _ ξ K _ J _ y k₀ hTie hEmb e M _ A U lam hE κ _ ix x p hp j hj
  classical
  have hev : ∀ (z : (Σ k, J k) → ℂ) (f : MRing J),
      MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = MvPolynomial.aeval z f := fun z f => by
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    congr 1
  set G : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun v => lam x ((A.chart j).symm v) with hGdef
  set v₀ : Fin e → ℂ := A.chart j x with hv₀
  have hG0 : G v₀ = lam x x := by
    simp only [hGdef, hv₀]
    rw [(A.chart j).left_inv hj]
  have hS : v₀ ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U x := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    change (A.chart j).symm (A.chart j x) ∈ U x
    rw [(A.chart j).left_inv hj]
    exact hE.mem_U x
  have hSo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U x) :=
    (A.chart j).isOpen_inter_preimage_symm (hE.isOpen x)
  have hAn : ∀ q, DifferentiableAt ℂ (fun v => G v q) v₀ := fun q =>
    (hE.holo x q j v₀ hS).differentiableAt
  have hCo : ∀ q, ContinuousAt (fun v => G v q) v₀ := fun q => (hAn q).continuousAt
  have hw : lam x x ∈ mcPts (mCoordIdeal y) := hE.mem x x (hE.mem_U x)
  have hwpts : lam x x ∈ Small.ptsOver ℂ (mCoordIdeal y) :=
    ⟨hw.1, fun f hf => by rw [← hev]; exact hw.2 f hf⟩
  choose r hr using hw.1
  set p' : (k : K) → J k := Function.update r k₀ (ix p) with hp'def
  have hp'0 : p' k₀ = ix p := by simp [hp'def]
  have hp' : ∀ k, lam x x ⟨k, p' k⟩ ≠ 0 := by
    intro k
    by_cases h : k = k₀
    · subst h
      rw [hp'0]
      exact hp
    · rw [hp'def, Function.update_of_ne h]
      exact hr k
  have hblk := fun k => GlobalTheory.T.small_points_coord_ratio_bound X Ω ξ K J y k₀ hTie hEmb ℂ (lam x x) hwpts (ix p) k (p' k) hp (hp' k)
  choose n F hFh hFr hFn using hblk

  set f : (Fin e → ℂ) → κ → ℂ := fun v i => G v ⟨k₀, ix i⟩ / G v ⟨k₀, ix p⟩ with hfdef
  have ht0 : G v₀ ⟨k₀, ix p⟩ ≠ 0 := by rw [hG0]; exact hp
  have hfd : DifferentiableAt ℂ f v₀ :=
    by
    refine differentiableAt_pi.2 fun i => ?_
    have h := differentiableAt_quot (hAn ⟨k₀, ix i⟩) (hAn ⟨k₀, ix p⟩) ht0
    exact h

  set ev : MvPolynomial (J k₀) ℤ → (κ → ℂ) → ℂ :=
    fun P u => MvPolynomial.aeval (fun i' : J k₀ => u (ix.symm i')) P with hevdef
  have hevd : ∀ P, Differentiable ℂ (ev P) := fun P => differentiable_aeval (fun i' => ix.symm i') P
  have hscale : ∀ v k (d : J k), ev (F k d) (f v) =
      MvPolynomial.aeval (fun i' : J k₀ => G v ⟨k₀, i'⟩) (F k d) * ((G v ⟨k₀, ix p⟩)⁻¹) ^ n k := by
    intro v k d
    rw [← aeval_mul_of_isHomogeneous (hFh k d)]
    simp only [hevdef, hfdef, Equiv.apply_symm_apply, div_eq_mul_inv]
  have hden0 : ∀ k, ev (F k (p' k)) (f v₀) ≠ 0 := by
    intro k
    rw [hscale, hG0]
    exact mul_ne_zero (hFn k) (pow_ne_zero _ (inv_ne_zero hp))
  set Ψ : (κ → ℂ) → (Σ k, J k) → ℂ := fun u q => ev (F q.1 q.2) u / ev (F q.1 (p' q.1)) u with hΨdef
  have hΨd : DifferentiableAt ℂ Ψ (f v₀) :=
    by
    refine differentiableAt_pi.2 fun q => ?_
    have h := differentiableAt_quot (hevd (F q.1 q.2) (f v₀)) (hevd (F q.1 (p' q.1)) (f v₀)) (hden0 q.1)
    exact h

  have e1 : ∀ᶠ v in nhds v₀, G v ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hSo.mem_nhds hS] with v hv
    exact hE.mem x _ hv.2
  have e2 : ∀ᶠ v in nhds v₀, ∀ k, G v ⟨k, p' k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k =>
      (hCo ⟨k, p' k⟩).eventually_ne (by rw [hG0]; exact hp' k)
  have e3 : ∀ᶠ v in nhds v₀, ∀ k, ev (F k (p' k)) (f v) ≠ 0 :=
    Filter.eventually_all.2 fun k =>
      (((hevd _).continuous.continuousAt).comp hfd.continuousAt).eventually_ne (hden0 k)
  have e4 : ∀ᶠ v in nhds v₀, G v ⟨k₀, ix p⟩ ≠ 0 := (hCo _).eventually_ne ht0
  have hfac : (fun v => affCoord p' (G v)) =ᶠ[nhds v₀] Ψ ∘ f := by
    filter_upwards [e1, e2, e3, e4] with v h1 h2 h3 h4
    funext q
    obtain ⟨k, d⟩ := q
    have hmem := form_mem y k₀ k (n k) (F k d) (F k (p' k)) (hFh k d) (hFh k (p' k)) (p' k) d (hFr k d)
    have h0 := h1.2 _ hmem
    rw [hev] at h0
    simp only [map_sub, map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_X, Function.comp_def] at h0
    have hrel : ev (F k d) (f v) * G v ⟨k, p' k⟩ = ev (F k (p' k)) (f v) * G v ⟨k, d⟩ := by
      rw [hscale, hscale]
      linear_combination ((G v ⟨k₀, ix p⟩)⁻¹) ^ n k * h0
    change G v ⟨k, d⟩ / G v ⟨k, p' k⟩ = ev (F k d) (f v) / ev (F k (p' k)) (f v)
    rw [div_eq_div_iff (h2 k) (h3 k)]
    linear_combination -hrel
  have hk : (fderiv ℂ (fun v => affCoord p' (G v)) v₀).ker = ⊥ :=
    hE.immersion x p' hp' j hj
  exact ⟨hfd, ker_bot_of_factor hfd hΨd hfac hk⟩

end GlobalTheory.CompanionTheory.Ar.ImmBlock
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatHerm
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem FlatHerm.inter_eq : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω)
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ),
    IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W →
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    I W (n + 1) (Fin.snoc L A) = S.ht * ptsIntegral W (pot L) (fun _ => 1) := by
  intro hP K _ ι _ Ω _ F _ _ y φ I W n L A S d hI hY hO hyW hW hL hA
  obtain ⟨u, hu, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (fun σ => Real.log (S.κ σ)) hO
  rw [GlobalTheory.T.intersection_family_flat_twist K ι Ω F y φ I W n L A S d u hI hY hO hyW hW hL hA hu,
    GlobalTheory.T.intersection_family_place_weight hP K ι Ω F y φ I W n L d (fun σ => Real.log (S.κ σ)) u hI hY hO hyW hW hL
      (fun σ => congrArg Real.log (S.κ_conj σ)) (fun σ z hz => (hu.near σ z hz).self_of_nhds),
    FlatHerm.ht, neg_mul]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleClosedIntegralSubschemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_closed_integral_subscheme : ∀ (S : Scheme.{0}) (F : Set S), IsClosed F → IsIrreducible F →
    ∃ (Z : Scheme.{0}) (_ : IsIntegral Z) (i : Z ⟶ S), IsClosedImmersion i ∧ Set.range i = F ∧
      ∀ (k : Type) [Field k] (x : Sp k ⟶ S), x (IsLocalRing.closedPoint k) ∈ F → ∃ x' : Sp k ⟶ Z, x' ≫ i = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_integral_closed_subscheme | exact GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_integral_closed_subscheme | (intros; apply GlobalTheory.CompanionTheory.Ar.TorusUnif.exists_integral_closed_subscheme <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelEmbeddingInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.label_embedding_injective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Geo.Tor.Level H) (c : Coeff l), Function.Injective (labelEmb (H := H) c) ∧ Nat.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.labels_all_once | exact GlobalTheory.CompanionTheory.Ar.labels_all_once | (intros; apply GlobalTheory.CompanionTheory.Ar.labels_all_once <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsoTransportStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_iso_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (m : SABMap t' t e.hom) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V), ξ' ≫ e.hom = ξ → ∃ M' : LieModel t'.G ξ' V, (∀ v, (M'.pt v).left ≫ m.φ = (M.pt v).left) ∧ (∀ n, FullTorsion t.G ξ n → FullTorsion t'.G ξ' n) ∧ (IsCptGen ξ → IsCptGen ξ') ∧ ∀ (q : Cpt ξ') (h : genPt ξ ⤳ e.hom q.1), regAt ξ' q = regAt ξ ⟨e.hom q.1, h⟩ ∧ (M'.lat q : Set V) = M.lat ⟨e.hom q.1, h⟩ ∧ ∀ n, (M'.htOm t'.PP.L n q : Set (Module.Dual Ω V)) = M.htOm t.PP.L n ⟨e.hom q.1, h⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IsoMove.lieModel_isoMove | exact GlobalTheory.CompanionTheory.Ar.IsoMove.lieModel_isoMove | (intros; apply GlobalTheory.CompanionTheory.Ar.IsoMove.lieModel_isoMove <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightBoundedUnitStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_height_bounded_unit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (d : ℕ), IsArithVar (mCoordIdeal y) d → Birational y → ∀ (A : HermLine ι) (k : ℕ) (u : Ω) (c : ℝ), IsSmoothHerm A → 0 < k → GenUnit y (fun b => k * A.a b) u → VertBound y (fun b => k * A.a b) u c → ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], ∀ w ∈ ptsOver L (mCoordIdeal y), |lineHt A L w| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit | exact GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.Ht.lineHt_bounded_of_genUnit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_scheme_coords_injective : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → (∀ q : X, genPt ξ ⤳ q) → ∀ (z z' : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → CoordsAt ξ y z' w → z = z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.point_eq_of_coordsAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricHermitianBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_metric_hermitian_bundle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ (s s' : CMType H ⊕ CMType H), s ≠ s' → ∀ U U' : Submodule Ω 𝔐.Li, U ≤ 𝔐.Vgen s → U' ≤ 𝔐.Vgen s' → OrthAt B (FlagFib.subFib 𝔐.M U z MB) (FlagFib.subFib 𝔐.M U' z MB) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth.orthAt_subFib | exact GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth.orthAt_subFib | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth.orthAt_subFib <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionContinuousAtStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_function_continuous_at : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ) (h₀ : genPt ξ ⤳ centre z₀) (a : Ω), CoordsAt ξ y z₀ w₀ →
      a ∈ regAt ξ ⟨centre z₀, h₀⟩ →
      ∃ φ : ((Σ k, J k) → ℂ) → ℂ, ContinuousAt φ w₀ ∧ ∃ N ∈ 𝓝 w₀, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ),
        w ∈ N → CoordsAt ξ y z w → ValAt ξ z a (φ w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.val_near | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.val_near | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.val_near <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularSectionsOpenNeighbourhoodStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_sections_open_neighbourhood : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li),
    IsCptGen ξ → SmoothOfRelativeDimension g G.hom →
    ∀ (p : Cpt ξ) (n : ℕ) (S : Fin n → Li) (Φ : Fin n → Module.Dual Ω Li),
      (∀ j, S j ∈ M.lat p) → (∀ j, ∀ e ∈ M.lat p, Φ j e ∈ regAt ξ p) →
      ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
        (∀ j, S j ∈ M.lat q) ∧ ∀ j, ∀ e ∈ M.lat q, Φ j e ∈ regAt ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near <;> assumption)
end

