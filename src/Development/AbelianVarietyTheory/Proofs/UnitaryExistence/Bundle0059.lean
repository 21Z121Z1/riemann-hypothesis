import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0052
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemCuspSpaceIffOfFinite
section
noncomputable section

namespace GlobalTheory.CuspSecCompare

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.CuspSectionNorms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {ι : Type}

theorem bdd_iff_supE_ne_top (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    (∃ C : ℝ, ∀ p : FramePt X, ptNorm la P p ≤ C) ↔ Formalism.L2.PjFree.supE X la P ≠ ⊤ := by
  constructor
  · rintro ⟨C, hC⟩
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun p => ENNReal.ofReal_le_ofReal (hC p))
  · intro h
    refine ⟨(Formalism.L2.PjFree.supE X la P).toReal, fun p => ?_⟩
    rw [← ENNReal.ofReal_le_iff_le_toReal h]
    exact le_iSup (fun q : FPt X => ENNReal.ofReal ((X q.1).pnorm (la q.1) (P q.1) q.2)) p

theorem isCuspSec_iff (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    IsCuspSec la P ↔ IsHolCusp X la P ∧ Formalism.L2.PjFree.supE X la P ≠ ⊤ :=
  and_congr Iff.rfl (bdd_iff_supE_ne_top X la P)

theorem isCuspSec_iff_isHolCusp [Finite ι] (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    IsCuspSec la P ↔ IsHolCusp X la P :=
  isCuspSec_iff_of_finite la P

theorem mem_holSub_iff (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    P ∈ holSub X la ↔ IsHolCusp X la P := by
  refine ⟨fun h => ?_, holCusp_mem_holSub X la⟩
  induction h using Submodule.span_induction with
  | mem Q hQ => exact hQ
  | zero => exact fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.1
  | add Q R _ _ hQ hR => exact fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.2.1 _ (hQ c) _ (hR c)
  | smul a Q _ hQ => exact fun c => (siegelSpaceAlgebra_holds r (X c) (la c) (la c) 0).1.2.2 a _ (hQ c)

theorem mem_cuspSpace_iff (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    P ∈ cuspSpace la ↔ P ∈ holSub X la ∧ Formalism.L2.PjFree.supE X la P ≠ ⊤ ∧ ZeroOff P := by
  rw [mem_holSub_iff, ← and_assoc, ← isCuspSec_iff]
  rfl

theorem mem_cuspSpace_iff_of_finite [Finite ι] (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    P ∈ cuspSpace la ↔ P ∈ holSub X la ∧ ZeroOff P := by
  rw [mem_holSub_iff, ← isCuspSec_iff_isHolCusp]
  rfl

theorem cuspSpace_le_holSub (X : ι → Data E r) (la : FamWt X) : cuspSpace la ≤ holSub X la :=
  fun P hP => ((mem_cuspSpace_iff X la P).1 hP).1

theorem mem_SS_congr (X : Data E r) (la : Wt X.Ψ r) {P Q : Frame X.Ψ r → ℂ}
    (h : ∀ x ∈ X.dom, P x = Q x) (hP : P ∈ X.SS la) : Q ∈ X.SS la := by
  obtain ⟨⟨⟨hd, hb, hg⟩, C, hC⟩, hc⟩ := hP
  refine ⟨⟨⟨hd.congr fun x hx => (h x hx).symm, fun x hx b hb' => ?_, fun γ hγ x hx => ?_⟩, C,
    fun x hx => ?_⟩, fun ξ hξ x hx => ?_⟩
  · rw [← h _ (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb'), ← h x hx, hb x hx b hb']
  · rw [← h _ (ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact X hγ hx), ← h x hx, hg γ hγ x hx]
  · have := hC x hx
    unfold Data.pnorm at this ⊢
    rwa [← h x hx]
  · have e : ∀ s : X.Ψ → ℝ,
        P (X.flow ξ (fun τ => (s τ : ℂ)) x) = Q (X.flow ξ (fun τ => (s τ : ℂ)) x) :=
      fun s => h _ (TransvectionPeriodicity.flow_real_mem_dom X hξ.2.1 s x hx)
    have := hc ξ hξ x hx
    unfold Data.fj at this ⊢
    simpa only [e] using this

def res (X : ι → Data E r) : FDSec X →ₗ[ℂ] (FPt X → ℂ) where
  toFun P p := P p.1 p.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def trunc (X : ι → Data E r) : FDSec X →ₗ[ℂ] FDSec X where
  toFun P c := (X c).dom.indicator (P c)
  map_add' P Q := funext fun c => Set.indicator_add' _ (P c) (Q c)
  map_smul' a P := funext fun c => funext fun x => by
    by_cases hx : x ∈ (X c).dom <;> simp [hx]

theorem trunc_of_mem (X : ι → Data E r) (P : FDSec X) (c : ι) {x : Frame (X c).Ψ r}
    (hx : x ∈ (X c).dom) : trunc X P c x = P c x := Set.indicator_of_mem hx _

theorem zeroOff_trunc (X : ι → Data E r) (P : FDSec X) : ZeroOff (trunc X P) :=
  fun _ _ hx => Set.indicator_of_notMem hx _

theorem trunc_eq_self (X : ι → Data E r) {P : FDSec X} (h : ZeroOff P) : trunc X P = P := by
  funext c x
  by_cases hx : x ∈ (X c).dom
  · exact trunc_of_mem X P c hx
  · rw [zeroOff_trunc X P c x hx, h c x hx]

theorem res_trunc (X : ι → Data E r) (P : FDSec X) : res X (trunc X P) = res X P :=
  funext fun p => trunc_of_mem X P p.1 p.2.2

theorem ker_trunc (X : ι → Data E r) : LinearMap.ker (trunc X) = LinearMap.ker (res X) := by
  ext P
  simp only [LinearMap.mem_ker]
  constructor
  · intro h
    rw [← res_trunc, h, map_zero]
  · intro h
    funext c x
    by_cases hx : x ∈ (X c).dom
    · rw [trunc_of_mem X P c hx]
      exact congrFun h ⟨c, x, hx⟩
    · exact zeroOff_trunc X P c x hx

theorem isHolCusp_trunc_iff (X : ι → Data E r) (la : FamWt X) (P : FDSec X) :
    IsHolCusp X la (trunc X P) ↔ IsHolCusp X la P :=
  ⟨fun h c => mem_SS_congr _ _ (fun _ hx => trunc_of_mem X P c hx) (h c),
    fun h c => mem_SS_congr _ _ (fun _ hx => (trunc_of_mem X P c hx).symm) (h c)⟩

theorem holSub_eq_comap [Finite ι] (X : ι → Data E r) (la : FamWt X) :
    holSub X la = (cuspSpace la).comap (trunc X) := by
  ext P
  rw [Submodule.mem_comap, mem_cuspSpace_iff_of_finite, mem_holSub_iff, mem_holSub_iff,
    isHolCusp_trunc_iff, and_iff_left (zeroOff_trunc X P)]

theorem map_res_eq [Finite ι] (X : ι → Data E r) (la : FamWt X) :
    (holSub X la).map (res X) = (cuspSpace la).map (res X) := by
  refine le_antisymm ?_ (Submodule.map_mono (cuspSpace_le_holSub X la))
  rintro _ ⟨P, hP, rfl⟩
  exact ⟨trunc X P, (holSub_eq_comap X la).le hP, res_trunc X P⟩

theorem disjoint_cuspSpace_ker (X : ι → Data E r) (la : FamWt X) :
    Disjoint (cuspSpace la) (LinearMap.ker (res X)) := by
  rw [← ker_trunc, Submodule.disjoint_def]
  intro P hP h0
  rw [← trunc_eq_self X hP.2]
  exact h0

def cuspSpaceEquiv [Finite ι] (X : ι → Data E r) (la : FamWt X) :
    cuspSpace la ≃ₗ[ℂ] (holSub X la).map (res X) :=
  LinearEquiv.ofBijective
    ((res X).restrict fun _ hP => Submodule.mem_map_of_mem (cuspSpace_le_holSub X la hP))
    ⟨fun P Q h => Subtype.ext (LinearMap.disjoint_ker_iff_injOn.1 (disjoint_cuspSpace_ker X la)
        P.2 Q.2 (congrArg Subtype.val h)),
      fun F => by
        obtain ⟨P, hP, e⟩ := (map_res_eq X la).le F.2
        exact ⟨⟨P, hP⟩, Subtype.ext e⟩⟩

end GlobalTheory.CuspSecCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemPrincipalCongruenceInterCuspCentreIff
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.CuspCentre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem zMatE_congr_of_entries (X : Data E r) (N : ℕ) (cu : FJ.CuspFD X ρ)
    (c : Fin ρ → FractionalIdeal (𝓞 E)⁰ E)
    (hd : ∀ v ∈ X.Λ, ∀ b, ∀ a' ∈ c b, ∃ n : ℤ,
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v (cu.e b) * cc a') = n)
    (hc : ∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ c b)
    (β : Matrix (Fin ρ) (Fin ρ) E)
    (hβ : ∀ a b (y : E), (∀ a' ∈ c b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) →
      ∃ z ∈ c a, β a b / X.ξ0 * y = (N : E) * z) :
    ∀ v ∈ X.Λ, ∃ w ∈ X.Λ, FJ.zMatE X cu.e β *ᵥ v = v + N • w := by
  intro v hv
  choose z hz hz' using fun a b => hβ a b _ (hd v hv b)
  refine ⟨∑ a, (∑ b, -z a b) • cu.e a, (hc _).2 fun a => ?_, ?_⟩
  · exact (c a : Submodule (𝓞 E) E).sum_mem fun b _ => (c a : Submodule (𝓞 E) E).neg_mem (hz a b)
  · rw [zMatE_mulVec, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Nat.cast_smul_eq_nsmul E, smul_smul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    have h := hz' a b
    have h0 := X.ξ0_ne
    rw [mul_neg, ← h]
    field_simp

theorem mem_zGam_principal_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (r ρ : ℕ) (X : Data E r) (N : ℕ) (D : Datum H) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (cu : FJ.CuspFD X ρ) (cc' : Fin ρ → FractionalIdeal (𝓞 E)⁰ E), LinearMap.range φ = X.Λ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (X.Gm a b) = X.Gm b a) ∧ X.Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-X.ξ0 * herm X.Gm (φ x) (φ y))) → (∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧ ∀ v ∈ X.Λ, ∃ w ∈ X.Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + N • w) → (∀ a : Fin ρ → E, (∑ b, a b • cu.e b) ∈ X.Λ ↔ ∀ b, a b ∈ cc' b) → ∀ β, β ∈ FJ.zGam X cu ↔ FJ.IsSkew β ∧ ∀ a b (y : E), (∀ a' ∈ cc' b, ∃ n : ℤ, Algebra.trace ℚ E (y * cc a') = n) → ∃ z ∈ cc' a, β a b / X.ξ0 * y = (N : E) * z := by
  intro E _ _ _ H r ρ X N D φ cu c hΛ hφ hΓ hc β
  have hsd := GlobalTheory.SatDual.pairing_pseudoBasis E H D r (-X.ξ0) X.Gm φ ρ cu.e c
    (by rw [cc_neg', X.ξ0_im]) hφ cu.ind (by rw [hΛ]; exact hc)
  have hd : ∀ v ∈ X.Λ, ∀ b, ∀ a' ∈ c b, ∃ n : ℤ,
      Algebra.trace ℚ E (-X.ξ0 * herm X.Gm v (cu.e b) * cc a') = n := by
    intro v hv
    rw [← hΛ] at hv
    obtain ⟨x, rfl⟩ := hv
    exact (hsd fun b => -X.ξ0 * herm X.Gm (φ x) (cu.e b)).1 ⟨x, fun _ => rfl⟩
  have h0 := X.ξ0_ne
  constructor
  · rintro ⟨hs, γ, hγ, e⟩
    refine ⟨hs, fun a b y hy => ?_⟩
    obtain ⟨x, hx⟩ := (hsd (Pi.single b y)).2 (by
      intro b' a' ha'
      by_cases hb : b' = b
      · subst hb
        simpa using hy a' ha'
      · exact ⟨0, by simp [Pi.single_eq_of_ne hb]⟩)
    obtain ⟨w, hw, hw'⟩ := ((hΓ γ).1 hγ).2 (φ x) (hΛ ▸ ⟨x, rfl⟩)
    rw [e, zMatE_mulVec, add_right_inj] at hw'
    have h1 : ∀ a, ∑ b', β a b' * herm X.Gm (φ x) (cu.e b') = -(β a b / X.ξ0 * y) := by
      intro a
      rw [Finset.sum_eq_single b]
      · have h2 := hx b
        rw [Pi.single_eq_same] at h2
        rw [← h2]
        field_simp
      · intro b' _ hb'
        have h2 := hx b'
        rw [Pi.single_eq_of_ne hb', mul_eq_zero, neg_eq_zero] at h2
        rw [h2.resolve_left h0, mul_zero]
      · simp
    simp only [h1] at hw'
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      rw [zero_smul] at hw'
      have h3 := Fintype.linearIndependent_iff.1 cu.ind _ hw' a
      exact ⟨0, FractionalIdeal.zero_mem _, by rw [mul_zero]; exact neg_eq_zero.1 h3⟩
    · have hN' : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
      have h3 : ∑ a, ((N : E)⁻¹ * (β a b / X.ξ0 * y)) • cu.e a = -w := by
        have h4 : w = (N : E)⁻¹ • (N • w) := by
          rw [← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ hN', one_smul]
        rw [h4, ← hw', Finset.smul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_smul, ← neg_smul, mul_neg, neg_neg]
      refine ⟨_, (hc _).1 (h3 ▸ X.Λ.neg_mem hw) a, ?_⟩
      rw [mul_inv_cancel_left₀ hN']
  · rintro ⟨hs, hβ⟩
    have h1 := zMatE_congr_of_entries X N cu c hd hc β hβ
    have h2 := zMatE_congr_of_entries X N cu c hd hc (-β) (by
      intro a b y hy
      obtain ⟨z, hz, hz'⟩ := hβ a b y hy
      refine ⟨-z, (c a : Submodule (𝓞 E) E).neg_mem hz, ?_⟩
      rw [Matrix.neg_apply, neg_div, neg_mul, hz', mul_neg])
    have hm : FJ.zMatE X cu.e β * FJ.zMatE X cu.e (-β) = 1 := by
      rw [← zMatE_add, add_neg_cancel, zMatE_zero]
    have hm' : FJ.zMatE X cu.e (-β) * FJ.zMatE X cu.e β = 1 := by
      rw [← zMatE_add, neg_add_cancel, zMatE_zero]
    refine ⟨hs, ⟨_, _, hm, hm'⟩, (hΓ _).2 ⟨⟨zMatE_unitary X cu β hs, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩, h1⟩, rfl⟩
    · obtain ⟨w, hw, hw'⟩ := h1 x hx
      change FJ.zMatE X cu.e β *ᵥ x ∈ X.Λ
      rw [hw']
      exact X.Λ.add_mem hx (nsmul_mem hw N)
    · obtain ⟨w, hw, hw'⟩ := h2 _ hx
      change FJ.zMatE X cu.e β *ᵥ x ∈ X.Λ at hx
      change FJ.zMatE X cu.e (-β) *ᵥ (FJ.zMatE X cu.e β *ᵥ x) = FJ.zMatE X cu.e β *ᵥ x + _ at hw'
      rw [Matrix.mulVec_mulVec, hm', Matrix.one_mulVec] at hw'
      rw [hw']
      exact X.Λ.add_mem hx (nsmul_mem hw N)

end GlobalTheory.CuspCentre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormalisedPointsSatisfySingleFrame
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.NormFrame

theorem eq_zero_of_eventually {g : ℕ} {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) {z : Fin g → ℂ}
    (hz : ∀ᶠ w in nhds z, θ w = 0) (w : Fin g → ℂ) : θ w = 0 := by
  have hl : Differentiable ℂ (fun t : ℂ => z + t • (w - z)) := by fun_prop
  have hd : Differentiable ℂ (fun t : ℂ => θ (z + t • (w - z))) := hθ.comp hl
  have ha : AnalyticOnNhd ℂ (fun t : ℂ => θ (z + t • (w - z))) Set.univ :=
    hd.differentiableOn.analyticOnNhd isOpen_univ
  have ht : Filter.Tendsto (fun t : ℂ => z + t • (w - z)) (nhds 0) (nhds z) := by
    simpa using hl.continuous.tendsto 0
  have h0 : (fun t : ℂ => θ (z + t • (w - z))) =ᶠ[nhds 0] 0 := ht.eventually hz
  have := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) h0
    (Set.mem_univ 1)
  simpa using this

theorem cancel_entire {g : ℕ} {θ f f' : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (hne : ∃ w, θ w ≠ 0)
    {O : Set (Fin g → ℂ)} (hO : IsOpen O) (hf : ContinuousOn f O) (hf' : ContinuousOn f' O)
    (h : ∀ z ∈ O, θ z * f z = θ z * f' z) : ∀ z ∈ O, f z = f' z := by
  intro z hz
  by_contra hc
  obtain ⟨w, hw⟩ := hne
  apply hw
  apply eq_zero_of_eventually hθ (z := z)
  have h1 : ∀ᶠ w in nhds z, f w ≠ f' w :=
    (((hf.continuousAt (hO.mem_nhds hz)).sub (hf'.continuousAt (hO.mem_nhds hz))).eventually_ne
      (sub_ne_zero.2 hc)).mono fun _ h => sub_ne_zero.1 h
  filter_upwards [h1, hO.mem_nhds hz] with w h1 h2
  by_contra h3
  exact h1 (mul_left_cancel₀ h3 (h w h2))

theorem norm_sq_scalar {g : ℕ} {κ d : ℂ} {P y : ℝ} (hy : 0 < y) (hd : d ≠ 0)
    (hκ : κ ^ 2 = (Real.sqrt (2 ^ g / P) : ℝ) * d) (hP : (P : ℂ) * (y : ℂ) = ((‖d‖ ^ 2 : ℝ) : ℂ)) :
    ‖κ‖ ^ 2 * (Real.sqrt (2 ^ g * y))⁻¹ = 1 := by
  have hP' : P * y = ‖d‖ ^ 2 := by exact_mod_cast hP
  have hd' : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hP0 : 0 < P := by
    have : 0 < P * y := by rw [hP']; positivity
    exact (mul_pos_iff_of_pos_right hy).1 this
  have h1 : ‖κ‖ ^ 2 = Real.sqrt (2 ^ g / P) * ‖d‖ := by
    rw [← norm_pow, hκ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have h2 : Real.sqrt (2 ^ g * y) = Real.sqrt (2 ^ g / P) * ‖d‖ := by
    rw [← Real.sqrt_sq hd'.le, ← Real.sqrt_mul (by positivity), ← hP']
    congr 1
    field_simp
  rw [h1, ← h2]
  exact mul_inv_cancel₀ (Real.sqrt_pos.2 (by positivity)).ne'

theorem period_bas {g : ℕ} {L : Type} [AddCommGroup L] (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] L)
    (P : L →+ (Fin g → ℂ)) (h τ : Matrix (Fin g) (Fin g) ℂ)
    (hn : ∀ i, h *ᵥ P (bas (Pi.single (Sum.inl i) 1)) = Pi.single i 1 ∧
      h *ᵥ P (bas (Pi.single (Sum.inr i) 1)) = τ *ᵥ Pi.single i 1) (v : Fin g ⊕ Fin g → ℤ) :
    h *ᵥ P (bas v) = (fun i => (v (Sum.inl i) : ℂ)) + τ *ᵥ (fun i => (v (Sum.inr i) : ℂ)) := by
  have hs : ∀ w : Fin g → ℤ, (fun i => (w i : ℂ)) = ∑ i, w i • (Pi.single i (1 : ℂ) : Fin g → ℂ) := by
    intro w
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hv : v = ∑ s, v s • (Pi.single s (1 : ℤ) : Fin g ⊕ Fin g → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hs fun i => v (Sum.inl i), hs fun i => v (Sum.inr i)]
  conv_lhs => rw [hv]
  simp only [map_sum, map_zsmul, map_add, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Fintype.sum_sum_type, (hn _).1, (hn _).2]

open MonoidalCategory CartesianMonoidalCategory MonObj in

theorem ex_add_period {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (F : FamilyUnif Xo σ ty) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di k) ty P)
    (a : (F.Di k).La) (z : Fin g → ℂ) : F.ex k P (z + P a) = F.ex k P z := by
  rw [F.ex_add k _ hP, (F.ex_ker k _ hP _).2 ⟨a, rfl⟩, _root_.mul_one]

set_option maxHeartbeats 1600000 in

theorem frameOK_of_isNormUn : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (un : (M.X k).dom → FrPt Xo c (CAt σ)), GoodEmb c σ → ModelBase M → NegXi M → IsNormUn T un → ∀ x, FrameOK e F M k x (un x) := by
  intro _ E _ _ _ H Dw l Xo c σ g e F r M k T un hG hM hX hN x
  obtain ⟨κ, hκ, hx, hu, hs⟩ := hN x
  set b := T.co.symm x.1 with hb
  have hbx : T.co b = x.1 := T.co.apply_symm_apply _
  have hbd : b ∈ T.co ⁻¹' (M.X k).dom := by
    rw [Set.mem_preimage, hbx]; exact x.2
  have hper := T.isPer _ hbd
  refine ⟨T.Pf (T.co b), fun a j => by rw [hbx]; exact T.per _ a j, hper, hx, hu, fun hunit => ?_⟩
  obtain ⟨Hm, hH1, hH2, hH3⟩ := hper.2.2.2.2
  obtain ⟨hdet, hsym, hpos, hn⟩ := T.norm b hbd
  obtain ⟨hHm, hHdet⟩ := GlobalTheory.RiemannForm.herm_eq_of_normalised E H _ g _ T.bas _ (T.h b) (T.ta b) Hm T.sympl hper hn
    ⟨hsym, hpos⟩ hH3
  have hud := GlobalTheory.UnitDet.det_eq_prod E H Dw l Xo c σ g e F r M hG hM hX k T.Pf T.per x.1 x.2 hunit Hm
    (by rw [← hbx]; exact hH3)
  rw [hud] at hHdet
  have hnorm := norm_sq_scalar (g := g) hpos.det_pos hdet.ne_zero hκ hHdet
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    simp at hnorm
  obtain ⟨q, hq⟩ : ∃ q : (Fin g → ℂ) → ℂ, ∀ z, q z = Real.pi / 2 * ((T.h b *ᵥ z) ⬝ᵥ
      ((((T.ta b).map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ (T.h b *ᵥ z))) := ⟨_, fun _ => rfl⟩
  have hlin : Differentiable ℂ (fun z : Fin g → ℂ => T.h b *ᵥ z) :=
    (Matrix.mulVecLin (T.h b)).toContinuousLinearMap.differentiable
  have hqd : Differentiable ℂ q := by
    rw [funext hq]
    simp only [dotProduct, Matrix.mulVec]
    fun_prop
  have hq0 : q 0 = 0 := by simp [hq]
  obtain ⟨hA1, hA2⟩ := GlobalTheory.ThetaAH.exp_mul_thetaChar_automorphy g (T.ta b) (T.h b) Hm T.c₁ T.c₂ q hsym hpos
    T.half₁ T.half₂ hHm hq
  have hlat : ∀ lam, lam ∈ (T.Pf (T.co b)).range ↔ ∃ m n : Fin g → ℤ,
      T.h b *ᵥ lam = (fun i => (m i : ℂ)) + T.ta b *ᵥ (fun i => (n i : ℂ)) := by
    intro lam
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨v, rfl⟩ := T.bas.surjective a
      exact ⟨_, _, period_bas T.bas _ _ _ hn v⟩
    · rintro ⟨m, n, hmn⟩
      refine ⟨T.bas (Sum.elim m n), ?_⟩
      apply Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet)
      rw [hmn]
      exact period_bas T.bas _ _ _ hn _
  obtain ⟨Fd, hFd, hint⟩ := GlobalTheory.ThetaMean.exists_fundamentalDomain_mean_norm_sq_thetaChar g (T.ta b) (T.h b)
    T.c₁ T.c₂ _ hsym hpos hdet T.half₁ T.half₂ hlat
  obtain ⟨hθd, w0, hw0⟩ := (GlobalTheory.ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).1 _ hsym hpos
  have hχ : ∀ lam : Fin g → ℂ, ∃ χ : ℂ, lam ∈ (T.Pf (T.co b)).range → ‖χ‖ = 1 ∧ ∀ z,
      Complex.exp (q (z + lam)) * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ (z + lam)) =
        χ * Complex.exp (Real.pi * hermForm Hm z lam + Real.pi / 2 * hermForm Hm lam lam) *
          (Complex.exp (q z) * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)) := by
    intro lam
    by_cases hl : lam ∈ (T.Pf (T.co b)).range
    · obtain ⟨m, n, hmn⟩ := (hlat lam).1 hl
      obtain ⟨χ, hχ⟩ := hA2 lam m n hmn
      exact ⟨χ, fun _ => hχ⟩
    · exact ⟨1, fun h => absurd h hl⟩
  choose χl hχl using hχ
  have hfrd : ∀ j, DifferentiableOn ℂ (fun z => T.fr j (b, z) * Complex.exp (-q z))
      {z | ⊤ ≤ (F.ex k (T.Pf (T.co b)) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
    intro j
    refine DifferentiableOn.mul ?_ (by fun_prop)
    exact (T.fr_hol j).comp (f := fun z => (b, z)) (by fun_prop) fun z hz => ⟨hbd, hz⟩
  have hval : ∀ j z (pt : Sp ℂ ⟶ Gx (un x).x),
      pt ≫ gxFst (un x).x = (F.ex k (T.Pf (T.co b)) z).left → pt ≫ gxSnd (un x).x = 𝟙 (Sp ℂ) →
      ⊤ ≤ (F.ex k (T.Pf (T.co b)) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' pt ((PPx (un x).x).U (fun _ => j)) ((un x).s.f (fun _ => j)) =
        (κ * (Complex.exp (q z) * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z))) *
          (T.fr j (b, z) * Complex.exp (-q z)) := by
    intro j z pt h1 h2 h3
    rw [hs j z pt h1 h2 h3, Complex.exp_neg]
    have := Complex.exp_ne_zero (q z)
    field_simp
  refine ⟨Hm, χl, fun j z => T.fr j (b, z) * Complex.exp (-q z),
    fun z => κ * (Complex.exp (q z) * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z)), Fd, hH1, hH2, hH3, hfrd,
    fun j z hz => mul_ne_zero (T.fr_ne j b z hbd hz) (Complex.exp_ne_zero _),
    fun j j' z hz => ?_, fun j hz => ?_, fun a j z => ⟨(hχl _ ⟨a, rfl⟩).1, ?_⟩, hval, hFd, ?_⟩
  · beta_reduce
    rw [T.fr_coc j j' b z hbd hz, mul_assoc]
  · beta_reduce
    rw [hq0, neg_zero, Complex.exp_zero, mul_one, T.fr_rig j b hbd hz, hx]
  · have hex : ∀ z, F.ex k (T.Pf (T.co b)) (z + T.Pf (T.co b) a) = F.ex k (T.Pf (T.co b)) z :=
      ex_add_period F k _ hper a
    have hO : IsOpen {z | ⊤ ≤ (F.ex k (T.Pf (T.co b)) z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      have h1 := ((F.hol k 0 Set.univ (fun _ => T.Pf (T.co b)) isOpen_univ
        ⟨fun _ _ => hper, fun _ => differentiableOn_const _⟩).2 (Xo.univ.t.PP.L.U j) 0).1
      have h2 := h1.preimage (f := fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
      convert h2 using 1
      ext z
      simp
    obtain ⟨s, hsec⟩ := T.fr_sec b hbd
    refine cancel_entire (θ := fun z => Complex.exp (q z) * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z))
      (f := fun z => T.fr j (b, z) * Complex.exp (-q z))
      (f' := fun z => χl (T.Pf (T.co b) a) * Complex.exp (Real.pi * hermForm Hm z (T.Pf (T.co b) a) +
        Real.pi / 2 * hermForm Hm (T.Pf (T.co b) a) (T.Pf (T.co b) a)) *
        (T.fr j (b, z + T.Pf (T.co b) a) * Complex.exp (-q (z + T.Pf (T.co b) a))))
      ((hqd.cexp).mul (hθd.comp hlin)) ?_ hO (hfrd j).continuousOn ?_ ?_ z
    · obtain ⟨w, hw⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet) w0
      exact ⟨w, mul_ne_zero (Complex.exp_ne_zero _) (by rw [hw]; exact hw0)⟩
    · refine ContinuousOn.mul (Continuous.continuousOn ?_) ?_
      · simp only [hermForm, dotProduct]
        fun_prop
      · refine (hfrd j).continuousOn.comp (f := fun z => z + T.Pf (T.co b) a) (by fun_prop) fun z hz => ?_
        rw [Set.mem_ofPred_eq, hex]
        exact hz
    · intro z hz
      have hw : (F.ex k (T.Pf (T.co b)) z).left ≫ Xo.univ.t.G.hom = 𝟙 _ ≫ F.u k (T.Pf (T.co b)) := by
        rw [Category.id_comp]
        exact Over.w (F.ex k (T.Pf (T.co b)) z)
      have h1 := hsec j z (pullback.lift _ _ hw) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hz
      have h2 := hsec j (z + T.Pf (T.co b) a) (pullback.lift _ _ hw) (by rw [hex]; exact pullback.lift_fst _ _ _)
        (pullback.lift_snd _ _ _) (by rw [hex]; exact hz)
      have h3 := h1.symm.trans h2
      have h4 := (hχl _ ⟨a, rfl⟩).2 z
      have e1 : Complex.exp (q z) * Complex.exp (-q z) = 1 := by rw [← Complex.exp_add]; simp
      have e2 : Complex.exp (q (z + T.Pf (T.co b) a)) * Complex.exp (-q (z + T.Pf (T.co b) a)) = 1 := by
        rw [← Complex.exp_add]; simp
      linear_combination (thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ z) * T.fr j (b, z)) * e1 + h3 +
        (T.fr j (b, z + T.Pf (T.co b) a) * Complex.exp (-q (z + T.Pf (T.co b) a))) * h4 -
        (thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ (z + T.Pf (T.co b) a)) * T.fr j (b, z + T.Pf (T.co b) a)) * e2
  · rw [← hnorm, ← hint, ← mul_div_assoc, ← MeasureTheory.integral_const_mul]
    congr 2
    ext z
    rw [← hA1 z, norm_mul, norm_mul]
    ring

end GlobalTheory.NormFrame
end

